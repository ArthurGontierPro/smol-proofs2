# This file has the following sections
# Main, Trimmer, Printer, and Parser

# ================ Main ================

struct Options
    ins::String     # one instance name (leave blank if you want all instances)
    proofs::String  # directory containing instances.
    sort::Bool      # sort the instances by size
    veripb::Bool    # veripb comparison (need veripb installed)
    trace::Bool     # veripb trace
    cshow::Bool     # prettyprint of the proof in html
    adjm::Bool      # adj matrix representation of the cone
    order::Bool     # var order
end
function parseargs(args)
    ins = ""
    proofs = pwd()*"/"
    sort = true
    veripb = true
    trace = false
    cshow = false
    adjm = false
    order = false
    for (i, arg) in enumerate(args)
        if arg == "cd" cd() end # hack to add cd in paths
        if arg in ["noveripb","nv"] veripb = false end
        if arg in ["nosort","ns"] sort = false end
        if arg in ["adj","adjm","adjmat"] adjm = false end
        if arg in ["varorder","order","vo"] order = true end
        if arg in ["cshow","show","cs","ciaran_show","ciaranshow"] cshow = true end
        if arg in ["--trace","-trace","trace","-tr","tr"] trace = true end
        if ispath(arg)&&isdir(arg) 
            if arg[end]!='/' 
                proofs = arg*'/'
            else proofs = arg end
        end
        if (ispath(arg)||ispath(arg*".opb"))&&(isfile(arg)||isfile(arg*".opb"))
            if (tmp = findlast('/',arg))===nothing
                ins = arg
                proofs=""
            else 
                ins = arg[tmp+1:end]
                proofs = arg[1:tmp-1]
            end
        end
    end
    for (i, arg) in enumerate(args)
        if isfile(proofs*arg)||isfile(proofs*arg*".opb") 
            ins = arg
        end
    end
    if split(ins,'.')[end] in ["opb","pbp"] ins = ins[1:end-4] end
    if proofs!="" print("Dir:$proofs ") end
    if ins!="" print("Ins:$ins ") end
    return Options(ins,proofs,sort,veripb,trace,cshow,adjm,order)
end
const CONFIG = parseargs(ARGS)
const proofs = CONFIG.proofs
const extention = ".pbp"
const version = "2.0"
mutable struct Lit
    coef::Int
    sign::Bool
    var::Int
end
mutable struct Eq
    t::Vector{Lit}
    b::Int
end
mutable struct Red                      # w: witness. range: id range from beign to end of red. pgranges are the proof goals ranges.
    w::Vector{Lit}                      # each odd index is the variable and each next even is tha target (lit(0,0,-1) means constant 1 and 0 means constant 0)
    range::UnitRange{Int64}
    pgranges::Vector{UnitRange{Int64}}
end
function main()
    if CONFIG.ins != ""
        runtrimmer(CONFIG.ins)
    else
        list = cd(readdir, proofs)
        list = [s for s in list if length(s)>5]
        list = [s[1:end-4] for s in list if s[end-3:end]==".opb" && s[1:5]!="smol."]
        list = [s for s in list if isfile(proofs*s*extention)]
        if CONFIG.sort
            stats = [stat(proofs*file*extention).size+stat(proofs*file*".opb").size for file in list]
            p = sortperm(stats)
        else p = [i for i in eachindex(list)] end
        println(list[p])
        for i in eachindex(list)
            print(i,' ')
            ins = list[p[i]]
            printstyled(ins,"  "; color = :yellow)
            runtrimmer(ins)
        end
    end
end
function runtrimmer(file)
    tvp = @elapsed begin
        if CONFIG.veripb
            if CONFIG.trace
                v1 = run(`veripb --trace --useColor $proofs/$file.opb $proofs/$file$extention`)
            else
                v1 = read(`veripb $proofs/$file.opb $proofs/$file$extention`)
            end
        end
    end
    printstyled(prettytime(tvp),"  "; color = :cyan)
    tri = @elapsed begin
        system,systemlink,redwitness,nbopb,varmap,output,conclusion,version,obj = readinstance(proofs,file)
    end
    printstyled(prettytime(tri),"  "; color = :cyan)
    normcoefsystem(system)
    invsys = getinvsys(system,systemlink,varmap)
    prism = availableranges(redwitness)
    if conclusion in ["BOUNDS"] || conclusion in ["SAT","NONE"] && !isequal(system[end],Eq([],1)) return println() end
    tms = @elapsed begin
        cone = makesmol(system,invsys,varmap,systemlink,nbopb,prism,redwitness)
    end
    printstyled(prettytime(tms),'\n'; color = :cyan)
    twc = @elapsed begin
        writeconedel(proofs,file,version,system,cone,systemlink,redwitness,nbopb,varmap,output,conclusion,obj,prism)
    end
    varocc = printorder(file,cone,invsys,varmap)
    succ = Vector{Vector{Int}}(undef,length(system))
    invlink(systemlink,succ,cone,nbopb)
    index = zeros(Int,length(system)) # map the old indexes to the new ones
    findallindexfirst(index,cone)
    if CONFIG.adjm
        showadjacencymatrix(file,cone,index,systemlink,succ,nbopb)
    end
    if CONFIG.cshow
        ciaranshow(proofs,file,version,system,cone,index,systemlink,succ,redwitness,nbopb,varmap,output,conclusion,obj,prism,varocc)
    end
    tvs = @elapsed begin
        if CONFIG.veripb
            if CONFIG.trace
                v2 = run(`veripb --trace --useColor --traceFail $proofs/smol.$file.opb $proofs/smol.$file$extention`) 
            else
                v2 = read(`veripb $proofs/smol.$file.opb $proofs/smol.$file$extention`) 
            end
        end
    end
    so = stat(string(proofs,"/",file,".opb")).size + stat(string(proofs,"/",file,extention)).size
    st = stat(string(proofs,"/smol.",file,".opb")).size + stat(string(proofs,"/smol.",file,extention)).size
    if !CONFIG.veripb tvp = tvs = 0.1 end
    if file[1] == 'b'
        t = [roundt([parse(Float64,file[end-5:end-3]),parse(Float64,file[end-2:end]),so,st,st/so,tvp,tvs,tvs/tvp,tms,twc,tri],3)]
    elseif file[1] == 'L'
        t = [roundt([parse(Float64,split(file,'g')[2]),parse(Float64,split(file,'g')[3]),so,st,st/so,tvp,tvs,tvs/tvp,tms,twc,tri],3)]
    else
        t = [roundt([0.0,0.0,so,st,st/so,tvp,tvs,tvs/tvp,tms,twc,tri],3)]
    end
    printtabular(t)
    open(string(proofs,"/atable"), "a") do f
        write(f,string(t[1],",\n"))
    end
    if CONFIG.veripb && v1!=v2
        printstyled("Traces are not identical\n"; color = :red)
        open(string(proofs,"/afailedtrims"), "a") do f
            write(f,string(file," \n"))
        end
    end
end




# ================ Trimmer ================

function makesmol(system,invsys,varmap,systemlink,nbopb,prism,redwitness)
    n = length(system)
    antecedants = zeros(Bool,n)
    assi = zeros(Int8,length(varmap))
    cone = zeros(Bool,n)
    cone[end] = true
    front = zeros(Bool,n)
    contradictions = findall(x->length(x.t)==0,system)
    firstcontradiction = 0
    for contradiction in contradictions
        if !inprism(contradiction,prism)
            firstcontradiction = contradiction
        end
    end
    cone[firstcontradiction] = true
    if systemlink[firstcontradiction-nbopb][1] == -2         # pol case
        fixfront(front,systemlink[firstcontradiction-nbopb])
    else
        upquebit(system,invsys,assi,front,prism)
        # println("  init : ",sum(front))#,findall(front)
        append!(systemlink[firstcontradiction-nbopb],findall(front))
    end
    red = Red([],0:0,[]);
    newpfgl = true
    pfgl = Vector{UnitRange{Int64}}()
    while newpfgl # restart if new frontless proofgoals are needed.
        newpfgl = false
        while true in front
            i = findlast(front)
            front[i] = false
            if !cone[i]
                cone[i] = true
                if i>nbopb
                    tlink = systemlink[i-nbopb][1]
                    if tlink == -1                      # u statement 
                        antecedants .=false ; assi.=0
                        if rup(system,invsys,antecedants,i,assi,front,cone,prism,0:0)
                            antecedants[i] = false
                            append!(systemlink[i-nbopb],findall(antecedants))
                            fixfront(front,antecedants)
                        else
                            println("\n",i," s=",slack(reverse(system[i]),assi))
                            println(writepol(systemlink[i-1-nbopb],[i for i in eachindex(system)],varmap))
                            println(writeeq(system[i-1],varmap))
                            println(writeeq(system[i],varmap))
                            printstyled(" rup failed \n"; color = :red)
                            return cone
                        end
                    elseif tlink >= -3                  # pol and ia statements
                        antecedants .= false
                        fixante(systemlink,antecedants,i-nbopb)
                        fixfront(front,antecedants)
                    elseif tlink == -10                 # (end of subproof)
                        red = redwitness[i]
                        front[red.range.start] = true
                        for subr in red.pgranges
                            if systemlink[subr.start-nbopb] == -8 && !(front[subr.start]||cone[subr.start])
                                push!(pfgl,subr)
                            else
                                front[subr.start] = true
                                front[subr.stop] = true
                            end
                        end
                    elseif tlink == -5                  # subproof rup
                        subran = findfirst(x->i in x,red.pgranges)
                        antecedants .=false ; assi.=0
                        if rup(system,invsys,antecedants,i,assi,front,cone,prism,red.pgranges[subran])
                            antecedants[i] = false
                            append!(systemlink[i-nbopb],findall(antecedants))
                            fixfront(front,antecedants) 
                        else printstyled(" subproof rup failed \n"; color = :red)
                        end
                    elseif tlink == -6 || tlink == -8   # subproof pol and proofgoal of a previous eq
                        antecedants .= false
                        fixante(systemlink,antecedants,i-nbopb)
                        fixfront(front,antecedants)
                    elseif tlink == -7
                    end
                end
            end
        end
        for r in pfgl           # we check if any new proofgoal is needed
            id = systemlink[r.start-nbopb][2]
            if cone[id] && !cone[r.start]
                println("restart red at ")
                printeq(system[r.start])
                front[r.start] = front[r.stop] = true
                newpfgl = true
            end
        end
    end
    fixredsystemlink(systemlink,cone,prism,nbopb)
    return cone
end
function rup(system,invsys,antecedants,init,assi,front,cone,prism,subrange)# I am putting back cone and front together because they will both end up in the cone at the end.
    que = ones(Bool,init)
    rev = reverse(system[init])
    prio = true
    r0 = i = 1
    r1 = init+1
    while i<=init
        if que[i] && (!prio || (prio&&(front[i]||cone[i]))) && (!inprism(i,prism) || (i in subrange))
            eq = i==init ? rev : system[i]
            s = slack(eq,assi)
            if s<0
                antecedants[i] = true
                return true
            else
                r0,r1 = updateprioquebit(eq,cone,front,que,invsys,s,i,init,assi,antecedants,r0,r1)
            end
            que[i] = false
            i+=1
            if prio
                i = min(i,r1)
                r1 = init+1
            else
                if r1<init+1
                    prio = true
                    r0 = min(i,r0)
                    i = r1
                    r1 = init+1
                else
                    i = min(i,r0)
                    r0 = init+1
                end
            end
        else
            i+=1
        end
        if prio && i==init+1
            prio=false
            i=r0
            r0=init+1
        end
    end
    return false
end
function slack(eq::Eq,assi::Vector{Int8}) # slack is the difference between the space left to catch the bound and the space catchable by the unaffected variables.
    c=0
    for l in eq.t
        if assi[l.var] == 0 || 
            (l.sign && assi[l.var] == 1) || 
            (!l.sign && assi[l.var] == 2) 
            c+=l.coef
        end
    end
    if length(eq.t) > 0
        c-= eq.b
    end
    return c
end
function addinvsys(invsys,eq,id)
    for l in eq.t
        if !isassigned(invsys,l.var)
            invsys[l.var] = [id]
        else
            push!(invsys[l.var],id)
        end
    end
end
function getinvsys(system,systemlink,varmap)
    invsys = Vector{Vector{Int}}(undef,length(varmap))
    for i in eachindex(system)
        addinvsys(invsys,system[i],i)
    end # arrays should be sorted at this point
    return invsys
end
function updatequebit(eq,que,invsys,s,i,assi::Vector{Int8},antecedants)
    rewind = i+1
    for l in eq.t
        if l.coef > s && assi[l.var]==0
            assi[l.var] = l.sign ? 1 : 2
            antecedants[i] = true
            for id in invsys[l.var]
                rewind = min(rewind,id)
                que[id] = true
            end
        end
    end
    return rewind
end
function upquebit(system,invsys,assi,antecedants,prism)
    que = ones(Bool,length(system))
    i = 1
    while i<=length(system)
        if que[i] && !inprism(i,prism)
            eq = system[i]
            s = slack(eq,assi)
            if s<0
                antecedants[i] = true
                return 
            else
                rewind = updatequebit(eq,que,invsys,s,i,assi,antecedants)
                que[i] = false
                i = min(i,rewind-1)
            end
        end
        i+=1
    end
    printstyled(" upQueBit empty "; color = :red)
end
function updateprioquebit(eq,cone,front,que,invsys,s,i,init,assi::Vector{Int8},antecedants,r0,r1)
    for l in eq.t
        if l.coef > s && assi[l.var]==0
            assi[l.var] = l.sign ? 1 : 2
            antecedants[i] = true
            for id in invsys[l.var]
                if id<=init && id!=i
                    que[id] = true
                    if cone[id] || front[id]
                        r1 = min(r1,id)
                    else
                        r0 = min(r0,id)
                    end
                end
            end
        end
    end
    return r0,r1
end
function reverse(eq::Eq)
    c=0
    lits = [Lit(l.coef,l.sign,l.var) for l in eq.t]
    for l in lits
        l.sign = !l.sign
        c+=l.coef
    end
    return Eq(lits,-eq.b+1+c)
end
function fixante(systemlink::Vector{Vector{Int}},antecedants::Vector{Bool},i)
    for j in eachindex(systemlink[i])
        t = systemlink[i][j]
        if t>0 && !(j<length(systemlink[i]) && (systemlink[i][j+1] == -2 || systemlink[i][j+1] == -3))
            antecedants[t] = true
        end
    end
end
function fixfront(front::Vector{Bool},antecedants::Vector{Bool})
    for i in eachindex(antecedants)
        if antecedants[i]
            front[i] = true
        end
    end
end
function fixfront(front::Vector{Bool},antecedants::Vector{Int})
    for i in antecedants
        if i>0
            front[i] = true
        end
    end
end
function fixredsystemlink(systemlink,cone,prism,nbopb)
    for range in prism
        for i in range
            if cone[i]
                for j in eachindex(systemlink[i-nbopb])
                    k = systemlink[i-nbopb][j]
                    if isid(systemlink[i-nbopb],j) && !(k in systemlink[range.start-nbopb]) && k<range.start-nbopb
                        push!(systemlink[range.start-nbopb],k)
                    end
                end
            end
        end
        sort!(systemlink[range.start-nbopb])
    end
end
function inprism(n,prism)
    for r in prism
        if n in r return true end
    end
    return false
end
function availableranges(redwitness)                   # build the prism, a range colections of all the red subproofs
    prism = [a.range for (_,a) in redwitness if a.range!=0:0]
    return prism
end




# ================ Printer ================

function writeconedel(path,file,version,system,cone,systemlink,redwitness,nbopb,varmap,output,conclusion,obj,prism)
    index = zeros(Int,length(system))
    lastindex = 0
    open(string(path,"/smol.",file,".opb"),"w") do f
        write(f,obj)
        for i in 1:nbopb
            if cone[i]
                lastindex += 1
                index[i] = lastindex
                eq = system[i]
                write(f,writeeq(eq,varmap))
            end
        end
    end
    succ = Vector{Vector{Int}}(undef,length(system))
    dels = zeros(Bool,length(system))
    dels[1:nbopb].=true #we dont delete in the opb
    for p in prism
        dels[p].=true # we dont delete red and supproofs because veripb is already doing it
    end
    # dels = ones(Bool,length(system)) # uncomment if you dont want deletions.
    invlink(systemlink,succ,cone,nbopb)
    todel = Vector{Int}()
    open(string(path,"/smol.",file,extention),"w") do f
        write(f,string("pseudo-Boolean proof version ",version,"\n"))
        write(f,string("f ",sum(cone[1:nbopb])," 0\n"))
        for i in nbopb+1:length(system)
            if cone[i]
                lastindex += 1
                index[i] = lastindex
                eq = system[i]
                tlink = systemlink[i-nbopb][1]
                if tlink == -1               # rup
                    write(f,writeu(eq,varmap))
                    if length(eq.t)>0 
                        writedel(f,systemlink,i,succ,index,nbopb,dels)
                    end
                elseif tlink == -2           # pol
                    write(f,writepol(systemlink[i-nbopb],index,varmap))
                    writedel(f,systemlink,i,succ,index,nbopb,dels)
                elseif tlink == -3           # ia
                    write(f,writeia(eq,systemlink[i-nbopb][2],index,varmap))
                    writedel(f,systemlink,i,succ,index,nbopb,dels)
                elseif tlink == -4           # red alone
                    write(f,writered(eq,varmap,redwitness[i],"")) # since simple red have no antecedants, they cannot trigger deletions ie they cannot be the last successor of a previous eq
                    dels[i] = true           # we dont delete red statements
                elseif tlink == -5           # rup in subproof
                    write(f,"    ")
                    write(f,writeu(eq,varmap))
                    push!(todel,i)
                elseif tlink == -6           # pol in subproofs
                    write(f,"    ")
                    write(f,writepol(systemlink[i-nbopb],index,varmap))
                    push!(todel,i)
                elseif tlink == -9           # red with begin initial reverse equation (will be followed by subproof)
                    write(f,writered(reverse(eq),varmap,redwitness[i]," ; begin"))
                    todel = [i]
                    dels[i] = true           # we dont delete red statements
                elseif tlink == -7           # red proofgoal 
                    write(f,"    proofgoal #1\n")
                elseif tlink == -8           # red proofgoal normal
                    write(f,string("    proofgoal ",index[systemlink[i-nbopb][2]],"\n"))
                    push!(todel,i)
                elseif tlink == -10          # red proofgoal end
                    lastindex -= 1
                    write(f,"    end -1\n")
                    next = systemlink[i-nbopb][1]
                    if next != -7 && next !=8  # if no more proofgoals, end the subproof
                        lastindex += 1
                        write(f,"end\n") 
                        for ii in todel
                            writedel(f,systemlink,ii,succ,index,nbopb,dels)
                        end
                    end
                elseif tlink == -20           # solx
                    write(f,writesol(eq,varmap))
                    dels[i] = true # do not delete sol
                # elseif tlink == -6           # soli
                    # write(f,writesol(eq,varmap)) #TODO
                    # dels[i] = true # do not delete sol
                else
                    println("ERROR tlink = ",tlink)
                    lastindex -= 1
                end
            end
        end
        write(f,string("output ",output,"\n"))
        if conclusion == "SAT"
            write(f,string("conclusion ",conclusion,"\n"))
        else
            write(f,string("conclusion ",conclusion," : -1\n"))
        end
        write(f,"end pseudo-Boolean proof\n")
    end
end
function invlink(systemlink,succ::Vector{Vector{Int}},cone,nbopb)
    for i in eachindex(systemlink)
        if isassigned(systemlink,i)
            link = systemlink[i]
            for k in eachindex(link)
                j = link[k]
                if isid(link,k) && cone[i+nbopb]
                    if isassigned(succ,j)
                        if !(i+nbopb in succ[j])
                            push!(succ[j],i+nbopb)
                        end
                    else
                        succ[j] = [i+nbopb]
                    end
                end
            end
        end
    end
end
function findallindexfirst(index,cone)
    lastindex = 0
    for i in eachindex(cone)
        if cone[i]
            lastindex += 1
            index[i] = lastindex
        end
    end
end
function mkdir2(p) if !isdir(p) mkdir(p) end end
function printorder(file,cone,invsys,varmap)
    s = "map<string,int> order { "     
    varocc = [sum(cone[j] for j in i) for i in invsys] # order from var usage in cone
    p = sortperm(varocc,rev=true)
    for i in eachindex(varmap)
        j = p[i]
        var = varmap[j]
        occ = varocc[j]
        s = string(s,"{\"",var,"\",",occ,"}, ")
    end
    s = s[1:end-2]*"};"
    if CONFIG.order
        dir = string(proofs,"/cone_var_order/")
        mkdir2(dir)
        open(string(dir,file,".cc"),"w") do f
            write(f,s)
        end
    end
    return varocc
end
function writeu(e,varmap)
    return string("u ",writeeq(e,varmap))
end
function writeia(e,link,index,varmap)
    return string("ia ",writeeq(e,varmap)[1:end-1]," ",index[link],"\n")
end
function writesol(e,varmap)
    s = "solx"
    for l in e.t
        s = string(s,if l.sign " ~" else " " end, varmap[l.var])
    end
    return string(s,"\n")
end
function writewitness(s,witness,varmap)
    for l in witness.w
        if l.var>0
            s = string(s,if !l.sign " ~" else " " end, varmap[l.var])
        else
            s = string(s," ",-l.var)
        end
    end
    return s
end
function writered(e,varmap,witness,beg)
    s = "red"
    for l in e.t
        s = string(s," ",l.coef,if !l.sign " ~" else " " end, varmap[l.var])
    end
    s = string(s," >= ",e.b," ;")
    s = writewitness(s,witness,varmap)
    return string(s,beg,"\n")
end
function writepol(link,index,varmap)
    s = string("p")
    for i in 2:length(link)
        t = link[i]
        if t==-1
            s = string(s," +")
        elseif t==-2
            s = string(s," *")
        elseif t==-3
            s = string(s," d")
        elseif t==-4
            s = string(s," s")
        elseif t==-5
            s = string(s," w")
        elseif t>0
            if link[i+1] in [-2,-3]
                s = string(s," ",t)
            else
                s = string(s," ",index[t])
            end
        elseif t<=-100
            sign = mod((-t),100)!=1
            s = string(s,if sign " " else " ~" end,varmap[(-t) ÷ 100])
        end
    end
    return string(s,"\n")
end
function writedel(f,systemlink,i,succ,index,nbopb,dels)
    isdel = false
    link = systemlink[i-nbopb]
    for k in eachindex(link)
        p = link[k]
        if isid(link,k) && !dels[p] 
            m = maximum(succ[p])
            if m == i
                if !isdel
                    write(f,string("del id "))
                    isdel = true
                end
                dels[p] = true
                write(f,string(index[p]," "))
                if index[p] == 0
                    printstyled(string(" index is 0 for ",p," => ",index[p],"\n"); color = :red)                end
            end
        end
    end
    if isdel
        write(f,string("\n"))
    end
end
function writeeq(e,varmap)
    s = ""
    for l in e.t
        s = string(s,writelit(l,varmap)," ")
    end
    return string(s,">= ",e.b," ;\n")
end
function writelit(l,varmap)
    return string(l.coef," ",if l.sign "" else "~" end, varmap[l.var])
end
function isid(link,k)                 # dont put mult and div coefficients as id and weakned variables too
    return link[k]>0 && (k==length(link)||(link[k+1] != -2 && link[k+1] != -3))
end
function isequal(a,b) # equality between lits
    return a.coef==b.coef && a.sign==b.sign && a.var==b.var
end
function isequal(e,f) # equality between eq
    if e.b!=f.b
        return false
    elseif length(e.t) != length(f.t)
        return false
    else
        for i in eachindex(e.t)
            if !isequal(e.t[i],f.t[i])
                return false
            end
        end
        return true
    end
end
function printlit(l)
    printstyled(l.coef,' '; color = :blue)
    if !l.sign printstyled('~'; color = :red) end
    printstyled(l.var; color = :green)
end
function printlit(l,varmap)
    printstyled(l.coef,' '; color = :blue)
    if !l.sign printstyled('~'; color = :red) end
    printstyled(varmap[l.var]; color = :green)
end
function printeq(e)
    for l in e.t
        print("  ")
        printlit(l)
    end
    println("  >= ",e.b)
end
function printeq(e,varmap)
    for l in e.t
        print("  ")
        printlit(l,varmap)
    end
    println("  >= ",e.b)
end
function showadjacencymatrix(file,cone,index,systemlink,succ,nbopb)
    M,D,n = computeMD(file,cone,index,systemlink,succ,nbopb)
    dir = string(proofs,"/cone_mat/")
    mkdir2(dir)
    open(string(dir,file,".html"),"w") do f
        write(f,"<!DOCTYPE html><head>
  <title> $file </title>
  <script src=\"https://d3js.org/d3.v7.min.js\"></script>
  <style>
    .cell {
      stroke: #ccc;
      shape-rendering: crispEdges;
    }
    .label {
      font-size: 14px;
      font-family: Arial, sans-serif;
      text-anchor: middle;
    }
  </style>
</head>
<body>
  <script>")

    writematjs("matrix",M,n,f)
    writematjs("dist",D,n,f)
    max = maximum(D)

    write(f,"const size = 20; // Cell size
    const n = matrix.length;
    const max = $max;

    // Create SVG
    const svg = d3.select(\"body\")
      .append(\"svg\")
      .attr(\"width\", n * size+size)
      .attr(\"height\", n * size+size);
    let isHighlighted = false; // Track if the matrix is highlighted
    // Draw cells
    for (let row = 0; row < n; row++) {
      for (let col = 0; col < n; col++) {
        svg.append(\"rect\")
          .datum({ value: matrix[row][col], row, col }) // Bind data directly
          .attr(\"class\", \"cell\")
          .attr(\"x\", col * size+size)
          .attr(\"y\", row * size+size)
          .attr(\"width\", size)
          .attr(\"height\", size)
          .attr(\"fill\", matrix[row][col] ? \"steelblue\" : \"white\")
          .on(\"click\", function (event, d) {
            if (isHighlighted) {
          // Reset all cells
          d3.selectAll(\".cell\")
            .attr(\"fill\", d => d.value ? \"steelblue\" : \"white\");
          isHighlighted = false; // Unset highlight
        } else {
            d3.selectAll(\".cell\")
              .attr(\"fill\",  cell => {
                const val = dist[cell.row][cell.col];
                if (val>0&& cell!=d && d.value>0) {
                    if (cell.row==row){
                        return `rgb(0,\${55+val*200/max},0)`;
                    }else if(cell.col==col) {
                        return `rgb(\${55+val*200/max},0,0)`;
                    }else{
                        return matrix[cell.row][cell.col] ? \"steelblue\" : \"white\"
                    }
                }else{
                        return matrix[cell.row][cell.col] ? \"steelblue\" : \"white\"
                    }
              });
            isHighlighted = true; // Set highlight
            }
          });
      }
    }

    // Add row labels
    svg.selectAll(\".row-label\")
      .data(d3.range(n))
      .enter()
      .append(\"text\")
      .attr(\"class\", \"label\")
      .attr(\"x\", size/2-2*size/10) // Offset for the label
      .attr(\"y\", d => d * size + size + 2*size/10 + size / 2)
      .text(d => d + 1); // Row numbers start from 1

    // Add column labels
    svg.selectAll(\".col-label\")
      .data(d3.range(n))
      .enter()
      .append(\"text\")
      .attr(\"class\", \"label\")
      .attr(\"x\", d => d * size + size + size / 2)
      .attr(\"y\", 8*size/10) // Offset for the label
      .text(d => d + 1);

  </script>
  </body>
</html>
")
    end
end
function writematjs(name,a,n,f)
    write(f,"const $name = [\n")
    for i in 1:n
        write(f,"[")
        for j in 1:n
            write(f,string(Int(a[i,j])))
            if j<n write(f,", ") end
        end
        if i<n write(f,"],\n") else write(f,"]];\n") end
    end
end
function distrec(M,i,n,D,rank)
    for j in 1:n
        if M[i,j] && D[i,j] > rank
            D[i,j] = rank
            distrec(M,j,n,D,rank+1)
        end
    end
end
function computeMD(file,cone,index,systemlink,succ,nbopb)
    n = sum(cone)
    M = zeros(Bool,n,n)
    for i in findall(cone)
        if isassigned(succ,i)
            for j in succ[i]
                M[index[i],index[j]] = true
            end
        end
    end
    D = fill(n+1,(n,n))
    distrec(M,1,n,D,1)
    for i in eachindex(D)
        if D[i]==n+1 D[i] = 0 end
    end
    return M,D,n
end
# reprint the proof with colors for ciaran
function printpred(i,link,nbpred,maxpred,index,nbopb)
    if length(link)<=1
        return ""
    else
        s = string( "<span style=\"color: rgb(",Int(round(200*nbpred[i-nbopb]/maxpred))+55,",0,0)\">Pred (",nbpred[i-nbopb],") ")
        for k in eachindex(link)
            if isid(link,k)
                s = string(s,lid(index[link[k]]))
            end
        end
        return string(s,"</span>\n")
    end
end
function printsucc(i,succ,nbsucc,maxsucc,index)
    s = string( "<span style=\"color: rgb(0,",Int(round(150*nbsucc[i]/maxsucc))+55,",0)\">Succ (",nbsucc[i],") ")
    for j in succ
        s = string(s,lid(index[j]))
    end
    return string(s,"</span>\n")
end
function writelitcolor(l,varmap,varocc,m,r)
    return string(l.coef," ",if l.sign "" else "~" end, "<span style=\"color: rgb(",Int(round(255*(varocc[l.var]-m)/r)),",0,255)\">",varmap[l.var],"</span>")
end
function writeeqcolor(e,varmap,varocc,m,r)
    s = ""
    for l in e.t
        s = string(s,writelitcolor(l,varmap,varocc,m,r)," ")
    end
    return string(s,">= ",e.b," ;\n")
end
function writedelcolor(f,systemlink,i,succ,index,nbopb,dels)
    isdel = false
    link = systemlink[i-nbopb]
    for k in eachindex(link)
        p = link[k]
        if isid(link,k) && !dels[p] 
            m = maximum(succ[p])
            if m == i
                if !isdel
                    write(f,string("del id "))
                    isdel = true
                end
                dels[p] = true
                write(f,lid(index[p]))
                if index[p] == 0
                    printstyled(string(" index is 0 for ",p," => ",index[p],"\n"); color = :red)                end
            end
        end
    end
    if isdel
        write(f,string("\n"))
    end
end
function makelinefit(len,s)
    if length(s)<len
        return s
    else 
        s = s[1:len-3]
        lastbr1 = findlast('{',s)
        lastbr2 = findlast('}',s)
        if lastbr1===nothing || !(lastbr2===nothing) && lastbr1<lastbr2
            return string(s,"...\n")
        else
            return string(s,"}...\n")
        end
    end
end
function findallindexfirst(index,cone)
    lastindex = 0
    for i in eachindex(cone)
        if cone[i]
            lastindex += 1
            index[i] = lastindex
        end
    end
end
function wid(i)
    return string("<span style=\"background-color: rgb(160,160,0)\" id=\"",i,"\">Id ",i,"</span> ")
end
function lid(i)
    return string("<a href=\"#",i,"\">",i,"</a> ")
end
function writeredcolor(e,varmap,witness,beg,varocc,m,r)
    s = "red "
    for l in e.t
        s = string(s,writelitcolor(l,varmap,varocc,m,r)," ")
    end
    s = string(s,">= ",e.b," ;")
    for l in witness.w
        if l.var>0
            s = string(s,if !l.sign " ~" else " " end, "<span style=\"color: rgb(",Int(round(255*(varocc[l.var]-m)/r)),",0,255)\">",varmap[l.var],"</span>")
        else
            s = string(s," ",-l.var)
        end
    end
    return string(s,beg,"\n")
end
function ciaranshow(path,file,version,system,cone,index,systemlink,succ,redwitness,nbopb,varmap,output,conclusion,obj,prism,varocc)
    dels = zeros(Bool,length(system))
    dels[1:nbopb].=true
    for p in prism
        dels[p].=true # we dont delete red and supproofs because veripb is already doing it
    end
    # dels = ones(Bool,length(system)) # uncomment if you dont want deletions.
    todel = Vector{Int}()
    nbsucc = [if isassigned(succ,i) length(succ[i]) else 0 end for i in eachindex(succ)]
    maxsucc = maximum(nbsucc)
    nbpred = [sum(Int(isid(link,k)) for k in eachindex(link)) for link in systemlink]
    maxpred = maximum(nbpred)
    ID = [i for i in eachindex(cone)]
    m = minimum(varocc)
    r = maximum(varocc) - m
    lastindex = 0
    dir = string(proofs,"/ciaran_show/")
    mkdir2(dir)
    open(string(dir,file,".html"),"w") do f
        write(f,"<html><head><style> a {color: inherit;text-decoration: none;}</style></head><body style=\"font-family: Courier, monospace; background-color:#a9a9a9 \"><pre>\n")
        write(f,"======================   ",file,".opb   ======================   <a href=\"#pbp\" style=\"color: blue;\">Go to pbp</a>\n")
        write(f,obj)
        for i in 1:nbopb
            eq = system[i]
            if cone[i]
                lastindex += 1
                write(f,string(wid(lastindex),writeeqcolor(eq,varmap,varocc,m,r)))
                write(f,printsucc(i,succ[i],nbsucc,maxsucc,index))
            else
                write(f,writeeq(eq,varmap))
            end
        end
        write(f,"<span id=\"pbp\">======================   ",file,".pbp   ======================</span>\n")
        for i in nbopb+1:length(system)
            eq = system[i]
            tlink = systemlink[i-nbopb][1]
            if cone[i]
                lastindex += 1
                if tlink == -1               # rup
                    write(f,string(wid(lastindex),"u ",writeeqcolor(eq,varmap,varocc,m,r)))
                    write(f,printpred(i,systemlink[i-nbopb],nbpred,maxpred,index,nbopb))
                    if length(eq.t)>0 
                        write(f,printsucc(i,succ[i],nbsucc,maxsucc,index))
                        writedelcolor(f,systemlink,i,succ,index,nbopb,dels)
                    end
                elseif tlink == -2           # pol
                    write(f,string(wid(lastindex),writepol(systemlink[i-nbopb],index,varmap)))
                    write(f,writeeqcolor(eq,varmap,varocc,m,r))
                    write(f,printpred(i,systemlink[i-nbopb],nbpred,maxpred,index,nbopb))
                    write(f,printsucc(i,succ[i],nbsucc,maxsucc,index))
                    writedelcolor(f,systemlink,i,succ,index,nbopb,dels)
                elseif tlink == -3           # ia
                    write(f,string(wid(lastindex),"ia ",writeeqcolor(eq,varmap,varocc,m,r)[1:end-1]," ",lid(index[systemlink[i-nbopb][2]]),"\n"))
                    write(f,printpred(i,systemlink[i-nbopb],nbpred,maxpred,index,nbopb))
                    write(f,printsucc(i,succ[i],nbsucc,maxsucc,index))
                    writedelcolor(f,systemlink,i,succ,index,nbopb,dels)
                elseif tlink == -4           # red alone
                    write(f,string(wid(lastindex),writeredcolor(eq,varmap,redwitness[i],"",varocc,m,r)))
                    write(f,printpred(i,systemlink[i-nbopb],nbpred,maxpred,index,nbopb))
                    write(f,printsucc(i,succ[i],nbsucc,maxsucc,index)) # since simple red have no antecedants, they cannot trigger deletions ie they cannot be the last successor of a previous eq
                    dels[i] = true  # we dont delete red statements
                elseif tlink == -5           # rup in subproof
                    write(f,"    ")
                    write(f,string(wid(lastindex),"u ",writeeqcolor(eq,varmap,varocc,m,r)))
                    write(f,"    ",printpred(i,systemlink[i-nbopb],nbpred,maxpred,index,nbopb))
                    if isassigned(succ,i) write(f,"    ",printsucc(i,succ[i],nbsucc,maxsucc,index)) end
                    push!(todel,i)
                elseif tlink == -6           # pol in subproofs
                    write(f,"    ")
                    write(f,string(wid(lastindex),writepol(systemlink[i-nbopb],index,varmap)))
                    write(f,"    ",writeeqcolor(eq,varmap,varocc,m,r))
                    write(f,"    ",printpred(i,systemlink[i-nbopb],nbpred,maxpred,index,nbopb))
                    if isassigned(succ,i) write(f,"    ",printsucc(i,succ[i],nbsucc,maxsucc,index)) end
                    push!(todel,i)
                elseif tlink == -9           # red with begin initial reverse equation (will be followed by subproof)
                    write(f,string(wid(lastindex),writeredcolor(reverse(eq),varmap,redwitness[i]," ; begin",varocc,m,r)))
                    write(f,"    ",printpred(i,systemlink[i-nbopb],nbpred,maxpred,index,nbopb))
                    if isassigned(succ,i) write(f,"    ",printsucc(i,succ[i],nbsucc,maxsucc,index)) end
                    todel = [i]
                    dels[i] = true  # we dont delete red statements
                elseif tlink == -7           # red proofgoal #
                    write(f,"    ",wid(lastindex),"proofgoal #1\n")
                    write(f,"    ",writeeqcolor(eq,varmap,varocc,m,r))
                    write(f,"    ",printpred(i,systemlink[i-nbopb],nbpred,maxpred,index,nbopb))
                    write(f,"    ",printsucc(i,succ[i],nbsucc,maxsucc,index))
                elseif tlink == -8           # red proofgoal normal
                    write(f,string("    ",wid(lastindex),"proofgoal ",lid(index[systemlink[i-nbopb][2]]),"\n"))
                    write(f,"    ",writeeqcolor(eq,varmap,varocc,m,r))
                    write(f,"    ",printpred(i,systemlink[i-nbopb],nbpred,maxpred,index,nbopb))
                    if isassigned(succ,i) write(f,"    ",printsucc(i,succ[i],nbsucc,maxsucc,index)) end
                    push!(todel,i)
                elseif tlink == -10          # red proofgoal end
                    lastindex -= 1
                    write(f,"    end -1\n")
                    next = systemlink[i-nbopb][1]
                    if next != -7 && next !=8  # if no more proofgoals, end the subproof
                        lastindex += 1
                        write(f,"end\n") 
                        for ii in todel
                            writedelcolor(f,systemlink,ii,succ,index,nbopb,dels)
                        end
                    end
                elseif tlink == -20           # solx
                    write(f,string(wid(lastindex),writesol(eq,varmap)))
                    dels[i] = true # do not delete sol
                # elseif tlink == -6           # soli
                    # write(f,writesol(eq,varmap)) #TODO
                    # dels[i] = true # do not delete sol
                else
                    println("ERROR tlink = ",tlink)
                    lastindex -= 1
                end
            else
                if tlink == -1               # rup
                    write(f,writeu(eq,varmap))
                elseif tlink == -2           # pol
                    write(f,writepol(systemlink[i-nbopb],ID,varmap))
                elseif tlink == -3           # ia
                    write(f,writeia(eq,systemlink[i-nbopb][2],ID,varmap))
                elseif tlink == -4           # red alone
                    write(f,writered(eq,varmap,redwitness[i],""))
                elseif tlink == -5           # rup in subproof
                    write(f,"    ")
                    write(f,writeu(eq,varmap))
                elseif tlink == -6           # pol in subproofs
                    write(f,"    ")
                    write(f,writepol(systemlink[i-nbopb],ID,varmap))
                elseif tlink == -9           # red with begin initial reverse equation (will be followed by subproof)
                    write(f,writered(reverse(eq),varmap,redwitness[i]," ; begin"))
                elseif tlink == -7           # red proofgoal #
                    write(f,"    proofgoal #1\n")
                elseif tlink == -8           # red proofgoal normal
                    write(f,string("    proofgoal ",ID[systemlink[i-nbopb][2]],"\n"))
                elseif tlink == -10          # red proofgoal end
                    write(f,"    end -1\n")
                    next = systemlink[i-nbopb][1]
                    if next != -7 && next !=8  # if no more proofgoals, end the subproof
                        write(f,"end\n") 
                    end
                elseif tlink == -20           # solx
                    write(f,writesol(eq,varmap))
                else
                    println("ERROR tlink = ",tlink)
                end
            end
        end
        write(f,"</pre></body></html>")
    end
end
function printtabular(t)
    for i in t 
        println(
        round(Int,i[1])," & ",
        round(Int,i[2])," & ",
        prettybytes(i[3])," & ",
        prettybytes(i[4])," &   ",
        prettypourcent(i[5]),"   & ",
        prettytime(i[6])," & ",
        prettytime(i[7])," &   ",
        prettypourcent(i[8]),"   & ",
        prettytime(i[9])," & ",
        prettytime(i[10])," & ",
        prettytime(i[11])," \\\\\\hline"
        )
    end
end
function prettybytes(b)
    if b>=10^9
        return string(round(b/(10^9); sigdigits=4)," GB")
    elseif b>=10^6
        return string(round(b/(10^6); sigdigits=4)," MB")
    elseif b>=10^3
        return string(round(b/(10^3); sigdigits=4)," KB")
    else
        return  string(round(b; sigdigits=4)," B")
    end
end 
function prettytime(b)
    if b<0.01
        return  string(0)
    elseif b<0.1
        return  string(round(b; sigdigits=1))
    elseif b<1
        return  string(round(b; sigdigits=2))
    else
        return  string(round(b; sigdigits=3))
    end
end
function prettypourcent(b)
    b = b*100
    c = round(Int,b)
    return  string(c)
end
function roundt(t,d)
    for i in eachindex(t)
        t[i] = round(t[i],digits = d)
    end
    return t
end




# ================ Parser ================

function readinstance(path,file)
    system,varmap,obj = readopb(path,file)
    nbopb = length(system)
    system,systemlink,redwitness,output,conclusion,version = readveripb(path,file,system,varmap,obj)
    return system,systemlink,redwitness,nbopb,varmap,output,conclusion,version,obj
end
function readvar(s,varmap)
    tmp = s[1]=='~' ? s[2:end] : s
    # tmp = split(s,'~')[end]
    for i in eachindex(varmap)
        if varmap[i]==tmp
            return i
        end
    end
    push!(varmap,tmp)
    return length(varmap)
end
function readeq(st,varmap)
    return readeq(st,varmap,1:2:length(st)-4)
end
function merge(lits)
    c=0
    del = Vector{Int}()
    i=j=1
    while i<length(lits)
        j = i
        while j<length(lits) && lits[i].var==lits[j+1].var
            j+=1
            lits[i],cc = add(lits[i],lits[j])
            c+=cc
            push!(del,j)
        end
        i = j+1
    end
    if length(del)>0
        deleteat!(lits,del)
    end
    return lits,c
end
function readlits(st,varmap,range)
    lits = Vector{Lit}(undef,(length(range)))
    for i in range
        coef = parse(Int,st[i])
        sign = st[i+1][1]!='~'
        var = readvar(st[i+1],varmap)
        lits[(i - range.start)÷range.step+1] = Lit(coef,sign,var)
    end
    sort!(lits,by=x->x.var)
    return lits
end
function readeq(st,varmap,range)
    lits = readlits(st,varmap,range)
    bid = range.start-1+2length(lits)+2
    lits,c = merge(lits)
    eq = Eq(lits,parse(Int,st[bid])-c)
    return eq
end
function readobj(st,varmap)
    return readlits(st,varmap,2:2:length(st)-1)
end
function remove(s,st)
    r = findall(x->x==s,st)
    deleteat!(st,r)
end
function readopb(path,file)
    system = Eq[]
    varmap = String[]
    obj = ""
    open(string(path,'/',file,".opb"),"r"; lock = false) do f
        for ss in eachline(f)
            if ss[1] != '*'                                 # do not parse comments
                st = split(ss,keepempty=false)              # structure of a line is: int var int var ... >= int ; 
                if ss[1] == 'm'
                    obj = readobj(st,varmap)
                else
                    eq = readeq(st,varmap)
                    if length(eq.t)==0 && eq.b==1
                        printstyled(" !opb"; color = :blue)
                    end
                    normcoefeq(eq)
                    push!(system, eq)
                end
            end
        end
    end
    return system,varmap,obj
end
function normcoef(l)
    if l.coef<0
        l.coef = -l.coef
        l.sign = !l.sign
        return l.coef
    end
    return 0
end
function normcoefeq(eq)
    c=0
    for l in eq.t
        c+= normcoef(l)
    end
    eq.b = c+eq.b
end
function normcoefsystem(s)
    for eq in s
        normcoefeq(eq)
    end
end
function normlit(l)
    if !l.sign
        return Lit(-l.coef,true,l.var),l.coef
    end
    return l,0
end
function add(lit1,lit2)
    lit1,c1 = normlit(lit1)
    lit2,c2 = normlit(lit2)
    return Lit(lit1.coef+lit2.coef,true,lit1.var),c1+c2
end
function removenulllits(lits)
    return [l for l in lits if l.coef!=0]
end
function addeq(eq1,eq2)
    lits = copy(eq2.t)
    vars = [l.var for l in lits]
    c = 0
    for lit in eq1.t
        i = findfirst(x->x==lit.var,vars)
        if !isnothing(i)
            tmplit,tmpc = add(lit,lits[i])
            lits[i] = tmplit
            c+=tmpc
        else
            push!(lits,lit)
        end
    end
    lits=removenulllits(lits)
    # lits=sort(lits,lt=islexicolesslit)                          # optionnal sorting of literrals
    return Eq(lits,eq1.b+eq2.b-c)
end
function multiply(eq,d)
    lits = copy(eq.t)
    for l in lits
        l.coef = l.coef*d
    end
    return Eq(lits,eq.b*d)
end
function divide(eq,d)
    normcoefeq(eq)
    lits = copy(eq.t)
    for l in lits
        l.coef = ceil(Int,l.coef/d)
    end
    return Eq(lits,ceil(Int,eq.b/d))
end
function weaken(eq,var)                                            # coef should be > 0
    lits = copy(eq.t)
    b = eq.b
    for l in lits
        if l.var==var
            b-=l.coef
            l.coef = 0
        end
    end
    lits = removenulllits(lits) 
    return Eq(lits,b)
end
function saturate(eq)
    for l in eq.t
        l.coef = min(l.coef,eq.b)
    end
end
function copyeq(eq)
    return Eq([Lit(l.coef,l.sign,l.var) for l in eq.t], eq.b)
end
function solvepol(st,system,link,init,varmap)
    id = parse(Int,st[2])
    if id<1
        id = init+id
    end
    eq = copyeq(system[id])
    stack = Vector{Eq}()
    weakvar = ""
    push!(stack,eq)
    push!(link,id)
    lastsaturate = false
    noLP = true
    for j in 3:length(st)
        i=st[j]
        if i=="+"
            push!(stack,addeq(pop!(stack),pop!(stack)))     
            push!(link,-1)
        elseif i=="*"
            push!(stack,multiply(pop!(stack),link[end]))
            push!(link,-2)
        elseif i=="d"
            push!(stack,divide(pop!(stack),link[end]))
            push!(link,-3)
            noLP = true
        elseif i=="s"
            noLP = true
            if j == length(st)
                lastsaturate = true
            else
                normcoefeq(first(stack))
                saturate(first(stack))
            end
            push!(link,-4)
        elseif i=="w"
            noLP = true
            push!(stack,weaken(pop!(stack),weakvar))
            push!(link,-5)
        elseif !isdigit(i[1])
            if length(st)>j && st[j+1] == "w"
                weakvar = readvar(i,varmap)
                push!(link,-100weakvar-99) # ATTENTION HARDCODING DE SHIFT
            else
                sign = i[1]!='~'
                var = readvar(i,varmap)
                push!(stack,Eq([Lit(1,sign,var)],0))
                push!(link,-100var-99sign) # ATTENTION HARDCODING DE SHIFT
            end
        elseif i!="0"
            id = parse(Int,i)
            if id<1
                id = init+id
            end
            push!(link,id)
            if !(st[j+1] in ["*","d"])
                push!(stack,copyeq(system[id]))
            end
        end
    end
    eq = pop!(stack)
    lits = eq.t
    lits2 = removenulllits(lits)
    if length(link)==2
        link[1] = -3
    end
    res = Eq(lits2,eq.b)
    if !noLP
        printstyled("POL simplification is hard disabled "; collor = :red)
        # p2 = simplepol(res,system,link)
    end
    if lastsaturate
        normcoefeq(res)
        saturate(res)
    end
    return res
end
function findfullassi(system,st,init,varmap,prism)
    assi = zeros(Int8,length(varmap))
    lits = Vector{Lit}(undef,length(st)-1)
    for i in 2:length(st)
        sign = st[i][1]!='~'
        var = readvar(st[i],varmap)
        lits[i-1] = Lit(1,!sign,var)
        assi[var] = sign ? 1 : 2
    end
    changes = true
    while changes
        changes = false
        for i in 1:init-1 # can be replaced with efficient unit propagation
            if !inprism(i,prism)
                eq = system[i]
                s = slack(eq,assi)
                if s<0
                    printstyled(" !sol"; color = :red)
                    print(" ",i," ")
                    println(st)
                    println(writeeq(eq,varmap))
                    printeq(eq)
                    lits = [Lit(l.coef,!l.sign,l.var) for l in lits]
                    return Eq(lits,1)
                else
                    for l in eq.t                    
                        if l.coef > s && assi[l.var]==0
                            assi[l.var] = l.sign ? 1 : 2
                            changes = true
                        end
                    end
                end
            end
        end
    end
    lits = Vector{Lit}(undef,length(assi))
    for i in eachindex(assi)
        if assi[i]==0
            printstyled(" !FA"; color = :blue)
            println(varmap[i]," not assigned ")
        else
            lits[i] = Lit(1,assi[i]!=1,i) # we add the negation of the assignement
        end
    end
    eq = Eq(lits,1)
    return eq
end
function readwitnessvar(s,varmap)
    if s=="0"
        return 0
    elseif s=="1"
        return -1
    else 
        return readvar(s,varmap)
    end
end
function lparse(f)
    ss = readline(f)
    while length(ss)==0 || ss[1]=='*'
        ss = readline(f)
    end
    st = split(ss,keepempty=false)
    type = st[1]
    return type,st
end
function readwitness(st,varmap)
    remove("->",st)
    remove(";",st)
    t = Vector{Lit}(undef,length(st))
    k = 1
    for i in 1:2:length(st)
        j = i+1
        t[i] = Lit(0,st[i][1]!='~',readwitnessvar(st[i],varmap))
        t[j] = Lit(0,st[j][1]!='~',readwitnessvar(st[j],varmap))
    end
    return t
end
function applywitness(eq,w)
    t = Lit[]
    b = eq.b
    for l in eq.t
        for i in 1:2:length(w)
            if l.var == w[i].var
                if w[i+1].var > 0
                    if l.sign != w[i].sign
                        b-= l.coef
                    end
                else 
                    if l.sign == w[i].sign
                        b-= l.coef
                    end
                end
            else
                push!(t,l)
            end
        end
    end
    return Eq(t,b)
end
function readsubproof(system,systemlink,eq,w,c,f,varmap)
    # notations : 
    # proofgoal i est la i eme contrainte de la formule F /\ ~C /\` ~`Ciw
    # proofgoal #1 est la contrainte dans la reduction
    # -1 est la contrainte qui est declaree dans le proofgoal. elle est affecte par w
    # -2 est la negation de la contrainte declaree dans le red
    # end -1  le -1 donne l'id de la contradiction. on peux aussi mettre c -1
    # l'affectation du temoins refais une nouvelle contrainte.
    nbopb = length(system)-length(systemlink)
    type,st = lparse(f)
    redid = c-1
    pgranges = Vector{UnitRange{Int64}}()
    while type !="end"
        if type == "proofgoal"
            pgid = c
            if st[2][1] == '#' 
                push!(system,reverse(applywitness(eq,w)))
                push!(systemlink,[-7])
            else
                pgref = parse(Int,st[2])
                push!(system,reverse(applywitness(system[pgref],w)))
                push!(systemlink,[-8,pgref])
            end
            c+=1
            type,st = lparse(f)
            while type != "end"
                eq = Eq([],0)
                if type == "u" || type == "rup"
                    eq = readeq(st,varmap,2:2:length(st)-4)     # can fail if space is missing omg
                    push!(systemlink,[-5])
                elseif type == "p" || type == "pol"
                    push!(systemlink,[-6])
                    eq = solvepol(st,system,systemlink[end],c,varmap)
                end
                if length(eq.t)!=0 || eq.b!=0
                    normcoefeq(eq)
                    push!(system,eq)
                    c+=1
                end
                type,st = lparse(f)
            end
            push!(pgranges,pgid:c-1)
        end
        type,st = lparse(f)
    end
    return redid:c-1,pgranges,c
end
function readred(system,systemlink,st,varmap,redwitness,redid,f,prism)
    i = findfirst(x->x==";",st)
    eq = readeq(st[2:i],varmap)
    j = findlast(x->x==";",st)
    if i==j # detect the word begin
        j=length(st)
    end
    w = readwitness(st[i+1:j],varmap)
    c = redid
    range = 0:0
    pgranges = Vector{UnitRange{Int64}}()
    if st[end] == "begin"
        rev = reverse(eq)
        normcoefeq(rev)
        push!(system,rev)
        push!(systemlink,[-9])
        c+=1
        range,pgranges,c = readsubproof(system,systemlink,eq,w,c,f,varmap)
        push!(prism,range)
        push!(systemlink,[-10])
    else
        push!(systemlink,[-4])
    end
    normcoefeq(eq)
    push!(system,eq)
    redwitness[redid] = Red(w,range,pgranges)
    redwitness[length(system)] = Red(w,range,pgranges)
    return c+1
end
function readveripb(path,file,system,varmap,obj)
    systemlink = Vector{Vector{Int}}()
    redwitness = Dict{Int, Red}()
    prism = Vector{UnitRange{Int64}}() # the subproofs should not be available to all
    output = conclusion = ""
    c = length(system)+1
    d = length(system)
    open(string(path,'/',file,extention),"r"; lock = false) do f
        for ss in eachline(f)
            st = split(ss,keepempty=false)
            if length(ss)>0
                type = st[1]
                eq = Eq([],0)
                if type == "u" || type == "rup"
                    eq = readeq(st,varmap,2:2:length(st)-4)     # can fail if space is missing omg
                    push!(systemlink,[-1])
                elseif type == "p" || type == "pol"
                    push!(systemlink,[-2])
                    eq = solvepol(st,system,systemlink[end],c,varmap)
                    if !(length(eq.t)!=0 || eq.b!=0) printstyled("POL empty"; color=:red) end
                elseif type == "ia"
                    l = 0
                    if st[end] == ";" 
                        eq = readeq(st,varmap,2:2:length(st)-4)
                        printstyled("missing ia ID ";color = :red)
                    else
                        eq = readeq(st,varmap,2:2:length(st)-5)
                        l = parse(Int,st[end])
                        if l<0
                            l = c+l
                        end
                    end
                    push!(systemlink,[-3,l])
                elseif type == "red"  
                    c = readred(system,systemlink,st,varmap,redwitness,c,f,prism)
                    eq = Eq([],0)
                elseif type == "sol" 
                    printstyled("SAT Not supported."; color=:red)
                    eq = Eq([Lit(0,true,1)],15) # just to add something to not break the id count
                elseif type == "soli" 
                    printstyled("BOUNDS Not supported(soli) "; color=:red)
                    # push!(systemlink,[-6])
                    # eq = findbound(system,st,c,varmap,obj)
                    eq = Eq([Lit(0,true,1)],15) # just to add something to not break the id count
                elseif type == "solx"         # on ajoute la negation de la sol au probleme pour chercher d'autres solutions. jusqua contradiction finale. dans la preuve c.est juste des contraintes pour casser toutes les soloutions trouvees
                    push!(systemlink,[-20])
                    eq = findfullassi(system,st,c,varmap,prism)
                elseif type == "output"
                    output = st[2]
                elseif type == "conclusion"
                    conclusion = st[2]
                    if conclusion == "BOUNDS"
                        printstyled("BOUNDS Not supported. "; color=:red)
                    elseif !isequal(system[end],Eq([],1)) && (conclusion == "SAT" || conclusion == "NONE")
                        printstyled("SAT Not supported.."; color=:red)
                    end
                elseif !(type in ["*trim","#","w","*","f","d","del","end","pseudo-Boolean"])#,"de","co","en","ps"])
                    printstyled("unknown2: ",ss; color=:red)
                end
                if length(eq.t)!=0 || eq.b!=0
                    normcoefeq(eq)
                    push!(system,eq)
                    c+=1
                end
            end
        end
    end
    return system,systemlink,redwitness,output,conclusion,version
end




main()