
#=    Instances managements    =#

function okinstancelist()
    type = "LV"
    cd()
    list = cd(readdir, proofs)
    # list = [s[1:end-4] for s in list if s[end-3:end]==".opb" && s[1:3]=="bio"]
    list = [s[1:end-4] for s in list if s[end-3:end]==".opb" && s[1:3]=="LVg"]
    list = [s for s in list if isfile(string(proofs,"/",s,extention))]
    list = [s for s in list if read(`tail -n 1 $proofs/$s$extention`,String) == "end pseudo-Boolean proof\n"]
    list = [s for s in list if read(`tail -n 2 $proofs/$s$extention`,String)[1:14] != "conclusion SAT"]
    stats = [stat(string(path,"/",file,".opb")).size + stat(string(proofs,"/",file,extention)).size for file in list]

    println(list)
    p = sortperm(stats)
    # listm = [list[i] for i in eachindex(list) if stats[i] > 1_000_000]
    open(string(proofs,"/a",type,"list.jl"),"w") do f
        write(f,string("const ",type,"list = [\"",list[1],"\""))
        for i in 2:length(list) 
            write(f,string(",\"",list[i],"\""))
        end
        write(f,string("]\n"))
        write(f,string("const ",type,"stats = [",stats[1]))
        for i in 2:length(list) 
            write(f,string(",",stats[i]))
        end
        write(f,string("]\n"))
    end
end
function solve(ins,pathpat,pattern,pathtar,target,format,minsize=2_000_000,timeout=1,remake=false,verbose=false)
    if remake || !isfile(string(proofs,"/",ins,".opb")) || !isfile(string(proofs,"/",ins,extention)) || 
            length(read(`tail -n 1 $proofs/$ins$extention`,String)) < 24 ||
            read(`tail -n 1 $proofs/$ins$extention`,String)[1:24] != "end pseudo-Boolean proof"
        print(ins,' ')
        t = @elapsed begin
            # p = run(pipeline(`timeout $timeout ./$solver --prove $proofs/$ins --no-supplementals --no-clique-detection --format $format $pathpat/$pattern $pathtar/$target`, devnull),wait=false); wait(p)
            if verbose
                p = run(pipeline(`timeout $timeout ./$solver --prove $proofs/$ins --no-clique-detection --format $format $pathpat/$pattern $pathtar/$target`),wait=true);
            else
                p = run(pipeline(`timeout $timeout ./$solver --prove $proofs/$ins --no-clique-detection --format $format $pathpat/$pattern $pathtar/$target`, devnull),wait=false); wait(p)
            end
        end
        t+=0.01
        ok = false
        print(prettytime(t))
        if t>timeout
            printstyled(" timeout "; color = :red)
        elseif read(`tail -n 2 $proofs/$ins$extention`,String)[1:14] == "conclusion SAT"
            printstyled(" sat     "; color = 166)
        elseif minsize > stat(string(proofs,"/",ins,extention)).size            
            printstyled(" toosmal "; color = :yellow)
        else printstyled(" OK      "; color = :green)
            ok = true
            # g = ladtograph(pathpat,pattern)
            # draw(PNG(string(proofs,"/aimg/graphs/",ins,pattern[1:3],".png"), 16cm, 16cm), gplot(g))
            # g = ladtograph(pathtar,target)
            # draw(PNG(string(proofs,"/aimg/graphs/",ins,target[1:3],".png"), 16cm, 16cm), gplot(g))
        end
        println()
        if !ok
            run(`rm -f $proofs/$ins$extention`)
            run(`rm -f $proofs/$ins.opb`)
        end
    end
end
function run_bio_solver()
    path = string(benchs,"/biochemicalReactions")
    cd()
    graphs = cd(readdir, path)
    n = length(graphs)
    for target in graphs[1:end], pattern in graphs[1:end]
        # target = graphs[rand(1:n)]
        # pattern = graphs[rand(1:n)]
        if pattern != target
            ins = string("bio",pattern[1:end-4],target[1:end-4])
            solve(ins,path,pattern,path,target,"lad")
        end
    end
end
function run_si_solver() # all sat or timeout
    sipath = string(benchs,"/si")
    cd()
    inst = cd(readdir, string(sipath))
    for ins in inst
        inst2 = cd(readdir, string(sipath,"/",ins))
        for ins2 in inst2
            solve(ins2,string(sipath,'/',ins,'/',ins2,),"pattern",string(sipath,'/',ins,'/',ins2),"target","lad")
        end
    end
end
function run_LV_solver()
    path = string(benchs,"/LV")
    cd()
    for i in 51:112
        for j in 2:50
            target = string('g',i)
            pattern = string('g',j)
            ins = string("LV",pattern,target)
            if ins in LVlist
            solve(ins,path,pattern,path,target,"lad",100000,1,true)
            end
        end
    end
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
function iscontained(e,f) # is e contained in f so that f only has more litteral axioms
    printeq(e)
    printeq(f)
    if e.b!=f.b
        return false
    elseif length(e.t) < length(f.t)
        return false
    else
        j=1
        for l in e.t
            search = true
            l2 = f.t[j]
            while search
                # TODO
                l2 = f.t[j]
            end
            if !isequal(l,l2)

            end
        end
        return true
    end
end
function getid(eq,a,b,system)
    for i in a:b
        if iscontained(eq,system[i])
            return i
        end
    end
end

#=    Stat prints   =#


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
function printsys(system)
    for id in eachindex(system)
        print(id," ")
        printeq(system[id])
    end
end
function printcone(system,systemlink,cone) 
    for id in eachindex(system)
        if cone[id]
            print(id," ")
            if isassigned(systemlink,id)
                if systemlink[id][1]==-1
                    print("sol ")
                end
            end
            printeq(system[id])
        end
    end
end
function writelit(l,varmap)
    return string(l.coef," ",if l.sign "" else "~" end, varmap[l.var])
end
function writeeq(e,varmap)
    s = ""
    for l in e.t
        s = string(s,writelit(l,varmap)," ")
    end
    return string(s,">= ",e.b," ;\n")
end
function writeu(e,varmap)
    return string("u ",writeeq(e,varmap))
end
function writeiaold(e,link,cone,varmap)
    return string("ia ",sum(cone[1:link])," : ",writeeq(e,varmap))
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
function isid(link,k)                 # dont put mult and div coefficients as id and weakned variables too
    return link[k]>0 && (k==length(link)||(link[k+1] != -2 && link[k+1] != -3))
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
                    write(f,writered(eq,varmap,redwitness[i],""))
                    # writedel(f,systemlink,i,succ,index,nbopb,dels) # since simple red have no antecedants, they cannot trigger deletions ie they cannot be the last successor of a previous eq
                    dels[i] = true  # we dont delete red statements
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
                    dels[i] = true  # we dont delete red statements
                elseif tlink == -7           # red proofgoal #
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
function writerepartition(path,file,cone,nbopb)
    open(string(path,"/repartition"), "a") do f
        write(f,string(file,"\n"))
        for i in eachindex(cone)
            if cone[i] 
                write(f,string("1"))
            else
                write(f,string("."))
            end
            if i==nbopb
                write(f,string("\n"))
            end
        end
        write(f,string("\n"))
    end
end
function writeshortrepartition(path,file,cone,nbopb)
    if nbopb>100 && length(cone)-nbopb>100
        open(string(path,"/arepartition"), "a") do f
            chunk = nbopb ÷ 100
            proofchunk = (length(cone)-nbopb) ÷ 100
            write(f,string(file," opb and proof chunks are :",chunk," ",proofchunk,"\n"))
            s = 0
            j = 1
            for i in eachindex(cone)
                if cone[i] 
                    s += cone[i]
                end
                if i-j==chunk
                    if s == 0
                        write(f,string("."))
                    else
                        write(f,string(" ",100s÷chunk))
                    end
                    s = 0 
                    j = i
                end
                if i==nbopb
                    write(f,string(" ",s,"\n"))
                    chunk = proofchunk
                    s = 0
                    j = i
                end
            end
            write(f,string(" ",s,"\n"))
        end
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
function delindividualist(g)
    i = findfirst(v->degree(g,v)==0,vertices(g))
    while !(i === nothing)
        rem_vertex!(g, i)
        i = findfirst(v->degree(g,v)==0,vertices(g))
    end
end
function makeg2win(g)
    n = nv(g)
    g2 = SimpleGraph(n,0)
    for i in vertices(g)
        for j in neighbors(g, i)
            for k in neighbors(g, j)
                add_edge!(g2,i,k)
            end
        end
    end
    return g2
end 
function add_nei(deb,cur,l,g,A)
    if k == 0 A[deb,cur] +=1 
    else
        for nei in neighbors(g, cur)
            add_nei(deb,nei,l-1,g,A)
        end
    end
end
function makegkwin(g,k) return makegkwin(g,2,k) end
function makegkwin(g,l,k) # l length of path (default 2); k number of paths
    n = nv(g)
    A = zeros(Int,n,n)
    gg = [SimpleGraph(n,0) for _ in 1:k]
    for i in vertices(g)
        add_nei(i,i,l,g,A)
    end
    for occ in 1:k
        for i in 1:n
            for j in i:n
                if A[i,j]>=occ
                    add_edge!(gg[occ],i,j)
                end
            end
        end
    end
    return gg
end 
function printcom(file,system,invsys,cone,com)
#print the type of the trimed constraints from the coms of the solver and the adjacency graphs.
    names = [
        "backtrack", "backtrackbin", "backtrackbincolor", "disconnected",
        "degre", "hall", "nds", "nogood", "loops", "fail", "colorbound",
        "adjacencyhack", "adjacencydist1", "adjacencydist2", "adjacencydist3",
        "adjacency", "adjacency0", "adjacency1", "adjacency2", "adjacency3", "adjacency4"]
    n = length(names)
    og = zeros(Int,n)
    sm = zeros(Int,n)
    # ogg =  SimpleGraph()
    # smg =  SimpleGraph()
    ogd = Dict{Int,SimpleGraph{Int}}()
    smd = Dict{Int,SimpleGraph{Int}}()
    lastadj = 0
    ti = sort!(collect(keys(com)))
    for i in ti#eachindex(com)
        s = com[i]
        st = split(s,keepempty=false)
        type = string(st[1])
        removespaces(st)
        j = findfirst(isequal(type),names)
        if j === nothing
            push!(names,type)
            push!(og,1)
            push!(sm,0)
            if cone[i] sm[end]+=1 end
        else
            og[j]+=1
            if cone[i] sm[j]+=1 end
            # if cone[i] 
            #     if type[1:3] == "hal" println("     ",s) end
            #     if type[1:3] == "deg" println("     ",s) end
            # else
            #     if type[1:3] == "hal" println(s) end
            #     if type[1:3] == "deg" println(s) end
            # end
            if type[1:3] == "adj"
                lastadj = i
                v1 = parse(Int,st[2])
                println(v1," ")
                v2 = parse(Int,st[3])
                idg = parse(Int,st[4])
                if !haskey(ogd,idg) ogd[idg] = SimpleGraph() end
                if !haskey(smd,idg) smd[idg] = SimpleGraph() end
                ogg = ogd[idg]
                smg = smd[idg]
                n = size(ogg, 1)
                m = max(v1,v2)
                if m > n 
                    add_vertices!(ogg, m-n)
                    add_vertices!(smg, m-n)
                end
                add_edge!(ogg, v1, v2)
                if cone[i] add_edge!(smg, v1, v2) end
            end
        end
    end
    p = sortperm(names)
    for i in p
        if og[i]>0
            col =  sm[i]==og[i] ? 3 : sm[i]==0 ? 1 : 2
            printstyled(names[i]," ",sm[i],"/",og[i],"\n"; color = col)
        end
    end
    # println(lastadj)
    for i in eachindex(ogd)
        ogg = ogd[i]
        delindividualist(ogg)
        draw(PNG(string(proofs,"/aimg/",file,"-g",i,".png"), 16cm, 16cm), gplot(ogg))
    end
    for i in eachindex(smd)
        smg = smd[i]
        delindividualist(smg)
        if nv(smg)>1
            draw(PNG(string(proofs,"/aimg/",file,"-g",i,".smol.png"), 16cm, 16cm), gplot(smg))
        end
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
function printrepartition(ins,t1,t2)
    println("\\begin{tikzpicture}[xscale=0.5,font=\\sffamily]\n\\node[right] at (0,1.5) {",ins,"};")
    print("\\foreach \\x/\\y in{")
    for i in 1:length(t1)-1
        print(i,"/",t1[i],',')
    end
    print(length(t1),"/",t1[end])
    println("} {\\fill[color=black!\\y] (\\x,0) rectangle (\\x+1,1);\\node at (\\x+0.5,0.5) {\\y};} \\draw (1,0) grid (102,1);")
    print("\\foreach \\x/\\y in{")
    for i in 1:length(t2)-1
        print(i,"/",t2[i],',')
    end
    print(length(t2),"/",t2[end])
    println("} {\\fill[color=black!\\y] (\\x,-1) rectangle (\\x+1,0);\\node at (\\x+0.5,-0.5) {\\y};} \\draw (1,-1) grid (102,0);")
    println("\\end{tikzpicture}") 
end
function readrepartition()
    cko = 0
    ckp = 0
    s = 0
    t1 = [0 for i in 1:101]
    t2 = [0 for i in 1:101]
    Σ1 = [0 for i in 1:101]
    Σ2 = [0 for i in 1:101]
    nb1 = 0
    nb2 = 0
    cd()
    println("\\documentclass[tikz,border=5mm]{standalone}\n\\begin{document}")
    open(string(proofs,'/',"arepartition"),"r"; lock = false) do f
        for ss in eachline(f)
            if ss!="" && ss[1] != ' ' && ss[1] != '.'
                st  = split(ss,keepempty=false)
                cko = parse(Int,st[end-1][2:end])
                ckp = parse(Int,st[end])
                ins = string(st[1]," (opb chunk size:",cko,") (pbp chunk size:",ckp,')')
                ss = readline(f)
                ss = replace(ss,'.'=>" 0")
                st = split(ss,keepempty=false)
                # removespaces(st)
                for i in 1:101
                    v = cko>0 ? parse(Int,st[i]) : 100
                    t1[i] = v
                    Σ1[i] +=v
                end
                nb1 += 1
                ss = readline(f)
                ss = replace(ss,'.'=>" 0")
                st = split(ss,keepempty=false)
                # removespaces(st)
                for i in 1:101
                    ckp>0 ? parse(Int,st[i]) : 100
                    v =  parse(Int,st[i])
                    t2[i] = v
                    Σ2[i] +=v
                end
                nb2 += 1
                printrepartition(ins,t1,t2)
            end
        end
    end
    ins =  string("Mean ",nb1,' ',nb2)
    st = Σ1./nb1
    for i in 1:101
        v =  round(Int,st[i])
        t1[i] = v
        nb1 += 1
    end
    st = Σ2./nb2
    for i in 1:101
        v =  round(Int,st[i])
        t2[i] = v
        nb2 += 1
    end
    printrepartition(ins,t1,t2)
    println("\\end{document}")
    # return Σ./nb
end
function printcone(cone,nbopb)
    for i in nbopb+1:length(cone)
        if cone[i]
            print('1')
        else
            print('_')
        end
    end
    println()
end
function mkdir2(p) if !isdir(p) mkdir(p) end end
function printorder(file,cone,invsys,varmap)
    n = 30 # limit the number of most used var
    # varocc = [length(i) for i in invsys] # order from var usage
    # p = sortperm(varocc,rev=true)
    # for i in 1:min(n,length(varmap))
    #     j = p[i]
    #     var = varmap[j]
    #     occ = varocc[j]
    #     print(var," ")
    # end
    # println("Var order from usage in cone :")
    s = "map<string,int> order { "     
    varocc = [sum(cone[j] for j in i) for i in invsys] # order from var usage in cone
    p = sortperm(varocc,rev=true)
    for i in eachindex(varmap)
        j = p[i]
        var = varmap[j]
        occ = varocc[j]
        s = string(s,"{\"",var,"\",",occ,"}, ")
        if i<n
            # print(var," ")
        end
    end
    s = s[1:end-2]*"};"
    dir = string(proofs,"/cone_var_order/")
    mkdir2(dir)
    open(string(dir,file,".cc"),"w") do f
        write(f,s)
    end
    # println()
    return varocc
end
function printsummit(cone,invsys,varmap)
    max1 = 0
    maxi = Int[]
    smax = 0
    smaxi = Int[]
    for i in eachindex(invsys)
        link = invsys[i]
        if length(link)>max1
            max1 = length(link)
            # maxi = i
        end
        s = sum(cone[j] for j in link)
        if s>smax
            smax = s
            # smaxi = i
        end 
    end
    for i in eachindex(invsys)
        link = invsys[i]
        if length(link)==max1
            push!(maxi,i)
        end
        s = sum(cone[j] for j in link)
        if s==smax
            push!(smaxi,i)
        end
    end
    max2 = 0
    for i in smaxi
        max2 = max(max2,length(invsys[i]))
    end
    max3 = 0
    for i in maxi
        max3 = max(max3,sum(cone[j] for j in invsys[i]))
    end
    println("summit:     ",varmap[max1],' ',maxi)
    println("smolsummit: ",smax,' ',smaxi,' ',max2,' ',max3)
end
function varcone(system,cone,varmap)
    vcone = zeros(Bool,length(varmap))
    for i in eachindex(system)
        if cone[i]
            eq = system[i]
            for l in eq.t
                vcone[l.var] = true
            end
        end
    end
    return vcone
end
function printvarcone(vcone,varmap)
    for i in eachindex(varmap)
        if vcone[i]
            println(varmap[i])
        end
    end
end
function patterntargetcone(varcone,varmap)
    patcone = Set{Int}()
    tarcone = Set{Int}()
    for i in findall(varcone)
        s = varmap[i]
        st = split(s,'_',keepempty=false)
        p = parse(Int,st[1][2:end])
        t = parse(Int,st[2])
        push!(patcone,p)
        push!(tarcone,t)
    end
    return patcone,tarcone
end
function printbioconegraphs(ins,cone,patcone,tarcone)
    benchs = "veriPB/newSIPbenchmarks"

    path = string(benchs,"/biochemicalReactions")
    cd()
    pattern = string(ins[4:6],".txt")
    target = string(ins[7:9],".txt")
    gp = ladtograph(path,pattern)
    gt = ladtograph(path,target)
    # draw(PNG(string(proofs,"/aimg/graphs/",pattern[1:3],".png"), 16cm, 16cm), gplot(gp))
    # draw(PNG(string(proofs,"/aimg/graphs/", target[1:3],".png"), 16cm, 16cm), gplot(gt))

    pc = patcone.+1
    # println(pc)
    # println(nv(gp))
    delp = [i for i in 1:nv(gp) if !(i in pc)]
    # println(delp)
    tc = tarcone.+1
    # println(tc)
    # println(nv(gt))
    delt = [i for i in 1:nv(gt) if !(i in tc)]
    # println(delt)
    rem_vertices!(gp, delp, keep_order=true)
    rem_vertices!(gt, delt, keep_order=true)
    if length(delp)>0
        draw(PNG(string(proofs,"/aimg/graphs/",pattern[1:3],ins,".png"), 16cm, 16cm), gplot(gp))
        gp = ladtograph(path,pattern)
        draw(PNG(string(proofs,"/aimg/graphs/",pattern[1:3],".png"), 16cm, 16cm), gplot(gp))    
    end
    if length(delt)>0
        draw(PNG(string(proofs,"/aimg/graphs/", target[1:3],ins,".png"), 16cm, 16cm), gplot(gt))
        gt = ladtograph(path,target)
        draw(PNG(string(proofs,"/aimg/graphs/", target[1:3],".png"), 16cm, 16cm), gplot(gt))    
    end
end

# using JuMP,GLPK

function LPpol(a,b,asol,bsol)
    # nbctr = size(a,1)
    # nbvar = size(a,2)
    # m = Model()
    # set_optimizer(m,GLPK.Optimizer)

    # @variable(m,lambda[i = 1:nbctr] >=0,Int)
    # @variable(m,lambdaBin[i = 1:nbctr], Bin)
    
    # @constraint(m, ctr_milp1[j in 1:nbvar], sum(a[i,j]*lambda[i] for i in 1:nbctr) == asol[j])
    # @constraint(m, ctr_milp2, sum(lambda[i] * b[i] for i in 1:nbctr) == bsol)
    # @constraint(m, ctr_milp_flag[i in 1:nbctr], lambda[i] <= lambdaBin[i] * 2^16) # 2^64 
    
    # @objective(m, Min, sum(lambdaBin[i] for i in 1:nbctr))

    # # print(m)
    # optimize!(m)
    # if objective_value(m) < nbctr
    #     for i in 1:nbctr
    #         println(value(lambda[i]))
    #     end
    # else
    #     print('|')
    # end
end
# a = [ 1 0 0 4; -2 3 0 -5; 1 0 0 4; 0 -1 0 1]
# b = [1,-2,1,2]
# asol = [0 0 0 6]
# bsol = 6
# LPpol(a,b,asol,bsol)

function simplepol(res,system,link)
    if !(-3 in link[1:end-1]) && !(-4 in link)
        # println(link)
    varset = Vector{Int}()
    ctrs = [i for i in link if i>0]
    nbctr = length(ctrs)
    for i in ctrs
        for l in system[i].t
            if !(l.var in varset)
                push!(varset,l.var)
            end
        end
    end
    sort!(varset)
    # println(varset)
    nbvar = length(varset)
    a = zeros(Int,nbctr,nbvar)
    b = zeros(Int,nbctr)
    eq0 = Eq([Lit(0,true,v) for v in varset],0)
    for i in eachindex(ctrs)
        id = ctrs[i]
        eq = system[id]
        eq = addeq(eq,eq0)
        for l in eq.t
            a[i,findfirst(isequal(l.var),varset)] = l.coef
        end
        b[i] = eq.b
    end
    aeq = addeq(res,eq0)
    avars = [l.var for l in aeq.t]
    asol = zeros(Int,nbvar)
    for i in eachindex(varset)
        v = varset[i]
        j = findfirst(x->x==v,avars)
        if !(j === nothing)
            asol[i] = aeq.t[j].coef
        end
    end
    bsol = aeq.b
    # println(a)
    # println(asol)
    # println(b)
    # println(bsol)
    # a = [ 1 0 0 4; -2 3 0 -5; 1 0 0 4; 0 -1 0 1]
    # b = [1,-2,1,2]
    # asol = [0 0 0 3]
    # bsol = 6
    LPpol(a,b,asol,bsol)

    end
    return link
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
                    write(f,string(wid(lastindex),"ia ",writeeqcolor(e,varmap,varocc,m,r)[1:end-1]," ",lid(index[systemlink[i-nbopb][2]]),"\n"))
                    write(f,printpred(i,systemlink[i-nbopb],nbpred,maxpred,index,nbopb))
                    write(f,printsucc(i,succ[i],nbsucc,maxsucc,index))
                    writedelcolor(f,systemlink,i,succ,index,nbopb,dels)
                elseif tlink == -4           # red alone
                    write(f,string(wid(lastindex),writeredcolor(eq,varmap,redwitness[i],"",varocc,m,r)))
                    write(f,printpred(i,systemlink[i-nbopb],nbpred,maxpred,index,nbopb))
                    write(f,printsucc(i,succ[i],nbsucc,maxsucc,index))
                    # writedel(f,systemlink,i,succ,index,nbopb,dels) # since simple red have no antecedants, they cannot trigger deletions ie they cannot be the last successor of a previous eq
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
function conegraphviz(file,cone,index,systemlink,succ,nbopb)
    dir = string(proofs,"/cone_graphviz/")
    mkdir2(dir)
    open(string(dir,file,".dot"),"w") do f
        write(f,"digraph G {\n splines=false;\nedge [color=lightgray];\n")
        for i in findall(cone)
            if isassigned(succ,i)
                for j in succ[i]
                    write(f,string(index[i],"->",index[j],";\n"))
                end
            end
        end
        write(f,"}")
    end
    t = @elapsed begin
        v2 = read(`dot -O -T svg $proofs/cone_graphviz/$file.dot `) 
    end
    if t>5
        println("graph sorted in ",prettytime(t)," s")
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



# letter analysis
# jakob using resolution proofs to analyze cdcl 2020 cp
# kuldep meel crystalball