
mutable struct Lit
    coef::Int
    sign::Bool
    var::Int
end
mutable struct Eq
    t::Vector{Lit}
    b::Int
end
function printlit(l)
    printstyled(l.coef,' '; color = :blue)
    if !l.sign printstyled('~'; color = :red) end
    printstyled(l.var; color = :green)
end
function printeq(e)
    for l in e.t
        print("  ")
        printlit(l)
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
function readvar(s,varmap)
    tmp = split(s,'~')[end]
    for i in eachindex(varmap)
        if varmap[i]==tmp
            return i
        end
    end
    push!(varmap,tmp)
    return length(varmap)
end
function readeq(st,varmap)
    return readeq(st,varmap,1:2:length(st)-3)
end
function readeq(st,varmap,range)
    lits = Vector{Lit}(undef,(length(range)))
    for i in range
        coef = parse(Int,st[i])
        sign = st[i+1][1]!='~'
        var = readvar(st[i+1],varmap)
        lits[(i - range.start)÷range.step+1] = Lit(coef,sign,var)
    end
    eq = Eq(lits,parse(Int,st[end-1]))
    return eq
end
function removespaces(st)
    r = findall(x->x=="",st)
    deleteat!(st,r)
end
function readopb(path,file)
    system = Eq[]
    varmap = String[]
    open(string(path,'/',file,".opb"),"r"; lock = false) do f
        for ss in eachline(f)
            if ss[1] != '*'                                     #do not parse comments
                st = split(ss,' ')                              #structure of line is: int var int var ... >= int ; 
                removespaces(st)
                eq = readeq(st,varmap)
                if length(eq.t)==0 && eq.b==1
                    printstyled(" !opb"; color = :blue)
                end
                normcoefeq(eq)
                push!(system, eq)
            end
        end
    end
    return system,varmap
end
function normlit(l)
    if !l.sign
        return Lit(-l.coef,true,l.var),l.coef
    end
    return l,0
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
    lits = copy(eq.t)
    for l in lits
        l.coef = ceil(Int,l.coef/d)
    end
    return Eq(lits,ceil(Int,eq.b/d))
end
function saturate(eq)
    for l in eq.t
        l.coef = min(l.coef,eq.b)
    end
end
function solvepol(st,system,link)
    id = parse(Int,st[2])
    eq = deepcopy(system[id])
    stack = [eq]
    push!(link,id)
    for j in 3:length(st)
        i=st[j]
        if i=="+"
            stack[end] = addeq(pop!(stack),stack[end])      #order is important for stack
            push!(link,-1)
        elseif i=="*"
            stack[end] = multiply(stack[end],systemlink[c][end])
            push!(link,-2)
        elseif i=="d"
            stack[end] = divide(stack[end],systemlink[c][end])
            push!(link,-3)
        elseif i=="s"
            normcoefeq(stack[end])
            saturate(stack[end])
            push!(link,-4)
        elseif i=="w"
            printstyled(" !weak"; color = :blue)
        elseif i!="0"
            id = parse(Int,i)
            push!(link,id)
            if !(st[j+1] in ["*","d"])
                push!(stack,deepcopy(system[id]))    
            end
        end
    end
    eq = pop!(stack)
    lits = eq.t
    lits2 = removenulllits(lits)
    if length(link)==2
        link[1] = -3
    end
    return Eq(lits2,eq.b)
end
function findfullassi(system,st,init,varmap)
    isassi,assi = initassignement(varmap)
    lits = Vector{Lit}(undef,length(st)-1)
    for i in 2:length(st)
        sign = st[i][1]!='~'
        var = readvar(st[i],varmap)
        lits[i-1] = Lit(1,!sign,var)
        assi[var] = sign
        isassi[var] = true
    end
    changes = true
    while changes
        changes = false
        for i in 1:init-1
            eq = system[i]
            s = slack(eq,isassi,assi)
            if s<0
                printstyled(" !sol"; color = :red)
                print(" ",i," ")
                printeq(eq)
                lits = [Lit(l.coef,!l.sign,l.var) for l in lits]
                return Eq(lits,1)
            else
                for l in eq.t
                    if !isassi[l.var] && l.coef > s
                        assi[l.var] = l.sign
                        isassi[l.var] = true 
                        changes = true
                    end
                end
            end
        end
    end

    lits = Vector{Lit}(undef,sum(isassi))
    j=1
    for i in findall(isassi)
        lits[j] = Lit(1,!assi[i],i)
        j+=1
    end
    eq = Eq(lits,1)
    if sum(isassi)!=length(isassi)
        printstyled(" !FA"; color = :blue)
        printeq(eq)
    end
    return eq
end
function readred(st,varmap,redwitness,c)
    i = findfirst(x->x==";",st)
    eq = readeq(st[2:i],varmap)
    redwitness[c] = join(st[i+1:end]," ")
    return eq
end
function readveripb(path,file,system,varmap)
    systemlink = Vector{Int}[]
    redwitness = Dict{Int, String}()
    version = output = conclusion = ""
    version = "2.0" #split(s[1],' ')[end]
    c = length(system)
    open(string(path,'/',file,".veripb"),"r"; lock = false) do f
        c+=1
        for ss in eachline(f)
            st = split(ss,' ')
            removespaces(st)
            eq = Eq([],0)
            if ss[1:2] == "u " || ss[1:3] == "rup"
                eq = readeq(st,varmap,2:2:length(st)-3)
                push!(systemlink,[-1])
            elseif ss[1:2] == "p " || ss[1:3] == "pol"
                push!(systemlink,[-2])
                eq = solvepol(st,system,systemlink[end])
            elseif ss[1:2] == "ia"
                push!(systemlink,[-3,parse(Int,st[2])])
                eq = readeq(st,varmap,4:2:length(st)-3)
            elseif ss[1:3] == "red"  
                push!(systemlink,[-4])
                eq = readred(st,varmap,redwitness,c)
            elseif ss[1:3] == "sol"                                  # on ajoute la negation au probleme pour chercher d'autres solutions. jusqua contradiction finale. dans la preuve c.est juste des contraintes pour casser toutes les soloutions trouvees
                push!(systemlink,[-5])
                eq = findfullassi(system,st,c,varmap)
            elseif st[1] == "output"
                output = st[2]
            elseif st[1] == "conclusion"
                conclusion = st[2]
            elseif !(ss[1:2] in ["# ","w ","ps","* ","f ","d ","de","co","en"])
                println("unknown: ",ss)
            end
            if length(eq.t)!=0 || eq.b!=0
                normcoefeq(eq)
                push!(system,eq)
            end
        end
    end
    return system,systemlink,redwitness,output,conclusion,version
end
function slack(eq::Eq,isassi::Vector{Bool},assi::Vector{Bool})
    c=0
    for l in eq.t
        if isassi[l.var]
            if assi[l.var] == l.sign
                c+=l.coef 
            end
        else
            c+=l.coef
        end
    end
    if length(eq.t) > 0
        c-= eq.b
    end
    return c
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
function initassignement(invsys)
    l = length(invsys)
    return zeros(Bool,l),zeros(Bool,l)
end
function reset(mats)
    for mat in mats
        mat .=false
    end
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
function makesmol(system,invsys,systemlink,nbopb)
    n = length(system)
    antecedants = zeros(Bool,n)
    isassi,assi = initassignement(invsys)
    cone = zeros(Bool,n)
    cone[end] = true
    front = zeros(Bool,n)
    firstcontradiction = findfirst(x->length(x.t)==0,system)
    cone[firstcontradiction] = true
    if systemlink[firstcontradiction-nbopb][1] == -2         # pol case
        fixfront(front,systemlink[firstcontradiction-nbopb])
    else
        updumb(system,invsys,front)                     #front now contains the antecedants of the final claim
        append!(systemlink[firstcontradiction-nbopb],findall(front))
    end
    # print("  init : ",sum(front))#,findall(front))
    while true in front
        i = findlast(front)
        front[i] = false
        if !cone[i] 
            cone[i] = true
            if i>nbopb
                tlink = systemlink[i-nbopb][1]
                if tlink == -1 
                    antecedants .=false ; isassi .=false ; assi.=false
                    rupdumb(system,antecedants,i,isassi,assi)
                    append!(systemlink[i-nbopb],findall(antecedants))
                    fixfront(front,antecedants)
                elseif tlink >= -3
                    antecedants .= false
                    fixante(systemlink,antecedants,i-nbopb)
                    fixfront(front,antecedants)
                end
            end
        end
    end
    return cone
end
function updumb(system,invsys,antecedants)
    isassi,assi = initassignement(invsys)
    changes = true
    while changes
        changes = false
        for i in eachindex(system)
            eq = system[i]
            s = slack(eq,isassi,assi)
            if s<0
                antecedants[i] = true
                return 
            else
                for l in eq.t
                    if !isassi[l.var] && l.coef > s
                        assi[l.var] = l.sign
                        isassi[l.var] = true 
                        antecedants[i] = true
                        changes = true
                    end
                end
            end
        end
    end
    printstyled(" updumb Failed "; color = :red)
end
function rupdumb(system::Vector{Eq},antecedants::Vector{Bool},init,isassi::Vector{Bool},assi::Vector{Bool})
    rev = reverse(system[init])
    changes = true
    while changes
        changes = false
        for i in 1:init
            eq = i==init ? rev : system[i]
            s = slack(eq,isassi,assi)
            if s<0
                antecedants[i] = true
                return 
            else
                for l in eq.t
                    if !isassi[l.var] && l.coef > s
                        assi[l.var] = l.sign
                        isassi[l.var] = true 
                        antecedants[i] = true
                        changes = true
                    end
                end
            end
        end
    end
    printstyled("!rup "; color = :red)
end
function readinstance(path,file)
    system,varmap = readopb(path,file)
    nbopb = length(system)
    system,systemlink,redwitness,output,conclusion,version = readveripb(path,file,system,varmap)
    return system,systemlink,redwitness,nbopb,varmap,output,conclusion,version
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
function writeia(e,link,cone,varmap)
    return string("ia ",sum(cone[1:link])," : ",writeeq(e,varmap))
end
function writesol(e,varmap)
    s = "solx"
    for l in e.t
        s = string(s,if l.sign " ~" else " " end, varmap[l.var])
    end
    return string(s,"\n")
end
function writered(e,varmap,witness)
    s = "red"
    for l in e.t
        s = string(s," ",l.coef,if !l.sign " ~" else " " end, varmap[l.var])
    end
    return string(s," >= ",e.b," ; ",witness,"\n")
end
function writepol(link,cone)
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
        elseif t>0
            if link[i+1] in [-2,-3]
                s = string(s," ",t)
            else
                s = string(s," ",sum(cone[1:t]))
            end
        end
    end
    return string(s,"\n")
end
function invlink(systemlink,succ::Vector{Vector{Int}},nbopb)
    for i in eachindex(systemlink)
        if isassigned(systemlink,i)
            t = systemlink[i]
            for j in t
                if j>0
                    if isassigned(succ,j)
                        push!(succ[j],i+nbopb)
                    else
                        succ[j] = [i+nbopb]
                    end
                end
            end
        end
    end
end
function writedel(f,systemlink,i,succ,cone,nbopb,dels)
    isdel = false
    for p in systemlink[i-nbopb]
        if p>nbopb && !dels[p] 
            m = maximum(succ[p])
            if m == i
                if !isdel
                    write(f,string("del id "))
                    isdel = true
                end
                dels[p] = true
                write(f,string(sum(cone[1:p])," "))
            end
        end
    end
    if isdel
        write(f,string("\n"))
    end
end
function writeconedel(path,file,extention,version,system,cone,systemlink,redwitness,nbopb,varmap,output,conclusion)
    open(string(path,"/smol.",file,".opb"),"w") do f
        for i in 1:nbopb
            if cone[i]
                eq = system[i]
                write(f,writeeq(eq,varmap))
            end
        end
    end
    succ = Vector{Vector{Int}}(undef,length(system))
    dels = zeros(Bool,length(system))
    invlink(systemlink,succ,nbopb)
    open(string(path,"/smol.",file,extention),"w") do f
        write(f,string("pseudo-Boolean proof version ",version,"\n"))
        write(f,string("f ",sum(cone[1:nbopb])," 0\n"))
        for i in nbopb+1:length(system)
            if cone[i]
                eq = system[i]
                tlink = systemlink[i-nbopb][1]
                if tlink == -1               # rup
                    write(f,writeu(eq,varmap))
                    writedel(f,systemlink,i,succ,cone,nbopb,dels)
                elseif tlink == -2           # pol
                    write(f,writepol(systemlink[i-nbopb],cone))
                    writedel(f,systemlink,i,succ,cone,nbopb,dels)
                elseif tlink == -3           # ia
                    write(f,writeia(eq,systemlink[i-nbopb][2],cone,varmap))
                    writedel(f,systemlink,i,succ,cone,nbopb,dels)
                elseif tlink == -4           # red
                    write(f,writered(eq,varmap,redwitness[i]))
                elseif tlink == -5           # solx
                    write(f,writesol(eq,varmap))
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
function runtrimer(file)
    tri = @elapsed begin
        system,systemlink,redwitness,nbopb,varmap,output,conclusion,version = readinstance(path,file)
    end
    normcoefsystem(system)
    tms = @elapsed begin
        cone = makesmol(system,varmap,systemlink,nbopb)
    end
    twc = @elapsed begin
        writeconedel(path,file,extention,version,system,cone,systemlink,redwitness,nbopb,varmap,output,conclusion)
    end
    writeshortrepartition(path,file,cone,nbopb)
    
    open(string(path,"/attimes"), "a") do f
        write(f,string(file,"/",round(tri; sigdigits=4),"/",
        round(tms; sigdigits=4),"/",round(twc; sigdigits=4),",\n"))
    end
end
function runveriPB(file)
    sat = read(`tail -n 2 $path/$file$extention`,String)[1:14] == "conclusion SAT"
    nline = parse(Int,split(read(`wc -l $path/$file$extention`,String)," ")[1])
    if !sat && nline>10
        tvp = @elapsed begin
            v1 = read(`veripb $path/$file.opb $path/$file$extention`)
        end
        tvs = @elapsed begin
            v2 = read(`veripb $path/smol.$file.opb $path/smol.$file$extention`)
        end
        so = stat(string(path,"/",file,".opb")).size + stat(string(path,"/",file,extention)).size
        st = stat(string(path,"/smol.",file,".opb")).size + stat(string(path,"/smol.",file,extention)).size
        color = 1
        if tvp>tvs
            color = 2
        end
        printstyled(file,"   trim : ",prettybytes(so),"  ->  ",prettybytes(st),"       ",
            round(tvp; sigdigits=4)," s  ->  ",round(tvs; sigdigits=4)," s\n"; color = color)
        open(string(path,"/abytes"), "a") do f
            write(f,string(file,"/",so/10^6,"/",st/10^6,",\n"))
        end
        open(string(path,"/avtimes"), "a") do f
            write(f,string(file,"/",round(tvp; sigdigits=4),"/",round(tvs; sigdigits=4),",\n"))
        end
        if color == 1
            open(string(path,"/aworst"), "a") do f
                write(f,string(file,"\n")) 
            end
        end
        if v1!=v2
            printstyled("catch (u cant see me)\n"; color = :red)
            open(string(path,"/afailedtrims"), "a") do f
                write(f,string(file," \n"))
            end
        end
    elseif sat
        # println("SAT")
    else
        # println("atomic")
    end
end
function runtrimmer(path,file,extention)
    sat = read(`tail -n 2 $path/$file$extention`,String)[1:14] == "conclusion SAT"
    nline = parse(Int,split(read(`wc -l $path/$file$extention`,String)," ")[1])
    if !sat && nline>10
        tvp = @elapsed begin
            v1 = read(`veripb $path/$file.opb $path/$file$extention`)
        end
        tri = @elapsed begin
            system,systemlink,redwitness,nbopb,varmap,output,conclusion,version = readinstance(path,file)
        end
        normcoefsystem(system)
        tms = @elapsed begin
            cone = makesmol(system,varmap,systemlink,nbopb)
        end
        twc = @elapsed begin
            writeconedel(path,file,extention,version,system,cone,systemlink,redwitness,nbopb,varmap,output,conclusion)
        end
        writeshortrepartition(path,file,cone,nbopb)
        tvs = @elapsed begin
            v2 = read(`veripb $path/smol.$file.opb $path/smol.$file$extention`)
        end
        so = stat(string(path,"/",file,".opb")).size + stat(string(path,"/",file,extention)).size
        st = stat(string(path,"/smol.",file,".opb")).size + stat(string(path,"/smol.",file,extention)).size
        color = 1
        if tvp>tvs
            color = 2
            if tvp>tvs+tms
                color = 3
            end
        end
        printstyled(file,"   trim : ",prettybytes(so),"  ->  ",prettybytes(st),"       ",
            round(tvp; sigdigits=4)," s  ->  ",round(tvs; sigdigits=4)," s      ",
            round(tri; sigdigits=4),"+",round(tms; sigdigits=4),"+",round(twc; sigdigits=4)," s\n"; color = color)
        # open(string(path,"/abytes"), "a") do f
        #     write(f,string(file,"/",so/10^6,"/",st/10^6,",\n"))
        # end
        # open(string(path,"/atimes"), "a") do f
        #     write(f,string(file,"/",
        #     round(tvp; sigdigits=4),"/",round(tri; sigdigits=4),"/",
        #     round(tms; sigdigits=4),"/",round(twc; sigdigits=4),"/",
        #     round(tvs; sigdigits=4),",\n"))
        # end
        # if color == 1
        #     open(string(path,"/aworst"), "a") do f
        #         write(f,string(file,"\n"))       
        #     end
        # end
        # if v1!=v2
        #     printstyled("catch (u cant see me)\n"; color = :red)
        #     open(string(path,"/afailedtrims"), "a") do f
        #         write(f,string(file," \n"))
        #     end
        # end
    elseif sat
        # println("SAT")
    else
        # println("atomic")
    end
end
function run_bio(benchs,solver,proofs,extention)
    path = string(benchs,"/biochemicalReactions")
    cd()
    graphs = cd(readdir, path)
    println("threads available:",Threads.nthreads()) 
    for i in 2:2#eachindex(graphs)
        target = graphs[i]
        Threads.@threads for j in 1:40#eachindex(graphs)
            if i!=j
                pattern = graphs[j]
                # pattern = "001.txt"
                # target = "061.txt"
                ins = string("bio",pattern[1:end-4],target[1:end-4])
                if !isfile(string(proofs,"/",ins,".opb")) || 
                    (isfile(string(proofs,"/",ins,extention)) && 
                    (length(read(`tail -n 1 $proofs/$ins$extention`,String))) < 24 || 
                    read(`tail -n 1 $proofs/$ins$extention`,String)[1:24] != "end pseudo-Boolean proof")
                    run(pipeline(`./$solver --prove $proofs/$ins --no-clique-detection --proof-names --format lad $path/$pattern $path/$target`, devnull))
                end
                runtrimmer(proofs,ins,extention)
            end
        end
    end
end
function run_images(benchs,solver,proofs,extention)
    path = string(benchs,"/images-CVIU11")
    cd()
    patterns = cd(readdir, string(path,"/patterns"))
    targets = cd(readdir, string(path,"/targets"))
    for target in targets
        for pattern in patterns
            ins = string("images-CVIU11",pattern,target)
            if !isfile(string(proofs,"/",ins,".opb")) || 
                (isfile(string(proofs,"/",ins,extention)) && 
                (length(read(`tail -n 1 $proofs/$ins$extention`,String))) < 24 || 
                read(`tail -n 1 $proofs/$ins$extention`,String)[1:24] != "end pseudo-Boolean proof")
                run(`./$solver --prove $proofs/$ins --no-clique-detection --proof-names --format lad $path/patterns/$pattern $path/targets/$target`)
            end
            runtrimmer(proofs,ins,extention)
        end
    end
end
function run_images2(benchs,solver,proofs,extention)
    path = string(benchs,"/images-PR15")
    cd()
    patterns = [string("pattern",i) for i in 1:24]
    target = "target"
    for pattern in patterns
        ins = string("images-PR15",pattern,target)
        if !isfile(string(proofs,"/",ins,".opb")) || 
            (isfile(string(proofs,"/",ins,extention)) && 
            (length(read(`tail -n 1 $proofs/$ins$extention`,String))) < 24 || 
            read(`tail -n 1 $proofs/$ins$extention`,String)[1:24] != "end pseudo-Boolean proof")
            run(`./$solver --prove $proofs/$ins --no-clique-detection --proof-names --format lad $path/$pattern $path/$target`)
        end
        runtrimmer(proofs,ins,extention)
    end
end
function run_LV(benchs,solver,proofs,extention)
    path = string(benchs,"/LV")
    cd()
    graphs = cd(readdir, path)
    for i in 50:111
        for j in 1:49
            target = graphs[i]
            pattern = graphs[j]
            # target = "target"
            # pattern = "pattern"
            ins = string("LV",pattern,target)
            if !isfile(string(proofs,"/",ins,".opb")) || 
                (isfile(string(proofs,"/",ins,extention)) && 
                (length(read(`tail -n 1 $proofs/$ins$extention`,String))) < 24 || 
                read(`tail -n 1 $proofs/$ins$extention`,String)[1:24] != "end pseudo-Boolean proof")
                run(`./$solver --prove $proofs/$ins --no-clique-detection --proof-names --format lad $path/$pattern $path/$target`)
            end
            runtrimmer(proofs,ins,extention)
        end
    end
end
function run_meshes(benchs,solver,proofs,extention)
    path = string(benchs,"/meshes-CVIU11")
    cd()
    patterns = cd(readdir, string(path,"/patterns"))
    targets = cd(readdir, string(path,"/targets"))
    for target in targets
        for pattern in patterns
            ins = string("meshes",pattern,target)
            if !isfile(string(proofs,"/",ins,".opb")) || 
                (isfile(string(proofs,"/",ins,extention)) && 
                (length(read(`tail -n 1 $proofs/$ins$extention`,String))) < 24 || 
                read(`tail -n 1 $proofs/$ins$extention`,String)[1:24] != "end pseudo-Boolean proof")
                run(`./$solver --prove $proofs/$ins --no-clique-detection --proof-names --format lad $path/patterns/$pattern $path/targets/$target`)
            end
            runtrimmer(proofs,ins,extention)
        end
    end
end
function run_phase(benchs,solver,proofs,extention)
    path = string(benchs,"/phase")
    cd()
    rawfiles = cd(readdir, path)
    files = [s[1:end-7] for s in rawfiles if s[end-5:end]=="target"]
    for ins in files
        if !isfile(string(proofs,"/",ins,".opb")) || 
            (isfile(string(proofs,"/",ins,extention)) && 
            (length(read(`tail -n 1 $proofs/$ins$extention`,String))) < 24 || 
            read(`tail -n 1 $proofs/$ins$extention`,String)[1:24] != "end pseudo-Boolean proof")
            run(`./$solver --prove $proofs/$ins --no-clique-detection --proof-names --format lad $path/$ins-pattern $path/$ins-target`)
        end
        runtrimmer(proofs,ins,extention)
    end
end
function run_scalefree(benchs,solver,proofs,extention)
    scpath = string(benchs,"/scalefree")
    cd()
    inst = cd(readdir, string(scpath))
    for ins in inst
        if !isfile(string(proofs,"/",ins,".opb")) || 
            (isfile(string(proofs,"/",ins,extention)) && 
            (length(read(`tail -n 1 $proofs/$ins$extention`,String))) < 24 || 
            read(`tail -n 1 $proofs/$ins$extention`,String)[1:24] != "end pseudo-Boolean proof")
            run(`./$solver --prove $proofs/$ins --no-clique-detection --proof-names --format lad $scpath/$ins/pattern $scpath/$ins/target`)
        end
        runtrimmer(proofs,ins,extention)
    end
end
function run_si(benchs,solver,proofs,extention)
    sipath = string(benchs,"/si")
    cd()
    inst = cd(readdir, string(sipath))
    for ins in inst
        inst2 = cd(readdir, string(sipath,"/",ins))
        for ins2 in inst2
            if !isfile(string(proofs,"/",ins2,".opb")) || 
                (isfile(string(proofs,"/",ins2,extention)) && 
                (length(read(`tail -n 1 $proofs/$ins2$extention`,String))) < 24 || 
                read(`tail -n 1 $proofs/$ins2$extention`,String)[1:24] != "end pseudo-Boolean proof")
                run(`./$solver --prove $proofs/$ins2 --no-clique-detection --proof-names --format lad $sipath/$ins/$ins2/pattern $sipath/$ins/$ins2/target`)
            end
            runtrimmer(proofs,ins2,extention)
        end
    end
end

# const benchs = "veriPB/newSIPbenchmarks"
# const solver = "veriPB/subgraphsolver/glasgow-subgraph-solver/build/glasgow_subgraph_solver"
# const proofs = "veriPB/proofs"    
# const proofs = "veriPB/prooframdisk"    
const benchs = "newSIPbenchmarks"
const solver = "glasgow-subgraph-solver/build/glasgow_subgraph_solver"
const proofs = "/cluster/proofs"
const extention = ".veripb"

function main()
    b,s,p,e = benchs,solver,proofs,extention
    if length(ARGS) == 1
        if ARGS[1] == "bio" #program argument parsing
            @time run_bio(b,s,p,e)
        elseif  ARGS[1] == "im1"
            run_images(b,s,p,e)
        elseif  ARGS[1] == "im2"
            run_images2(b,s,p,e)
        elseif  ARGS[1] == "lv"
            run_LV(b,s,p,e)
        elseif  ARGS[1] == "meshes"
            run_meshes(b,s,p,e)
        elseif  ARGS[1] == "phase"
            run_phase(b,s,p,e)
        elseif  ARGS[1] == "scalefree"
            run_scalefree(b,s,p,e)
        elseif  ARGS[1] == "si"
            run_si(b,s,p,e)        # all si are sat ?
        else
            println("Arguments are: bio im1 im2 lv meshes phase scalefree si")
        end
    else
        println("Arguments are: bio im1 im2 lv meshes phase scalefree si")
    end
end

#=
export JULIA_NUM_THREADS=192
julia 'trimer 4.jl' bio

rm atimes
rm abytes
rm afailedtrims
rm aworst
rm arepartition


=#
main()

# scp -r \\wsl.localhost\Ubuntu\home\arthur_gla\veriPB\trim\smol-proofs2\Instances\ arthur@fataepyc-01.dcs.gla.ac.uk:/users/grad/arthur/smol-proofs2
# scp -r /home/arthur_gla/veriPB/newSIPbenchmarks/ arthur@fataepyc-01.dcs.gla.ac.uk:/users/grad/arthur/
# find . -name "*Zone.Identifier" -type f -delete 
# find . -name ".*" -type f -delete 
# ssh arthur@fataepyc-01.dcs.gla.ac.uk
# scp arthur@fataepyc-01.dcs.gla.ac.uk:/cluster/proofs/smol.bio063002.veripb smol.bio063002.veripb
# scp arthur@fataepyc-01.dcs.gla.ac.uk:/cluster/proofs/times times2
# cd /home/arthur_gla/veriPB/trim/smol-proofs2/


#=
bio007030   trim : 6.786 MB  ->  875.3 KB       7.356 s  ->  1.119 s      14.4+1.5+0.6963 s
bio007030   trim : 6.786 MB  ->  875.3 KB       2.269 s  ->  0.3824 s      4.07+0.5586+0.2704 s

bio001061   trim : 14.8 MB  ->  5.055 MB       17.85 s  ->  5.494 s      32.46+10.84+4.102 s
bio001061   trim : 14.8 MB  ->  5.055 MB       5.553 s  ->  2.529 s      11.89+7.274+1.488 s
    benchs = "newSIPbenchmarks"
    solver = "glasgow-subgraph-solver/build/glasgow_subgraph_solver"
    proofs = "/cluster/proofs"
    extention = ".veripb"
    path = string(benchs,"/biochemicalReactions")
    cd()
    graphs = cd(readdir, path)
    println("threads available:",Threads.nthreads())
                pattern = "007.txt"
                target = "030.txt"
                # pattern = "096.txt"
                # target = "061.txt"
                # pattern = "144.txt"
                # target = "093.txt"
                ins = string("bio",pattern[1:end-4],target[1:end-4])
                path = proofs
                file = ins

bio096061   trim : 11.78 MB  ->  2.591 MB       141.7 s  ->  68.18 s      4.112 s
bio096061   trim : 11.78 MB  ->  2.591 MB       3.921 s  ->  1.137 s      2.739 s
bio096061   trim : 11.78 MB  ->  2.591 MB       4.046 s  ->  1.422 s      7.871+2.942+1.057 s
julia>         @time testparse(path,file,1)
 17.011996 seconds (20.70 M allocations: 2.132 GiB, 6.73% gc time, 9.71% compilation time)
julia>         @time testparse(path,file,10)
 22.657625 seconds (206.64 M allocations: 21.333 GiB, 24.47% gc time)
julia>         @time testparse(path,file,32)
 37.965171 seconds (661.25 M allocations: 68.231 GiB, 35.41% gc time)
julia>         @time testparse(path,file,64)
 81.763286 seconds (1.32 G allocations: 136.444 GiB, 40.61% gc time)
julia>         @time testparse(path,file,192)
295.423247 seconds (3.97 G allocations: 409.409 GiB, 27.31% gc time)

julia>         @time testpara(path,file,extention,1)
  6.840462 seconds (140.03 k allocations: 9.787 MiB, 53.39% compilation time)
julia>         @time testpara(path,file,extention,32)
  7.377385 seconds (4.07 k allocations: 6.488 MiB)
julia>         @time testpara(path,file,extention,64)
  8.549569 seconds (7.13 k allocations: 11.942 MiB)
julia>         @time testpara(path,file,extention,192)
 18.348672 seconds (18.80 k allocations: 21.007 MiB)

  julia> @time testtrim(system,invsys,systemlink,nbopb,1)
  3.588706 seconds (990 allocations: 650.484 KiB)
julia> @time testtrim(system,invsys,systemlink,nbopb,10)
  3.684693 seconds (1.26 k allocations: 13.278 MiB)
julia>         @time testtrim(system,invsys,systemlink,nbopb,32)
  4.133111 seconds (2.27 k allocations: 67.544 MiB)
julia>         @time testtrim(system,invsys,systemlink,nbopb,64)
  5.028341 seconds (4.17 k allocations: 163.692 MiB)

  ramdisk
bio028002   trim : 463.3 KB  ->  77.96 KB       0.1658 s  ->  0.1338 s      0.1548+0.006754+0.2604 s
bio038002   trim : 424.4 KB  ->  104.4 KB       0.3408 s  ->  0.2184 s      0.2014+0.007979+0.05013 s
bio044002   trim : 2.525 MB  ->  472.5 KB       2.563 s  ->  1.343 s      4.859+1.307+0.3612 s
bio031002   trim : 3.178 MB  ->  556.3 KB       4.385 s  ->  1.906 s      14.91+0.7756+1.469 s
bio035002   trim : 5.298 MB  ->  887.0 KB       4.613 s  ->  1.863 s      13.41+2.276+1.55 s
bio007002   trim : 6.438 MB  ->  817.1 KB       6.434 s  ->  1.472 s      17.28+1.254+1.455 s
bio025002   trim : 4.968 MB  ->  1.63 MB       8.412 s  ->  4.341 s      21.35+2.492+2.702 s
bio008002   trim : 3.116 MB  ->  474.5 KB       4.718 s  ->  1.455 s      9.439+0.9916+0.9183 s
bio046002   trim : 7.714 MB  ->  1.017 MB       13.03 s  ->  2.362 s      21.91+2.805+2.006 s
bio041002   trim : 9.438 MB  ->  1.123 MB       17.76 s  ->  2.286 s      36.21+2.966+2.017 s
bio010002   trim : 3.525 MB  ->  662.5 KB       6.77 s  ->  1.003 s      9.906+1.944+0.7735 s
bio017002   trim : 10.32 MB  ->  654.1 KB       19.74 s  ->  1.285 s      43.44+1.146+1.647 s
bio021002   trim : 6.354 MB  ->  814.0 KB       7.358 s  ->  3.348 s      19.22+43.91+1.339 s
bio022002   trim : 382.1 KB  ->  61.2 KB       0.1652 s  ->  0.1063 s      0.1007+0.004035+0.00396 s
bio023002   trim : 415.8 KB  ->  74.28 KB       0.1607 s  ->  0.1234 s      0.2591+0.005265+0.004593 s
bio029002   trim : 10.17 MB  ->  664.6 KB       24.34 s  ->  1.018 s      49.3+1.633+1.324 s
bio026002   trim : 10.27 MB  ->  1.254 MB       19.31 s  ->  1.16 s      23.69+1.739+0.8301 s
bio027002   trim : 3.423 MB  ->  643.4 KB       3.394 s  ->  0.8598 s      6.116+0.4506+0.8279 s
bio037002   trim : 3.554 MB  ->  669.4 KB       4.83 s  ->  2.513 s      10.78+83.73+1.597 s

  ssd
bio028002   trim : 463.3 KB  ->  77.96 KB       0.2903 s  ->  0.1396 s      0.2066+0.005378+0.2075 s
bio038002   trim : 424.4 KB  ->  104.4 KB       0.3132 s  ->  0.1612 s      0.2665+0.008237+0.1932 s
bio044002   trim : 2.525 MB  ->  472.5 KB       2.584 s  ->  1.426 s      4.221+1.303+0.4921 s
bio035002   trim : 5.298 MB  ->  887.0 KB       4.57 s  ->  1.88 s      13.22+1.848+1.13 s
bio031002   trim : 3.178 MB  ->  556.3 KB       4.349 s  ->  2.045 s      15.8+0.5555+0.881 s
bio007002   trim : 6.438 MB  ->  817.1 KB       5.393 s  ->  1.841 s      18.28+1.517+1.421 s
bio025002   trim : 4.968 MB  ->  1.63 MB       7.884 s  ->  3.977 s      21.91+2.671+2.528 s
bio008002   trim : 3.116 MB  ->  474.5 KB       4.394 s  ->  1.337 s      9.526+1.055+0.7747 s
bio046002   trim : 7.714 MB  ->  1.017 MB       13.89 s  ->  2.467 s      22.99+2.846+2.732 s
bio041002   trim : 9.438 MB  ->  1.123 MB       19.95 s  ->  2.153 s      36.65+3.272+2.093 s
bio010002   trim : 3.525 MB  ->  662.5 KB       6.96 s  ->  1.402 s      9.89+1.794+0.5124 s
bio017002   trim : 10.32 MB  ->  654.1 KB       20.86 s  ->  1.706 s      44.24+1.72+1.485 s
bio021002   trim : 6.354 MB  ->  814.0 KB       5.91 s  ->  3.703 s      20.47+45.02+1.192 s
bio022002   trim : 382.1 KB  ->  61.2 KB       0.1542 s  ->  0.08337 s      0.1218+0.003745+0.004114 s
bio023002   trim : 415.8 KB  ->  74.28 KB       0.3594 s  ->  0.1401 s      0.2128+0.006075+0.006485 s
bio029002   trim : 10.17 MB  ->  664.6 KB       24.78 s  ->  0.9442 s      49.28+1.413+1.339 s
bio026002   trim : 10.27 MB  ->  1.254 MB       19.88 s  ->  1.287 s      24.57+1.765+0.9253 s
bio027002   trim : 3.423 MB  ->  643.4 KB       3.263 s  ->  0.97 s      6.456+0.3612+0.4317 s
bio037002   trim : 3.554 MB  ->  669.4 KB       6.015 s  ->  2.496 s      10.89+83.47+1.642 s
=#

