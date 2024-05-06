
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
function addinvsys(invsys,eq,id)
    for l in eq.t
        if !isassigned(invsys,l.var)
            invsys[l.var] = [id]
        else
            push!(invsys[l.var],id)
        end
    end
end
function readvar(s,varmap)
    tmp = split(s,'~')[end]
    i = findfirst(x->x==tmp,varmap)
    if isnothing(i)
        println("Var ",tmp," does not exists")
    end
    return i
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
function opbsize(s)
    nbctr = 0
    varmap = String[]
    for ss in s
        if ss[1] != '*'
            nbctr+=1
            st = split(ss,' ')
            for v in 2:2:length(st)-3
                var = split(st[v],'~')[end]
                if !(var in varmap)
                    push!(varmap,var)
                end
            end
        end
    end
    return nbctr,varmap
end
function removespaces(st)
    r = findall(x->x=="",st)
    deleteat!(st,r)
end
function readopb(path,file)
    system = Vector{Eq}
    invsys = Vector{Vector{Int}}
    varmap = Vector{String}
    open(string(path,'/',file,".opb"),"r") do f
        s = readlines(f)
        nbctr,varmap = opbsize(s)
        nbvar = length(varmap)
        c = 1
        system = Vector{Eq}(undef,nbctr)
        invsys = Vector{Vector{Int}}(undef,nbvar)
        for ss in s
            if ss[1] != '*'                                     #do not parse comments
                st = split(ss,' ')                              #structure of line is: int var int var ... >= int ; 
                removespaces(st)
                eq = readeq(st,varmap)
                if length(eq.t)==0 && eq.b==1
                    printstyled(" !opb"; color = :blue)
                end
                normcoefeq(eq)
                system[c] = eq
                addinvsys(invsys,eq,c)
                c+=1
            end
        end
    end
    return system,invsys,varmap
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
function islexicolesslit(l1,l2)
    return l1.var<l2.var
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
function proofsize(s,varmap,words)
    nbctr = 0
    for ss in s
        if ss[1:2] in ["p ","u ","ia","re","so"]
            nbctr+=1
            st = split(ss,' ')
            for v in st
                if !(v in words) && !(tryparse(Int64,v) isa Number)
                    var = split(v,'~')[end]
                    if !(var in varmap)
                        push!(varmap,var)
                    end
                end 
            end
        end
    end
    return nbctr
end
function findfullassi(system,invsys,st,init,varmap)
    isassi,assi = initassignement(invsys)
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
function readveripb(path,file,system,invsys,varmap,words)
    systemlink = Vector{Vector{Int}}
    redwitness = Vector{String}
    version = output = conclusion = ""
    open(string(path,'/',file,".veripb"),"r") do f
        s = readlines(f)
        version = split(s[1],' ')[end]
        c = length(system)
        nbctr = proofsize(s,varmap,words) + c
        system = vcat(system,Vector{Eq}(undef,nbctr-c))
        invsys = vcat(invsys,Vector{Vector{Int}}(undef,length(varmap)-length(invsys)))
        systemlink = Vector{Vector{Int}}(undef,nbctr)
        redwitness = Vector{String}(undef,nbctr)
        c+=1
        for ss in s
            st = split(ss,' ')
            removespaces(st)
            eq = Eq([],0)
            if ss[1:2] == "u " || ss[1:3] == "rup"
                eq = readeq(st,varmap,2:2:length(st)-3)
                systemlink[c] = [-1]
                if length(eq.t)==0 && eq.b>0            # contradiction case
                    system[c] = eq
                    addinvsys(invsys,eq,c)
                    system = system[1:c]
                    output = split(s[end-2],' ')[2]
                    conclusion = split(s[end-1],' ')[2]
                    return system,invsys,systemlink,output,conclusion
                end
            elseif ss[1:2] == "p " || ss[1:3] == "pol"
                systemlink[c] = [-2]
                eq = solvepol(st,system,systemlink[c])
            elseif ss[1:2] == "ia"
                systemlink[c] = [-3,parse(Int,st[2])]
                eq = readeq(st,varmap,4:2:length(st)-3)
            elseif ss[1:3] == "red"  
                systemlink[c] = [-4]
                eq = readred(st,varmap,redwitness,c)
            elseif ss[1:3] == "sol"                                  # on ajoute la negation au probleme pour chercher d'autres solutions. jusqua contradiction finale. dans la preuve c.est juste des contraintes pour casser toutes les soloutions trouvees
                systemlink[c] = [-5]
                eq = findfullassi(system,invsys,st,c,varmap)
            elseif st[1] == "output"
                output = st[2]
            elseif st[1] == "conclusion"
                conclusion = st[2]
            elseif !(ss[1:2] in ["# ","w ","ps","* ","f ","d ","de","co","en"])
                println("unknown: ",ss)
            end
            if length(eq.t)!=0 || eq.b!=0
                normcoefeq(eq)
                system[c] = eq
                addinvsys(invsys,eq,c)
                c+=1
            end
        end
    end
    return system,invsys,systemlink,redwitness,output,conclusion,version
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
function nbfreelits(eq,isassi)
    s = 0
    for l in eq.t
        if !isassi[l.var]
            s+=1
        end
    end
    return s
end
function comparefreelits(eq1,eq2,system,isassi)
    return nbfreelits(system[eq1],isassi) < nbfreelits(system[eq2],isassi)
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
    if systemlink[firstcontradiction][1] == -2         # pol case
        fixfront(front,systemlink[firstcontradiction])
    else
        updumb(system,invsys,front)                     #front now contains the antecedants of the final claim
        append!(systemlink[firstcontradiction],findall(front))
    end
    # print("  init : ",sum(front))#,findall(front))
    while true in front
        i = findlast(front)
        front[i] = false
        if !cone[i] 
            cone[i] = true
            if i>nbopb
                tlink = systemlink[i][1]
                if tlink == -1 
                    antecedants .=false ; isassi .=false ; assi.=false
                    rupdumb(system,antecedants,i,isassi,assi)
                    append!(systemlink[i],findall(antecedants))
                    fixfront(front,antecedants)
                elseif tlink >= -3
                    antecedants .= false
                    fixante(systemlink,antecedants,i)
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
function updumb(system,invsys,antecedants,init,isassi,assi)
    changes = true
    while changes
        changes = false
        for i in 1:init
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
    printstyled("!up "; color = :red)
end
function nbfreelits(eq,isassi)
    s = 0
    for l in eq.t
        if !isassi[l.var]
            s+=1
        end
    end
    return s
end
function comparefreelits(eq1,eq2,system,isassi)
    return nbfreelits(system[eq1],isassi) < nbfreelits(system[eq2],isassi)
end
function upsmart(system,invsys,antecedants)       #extremely costly in freelit comparisons
    isassi,assi = initassignement(invsys)
    n = length(system)
    front = zeros(Bool,n)
    init = n-1                          #je devrais commencer par un petit slack de tous le monde pour choisir le premier point de contradiction
    while init>0
        front[init] = true
        while true in front
            tab = findall(front)
            sort!(tab,lt=(x,y)->comparefreelits(x,y,system,isassi))
            change = false
            sortid = 1
            while !change && sortid<=length(tab)
                i = tab[sortid]
                sortid+=1
                front[i] = false
                eq = system[i]
                s = slack(eq,isassi,assi)
                if s<0
                    antecedants[i] = true
                    return 
                else
                    for l in eq.t
                        if !isassi[l.var] && l.coef > s
                            change = true
                            assi[l.var] = l.sign
                            isassi[l.var] = true 
                            antecedants[i] = true
                            for j in invsys[l.var]          
                                if j!=i 
                                    front[j] = true
                                end 
                            end
                        end
                    end
                end
            end
        end
        init-=1
    end
    printstyled("!upsmartfront "; color = :red)
end
function rupsmart(system,invsys,antecedants,init,isassi,assi) # This rup does not respect the order of the proof is that bad ?
    rev = reverse(system[init])
    n = length(system)
    front = zeros(Bool,init)
    front[init] = true
    while true in front
        tab = findall(front)
        sort!(tab,lt=(x,y)->comparefreelits(x,y,system,isassi))
        change = false
        sortid = 1
        while !change && sortid<=length(tab)
            i = tab[sortid]
            sortid+=1
            front[i] = false
            eq = i==init ? rev : system[i]
            s = slack(eq,isassi,assi)
            if s<0
                antecedants[i] = true
                return 
            else
                for l in eq.t
                    if !isassi[l.var] && l.coef > s
                        change = true
                        assi[l.var] = l.sign
                        isassi[l.var] = true 
                        antecedants[i] = true
                        for j in invsys[l.var]          
                            if j!=i && j<=init
                                front[j] = true
                            end 
                        end
                    end
                end
            end
        end
    end
    printstyled("!rups "; color = :red)
end
function readinstance(path,file)
    words = ["p","u","red","sol","solx","soli",">=",";",":","+","s","ia"]
    system,invsys,varmap = readopb(path,file)
    nbopb = length(system)
    system,invsys,systemlink,redwitness,output,conclusion,version = readveripb(path,file,system,invsys,varmap,words)
    return system,invsys,systemlink,redwitness,nbopb,varmap,output,conclusion,version
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
function invlink(systemlink,succ::Vector{Vector{Int}})
    for i in eachindex(systemlink)
        if isassigned(systemlink,i)
            t = systemlink[i]
            for j in t
                if j>0
                    if isassigned(succ,j)
                        push!(succ[j],i)
                    else
                        succ[j] = [i]
                    end
                end
            end
        end
    end
end
function writedel(f,systemlink,i,succ,cone,nbopb,dels)
    isdel = false
    for p in systemlink[i]
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
    succ = Vector{Vector{Int}}(undef,length(systemlink))
    dels = zeros(Bool,length(systemlink))
    invlink(systemlink,succ)
    open(string(path,"/smol.",file,extention),"w") do f
        write(f,string("pseudo-Boolean proof version ",version,"\n"))
        write(f,string("f ",sum(cone[1:nbopb])," 0\n"))
        for i in nbopb+1:length(system)
            if cone[i]
                eq = system[i]
                tlink = systemlink[i][1]
                if tlink == -1               # rup
                    write(f,writeu(eq,varmap))
                    writedel(f,systemlink,i,succ,cone,nbopb,dels)
                elseif tlink == -2           # pol
                    write(f,writepol(systemlink[i],cone))
                    writedel(f,systemlink,i,succ,cone,nbopb,dels)
                elseif tlink == -3           # ia
                    write(f,writeia(eq,systemlink[i][2],cone,varmap))
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
            write(f,string("conclusion ",conclusion," : -1\n"))#,sum(cone),"\n"))
            # write(f,string("conclusion ",conclusion," : ",length(system),"\n")) # for full system
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
function runtrimmer(path,file,extention)
    # printstyled(file,"                : \n"; color = :yellow)
    # println("path = \"",path,"\"\nfile = \"",file,"\"\n")
    # path = "veriPB/proofs"
    # file = "si2_b03_m200.00"
    sat = read(`tail -n 2 $path/$file$extention`,String)[1:14] == "conclusion SAT"

    nline = parse(Int,split(read(`wc -l $path/$file$extention`,String)," ")[1])

    if !sat && nline>10
        @time system,invsys,systemlink,redwitness,nbopb,varmap,output,conclusion,version = readinstance(path,file)

        @time Threads.@threads for i in 1:64
        system,invsys,systemlink,redwitness,nbopb,varmap,output,conclusion,version = readinstance(path,file)
        end

        @time v1 = read(`veripb $path/$file.opb $path/$file$extention`)
        @time Threads.@threads for i in 1:64
        v1 = read(`veripb $path/$file.opb $path/$file$extention`)
        end

        @time cone = makesmol(system,invsys,systemlink,nbopb)
        @time Threads.@threads for i in 1:64
            cone = makesmol(system,invsys,systemlink,nbopb)
        end

        #=
        t1=t2=t3 = 0.0
        v1=v2=""
        try
            t1 = @elapsed begin
                v1 = read(`veripb $path/$file.opb $path/$file$extention`)
            end        
        catch
            printstyled(file,"veriPB fail\n"; color = :red)
        end
        system,invsys,systemlink,redwitness,nbopb,varmap,output,conclusion,version = readinstance(path,file)
        # print("   size : ",nbopb,"|",length(system)-nbopb)
        normcoefsystem(system)
        t2 = @elapsed begin
            cone = makesmol(system,invsys,systemlink,nbopb)
        end
        writeconedel(path,file,extention,version,system,cone,systemlink,redwitness,nbopb,varmap,output,conclusion)
        nto = sum(cone[1:nbopb])
        ntp = sum(cone[nbopb+1:end])
        # println("   opb : ",nto,"/",nbopb," (",round(Int,100*nto/nbopb),"%)",
        #         "   pbp : ",ntp,"/",(length(system)-nbopb)," (",round(Int,100*ntp/(length(system)-nbopb)),"%)",
        #         "   time : ",round(t2; digits=3)," s")
        # printstyled(file," (smol)         : "; color = :yellow)
        writeshortrepartition(path,file,cone,nbopb)
        try
            t3 = @elapsed begin
                v2 = read(`veripb $path/smol.$file.opb $path/smol.$file$extention`)
            end
            so = stat(string(path,"/",file,".opb")).size + stat(string(path,"/",file,extention)).size
            st = stat(string(path,"/smol.",file,".opb")).size + stat(string(path,"/smol.",file,extention)).size
            if t1>t3
                printstyled(file,"   trim : ",prettybytes(so),"  ->  ",prettybytes(st),
                "       ",round(t1; sigdigits=4)," s  ->  ",round(t3; sigdigits=4)," s      ",round(t2; sigdigits=4)," s\n"; color = :green)
            else
                printstyled(file,"   trim : ",prettybytes(so),"  ->  ",prettybytes(st),
                "       ",round(t1; sigdigits=4)," s  ->  ",round(t3; sigdigits=4)," s      ",round(t2; sigdigits=4)," s\n"; color = :red)
            end
            open(string(path,"/abytes"), "a") do f
                write(f,string(file,"/",so/10^6,"/",st/10^6,",\n"))
            end
            open(string(path,"/atimes"), "a") do f
                write(f,string(file,"/",round(t1; sigdigits=4),"/",round(t2; sigdigits=4),"/",round(t3; sigdigits=4),",\n"))
            end
            if t1<t2 || t1<t3                
                open(string(path,"/aworst"), "a") do f
                    write(f,string(file,"/",round(t1; sigdigits=4),"/",round(t2; sigdigits=4),"/",round(t3; sigdigits=4),",\n"))
                end
            end
            if v1!=v2
                printstyled("catch (u cant see me)\n"; color = :red)
                open(string(path,"/afailedtrims"), "a") do f
                    write(f,string(file," \n"))
                end
            end
        catch
            printstyled("catch (u cant see me)\n"; color = :red)
            open(string(path,"/afailedtrims"), "a") do f
                write(f,string(file," \n"))
            end
        end=#
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
    # for i in 1:1 #eachindex(graphs)
    #     for j in 1:1 #eachindex(graphs)
    #         if i!=j
    #             target = graphs[i]
    #             pattern = graphs[j]
                pattern = "096.txt"
                target = "061.txt"
                ins = string("bio",pattern[1:end-4],target[1:end-4])
                if !isfile(string(proofs,"/",ins,".opb")) || 
                    (isfile(string(proofs,"/",ins,extention)) && 
                    (length(read(`tail -n 1 $proofs/$ins$extention`,String))) < 24 || 
                    read(`tail -n 1 $proofs/$ins$extention`,String)[1:24] != "end pseudo-Boolean proof")
                    run(pipeline(`./$solver --prove $proofs/$ins --no-clique-detection --proof-names --format lad $path/$pattern $path/$target`, devnull))
                end
                runtrimmer(proofs,ins,extention)
    #         end
    #     end
    # end
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
                @time run(`./$solver --prove $proofs/$ins --no-clique-detection --proof-names --format lad $path/patterns/$pattern $path/targets/$target`)
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
            @time run(`./$solver --prove $proofs/$ins --no-clique-detection --proof-names --format lad $path/$pattern $path/$target`)
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
                @time run(`./$solver --prove $proofs/$ins --no-clique-detection --proof-names --format lad $path/$pattern $path/$target`)
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
                @time run(`./$solver --prove $proofs/$ins --no-clique-detection --proof-names --format lad $path/patterns/$pattern $path/targets/$target`)
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
            @time run(`./$solver --prove $proofs/$ins --no-clique-detection --proof-names --format lad $path/$ins-pattern $path/$ins-target`)
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
            @time run(`./$solver --prove $proofs/$ins --no-clique-detection --proof-names --format lad $scpath/$ins/pattern $scpath/$ins/target`)
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
                @time run(`./$solver --prove $proofs/$ins2 --no-clique-detection --proof-names --format lad $sipath/$ins/$ins2/pattern $sipath/$ins/$ins2/target`)
            end
            runtrimmer(proofs,ins2,extention)
        end
    end
end

function main()
    # benchs = "veriPB/newSIPbenchmarks"
    # solver = "veriPB/subgraphsolver/glasgow-subgraph-solver/build/glasgow_subgraph_solver"
    # proofs = "veriPB/proofs"    
    benchs = "newSIPbenchmarks"
    solver = "glasgow-subgraph-solver/build/glasgow_subgraph_solver"
    proofs = "/cluster/proofs"
    extention = ".veripb"

    b,s,p,e = benchs,solver,proofs,extention
    if length(ARGS) == 1
        if ARGS[1] == "bio" #program argument parsing
            run_bio(b,s,p,e)
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



threads available:1
bio096061   trim : 11.78 MB  ->  2.591 MB       4.471 s  ->  1.192 s      2.89 s
bio096061   trim : 11.78 MB  ->  2.591 MB       4.324 s  ->  1.177 s      2.791 s
bio096061   trim : 11.78 MB  ->  2.591 MB       4.262 s  ->  1.188 s      2.785 s
bio096061   trim : 11.78 MB  ->  2.591 MB       4.18 s  ->  1.276 s      2.786 s
bio096061   trim : 11.78 MB  ->  2.591 MB       4.578 s  ->  1.341 s      2.848 s
bio096061   trim : 11.78 MB  ->  2.591 MB       4.48 s  ->  1.395 s      2.932 s
bio096061   trim : 11.78 MB  ->  2.591 MB       4.584 s  ->  1.368 s      2.927 s
bio096061   trim : 11.78 MB  ->  2.591 MB       4.627 s  ->  1.429 s      3.087 s
bio096061   trim : 11.78 MB  ->  2.591 MB       5.025 s  ->  1.346 s      3.239 s
200.983978 seconds (206.94 M allocations: 70.214 GiB, 4.85% gc time, 0.39% compilation time)



threads available:12
bio096061   trim : 11.78 MB  ->  2.591 MB       9.49 s  ->  1.474 s      6.649 s
bio096061   trim : 11.78 MB  ->  2.591 MB       9.311 s  ->  2.87 s      6.53 s
bio096061   trim : 11.78 MB  ->  2.591 MB       9.578 s  ->  2.894 s      6.687 s
bio096061   trim : 11.78 MB  ->  2.591 MB       9.338 s  ->  3.275 s      6.675 s
bio096061   trim : 11.78 MB  ->  2.591 MB       9.351 s  ->  3.363 s      6.313 s
bio096061   trim : 11.78 MB  ->  2.591 MB       8.975 s  ->  3.496 s      6.864 s
bio096061   trim : 11.78 MB  ->  2.591 MB       9.07 s  ->  3.221 s      6.534 s
bio096061   trim : 11.78 MB  ->  2.591 MB       8.966 s  ->  2.862 s      6.7 s
bio096061   trim : 11.78 MB  ->  2.591 MB       9.251 s  ->  2.951 s      6.591 s
 86.292714 seconds (207.11 M allocations: 70.235 GiB, 17.97% gc time, 4.78% compilation time)


threads available:12
bio096061   trim : 11.78 MB  ->  2.591 MB       17.78 s  ->  4.364 s      3.253 s
bio096061   trim : 11.78 MB  ->  2.591 MB       21.96 s  ->  2.456 s      8.878 s
bio096061   trim : 11.78 MB  ->  2.591 MB       21.94 s  ->  3.951 s      8.87 s
bio096061   trim : 11.78 MB  ->  2.591 MB       21.94 s  ->  4.107 s      8.73 s
bio096061   trim : 11.78 MB  ->  2.591 MB       21.96 s  ->  4.567 s      8.874 s
bio096061   trim : 11.78 MB  ->  2.591 MB       21.94 s  ->  4.157 s      8.866 s
bio096061   trim : 11.78 MB  ->  2.591 MB       21.96 s  ->  4.205 s      8.893 s
bio096061   trim : 11.78 MB  ->  2.591 MB       21.96 s  ->  4.272 s      8.911 s
bio096061   trim : 11.78 MB  ->  2.591 MB       21.94 s  ->  4.385 s      8.866 s
bio096061   trim : 11.78 MB  ->  2.591 MB       21.96 s  ->  4.524 s      8.905 s
 56.580600 seconds (44.41 M allocations: 58.904 GiB, 2.68% gc time, 13.45% compilation time)

threads available:6
bio096061   trim : 11.78 MB  ->  2.591 MB       13.64 s  ->  3.452 s      6.17 s
bio096061   trim : 11.78 MB  ->  2.591 MB       13.09 s  ->  3.575 s      6.264 s
bio096061   trim : 11.78 MB  ->  2.591 MB       12.26 s  ->  3.448 s      6.311 s
bio096061   trim : 11.78 MB  ->  2.591 MB       12.94 s  ->  3.574 s      6.122 s
bio096061   trim : 11.78 MB  ->  2.591 MB       12.8 s  ->  3.848 s      6.347 s
bio096061   trim : 11.78 MB  ->  2.591 MB       13.87 s  ->  3.841 s      5.953 s
bio096061   trim : 11.78 MB  ->  2.591 MB       10.88 s  ->  2.614 s      5.127 s
bio096061   trim : 11.78 MB  ->  2.591 MB       9.874 s  ->  2.836 s      4.937 s
bio096061   trim : 11.78 MB  ->  2.591 MB       9.985 s  ->  2.724 s      4.919 s
bio096061   trim : 11.78 MB  ->  2.591 MB       9.973 s  ->  2.92 s      4.947 s
 61.665076 seconds (44.42 M allocations: 58.913 GiB, 2.41% gc time, 8.70% compilation time)


 =#


#=
bio171002        : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   size : 3971|62092  init : 655   opb : 3778/3971 (95%)   pbp : 13543/62092 (22%)   time : 59.023 s
bio171002 (smol) : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   trim : 5.852 MB  ->  880.8 KB       2.324 s  ->  11.08 s
del id

bio021002                : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   size : 4255|73903  init : 761   opb : 3967/4255 (93%)   pbp : 10557/73903 (14%)   time : 20.965 s
bio021002 (smol)         : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   trim : 6.354 MB  ->  704.1 KB       3.073 s  ->  2.812 s
bio021002 (smol) & (del) : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   trim : 6.354 MB  ->  814.0 KB       3.073 s  ->  1.725 s

bio037002                : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   size : 2539|37522  init : 1095   opb : 2259/2539 (89%)   pbp : 8491/37522 (23%)   time : 64.39 s
bio037002 (smol)         : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   trim : 3.554 MB  ->  596.1 KB       1.843 s  ->  11.77 s
bio037002 (smol) & (del) : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   trim : 3.554 MB  ->  669.4 KB       1.843 s  ->  2.562 s

bio063002                : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   size : 4609|250361  init : 760   opb : 4271/4609 (93%)   pbp : 21695/250361 (9%)   time : 3.424 s
bio063002 (smol)         : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   trim : 17.26 MB  ->  1.387 MB       10.93 s  ->  1.176 s
bio063002 (smol) & (del) : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   trim : 17.26 MB  ->  1.611 MB       10.93 s  ->  1.361 s

bio065002                : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   size : 2729|33440  init : 432   opb : 2549/2729 (93%)   pbp : 6813/33440 (20%)   time : 18.321 s
bio065002 (smol)         : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   trim : 3.216 MB  ->  444.3 KB       1.333 s  ->  2.11 s
bio065002 (smol) & (del) : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   trim : 3.216 MB  ->  505.7 KB       1.333 s  ->  1.344 s

bio171002                : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   size : 3971|62092  init : 655   opb : 3778/3971 (95%)   pbp : 13543/62092 (22%)   time : 51.182 s
bio171002 (smol)         : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   trim : 5.852 MB  ->  880.8 KB       2.109 s  ->  12.56 s
bio171002 (smol) & (del) : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   trim : 5.852 MB  ->  1.016 MB       2.109 s  ->  6.925 s




  0.077492 seconds (113 allocations: 7.125 KiB)
bio037002        : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   size : 2539|37522  init : 1095   opb : 2259/2539 (89%)   pbp : 8491/37522 (23%)   time : 167.666 s
bio037002 (smol) : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   trim : 3.554 MB  ->  666.8 KB       2.462 s  ->  4.129 s

  0.196476 seconds (113 allocations: 7.125 KiB)
bio041002        : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   size : 4331|130077  init : 786   opb : 3438/4331 (79%)   pbp : 14438/130077 (11%)   time : 2.099 s
bio041002 (smol) : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   trim : 9.438 MB  ->  1.118 MB       9.3 s  ->  1.272 s

  0.127089 seconds (113 allocations: 7.125 KiB)
bio046002        : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   size : 4621|94361  init : 889   opb : 3965/4621 (86%)   pbp : 13661/94361 (14%)   time : 1.256 s
bio046002 (smol) : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   trim : 7.714 MB  ->  1.012 MB       6.635 s  ->  0.6311 s

     0.205192 seconds (113 allocations: 7.125 KiB)
bio063002        : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   size : 4609|250361  init : 760   opb : 4271/4609 (93%)   pbp : 21695/250361 (9%)   time : 4.19 s
bio063002 (smol) : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   trim : 17.26 MB  ->  1.607 MB       17.4 s  ->  2.1 s
   
     0.105112 seconds (113 allocations: 7.125 KiB)
bio065002        : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   size : 2729|33440  init : 432   opb : 2549/2729 (93%)   pbp : 6813/33440 (20%)   time : 44.615 s
bio065002 (smol) : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   trim : 3.216 MB  ->  503.1 KB       2.199 s  ->  1.6 s

     0.184300 seconds (113 allocations: 7.125 KiB)
bio071002        : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   size : 5765|163909  init : 989   opb : 4577/5765 (79%)   pbp : 21158/163909 (13%)   time : 2.659 s
bio071002 (smol) : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   trim : 12.07 MB  ->  1.617 MB       12.62 s  ->  1.951 s

 0.113359 seconds (114 allocations: 7.422 KiB)
bio075002        : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   size : 4425|166447  init : 697   opb : 3667/4425 (83%)   pbp : 14313/166447 (9%)   time : 1.642 s
bio075002 (smol) : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   trim : 11.64 MB  ->  1.129 MB       10.51 s  ->  1.44 s

 0.174116 seconds (113 allocations: 7.125 KiB)
bio084002        : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   size : 3287|107140  init : 704   opb : 3012/3287 (92%)   pbp : 18354/107140 (17%)   time : 1.395 s
bio084002 (smol) : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   trim : 7.293 MB  ->  1.302 MB       7.632 s  ->  1.554 s


   bio167002                : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   size : 2719|61630  init : 791   opb : 2600/2719 (96%)   pbp : 10301/61630 (17%)   time : 28.294 s
bio167002 (smol)         : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   trim : 4.603 MB  ->  758.2 KB       2.598 s  ->  1.051 s
   =#


#=
   bio144093   trim : 1.101 MB  ->  115.5 KB       67.31 s  ->  0.08961 s      0.01088 s
   bio091033   trim : 12.41 MB  ->  740.6 KB       71.14 s  ->  0.7427 s      1.23 s
   bio096061   trim : 11.78 MB  ->  2.591 MB       141.7 s  ->  68.18 s      4.112 s
bio096061   trim : 11.78 MB  ->  2.591 MB       3.921 s  ->  1.137 s      2.739 s
bio096061   trim : 11.78 MB  ->  2.591 MB       5.5e-8 s  ->  5.3e-8 s      5.207 s 4t

bio035164   trim : 9.835 MB  ->  1.842 MB       64.34 s  ->  71.77 s      75600.0 s
bio097061   trim : 11.78 MB  ->  2.591 MB       71.41 s  ->  71.56 s      354.8 s

bio149094   trim : 969.6 KB  ->  90.24 KB       67.63 s  ->  0.08493 s      0.006856 s
   =#

