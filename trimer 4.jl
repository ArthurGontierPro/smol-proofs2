
using Profile,StatProfilerHTML,DataStructures

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
            stack[end] = multiply(stack[end],link[end])
            push!(link,-2)
        elseif i=="d"
            stack[end] = divide(stack[end],link[end])
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
    output = conclusion = ""
    c = length(system)
    open(string(path,'/',file,".veripb"),"r"; lock = false) do f
        c+=1
        for ss in eachline(f)
            st = split(ss,' ')
            type = st[1]
            removespaces(st)
            eq = Eq([],0)
            if type == "u" || type == "rup"
                eq = readeq(st,varmap,2:2:length(st)-3)     # can fail is space is missing omg
                push!(systemlink,[-1])
            elseif type == "p" || type == "pol"
                push!(systemlink,[-2])
                eq = solvepol(st,system,systemlink[end])
            elseif type == "ia"
                push!(systemlink,[-3,parse(Int,st[2])])
                eq = readeq(st,varmap,4:2:length(st)-3)
            elseif type == "red"  
                push!(systemlink,[-4])
                eq = readred(st,varmap,redwitness,c)
            elseif type == "sol" || type == "soli"         # on ajoute la negation au probleme pour chercher d'autres solutions. jusqua contradiction finale. dans la preuve c.est juste des contraintes pour casser toutes les soloutions trouvees
                push!(systemlink,[-5])
                eq = findfullassi(system,st,c,varmap)
            elseif type == "output"
                output = st[2]
            elseif type == "conclusion"
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
function initassignement(varmap)
    l = length(varmap)
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
function makesmol(system,invsys,varmap,systemlink,nbopb)
    n = length(system)
    antecedants = zeros(Bool,n)
    isassi,assi = initassignement(varmap)
    cone = zeros(Bool,n)
    cone[end] = true
    front = zeros(Bool,n)
    firstcontradiction = findfirst(x->length(x.t)==0,system)
    cone[firstcontradiction] = true
    if systemlink[firstcontradiction-nbopb][1] == -2         # pol case
        fixfront(front,systemlink[firstcontradiction-nbopb])
    else
        updumb(system,varmap,front)                     #front now contains the antecedants of the final claim
        append!(systemlink[firstcontradiction-nbopb],findall(front))
    end
    order = 1
    # println("  init : ",sum(front))#,findall(front))
    while true in front
        i = findlast(front)
        front[i] = false
        if !cone[i] 
            cone[i] = true
            if i>nbopb
                tlink = systemlink[i-nbopb][1]
                if tlink == -1 
                    antecedants .=false ; isassi .=false ; assi.=false
                    # rupdumb(system,antecedants,i,isassi,assi)
                    # rupcorefirst(system,antecedants,i,isassi,assi,front,cone)
                    # rupforque(system,invsys,antecedants,i,isassi,assi,front,cone)
                    rupque(system,invsys,antecedants,order,i,isassi,assi,front,cone) # la rupque est moins efficace pour le trimmer mais elle fais de plus petites preuves
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
function update(eq,s,i,isassi,assi,antecedants)
    changes = false
    for l in eq.t
        if !isassi[l.var] && l.coef > s
            isassi[l.var] = true 
            assi[l.var] = l.sign
            antecedants[i] = true
            changes = true
        end
    end
    return changes
end
function updateque(eq,que,invsys,init,s,i,isassi,assi,antecedants)
    changes = false
    for l in eq.t
        if !isassi[l.var] && l.coef > s
            isassi[l.var] = true 
            assi[l.var] = l.sign
            antecedants[i] = true
            changes = true
            for id in invsys[l.var]
                if id<=init
                    que[id] = true
                end
            end
        end
    end
    return changes
end
function fillprioque(invsys,l,init,cone,front,prioque,que)
    for id in invsys[l.var]
        if id<=init
            if cone[id] || front[id]
                pushfirst!(prioque,id)
            else
                pushfirst!(que,id)  
end end end end
function updateprioque(eq,prioque,que,invsys,cone,front,s,i,init,isassi,assi,antecedants)
    for l in eq.t
        if !isassi[l.var] && l.coef > s
            isassi[l.var] = true 
            assi[l.var] = l.sign
            antecedants[i] = true
            fillprioque(invsys,l,init,cone,front,prioque,que)
end end end
function addinvsys(invsys,eq,id)
    for l in eq.t
        if !isassigned(invsys,l.var)
            invsys[l.var] = [id]
        else
            push!(invsys[l.var],id)
        end
    end
end
function getinvsys(system,varmap)
    invsys = Vector{Vector{Int}}(undef,length(varmap))
    for i in eachindex(system)
        addinvsys(invsys,system[i],i)
    end
    return invsys
end
function score(system,invsys,varmap,init,issasi,assi,score,order)
    for i in 1:init
        s = 0
        for l in system[i].t
            s += length(invsys[l.var])
        end
        if s!=0
            score[i] = s
        end
    end
    println(minimum(score)," ",sum(score)/length(score)," ",maximum(score))
    order = sortperm(score)
    return order
end
function updumb(system,varmap,antecedants) 
    isassi,assi = initassignement(varmap)
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
                changes |= update(eq,s,i,isassi,assi,antecedants)
            end
        end
    end
    printstyled(" updumb Failed "; color = :red)
end
function rupque(system::Vector{Eq},invsys,antecedants::Vector{Bool},order,init,isassi::Vector{Bool},assi::Vector{Bool},front::Vector{Bool},cone::Vector{Bool})
    que = Deque{Int}()
    prioque = Deque{Int}()
    for id in 1:init
        if id<=init
            pushfirst!(que,id) end end
    for i in que
        if cone[i] || front[i]
            pushfirst!(prioque,i) end end
    rev = reverse(system[init])
    while !isempty(prioque) || !isempty(que)
        i = !isempty(prioque) ? pop!(prioque) : pop!(que)
        eq = i==init ? rev : system[i]
        s = slack(eq,isassi,assi)
        if s<0
            antecedants[i] = true
            return 
        else
            updateprioque(eq,prioque,que,invsys,cone,front,s,i,init,isassi,assi,antecedants)
        end
    end
    printstyled(" rupQue empty "; color = :red)
end
function rupforque(system::Vector{Eq},invsys,antecedants::Vector{Bool},init,isassi::Vector{Bool},assi::Vector{Bool},front::Vector{Bool},cone::Vector{Bool})
    rev = reverse(system[init])
    que = ones(Bool,init)
    changes = true
    while changes
        changes = false
        for i in 1:init
            if que[i] && (front[i] || cone[i])
                que[i] = false
                eq = i==init ? rev : system[i]
                s = slack(eq,isassi,assi)
                if s<0
                    antecedants[i] = true
                    return 
                else
                    changes |= updateque(eq,que,invsys,init,s,i,isassi,assi,antecedants)
                end
            end
        end
        if !changes 
            for i in 1:init
                if que[i]
                    que[i] = false
                eq = i==init ? rev : system[i]
                s = slack(eq,isassi,assi)
                if s<0
                    antecedants[i] = true
                    return 
                else
                    changes |= updateque(eq,que,invsys,init,s,i,isassi,assi,antecedants)
                end
            end
            end
        end
    end
    printstyled(" rup core first Failed "; color = :red)
end
function rupcorefirst(system::Vector{Eq},antecedants::Vector{Bool},init,isassi::Vector{Bool},assi::Vector{Bool},front::Vector{Bool},cone::Vector{Bool})
    rev = reverse(system[init])
    changes = true
    while changes
        changes = false
        for i in 1:init
            if front[i] || cone[i]
                eq = i==init ? rev : system[i]
                s = slack(eq,isassi,assi)
                if s<0
                    antecedants[i] = true
                    return 
                else
                    changes |= update(eq,s,i,isassi,assi,antecedants)
                end
            end
        end
        if !changes 
            for i in 1:init
                eq = i==init ? rev : system[i]
                s = slack(eq,isassi,assi)
                if s<0
                    antecedants[i] = true
                    return 
                else
                    changes |= update(eq,s,i,isassi,assi,antecedants)
                end
            end
        end
    end
    printstyled(" rup core first Failed "; color = :red)
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
                changes |= update(eq,s,i,isassi,assi,antecedants)
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
function prettytime(b)
    if b<0.01
        return  string(round(b; sigdigits=1))
    elseif b<0.1
        return  string(round(b; sigdigits=2))
    elseif b<1
        return  string(round(b; sigdigits=3))
    else
        return  string(round(b; sigdigits=4))
    end
end
function runtrimer(file)
    try
    sat = read(`tail -n 2 $path/$file$extention`,String)[1:14] == "conclusion SAT"
    nline = parse(Int,split(read(`wc -l $path/$file$extention`,String)," ")[1])
    if !sat && nline>10
        tri = @elapsed begin
            system,systemlink,redwitness,nbopb,varmap,output,conclusion,version = readinstance(path,file)
        end
        normcoefsystem(system)
        tms = @elapsed begin
            cone = makesmol(system,invsys,varmap,systemlink,nbopb)
        end
        twc = @elapsed begin
            writeconedel(path,file,extention,version,system,cone,systemlink,redwitness,nbopb,varmap,output,conclusion)
        end
        writeshortrepartition(path,file,cone,nbopb)
        so = stat(string(path,"/",file,".opb")).size + stat(string(path,"/",file,extention)).size
        st = stat(string(path,"/smol.",file,".opb")).size + stat(string(path,"/smol.",file,extention)).size
        color = 1
        if so>st
            color = 2
        end
        printstyled(file,"   trim : ",prettybytes(so),"  ->  ",prettybytes(st),"       ",
            round(tri+tms+twc; sigdigits=4),'=',round(tri; sigdigits=4),"+",
            round(tms; sigdigits=4),"+",round(twc; sigdigits=4)," s\n"; color = color)
        open(string(path,"/attimes"), "a") do f
            write(f,string(file,"/",round(tri; sigdigits=4),"/",
            round(tms; sigdigits=4),"/",round(twc; sigdigits=4),",\n"))
        end
    end
    catch
        println("No ",file," to trim")
    end
end
function runveriPB(file)
    try
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
    catch
        println("No ",file," to veri")
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
        invsys = getinvsys(system,varmap)
        normcoefsystem(system)
        tms = @elapsed begin
            cone = @profilehtml makesmol(system,invsys,varmap,systemlink,nbopb)
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
            if tvp>tri+tms+twc
                color = 3
            end
        end
        # printstyled(file,"   trim : ",prettybytes(so),"  ->  ",prettybytes(st),"       ",
        #     round(tvp; sigdigits=4)," s  ->  ",round(tvs; sigdigits=4)," s      ",
        #     round(tri+tms+twc; sigdigits=4),'=',round(tri; sigdigits=4),"+",
        #     round(tms; sigdigits=4),"+",round(twc; sigdigits=4)," s\n"; color = color)

        t = [[parse(Float64,file[end-4:end-3]),so,st,tvp,tvs,tms,twc,tri]]
        printtabular(t)
        # println("[",file[5:6],",",so,",",st,",",tvp,",",tvs,",",tms,",",twc,",",tri,"],")
        open(string(path,"/abytes"), "a") do f
            write(f,string(file,"/",so/10^6,"/",st/10^6,",\n"))
        end
        open(string(path,"/atimes"), "a") do f
            write(f,string(file,"/",
            round(tvp; sigdigits=4),"/",round(tri; sigdigits=4),"/",
            round(tms; sigdigits=4),"/",round(twc; sigdigits=4),"/",
            round(tvs; sigdigits=4),"/",round(tri+tms+twc; sigdigits=4),",\n"))
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
        # push!(pool,[so/10^6,st/10^6,tvp,tvs,tri])
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
    # println("threads available:",Threads.nthreads()) 
    for i in 2:2#eachindex(graphs)
        target = graphs[i]
        # Threads.@threads 
        for j in 31:31#eachindex(graphs)
            if i!=j
                pattern = graphs[j]
                # pattern = "149.txt"
                # target = "094.txt"
                ins = string("bio",pattern[1:end-4],target[1:end-4])
                if !isfile(string(proofs,"/",ins,".opb")) || 
                    (isfile(string(proofs,"/",ins,extention)) && 
                    (length(read(`tail -n 1 $proofs/$ins$extention`,String))) < 24 || 
                    read(`tail -n 1 $proofs/$ins$extention`,String)[1:24] != "end pseudo-Boolean proof")
                    println("solver run on ", ins)
                    run(pipeline(`./$solver --prove $proofs/$ins --no-clique-detection --proof-names --format lad $path/$pattern $path/$target`, devnull))
                end
                runtrimmer(proofs,ins,extention)
            end
        end
    end
end
function run_bio_solver()
    path = string(benchs,"/biochemicalReactions")
    cd()
    graphs = cd(readdir, path)
    # println("threads available:",Threads.nthreads()) 
    for i in eachindex(graphs)
        target = graphs[i]
        # Threads.@threads 
        for j in eachindex(graphs)
            if i!=j
                pattern = graphs[j]
                # pattern = "001.txt"
                # target = "061.txt"
                ins = string("bio",pattern[1:end-4],target[1:end-4])
                if !isfile(string(proofs,"/",ins,".opb")) || 
                    (isfile(string(proofs,"/",ins,extention)) && 
                    (length(read(`tail -n 1 $proofs/$ins$extention`,String))) < 24 || 
                    read(`tail -n 1 $proofs/$ins$extention`,String)[1:24] != "end pseudo-Boolean proof")
                    print(ins)
                    @time run(pipeline(`./$solver --prove $proofs/$ins --no-clique-detection --proof-names --format lad $path/$pattern $path/$target`, devnull))
                end
            end
        end
    end
end
function run_bio_trim()
    path = string(benchs,"/biochemicalReactions")
    cd()
    graphs = cd(readdir, path)
    for i in eachindex(graphs)
        target = graphs[i]
        for j in eachindex(graphs)
            if i!=j
                pattern = graphs[j]
                ins = string("bio",pattern[1:end-4],target[1:end-4])
                runtrimer(ins)
            end
        end
    end
end
function run_bio_veri()
    path = string(benchs,"/biochemicalReactions")
    cd()
    graphs = cd(readdir, path)
    for i in eachindex(graphs)
        target = graphs[i]
        for j in eachindex(graphs)
            if i!=j
                pattern = graphs[j]
                ins = string("bio",pattern[1:end-4],target[1:end-4])
                runveriPB(ins)
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

const benchs = "veriPB/newSIPbenchmarks"
const solver = "veriPB/subgraphsolver/glasgow-subgraph-solver/build/glasgow_subgraph_solver"
const proofs = "veriPB/proofs"    
# const proofs = "veriPB/prooframdisk"    
# const benchs = "newSIPbenchmarks"
# const solver = "glasgow-subgraph-solver/build/glasgow_subgraph_solver"
# const proofs = "/cluster/proofs"
const path = proofs
const extention = ".veripb"
const version = "2.0"

function main()
    b,s,p,e = benchs,solver,proofs,extention
    if length(ARGS) > 0
        if ARGS[1] == "bio" #program argument parsing
            if ARGS[2] == "all"
                run_bio(b,s,p,e)
            elseif ARGS[2] == "solver"
                run_bio_solver()
            elseif ARGS[2] == "trimer"
                run_bio_trim()
            elseif ARGS[2] == "veri"
                run_bio_veri()
            end
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

global pool = Vector{Vector{Float64}}()
# main()
 # min: 1 ~x1 1 ~x2 1 ~x3 1 ~x4 1 ~x5 1 ~x6 1 ~x7 1 ~x8 1 ~x9 1 ~x10 1 ~x11 1 ~x12 1 ~x13 1 ~x14 1 ~x15 1 ~x16 1 ~x17 1 ~x18 1 ~x19 1 ~x20 1 ~x21 1 ~x22 1 ~x23 1 ~x24 1 ~x25 1 ~x26 1 ~x27 1 ~x28 1 ~x29 1 ~x30 1 ~x31 1 ~x32 1 ~x33 1 ~x34 1 ~x35 1 ~x36 1 ~x37 1 ~x38 1 ~x39 1 ~x40 1 ~x41 1 ~x42 1 ~x43 1 ~x44 1 ~x45 1 ~x46 1 ~x47 1 ~x48 1 ~x49 1 ~x50 1 ~x51 1 ~x52 1 ~x53 1 ~x54 1 ~x55 1 ~x56 1 ~x57 1 ~x58 1 ~x59 1 ~x60 1 ~x61 1 ~x62 1 ~x63 1 ~x64 1 ~x65 1 ~x66 1 ~x67 1 ~x68 1 ~x69 1 ~x70 1 ~x71 1 ~x72 1 ~x73 1 ~x74 1 ~x75 1 ~x76 1 ~x77 1 ~x78 1 ~x79 1 ~x80 1 ~x81 1 ~x82 1 ~x83 1 ~x84 1 ~x85 1 ~x86 1 ~x87 1 ~x88 1 ~x89 1 ~x90 1 ~x91 1 ~x92 1 ~x93 1 ~x94 1 ~x95 1 ~x96 1 ~x97 1 ~x98 1 ~x99 1 ~x100 1 ~x101 1 ~x102 1 ~x103 1 ~x104 1 ~x105 1 ~x106 1 ~x107 1 ~x108 1 ~x109 1 ~x110 1 ~x111 1 ~x112 1 ~x113 1 ~x114 1 ~x115 1 ~x116 1 ~x117 1 ~x118 1 ~x119 1 ~x120 1 ~x121 1 ~x122 1 ~x123 1 ~x124 1 ~x125 1 ~x126 1 ~x127 1 ~x128 1 ~x129 1 ~x130 1 ~x131 1 ~x132 1 ~x133 1 ~x134 1 ~x135 1 ~x136 1 ~x137 1 ~x138 1 ~x139 1 ~x140 1 ~x141 1 ~x142 1 ~x143 1 ~x144 1 ~x145 1 ~x146 1 ~x147 1 ~x148 1 ~x149 1 ~x150 1 ~x151 1 ~x152 1 ~x153 1 ~x154 1 ~x155 1 ~x156 1 ~x157 1 ~x158 1 ~x159 1 ~x160 1 ~x161 1 ~x162 1 ~x163 1 ~x164 1 ~x165 1 ~x166 1 ~x167 1 ~x168 1 ~x169 1 ~x170 1 ~x171 1 ~x172 1 ~x173 1 ~x174 1 ~x175 1 ~x176 1 ~x177 1 ~x178 1 ~x179 1 ~x180 1 ~x181 1 ~x182 1 ~x183 1 ~x184 1 ~x185 1 ~x186 1 ~x187 1 ~x188 1 ~x189 1 ~x190 1 ~x191 1 ~x192 1 ~x193 1 ~x194 1 ~x195 1 ~x196 1 ~x197 1 ~x198 1 ~x199 1 ~x200 ;

function readrepartition()
    nb = 0
    cko = 0
    ckp = 0
    Σ = [0 for i in 1:101]
    cd()
    c = 1
    open(string(proofs,'/',"servarepartition"),"r"; lock = false) do f
        for ss in eachline(f)
            c+=1
            if ss!="" && ss[1] == 'b'
                st  = split(ss,' ')
                cko = parse(Int,st[end-1][2:end])
                ckp = parse(Int,st[end])
                c   = 1
            elseif ckp>1 && ckp<100 && c==3
                nb += 1
                st = split(ss,' ')
                i = 1
                for s in st
                    nbp = count('.',s)
                    if nbp>0
                        s = replace(s,'.'=>"")
                    end
                    if s!="" && i<102
                        Σ[i] += parse(Int,s)
                        i+=1
                    end
                    i+=nbp
                end
            end
        end
    end
    println(nb)
    t = Σ./nb
    for i in eachindex(t)
        print(string(i,'/',round(t[i]; sigdigits=4),','))
    end
    # return Σ./nb
end
function printtabular(t)
    for i in t 
        println(round(Int,i[1])," & ",
        prettybytes(i[2])," & ",
        prettybytes(i[3])," & ",
        prettytime(i[4])," & ",
        prettytime(i[5])," & ",
        prettytime(i[6])," & ",
        prettytime(i[7])," & ",
        prettytime(i[8])," \\\\\\hline"
        )
    end
end

ins = "aaaclique"
cd()
# ins = "bio021002"
# runtrimmer(proofs,ins,extention)

ins = "bio037002"
runtrimmer(proofs,ins,extention)

# main()

#=
export JULIA_NUM_THREADS=192
julia --check-bounds=no 'trimer 4.jl' bio all


rm atimes
rm abytes
rm afailedtrims
rm aworst
rm arepartition

hardest one bio 7 13 (310_916_484 lignes)
lon sur le serv bio 89 32 (421_805_749 lignes)
=#

# readrepartition()

# scp -r \\wsl.localhost\Ubuntu\home\arthur_gla\veriPB\trim\smol-proofs2\Instances\ arthur@fataepyc-01.dcs.gla.ac.uk:/users/grad/arthur/smol-proofs2
# scp -r /home/arthur_gla/veriPB/newSIPbenchmarks/ arthur@fataepyc-01.dcs.gla.ac.uk:/users/grad/arthur/
# find . -name "*Zone.Identifier" -type f -delete 
# find . -name ".*" -type f -delete 
# ssh arthur@fataepyc-01.dcs.gla.ac.uk
# scp arthur@fataepyc-01.dcs.gla.ac.uk:/cluster/proofs/smol.bio063002.veripb smol.bio063002.veripb
# scp arthur@fataepyc-01.dcs.gla.ac.uk:/cluster/proofs/times times2
# cd /home/arthur_gla/veriPB/trim/smol-proofs2/
