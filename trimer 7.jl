# using Profile,DataStructures,Graphs,GraphPlot,Compose,Cairo
# using StatProfilerHTML
mutable struct Lit
    coef::Int
    sign::Bool
    var::Int
end
mutable struct Eq
    t::Vector{Lit}
    b::Int
end
mutable struct Red
    w::Vector{Lit}                      # each odd is the variable and each next even is tha target (lit(0,0,-1) means constant 1 and 0 means constant 0)
    range::UnitRange{Int64}
    pgranges::Vector{UnitRange{Int64}}
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
        lits = [lits[i] for i in eachindex(lits) if !(i in del)]
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
    # f = read(string(path,'/',file,".opb"),String)
    open(string(path,'/',file,".opb"),"r"; lock = false) do f
        for ss in eachline(f)
        # for ss in split(f,'\n',keepempty=false)
            if ss[1] != '*'                                     #do not parse comments
                st = split(ss,keepempty=false)              #structure of a line is: int var int var ... >= int ; 
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
    normcoefeq(eq)
    lits = copy(eq.t)
    for l in lits
        l.coef = ceil(Int,l.coef/d)
    end
    return Eq(lits,ceil(Int,eq.b/d))
end
function weaken(eq,var) # les eq sont supposees normalise avec des coef positifs seulement.
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
            # normcoefeq(stack[end])
            push!(link,-1)
        elseif i=="*"
            push!(stack,multiply(pop!(stack),link[end]))
            # normcoefeq(stack[end])
            push!(link,-2)
        elseif i=="d"
            push!(stack,divide(pop!(stack),link[end]))
            # normcoefeq(stack[end])
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
        p2 = simplepol(res,system,link)
    end
    if lastsaturate
        normcoefeq(res)
        saturate(res)
    end
    return res
end
function findfullassi(system,st,init,varmap,prism)
    # isassi,assi = initassignement(varmap)
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
            lits[i] = Lit(1,assi[i]!=1,i) # we add the negation
        end
    end
    eq = Eq(lits,1)
    return eq
end
function findbound(system,st,init,varmap,obj,prism)
    eq = findfullassi(system,st,init,varmap,prism)
    bound = 0
    for l in eq.t

    end
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
function fuckparsers(f)
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
function applywitness(eq,w) # je supppose que les literaux opposes ne s.influencent pas.
    t = Lit[]
    b = eq.b
    for l in eq.t
        for i in 1:2:length(w)
            if l.var == w[i].var
                if w[i+1].var > 0
                    if l.sign != w[i].sign
                        b-= l.coef
                    end
                else # negatives var are constants. the coef seems useless
                    # b-= (~((-w[i+1]) ⊻ l.sign)) * l.coef # w s c  0 0 c  0 1 0  1 0 0  1 1 c
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
    # proofgoal #i est la i eme contrainte de la subproof ?
    # -1 est la contrainte qui est declaree dans le proofgoal. elle est affecte par w
    # -2 est la negation de la contrainte declaree dans le red
    # end -1  le -1 donne l'id de la contradiction. on peux aussi mettre c -1
    # l'affectation du temoins refais une nouvelle contrainte. on en repart pas pour le rup.
    nbopb = length(system)-length(systemlink)
    type,st = fuckparsers(f)
    redid = c-1
    pgranges = Vector{UnitRange{Int64}}()
    while type !="end"
        if type == "proofgoal"
            pgid = c
            if st[2][1] == '#' # le proofgoal #1 dans un red c'est simplement l'eq 
                push!(system,reverse(applywitness(eq,w)))
                push!(systemlink,[-7])
            else
                pgref = parse(Int,st[2])
                # printeq(system[pgref],varmap)
                push!(system,reverse(applywitness(system[pgref],w)))
                # printeq(system[end],varmap)
                # println()
                push!(systemlink,[-8,pgref])
            end
            c+=1
            type,st = fuckparsers(f)
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
                type,st = fuckparsers(f)
            end
            push!(pgranges,pgid:c-1)
        end
        type,st = fuckparsers(f)
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
        # println("So it begins")
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
    com = Dict{Int, String}()
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
                    if !(length(eq.t)!=0 || eq.b!=0) println("POL empty") end
                elseif type == "ia"
                    l = 0
                    if st[end] == ";" 
                        eq = readeq(st,varmap,2:2:length(st)-4)
                        printstyled("ia ID is missing";color = :red)
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
                    println("SAT Not supported.")
                    eq = Eq([Lit(0,true,1)],15) # just to add something to not break the id count
                elseif type == "soli" 
                    println("BOUNDS Not supported(soli)")
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
                        println("BOUNDS Not supported.")
                    elseif !isequal(system[end],Eq([],1)) && (conclusion == "SAT" || conclusion == "NONE")
                        println("SAT Not supported.")
                    end
                elseif type == "*trim"
                    com[length(system)+1] = ss[7:end]
                elseif !(type in ["#","w","*","f","d","del","end","pseudo-Boolean"])#,"de","co","en","ps"])
                    println("unknown2: ",ss)
                end
                if length(eq.t)!=0 || eq.b!=0
                    normcoefeq(eq)
                    push!(system,eq)
                    c+=1
                end
            end
        end
    end
    return system,systemlink,redwitness,output,conclusion,com,version
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
                if r1<init+1 # if init == 450 printstyled("\n upgrade"; color=  :blue) end
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
        if prio && i==init+1 # if init == 450 printstyled("\n drop"; color=  :cyan) end
            prio=false
            i=r0
            r0=init+1
        end
    end
    return false
end
function readinstance(path,file)
    system,varmap,obj = readopb(path,file)
    nbopb = length(system)
    system,systemlink,redwitness,output,conclusion,com,version = readveripb(path,file,system,varmap,obj)
    return system,systemlink,redwitness,nbopb,varmap,output,conclusion,com,version,obj
end
function inprism(n,prism)
    for r in prism
        if n in r return true end
    end
    return false
end
function  availableranges(redwitness)                   # build the prism, a range colections of all the red subproofs
    prism = [a.range for (_,a) in redwitness if a.range!=0:0]
    return prism
end
function runtrimmer(file)
    tvp = @elapsed begin
        # v1 = run(`veripb --trace --useColor $proofs/$file.opb $proofs/$file$extention`)
        v1 = read(`veripb $proofs/$file.opb $proofs/$file$extention`)
    end
    print(prettytime(tvp),' ')

# end
# function a()
    tri = @elapsed begin
        system,systemlink,redwitness,nbopb,varmap,output,conclusion,com,version,obj = readinstance(proofs,file)
    end
    print(prettytime(tri),' ')
    invsys = getinvsys(system,systemlink,varmap)
    prism = availableranges(redwitness)
    normcoefsystem(system)
 
    if conclusion in ["BOUNDS"] || conclusion in ["SAT","NONE"] && !isequal(system[end],Eq([],1)) return println() end

    tms = @elapsed begin
        cone = makesmol(system,invsys,varmap,systemlink,nbopb,prism,redwitness)
    end
    println(prettytime(tms))

    twc = @elapsed begin
        writeconedel(proofs,file,version,system,cone,systemlink,redwitness,nbopb,varmap,output,conclusion,obj,prism)
    end
    # printcom(file,system,invsys,cone,com) # only works for subgraph solver with additionnals comments.
    # printsummit(cone,invsys,varmap)
    varocc = printorder(file,cone,invsys,varmap)
    ciaranshow(proofs,file,version,system,cone,systemlink,redwitness,nbopb,varmap,output,conclusion,obj,prism,varocc)
    if file[1:3]=="bio"
        vcone = varcone(system,cone,varmap)
        patcone,tarcone = patterntargetcone(vcone,varmap)
        printbioconegraphs(file,cone,patcone,tarcone)
    end
    # printcone(cone,nbopb)

    writeshortrepartition(proofs,file,cone,nbopb)
    tvs = @elapsed begin
        # v2 = run(`veripb --trace --useColor --traceFail $proofs/smol.$file.opb $proofs/smol.$file$extention`) 
        # v2 = run(`veripb --trace --useColor $proofs/smol.$file.opb $proofs/smol.$file$extention`) 
        # v2 = run(`veripb --traceFail --useColor $proofs/smol.$file.opb $proofs/smol.$file$extention`) 
        # v2 = run(`veripb $proofs/smol.$file.opb $proofs/smol.$file$extention`) 
        v2 = read(`veripb $proofs/smol.$file.opb $proofs/smol.$file$extention`) # --forceCheckDeletion
    end
    so = stat(string(proofs,"/",file,".opb")).size + stat(string(proofs,"/",file,extention)).size
    st = stat(string(proofs,"/smol.",file,".opb")).size + stat(string(proofs,"/smol.",file,extention)).size
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
    if v1!=v2
        printstyled("Traces are not identical\n"; color = :red)
        open(string(proofs,"/afailedtrims"), "a") do f
            write(f,string(file," \n"))
        end
    end
end

# const benchs = "veriPB/newSIPbenchmarks"
# const solver = "veriPB/subgraphsolver/glasgow-subgraph-solver/build/glasgow_subgraph_solver"
# const proofs = "veriPB/proofs"    
const proofs = "veriPB/proofs/small"    
# const proofs = "veriPB/proofs/medium"    
# const proofs = "veriPB/proofs/big"    
# const proofs = "veriPB/prooframdisk"    
# const benchs = "newSIPbenchmarks"
# const solver = "glasgow-subgraph-solver/build/glasgow_subgraph_solver"
# const proofs = "/cluster/proofs"
# const proofs = "/scratch/proofs_to_trim/big"
# const extention = ".veripb"
const extention = ".pbp"
# const path = proofs
const version = "2.0"

cd()
# include("ladtograph.jl")
include("trimerPrints.jl")

function main()
    cd()
    list = cd(readdir, proofs)
    list = [s[1:end-4] for s in list if s[end-3:end]==".opb" && s[1:5]!="smol."]
    list = [s for s in list if isfile(string(proofs,"/",s,extention))]
    stats = [stat(string(proofs,"/",file,extention)).size for file in list]

    println(list)
    p = sortperm(stats)
    for i in 1:length(stats) 
    # for i in 1:length(stats) if !(i in [23]) # small | 23 ia ID missing
    # for i in 1:length(stats) if !(i in [0]) # medium
        print(i,' ')
        ins = list[p[i]]
        printstyled(ins,"\n"; color = :yellow)
        runtrimmer(ins)
    end
    # readrepartition()

end

main()

# ins = "circuit_prune_root_test"
# ins = "mult_experiment_gac" # pas de contradictions donc pas de trimmer.
# runtrimmer(ins)

