using Profile,StatProfilerHTML,DataStructures,Graphs,GraphPlot,Compose,Cairo
~a=1-a
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
    w::Vector{Lit}
    systems::Vector{Vector{Eq}}
    syslinks::Vector{Vector{Int}}
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
function isequal(a,b)
    return a.coef==b.coef && a.sign==b.sign && a.var==b.var
end
function isequal(e,f)
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

                l2 = f.t[j]
            end
            if !isequal(l,l2)

            end
        end
        return true
    end
end
function removespaces(st)
    r = findall(x->x=="",st)
    deleteat!(st,r)
end
function remove(s,st)
    r = findall(x->x==s,st)
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
function weaken(eq,eqvar) # les eq sont supposees normalise avec des coef positifs seulement.
    var = eqvar.t[1].var
    lits = copy(eq.t)
    for l in lits
        if l.var==var
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
function getid(eq,a,b,system)
    for i in a:b
        if iscontained(eq,system[i])
            return i
        end
    end
end
function solvepol(st,system,link,init,varmap)
    id = parse(Int,st[2])
    if id<1
        id = init-id
    end
    eq = copyeq(system[id])
    stack = Stack{Eq}()
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
            push!(stack,weaken(pop!(stack),))
            push!(link,-5)
        elseif i[1]=='~'||i[1]=='x'
            sign = i[1]!='~'
            var = readvar(i,varmap)
            push!(stack,Eq([Lit(0,sign,var)],0))
            push!(link,-var-10) # ATTENTION HARDCODING DE SHIFT
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
            s = slack(eq,assi)
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
    while length(ss)==0
        ss = readline(f)
    end
    st = split(ss,' ')
    removespaces(st)
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
                    push!(t,Lit(l.coef,!(l.sign ⊻ w[i+1].sign),w[i+1].var))
                else
                    # b-= (~((-w[i+1]) ⊻ l.sign)) * l.coef # w s c  0 0 c  0 1 0  1 0 0  1 1 c
                    b-= (-w[i+1].var) * l.coef 
                end
            end
        end
    end
    return Eq(t,b)
end
function readsubproof(system,systemlink,eq,w,c,f,varmap)
    # notations : 
    # proofgoal i est la i eme contrainte de la formule F /\ ~C /\ ~Ciw
    # proofgoal #i est la i eme contrainte de la subproof ?
    # -1 est la contrainte qui est declaree dans le proofgoal. elle est affecte par w
    # -2 est la negation de la contrainte declaree dans le red
    # end -1  le -1 donne l'id de la contradiction. on peux aussi mettre c -1
    # l'affectation du temoins refais une nouvelle contrainte. on en repart pas pour le rup.
    push!(system,reverse(eq))
    type,st = fuckparsers(f)
    while type !="end"
        if type == "proofgoal"
            if st[2][1] == '#'
                push!(system,reverse(applywitness(eq,w)))
            else
                push!(system,reverse(applywitness(system[parse(Int,st[2])],w)))
            end
            type,st = fuckparsers(f)
            while type != "end"
                println(st)
                eq = Eq([],0)
                if type == "u" || type == "rup"
                    eq = readeq(st,varmap,2:2:length(st)-3)     # can fail if space is missing omg
                    push!(systemlink,[-1])
                elseif type == "p" || type == "pol"
                    push!(systemlink,[-2])
                    eq = solvepol(st,system,systemlink[end],c,varmap)
                end
                type,st = fuckparsers(f)
            end
        end
        type,st = fuckparsers(f)
    end
end
function readred(system,systemlink,st,varmap,redwitness,c,f)
    print("readred")
    i = findfirst(x->x==";",st)
    eq = readeq(st[2:i],varmap)
    j = findlast(x->x==";",st)
    if i==j # detect the word begin
        j=length(st)
    end
    w = readwitness(st[i+1:j],varmap)
    if st[end] == "begin"
        readsubproof(system,systemlink,eq,w,c,f,varmap)
    end
    subsys = Eq[]
    subsystemlink = Vector{Int}[]
    redwitness[c] = Red(w,subsys,systemlink)
    print("   endred   ")
    return eq
end
function readveripb(path,file,system,varmap)
    systemlink = Vector{Int}[]
    redwitness = Dict{Int, Red}()
    com = Dict{Int, String}()
    output = conclusion = ""
    c = length(system)+1
    d = length(system)
    open(string(path,'/',file,extention),"r"; lock = false) do f
        for ss in eachline(f)
            println(ss)
            st = split(ss,' ')
            if length(ss)>0
                removespaces(st)
                type = st[1]
                eq = Eq([],0)
                if type == "u" || type == "rup"
                    eq = readeq(st,varmap,2:2:length(st)-3)     # can fail if space is missing omg
                    push!(systemlink,[-1])
                elseif type == "p" || type == "pol"
                    push!(systemlink,[-2])
                    eq = solvepol(st,system,systemlink[end],c,varmap)
                elseif type == "ia"
                    l = 0
                    if st[end] == ";" 
                        eq = readeq(st,varmap,2:2:length(st)-3)
                        normcoefeq(eq)
                        l = getid(eq,1,c-1,system)
                    else
                        eq = readeq(st,varmap,2:2:length(st)-4)
                        l = parse(Int,st[end])
                    end
                    push!(systemlink,[-3,l])
                    printeq(eq)
                elseif type == "red"  
                    push!(systemlink,[-4])
                    eq = readred(system,systemlink,st,varmap,redwitness,c,f)
                elseif type == "sol" || type == "soli"         # on ajoute la negation au probleme pour chercher d'autres solutions. jusqua contradiction finale. dans la preuve c.est juste des contraintes pour casser toutes les soloutions trouvees
                    push!(systemlink,[-5])
                    eq = findfullassi(system,st,c,varmap)
                elseif type == "output"
                    output = st[2]
                elseif type == "conclusion"
                    conclusion = st[2]
                elseif type == "*trim"
                    com[length(system)+1] = ss[7:end]
                elseif !(type in ["#","w","*","f","d","end","pseudo-Boolean"])#,"de","co","en","ps"])
                    println("unknown: ",ss)
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
function slack(eq::Eq,assi::Vector{Int8})
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
function makesmol(system,invsys,varmap,systemlink,nbopb)
    n = length(system)
    antecedants = zeros(Bool,n)
    assi = zeros(Int8,length(varmap))
    cone = zeros(Bool,n)
    cone[end] = true
    front = zeros(Bool,n)
    firstcontradiction = findfirst(x->length(x.t)==0,system)
    cone[firstcontradiction] = true
    if systemlink[firstcontradiction-nbopb][1] == -2         # pol case
        fixfront(front,systemlink[firstcontradiction-nbopb])
    else
        upquebit(system,invsys,assi,front)
        # println("  init : ",sum(front))#,findall(front)
        append!(systemlink[firstcontradiction-nbopb],findall(front))
    end
    while true in front
        i = findlast(front)
        front[i] = false
        if !cone[i] 
            cone[i] = true
            if i>nbopb
                tlink = systemlink[i-nbopb][1]
                if tlink == -1 
                    antecedants .=false ; assi.=0
                    rup(system,invsys,antecedants,i,assi,front,cone)
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
function upquebit(system,invsys,assi,antecedants)
    que = ones(Bool,length(system))
    i = 1
    while i<=length(system)
        if que[i]
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
function updateprioquebit(eq,cone,front,que,invsys,s,i,init,assi::Vector{Int8},antecedants,r0,r1,r2)
    for l in eq.t
        if l.coef > s && assi[l.var]==0
            assi[l.var] = l.sign ? 1 : 2
            antecedants[i] = true
            for id in invsys[l.var]
                if id<=init
                    que[id] = true
                    if cone[id]
                        r2 = min(r2,id)
                    elseif front[id]
                        r1 = min(r1,id)
                    else
                        r0 = min(r0,id)
                    end
                end
            end
        end
    end
    return r0,r1,r2
end
function rup(system,invsys,antecedants,init,assi,front,cone)
    que = ones(Bool,init)
    rev = reverse(system[init])
    i = 1
    prio = 2
    r0 = r1 = 1
    r2 = init+1
    while i<=init && prio>=0
        if que[i] && (prio==0 || (prio==1&&front[i]) || (prio==2&&cone[i]))
            # print(i,' ')
            eq = i==init ? rev : system[i]
            s = slack(eq,assi)
            if s<0
                antecedants[i] = true
                return
            else
                r0,r1,r2 = updateprioquebit(eq,cone,front,que,invsys,s,i,init,assi,antecedants,r0,r1,r2)
            end
            que[i] = false
        end
        i+=1
        if prio == 2
            if r2<i 
                i = r2
                r2 = init+1
            elseif i == init+1
                if r1<init+1
                    prio = 1
                    i = r1
                    r1 = init+1
                elseif r0<init+1
                    prio = 0
                    i = r0
                    r0 = init+1
                else
                    prio = -1
                end
            end
        elseif prio == 1
            if r2<init+1
                prio = 2
                r1 = min(i,r1)
                i = r2
                r2 = init+1
            elseif r1<i 
                i = r1
                r1 = init+1
            elseif i == init+1
                if r0<init+1
                    prio = 0
                    i = r0
                    r0 = init+1
                else
                    prio = -1
                end
            end
        elseif prio==0
            if r2<init+1
                prio = 2
                r1 = min(i,r1)
                i = r2
                r2 = init+1
            elseif r1<init+1
                prio = 1
                r0 = min(i,r0)
                i = r1
                r1 = init+1
            elseif r0<i 
                i = r0
                r0 = init+1
            elseif i == init+1
                prio = -1
            end
        end
    end
    printstyled(" rup faled \n"; color = :red)
end
function readinstance(path,file)
    system,varmap = readopb(path,file)
    nbopb = length(system)
    system,systemlink,redwitness,output,conclusion,com,version = readveripb(path,file,system,varmap)
    return system,systemlink,redwitness,nbopb,varmap,output,conclusion,com,version
end
function runtrimmer(file)
    tvp = @elapsed begin
        v1 = read(`veripb $proofs/$file.opb $proofs/$file$extention`)
    end
    print(prettytime(tvp),' ')
    tri = @elapsed begin
        system,systemlink,redwitness,nbopb,varmap,output,conclusion,com,version = readinstance(proofs,file)
    end
    print(prettytime(tri),' ')
    invsys = getinvsys(system,varmap)
    normcoefsystem(system)
    tms = @elapsed begin
        cone = makesmol(system,invsys,varmap,systemlink,nbopb)
    end
    println(prettytime(tms))
    twc = @elapsed begin
        writeconedel(proofs,file,version,system,cone,systemlink,redwitness,nbopb,varmap,output,conclusion)
    end

    printcom(file,system,invsys,cone,com)
    printsummit(cone,invsys)
    if file[1]=='b'
        vcone = varcone(system,cone,varmap)
        patcone,tarcone = patterntargetcone(vcone,varmap)
        printbioconegraphs(file,cone,patcone,tarcone)
    end
    # printcone(cone,nbopb)

    writeshortrepartition(proofs,file,cone,nbopb)
    tvs = @elapsed begin
        v2 = read(`veripb $proofs/smol.$file.opb $proofs/smol.$file$extention`)
    end
    so = stat(string(proofs,"/",file,".opb")).size + stat(string(proofs,"/",file,extention)).size
    st = stat(string(proofs,"/smol.",file,".opb")).size + stat(string(proofs,"/smol.",file,extention)).size
    if file[1] == 'b'
        t = [roundt([parse(Float64,file[end-5:end-3]),parse(Float64,file[end-2:end]),so,st,st/so,tvp,tvs,tvs/tvp,tms,twc,tri],3)]
    elseif file[1] == 'L'
        t = [roundt([parse(Float64,split(file,'g')[2]),parse(Float64,split(file,'g')[3]),so,st,st/so,tvp,tvs,tvs/tvp,tms,twc,tri],3)]
    end
    printtabular(t)
    open(string(proofs,"/atable"), "a") do f
        write(f,string(t[1],",\n"))
    end
    if v1!=v2
        printstyled("catch (u cant see me)\n"; color = :red)
        open(string(proofs,"/afailedtrims"), "a") do f
            write(f,string(file," \n"))
        end
    end
end
function run_bio_list(l=1,u=length(biolist),m=1)
    p = sortperm(biostats)
    for i in l:m:u
        ins = biolist[p[i]]
        run_bio_solver(ins)
        println(i," ",ins)
        runtrimmer(ins)
    end
end
function run_LV_list(l=1,u=length(LVlist),m=1)
    p = sortperm(LVstats)
    for i in l:m:u
        ins = LVlist[p[i]]
        run_LV_solver(ins)
        println(i," ",ins)
        runtrimmer(ins)
    end
end
function run_bio_solver(ins)
    path = string(benchs,"/biochemicalReactions")
    cd()
    pattern = string(ins[4:6],".txt")
    target = string(ins[7:9],".txt")
    solve(ins,path,pattern,path,target,"lad",2_000_000,1000,true)
end
function run_LV_solver(ins)
    path = string(benchs,"/LV")
    cd()
    st = split(ins,'g')
    pattern = string('g',st[2])
    target = string('g',st[3])
    solve(ins,path,pattern,path,target,"lad",100_000,1000,true,true)
end

const benchs = "veriPB/newSIPbenchmarks"
const solver = "veriPB/subgraphsolver/glasgow-subgraph-solver/build/glasgow_subgraph_solver"
const proofs = "veriPB/proofs"    
# const proofs = "veriPB/prooframdisk"    
# const benchs = "newSIPbenchmarks"
# const solver = "glasgow-subgraph-solver/build/glasgow_subgraph_solver"
# const proofs = "/cluster/proofs"
# const extention = ".veripb"
const extention = ".pbp"
# const path = proofs
const version = "2.0"

cd()
# include("abiolist.jl")
# include("aLVlist.jl")
include("ladtograph.jl")
include("trimerPrints.jl")

function main()
    # run_LV_solver()
    # run_si_solver()
    # okinstancelist()
    # run_bio_solver()
    # run_LV_list(1,1,1)
    # run_LV_list(172,length(LVlist),1)
    # run_LV_list(length(LVlist),1,-1)
    run_bio_list(length(biolist)-1500,length(biolist),1)
    # run_bio_list(1580,length(biolist),1)
    # run_bio_list(13226,length(biolist),1)
    # run_bio_list(13273,length(biolist),1)
    # run_bio_list(14275,length(biolist),1)

    # readrepartition()
end

# main()

# ins = "test/subproof"
# println(ins)
# runtrimmer(ins)


# ins = "bio037002"
# ins = "bio019014"
# ins = "bio112002"

# long "bio055018"


# ins = "bio021002"
# ins = "bio070014"

# run_bio_solver(ins)

# ins = "LVg20g57"
# ins = "LVg34g61"
# run_LV_solver(ins)
ins = "mult_single_bc"
runtrimmer(ins)

#=
optu rup
je rerup a partir des antecedants ?

opti pol


=#
# using Plots,ColorSchemes


# function f(x, y)
#     r = sqrt(x^2 + y^2)
#     return cos(r) / (1 + r)
# end
# x = range(0, 2π, length = 30)
# p = heatmap(x, x, f, c = :thermal)

# savefig(p,string(proofs,"/aimg/test.png"))

# Plots.pdf(p,string(proofs,"/aimg/test"))


# draw(PNG(string(proofs,"/aimg/test"), 16cm, 16cm), plot(x, y))

# println("done")

#=
102 LVg26g52
degre 139/1520
hall 0/1
26 & 52 & 5.722 MB & 785.1 KB & 14 & 0.65 & 0.12 & 19 & 0.26 & 0.05 & 4.02 \\\hline
103 LVg46g51
degre 1261/1290
hall 1/1
46 & 51 & 23.21 MB & 2.048 MB & 9 & 1.73 & 0.62 & 36 & 1.11 & 0.25 & 25.8 \\\hline


116 LVg45g51
degre 1120/1170
hall 1/1
45 & 51 & 22.58 MB & 2.614 MB & 12 & 1.74 & 0.63 & 36 & 0.65 & 0.09 & 31.7 \\\hline
117 LVg38g58
degre 657/1650
hall 1/1
38 & 58 & 7.758 MB & 1.585 MB & 20 & 0.91 & 0.34 & 38 & 0.66 & 0.06 & 12.0 \\\hline


141 LVg2g57
adjacency1 64/3130
adjacency2 64/3130
backtrack 5/5
degre 30/2500
fail 24/41
hall 9/31
2 & 57 & 1.494 MB & 91.33 KB & 6 & 0.67 & 0.07 & 10 & 0.21 & 0 & 0.17 \\\hline
169 LVg2g100
adjacency1 6971/40000
adjacency2 6971/40000
degre 992/2016
2 & 100 & 15.39 MB & 2.531 MB & 16 & 5.82 & 0.81 & 14 & 4.78 & 0.18 & 8.39 \\\hline

170 LVg5g72
adjacency1 333/15066
adjacency10 310/1987
adjacency11 299/1936
adjacency12 244/1841
adjacency13 212/1779
adjacency14 179/1706
adjacency15 157/1346
adjacency16 157/1226
adjacency17 136/1026
adjacency18 106/906
adjacency19 86/706
adjacency2 333/15066
adjacency20 31/571
adjacency21 10/520
adjacency22 0/360
adjacency23 0/320
adjacency24 0/200
adjacency25 0/200
adjacency26 0/160
adjacency27 0/80
adjacency28 0/40
adjacency29 0/40
adjacency3 327/2064
adjacency30 0/40
adjacency4 327/2064
adjacency5 324/2031
adjacency6 321/1998
adjacency7 321/1998
adjacency8 321/1998
adjacency9 320/1987
backtrack 46/180
degre 222/5843
fail 1/254
hall 20/198
nds 6/56
5 & 72 & 15.62 MB & 901.7 KB & 6 & 18.2 & 2.11 & 12 & 25.4 & 0.06 & 13.5 \\\hline

171 LVg3g70
adjacency1 2045/29260
adjacency2 2045/29260
backtrack 121/157
degre 1916/2260
fail 233/552
hall 101/740
nds 780/810
3 & 70 & 15.87 MB & 1.524 MB & 10 & 6.04 & 0.78 & 13 & 270.0 & 0.28 & 7.05 \\\hline

172 LVg3g61
adjacency1 419/19860
adjacency2 419/19860
backtrack 6714/8197
fail 1486/23235
hall 126/29942
nogood 4/339
3 & 61 & 23.26 MB & 1.043 MB & 4 & 44.8 & 3.76 & 8 & 1010.0 & 0.31 & 15.9 \\\hline
=#

#=
export JULIA_NUM_THREADS=192
julia --check-bounds=no 'trimer 5.jl'
=#
# scp circuit_prune_skip_test.html arthur@fataepyc-01.dcs.gla.ac.uk:/scratch/circuit_prune_skip_test.html 

# scp -r \\wsl.localhost\Ubuntu\home\arthur_gla\veriPB\trim\smol-proofs2\Instances\ arthur@fataepyc-01.dcs.gla.ac.uk:/users/grad/arthur/smol-proofs2
# scp -r /home/arthur_gla/veriPB/newSIPbenchmarks/ arthur@fataepyc-01.dcs.gla.ac.uk:/users/grad/arthur/
# find . -name "*Zone.Identifier" -type f -delete 
# find . -name ".*" -type f -delete 
# ssh arthur@fataepyc-01.dcs.gla.ac.uk
# scp arthur@fataepyc-01.dcs.gla.ac.uk:/cluster/proofs/smol.bio063002.veripb smol.bio063002.veripb
# scp arthur@fataepyc-01.dcs.gla.ac.uk:/cluster/proofs/smol.bio170041.veripb smol.bio170041.veripb
# scp arthur@fataepyc-01.dcs.gla.ac.uk:/cluster/proofs/times times2
# cd /home/arthur_gla/veriPB/trim/smol-proofs2/
# scp arthur@fataepyc-01.dcs.gla.ac.uk:/cluster/proofs/atable atableserv
# /scratch
# mult_single_bc.opb
# mult_single_bc.pbp
# scp arthur@fataepyc-01.dcs.gla.ac.uk:/scratch/mult_single_bc.opb mult_single_bc.opb
# scp arthur@fataepyc-01.dcs.gla.ac.uk:/scratch/mult_single_bc.pbp mult_single_bc.pbp

# scp -r arthur@fataepyc-01.dcs.gla.ac.uk:/scratch/proofs_to_trim/small/ small/
# scp -r arthur@fataepyc-01.dcs.gla.ac.uk:/scratch/proofs_to_trim/medium/ medium/