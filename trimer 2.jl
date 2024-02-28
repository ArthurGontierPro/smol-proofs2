
struct Var # variables with two indexes x and v
    x::Int
    v::Int
end
mutable struct Lit
    coef::Int
    sign::Bool
    var::Var
end
mutable struct Eq
    t::Vector{Lit}
    b::Int
end
function printvar(v)
    print('x',v.x,'_',v.v)
end
function printlit(l)
    print(l.coef,' ')
    if !l.sign print('~') end
    printvar(l.var)
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
function printsys(system,subset)
    for id in eachindex(system)
        if id in subset
            print(id," ")
            printeq(system[id])
        end
    end
end
function addinvsys(invsys,var,id)
    if haskey(invsys,var)
        push!(invsys[var],id)
    else
        invsys[var] = [id]
    end
end
function addinvsyseq(invsys,eq,id)
    for l in eq.t
        addinvsys(invsys,l.var,id)
    end
end
function readvar(s)
    tmp = split(split(s,'x')[end],'_')
    return Var(parse(Int,tmp[1]),parse(Int,tmp[2]))
end
function readeq(st)
    return readeq(st,1:2:length(st)-3)
end
function readeq(st,range)
    lits = Vector{Lit}(undef,(length(range)))
    for i in range
        coef = parse(Int,st[i])
        sign = st[i+1][1]=='x'
        var = readvar(st[i+1])
        lits[(i - range.start)÷range.step+1] = Lit(coef,sign,var)
    end
    eq = Eq(lits,parse(Int,st[end-1])) 
    return eq
end
function readopb(path,file)
    system = Vector{Eq}
    invsys = Dict{Var,Vector{Int}}()
    open(string(path,file,".opb"),"r") do f
        s = readlines(f)
        nbctr = parse(Int,split(s[1],' ')[end])
        c = 1
        system = Vector{Eq}(undef,nbctr)
        for ss in s
            if ss[1] != '*'                                     #do not parse comments
                st = split(ss,' ')                              #structure of line is: int var int var ... >= int ; 
                eq = readeq(st)
                system[c] = eq
                addinvsyseq(invsys,eq,c)
                c+=1
            end
        end
    end
    return system,invsys
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
function addlit(lit1,lit2)
    lit1,c1 = normlit(lit1)
    lit2,c2 = normlit(lit2)
    return Lit(lit1.coef+lit2.coef,true,lit1.var),c1+c2
end
function removenulllits(lits)
    return [l for l in lits if l.coef!=0]
end
function islexicolesslit(l1,l2)
    return islexicolessvar(l1.var,l2.var)
end
function islexicolessvar(v1,v2)
    if v1.x == v2.x
        return v1.v < v2.v
    else
        return v1.x < v2.x
    end
end
function addeq(eq1,eq2)
    lits = copy(eq1.t)
    vars = [l.var for l in lits]
    c = 0
    for lit in eq2.t
        i = findfirst(x->x==lit.var,vars)
        if !isnothing(i)
            tmplit,tmpc = addlit(lit,lits[i])
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
function solvepol(st,system)
    eq1 = system[parse(Int,st[2])]
    for i in 3:2:length(st)-1
        eq1 = addeq(eq1,system[parse(Int,st[i])])
    end
    return eq1
end    
function solvesol(st)
    lits = Vector{Lit}(undef,length(st)-1)
    for i in 2:length(st)
        sign = st[i][1]=='x'
        var = readvar(st[i])
        lits[i-1] = Lit(1,!sign,var)
    end
    eq = Eq(lits,1) 
    return eq
end
function readveripb(path,file,system,invsys)
    systemlink = Vector{Vector{Int}}
    open(string(path,file,".veripb"),"r") do f
        s = readlines(f)
        nbctr = parse(Int,split(s[end],' ')[end-1])-1
        c = length(system)
        system = vcat(system,Vector{Eq}(undef,nbctr-c))
        systemlink = Vector{Vector{Int}}(undef,nbctr)
        c+=1
        for ss in s
            st = split(ss,' ')
            eq = Eq([],0)
            if ss[1:2] == "p "
                # systemlink[c] = [parse(Int,st[i]) for i in [2,3:2:length(st)-1]] 
                systemlink[c] = vcat([parse(Int,st[2])],[parse(Int,st[i]) for i in 3:2:length(st)-1]) 
                eq = solvepol(st,system)
            elseif ss[1:2] == "u "
                start = 2
                if ss[3] == ' '                                     # weard case of file with multiple spaces
                    start = 3
                end
                eq = readeq(st,start:2:length(st)-3)
            elseif ss[1:2] == "j "
                systemlink[c] = [parse(Int,st[2])]
                eq = readeq(st,3:2:length(st)-3)
            elseif ss[1:2] == "v "                                  # on ajoute la negation au probleme pour chercher d'autres solutions. jusqua contradiction finale. dans la preuve c.est juste des contraintes pour casser toutes les soloutions trouvees
                eq = solvesol(st)
            end
            if length(eq.t)!=0 || eq.b!=0
                system[c] = eq
                addinvsyseq(invsys,eq,c)
                c+=1
            end
        end
    end
    return system,invsys,systemlink
end
function slack(eq,isassi,assi)
    c=0
    for l in eq.t
        if isassi[l.var.x+1,l.var.v+1]
            if assi[l.var.x+1,l.var.v+1] == l.sign
                c+=l.coef 
            end
        else
            c+=l.coef
        end
    end
    return c-eq.b
end
function reverse(eq)
    c=0
    lits = [Lit(l.coef,l.sign,Var(l.var.x,l.var.v)) for l in eq.t]
    for l in lits
        l.sign = !l.sign
        c+=l.coef
    end
    return Eq(lits,-eq.b+1+c)
end
function initassignement(invsys)
    vars = eachindex(invsys)
    maxx = maximum(x->x.x,vars)
    maxv = maximum(x->x.v,vars)
    return zeros(Bool,maxx+1,maxv+1),zeros(Bool,maxx+1,maxv+1)
end
function reset(mats)
    for mat in mats
        mat .=false
    end
end
function nbfreelits(eq,isassi)
    s = x = v = 0
    for l in eq.t
        x,v = l.var.x+1,l.var.v+1
        if !isassi[x,v]
            s+=1
        end
    end
    return s
end
function comparefreelits(eq1,eq2,system,isassi)
    return nbfreelits(system[eq1],isassi) < nbfreelits(system[eq2],isassi)
end
function smolproof4(system,invsys,systemlink,nbopb)
    n = length(system)
    antecedants = zeros(Bool,n)
    isassi,assi = initassignement(invsys)

    cone = zeros(Bool,n)
    cone[end] = true
    front = zeros(Bool,n)
    updumb(system,invsys,front)                     #front now contains the antecedants of the final claim
    println(findall(front))
    while true in front
        i = findlast(front)
        front[i] = false
        if !cone[i] 
            cone[i] = true
            if i>nbopb
                reset([antecedants,isassi,assi])
                if isassigned(systemlink,i)
                    for j in systemlink[i]
                        antecedants[j] = true
                    end
                else
                    rupdumb(system,invsys,antecedants,i,isassi,assi)
                end
                front = front .|| antecedants
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
                println(findall(antecedants))
                printeq(eq)
                printsys(system)
                println(findall(assi))
                println(findall(x->!x,assi))
                for e in system
                    println(slack(e,isassi,assi))
                    printeq(e)
                end
                return 
            else
                for l in eq.t
                    x,v = l.var.x+1,l.var.v+1
                    if !isassi[x,v] && l.coef > s
                        println("fix ",x)
                        print(i,"  ")
                        printeq(eq)
                        assi[x,v] = l.sign
                        isassi[x,v] = true 
                        antecedants[i] = true
                        changes = true
                    end
                end
            end
        end
    end
    println("updumb Failed")
end
function rupdumb(system,invsys,antecedants,init,isassi,assi)
    rev = reverse(system[init])
    changes = true
    while changes
        for i in 1:init
            eq = i==init ? rev : system[i]
            s = slack(eq,isassi,assi)
            if s<0
                antecedants[i] = true
                return 
            else
                for l in eq.t
                    x,v = l.var.x+1,l.var.v+1
                    if !isassi[x,v] && l.coef > s
                        assi[x,v] = l.sign
                        isassi[x,v] = true 
                        antecedants[i] = true
                        changes = true
                    end
                end
            end
        end
    end
    println("rupdumb Failed")
end

function inittest()
    system = Vector{Eq}(undef,10)
    invsys = Dict{Var,Vector{Int}}()
    # system[1] = Eq([Lit(1,false,Var(2,0)),Lit(1,false,Var(3,0))],1)
    system[1] = Eq([Lit(1,false,Var(2,0)),Lit(1,true,Var(3,0))],1)#corr
    system[2] = Eq([Lit(1,true ,Var(1,0)),Lit(1,true ,Var(3,0))],1)
    system[3] = Eq([Lit(1,false,Var(1,0)),Lit(1,true ,Var(2,0))],1)
    system[4] = Eq([Lit(1,false,Var(1,0)),Lit(1,false,Var(2,0))],1)
    system[5] = Eq([Lit(1,true ,Var(1,0)),Lit(1,false,Var(2,0))],1)
    # system[6] = Eq([Lit(1,true ,Var(2,0)),Lit(1,true ,Var(3,0))],1)
    system[6] = Eq([Lit(1,true ,Var(2,0)),Lit(1,false ,Var(3,0))],1)#corr
    invsys[Var(1,0)] = [2,3,4,5,8]
    invsys[Var(2,0)] = [1,3,4,5,6]
    invsys[Var(3,0)] = [1,2,6,10]
    systemlink = Vector{Vector{Int}}(undef,11)
    system[7] = addeq(system[4],system[5])
    systemlink[7] = [4,5]
    addinvsyseq(invsys,system[7],7)
    system[8] = Eq([Lit(1,false,Var(1,0))],1)
    system[9] = addeq(addeq(system[1],system[2]),system[3])
    systemlink[9] = [1,2,3]
    addinvsyseq(invsys,system[9],9)
    system[10] = Eq([Lit(1,true,Var(3,0))],1)
    systemlink[10] = [9]
    # system[11] = Eq([],1)
    nbopb = 6
    file = "inittest"
    cone =  makesmol(system,invsys,systemlink,nbopb)

    isassi,assi = initassignement(invsys)

    for e in system
        println(nbfreelits(e,isassi))
    end

    front = ones(Bool,10)



    nto = sum(cone[1:nbopb])
    ntp = sum(cone[nbopb+1:end])
    println(file,"\n        ",round(Int,100-100*nto/nbopb)," %    (",nto,"/",nbopb,")\n        ",round(Int,100-100*ntp/(length(system)-nbopb))," %    (",ntp,"/",(length(system)-nbopb),")")
    println(findall(cone))
end
function runinstance(path,file)
    system,invsys = readopb(path,file)
    nbopb = length(system)
    system,invsys,systemlink = readveripb(path,file,system,invsys)
    return system,invsys,systemlink,nbopb
end
function makesmol(system,invsys,systemlink,nbopb)
    normcoefsystem(system)
    # printsys(system)
    return smolproof4(system,invsys,systemlink,nbopb)
    # printsys(system,cone)
end
function main()
    println("==========================")


    inittest()
    path = "\\\\wsl.localhost\\Ubuntu\\home\\arthur_gla\\veriPB\\trim\\smol-proofs2\\Instances\\"
    files = cd(readdir, path)
    files = [s[1:end-4] for s in files if s[end-3:end]==".opb"]

    # println("threads available:",Threads.nthreads())

    # Threads.@threads 
    # for file in files
    #     system,invsys,systemlink,nbopb = runinstance(path,file)
    #     cone =  makesmol(system,invsys,systemlink,nbopb)
    #     nto = sum(cone[1:nbopb])
    #     ntp = sum(cone[nbopb+1:end])
    #     println(file,"\n        ",round(Int,100-100*nto/nbopb)," %    (",nto,"/",nbopb,")\n        ",round(Int,100-100*ntp/(length(system)-nbopb))," %    (",ntp,"/",(length(system)-nbopb),")")
    # end
end

main()

# println("threads available:",Threads.nthreads())
