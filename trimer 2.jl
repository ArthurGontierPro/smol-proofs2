
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
    print(l.coef,' ')
    if !l.sign print('~') end
    print(l.var)
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
function readopb(path,file)
    system = Vector{Eq}
    invsys = Vector{Vector{Int}}
    varmap = Vector{String}
    open(string(path,file,".opb"),"r") do f
        s = readlines(f)
        nbctr,varmap = opbsize(s)
        nbvar = length(varmap)
        c = 1
        system = Vector{Eq}(undef,nbctr)
        invsys = Vector{Vector{Int}}(undef,nbvar)
        for ss in s
            if ss[1] != '*'                                     #do not parse comments
                st = split(ss,' ')                              #structure of line is: int var int var ... >= int ; 
                eq = readeq(st,varmap)
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
    eq.b = max(c+eq.b,0)
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
function divide(eq,d)
    lits = copy(eq1)
    for l in lits
        l.coef = ceil(Int,l.coef/d)
    end
    return Eq(lits,ceil(Int,eq.b/d))
end
function solvepol(st,system,systemlink,c)
    id = parse(Int,st[2])
    eq1 = copy(system[id])
    systemlink[c] = [id]
    for i in 3:2:length(st)-1
        if st[i+1] == '+'
            id = parse(Int,st[i])
            eq1 = addeq(eq1,system[id])
            push!(systemlink[c],id)
        elseif st[i+1] == 'd'
            eq1 = divide(eq1,parse(Int,st[i]))
        else
            println("unknown pol operator")
        end
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
function proofsize(s)
    nbctr = 0
    for ss in s
        if ss[1:2] in ["p ","u ","re","so"]
            nbctr+=1
        end
    end
    return nbctr
end
function readveripb(path,file,system,invsys,varmap)
    systemlink = Vector{Vector{Int}}
    open(string(path,file,".veripb"),"r") do f
        s = readlines(f)
        # nbctr = parse(Int,split(s[end],' ')[end-1])-1
        c = length(system)
        nbctr = proofsize(s) + c
        system = vcat(system,Vector{Eq}(undef,nbctr-c))
        systemlink = Vector{Vector{Int}}(undef,nbctr)
        c+=1
        for ss in s
            st = split(ss,' ')
            eq = Eq([],0)
            if ss[1:2] == "red "  
                println("red not implemented yet")
            end          
            if ss[1:2] == "p "
                eq = solvepol(st,system,systemlink,c)
            elseif ss[1:2] == "u "
                start = 2
                if ss[3] == ' '                                     # weard case of file with multiple spaces
                    start = 3
                end
                eq = readeq(st,varmap,start:2:length(st)-3)
            elseif ss[1:2] == "j "
                systemlink[c] = [parse(Int,st[2])]
                eq = readeq(st,3:2:length(st)-3)
            elseif ss[1:2] == "solx "                                  # on ajoute la negation au probleme pour chercher d'autres solutions. jusqua contradiction finale. dans la preuve c.est juste des contraintes pour casser toutes les soloutions trouvees
                eq = solvesol(st)
            end
            if length(eq.t)!=0 || eq.b!=0
                system[c] = eq
                addinvsys(invsys,eq,c)
                c+=1
            end
        end
    end
    return system,invsys,systemlink
end
function slack(eq,isassi,assi)
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
    return c-eq.b
end
function reverse(eq)
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
    println("rupdumb Failed")
end

function inittest()
    system = Vector{Eq}(undef,10)
    invsys = Vector{Vector{Int}}(undef,3)
    # system[1] = Eq([Lit(1,false,Var(2,0)),Lit(1,false,Var(3,0))],1)
    system[1] = Eq([Lit(1,false,2),Lit(1,true,3)],1)#corr
    system[2] = Eq([Lit(1,true ,1),Lit(1,true ,3)],1)
    system[3] = Eq([Lit(1,false,1),Lit(1,true ,2)],1)
    system[4] = Eq([Lit(1,false,1),Lit(1,false,2)],1)
    system[5] = Eq([Lit(1,true ,1),Lit(1,false,2)],1)
    # system[6] = Eq([Lit(1,true ,Var(2,0)),Lit(1,true ,Var(3,0))],1)
    system[6] = Eq([Lit(1,true ,2),Lit(1,false ,3)],1)#corr
    invsys[1] = [2,3,4,5,8]
    invsys[2] = [1,3,4,5,6]
    invsys[3] = [1,2,6,10]
    systemlink = Vector{Vector{Int}}(undef,11)
    system[7] = addeq(system[4],system[5])
    systemlink[7] = [4,5]
    addinvsys(invsys,system[7],7)
    system[8] = Eq([Lit(1,false,1)],1)
    system[9] = addeq(addeq(system[1],system[2]),system[3])
    systemlink[9] = [1,2,3]
    addinvsys(invsys,system[9],9)
    system[10] = Eq([Lit(1,true,3)],1)
    systemlink[10] = [9]
    # system[11] = Eq([],1)
    nbopb = 6
    file = "inittest"
    cone =  makesmol(system,invsys,systemlink,nbopb)
    nto = sum(cone[1:nbopb])
    ntp = sum(cone[nbopb+1:end])
    println(file,"\n        ",round(Int,100-100*nto/nbopb)," %    (",nto,"/",nbopb,")\n        ",round(Int,100-100*ntp/(length(system)-nbopb))," %    (",ntp,"/",(length(system)-nbopb),")")
    println(findall(cone))
end
function runinstance(path,file)
    system,invsys,varmap = readopb(path,file)
    nbopb = length(system)
    system,invsys,systemlink = readveripb(path,file,system,invsys,varmap)
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
    for file in files
        system,invsys,systemlink,nbopb = runinstance(path,file)
        cone =  makesmol(system,invsys,systemlink,nbopb)
        nto = sum(cone[1:nbopb])
        ntp = sum(cone[nbopb+1:end])
        println(file,"\n        ",round(Int,100-100*nto/nbopb)," %    (",nto,"/",nbopb,")\n        ",round(Int,100-100*ntp/(length(system)-nbopb))," %    (",ntp,"/",(length(system)-nbopb),")")
    end
end

main()

# println("threads available:",Threads.nthreads())
