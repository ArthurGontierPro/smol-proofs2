
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
        nbctr = parse(Int,split(s[end],' ')[end-1])
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
    # vars = collect(keys(invsys))
    vars = eachindex(invsys)
    maxx = maximum(x->x.x,vars)
    maxv = maximum(x->x.v,vars)
    return  zeros(Bool,maxx+1,maxv+1),zeros(Bool,maxx+1,maxv+1)
end
function unitpropag(system,invsys,init,isassi,assi) 
    front = Set(Int[init])
    antecedants = Set(Int[])
    id = init
    eq = system[init]
    s = 0
    while length(front)>0
        id = pop!(front)
        eq = id==init ? reverse(system[id]) : system[id]
        s = slack(eq,isassi,assi)
        if s<0
            push!(antecedants,id)
            return antecedants
        else
            for l in eq.t
                if !isassi[l.var.x+1,l.var.v+1] && l.coef > s
                    isassi[l.var.x+1,l.var.v+1] = true
                    assi[l.var.x+1,l.var.v+1] = l.sign
                    push!(antecedants,id)
                    for j in invsys[l.var]
                        if j!=id
                            push!(front,j)
                        end
                    end
                end
            end
        end
    end
    return antecedants
end
function smolproof2(system,invsys,systemlink)
    n = length(system)
    isassi,assi = initassignement(invsys)
    antecedants = Set(Int[])
    cone = zeros(Bool,n)
    front = zeros(Bool,n)
    front[n-1] = true
    while true in front
        id = findfirst(front)
        front[id] = false
        if isassigned(systemlink,id)
            antecedants=systemlink[id]
        else
            isassi .= false
            assi .= false
            antecedants = unitpropag(system,invsys,id,isassi,assi)
        end
        for i in antecedants
            if !cone[i]
                cone[i]=true
                front[i]=true
            end
        end
    end
    return cone
end
function inittest()
    system = Vector{Eq}(undef,11)
    invsys = Dict{Var,Vector{Int}}()
    # system[1] = Eq([Lit(1,false,Var(2,0)),Lit(1,false,Var(3,0))],1)
    system[1] = Eq([Lit(1,false,Var(2,0)),Lit(1,true,Var(3,0))],1)#corr
    system[2] = Eq([Lit(1,true ,Var(1,0)),Lit(1,true ,Var(3,0))],1)
    system[3] = Eq([Lit(1,false,Var(1,0)),Lit(1,true ,Var(2,0))],1)
    system[4] = Eq([Lit(1,false,Var(1,0)),Lit(1,false,Var(2,0))],1)
    system[5] = Eq([Lit(1,true ,Var(1,0)),Lit(1,false,Var(2,0))],1)
    system[6] = Eq([Lit(1,true ,Var(2,0)),Lit(1,true ,Var(3,0))],1)
    invsys[Var(1,0)] = [2,3,4,5,8]
    invsys[Var(2,0)] = [1,3,4,5,6]
    invsys[Var(3,0)] = [1,2,6,10]
    systemlink = Vector{Vector{Int}}(undef,11)
    system[7] = addeq(system[4],system[5])
    systemlink[7] = [4,5]
    addinvsyseq(invsys,system[7],7)
    system[8] = Eq([Lit(1,true,Var(1,0))],1)
    system[9] = addeq(addeq(system[1],system[2]),system[3])
    systemlink[9] = [1,2,3]
    addinvsyseq(invsys,system[9],9)
    system[10] = Eq([Lit(1,false,Var(3,0))],1)
    systemlink[10] = [9]
    system[11] = Eq([],1)
    return system,invsys,systemlink
end
function runinstance(path,file)
    system,invsys = readopb(path,file)
    system,invsys,systemlink = readveripb(path,file,system,invsys)
    return system,invsys,systemlink
end
function makesmol(system,invsys,systemlink)
    normcoefsystem(system)
    # printsys(system)
    return smolproof2(system,invsys,systemlink)
    # printsys(system,cone)
end

function main()
    println("==========================")
    # system,invsys,systemlink = inittest()
    # makesmol(system,invsys,systemlink)
    # path = "\\\\wsl.localhost\\Ubuntu\\home\\arthur_gla\\veriPB\\trim\\"
    path = "\\\\wsl.localhost\\Ubuntu\\home\\arthur_gla\\veriPB\\trim\\smol-proofs\\sip_proofs\\"
    # file = "g2-g3"
    # file = "g2-g5"
    # file = "g7-g23"
    # file = "g24-g28"
    println("threads available:",Threads.nthreads())

    Threads.@threads for file in ["g2-g3","g2-g5","g3-g6","g4-g10","g4-g14","g4-g33","g5-g6","g7-g11","g7-g15","g7-g23","g7-g28","g7-g33","g8-g9","g10-g14","g10-g25","g11-g13","g11-g28","g17-g25","g18-g22","g24-g28"]
        system,invsys,systemlink = runinstance(path,file)
        cone = makesmol(system,invsys,systemlink)
        println(file,":",sum(cone),"/",length(system))
    end
end

main()


#= 
==========================
g2-g3:
  0.015955 seconds (7.45 k allocations: 1.010 MiB)
  0.112484 seconds (200.47 k allocations: 23.322 MiB, 72.17% compilation time)
  0.574211 seconds (12.24 k allocations: 17.901 MiB)
1151/2531
g2-g5:
  0.012458 seconds (8.87 k allocations: 1.188 MiB)
  0.154311 seconds (178.67 k allocations: 31.551 MiB, 42.84% gc time)
  0.944702 seconds (13.41 k allocations: 19.213 MiB)
1210/2643
g3-g6:
  0.016844 seconds (20.48 k allocations: 2.673 MiB)
  0.059255 seconds (373.56 k allocations: 42.712 MiB, 5.60% gc time)
  3.866249 seconds (25.90 k allocations: 107.933 MiB, 0.28% gc time)
5292/6561
g4-g10:
  0.027052 seconds (127.54 k allocations: 16.919 MiB)
  0.020573 seconds (15.10 k allocations: 2.313 MiB)
  3.109376 seconds (148.18 k allocations: 564.057 MiB, 1.27% gc time)
3731/3913
g4-g14:
  0.044422 seconds (164.60 k allocations: 20.567 MiB)
  0.052560 seconds (64.25 k allocations: 9.464 MiB, 8.88% gc time)
  3.697321 seconds (142.81 k allocations: 372.954 MiB, 0.67% gc time)
4384/5328
g4-g33:
  0.095689 seconds (405.20 k allocations: 53.279 MiB, 4.81% gc time)
  0.050947 seconds (108.16 k allocations: 21.007 MiB, 11.53% gc time)
 61.463491 seconds (400.45 k allocations: 1.452 GiB, 0.13% gc time)
10061/10183
g5-g6:
  0.027208 seconds (26.59 k allocations: 3.473 MiB)
  0.355994 seconds (1.52 M allocations: 185.857 MiB, 42.89% gc time)
 14.876507 seconds (35.09 k allocations: 511.352 MiB, 1.04% gc time)
16027/26090
g7-g11:
  0.096185 seconds (353.21 k allocations: 46.271 MiB, 3.97% gc time)
  0.022820 seconds (19.47 k allocations: 4.870 MiB)
 59.304870 seconds (419.86 k allocations: 1.884 GiB, 0.14% gc time)
8622/8648
g7-g15:
  0.060827 seconds (437.18 k allocations: 57.182 MiB, 8.27% gc time)
  0.037761 seconds (79.31 k allocations: 15.907 MiB, 14.69% gc time)
 73.420885 seconds (394.00 k allocations: 1.535 GiB, 0.08% gc time)
8899/10912
g7-g23:
  0.093485 seconds (783.34 k allocations: 102.533 MiB, 9.16% gc time)
  0.050182 seconds (230.07 k allocations: 63.655 MiB, 14.89% gc time)
227.013073 seconds (705.20 k allocations: 5.889 GiB, 0.09% gc time)
16385/16653
g7-g28:
  0.067647 seconds (460.64 k allocations: 54.505 MiB, 4.65% gc time)
  0.026563 seconds (58.88 k allocations: 8.102 MiB)
 58.600608 seconds (637.56 k allocations: 5.279 GiB, 0.58% gc time)
14912/20291
g7-g33:
  0.102984 seconds (895.87 k allocations: 117.412 MiB, 8.72% gc time)
  0.018334 seconds (73.04 k allocations: 19.104 MiB)
887.864739 seconds (1.09 M allocations: 14.379 GiB, 0.04% gc time)
20931/20937
g8-g9:
  0.037838 seconds (156.49 k allocations: 19.754 MiB, 6.14% gc time)
  0.021842 seconds (33.77 k allocations: 4.363 MiB)
 10.019443 seconds (165.15 k allocations: 542.267 MiB, 0.20% gc time)
4318/5407
g10-g14:
  0.096011 seconds (313.64 k allocations: 39.333 MiB, 2.25% gc time)
  0.048104 seconds (66.76 k allocations: 12.383 MiB)
 75.430113 seconds (307.45 k allocations: 1.119 GiB, 0.27% gc time)
7771/9430
g10-g25:
  0.060173 seconds (385.80 k allocations: 46.176 MiB, 3.50% gc time)
  0.035077 seconds (96.54 k allocations: 11.414 MiB, 9.32% gc time)
 26.100259 seconds (238.26 k allocations: 855.204 MiB, 0.13% gc time)
5356/14535
g11-g13:
  0.074360 seconds (465.87 k allocations: 59.605 MiB, 9.29% gc time)
  0.027814 seconds (73.98 k allocations: 15.350 MiB)




veripb --trace --useColor test.opb test.pbp
restart RELP  alt j alt r
union ∪
intersect ∩
setdiff
symdiff rend les elements uniques
issubset ⊆⊇
i belive it matters




=#
