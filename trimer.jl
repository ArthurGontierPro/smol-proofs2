
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
function readeq(st)
    lits = Vector{Lit}(undef,(length(st)-3)÷2)
    for i in 1:2:length(st)-3
        coef = parse(Int,st[i])
        sign = st[i+1][1]=='x'
        tmp = split(split(st[i+1],'x')[end],'_')
        var = Var(parse(Int,tmp[1]),parse(Int,tmp[2]))
        lits[(i+1)÷2] = Lit(coef,sign,var)
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
        if i!=nothing
            tmplit,tmpc = addlit(lit,lits[i])
            lits[i] = tmplit
            c+=tmpc
        else
            push!(lits,lit)
        end
    end
    lits=removenulllits(lits)
    lits=sort(lits,lt=islexicolesslit)                          # optionnal sorting of literrals
    return Eq(lits,eq1.b+eq2.b-c)
end
function solvepol(st,system)
    eq1 = system[parse(Int,st[2])]
    for i in 3:2:length(st)-1
        eq1 = addeq(eq1,system[parse(Int,st[i])])
    end
    return eq1
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
            if ss[1:2] == "p "
                st = split(ss,' ')
                # systemlink[c] = [parse(Int,st[i]) for i in [2,3:2:length(st)-1]] 
                systemlink[c] = vcat([parse(Int,st[2])],[parse(Int,st[i]) for i in 3:2:length(st)-1]) 
                eq = solvepol(st,system)
                system[c] = eq
                addinvsyseq(invsys,eq,c)
                c+=1
            elseif ss[1:2] == "u "
                st = split(ss,' ')
                start = 2
                if ss[3] == ' '     # weard case of file with multiple spaces
                    start = 3
                end
                eq = readeq(st[start:end])
                system[c] = eq
                addinvsyseq(invsys,eq,c)
                c+=1
            elseif ss[1:2] == "j "
                st = split(ss,' ')
                systemlink[c] = [parse(Int,st[2])]
                eq = readeq(st[3:end])
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
    lits = copy(eq.t)
    for l in lits
        l.sign = !l.sign
        c+=l.coef
    end
    return Eq(lits,-eq.b+1+c)
end

function unitpropag(system,invsys,init,isassi,assi)
    front = Set(Int[])
    antecedants = Set(Int[])
    id=0
    c=0
    while length(front)>0 || id==0 
        c+=1
        if length(front)==0
            eq = init
        else
            id = pop!(front)
            eq = system[id]
        end
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


    println("==========================")
    # path = "\\\\wsl.localhost\\Ubuntu\\home\\arthur_gla\\veriPB\\trim\\"
    path = "\\\\wsl.localhost\\Ubuntu\\home\\arthur_gla\\veriPB\\trim\\smol-proofs\\sip_proofs\\"
    file = "g2-g3"
    # file = "g24-g28"
    system,invsys = @time readopb(path,file)
    system,invsys,systemlink = @time readveripb(path,file,system,invsys)

    vars = collect(keys(invsys))
    maxx = maximum(x->x.x,vars)
    maxv = maximum(x->x.v,vars)
    isassi = zeros(Bool,maxx+1,maxv+1)
    assi = zeros(Bool,maxx+1,maxv+1)

    normcoefsystem(system)
    init = reverse(system[end-1])
    antecedants = unitpropag(system,invsys,init,isassi,assi)

    printeq(init)
    for id in antecedants
        eq = id==0 ? init : system[id]
        print("slack: ",slack(eq,isassi,assi))
        printeq(eq)
    end



#= 
veripb --trace --useColor test.opb test.pbp
restart RELP  alt j alt r
union ∪
intersect ∩
setdiff
symdiff rend les elements uniques
issubset ⊆⊇
i belive it matters
=#
