
function smolproof(system,invsys,systemlink)
    isassi,assi = initassignement(invsys)
    antecedants = Set(Int[])
    cone = Set(Int[])
    front = Set(Int[length(system)-1])
    while length(front)>0
        id = pop!(front)
        if isassigned(systemlink,id)
            antecedants = systemlink[id]
        else
            isassi .= false
            assi .= false
            antecedants = unitpropag(system,invsys,id,isassi,assi)
            # antecedants = findall(unitpropag2(system,invsys,id,isassi,assi))
        end
        for i in antecedants
            if !(i in cone)
                push!(cone,i)
                push!(front,i)
            end
        end
    end
    return cone
end


function unitpropag2(system,invsys,init,isassi,assi) 
    n = length(system)
    front = zeros(Bool,n)
    front[init] = true
    antecedants = zeros(Bool,n)
    id = init
    eq = system[init]
    s = 0
    while true in front
        id = findfirst(front)
        front[id] = false
        eq = id==init ? reverse(system[id]) : system[id]
        s = slack(eq,isassi,assi)
        if s<0
            antecedants[id]=true
            return antecedants
        else
            for l in eq.t
                if !isassi[l.var.x+1,l.var.v+1] && l.coef > s
                    isassi[l.var.x+1,l.var.v+1] = true
                    assi[l.var.x+1,l.var.v+1] = l.sign
                    antecedants[id] = true
                    for j in invsys[l.var]
                        if j!=id
                            front[j] = true
                        end
                    end
                end
            end
        end
    end
    return antecedants
end
function makesmol(system,invsys,systemlink)
    normcoefsystem(system)
    # printsys(system)
    cone = @time smolproof2(system,invsys,systemlink)
    println(sum(cone),"/",length(system))
    # printsys(system,cone)
    
    cone = @time smolproof(system,invsys,systemlink)
    println(length(cone),"/",length(system))
    # printsys(system,cone)

end