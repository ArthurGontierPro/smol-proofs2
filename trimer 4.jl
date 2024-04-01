
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
function solvepol(st,system,systemlink,c)
    id = parse(Int,st[2])
    eq = deepcopy(system[id])
    stack = [eq]
    systemlink[c] = [id]
    for j in 3:length(st)
        i=st[j]
        if i=="+"
            stack[end] = addeq(stack[end],pop!(stack))
            push!(systemlink[c],-1)
        elseif i=="*"
            stack[end] = multiply(stack[end],systemlink[c][end])
            push!(systemlink[c],-2)
        elseif i=="d"
            stack[end] = divide(stack[end],systemlink[c][end])
            push!(systemlink[c],-3)
        elseif i=="s"
            normcoefeq(stack[end])
            saturate(stack[end])
            push!(systemlink[c],-4)
        elseif i=="w"
            printstyled(" !weak"; color = :blue)
        elseif i!="0"
            id = parse(Int,i)
            push!(systemlink[c],id)
            if !(st[j+1] in ["*","d"])
                push!(stack,deepcopy(system[id]))    
            end
        end
    end
    eq = pop!(stack)
    lits = eq.t
    lits2 = removenulllits(lits)
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
            eq = Eq([],0)
            if ss[1:3] == "red"  
                eq = readred(st,varmap,redwitness,c)
                systemlink[c] = [-2]
            elseif ss[1:2] == "p " || ss[1:3] == "pol"
                eq = solvepol(st,system,systemlink,c)
            elseif ss[1:2] == "u " || ss[1:3] == "rup"
                eq = readeq(st,varmap,2:2:length(st)-3)
                if length(eq.t)==0 && eq.b>0
                    system[c] = eq
                    addinvsys(invsys,eq,c)
                    system = system[1:c]
                    output = split(s[end-2],' ')[2]
                    conclusion = split(s[end-1],' ')[2]
                    return system,invsys,systemlink,output,conclusion
                end
            elseif ss[1:2] == "ia"
                systemlink[c] = [parse(Int,st[2])]
                eq = readeq(st,varmap,4:2:length(st)-3)
            elseif ss[1:3] == "sol"                                  # on ajoute la negation au probleme pour chercher d'autres solutions. jusqua contradiction finale. dans la preuve c.est juste des contraintes pour casser toutes les soloutions trouvees
                eq = findfullassi(system,invsys,st,c,varmap)
                systemlink[c] = [-1]
            elseif st[1] == "output"
                output = st[2]
            elseif st[1] == "conclusion"
                conclusion = st[2]
            elseif !(ss[1:2] in ["# ","w ","ps","* ","f ","de","co","en"])
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
    if length(eq.t) > 0
        c-= eq.b
    end
    return c
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
    firstcontradiction = findfirst(x->length(x.t)==0,system)
    if firstcontradiction <= nbopb
        cone[firstcontradiction] = true
        return cone
    end
    updumb(system,invsys,front)                     #front now contains the antecedants of the final claim
    # upsmart(system,invsys,front)
    println(" init contradiction: ",sum(front),findall(front))
    while true in front
        i = findlast(front)
        front[i] = false
        if !cone[i] 
            cone[i] = true
            if i>nbopb
                reset([antecedants,isassi,assi])
                if isassigned(systemlink,i)
                    if systemlink[i][1]<0 #sol and red cases
                        # updumb(system,invsys,antecedants,i,isassi,assi) # we consider sol as axioms ?
                    else
                        for j in systemlink[i]
                            antecedants[j] = true
                        end
                    end
                else
                    rupdumb(system,invsys,antecedants,i,isassi,assi)
                    # rupsmart(system,invsys,antecedants,i,isassi,assi)
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
    printstyled(" updumb Failed "; color = :red)
end
function rupdumb(system,invsys,antecedants,init,isassi,assi)
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
function readinstance(path,file)
    words = ["p","u","red","sol","solx","soli",">=",";",":","+","s","ia"]
    system,invsys,varmap = readopb(path,file)
    nbopb = length(system)
    system,invsys,systemlink,redwitness,output,conclusion,version = readveripb(path,file,system,invsys,varmap,words)
    return system,invsys,systemlink,redwitness,nbopb,varmap,output,conclusion,version
end
function makesmol(system,invsys,systemlink,nbopb)
    # printsys(system)
    # normcoefsystem(system)
    # printsys(system)
    return smolproof4(system,invsys,systemlink,nbopb)
    # printsys(system,cone)
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
    return string("ia ",sum(cone[1:link])," ",writeeq(e,varmap))
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
    for i in eachindex(link)
        t = link[i]
        if t==-1
            s = string(s," +")
        elseif t==-2
            s = string(s," *")
        elseif t==-3
            s = string(s," d")
        elseif t==-4
            s = string(s," s")
        else
            if link[i+1] in [-2,-3]
                s = string(s," ",t)
            else
                s = string(s," ",sum(cone[1:t]))
            end
        end
    end
    return string(s,"\n")
end
function writecone(path,file,extention,version,system,cone,systemlink,redwitness,nbopb,varmap,output,conclusion)
    open(string(path,"/smol.",file,".opb"),"w") do f
        for i in 1:nbopb
            if cone[i]
                eq = system[i]
                write(f,writeeq(eq,varmap))
            end
        end
    end
    open(string(path,"/smol.",file,extention),"w") do f
        write(f,string("pseudo-Boolean proof version ",version,"\n"))
        write(f,string("f ",sum(cone[1:nbopb])," 0\n"))
        # write(f,string("f ",nbopb," 0\n")) # for full system
        for i in nbopb+1:length(system)
            if cone[i]
                eq = system[i]
                if isassigned(systemlink,i)
                    if systemlink[i][1] == -1           #solx
                        write(f,writesol(eq,varmap))
                    elseif systemlink[i][1] == -2       #red
                        write(f,writered(eq,varmap,redwitness[i]))
                    elseif length(systemlink[i])==1     #ia
                        write(f,writeia(eq,systemlink[i][1],cone,varmap))
                    else
                        write(f,writepol(systemlink[i],cone))
                    end
                else
                    write(f,writeu(eq,varmap))
                end
            end
        end
        write(f,string("output ",output,"\n"))
        if conclusion == "SAT"
            write(f,string("conclusion ",conclusion,"\n"))
        else
            write(f,string("conclusion ",conclusion," : ",sum(cone),"\n"))
            # write(f,string("conclusion ",conclusion," : ",length(system),"\n")) # for full system
        end
        write(f,"end pseudo-Boolean proof\n")
    end
end

function runtrimmer(path,file,extention)
    println("==========================")
    printstyled(file," : "; color = :yellow)
    # println("path = \"",path,"\"\nfile = \"",file,"\"\n")
    # path = "veriPB/proofs"
    # file = "si2_b03_m200.00"

    sat = read(`tail -n 2 $path/$file$extention`,String)[1:14] == "conclusion SAT"
    
    if !sat
        try
            @time run(`veripb $path/$file.opb $path/$file$extention`)
        catch
            printstyled("catch veriPB fail\n"; color = :red)
        end
        system,invsys,systemlink,redwitness,nbopb,varmap,output,conclusion,version = readinstance(path,file)
        println("\n size ",nbopb," ",length(system)-nbopb)
        cone = @time makesmol(system,invsys,systemlink,nbopb)
        writecone(path,file,extention,version,system,cone,systemlink,redwitness,nbopb,varmap,output,conclusion)
        nto = sum(cone[1:nbopb])
        ntp = sum(cone[nbopb+1:end])
        println(file,"\n        ",round(Int,100-100*nto/nbopb)," %    (",nto,"/",nbopb,")\n        ",round(Int,100-100*ntp/(length(system)-nbopb))," %    (",ntp,"/",(length(system)-nbopb),")")
        printstyled(file," (smol) : "; color = :yellow)
        try
            @time run(`veripb $path/smol.$file.opb $path/smol.$file$extention`)
        catch
            printstyled("catch (u cant see me)\n"; color = :red)
            if sum(cone)<30
                printcone(system,systemlink,cone)
            end
        end
    else
        println("SAT")
    end
    println("==========================\n")
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
        end
        runtrimmer(proofs,ins,extention)
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
    proofs = "proofs"    
    extention = ".veripb"

    # run_si(benchs,solver,proofs,extention)        # all si are sat ?
    # run_scalefree(benchs,solver,proofs,extention)
    # run_phase(benchs,solver,proofs,extention)
    run_meshes(benchs,solver,proofs,extention)
end
#  julia 'home/arthur_gla/veriPB/trim/smol-proofs2/trimer 4.jl'
# julia 'trimer 4.jl'
main()

# scp -r \\wsl.localhost\Ubuntu\home\arthur_gla\veriPB\trim\smol-proofs2\Instances\ arthur@fataepyc-01.dcs.gla.ac.uk:/users/grad/arthur/smol-proofs2
# scp -r /home/arthur_gla/veriPB/newSIPbenchmarks/ arthur@fataepyc-01.dcs.gla.ac.uk:/users/grad/arthur/
# find . -name "*Zone.Identifier" -type f -delete 
# find . -name ".*" -type f -delete 
# ssh arthur@fataepyc-01.dcs.gla.ac.uk