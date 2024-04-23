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
function makesmol(system,invsys,systemlink,nbopb)
    n = length(system)
    antecedants = zeros(Bool,n)
    isassi,assi = initassignement(invsys)

    cone = zeros(Bool,n)
    cone[end] = true
    front = zeros(Bool,n)
    firstcontradiction = findfirst(x->length(x.t)==0,system)
    cone[firstcontradiction] = true
    if isassigned(systemlink,firstcontradiction) && length(systemlink[firstcontradiction])>1
        for i in systemlink[firstcontradiction]
            if i>0
                front[i] = true
            end
        end
    else
        updumb(system,invsys,front)                     #front now contains the antecedants of the final claim
    end

    # upsmart(system,invsys,front)
    print("  init : ",sum(front))#,findall(front))
    while true in front
        i = findlast(front)
        front[i] = false
        if !cone[i] 
            cone[i] = true
            if i>nbopb
                tlink = systemlink[i][1]
                if tlink == -1 
                    antecedants .=false
                    isassi .=false
                    assi.=false
                    rupdumb(system,invsys,antecedants,i,isassi,assi)
                    append!(systemlink[i],findall(antecedants))
                    front = front .|| antecedants
                elseif tlink >= -3
                    antecedants .=false
                    for j in eachindex(systemlink[i])
                        t = systemlink[i][j]
                        if t>0 && !(j<length(systemlink[i]) && (systemlink[i][j+1] == -2 || systemlink[i][j+1] == -3))
                            antecedants[t] = true
                        end
                    end
                    front = front .|| antecedants
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
                tlink = systemlink[i][1]
                if tlink == -1               # rup
                    write(f,writeu(eq,varmap))
                elseif tlink == -2           # red
                    write(f,writepol(systemlink[i],cone))
                elseif tlink == -3           # ia
                    write(f,writeia(eq,systemlink[i][2],cone,varmap))
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
            write(f,string("conclusion ",conclusion," : ",sum(cone),"\n"))
            # write(f,string("conclusion ",conclusion," : ",length(system),"\n")) # for full system
        end
        write(f,"end pseudo-Boolean proof\n")
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
    # println("==========================")
    printstyled(file,"        : "; color = :yellow)
    # println("path = \"",path,"\"\nfile = \"",file,"\"\n")
    # path = "veriPB/proofs"
    # file = "si2_b03_m200.00"

    sat = read(`tail -n 2 $path/$file$extention`,String)[1:14] == "conclusion SAT"
    
    if !sat
        t1=t2=t3 = 0.0
        try
            t1 = @elapsed run(`veripb $path/$file.opb $path/$file$extention`)
        catch
            printstyled("catch veriPB fail\n"; color = :red)
        end
        system,invsys,systemlink,redwitness,nbopb,varmap,output,conclusion,version = readinstance(path,file)
        print("   size : ",nbopb,"|",length(system)-nbopb)
        normcoefsystem(system)
        t2 = @elapsed begin
            cone = makesmol(system,invsys,systemlink,nbopb)
        end
        writecone(path,file,extention,version,system,cone,systemlink,redwitness,nbopb,varmap,output,conclusion)
        nto = sum(cone[1:nbopb])
        ntp = sum(cone[nbopb+1:end])
        println("   opb : ",nto,"/",nbopb," (",round(Int,100*nto/nbopb),"%)",
                "   pbp : ",ntp,"/",(length(system)-nbopb)," (",round(Int,100*ntp/(length(system)-nbopb)),"%)",
                "   time : ",round(t2; digits=3)," s")
        printstyled(file," (smol) : "; color = :yellow)
        try
            t3 = @elapsed run(`veripb $path/smol.$file.opb $path/smol.$file$extention`)
            so = stat(string(path,"/",file,".opb")).size + stat(string(path,"/",file,extention)).size
            st = stat(string(path,"/smol.",file,".opb")).size + stat(string(path,"/smol.",file,extention)).size
            println("   trim : ",prettybytes(so),"  ->  ",prettybytes(st),
                    "       ",round(t1; sigdigits=4)," s  ->  ",round(t3; sigdigits=4)," s")
            open(string(path,"/times"), "a") do f
                write(f,string(file,"/",t1,"/",t2,","))
            end
            open(string(path,"/bytes"), "a") do f
                write(f,string(file,"/",so/10^6,"/",st/10^6,","))
            end
        catch
            printstyled("catch (u cant see me)\n"; color = :red)
            if sum(cone)<30
                printcone(system,systemlink,cone)
            end
        end
    else
        println("SAT")
    end
    # println("==========================")
end
function run_bio(benchs,solver,proofs,extention)
    path = string(benchs,"/biochemicalReactions")
    cd()
    graphs = cd(readdir, path)
    # for i in eachindex(graphs)
    #     for j in eachindex(graphs)
    #         if i!=j
    #             target = graphs[i]
    #             pattern = graphs[j]
                target = "002.txt"
                pattern = "171.txt"
                ins = string("bio",pattern[1:end-4],target[1:end-4])
                if !isfile(string(proofs,"/",ins,".opb")) || 
                    (isfile(string(proofs,"/",ins,extention)) && 
                    (length(read(`tail -n 1 $proofs/$ins$extention`,String))) < 24 || 
                    read(`tail -n 1 $proofs/$ins$extention`,String)[1:24] != "end pseudo-Boolean proof")
                    @time run(`./$solver --prove $proofs/$ins --no-clique-detection --proof-names --format lad $path/$pattern $path/$target`)
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
    benchs = "veriPB/newSIPbenchmarks"
    solver = "veriPB/subgraphsolver/glasgow-subgraph-solver/build/glasgow_subgraph_solver"
    proofs = "veriPB/proofs"    
    # benchs = "newSIPbenchmarks"
    # solver = "glasgow-subgraph-solver/build/glasgow_subgraph_solver"
    # proofs = "/cluster/proofs"
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

# julia 'trimer 4.jl'
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
bio171002        : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   size : 3971|62092  init : 655   opb : 3778/3971 (95%)   pbp : 13543/62092 (22%)   time : 59.023 s
bio171002 (smol) : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
   trim : 5.852 MB  ->  880.8 KB       2.324 s  ->  11.08 s
=#

