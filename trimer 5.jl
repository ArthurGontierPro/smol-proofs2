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
function copyeq(eq)
    return Eq([Lit(l.coef,l.sign,l.var) for l in eq.t], eq.b)
end
function solvepol(st,system,link)
    id = parse(Int,st[2])
    eq = copyeq(system[id])
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
function readred(st,varmap,redwitness,c)
    i = findfirst(x->x==";",st)
    eq = readeq(st[2:i],varmap)
    redwitness[c] = join(st[i+1:end]," ")
    return eq
end
function readveripb(path,file,system,varmap)
    systemlink = Vector{Int}[]
    redwitness = Dict{Int, String}()
    com = Dict{Int, String}()
    output = conclusion = ""
    c = length(system)
    open(string(path,'/',file,extention),"r"; lock = false) do f
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
                push!(systemlink,[-3,parse(Int,st[end])])
                eq = readeq(st[1:end-1],varmap,2:2:length(st)-4)
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
            elseif type == "*trim"
                com[length(system)+1] = ss[7:end]
            elseif !(ss[1:2] in ["# ","w ","ps","* ","f ","d ","de","co","en"])
                println("unknown: ",ss)
            end
            if length(eq.t)!=0 || eq.b!=0
                normcoefeq(eq)
                push!(system,eq)
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
    assi = zeros(Int8,length(varmap))
    cone = zeros(Bool,n)
    cone[end] = true
    front = zeros(Bool,n)
    firstcontradiction = findfirst(x->length(x.t)==0,system)
    cone[firstcontradiction] = true
    if systemlink[firstcontradiction-nbopb][1] == -2         # pol case
        fixfront(front,systemlink[firstcontradiction-nbopb])
    else
        updumb(system,assi,front)                     #front now contains the antecedants of the final claim
        append!(systemlink[firstcontradiction-nbopb],findall(front))
    end
    # println("  init : ",sum(front))#,findall(front))
    while true in front
        i = findlast(front)
        front[i] = false
        if !cone[i] 
            cone[i] = true
            if i>nbopb
                tlink = systemlink[i-nbopb][1]
                if tlink == -1 
                    antecedants .=false ; assi.=0
                    rupque(system,invsys,antecedants,i,assi,front,cone) # la rupque est moins efficace pour le trimmer mais elle fais de plus petites preuves
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
function fillprioque(invsys,l,init,cone,front,prioque,que)
    for id in invsys[l.var]
        if id<=init
            if cone[id] || front[id]
                pushfirst!(prioque,id)
            else
                pushfirst!(que,id)  
end end end end
function updateprioque(eq,prioque,que,invsys,cone,front,s,i,init,assi::Vector{Int8},antecedants)
    for l in eq.t
        if l.coef > s && assi[l.var]==0
            assi[l.var] = l.sign ? 1 : 2
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
function update(eq,s,i,assi,antecedants)
    changes = false
    for l in eq.t
        if assi[l.var]==0 && l.coef > s
            assi[l.var] = l.sign ? 1 : 2
            antecedants[i] = true
            changes = true
        end
    end
    return changes
end
function updumb(system,assi,antecedants) 
    changes = true
    while changes
        changes = false
        for i in eachindex(system)
            eq = system[i]
            s = slack(eq,assi)
            if s<0
                antecedants[i] = true
                return 
            else
                changes |= update(eq,s,i,assi,antecedants)
            end
        end
    end
    printstyled(" updumb Failed "; color = :red)
end
function rupque(system::Vector{Eq},invsys,antecedants::Vector{Bool},init,assi::Vector{Int8},front::Vector{Bool},cone::Vector{Bool})
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
        s = slack(eq,assi)
        if s<0
            antecedants[i] = true
            return 
        else
            updateprioque(eq,prioque,que,invsys,cone,front,s,i,init,assi,antecedants)
        end
    end
    printstyled(" rupQue empty "; color = :red)
end
function readinstance(path,file)
    system,varmap = readopb(path,file)
    nbopb = length(system)
    system,systemlink,redwitness,output,conclusion,com,version = readveripb(path,file,system,varmap)
    return system,systemlink,redwitness,nbopb,varmap,output,conclusion,com,version
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
function writeiaold(e,link,cone,varmap)
    return string("ia ",sum(cone[1:link])," : ",writeeq(e,varmap))
end
function writeia(e,link,index,varmap)
    return string("ia ",writeeq(e,varmap)[1:end-1]," ",index[link],"\n")
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
function writepol(link,index)
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
                s = string(s," ",index[t])
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
function writedel(f,systemlink,i,succ,index,nbopb,dels)
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
                write(f,string(index[p]," "))
            end
        end
    end
    if isdel
        write(f,string("\n"))
    end
end
function writeconedel(path,file,version,system,cone,systemlink,redwitness,nbopb,varmap,output,conclusion)
    index = zeros(Int,length(system))
    lastindex = 0
    open(string(path,"/smol.",file,".opb"),"w") do f
        for i in 1:nbopb
            if cone[i]
                lastindex += 1
                index[i] = lastindex
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
                lastindex += 1
                index[i] = lastindex
                eq = system[i]
                tlink = systemlink[i-nbopb][1]
                if tlink == -1               # rup
                    write(f,writeu(eq,varmap))
                    writedel(f,systemlink,i,succ,index,nbopb,dels)
                elseif tlink == -2           # pol
                    write(f,writepol(systemlink[i-nbopb],index))
                    writedel(f,systemlink,i,succ,index,nbopb,dels)

                    # write(f,writeia(eq,i,index,varmap))
                    # write(f,string("del id ",lastindex,"\n"))
                    # lastindex += 1
                    # index[i] = lastindex
                elseif tlink == -3           # ia
                    write(f,writeia(eq,systemlink[i-nbopb][2],index,varmap))
                    writedel(f,systemlink,i,succ,index,nbopb,dels)
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
        return  string(0)
    elseif b<0.1
        return  string(round(b; sigdigits=1))
    elseif b<1
        return  string(round(b; sigdigits=2))
    else
        return  string(round(b; sigdigits=3))
    end
end
function prettypourcent(b)
    b = b*100
    c = round(Int,b)
    return  string(c)
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
function roundt(t,d)
    for i in eachindex(t)
        t[i] = round(t[i],digits = d)
    end
    return t
end
function printcom(system,invsys,cone,com)
    names = [
        "backtrack", "backtrackbin", "backtrackbincolor", "disconnected",
        "degre", "hall", "nds", "nogood", "loops", "fail", "colorbound",
        "adjacencyhack", "adjacencydist1", "adjacencydist2", "adjacencydist3",
        "adjacency", "adjacency0", "adjacency1", "adjacency2", "adjacency3", "adjacency4"]
    n = length(names)
    og = zeros(Int,n)
    sm = zeros(Int,n)
    for i in eachindex(com)
        s = com[i]
        st = split(s,' ')
        type = string(st[1])
        removespaces(st)
        j = findfirst(isequal(type),names)
        if j === nothing
            push!(names,type)
            push!(og,1)
            push!(sm,0)
            if cone[i] sm[end]+=1 end
        else
            og[j]+=1
            if cone[i] sm[j]+=1 end
        end
    end
    p = sortperm(names)
    for i in p
        if og[i]>0
            col =  sm[i]==og[i] ? 3 : sm[i]==0 ? 1 : 2
            printstyled(names[i]," ",sm[i],"/",og[i],"\n"; color = col)
        end
    end
end
function runtrimmer(file)
    run_bio_solver(file) # rerun for the pbp file with coms
    tvp = @elapsed begin
        v1 = read(`veripb $path/$file.opb $path/$file$extention`)
    end
    tri = @elapsed begin
        system,systemlink,redwitness,nbopb,varmap,output,conclusion,com,version = readinstance(path,file)
    end
    invsys = getinvsys(system,varmap)
    normcoefsystem(system)
    tms = @elapsed begin
        cone = makesmol(system,invsys,varmap,systemlink,nbopb)
    end
    twc = @elapsed begin
        writeconedel(path,file,version,system,cone,systemlink,redwitness,nbopb,varmap,output,conclusion)
    end

    printcom(system,invsys,cone,com)

    writeshortrepartition(path,file,cone,nbopb)
    tvs = @elapsed begin
        v2 = read(`veripb $path/smol.$file.opb $path/smol.$file$extention`)
    end
    so = stat(string(path,"/",file,".opb")).size + stat(string(path,"/",file,extention)).size
    st = stat(string(path,"/smol.",file,".opb")).size + stat(string(path,"/smol.",file,extention)).size
    t = [roundt([parse(Float64,file[end-5:end-3]),parse(Float64,file[end-2:end]),so,st,st/so,tvp,tvs,tvs/tvp,tms,twc,tri],3)]
    printtabular(t)
    open(string(path,"/atable"), "a") do f
        write(f,string(t[1],",\n"))
    end
    if v1!=v2
        printstyled("catch (u cant see me)\n"; color = :red)
        open(string(path,"/afailedtrims"), "a") do f
            write(f,string(file," \n"))
        end
    end
end
function run_bio_sorted()
    extentionstat = ".veripb"
    cd()
    list = cd(readdir, proofs)
    list = [s[1:end-4] for s in list if s[end-3:end]==".opb" && s[1:3]=="bio"]
    stats = [stat(string(path,"/",file,".opb")).size + stat(string(proofs,"/",file,extention)).size for file in list]
    p = sortperm(stats)
    for i in eachindex(p)
        file = list[p[i]]
        tail = read(`tail -n 1 $proofs/$file$extentionstat`,String)
        if length(tail) > 24 && 
            tail[1:24] == "end pseudo-Boolean proof" &&
            read(`tail -n 2 $proofs/$file$extentionstat`,String)[1:14] != "conclusion SAT"
            if stats[p[i]] > 500_000
                runtrimmer(file)
            end
        end
    end
end
function run_timeout_bio_solver()
    path = string(benchs,"/biochemicalReactions")
    cd()
    graphs = cd(readdir, path)
    n = length(graphs)
    for target in graphs, pattern in graphs
        # target = graphs[rand(1:n)]
        # pattern = graphs[rand(1:n)]
        if pattern != target
            ins = string("bio",pattern[1:end-4],target[1:end-4])
            if !isfile(string(proofs,"/",ins,".opb")) || !isfile(string(proofs,"/",ins,extention)) ||
                (isfile(string(proofs,"/",ins,extention)) && 
                (length(read(`tail -n 1 $proofs/$ins$extention`,String))) < 24 || 
                read(`tail -n 1 $proofs/$ins$extention`,String)[1:24] != "end pseudo-Boolean proof")
                print(ins)
                p = run(pipeline(`timeout 3 ./$solver --prove $proofs/$ins --no-clique-detection --format lad $path/$pattern $path/$target`, devnull),wait=false); wait(p)
            end # no --proof-names anymore ?
        end
    end
end
function run_bio_solver(ins)
    path = string(benchs,"/biochemicalReactions")
    cd()
    pattern = string(ins[4:6],".txt")
    target = string(ins[7:9],".txt")
    # run(`rm $proofs/$ins$extention`)
    # ins = string("bio",pattern[1:end-4],target[1:end-4])
    # if !isfile(string(proofs,"/",ins,".opb")) || !isfile(string(proofs,"/",ins,extention)) ||
    #     (isfile(string(proofs,"/",ins,extention)) && 
    #     (length(read(`tail -n 1 $proofs/$ins$extention`,String))) < 24 || 
    #     read(`tail -n 1 $proofs/$ins$extention`,String)[1:24] != "end pseudo-Boolean proof")
        print(ins)
        @time run(pipeline(`./$solver --prove $proofs/$ins --no-clique-detection --format  lad $path/$pattern $path/$target`, devnull))
    # end # no --proof-names anymore ?
end
# const benchs = "veriPB/newSIPbenchmarks"
# const solver = "veriPB/subgraphsolver/glasgow-subgraph-solver/build/glasgow_subgraph_solver"
# const proofs = "veriPB/proofs"    
# const proofs = "veriPB/prooframdisk"    
const benchs = "newSIPbenchmarks"
const solver = "glasgow-subgraph-solver/build/glasgow_subgraph_solver"
const proofs = "/cluster/proofs"
const path = proofs
const extention = ".pbp"
const version = "2.0"

function main()
    run_bio_sorted()
end

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
        println(
        round(Int,i[1])," & ",
        round(Int,i[2])," & ",
        prettybytes(i[3])," & ",
        prettybytes(i[4])," & ",
        prettypourcent(i[5])," & ",
        prettytime(i[6])," & ",
        prettytime(i[7])," & ",
        prettypourcent(i[8])," & ",
        prettytime(i[9])," & ",
        prettytime(i[10])," & ",
        prettytime(i[11])," \\\\\\hline"
        )
    end
end

run_timeout_bio_solver()
# run_bio_sorted()

# ins = "aaaclique"
# cd()
# ins = "bio021002"
# runtrimmer(proofs,ins,extention)

# ins = "bio037002"
# ins = "bio019014"
# ins = "bio001004"

# run_bio_solver(ins)

# ins = "bio070014"
# runtrimmer(ins)


#=
    bio037002  
adjacency 1936/12800
degre 220/220
hall 40/3788
backtrack 763/1403
fails 626/2917
nds 80/80
nogoods 1/17

    bio021002 
adjacency 3504/31902
degre 528/580
hall 25/360
backtrack 81/208
fails 4/224
nds 172/172

    bio070014  
degre 19620/19620
hall 1/1


bio017015  0.144826 seconds (109 allocations: 6.234 KiB)
adjacency 9753/61952
degre 423/907
hall 0/0
backtrack 0/0
fails 0/0
nds 7/7
nogoods 0/0
other 0/0
17 & 15 & 11.57 MB & 1.423 MB & 12 & 6.52 & 1.18 & 18 & 1.18 & 0.21 & 3.09 \\\hline
bio196013  0.135254 seconds (109 allocations: 6.234 KiB)
adjacency 11075/64347
degre 396/833
hall 7/9
backtrack 0/0
fails 4/4
nds 113/113
nogoods 0/0
other 0/0
196 & 13 & 11.71 MB & 1.611 MB & 14 & 6.78 & 1.51 & 22 & 2.24 & 0.09 & 2.8 \\\hline

bio041013  0.149115 seconds (109 allocations: 6.234 KiB)
adjacency 10807/63120
degre 548/816
hall 4/21
backtrack 3/4
fails 13/14
nds 158/158
nogoods 0/0
other 0/0

bio089013  0.129651 seconds (109 allocations: 6.234 KiB)
adjacency 6760/39852
degre 698/819
hall 88/4814
backtrack 247/2367
fails 45/2928
nds 98/98
nogoods 0/13
other 0/0

89 & 13 & 12.74 MB & 1.222 MB & 10 & 5.79 & 1.27 & 22 & 32.5 & 0.21 & 5.29 \\\hline
bio192002  0.099399 seconds (109 allocations: 6.234 KiB)
adjacency 9040/74186
degre 504/962
hall 0/0
backtrack 0/0
fails 0/0
nds 51/51
nogoods 0/0
other 0/0
192 & 2 & 12.97 MB & 1.45 MB & 11 & 5.41 & 0.8 & 15 & 1.08 & 0.06 & 2.01 \\\hline
bio026013  0.109130 seconds (109 allocations: 6.234 KiB)
adjacency 13659/68403
degre 589/907
hall 3/5
backtrack 2/2
fails 2/4
nds 151/151
nogoods 0/0
other 0/0
26 & 13 & 12.88 MB & 2.139 MB & 17 & 5.19 & 1.19 & 23 & 2.16 & 0.08 & 2.57 \\\hline
bio017013  0.110825 seconds (109 allocations: 6.234 KiB)
adjacency 11552/70322
degre 488/784
hall 0/0
backtrack 0/0
fails 0/0
nds 74/74
nogoods 0/0
other 0/0
17 & 13 & 12.95 MB & 1.69 MB & 13 & 5.41 & 1.03 & 19 & 1.25 & 0.07 & 3.11 \\\hline
bio075015  0.112467 seconds (109 allocations: 6.234 KiB)
adjacency 12095/71307
degre 254/1002
hall 0/0
backtrack 0/0
fails 0/0
nds 14/14
nogoods 0/0
other 0/0
75 & 15 & 13.0 MB & 1.827 MB & 14 & 5.5 & 1.09 & 20 & 1.38 & 0.14 & 2.76 \\\hline

bio001122  0.108955 seconds (109 allocations: 6.234 KiB)
adjacency 14360/61336
degre 1204/1204
hall 1/1
backtrack 0/0
fails 0/0
nds 128/128
nogoods 0/0
other 0/0
1 & 122 & 12.93 MB & 2.832 MB & 22 & 4.55 & 1.05 & 23 & 2.12 & 0.11 & 2.82 \\\hline

bio073074  0.124405 seconds (109 allocations: 6.234 KiB)
adjacency 24255/67873
degre 1825/2602
hall 1/1
backtrack 0/0
fails 0/0
nds 481/481
nogoods 0/0
other 0/0
73 & 74 & 13.54 MB & 3.83 MB & 28 & 5.07 & 1.9 & 37 & 3.45 & 0.14 & 3.28 \\\hline

bio096061  0.131999 seconds (109 allocations: 6.234 KiB)
adjacency 11696/52892
degre 1587/1587
hall 2/8
backtrack 2/2
fails 2/4
nds 1066/1066
nogoods 0/0
other 0/0
96 & 61 & 13.35 MB & 2.539 MB & 19 & 3.97 & 1.06 & 27 & 2.84 & 0.09 & 4.14 \\\hline




=#

# sat = read(`tail -n 2 $path/$file$extention`,String)[1:14] == "conclusion SAT"


# main()

#=
export JULIA_NUM_THREADS=192
julia --check-bounds=no 'trimer 5.jl'

degre
nds
hall
fail
backtrack
adjacency0:n
adjacencyhack
backtrackbincolor
backtrackbin
colorbound
disconnected

rm atimes
rm abytes
rm afailedtrims
rm aworst
rm arepartition

hardest one bio 7 13 (310_916_484 lignes)
lon sur le serv bio 89 32 (421_805_749 lignes)

on peut retenir l'assignement optenable depuis le cone
on met dans le cone toutes les unit


=#

# readrepartition()

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

#=
function test()
    for i in 9500:length(t)
        print(prettytime(t[i][3]/10^6),"/",min(100,t[i][6]),",")
    end
    for i in 9500:length(t)
        print(prettytime(t[i][3]/10^6),"/",min(100,t[i][7]),",")
    end

    for i in 9500:length(t)
        print(prettytime(t[i][3]/10^6),"/",min(100,t[i][9]),",")
    end
    for i in 9500:length(t)
        print(prettytime(t[i][3]/10^6),"/",min(100,t[i][10]),",")
    end
    for i in 9500:length(t)
        print(prettytime(t[i][3]/10^6),"/",min(100,t[i][11]),",")
    end

    r =  9500:length(t)
    s = 0.0
    for i in r
        s+=t[i][8]
    end
    println(s/length(r))

    r =  9500:length(t)
    m = 0.0
    for i in r
        m=max(m,t[i][5])
    end
    println(m)

    r =  9500:length(t)
    m = 100.0
    for i in r
        m=min(m,t[i][5])
    end
    println(m)

    r =  9500:length(t)
    t5 = [t[i][5] for i in r]
    t8 = [t[i][8] for i in r]

    for i in r
        if t[i][8]>0.8
            printtabular([t[i]])
        end
    end

    for i in 9000:length(t)
        print(prettytime(t[i][3]/10^6),"/",prettypourcent(t[i][8]),",")
    end

    for i in 9000:length(t)
        print(prettytime(t[i][3]/10^6),"/",prettytime(t[i][4]/10^6),",")
    end

    for i in 9000:length(t)
        print(prettytime(t[i][3]/10^6),"/",prettytime(t[i][4]/10^6),",")
    end
end
=#