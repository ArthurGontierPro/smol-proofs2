# This is a PB trimmer made to analyse proofs. If problem, ask arthur.pro.gontier@gmail.com
# julia GlasgowTrimnalyser.jl [options] [instance name or directory of instances]   options: atable sort rand clean veri profile load
const opb = ".opb"
const pbp = ".pbp"
const smol = ".smol"
const version = "3.0"
const abspath = "/home/arthur_gla/veriPB/subgraphsolver/"
const inst = findfirst(x -> isfile(x*pbp) && isfile(x*opb), ARGS)  # search for proof 
const proofs = (i = findfirst(x -> isdir(x), ARGS)) === nothing ? abspath*"proofs/" : ARGS[i]
using Random,DataStructures
# module Maine
    function main()
        if "atable" in ARGS
            plotresultstable(); return 
        elseif "clean" in ARGS
            rm.(filter(f -> endswith(f, ".out") || endswith(f, ".err"),readdir(proofs; join=true))); return
        elseif inst !== nothing 
            printabline(ins)
            trimnalyse(inst); return
        end
        println(tabhead)
        for ins in getinstancesfromdir(proofs)
            printabline(ins)
            t1,t2,t3 = trimnalyse(ins)
            t4,t5 = "verif" in ARGS ? verify(ins) : (-1,-1)
            printabline2(ins,t1,t2,t3,t4,t5)
        end
        println(tabfoot) end

    function getinstancesfromdir(proofs)
        list = onlyname.(filter(x -> ext(x)==opb && isfile(noext(x)*pbp), readdir(proofs, join=true)))
        if "rand" in ARGS
            shuffle!(list)
        elseif "sort" in ARGS
            sort!(list, by = x -> inssize(x))
        end
        println("%Found ", length(list), " instances in ", proofs)
        return list end

    function trimnalyse(ins)
        t1 = t2 = t3 = 0 ; file = ins
        if "load" in ARGS file,system,systemlink,redwitness,solirecord,assertrecord,nbopb,varmap,ctrmap,output,conclusion,obj,invsys,prism,cone,conelits,invctrmap,succ,index = loadsys(file); @goto skiped end # using goto because I was told not to
        t1 = @elapsed begin 
            system,systemlink,redwitness,solirecord,assertrecord,nbopb,varmap,ctrmap,output,conclusion,obj,invsysprism = readinstance(proofs,file) 
        end
        t2 = @elapsed begin # cone mark usfull ctrs and lits
            cone,conelits = getcone(system,invsys,varmap,systemlink,nbopb,prism,redwitness,conclusion,obj)
        end


        @label skiped
        return trunc(Int,t1),trunc(Int,t2),trunc(Int,t3) end

    function verify(ins)
        t4 = t5 = 0
        veripb = "/home/arthur_gla/veriPB/trim/VeriPB/target/release/veripb"
        ins2 = proofs*ins
        ins3 = ins2*".smolverif"
        ins4 = ins2*".verif"
        ins31 = ins3*".out"
        ins32 = ins3*".err"
        ins41 = ins4*".out"
        ins42 = ins4*".err"
        redirect_stdio(stderr=devnull) do
            tryrm(ins31); tryrm(ins32)
            t4 = @elapsed try run(pipeline(`$veripb $ins2$opb$smol $ins2$pbp$smol`,stdout=ins31)) catch e write(ins32,string(e)) end
            tryrm(ins41); tryrm(ins42)
            t5 = @elapsed try run(pipeline(`$veripb $ins2$opb $ins2$pbp`,stdout=ins41)) catch e write(ins42,string(e)) end
        end
        return trunc(Int,t4),trunc(Int,t5) end
# end; using .Maine

# module ploting # ======================================= plotting  ======================================= #
    function plotresultstable()
        list = onlyname.(filter(x -> ext(x)==".out", readdir(proofs)))
        table = Vector{Vector{Any}}()
        for file in list
            res = Any[file,nothing,nothing,nothing,nothing,nothing,nothing,nothing,nothing,nothing,nothing,nothing,nothing,nothing,nothing]
            for line in eachline(file)
                    if occursin("grim TIME ", line)         res[2] = tryparse(Int, split(line)[end])
                elseif occursin("grim OPB SIZE ", line)     res[3] = tryparse(Int, split(line)[end])
                elseif occursin("grim PBP SIZE ", line)     res[4] = tryparse(Int, split(line)[end])
                elseif occursin("grim SIZE ", line)         res[5] = tryparse(Int, split(line)[end])
                elseif occursin("veri smol TIME ", line)    res[6] = tryparse(Int, split(line)[end])
                elseif occursin("veri TIME ", line)         res[7] = tryparse(Int, split(line)[end])
                elseif occursin("veri OPB SIZE ", line)     res[8] = tryparse(Int, split(line)[end])
                elseif occursin("veri PBP SIZE ", line)     res[9] = tryparse(Int, split(line)[end])
                elseif occursin("veri SIZE ", line)         res[10]= tryparse(Int, split(line)[end])
                elseif occursin("brim TIME ", line)         res[11]= tryparse(Int, split(line)[end])
                elseif occursin("brim OPB SIZE ", line)     res[12]= tryparse(Int, split(line)[end])
                elseif occursin("brim PBP SIZE ", line)     res[13]= tryparse(Int, split(line)[end])
                elseif occursin("brim SIZE ", line)         res[14]= tryparse(Int, split(line)[end])
                end
            end
            push!(table,res)
        end
        # println(table)
        printpoints2Dlog(table,5,10,"grim SIZE","veri SIZE") end

    function maxvalue(table,a)
        m = 0
        for t in table
            if t[a]!==nothing
                if t[a]>m m=t[a] end
            end
        end
        return m end

    function printpoints2D(table,a,b,xlbl="",ylbl="")
        prefixtikz(maxvalue(table,a),maxvalue(table,b),xlbl,ylbl)
        for t in table
            if t[a]!==nothing &&t[b]!==nothing
                print(t[a],'/',t[b],',')
            end
        end
        println()
        postfixtikz() end

    function printpoints2Dlog(table,a,b,xlbl="",ylbl="")
        xlbl*=" (log)"; ylbl*=" (log)"
        prefixtikz(logsmooth(maxvalue(table,a)),logsmooth(maxvalue(table,b)),xlbl,ylbl)
        for t in table
            if t[a]!==nothing &&t[b]!==nothing
                print(logsmooth(t[a]),'/',logsmooth(t[b]),',')
            end
        end
        println()
        postfixtikz() end

    function logsmooth(a) round(max(log10(a),0),sigdigits = 3) end
    function prefixtikz(mx=10,my=10,xlbl="",ylbl="")
        m = max(mx,my)
        steps = Int(m÷10 + 1)
        m = Int((m÷10)*10 + 10) # to make a 10 integer scale
        mx = my = m
        xsteps = steps
        ysteps = steps
        scale = 1#/max(xsteps,ysteps)
        xx = 1/xsteps
        yy = 1/ysteps    # mx = Int(ceil(mx))
        println("\\begin{tikzpicture}[scale=$scale, x=$xx cm, y=$yy cm] \n\\def\\xmin{0} \\def\\xmax{$mx} \\def\\ymin{0} \\def\\ymax{$my} \n\\draw[style=help lines, ystep=$ysteps, xstep=$xsteps] (\\xmin,\\ymin) grid (\\xmax,\\ymax); \n\\draw[->] (\\xmin,\\ymin) -- (\\xmax,\\ymin) node[above left] {$xlbl}; \n\\draw[->] (\\xmin,\\ymin) -- (\\xmin,\\ymax) node[below right] {$ylbl}; \n\\foreach \\x in {0,$xsteps,...,\\xmax} \\node at (\\x, \\ymin) [below] {\\x}; \n\\foreach \\y in {0,$ysteps,...,\\xmax} \\node at (\\xmin,\\y) [left] {\\y}; \n\\foreach \\x/\\y in{") end

    function postfixtikz()
        println("}\\draw (\\x,\\y) node[noeudver] {};\n\\end{tikzpicture}") end

# end; using .ploting
# module Sugarbox # ======================================= sugar ======================================= #
    onlyname(x) = splitext(basename(x))[1]
    ext(x) = splitext(basename(x))[2]
    noext(x) = splitext(x)[1]
    filesize(file) = stat(file).size
    inssize(file) = filesize(proofs*file*opb) + filesize(proofs*file*pbp)
    tryrm(s) = if isfile(s) rm(s) end
    remove(s,c) = replace(s,c=>"")#deleteat!(s,findall(x->x==c,s))
    const tabhead = "\\begin{tabular}{|cc|cc|c|c|c|}\\hline sizes & & &  & times (s) & & Instance\\\\\\hline\nopb & pbp & smol o & smol p & grim time (parse trim write verif) & veri time & \\\\\\hline"
    const tabfoot = "\\end{tabular}\\\\\n"
    printgray(s)  = printstyled(s, color=:light_black)
    printyellow(s)= printstyled(s, color=:yellow)
    printred(s)   = printstyled(s, color=:red)
    printgreen(s) = printstyled(s, color=:green)
    printblue(s)  = printstyled(s, color=:blue)
    printcyan(s)  = printstyled(s, color=:cyan)
    function leftcarriage(c,s)
        carriage = string(c-length(s))
        return "\r\033["*carriage*"G"*s end

    function printabline(f)
        printgray("         &          &          &          &      (                   ) &      & ")
        printyellow(f)
        printgray(" \\\\\\hline")
        printcyan(leftcarriage(9,prettybytes(filesize(proofs*f*opb))))
        printcyan(leftcarriage(20,prettybytes(filesize(proofs*f*pbp)))) end

    function printabline2(f,t1,t2,t3,t4,t5)
        printgreen(leftcarriage(31,prettybytes(filesize(proofs*f*opb*smol))))
        printgreen(leftcarriage(42,prettybytes(filesize(proofs*f*pbp*smol))))
        printgreen(leftcarriage(49,string(t1+t2+t3+max(0,t4))))
        printblue(leftcarriage(54,string(t1)))
        printgreen(leftcarriage(59,string(t2)))
        printblue(leftcarriage(64,string(t3)))
        printcyan(leftcarriage(69,string(t4)))
        printcyan(leftcarriage(78,string(t5)))
        println() end

    function prettybytes(b)
        if b>=10^9
            return string(trunc(Int,b/(10^9))," GB")
        elseif b>=10^6
            return string(trunc(Int,b/(10^6))," MB")
        elseif b>=10^3
            return string(trunc(Int,b/(10^3))," KB")
        else
            return  string(trunc(Int,b)," B")
        end end 

# end; using .Sugarbox 
# module Dumping # ======================================= mem dump ======================================= #
    using Serialization
    function dumpsys(file,system,systemlink,redwitness,solirecord,assertrecord,nbopb,varmap,ctrmap,output,conclusion,obj,invsys,prism,cone,conelits,invctrmap,succ,index)
        println("dumping started")
        sys = [file,system,systemlink,redwitness,solirecord,assertrecord,nbopb,varmap,ctrmap,output,conclusion,obj,invsys,prism,cone,conelits,invctrmap,succ,index]
        open("dump.jls","w") do f
            serialize(f,sys)
        end
        println("dumping ended") end

    function loadsys(file) 
        println("loading started")
        file,system,systemlink,redwitness,solirecord,assertrecord,nbopb,varmap,ctrmap,output,conclusion,obj,invsys,prism,cone,conelits,invctrmap,succ,index = deserialize("dump.jls")
        println("loading ended")
        return file,system,systemlink,redwitness,solirecord,assertrecord,nbopb,varmap,ctrmap,output,conclusion,obj,invsys,prism,cone,conelits,invctrmap,succ,index end
# end; # using .Dumping # to save the import un comment this.
# module Parser # ======================================= parser  ======================================= #
    function readinstance(path,file)
        system,varmap,ctrmap,obj = readopb(path,file)
        nbopb = length(system)
        system,systemlink,redwitness,solirecord,assertrecord,output,conclusion = readproof(path,file,system,varmap,ctrmap,obj)
        normcoefeq.(system)
        invsys = getinvsys(system,systemlink,varmap)
        prism = availableranges(redwitness)
        return system,systemlink,redwitness,solirecord,assertrecord,nbopb,varmap,ctrmap,output,conclusion,obj,invsys,prism end

    function readopb(path,file)
        system = Eq[]
        varmap = Dict{String,Int}()
        ctrmap = Dict{String, Int}()
        obj = ""
        open(path*file*opb,"r"; lock = false) do f
            c = 1
            for ss in eachline(f)
                if length(ss)==0 || ss[1]=='*' continue end     # do not parse comments
                ss = remove(ss,";") # I fully rely on lines beeing complete TODO change that eventualy
                st = split(ss,keepempty=false)              # structure of a line is: int var int var ... >= int ;                 
                if st[1][1]=='@'
                    ctrmap[st[1][2:end]] = c
                    st = st[2:end] # remove the @label
                end
                if ss[1] == 'm'                     # objective function (only minimization is supported)
                    obj = readobj(st,varmap)
                else
                    eq = readeq(st,varmap)
                    if length(eq.t)==0 && eq.b==1
                        printstyled(" !opb"; color = :blue)
                    end
                    normcoefeq(eq)
                    push!(system, eq)
                    c+=1
                end
            end
        end
        return system,varmap,ctrmap,obj end

    mutable struct Lit
        coef::Int
        sign::Bool
        var::Int end

    mutable struct Eq
        t::Vector{Lit}
        b::Int end

    readobj(st,varmap) = readlits(st,varmap,2:2:length(st))
    function readlits(st,varmap,range)
        lits = Vector{Lit}(undef,(length(range)))
        for i in range
            coef = parse(Int,st[i])
            sign = st[i+1][1]!='~'
            var = readvar(st[i+1],varmap)
            lits[(i - range.start)÷range.step+1] = Lit(coef,sign,var)
        end
        sort!(lits,by=x->x.var)
        return lits end

    function readvar(s,varmap)
        if s[1]==';' throw("; added as variable") end
        tmp = s[1]=='~' ? s[2:end] : s
        if haskey(varmap,tmp)
            return varmap[tmp]
        end
        varmap[tmp] = length(varmap)+1
        return length(varmap) end

    readeq(st,varmap) = readeq(st,varmap,1:2:length(st))
    function readeq(st,varmap,r)
        lits = readlits(st,varmap,r.start:r.step:(r.stop-2)) # because range should cover: coef lit coef lit >= b
        lits,c = merge(lits)
        eq = Eq(lits,parse(Int,st[r.start+2length(r)-1])-c)     # insupportable theoreme de la fourchette avec ces ranges
        return eq end

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
            deleteat!(lits,del)
        end
        return lits,c end

    function add(lit1,lit2)
        lit1,c1 = normlit(lit1)
        lit2,c2 = normlit(lit2)
        return Lit(lit1.coef+lit2.coef,true,lit1.var),c1+c2 end

    normlit(l) = !l.sign ? (Lit(-l.coef,true,l.var),l.coef) : (l,0)
    function normcoefeq(eq)
        c=0
        for l in eq.t
            c+= normcoef(l)
        end
        eq.b = c+eq.b end

    function normcoef(l)
        if l.coef<0
            l.coef = -l.coef
            l.sign = !l.sign
            return l.coef
        end
        return 0 end
 
    function readproof(path,file,system,varmap,ctrmap,obj)
        systemlink = Vector{Vector{Int}}()
        redwitness = Dict{Int, Red}()
        solirecord = Dict{Int, Vector{Lit}}()
        assertrecord = Dict{Int, String}()
        prism = Vector{UnitRange{Int64}}() # the subproofs should not be available to all
        output = conclusion = ""
        c = length(system)+1
        nbopb = length(system)
        open(path*file*pbp,"r"; lock = false) do f
            for ss in eachline(f)
                if length(ss)==0 continue end
                ss = remove(ss,";") # I fully rely on lines beeing complete TODO change that eventualy
                i = findfirst(x->x=='%',ss)
                if i !== nothing # there is a comment
                    if i<3 continue end # comment is at the start of the line, ignore the line
                    if ss[1]=='a' # justifyable assertion needs hints that are in comments for the moment.
                        assertrecord[c] = ss[i+1:end]
                    end
                    ss = ss[1:i-1] # remove the comment
                end
                st = split(ss,keepempty=false)
                if st[1][1]=='@'
                    ctrmap[st[1][2:end]] = c # keep track of constraint name
                    st = st[2:end] # remove the @label
                end
                type = st[1]
                eq = Eq([],0)
                    if type == "rup" || type == "u" eq = processrup(st,varmap,systemlink)
                elseif type == "pol" || type == "p" eq = processpol(st,varmap,system,systemlink,c,ctrmap,nbopb)
                elseif type == "a"                  eq = processassumption(st,varmap,systemlink,assertrecord,c)
                elseif type == "ia"                 eq = processia(st,varmap,ctrmap,c,systemlink)
                elseif type == "red"                c,eq = processred(system,systemlink,st,varmap,ctrmap,redwitness,c,f,prism)
                elseif type == "sol"                throw("trimmed SAT is the solution")
                elseif type == "soli"               eq = processsoli(st,varmap,system,systemlink,c,prism,obj,solirecord)
                elseif type == "solx"               eq = processsolx(st,varmap,system,systemlink,c,prism)
                elseif type == "output"             output = remove(st[2],";")
                elseif type == "conclusion"
                    conclusion = remove(st[2],";")
                    if conclusion == "BOUNDS"
                        conclusion = ss
                    elseif !isequal(system[end],Eq([],1)) && (conclusion == "SAT" || conclusion == "NONE")
                        throw("SAT Not supported..")
                    end
                elseif !(type in ["%","*","wiplvl","w","setlvl","#","f","d","del","end","pseudo-Boolean"])#,"de","co","en","ps"])
                    printstyled("unknown line head (skiped): ",ss; color=:red)
                end
                if length(eq.t)!=0 || eq.b!=0 # the eq is not empty
                    normcoefeq(eq)
                    push!(system,eq)
                    c+=1
                end
            end
        end
        return system,systemlink,redwitness,solirecord,assertrecord,output,conclusion end

    mutable struct Red                      # w: witness. range: id range from beign to end of red. pgranges are the proof goals ranges.
        w::Vector{Lit}                      # each odd index is the variable and each next even is tha target (lit(0,0,-1) means constant 1 and 0 means constant 0)
        range::UnitRange{Int64}
        pgranges::Vector{UnitRange{Int64}} end

    function processrup(st,varmap,systemlink)
        push!(systemlink,[-1])
        return readeq(st,varmap,2:2:length(st)) end

    function processpol(st,varmap,system,systemlink,c,ctrmap,nbopb)
        push!(systemlink,[-2])
        eq = solvepol(st,system,systemlink[end],c,varmap,ctrmap,nbopb)
        if !(length(eq.t)!=0 || eq.b!=0) throw("POL empty") end
        return eq end 

    function solvepol(st,system,link,init,varmap,ctrmap,nbopb)
        i = st[2]
        id = i[1]=='@' ? ctrmap[i[2:end]] : parse(Int,i)
        if id<0
            id = init+id
        end
        eq = copyeq(system[id])
        stack = Vector{Eq}()
        weakvar = ""
        push!(stack,eq)
        push!(link,id)
        lastsaturate = false
        for j in 3:length(st) 
            i=st[j]
            if i == ";" #we dont take the last ';'
                continue
            elseif i=="+"
                push!(stack,addeq(pop!(stack),pop!(stack)))     
                push!(link,-1)
            elseif i=="*"
                push!(stack,multiply(pop!(stack),link[end]))
                push!(link,-2)
            elseif i=="d"
                push!(stack,divide(pop!(stack),link[end]))
                push!(link,-3)
            elseif i=="s"
                if j == length(st)
                    lastsaturate = true
                else
                    normcoefeq(first(stack))
                    saturate(first(stack))
                end
                push!(link,-4)
            elseif i=="w"
                push!(stack,weaken(pop!(stack),weakvar))
                push!(link,-5)
            elseif !isdigit(i[1]) && i[1]!='@' && i[1]!='-' #if it is a variable do litteral axiom
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
                id = i[1]=='@' ? ctrmap[i[2:end]] : parse(Int,i)
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
            link[1] = -3 # transform pol to ia 
        end
        res = Eq(lits2,eq.b)
        if lastsaturate
            normcoefeq(res)
            saturate(res)
        end
        return res end

    copyeq(eq) = Eq([Lit(l.coef,l.sign,l.var) for l in eq.t], eq.b)
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
        sort!(lits,by=x->x.var)
        return Eq(lits,eq1.b+eq2.b-c) end

    removenulllits(lits) = filter!(x->x.coef!=0,lits)
    function multiply(eq,d)
        lits = copy(eq.t)
        for l in lits
            l.coef = l.coef*d
        end
        return Eq(lits,eq.b*d) end

    function divide(eq,d)
        normcoefeq(eq)
        lits = copy(eq.t)
        for l in lits
            l.coef = ceil(Int,l.coef/d)
        end
        return Eq(lits,ceil(Int,eq.b/d)) end

    function saturate(eq)
        for l in eq.t
            l.coef = min(l.coef,eq.b)
        end end

    function weaken(eq,var)                                           
        lits = copy(eq.t) # coef should be > 0
        b = eq.b
        for l in lits
            if l.var==var
                b-=l.coef
                l.coef = 0
            end
        end
        lits = removenulllits(lits) 
        return Eq(lits,b) end

    function processassumption(st,varmap,systemlink,assertrecord,c)
        eq = readeq(st,varmap,2:2:length(st))
        if haskey(assertrecord,c)
            hints = split(assertrecord[c],keepempty=false)[2:end]
            link = [-30]
            for i in eachindex(hints)
                push!(link,parse(Int,hints[i]))
            end
            push!(systemlink,link)
        else
            push!(systemlink,[-30])
        end
        return eq end

    function processia(st,varmap,ctrmap,c,systemlink)
        eq,l = readia(st,varmap,ctrmap,Eq([],0),c)
        push!(systemlink,[-3,l])
        return eq end

    function readia(st,varmap,ctrmap,eq,c)
        col = length(st)-1
        if st[end-1] != ":" # coef lit coef lit >= b : id
            eq = Eq([],0)
            printstyled("missing ia ID: ctr will be ignored";color = :red)
        else
            eq = readeq(st,varmap,2:2:length(st)-3)
            l = st[end]
            l = l[1]=='@' ? ctrmap[l[2:end]] : parse(Int,l)
            if l<0
                l = c+l
            end
        end
        return eq,l end

    function processred(system,systemlink,st,varmap,ctrmap,redwitness,redid,f,prism)
        i = findfirst(x->x==":",st)
        eq = readeq(st[2:i],varmap)
        j = findlast(x->x==":",st)
        if i==j # detect the word begin
            j=length(st)
        end
        w = readwitness(st[i+1:j],varmap)
        c = redid
        range = 0:0
        pgranges = Vector{UnitRange{Int64}}()
        if st[end] == "begin"
            rev = reverse(eq)
            normcoefeq(rev)
            push!(system,rev)
            push!(systemlink,[-9])
            c+=1
            range,pgranges,c = readsubproof(system,systemlink,eq,w,c,f,varmap,ctrmap)
            push!(prism,range)
            push!(systemlink,[-10])
        else
            push!(systemlink,[-4])
        end
        normcoefeq(eq)
        push!(system,eq)
        redwitness[redid] = Red(w,range,pgranges)
        redwitness[length(system)] = Red(w,range,pgranges)
        return c+1,Eq([],0) end

    function readwitness(st,varmap)
        st = remove(st,"->")
        st = remove(st,";")
        t = Vector{Lit}(undef,length(st))
        k = 1
        for i in 1:2:length(st)
            j = i+1
            t[i] = Lit(0,st[i][1]!='~',readwitnessvar(st[i],varmap))
            t[j] = Lit(0,st[j][1]!='~',readwitnessvar(st[j],varmap))
        end
        return t end

    function readwitnessvar(s,varmap)
        if s=="0"
            return 0
        elseif s=="1"
            return -1
        else 
            return readvar(s,varmap)
        end end
            
    function readsubproof(system,systemlink,eq,w,c,f,varmap,ctrmap)
        # notations : 
        # proofgoal i est la i eme contrainte de la formule F /\ ~C /\` ~`Ciw
        # proofgoal #1 est la contrainte dans la reduction
        # -1 est la contrainte qui est declaree dans le proofgoal. elle est affecte par w
        # -2 est la negation de la contrainte declaree dans le red
        # end -1  le -1 donne l'id de la contradiction. on peux aussi mettre c -1
        # l'affectation du temoins refais une nouvelle contrainte.
        nbopb = length(system)-length(systemlink)
        type,st = lparse(f)
        redid = c-1
        pgranges = Vector{UnitRange{Int64}}()
        while type !="end"
            if type == "proofgoal"
                pgid = c
                if st[2][1] == '#' 
                    push!(system,reverse(applywitness(eq,w)))
                    push!(systemlink,[-7])
                else
                    pgref = parse(Int,st[2])
                    push!(system,reverse(applywitness(system[pgref],w)))
                    push!(systemlink,[-8,pgref])
                end
                c+=1
                type,st = lparse(f)
                while type != "end"
                    eq = Eq([],0)
                    if type == "u" || type == "rup"
                        eq = processrup(st,varmap,systemlink,in_pg=true)
                        systemlink[end][1] = -5 # in subproof, rup is -5
                    elseif type == "p" || type == "pol"
                        eq = processpol(st,varmap,system,systemlink,c,ctrmap,nbopb)
                        systemlink[end][1] = -6 # in subproof, rup is -6
                    end
                    if length(eq.t)!=0 || eq.b!=0
                        normcoefeq(eq)
                        push!(system,eq)
                        c+=1
                    end
                    type,st = lparse(f)
                end
                push!(pgranges,pgid:c-1)
            end
            type,st = lparse(f)
        end
        return redid:c-1,pgranges,c end

    function applywitness(eq,w)
        t = Lit[]
        b = eq.b
        for l in eq.t
            for i in 1:2:length(w)
                if l.var == w[i].var
                    if w[i+1].var > 0
                        if l.sign != w[i].sign
                            b-= l.coef
                        end
                    else 
                        if l.sign == w[i].sign
                            b-= l.coef
                        end
                    end
                else
                    push!(t,l)
                end
            end
        end
        return Eq(t,b) end

    function processsoli(st,varmap,system,systemlink,c,prism,obj,solirecord)
        push!(systemlink,[-21])
        return findbound(system,st,c,varmap,prism,obj,solirecord) end

    function findbound(system,st,c,varmap,prism,obj,solirecord)
        assi = findfullassi(system,st,c,varmap,prism)
        lits = Vector{Lit}(undef,length(assi))
        for i in eachindex(assi)
            if assi[i]==0
                throw(" assignement not propagated to full")
            else
                lits[i] = Lit(1,assi[i]==1,i) # we add the assignement
            end
        end
        solirecord[c] = lits
        b = 0
        for l in obj        #compute the bound
            if assi[l.var]==1 && l.sign || assi[l.var]==2 && !l.sign
                b+= l.coef
            end
        end
        negobj = [Lit(-l.coef,l.sign,l.var) for l in obj] # we negate the objective
        return Eq(negobj,-b+1) end # -b+1 because we want the bound to be strictly lower

    function findfullassi(system,st,init,varmap,prism)
        lits = Vector{Lit}(undef,length(st)-2)
        for i in 2:length(st) # sol var var var ;
            _ = readvar(st[i],varmap)# add the new vars in the varmap
        end
        assi = zeros(Int8,length(varmap))
        for i in 2:length(st)
            sign = st[i][1]!='~'
            var = readvar(st[i],varmap)
            lits[i-1] = Lit(1,!sign,var)
            assi[var] = sign ? 1 : 2
        end
        changes = true
        while changes
            changes = false
            for i in 1:init-1 # TODO can be replaced with efficient unit propagation
                if !inprism(i,prism)
                    eq = system[i]
                    s = slack(eq,assi)
                    if s<0
                        printstyled(" sol propagated assignement to contradiction "; color = :red)
                        print(" ",i," ")
                        println(st)
                        printeq(eq)
                        lits = [Lit(l.coef,!l.sign,l.var) for l in lits]
                        return assi
                    else
                        for l in eq.t                    
                            if l.coef > s && assi[l.var]==0
                                assi[l.var] = l.sign ? 1 : 2 # assi == 1 if l is true, 2 if l is false 0 if l is not assigned
                                changes = true
                            end end end end end end
        return assi end

    function processsolx(st,varmap,system,systemlink,c,prism)
        push!(systemlink,[-20])
        return solbreakingctr(system,st,c,varmap,prism) end

    function solbreakingctr(system,st,init,varmap,prism)
        assi = findfullassi(system,st,init,varmap,prism)
        lits = Vector{Lit}(undef,length(assi))
        for i in eachindex(assi)
            if assi[i]==0
                throw(" assignement not propagated to full")
            else
                lits[i] = Lit(1,assi[i]!=1,i) # we add the negation of the assignement
            end
        end
        return Eq(lits,1) end

# end; using .Parser 


# module Trimmer
    function getcone(system,invsys,varmap,systemlink,nbopb,prism,redwitness,conclusion,obj)
        n = length(system)
        antecedants = zeros(Bool,n)
        assi = zeros(Int8,length(varmap))
        cone = zeros(Bool,n)
        conelits = Dict{Int,Set{Int}}() # for the lits that we want to keep (works with conflict analysis)
        front = zeros(Bool,n)
        firstcontradiction = 0
        if conclusion == "UNSAT"
            firstcontradiction = getfirstcontradiction(system,varmap,prism)
        elseif occursin("BOUNDS",conclusion)
            firstcontradiction = getfirstboundeq(system,varmap,prism,obj,conclusion,cone)
        end
        cone[firstcontradiction] = 
        irminsul = Dict{} 
        if systemlink[firstcontradiction-nbopb][1] == -2         # first contradiction is pol
            fixfront(front,systemlink[firstcontradiction-nbopb])
        else
            if conclusion=="UNSAT" || conclusion=="NONE"
                # upquebit(system,invsys,assi,front,prism,conelits) #TODO i am here and I want my irminsul tree
                initialpropagation(system,invsys,)
            elseif conclusion == "BOUNDS"
                if !rup(system,invsys,front,firstcontradiction,assi,front,cone,conelits,prism,0:0) throw("rup failed onbound contradiction") end
            end
            append!(systemlink[firstcontradiction-nbopb],findall(front))
        end
        red = Red([],0:0,[]);
        newpfgl = true
        pfgl = Vector{UnitRange{Int64}}()
        while newpfgl # restart if new frontless proofgoals are needed.
            newpfgl = false
            while true in front
                #TODO put back stuff
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
        # fixredsystemlink(systemlink,cone,prism,nbopb)
        return cone,conelits
    end

    function getfirstcontradiction(system,varmap,prism) # find first syntactic ⊥ in sys
        assi = zeros(Int8,length(varmap))
        return findfirst(x->!inprism(x,prism) && slack(x,assi)<0,system) end

    function getfirstboundeq(system,varmap,prism,conclusion,obj,conclusion,cone) 
        st = split(conclusion,keepempty=false) # conclusion BOUNDS 10 20   ||  10 : id 20 : id 
        ub = 0; lb = parse(Int,st[3])
        if length(st)>3
            if st[4]!= ":"
                ub = parse(Int,st[4])
            else
                i = findlast(x->x==":",st)
                if i!=4
                    ub = parse(Int,st[i-1])
                end
            end
        end
        lbctr = Eq(obj,lb)
        ubctr = normcoefeq(negatecoefs(Eq(obj,ub)))
        lbid = ubid = 0
        for i in eachindex(system)
            if lbid>0 && isequal(system[i],lbctr)
                lbid = i
            end
            if ubid>0 && isequal(system[i],ubctr)
                ubid = i
            end
        end
        if ubid>0 cone[ubid] = true end
        conclusion = "conclusion BOUNDS $lb $ub" # ids will change
        return lbid end

    function negatecoefs(eq::Eq)
        c=0
        lits = [Lit(l.coef,l.sign,l.var) for l in eq.t]
        for l in lits
            l.coef = -l.coef
        end
        return Eq(lits,-eq.b) end

    function isequal(e::Eq,f::Eq) # equality between eq
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
        end end

    function isequal(a::Lit,b::Lit) # equality between lits
        return a.coef==b.coef && a.sign==b.sign && a.var==b.var end
    function fixfront(front::Vector{Bool},antecedants::Vector{Bool})
        for i in eachindex(antecedants)
            if antecedants[i]
                front[i] = true
            end
        end end

    function fixfront(front::Vector{Bool},antecedants::Vector{Int})
        for i in antecedants
            if i>0
                front[i] = true
            end
        end end











# end; using .Trimmer


# ======================================= main code ======================================= #

if "profile" in ARGS
    throw("uncomment here to enable profiling")
    # using StatProfilerHTML
    # @profilehtml main()
else main() end


#=
Differences with the veriPB grammar:
- the proof line is ended by \n, ; does not matter to the trimmer
- rup must not have hints (they will be discarded anyway)
- ia must be ended by : id
- the proof cannot end by SAT or NONE

Unsupported rules:
  - dom
  - obju
  - pbc
  - the ones I forgot
=#
