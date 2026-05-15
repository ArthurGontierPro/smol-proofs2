# This is a PB trimmer made to analyse proofs. If problem, ask arthur.pro.gontier@gmail.com
# julia GlasgowTrimnalyser.jl [options] [instance name or directory of instances]   options: atable sort rand clean veri profile load
const opb = ".opb"
const pbp = ".pbp"
const smol = ".smol"
const version = "3.0"
const abspath = "/home/arthur_gla/veriPB/subgraphsolver/"
const proofs = (i = findfirst(x -> isdir(x), ARGS)) === nothing ? abspath*"proofs/" : ARGS[i]
const inst   = (i = findfirst(x -> isfile(proofs*x*pbp) && isfile(proofs*x*opb), ARGS)) !== nothing ? ARGS[i] : nothing # search for proof 
using Random,DataStructures
# =============== main stuff =============
    function main()
        if "atable" in ARGS
            plotresultstable(); return 
        elseif "clean" in ARGS
            rm.(filter(f -> endswith(f, ".out") || endswith(f, ".err"),readdir(proofs; join=true))); return
        elseif inst !== nothing 
            trimnalyseandcie(inst); return
        end
        println(tabhead)
        for ins in getinstancesfromdir(proofs)
            trimnalyseandcie(ins)
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
    function trimnalyseandcie(ins)
            printabline(ins)
            t1,t2,t3 = trimnalyse(ins)
            t4,t5 = "verif" in ARGS ? verify(ins) : (-1,-1)
            printabline2(ins,t1,t2,t3,t4,t5) end

    function trimnalyse(ins)
        t1 = t2 = t3 = 0 ; file = ins
        # if "load" in ARGS file,system,systemlink,redwitness,solirecord,assertrecord,nbopb,varmap,ctrmap,output,conclusion,obj,invsys,prism,cone,conelits,invctrmap,succ,index = loadsys(file); @goto skiped end # using goto because I was told not to
        t1 = @elapsed begin 
            system,systemlink,redwitness,solirecord,assertrecord,nbopb,varmap,ctrmap,output,conclusion,obj,prism = readinstance(proofs,file) 
        end
        sys = PBSystem(system, length(varmap))
        t2 = @elapsed begin # cone mark usfull ctrs and lits
            cone,conelits = getcone(sys,systemlink,nbopb,prism,redwitness,conclusion,obj)
        end
        printconestat(cone)
        @label skiped
        t3 = @elapsed begin
            varmap_inv = Dict(varmap[k] => k for k in keys(varmap))
            writeconedel(proofs,file,sys,cone,conelits,systemlink,redwitness,solirecord,assertrecord,nbopb,varmap_inv,ctrmap,output,conclusion,obj,prism)
        end
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


# ======================================= plotting  ======================================= #
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

# ======================================= sugar ======================================= #
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
    function printconestat(cone)
        printgray("\r\033[99G% "*string(sum(cone))*"/"*string(length(cone))) end

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

module Dumping # ======================================= mem dump ======================================= #
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
end; # using .Dumping # to save the import un comment this.
# ======================================= parser  ======================================= #
    function readinstance(path,file)
        system,varmap,ctrmap,obj = readopb(path,file)
        nbopb = length(system)
        system,systemlink,redwitness,solirecord,assertrecord,output,conclusion = readproof(path,file,system,varmap,ctrmap,obj)
        normcoefeq.(system)
        # invsys = getinvsys(system,systemlink,varmap) # obselete since PBsys
        prism = availableranges(redwitness)
        return system,systemlink,redwitness,solirecord,assertrecord,nbopb,varmap,ctrmap,output,conclusion,obj,prism end

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
    function addeq(eq1, eq2)
        t1 = eq1.t; t2 = eq2.t
        lits = Lit[]; sizehint!(lits, length(t1) + length(t2))
        c = 0
        i = j = 1
        while i <= length(t1) && j <= length(t2)
            if t1[i].var < t2[j].var
                push!(lits, t1[i]); i += 1
            elseif t1[i].var > t2[j].var
                push!(lits, t2[j]); j += 1
            else
                tmplit, tmpc = add(t1[i], t2[j])
                c += tmpc
                tmplit.coef != 0 && push!(lits, tmplit)
                i += 1; j += 1
            end
        end
        while i <= length(t1); push!(lits, t1[i]); i += 1 end
        while j <= length(t2); push!(lits, t2[j]); j += 1 end
        return Eq(lits, eq1.b + eq2.b - c) end

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

    function applywitness(eq, w)
        witness_idx = Dict{Int,Int}(w[i].var => i for i in 1:2:length(w))
        t = Lit[]
        b = eq.b
        for l in eq.t
            idx = get(witness_idx, l.var, 0)
            if idx != 0
                if w[idx+1].var > 0
                    l.sign != w[idx].sign && (b -= l.coef)
                else
                    l.sign == w[idx].sign && (b -= l.coef)
                end
            else
                push!(t, l)
            end
        end
        return Eq(t, b) end

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
    function availableranges(redwitness)                   # build the prism, a range colections of all the red subproofs
        prism = [a.range for (_,a) in redwitness if a.range!=0:0]
        return prism end


# ======================================= data struct ======================================= #
    struct PBSystem
        # Forward: equation → terms
        vars    ::Vector{Int32}
        coefs   ::Vector{Int32}
        signs   ::BitVector
        rhs     ::Vector{Int64}
        row_ptr ::Vector{Int32}
        # Inverse: variable → equations containing it
        var_ptr ::Vector{Int32}     # length = n_vars + 1
        var_eqs ::Vector{Int32} end # flat list of equation ids end

    mutable struct Trail
        var  ::Vector{Int32}    # variables in propagation order
        eq   ::Vector{Int32}    # reason equation for each entry
        pos  ::Vector{Int}      # pos[v] = index in var/eq (0 = unassigned)
        assi ::Vector{Int8} end # current assignment (1=true, 2=false, 0=unset) end
# ======================================== Trimmer =====================================
    Trail(n_vars::Int) = Trail(Int32[], Int32[], zeros(Int, n_vars), zeros(Int8, n_vars))
    @inline function reset!(t::Trail)
        empty!(t.var); empty!(t.eq)
        fill!(t.pos, 0); fill!(t.assi, 0) end

    @inline function pushtrail!(t::Trail, v::Int32, eq::Int32, val::Int8)
        push!(t.var, v); push!(t.eq, eq)
        iv = Int(v)
        @inbounds t.pos[iv] = length(t.var)
        @inbounds t.assi[iv] = val end

    function PBSystem(system::Vector{Eq}, n_vars::Int)
        n_eqs  = length(system)
        n_lits = sum(length(eq.t) for eq in system; init=0)

        vars    = Vector{Int32}(undef, n_lits)
        coefs   = Vector{Int32}(undef, n_lits)
        signs   = BitVector(undef, n_lits)
        rhs     = Vector{Int64}(undef, n_eqs)
        row_ptr = Vector{Int32}(undef, n_eqs + 1)

        row_ptr[1] = 1
        k = 1
        for (e, eq) in enumerate(system)
            rhs[e] = eq.b
            for lit in eq.t
                vars[k]  = lit.var
                coefs[k] = lit.coef
                signs[k] = lit.sign
                k += 1
            end
            row_ptr[e+1] = k
        end

        var_count = zeros(Int32, n_vars)
        for eq in system, lit in eq.t
            var_count[lit.var] += 1
        end
        var_ptr = Vector{Int32}(undef, n_vars + 1)
        var_ptr[1] = 1
        for v in 1:n_vars
            var_ptr[v+1] = var_ptr[v] + var_count[v]
        end
        var_eqs = Vector{Int32}(undef, n_lits)
        fill!(var_count, 0)
        for (e, eq) in enumerate(system), lit in eq.t
            v = lit.var
            var_eqs[var_ptr[v] + var_count[v]] = e
            var_count[v] += 1
        end

        return PBSystem(vars, coefs, signs, rhs, row_ptr, var_ptr, var_eqs) end



    eqrange(sys::PBSystem, e) = Int(sys.row_ptr[e]):Int(sys.row_ptr[e+1])-1
    varrange(sys::PBSystem, v) = Int(sys.var_ptr[v]):Int(sys.var_ptr[v+1])-1
    function slack(sys::PBSystem, e::Int, assi::Vector{Int8})
        c = zero(Int32)
        @inbounds for i in eqrange(sys, e)
            val  = assi[Int(sys.vars[i])]
            sign = sys.signs[i]
            unaffected = (val == 0) | (sign & (val == 1)) | (!sign & (val == 2))
            c += unaffected ? sys.coefs[i] : zero(Int32)
        end
        return c - sys.rhs[e] end

    inprism(n, prism::BitVector) = n <= length(prism) && prism[n]
    # inprism(n, prism) = any(r -> n in r, prism)
    @inline function setconelits(conelits, v, id)
        push!(get!(Set{Int}, conelits, id), v) end

    function printlitcolor(coef, sign, var, color)
        if coef != 1 printstyled(coef; color = :blue) end
        sign ? print(" ") : printstyled('~'; color = :red)
        printstyled(var; color = color) end

    function printeqconelit(sys::PBSystem, e::Int, conelits)
        conelit = get(conelits, e, Set{Int}())
        s = zero(Int32)
        for k in eqrange(sys, e)
            v = Int(sys.vars[k])
            print(" ")
            if v in conelit
                printlitcolor(sys.coefs[k], sys.signs[k], v, :yellow)
            else
                printlitcolor(sys.coefs[k], sys.signs[k], v, :magenta)
                s += sys.coefs[k]
            end
        end
        if s == 0
            println(" >= ", sys.rhs[e])
        else
            println(" >= ", sys.rhs[e], " - ", s, " >= ", sys.rhs[e] - s)
        end end

    function printeq(sys::PBSystem, e::Int)
        for k in eqrange(sys, e)
            print(" ")
            printlitcolor(sys.coefs[k], sys.signs[k], Int(sys.vars[k]), :green)
        end
        println(" >= ", sys.rhs[e]) end

    function fixante(systemlink::Vector{Vector{Int}}, antecedants::Vector{Bool}, i)
        for j in eachindex(systemlink[i])
            t = systemlink[i][j]
            if t > 0 && !(j < length(systemlink[i]) && systemlink[i][j+1] in (-2,-3))
                antecedants[t] = true
            end
        end end

    function fixredsystemlink(systemlink, cone, prism, nbopb)
        for range in prism
            for i in range
                if cone[i]
                    for j in eachindex(systemlink[i-nbopb])
                        k = systemlink[i-nbopb][j]
                        if k > 0 && !(k in systemlink[range.start-nbopb]) && k < range.start - nbopb
                            push!(systemlink[range.start-nbopb], k)
                        end
                    end
                end
            end
            sort!(systemlink[range.start-nbopb])
        end end

    function eqvars(sys::PBSystem, e::Int)
        Set{Int}(Int(sys.vars[k]) for k in eqrange(sys, e)) end

    function istrivial(sys::PBSystem, e::Int, conelits)
        cl = get(conelits, e, nothing)
        cl === nothing && return sys.rhs[e] <= 0
        a = zero(Int32)
        for k in eqrange(sys, e)
            !(sys.vars[k] in cl) && (a += sys.coefs[k])
        end
        return sys.rhs[e] - a <= 0 end

    function fixconelits(sys::PBSystem, conelits, i::Int, antecedants::Vector{Bool}, link)
        anteids = findall(antecedants)
        # if -3 in link[2:end] # deactivate lit trimming. when div is there 
            # for j in anteids
                # conelits[j] = eqvars(sys, j)
            # end
            # return
        # end
        cl = get(conelits, i, nothing)
        myconelit = cl !== nothing ? cl : eqvars(sys, i)
        poslits = Set{Int}()
        neglits = Set{Int}()
        for j in anteids
            for k in eqrange(sys, j)
                sys.signs[k] ? push!(poslits, Int(sys.vars[k])) : push!(neglits, Int(sys.vars[k]))
            end
            cj = get(conelits, j, nothing)
            cj !== nothing && (myconelit = myconelit ∪ cj)
        end
        myconelit = myconelit ∪ (poslits ∩ neglits)
        conelits[i] = myconelit ∩ eqvars(sys, i)
        for j in anteids
            conelits[j] = myconelit ∩ eqvars(sys, j)
        end end

    function removetrivialantecedants(sys::PBSystem, antecedants::Vector{Bool}, conelits, link, init::Int)
        for i in findall(antecedants)
            istrivial(sys, i, conelits) || continue
            j = findfirst(x -> x == i, link)
            if j === nothing
                println("antecedant $i not found in link $link")
                continue
            end
            k0 = findfirst(x -> x == -1, link[j+1:end])
            if k0 === nothing
                printeqconelit(sys,init,conelits)
                println(link)
                for j in findall(antecedants)
                    printeqconelit(sys,j,conelits)
                end
                println("antecedant $i's addition not found in link $link")
                deleteat!(link, j)
                antecedants[i] = false
                continue
            end
            deleteat!(link, (j, k0 + j))
            antecedants[i] = false
        end end

    @inline function slack_reversed(sys::PBSystem, e::Int, assi::Vector{Int8})
        total = zero(Int32)
        c     = zero(Int32)
        @inbounds for k in eqrange(sys, e)
            coef   = sys.coefs[k]
            total += coef
            val    = assi[Int(sys.vars[k])]
            sign   = sys.signs[k]
            # ~lit is active when original lit is false or unassigned
            unaffected = (val == 0) | (sign & (val == Int8(2))) | (!sign & (val == Int8(1)))
            c += unaffected ? coef : zero(Int32)
        end
        return c - (total - sys.rhs[e] + 1) end

    # Given a falsified constraint ceq, traces back through the propagation trail to find
    # the minimal set of antecedent equations whose cone literals explain the contradiction.
    # Greedy heuristic: prefer falsified literals whose antecedent has the lowest proof index —
    # early constraints have smaller antecedent subtrees, so using them minimises cone size.
    function conflicttrail(ceq::Int, sys::PBSystem, t::Trail,
                           antecedants::Vector{Bool}, conelits; rev_init::Int=-1)
        n_vars = length(t.assi)
        heap   = BinaryMaxHeap{Tuple{Int,Int32}}()       # max-heap on trail pos: ensures antecedents are still assigned when needed
        inheap = falses(n_vars + 1)                      # inheap[v+1]: v is currently in the heap (index +1 to handle fake var 0)

        antecedants[ceq] = true
        push!(t.var, Int32(0)); push!(t.eq, Int32(ceq))  # fake var 0 represents the conflict eq itself
        push!(heap, (length(t.var), Int32(0))); inheap[1] = true

        falsified_lits = Tuple{Int,Int,Int,Int32}[]      # reused buffer: (antecedent eq index, trail pos, var, coef)
        while !isempty(heap)
            vtp, v32 = pop!(heap)                        # most recently propagated unexplained variable
            v = Int(v32)
            inheap[v+1] = false
            v != 0 && (t.assi[v] = Int8(0))             # unassign v: falsified check returns false for v in future iterations
            eq     = Int(t.eq[vtp])                      # antecedent equation that propagated v
            antecedants[eq] = true
            eq_rev = (eq == rev_init)
            b      = eq_rev ? (sum(sys.coefs[k] for k in eqrange(sys, eq); init=zero(Int32)) - sys.rhs[eq] + 1) :
                              sys.rhs[eq]                # effective RHS (adjusted if eq was used reversed in rup)
            empty!(falsified_lits)
            somme = zero(Int32)                          # sum of coefs of all literals except v
            @inbounds for k in eqrange(sys, eq)
                w = Int(sys.vars[k])
                w == v && continue                       # v is the propagated literal; skip it
                coef = sys.coefs[k]
                somme += coef
                wtp  = t.pos[w]
                wtp > vtp && continue                    # level skip: w assigned after v, cannot be an antecedent of v's propagation
                wval = t.assi[w]; wsign = sys.signs[k]
                falsified_w = eq_rev ? ((wsign & (wval == Int8(1))) | (!wsign & (wval == Int8(2)))) :
                                       ((wsign & (wval == Int8(2))) | (!wsign & (wval == Int8(1))))
                falsified_w && push!(falsified_lits, (wtp > 0 ? @inbounds(Int(t.eq[wtp])) : 0, wtp, w, coef))
            end
            sort!(falsified_lits; by = x -> x[1])        # lowest proof index first: early constraints have fewer antecedents, reducing cone size

            v != 0 && setconelits(conelits, v, eq)
            for (_, wtp, w, coef) in falsified_lits
                somme < b && break                        # enough literals removed: propagation of v is explained
                if wtp > 0 && !inheap[w+1]
                    push!(heap, (wtp, Int32(w))); inheap[w+1] = true
                end
                setconelits(conelits, w, eq)
                somme -= coef
            end
            if somme >= b                                 # falsified literals were insufficient to explain v — should not happen
                printstyled("conflicttrail: could not explain var $v in eq $eq\n"; color = :red)
                printeq(sys, eq); printeqconelit(sys, eq, conelits)
                throw(ErrorException("conflicttrail: could not explain $v with eq $eq"))
            end
        end end

        # Trail-based unit propagation (replaces upquebit).
    function propagate!(sys::PBSystem, t::Trail, prism, antecedants::Vector{Bool}, conelits)
        i = 1; n = length(sys.rhs)
        que = trues(n)
        while i <= n
            if !inprism(i, prism) && que[i]
                s = slack(sys, i, t.assi)
                if s < 0
                    conflicttrail(i, sys, t, antecedants, conelits)
                    return
                end
                que[i] = false
                rewind = i + 1
                @inbounds for k in eqrange(sys, i)
                    v = Int(sys.vars[k])
                    t.assi[v] != 0 && continue
                    sys.coefs[k] > s || continue
                    pushtrail!(t, Int32(v), Int32(i), sys.signs[k] ? Int8(1) : Int8(2))
                    for j in varrange(sys, v)
                        eid = Int(sys.var_eqs[j])
                        que[eid] = true
                        rewind = min(rewind, eid)
                    end
                end
                i = rewind
            else
                i += 1
            end
        end
        printstyled("propagate! found no conflict\n"; color = :red) end

        # Linear-scan RUP (kept for comparison). Two rewind pointers (r0/r1) + que BitVector guard.
    function ruptrail_deprecated(sys::PBSystem, init::Int, t::Trail,
                      antecedants::Vector{Bool}, front::Vector{Bool},
                      cone::Vector{Bool}, conelits, prism, subrange)
        prio = true
        r0   = 1           # non-priority rewind; starts at 1 so non-prio pass sweeps from eq 1
        r1   = init + 1    # priority rewind; init+1 = sentinel "none"
        i    = 1
        que  = trues(init)
        while i <= init
            in_queue = !inprism(i, prism) || (i in subrange)
            if que[i] && in_queue && (!prio || cone[i] || front[i])
                rev = (i == init)
                s   = rev ? slack_reversed(sys, i, t.assi) : slack(sys, i, t.assi)
                if s < 0
                    conflicttrail(i, sys, t, antecedants, conelits; rev_init=init)
                    return true
                end
                @inbounds for k in eqrange(sys, i)
                    v = Int(sys.vars[k])
                    t.assi[v] != 0 && continue
                    sys.coefs[k] > s || continue
                    sign = sys.signs[k]
                    pushtrail!(t, Int32(v), Int32(i),
                               rev ? (sign ? Int8(2) : Int8(1)) :
                                     (sign ? Int8(1) : Int8(2)))
                    for j in varrange(sys, v)
                        eid = Int(sys.var_eqs[j])
                        (eid <= init && eid != i) || continue
                        que[eid] = true
                        if cone[eid] || front[eid]
                            r1 = min(r1, eid)
                        else
                            r0 = min(r0, eid)
                        end
                    end
                end
                que[i] = false
                i += 1
                if prio
                    i  = min(i, r1)
                    r1 = init + 1
                else
                    if r1 < init + 1
                        prio = true
                        r0   = min(i, r0)
                        i    = r1
                        r1   = init + 1
                    else
                        i  = min(i, r0)
                        r0 = init + 1
                    end
                end
            else
                i += 1
            end
            if prio && i == init + 1
                prio = false
                i    = r0
                r0   = init + 1
            end
        end
        return false end

    # Push eid into the right heap if not already queued.
    @inline function activate!(eid, que, pq_prio, pq_nonprio, cone, front)
        que[eid] && return                 # already in a heap, skip
        que[eid] = true
        if cone[eid] || front[eid]; push!(pq_prio, eid)    # priority: already in cone
        else                        push!(pq_nonprio, eid)  # non-priority: new to cone
        end end

    # Compute slack, propagate, re-activate triggered equations. Return true on conflict.
    @inline function process_eq!(i, init, sys, t, antecedants, conelits,
                                 que, pq_prio, pq_nonprio, cone, front)
        rev = (i == init)                  # reversed constraint for RUP check of init
        s   = rev ? slack_reversed(sys, i, t.assi) : slack(sys, i, t.assi)
        if s < 0                           # falsified: conflict found
            conflicttrail(i, sys, t, antecedants, conelits; rev_init=init)
            return true
        end
        @inbounds for k in eqrange(sys, i)
            v = Int(sys.vars[k])
            t.assi[v] != 0 && continue     # already assigned
            sys.coefs[k] > s || continue   # coef too small to force propagation
            sign = sys.signs[k]
            pushtrail!(t, Int32(v), Int32(i),
                       rev ? (sign ? Int8(2) : Int8(1)) :
                             (sign ? Int8(1) : Int8(2)))            # assign variable
            for j in varrange(sys, v)
                eid = Int(sys.var_eqs[j])
                (eid <= init && eid != i) || continue               # only earlier/unrelated eqs
                activate!(eid, que, pq_prio, pq_nonprio, cone, front) # re-queue equations containing v
            end
        end
        que[i] = false                     # done: remove from queue
        return false end

        # Heap-based RUP check. Same algorithm as ruptrail_deprecated but replaces the linear scan
        # with two BinaryMinHeap{Int}: pq_prio (cone/front equations) and pq_nonprio (others).
        # Priority pass drains pq_prio fully before taking one step from pq_nonprio.
    function ruptrail(sys::PBSystem, init::Int, t::Trail,
                      antecedants::Vector{Bool}, front::Vector{Bool},
                      cone::Vector{Bool}, conelits, prism, subrange)
        que        = falses(init)              # true = equation is currently in a heap
        pq_prio    = BinaryMinHeap{Int}()      # cone/front equations (process first)
        pq_nonprio = BinaryMinHeap{Int}()      # all other equations
        for i in 1:init                        # seed both heaps with all eligible equations
            (!inprism(i, prism) || (i in subrange)) || continue
            activate!(i, que, pq_prio, pq_nonprio, cone, front)
        end
        while true
            while !isempty(pq_prio)            # drain priority equations first
                i = pop!(pq_prio)
                que[i] || continue             # stale pop guard (safety net)
                process_eq!(i, init, sys, t, antecedants, conelits,
                            que, pq_prio, pq_nonprio, cone, front) && return true
            end
            isempty(pq_nonprio) && break       # nothing left: no conflict found
            i = pop!(pq_nonprio)               # take one non-priority equation
            que[i] || continue                 # stale pop guard (safety net)
            process_eq!(i, init, sys, t, antecedants, conelits,
                        que, pq_prio, pq_nonprio, cone, front) && return true  # loop back to drain pq_prio
        end
        return false end

    function getcone(sys::PBSystem, systemlink, nbopb::Int,
                     prism::Vector{UnitRange{Int64}}, redwitness, conclusion::String, obj)
        n    = length(sys.rhs)
        nvar = length(sys.var_ptr) - 1
        prism_bv = falses(n)
        for r in prism, i in r
            1 <= i <= n && (prism_bv[i] = true)
        end
        cone      = zeros(Bool, n)
        conelits  = Dict{Int,Set{Int}}()
        front     = zeros(Bool, n)
        trail = Trail(nvar)

        firstcontradiction = 0
        if conclusion == "UNSAT"
            firstcontradiction = getfirstcontradiction(sys, prism_bv)
        elseif occursin("BOUNDS", conclusion)
            firstcontradiction = getfirstboundeq(sys, prism, obj, conclusion, cone)
        end
        if firstcontradiction == 0
            conclusion == "UNSAT" && printstyled("\nUNSAT contradiction not found\n"; color = :red)
            return cone, conelits
        end

        cone[firstcontradiction] = true
        if systemlink[firstcontradiction - nbopb][1] == -2
            fixfront(front, systemlink[firstcontradiction - nbopb])
        else
            if conclusion == "UNSAT" || conclusion == "NONE"
                propagate!(sys, trail, prism_bv, front, conelits)
            elseif occursin("BOUNDS", conclusion)
                if !ruptrail(sys, firstcontradiction, trail, front, front, cone, conelits, prism_bv, 0:0)
                    printstyled("initial rup for bound contradiction failed\n"; color = :red)
                end
            end
            append!(systemlink[firstcontradiction - nbopb], findall(front))
        end
        red         = Red([], 0:0, [])
        pfgl        = UnitRange{Int64}[]
        antecedants = zeros(Bool, n)
        newpfgl = true
        while newpfgl
            newpfgl = false
            while any(front)
                i = findlast(front)
                front[i] = false
                if !cone[i]
                    cone[i] = true
                    if i > nbopb
                        tlink = systemlink[i - nbopb][1]
                        if tlink == -1                              # rup
                            fill!(antecedants, false)
                            reset!(trail)
                            if ruptrail(sys, i, trail, antecedants, front, cone, conelits, prism_bv, 0:0)
                                antecedants[i] = false
                                append!(systemlink[i - nbopb], findall(antecedants))
                                fixfront(front, antecedants)
                            else
                                printstyled("rup failed at $i\n"; color = :red)
                                return cone, conelits
                            end
                        elseif tlink >= -3 || (tlink == -30 && length(systemlink[i - nbopb]) > 1)
                            fill!(antecedants, false)
                            fixante(systemlink, antecedants, i - nbopb)
                            fixconelits(sys, conelits, i, antecedants, systemlink[i - nbopb])
                            removetrivialantecedants(sys, antecedants, conelits, systemlink[i - nbopb], i)
                            fixfront(front, antecedants)
                        elseif tlink == -10                         # end of red subproof
                            red = redwitness[i]
                            front[red.range.start] = true
                            for subr in red.pgranges
                                if systemlink[subr.start - nbopb][1] == -8 && !(front[subr.start] || cone[subr.start])
                                    push!(pfgl, subr)
                                else
                                    front[subr.start] = true
                                    front[subr.stop]  = true
                                end
                            end
                        elseif tlink == -5                          # subproof rup
                            subran_idx = findfirst(x -> i in x, red.pgranges)
                            fill!(antecedants, false)
                            reset!(trail)
                            if ruptrail(sys, i, trail, antecedants, front, cone, conelits, prism_bv, red.pgranges[subran_idx])
                                antecedants[i] = false
                                append!(systemlink[i - nbopb], findall(antecedants))
                                fixfront(front, antecedants)
                            else
                                printstyled("subproof rup failed\n"; color = :red)
                            end
                        elseif tlink == -6 || tlink == -8           # subproof pol / proofgoal ref
                            fill!(antecedants, false)
                            fixante(systemlink, antecedants, i - nbopb)
                            fixfront(front, antecedants)
                        elseif tlink == -7                          # proofgoal #1: nothing needed
                        end
                    end
                end
            end
            for r in pfgl
                id = systemlink[r.start - nbopb][2]
                if cone[id] && !cone[r.start]
                    front[r.start] = front[r.stop] = true
                    newpfgl = true
                end
            end
        end
        fixredsystemlink(systemlink, cone, prism, nbopb)
        return cone, conelits end

    function getfirstcontradiction(sys::PBSystem, prism)
        assi = zeros(Int8, length(sys.var_ptr) - 1)
        for e in eachindex(sys.rhs)
            !inprism(e, prism) && slack(sys, e, assi) < 0 && return e
        end
        return 0 end

    function eqmatch(sys::PBSystem, e::Int, eq::Eq)
        sys.rhs[e] != eq.b && return false
        r = eqrange(sys, e)
        length(r) != length(eq.t) && return false
        for (i, lit) in zip(r, eq.t)
            (sys.vars[i] != lit.var || sys.coefs[i] != lit.coef || sys.signs[i] != lit.sign) && return false
        end
        return true end

    function getfirstboundeq(sys::PBSystem, prism::Vector{UnitRange{Int64}}, obj, conclusion::String, cone::Vector{Bool})
        st = split(conclusion, keepempty=false) # conclusion BOUNDS 10 20   ||  10 : id 20 : id
        ub = 0; lb = parse(Int, st[3])
        if length(st) > 3
            if st[4] != ":"
                ub = parse(Int, st[4])
            else
                i = findlast(x -> x == ":", st)
                if i != 4
                    ub = parse(Int, st[i-1])
                end
            end
        end
        lbctr = Eq(obj, lb)
        ubctr = negatecoefs(Eq(obj, ub)); normcoefeq(ubctr)
        lbid = ubid = 0
        for e in eachindex(sys.rhs)
            if lbid == 0 && eqmatch(sys, e, lbctr)
                lbid = e
            end
            if ubid == 0 && eqmatch(sys, e, ubctr)
                ubid = e
            end
            lbid > 0 && ubid > 0 && break
        end
        if ubid > 0 cone[ubid] = true end
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
    @inline function fixfront(front::Vector{Bool},antecedants::Vector{Bool})
        for i in eachindex(antecedants)
            if antecedants[i]
                front[i] = true
            end
        end end

    @inline function fixfront(front::Vector{Bool},antecedants::Vector{Int})
        for i in antecedants
            if i>0
                front[i] = true
            end
        end end

# ======================================= Printer ======================================= #
    function isid(link, k)
        return link[k] > 0 && (k == length(link) || (link[k+1] != -2 && link[k+1] != -3)) end

    function writelits(f::IO, lits, varmap)
        for l in lits
            print(f, l.coef, " ", l.sign ? "" : "~", varmap[l.var], " ")
        end end

    function writeeq(f::IO, sys::PBSystem, e::Int, varmap)
        for k in eqrange(sys, e)
            print(f, sys.coefs[k], " ", sys.signs[k] ? "" : "~", varmap[Int(sys.vars[k])], " ")
        end
        print(f, ">= ", sys.rhs[e], " ;\n") end

    function writeeqconelits(f::IO, sys::PBSystem, e::Int, varmap, conelit)
        b = zero(Int32)
        for k in eqrange(sys, e)
            v = Int(sys.vars[k])
            if v in conelit || -v in conelit
                print(f, sys.coefs[k], " ", sys.signs[k] ? "" : "~", varmap[v], " ")
            else
                b += sys.coefs[k]
            end
        end
        print(f, ">= ", max(0, Int(sys.rhs[e]) - Int(b)), " ;\n") end

    function writeu(f::IO, sys::PBSystem, e::Int, varmap)
        print(f, "rup "); writeeq(f, sys, e, varmap) end

    function writeuconelits(f::IO, sys::PBSystem, e::Int, varmap, conelit)
        print(f, "rup "); writeeqconelits(f, sys, e, varmap, conelit) end

    function writeia(f::IO, sys::PBSystem, e::Int, link, index, varmap)
        print(f, "ia ")
        for k in eqrange(sys, e)
            print(f, sys.coefs[k], " ", sys.signs[k] ? "" : "~", varmap[Int(sys.vars[k])], " ")
        end
        print(f, ">= ", sys.rhs[e], " : ", index[link], " ;\n") end

    function writeiaconelits(f::IO, sys::PBSystem, e::Int, link, index, varmap, conelit)
        b = zero(Int32)
        print(f, "ia ")
        for k in eqrange(sys, e)
            v = Int(sys.vars[k])
            if v in conelit || -v in conelit
                print(f, sys.coefs[k], " ", sys.signs[k] ? "" : "~", varmap[v], " ")
            else
                b += sys.coefs[k]
            end
        end
        print(f, ">= ", max(0, Int(sys.rhs[e]) - Int(b)), " : ", index[link], " ;\n") end

    function writewitness(f::IO, witness, varmap)
        for l in witness.w
            if l.var > 0; print(f, !l.sign ? " ~" : " ", varmap[l.var])
            else          print(f, " ", -l.var) end
        end end

    function writered(f::IO, sys::PBSystem, e::Int, varmap, witness, beg; reversed=false)
        print(f, "red")
        for k in eqrange(sys, e)
            sign = reversed ? !sys.signs[k] : sys.signs[k]
            print(f, " ", sys.coefs[k], sign ? " " : " ~", varmap[Int(sys.vars[k])])
        end
        rhs = reversed ? (sum(Int(sys.coefs[k]) for k in eqrange(sys, e); init=0) - Int(sys.rhs[e]) + 1) :
                         Int(sys.rhs[e])
        print(f, " >= ", rhs, " ;")
        writewitness(f, witness, varmap)
        print(f, beg, "\n") end

    function writepol(f::IO, link, index, varmap)
        print(f, "pol")
        for i in 2:length(link)
            t = link[i]
            if t == -1;      print(f, " +")
            elseif t == -2;  print(f, " *")
            elseif t == -3;  print(f, " d")
            elseif t == -4;  print(f, " s")
            elseif t == -5;  print(f, " w")
            elseif t > 0
                if link[i+1] in [-2, -3]; print(f, " ", t)
                else                       print(f, " ", index[t]) end
            elseif t <= -100
                sign = mod((-t), 100) != 1
                print(f, sign ? " " : " ~", varmap[(-t) ÷ 100])
            end
        end
        print(f, " ;\n") end

    function writesolx(f::IO, sys::PBSystem, e::Int, varmap)
        print(f, "solx")
        for k in eqrange(sys, e)
            print(f, sys.signs[k] ? " ~" : " ", varmap[Int(sys.vars[k])])
        end
        print(f, " ;\n") end

    function writesoli(f::IO, sol, varmap)
        print(f, "soli")
        for l in sol
            print(f, l.sign ? " " : " ~", varmap[l.var])
        end
        print(f, " ;\n") end

    function writedel(f, systemlink, i, succ, index, nbopb, dels)
        isdel = false
        link = systemlink[i - nbopb]
        for k in eachindex(link)
            p = link[k]
            if isid(link, k) && !dels[p]
                m = maximum(succ[p])
                if m == i
                    if !isdel
                        write(f, "del id ")
                        isdel = true
                    end
                    dels[p] = true
                    if index[p] == 0
                        println(p, " in ", systemlink[p - nbopb])
                        printstyled(string("del index is 0 for ", p, " => ", index[p], "\n"); color = :red)
                    else
                        write(f, string(index[p], " "))
                    end
                end
            end
        end
        if isdel write(f, " ;\n") end end

    function invlink(systemlink, succ::Vector{Vector{Int}}, cone, nbopb)
        for i in eachindex(systemlink)
            if isassigned(systemlink, i)
                link = systemlink[i]
                for k in eachindex(link)
                    j = link[k]
                    if isid(link, k) && cone[i + nbopb]
                        if isassigned(succ, j)
                            if !(i + nbopb in succ[j])
                                push!(succ[j], i + nbopb)
                            end
                        else
                            succ[j] = [i + nbopb]
                        end
                    end
                end
            end
        end end

    function justifydeg(f, sys::PBSystem, e::Int, hints, index, varmap)
        link = [-2, parse(Int, hints[1])]
        for j in 2:length(hints)-1
            push!(link, parse(Int, hints[j]))
            push!(link, -1)
        end
        push!(link, parse(Int, hints[end]))
        push!(link, -1, -4)
        writepol(f, link, index, varmap)
        print(f, "ia ")
        for k in eqrange(sys, e)
            print(f, sys.coefs[k], " ", sys.signs[k] ? "" : "~", varmap[Int(sys.vars[k])], " ")
        end
        print(f, ">= ", sys.rhs[e], " : -1 ;\n")
        write(f, "del id -2 ;\n")
        return 1 end

    function justify(f, sys::PBSystem, e::Int, asserthint, index, varmap)
        st = split(asserthint, keepempty=false)
        extrai = 0
        if st[1] == "deg"
            extrai = justifydeg(f, sys, e, st[2:end], index, varmap)
        end
        return extrai end

    function writeconedel(path, file, sys::PBSystem, cone, conelits, systemlink,
                          redwitness, solirecord, assertrecord, nbopb,
                          varmap, ctrmap, output, conclusion, obj, prism)
        index = zeros(Int, length(sys.rhs))
        lastindex = 0
        open(path*file*opb*smol, "w") do f
            if length(obj) > 0
                print(f, "min: ")
                writelits(f, obj, varmap)
                print(f, ";\n")
            end
            for i in 1:nbopb
                if cone[i]
                    lastindex += 1
                    index[i] = lastindex
                    cl = get(conelits, i, nothing)
                    if cl !== nothing; writeeqconelits(f, sys, i, varmap, cl)
                    else              writeeq(f, sys, i, varmap) end
                end
            end
        end
        succ = Vector{Vector{Int}}(undef, length(sys.rhs))
        dels = zeros(Bool, length(sys.rhs))
        # dels = ones(Bool, length(sys.rhs)); println("nodel mode")
        dels[1:nbopb] .= true
        for p in prism
            dels[p] .= true
        end
        invlink(systemlink, succ, cone, nbopb)
        todel = Vector{Int}()
        open(path*file*pbp*smol, "w") do f
            print(f, "pseudo-Boolean proof version ", version, "\n")
            print(f, "f ", sum(cone[1:nbopb]), " ;\n")
            for i in nbopb+1:length(sys.rhs)
                if cone[i]
                    lastindex += 1
                    index[i] = lastindex
                    tlink = systemlink[i - nbopb][1]
                    if tlink == -1               # rup
                        cl = get(conelits, i, nothing)
                        if cl !== nothing; writeuconelits(f, sys, i, varmap, cl)
                        else              writeu(f, sys, i, varmap) end
                        if !isempty(eqrange(sys, i))
                            writedel(f, systemlink, i, succ, index, nbopb, dels)
                        end
                    elseif tlink == -2           # pol
                        writepol(f, systemlink[i - nbopb], index, varmap)
                        writedel(f, systemlink, i, succ, index, nbopb, dels)
                    elseif tlink == -3           # ia
                        cl = get(conelits, i, nothing)
                        if cl !== nothing; writeiaconelits(f, sys, i, systemlink[i - nbopb][2], index, varmap, cl)
                        else              writeia(f, sys, i, systemlink[i - nbopb][2], index, varmap) end
                        writedel(f, systemlink, i, succ, index, nbopb, dels)
                    elseif tlink == -4           # red alone
                        writered(f, sys, i, varmap, redwitness[i], "")
                        dels[i] = true
                    elseif tlink == -5           # rup in subproof
                        print(f, "    "); writeu(f, sys, i, varmap)
                        push!(todel, i)
                    elseif tlink == -6           # pol in subproof
                        print(f, "    "); writepol(f, systemlink[i - nbopb], index, varmap)
                        push!(todel, i)
                    elseif tlink == -9           # red with begin (reversed initial equation)
                        writered(f, sys, i, varmap, redwitness[i], " ; begin"; reversed=true)
                        todel = [i]; dels[i] = true
                    elseif tlink == -7           # red proofgoal #1
                        write(f, "    proofgoal #1\n")
                    elseif tlink == -8           # red proofgoal normal
                        print(f, "    proofgoal ", index[systemlink[i - nbopb][2]], "\n")
                        push!(todel, i)
                    elseif tlink == -10          # red proofgoal end
                        lastindex -= 1
                        write(f, "    end -1\n")
                        next = systemlink[i - nbopb][1]
                        if next != -7 && next != -8
                            lastindex += 1
                            write(f, "end\n")
                            for ii in todel
                                writedel(f, systemlink, ii, succ, index, nbopb, dels)
                            end
                        end
                    elseif tlink == -20          # solx
                        writesolx(f, sys, i, varmap); dels[i] = true
                    elseif tlink == -21          # soli
                        writesoli(f, solirecord[i], varmap)
                    elseif tlink == -30          # unchecked assumption
                        if haskey(assertrecord, i)
                            lastindex += justify(f, sys, i, assertrecord[i], index, varmap)
                        else
                            print(f, "a "); writeeq(f, sys, i, varmap)
                        end
                    else
                        println("ERROR tlink = ", tlink)
                        lastindex -= 1
                    end
                end
            end
            print(f, "output ", output, " ;\n")
            if conclusion == "SAT"
                print(f, "conclusion ", conclusion, " ;\n")
            elseif conclusion == "UNSAT"
                print(f, "conclusion ", conclusion, " : -1 ;\n")
            else
                print(f, replace(conclusion, ";" => ""), " ;\n")
            end
            write(f, "end pseudo-Boolean proof ;")
        end end


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
