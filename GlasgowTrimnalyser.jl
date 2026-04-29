# This is a PB trimmer made to analyse proofs. If problem, ask arthur.pro.gontier@gmail.com
# julia GlasgowTrimnalyser.jl [options] [instance name or directory of instances]   options: atable sort rand clean veri profile load
const opb = ".opb"
const pbp = ".pbp"
const smol = ".smol"
const abspath = "/home/arthur_gla/veriPB/subgraphsolver/"
const inst = findfirst(x -> isfile(x*pbp) && isfile(x*opb), ARGS)  # search for proof 
const proofs = (i = findfirst(x -> isdir(x), ARGS)) === nothing ? abspath*"proofs/" : ARGS[i]
using Random,DataStructures
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
    t1 = t2 = t3 = 0
    if "load" in ARGS file,system,systemlink,redwitness,solirecord,assertrecord,nbopb,varmap,ctrmap,output,conclusion,version,obj,invsys,prism,cone,conelits,invctrmap,succ,index = loadsys(file) else
    t1 = @elapsed begin
        system,systemlink,redwitness,solirecord,assertrecord,nbopb,varmap,ctrmap,output,conclusion,version,
        obj = readinstance(proofs,file)
    end
    normcoefsystem(system)
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


module ploting # ======================================= plotting  ======================================= #
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

end; using .ploting
module Sugarbox # ======================================= sugar ======================================= #
    onlyname(x) = splitext(basename(x))[1]
    ext(x) = splitext(basename(x))[2]
    noext(x) = splitext(x)[1]
    filesize(file) = stat(file).size
    inssize(file) = filesize(proofs*file*opb) + filesize(proofs*file*pbp)
    tryrm(s) = if isfile(s) rm(s) end
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

end; using .Sugarbox 
module Dumping # ======================================= mem dump ======================================= #
    using Serialization
    function dumpsys(file,system,systemlink,redwitness,solirecord,assertrecord,nbopb,varmap,ctrmap,output,conclusion,version,obj,invsys,prism,cone,conelits,invctrmap,succ,index)
        println("dumping started")
        sys = [file,system,systemlink,redwitness,solirecord,assertrecord,nbopb,varmap,ctrmap,output,conclusion,version,obj,invsys,prism,cone,conelits,invctrmap,succ,index]
        open("dump.jls","w") do f
            serialize(f,sys)
        end
        println("dumping ended") end

    function loadsys(file) 
        println("loading started")
        file,system,systemlink,redwitness,solirecord,assertrecord,nbopb,varmap,ctrmap,output,conclusion,version,obj,invsys,prism,cone,conelits,invctrmap,succ,index = deserialize("dump.jls")
        println("loading ended")
        return file,system,systemlink,redwitness,solirecord,assertrecord,nbopb,varmap,ctrmap,output,conclusion,version,obj,invsys,prism,cone,conelits,invctrmap,succ,index end
end; # using .Dumping # to save the import un comment this.
module parser # ======================================= parser  ======================================= #
    function readinstance(path,file)
        system,varmap,ctrmap,obj = readopb(path,file)
        nbopb = length(system)
        system,systemlink,redwitness,solirecord,assertrecord,output,conclusion,version = readproof(path,file,system,varmap,ctrmap,obj)
        return system,systemlink,redwitness,solirecord,assertrecord,nbopb,varmap,ctrmap,output,conclusion,version,obj end

    function readopb(path,file)
        system = Eq[]
        varmap = Dict{String,Int}()
        ctrmap = Dict{String, Int}()
        obj = ""
        open(string(path,'/',file,".opb"),"r"; lock = false) do f
            c = 1
            for ss in eachline(f)
                if ss[1] != '*'                                 # do not parse comments
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
        end
        return system,varmap,ctrmap,obj end

    mutable struct Eq
        t::Vector{Lit}
        b::Int end

    mutable struct Lit
        coef::Int
        sign::Bool
        var::Int end

    readobj(st,varmap) = readlits(st,varmap,2:2:(length(st)-1))
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

    readeq(st,varmap) = readeq(st,varmap,1:2:length(st)-4)
    function readeq(st,varmap,range)
        lits = readlits(st,varmap,range)
        bid = range.start-1+2length(lits)+2
        lits,c = merge(lits)
        eq = Eq(lits,parse(Int,st[bid])-c)
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

    function readveripb(path,file,system,varmap,ctrmap,obj)
        systemlink = Vector{Vector{Int}}()
        redwitness = Dict{Int, Red}()
        solirecord = Dict{Int, Vector{Lit}}()
        assertrecord = Dict{Int, String}()
        prism = Vector{UnitRange{Int64}}() # the subproofs should not be available to all
        output = conclusion = ""
        c = length(system)+1
        nbopb = length(system)
        open(string(path,'/',file,extention),"r"; lock = false) do f
            for ss in eachline(f)
                if length(ss)==0 continue end
                i = findfirst(x->x=='%',ss)
                if i !== nothing # there is a comment
                    if i<3 continue end # comment is at the start of the line, ignore the line
                    if ss[1]=='a'
                        # justifyable assertion needs hints that are in comments for the moment.
                        assertrecord[c] = ss[i+1:end]
                    end
                    ss = ss[1:i-1] end # remove the comment
                end
                st = split(ss,keepempty=false)
                if st[1][1]=='@'
                    ctrmap[st[1][2:end]] = c # keep track of constraint name
                    st = st[2:end] # remove the @label
                end #TODO I AM HERE
                type = st[1]
                eq = Eq([],0)
                if type == "u" || type == "rup"
                    eq = readeq(st,varmap,2:2:length(st)-4)     # can fail if space is missing omg
                    push!(systemlink,[-1])
                elseif type == "p" || type == "pol"
                    push!(systemlink,[-2])
                    eq = solvepol(st,system,systemlink[end],c,varmap,ctrmap,nbopb)
                    if !(length(eq.t)!=0 || eq.b!=0) printstyled("POL empty"; color=:red) end
                elseif type == "a"  # unchecked assumption
                    eq = readeq(st,varmap,2:2:length(st)-4)
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
                elseif type == "ia"
                    eq,l = readia(st,varmap,ctrmap,eq,c)
                    push!(systemlink,[-3,l])
                elseif type == "red"  
                    c = readred(system,systemlink,st,varmap,ctrmap,redwitness,c,f,prism)
                    eq = Eq([],0)
                elseif type == "sol" 
                    printstyled("SAT Not supported."; color=:red)
                    eq = Eq([Lit(0,true,1)],15) # just to add something to not break the id count
                elseif type == "soli" 
                    push!(systemlink,[-21])
                    eq = findbound(system,st,c,varmap,prism,obj,solirecord)
                elseif type == "solx"         # on ajoute la negation de la sol au probleme pour chercher d'autres solutions. jusqua contradiction finale. dans la preuve c.est juste des contraintes pour casser toutes les soloutions trouvees
                    push!(systemlink,[-20])
                    eq = solbreakingctr(system,st,c,varmap,prism)
                elseif type == "output"
                    output = replace(st[2],";"=>"")
                elseif type == "conclusion"
                    conclusion = replace(st[2],";"=>"")
                    if conclusion == "BOUNDS"
                        conclusion = ss
                        # printstyled("BOUNDS Not supported. "; color=:red)
                    elseif !isequal(system[end],Eq([],1)) && (conclusion == "SAT" || conclusion == "NONE")
                        printstyled("SAT Not supported.."; color=:red)
                    end
                elseif !(type in ["%","*","wiplvl","w","setlvl","#","f","d","del","end","pseudo-Boolean"])#,"de","co","en","ps"])
                    printstyled("unknown2: ",ss; color=:red)
                end
                if length(eq.t)!=0 || eq.b!=0 # the eq is not empty
                    normcoefeq(eq)
                    push!(system,eq)
                    c+=1
                end
            end
        end
        return system,systemlink,redwitness,solirecord,assertrecord,output,conclusion,version end

    mutable struct Red                      # w: witness. range: id range from beign to end of red. pgranges are the proof goals ranges.
        w::Vector{Lit}                      # each odd index is the variable and each next even is tha target (lit(0,0,-1) means constant 1 and 0 means constant 0)
        range::UnitRange{Int64}
        pgranges::Vector{UnitRange{Int64}} end

end; using .parser 



# ======================================= main code ======================================= #

if "profile" in ARGS
    throw("uncomment here to enable profiling")
    # using StatProfilerHTML
    # @profilehtml main()
else main() end