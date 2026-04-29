# This is a PB trimmer made to analyse proofs. If problem, ask arthur.pro.gontier@gmail.com
# julia GlasgowTrimnalyser.jl [options] [instance name or directory of instances]   options: atable sort rand clean veri profile
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
        rm.(filter(f -> endswith(f, ".out") || endswith(f, ".err"),readdir(proofs; join=true)))
        return
    elseif inst !== nothing 
        printabline(ins)
        trimnalyse(inst)
        return
    end
    println(tabhead)
    for ins in getinstancesfromdir(proofs)
        printabline(ins)
        t1,t2,t3 = trimnalyse(ins)
        t4,t5 = "verif" in ARGS ? verify(ins) : (-1,-1)
        printabline2(ins,t1,t2,t3,t4,t5)
    end
    println(tabfoot)
end
function getinstancesfromdir(proofs)
    list = onlyname.(filter(x -> ext(x)==opb && isfile(noext(x)*pbp), readdir(proofs, join=true)))
    if "rand" in ARGS
        shuffle!(list)
    elseif "sort" in ARGS
        sort!(list, by = x -> inssize(x))
    end
    println("%Found ", length(list), " instances in ", proofs)
    return list
end

function trimnalyse(ins)
    t1 = t2 = t3 = 0

    return t1,t2,t3
end
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
    return trunc(Int,t4),trunc(Int,t5)
end


# ======================================= plotting codes ======================================= #

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
    printpoints2Dlog(table,5,10,"grim SIZE","veri SIZE")
end
function maxvalue(table,a)
    m = 0
    for t in table
        if t[a]!==nothing
            if t[a]>m m=t[a] end
        end
    end
    return m
end
function printpoints2D(table,a,b,xlbl="",ylbl="")
    prefixtikz(maxvalue(table,a),maxvalue(table,b),xlbl,ylbl)
    for t in table
        if t[a]!==nothing &&t[b]!==nothing
            print(t[a],'/',t[b],',')
        end
    end
    println()
    postfixtikz()
end
function printpoints2Dlog(table,a,b,xlbl="",ylbl="")
    xlbl*=" (log)"; ylbl*=" (log)"
    prefixtikz(logsmooth(maxvalue(table,a)),logsmooth(maxvalue(table,b)),xlbl,ylbl)
    for t in table
        if t[a]!==nothing &&t[b]!==nothing
            print(logsmooth(t[a]),'/',logsmooth(t[b]),',')
        end
    end
    println()
    postfixtikz()
end
function logsmooth(a)
    return round(max(log10(a),0),sigdigits = 3)
end
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
    println("\\begin{tikzpicture}[scale=$scale, x=$xx cm, y=$yy cm]
  \\def\\xmin{0} \\def\\xmax{$mx} \\def\\ymin{0} \\def\\ymax{$my}
  \\draw[style=help lines, ystep=$ysteps, xstep=$xsteps] (\\xmin,\\ymin) grid (\\xmax,\\ymax);
  \\draw[->] (\\xmin,\\ymin) -- (\\xmax,\\ymin) node[above left] {$xlbl};
  \\draw[->] (\\xmin,\\ymin) -- (\\xmin,\\ymax) node[below right] {$ylbl};
  \\foreach \\x in {0,$xsteps,...,\\xmax} \\node at (\\x, \\ymin) [below] {\\x};
  \\foreach \\y in {0,$ysteps,...,\\xmax} \\node at (\\xmin,\\y) [left] {\\y};
 \\draw (\\xmin,\\ymin) -- (\\xmax,\\ymax) ;
 \\foreach \\x/\\y in{")
end
function postfixtikz()
    println("}\\draw (\\x,\\y) node[noeudver] {};
 \\end{tikzpicture}")
end

# ======================================= sugar fun ======================================= #
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
    return "\r\033["*carriage*"G"*s
end
function printabline(f)
    printgray("         &          &          &          &      (                   ) &      & ")
    printyellow(f)
    printgray(" \\\\\\hline")
    printcyan(leftcarriage(9,prettybytes(filesize(proofs*f*opb))))
    printcyan(leftcarriage(20,prettybytes(filesize(proofs*f*pbp))))
end
function printabline2(f,t1,t2,t3,t4,t5)
    printgreen(leftcarriage(31,prettybytes(filesize(proofs*f*opb*smol))))
    printgreen(leftcarriage(42,prettybytes(filesize(proofs*f*pbp*smol))))
    printgreen(leftcarriage(49,string(t1+t2+t3+max(0,t4))))
    printblue(leftcarriage(54,string(t1)))
    printgreen(leftcarriage(59,string(t2)))
    printblue(leftcarriage(64,string(t3)))
    printcyan(leftcarriage(69,string(t4)))
    printcyan(leftcarriage(78,string(t5)))
    println()
end
function prettybytes(b)
    if b>=10^9
        return string(trunc(Int,b/(10^9))," GB")
    elseif b>=10^6
        return string(trunc(Int,b/(10^6))," MB")
    elseif b>=10^3
        return string(trunc(Int,b/(10^3))," KB")
    else
        return  string(trunc(Int,b)," B")
    end
end 


# ======================================= main code ======================================= #

if "profile" in ARGS
    throw("uncomment here to enable profiling")
    # using StatProfilerHTML
    # @profilehtml main()
else main()
end