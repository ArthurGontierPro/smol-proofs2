function plotresultstablenature(file)
    table = Vector{Vector{Any}}()
    legende = Vector{String}()
    n = 0
    pfile = string(pwd(),'/',file)
    println(pfile)
    open(pfile, "r") do f
        firstline = readline(f)
        legende = split(firstline,' ')
        n = length(legende)
        for line in eachline(f)
            st = split(line,' ')
            t = Vector{Any}()
            for i in 1:n
                push!(t,tryparse(Float64,st[i]))
            end
            push!(table,t)
        end
    end
    printpoints2D(table,2,8,"elab")
    printpoints2D(table,5,11,"verif")
    printpoints2Dlog(table,2,8,"elab")
    printpoints2Dlog(table,5,11,"verif")
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
function printpoints2D(table,a,b,title)
    prefixtikz(maxvalue(table,a),maxvalue(table,b),title,title)
    for t in table 
        if t[a]!==nothing &&t[b]!==nothing
            print(t[a],'/',t[b],',')
        end
    end
    println()
    postfixtikz()
end
function printpoints2Dlog(table,a,b,title)
    title = string(title," (log)")
    prefixtikz(logsmooth(maxvalue(table,a)),logsmooth(maxvalue(table,b)),title,title)
    for t in table 
        if t[a]!==nothing &&t[b]!==nothing
            print(
                logsmooth(t[a]),'/',
                logsmooth(t[b]),',')
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
  \\draw[->] (\\xmin,\\ymin) -- (\\xmin,\\ymax) node[below right] {verif $ylbl};
  \\foreach \\x in {0,$xsteps,...,\\xmax} \\node at (\\x, \\ymin) [below] {\\x};
  \\foreach \\y in {0,$ysteps,...,\\xmax} \\node at (\\xmin,\\y) [left] {\\y};
\\draw (\\xmin,\\ymin) -- (\\xmax,\\ymax) ;
\\foreach \\x/\\y in{")
end
function postfixtikz()
println("}\\draw (\\x,\\y) node[noeudver,fill opacity=0.75,scale=0.3] {}; 
\\end{tikzpicture}")
end
plotresultstablenature(ARGS[1])