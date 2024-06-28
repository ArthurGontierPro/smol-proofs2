using Graphs,GraphPlot,Compose,Cairo
function removespaces(st)
    r = findall(x->x=="",st)
    deleteat!(st,r)
end
function ladtograph(path,file)
    cd()
    g = SimpleGraph()
    open(string(path,'/',file),"r"; lock = false) do f
        s = readline(f)
        n = parse(Int,s)
        add_vertices!(g,n)
        g = SimpleGraph(n,0)
        l = 0
        for ss in eachline(f)
            l+=1
            st = split(ss,' ')
            removespaces(st)
            for sn in st
                n = parse(Int,sn)
                add_edge!(g, l, n)
            end
        end
    end
    return g
end