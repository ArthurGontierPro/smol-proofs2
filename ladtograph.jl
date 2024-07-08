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
        l = 0
        for ss in eachline(f)
            l+=1
            st = split(ss,' ')[2:end] # le premier chiffre est le degret du noeud
            removespaces(st)
            for sn in st
                n = parse(Int,sn)
                if n>0
                    add_edge!(g, l, n)
                end
            end
        end
    end
    return g
end

function csvtograph(path,file)
    cd()
    g = SimpleGraph()
    open(string(path,'/',file),"r"; lock = false) do f
        for ss in eachline(f)
            st = split(ss,',')
            v1 = parse(Int,st[1])
            v2 = parse(Int,st[2])
            n = size(g, 1)
            m = max(v1,v2)
            if m > n 
                add_vertices!(g, m-n)
            end
            add_edge!(g, v1, v2)
        end
    end
    return g
end