
#=    Instances managements    =#

function okinstancelist()
    type = "LV"
    cd()
    list = cd(readdir, proofs)
    # list = [s[1:end-4] for s in list if s[end-3:end]==".opb" && s[1:3]=="bio"]
    list = [s[1:end-4] for s in list if s[end-3:end]==".opb" && s[1:3]=="LVg"]
    list = [s for s in list if isfile(string(proofs,"/",s,extention))]
    list = [s for s in list if read(`tail -n 1 $proofs/$s$extention`,String) == "end pseudo-Boolean proof\n"]
    list = [s for s in list if read(`tail -n 2 $proofs/$s$extention`,String)[1:14] != "conclusion SAT"]
    stats = [stat(string(path,"/",file,".opb")).size + stat(string(proofs,"/",file,extention)).size for file in list]

    println(list)
    p = sortperm(stats)
    # listm = [list[i] for i in eachindex(list) if stats[i] > 1_000_000]
    open(string(proofs,"/a",type,"list.jl"),"w") do f
        write(f,string("const ",type,"list = [\"",list[1],"\""))
        for i in 2:length(list) 
            write(f,string(",\"",list[i],"\""))
        end
        write(f,string("]\n"))
        write(f,string("const ",type,"stats = [",stats[1]))
        for i in 2:length(list) 
            write(f,string(",",stats[i]))
        end
        write(f,string("]\n"))
    end
end
function solve(ins,pathpat,pattern,pathtar,target,format,minsize=2_000_000,timeout=1,remake=false)
    if remake || !isfile(string(proofs,"/",ins,".opb")) || !isfile(string(proofs,"/",ins,extention)) || 
            length(read(`tail -n 1 $proofs/$ins$extention`,String)) < 24 ||
            read(`tail -n 1 $proofs/$ins$extention`,String)[1:24] != "end pseudo-Boolean proof"
        print(ins,' ')
        t = @elapsed begin
            # p = run(pipeline(`timeout $timeout ./$solver --prove $proofs/$ins --no-supplementals --no-clique-detection --format $format $pathpat/$pattern $pathtar/$target`, devnull),wait=false); wait(p)
            p = run(pipeline(`timeout $timeout ./$solver --prove $proofs/$ins --no-clique-detection --format $format $pathpat/$pattern $pathtar/$target`, devnull),wait=false); wait(p)
        end
        t+=0.01
        ok = false
        print(prettytime(t))
        if t>timeout
            printstyled(" timeout "; color = :red)
        elseif read(`tail -n 2 $proofs/$ins$extention`,String)[1:14] == "conclusion SAT"
            printstyled(" sat     "; color = 166)
        elseif minsize > stat(string(proofs,"/",ins,extention)).size            
            printstyled(" toosmal "; color = :yellow)
        else printstyled(" OK      "; color = :green)
            ok = true
            # g = ladtograph(pathpat,pattern)
            # draw(PNG(string(proofs,"/aimg/graphs/",ins,pattern[1:3],".png"), 16cm, 16cm), gplot(g))
            # g = ladtograph(pathtar,target)
            # draw(PNG(string(proofs,"/aimg/graphs/",ins,target[1:3],".png"), 16cm, 16cm), gplot(g))
        end
        println()
        if !ok
            run(`rm -f $proofs/$ins$extention`)
            run(`rm -f $proofs/$ins.opb`)
        end
    end
end
function run_bio_solver()
    path = string(benchs,"/biochemicalReactions")
    cd()
    graphs = cd(readdir, path)
    n = length(graphs)
    for target in graphs[1:end], pattern in graphs[1:end]
        # target = graphs[rand(1:n)]
        # pattern = graphs[rand(1:n)]
        if pattern != target
            ins = string("bio",pattern[1:end-4],target[1:end-4])
            solve(ins,path,pattern,path,target,"lad")
        end
    end
end
function run_si_solver() # all sat or timeout
    sipath = string(benchs,"/si")
    cd()
    inst = cd(readdir, string(sipath))
    for ins in inst
        inst2 = cd(readdir, string(sipath,"/",ins))
        for ins2 in inst2
            solve(ins2,string(sipath,'/',ins,'/',ins2,),"pattern",string(sipath,'/',ins,'/',ins2),"target","lad")
        end
    end
end
function run_LV_solver()
    path = string(benchs,"/LV")
    cd()
    for i in 51:112
        for j in 2:50
            target = string('g',i)
            pattern = string('g',j)
            ins = string("LV",pattern,target)
            if ins in LVlist
            solve(ins,path,pattern,path,target,"lad",100000,1,true)
            end
        end
    end
end

#=    Stat prints   =#


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
function roundt(t,d)
    for i in eachindex(t)
        t[i] = round(t[i],digits = d)
    end
    return t
end
function delindividualist(g)
    i = findfirst(v->degree(g,v)==0,vertices(g))
    while !(i === nothing)
        rem_vertex!(g, i)
        i = findfirst(v->degree(g,v)==0,vertices(g))
    end
end
function makeg2win(g)
    n = nv(g)
    g2 = SimpleGraph(n,0)
    for i in vertices(g)
        for j in neighbors(g, i)
            for k in neighbors(g, j)
                add_edge!(g2,i,k)
            end
        end
    end
    return g2
end 
function add_nei(deb,cur,l,g,A)
    if k == 0 A[deb,cur] +=1 
    else
        for nei in neighbors(g, cur)
            add_nei(deb,nei,l-1,g,A)
        end
    end
end
function makegkwin(g,k) return makegkwin(g,2,k) end
function makegkwin(g,l,k) # l length of path (default 2); k number of paths
    n = nv(g)
    A = zeros(Int,n,n)
    gg = [SimpleGraph(n,0) for _ in 1:k]
    for i in vertices(g)
        add_nei(i,i,l,g,A)
    end
    for occ in 1:k
        for i in 1:n
            for j in i:n
                if A[i,j]>=occ
                    add_edge!(gg[occ],i,j)
                end
            end
        end
    end
    return gg
end 
function printcom(file,system,invsys,cone,com)
#print the type of the trimed constraints from the coms of the solver and the adjacency graphs.
    names = [
        "backtrack", "backtrackbin", "backtrackbincolor", "disconnected",
        "degre", "hall", "nds", "nogood", "loops", "fail", "colorbound",
        "adjacencyhack", "adjacencydist1", "adjacencydist2", "adjacencydist3",
        "adjacency", "adjacency0", "adjacency1", "adjacency2", "adjacency3", "adjacency4"]
    n = length(names)
    og = zeros(Int,n)
    sm = zeros(Int,n)
    # ogg =  SimpleGraph()
    # smg =  SimpleGraph()
    ogd = Dict{Int,SimpleGraph{Int}}()
    smd = Dict{Int,SimpleGraph{Int}}()
    lastadj = 0
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
            if type[1:3] == "adj"
                lastadj = i
                v1 = parse(Int,st[2])
                v2 = parse(Int,st[3])
                idg = parse(Int,st[4])
                if !haskey(ogd,idg) ogd[idg] = SimpleGraph() end
                if !haskey(smd,idg) smd[idg] = SimpleGraph() end
                ogg = ogd[idg]
                smg = smd[idg]
                n = size(ogg, 1)
                m = max(v1,v2)
                if m > n 
                    add_vertices!(ogg, m-n)
                    add_vertices!(smg, m-n)
                end
                add_edge!(ogg, v1, v2)
                if cone[i] add_edge!(smg, v1, v2) end
            end
        end
    end
    p = sortperm(names)
    for i in p
        if og[i]>0
            col =  sm[i]==og[i] ? 3 : sm[i]==0 ? 1 : 2
            printstyled(names[i]," ",sm[i],"/",og[i],"\n"; color = col)
        end
    end
    # println(lastadj)
    for i in eachindex(ogd)
        ogg = ogd[i]
        delindividualist(ogg)
        draw(PNG(string(proofs,"/aimg/",file,"-g",i,".png"), 16cm, 16cm), gplot(ogg))
    end
    for i in eachindex(smd)
        smg = smd[i]
        delindividualist(smg)
        if nv(smg)>1
            draw(PNG(string(proofs,"/aimg/",file,"-g",i,".smol.png"), 16cm, 16cm), gplot(smg))
        end
    end
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
function printrepartition(ins,t1,t2)
    println("\\begin{tikzpicture}[xscale=0.5,font=\\sffamily]\n\\node[right] at (0,1.5) {",ins,"};")
    print("\\foreach \\x/\\y in{")
    for i in 1:length(t1)-1
        print(i,"/",t1[i],',')
    end
    print(length(t1),"/",t1[end])
    println("} {\\fill[color=black!\\y] (\\x,0) rectangle (\\x+1,1);\\node at (\\x+0.5,0.5) {\\y};} \\draw (1,0) grid (102,1);")
    print("\\foreach \\x/\\y in{")
    for i in 1:length(t2)-1
        print(i,"/",t2[i],',')
    end
    print(length(t2),"/",t2[end])
    println("} {\\fill[color=black!\\y] (\\x,-1) rectangle (\\x+1,0);\\node at (\\x+0.5,-0.5) {\\y};} \\draw (1,-1) grid (102,0);")
    println("\\end{tikzpicture}") 
end
function readrepartition()
    cko = 0
    ckp = 0
    s = 0
    t1 = [0 for i in 1:101]
    t2 = [0 for i in 1:101]
    Σ1 = [0 for i in 1:101]
    Σ2 = [0 for i in 1:101]
    nb1 = 0
    nb2 = 0
    cd()
    println("\\documentclass[tikz,border=5mm]{standalone}\n\\begin{document}")
    open(string(proofs,'/',"arepartition"),"r"; lock = false) do f
        for ss in eachline(f)
            if ss!="" && ss[1] != ' ' && ss[1] != '.'
                st  = split(ss,' ')
                cko = parse(Int,st[end-1][2:end])
                ckp = parse(Int,st[end])
                ins = string(st[1],' ',cko,' ',ckp)
                if ckp>10
                    ss = readline(f)
                    ss = replace(ss,'.'=>" 0")
                    st = split(ss,' ')
                    removespaces(st)
                    for i in 1:101
                        v =  parse(Int,st[i])
                        t1[i] = v
                        Σ1[i] +=v
                    end
                    nb1 += 1
                    ss = readline(f)
                    ss = replace(ss,'.'=>" 0")
                    st = split(ss,' ')
                    removespaces(st)
                    for i in 1:101
                        v =  parse(Int,st[i])
                        t2[i] = v
                        Σ2[i] +=v
                    end
                    nb2 += 1
                    printrepartition(ins,t1,t2)
                end
            end
        end
    end
    ins =  string("Mean ",nb1,' ',nb2)
    st = Σ1./nb1
    for i in 1:101
        v =  round(Int,st[i])
        t1[i] = v
        nb1 += 1
    end
    st = Σ2./nb2
    for i in 1:101
        v =  round(Int,st[i])
        t2[i] = v
        nb2 += 1
    end
    printrepartition(ins,t1,t2)
    println("\\end{document}")
    # return Σ./nb
end

