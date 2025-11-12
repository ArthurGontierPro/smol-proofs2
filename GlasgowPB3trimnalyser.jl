#= This file has the following sections
    Main, Trimmer, Justifyer, Printer, and Parser
Command to run trim allinstances in the current directory is:
    julia GlasgowPB3trimnalyser.jl
You can specify an instance and a path and have the following options.
    show        to have the html colored prettyprint
    adj         to ha the adjacency matrix print in html
    noveripb    to not make the veripb comparison on the instance and the small one
Example with options:
    julia GlasgowPB3trimnalyser.jl noveripb path instance show adj tl 600

cargo r -- /home/arthur_gla/veriPB/proofs/small/linear_equality_test.opb out.pbp --trace

julia GlasgowPB3trimnalyser.jl 
verif brim path instance
=#
using Random,DataStructures


# ================ Main ================


struct Options
    ins::String     # one instance name (leave blank if you want all instances)
    insid::Int      # instance id (for fast testing from an instance list)
    proofs::String  # directory containing instances
    pbopath::String # directory containing veripb 3.0(rust)
    brimpath::String # directory containing veripb 3.0(rust) trimmer
    sort::Bool      # sort the instances by size
    veripb::Bool    # veripb comparison (need to give pboxide path pbopath in parseargs)
    brim::Bool      # trimmer in pboxide by Berhan
    grim::Bool      # trimmer in julia by Arthur
    trace::Bool     # veripb trace
    cshow::Bool     # prettyprint of the proof in html
    adjm::Bool      # adj matrix representation of the cone
    order::Bool     # output the variable usage rates in order
    smartrup::Bool  # use smart rup (conflict analysis) in the trimmer
    LPsimplif::Bool # simplificaiton of pol by LP (need more work)
    timelimit::Int  # time limit (one month default)
    profile::Bool  # make a flamegraph profile in html
    keeplabels::Bool # keep the labels in the trimmed proof (if they exist)
    withsmol::Bool # also trim smol
end
function parseargs(args)
    ins = ""
    proofs = pwd()*"/"
    # proofs = "/home/arthur_gla/veriPB/subgraphsolver/proofs/"
    # proofs = "/home/arthur_gla/veriPB/subgraphsolver/proofsthatbreaksveriPBtrimheuristics/"
    # proofs = "/home/arthur_gla/veriPB/trimmertests/veripb-dev-feature-trimmer-bench/benches/solver_instances/gss/"
    # proofs = "/home/arthur_gla/veriPB/subgraphsolver/nolabelsproofs3/"
    # proofs = "/scratch/matthew/huub3/"
    # proofs = "/scratch/arthur/proofs"
    # proofs = "/home/arthur_gla/veriPB/proofs/small/" # not 3.0 syntax yet
    proofs = "/users/grad/arthur/proofs/"
    pbopath = "/home/arthur_gla/veriPB/subgraphsolver/veripb-dev"
    # pbopath = "/users/grad/arthur/pboxide-dev"
    # brimpath = "/home/arthur_gla/veriPB/subgraphsolver/ftrimer/veripb-dev" # Berhan trimmer for testing.
    brimpath = "/users/grad/arthur/ftrimer/veripb-dev" # Berhan trimmer for testing.
    insid = 0
    tl = 2629800 # 1 month
    # tl = 2 # 1 month
    # ins = "circuit_prune_root_test"
    sort = true
    veripb = false
    brim = false # use brim trimmer
    grim = true # use grim trimmer
    trace = false
    cshow = false
    adjm = false
    order = false
    smartrup = false # use smart rup (conflict analysis)
    LPsimplif = false
    profile = false
    keeplabels = true
    withsmol = false
    for (i, arg) in enumerate(args)
        if arg == "cd" cd() end # hack to add cd in paths
        if arg in ["verif"] veripb = true end
        if arg in ["brim","btrim"] brim = true end
        if arg in ["nogrim"] grim = false end
        if arg in ["verif","veripb"] veripb = true end
        if arg in ["LPsimplif","lp"] LPsimplif = true end
        if arg in ["nosort","ns"] sort = false end
        if arg in ["adj","adjm","adjmat"] adjm = true end
        if arg in ["varorder","order","vo"] order = true end
        if arg in ["cshow","show","cs","ciaran_show","ciaranshow"] cshow = true end
        if arg in ["--trace","-trace","trace","-tr","tr"] trace = true end
        if arg in ["profile","flamegraph","fgp","fg","prof","profile"] profile = true end
        if arg in ["timelimit","tl"] tl = parse(Int, args[i+1]) end
        if arg in ["insid","ins"] insid = parse(Int, args[i+1]) end
        if arg in ["nogrim"] grim = false end
        if arg in ["withsmol"] withsmol = true end
        if arg == "smart" smartrup = true end
        if ispath(arg)&&isdir(arg) 
            if arg[end]!='/' 
                proofs = arg*'/'
            else proofs = arg end
        end
        if (ispath(arg)||ispath(arg*".opb"))&&(isfile(arg)||isfile(arg*".opb"))
            if (tmp = findlast('/',arg))===nothing
                ins = arg
                proofs=""
            else 
                ins = arg[tmp+1:end]
                proofs = arg[1:tmp-1]
            end
        end
    end
    for (i, arg) in enumerate(args)
        if isfile(proofs*arg)||isfile(proofs*arg*".opb") 
            ins = arg
            proofs = proofs[1:end-1]
        elseif isfile(proofs*"/"*arg)||isfile(proofs*"/"*arg*".opb") 
            ins = arg
        end
    end
    if split(ins,'.')[end] in ["opb","pbp"] ins = ins[1:end-4] end
    if proofs!="" print("Dir:$proofs ") end
    if ins!="" print("Ins:$ins ") end
    return Options(ins,insid,proofs,pbopath,brimpath,sort,veripb,brim,grim,trace,cshow,adjm,order,smartrup,LPsimplif,tl,profile,keeplabels,withsmol)
end
const CONFIG = parseargs(ARGS)
const proofs = CONFIG.proofs
const pbopath = CONFIG.pbopath
const SIPgraphpath = "/home/arthur_gla/veriPB/newSIPbenchmarks/"
const visualisationpath = "/home/arthur_gla/veriPB/subgraphsolver/visualisations/"
const tl = CONFIG.timelimit
const extention = ".pbp"
const version = "3.0"
mutable struct Lit
    coef::Int
    sign::Bool
    var::Int
end
mutable struct Eq
    t::Vector{Lit}
    b::Int
end
mutable struct Red                      # w: witness. range: id range from beign to end of red. pgranges are the proof goals ranges.
    w::Vector{Lit}                      # each odd index is the variable and each next even is tha target (lit(0,0,-1) means constant 1 and 0 means constant 0)
    range::UnitRange{Int64}
    pgranges::Vector{UnitRange{Int64}}
end
function main() # detect files (can sort them by size) and call the trimmers
    if "atable" in ARGS
        plotresultstable()
    else
        if CONFIG.grim

        end
        if CONFIG.ins != ""
            println()
            println("\\begin{tabular}{|c|ccc|ccc|}\\hline & sizes &  &  & times (s) &  & \\\\\\hline\nInstance & veriPB & btrim & gtrim & veriPB & btrim & gtrim (parse trim write verif)  \\\\\\hline")
            # print(" "^29);printstyled(CONFIG.ins,"  "; color = :yellow)
            runtrimmers(CONFIG.ins)
        else
            list = cd(readdir, proofs)
            list = [s for s in list if length(s)>5]
            list = [s[1:end-4] for s in list if s[end-3:end]==".opb" && (CONFIG.withsmol || s[1:5]!="smol.")]
            # a=[println(proofs*s*extention,isfile(proofs*s*extention)) for s in list]
            list = [s for s in list if isfile(proofs*s*extention)]
            p = [i for i in eachindex(list)]
            if CONFIG.sort
                stats = [stat(proofs*file*extention).size+ (if isfile(proofs*file*".opb") stat(proofs*file*".opb").size else 0 end) for file in list]
                p = sortperm(stats)
            else 
                rng = MersenneTwister(1234)
                p = randperm(rng,length(list)) # randomize the order of the instances
            end
            println(list[p])
            println("\\begin{tabular}{|c|ccc|ccc|}\\hline& sizes &  &  & times (s) &  & \\\\\\hline\nInstance & veriPB & btrim & gtrim & veriPB & btrim & gtrim (parse trim write verif)  \\\\\\hline")
            if CONFIG.insid>0
                ins = list[p[CONFIG.insid]]
                # print(" "^29);print(CONFIG.insid,' ');printstyled(ins,"  "; color = :yellow)
                runtrimmers(ins)
            else for i in eachindex(list)
            # else for i in 1:30
                ins = list[p[i]]
                # print(" "^29);print(i,' ');printstyled(ins,"  "; color = :yellow)
                runtrimmers(ins)
            end end
        end
        println("\\end{tabular}\\\\\n")
    end
end
function runtrimmers(ins)
    v1 = v2 = v3 = st = tri = tms = twc =0
    so = stat(string(proofs,"/",ins,".opb")).size + stat(string(proofs,"/",ins,extention)).size
    printstyled(ins; color = :yellow)
    d = length(ins)
    #instance & sizes (initial brimmed grimmed) & times (initial brimmed trimmed(parse trim write verif)) ///hline
    printstyled(" &          &          &          &      &      &      (                   ) \\\\\\hline"; color = :grey)
    printstyled("\r\033[",d+4,"G",prettybytes(so))
    tvp = @elapsed begin if CONFIG.veripb
        # v1 = ""
        v1 = verifier("$proofs/$ins.opb","$proofs/$ins$extention")
    end end
    printstyled("\r\033[",d+37,"G",prettytime(tvp); color = :blue)

    tvb = @elapsed begin if CONFIG.brim 
        try
        v3 = runbrimmer("$proofs/$ins.opb","$proofs/$ins$extention") 
        catch e
            printstyled("\nBrim trimmer failed on $ins:\n"; color = :red)
        end
    end end
    sb = stat(string(proofs,"/",ins,".opb")).size + stat(string(CONFIG.brimpath,"/out.tmp")).size
    printstyled("\r\033[",d+15,"G",if CONFIG.brim prettybytes(sb) else "" end)
    printstyled("\r\033[",d+37+7,"G",prettytime(tvb); color = :blue)

    if CONFIG.grim
        tri,tms,twc = rungrimmer(ins)
        st = stat(string(proofs,"/smol.",ins,".opb")).size + stat(string(proofs,"/smol.",ins,extention)).size
    end
    printstyled("\r\033[",d+15+11,"G",if CONFIG.grim prettybytes(st) else "" end)
    printstyled("\r\033[",d+37+7+7+6,"G",prettytime(tri); color = :cyan)
    printstyled("\r\033[",d+37+7+7+6+5,"G",prettytime(tms); color = :green)
    printstyled("\r\033[",d+37+7+7+6+10,"G",prettytime(twc); color = :cyan)

    tvs = @elapsed begin if CONFIG.veripb && CONFIG.grim
        v2 = verifier("$proofs/smol.$ins.opb","$proofs/smol.$ins$extention")
    end end
    printstyled("\r\033[",d+37+7+7,"G",prettytime(tvs+tri+tms+twc); color = :blue)
    printstyled("\r\033[",d+37+7+7+7+14,"G",prettytime(tvs),"\n"; color = :blue)
    # printstyled("\r",prettytime(tvs),'\n'; color = :blue)
    if !CONFIG.veripb tvp = tvs = 0.1 end
    if ins[1] == 'b'
        t = [roundt([parse(Float64,ins[end-5:end-3]),parse(Float64,ins[end-2:end]),
        so,sb,st,tvp,tvb,tvs+tri+tms+twc,tri,tms,twc,tvs],3)]
        # so,st,st/so,tvp,tvs,tvs/tvp,tms,twc,tri],3)]
    elseif ins[1] == 'L'
        t = [roundt([parse(Float64,split(ins,'g')[2]),parse(Float64,split(ins,'g')[3]),
        so,sb,st,tvp,tvb,tvs+tri+tms+twc,tri,tms,twc,tvs],3)]
        # so,st,st/so,tvp,tvs,tvs/tvp,tms,twc,tri],3)]
    else
        t = [roundt([0.0,0.0,
        so,sb,st,tvp,tvb,tvs+tri+tms+twc,tri,tms,twc,tvs],3)]
        # so,st,st/so,tvp,tvs,tvs/tvp,tms,twc,tri],3)]
    end
    # printtabular(t)
    open(string(proofs,"/atable"), "a") do f
        write(f,string(t[1],",\n"))
    end
    if CONFIG.veripb && v1!=v2
        # printstyled("\nTraces are not identical\n"; color = :red)
        open(string(proofs,"/afailedtrims"), "a") do f
            write(f,string(ins," \n"))
        end
    end
end
function verifier(formule,preuve)
    cd();cd(CONFIG.pbopath)
    v1 = 0
    r = "--release"   #run parameters (release is basically full compile optimizations)
    r = "" 
    if CONFIG.trace
        # println("timeout $tl cargo r -- --trace $formule $preuve ")
        v1 = run(`timeout $tl cargo r -- --trace $formule $preuve`)
        # v1 = run(`timeout $tl cargo r -- --trace $formule $preuve --elaborate out.tmp`)
    else
        redirect_stdio(stdout = devnull,stderr = devnull) do
        v1 =read(`timeout $tl cargo r -- $formule $preuve`)
        # v1 =read(`timeout $tl cargo r -- $formule $preuve --elaborate out.tmp`)
        end
    end
    return v1
end
function runbrimmer(formule,preuve)
    cd();cd(CONFIG.brimpath)
    v1 = 0
    r = "--release"   #run parameters (release is basically full compile optimizations)
    r = ""
    if CONFIG.trace
        # v1 = run(`timeout $tl cargo r $r -- --trim --trace $formule $preuve --elaborate out.tmp`)
        v1 = run(`timeout $tl cargo r -r -- trim $formule $preuve --elaborate out.tmp`)
        # v1 = run(`timeout $tl cargo r -- trim $formule $preuve --elaborate out.tmp --use-trimming-heuristic`)
        # v1 = run(`sudo timeout $tl samply record cargo r $r -- --trace --trim $formule $preuve --elaborate out.tmp `)
    else
        redirect_stdio(stdout = devnull,stderr = devnull) do
        # v1 =read(`timeout $tl cargo r $r -- --trim $formule $preuve --elaborate out.tmp`)
        v1 =read(`timeout $tl cargo r -r -- trim $formule $preuve --elaborate out.tmp`)
        # v1 =read(`timeout $tl cargo r -- trim $formule $preuve --elaborate out.tmp --use-trimming-heuristic`)
        # v1 =read(`sudo timeout $tl samply record cargo r $r -- --trim $formule $preuve --elaborate out.tmp `)
        end
    end
    return v1
end
function rungrimmer(file)
    tri = @elapsed begin
        system,systemlink,redwitness,solirecord,assertrecord,nbopb,varmap,ctrmap,output,conclusion,version,
        obj = readinstance(proofs,file)
    end
    # printstyled("\r"," "^18,prettytime(tri),"  "; color = :cyan)
    normcoefsystem(system)
    invsys = getinvsys(system,systemlink,varmap)
    prism = availableranges(redwitness)
    if conclusion in ["SAT","NONE"] && !isequal(system[end],Eq([],1)) return 0,0,0 end
    tms = @elapsed begin
        cone,conelits = makesmol(system,invsys,varmap,systemlink,nbopb,prism,redwitness,conclusion,obj)
    end
    # printstyled("\r"," "^12,prettytime(tms),"  "; color = :green)
    invctrmap = Dict(ctrmap[k] => k for k in keys(ctrmap)) # reverse the ctrmap (may be inneficient)
    # for (i,_) in conelits # nullify the conelits
    #     conelits[i] = Set([l.var for l in system[i].t]) # we reverse the lits to use the varmap
    # end
    # for i in systemlink[end][2:end] # prints out the used labels in the antecedants of the last rup
    #     print(invctrmap[i]," ")
    # end

    twc = @elapsed begin
        varmap = Dict(varmap[k] => k for k in keys(varmap)) # reverse the varmap (may be inneficient)
        writeconedel(proofs,file,version,system,cone,conelits,systemlink,redwitness,solirecord,assertrecord,nbopb,
                    varmap,ctrmap,invctrmap,output,conclusion,obj,prism)
    end
    # printstyled("\r"," "^6,prettytime(twc),"  "; color = :cyan)
    succ = Vector{Vector{Int}}(undef,length(system))
    invlink(systemlink,succ,cone,nbopb)
    index = zeros(Int,length(system)) # map the old indexes to the new ones
    findallindexfirst(index,cone)
    if CONFIG.adjm
        # showadjacencymatrixsimple(file,cone,index,systemlink,succ,nbopb)
        showadjacencymatrix(file,cone,index,systemlink,succ,nbopb)
    end
    # conelits = Dict{Int,Set{Int}}() # we nullify the conelits to compare stuff
    if CONFIG.order
        printorder(file,cone,invsys,varmap)
    end
    if CONFIG.cshow
        comparegraphs(file,system,nbopb,cone,conelits,varmap,ctrmap,invctrmap)
        showctrusage()
        # ciaranshow(proofs,file,version,system,cone,index,systemlink,succ,redwitness,nbopb,varmap,output,conclusion,obj,prism,varocc)
    end
    return tri,tms,twc
end


# ================ Trimmer ================


function makesmol(system,invsys,varmap,systemlink,nbopb,prism,redwitness,conclusion,obj)
    n = length(system)
    antecedants = zeros(Bool,n)
    assi = zeros(Int8,length(varmap))
    cone = zeros(Bool,n)
    conelits = Dict{Int,Set{Int}}() # for the lits that we want to keep (works with conflict analysis)
    front = zeros(Bool,n)
    contradictions = findall(x->length(x.t)==0,system)
    firstcontradiction = 0
    for contradiction in contradictions
        if !inprism(contradiction,prism)
            firstcontradiction = contradiction
            break
        end
    end
    if firstcontradiction == 0
        if conclusion == "UNSAT"
            printstyled("\nUNSAT contradiction not found in the system\n"; color = :red)
            return cone
        else
            st = split(conclusion,keepempty=false)
            if st[2] == "BOUNDS"
                conclusion = "BOUNDS"
                lowerbound = parse(Int,st[3])
                for i in eachindex(system)
                    if isobjlb(system[i],obj,lowerbound)
                        firstcontradiction = i
                        break;
                    end
                end
            end
        end
    end
    cone[firstcontradiction] = true
    if systemlink[firstcontradiction-nbopb][1] == -2         # pol case
        fixfront(front,systemlink[firstcontradiction-nbopb])
    else
        if conclusion=="UNSAT" || conclusion=="NONE"
            upquebit(system,invsys,assi,front,prism,conelits)
            # assi.=0
            # upquebitrestrained(system,invsys,assi,front,prism)
            # assi.=0 ; upquebitrestrainedconelits(system,invsys,assi,front,prism,conelits)
            # print("\r\033[110G ",sum(front))
            #  println(findall(front))
        elseif conclusion == "BOUNDS"
            begin
            if !rup(system,invsys,front,firstcontradiction,assi,front,cone,prism,0:0)
                println("\n",firstcontradiction," s=",slack(reverse(system[firstcontradiction]),assi))
                printeq(system[firstcontradiction-nbopb])
                printstyled(" initial rup to look for bound contradiction failed \n"; color = :red)
            end end
        end
        # println("  init : ",sum(front))#,findall(front)
        append!(systemlink[firstcontradiction-nbopb],findall(front))
        # printstyled(findall(front); color = :green)
    end
    red = Red([],0:0,[]);
    newpfgl = true
    pfgl = Vector{UnitRange{Int64}}()
    d = 120 #decalage du chariot
    while newpfgl # restart if new frontless proofgoals are needed.
        newpfgl = false
        while true in front
            i = findlast(front)
            front[i] = false
            # if istrivial(system[i],conelits,i)
            #     printstyled(" $i is trivial "; color = :green)
            #     printeqconelit(system[i],conelits[i])
            # end
            if !cone[i] # && !istrivial(system[i],conelits,i) # pol weakening backpropagation may have created trivial equations.
                # print("\r\033[$(d)G$i ")
                cone[i] = true
                if i>nbopb
                    tlink = systemlink[i-nbopb][1]
                    if tlink == -1                      # u statement 
                        antecedants .=false ; assi.=0
                        if rup(system,invsys,antecedants,i,assi,front,cone,conelits,prism,0:0)
                            # assi.=false; ruprestrained(system,invsys,antecedants,i,assi,front,cone,conelits,prism,0:0)
                            # assi.=false; ruprestrainedconelits(system,invsys,antecedants,i,assi,front,cone,conelits,prism,0:0)
                            antecedants[i] = false
                            append!(systemlink[i-nbopb],findall(antecedants))
                            fixfront(front,antecedants)
                        else
                            println("\n",i," s=",slack(reverse(system[i]),assi))
                            println(systemlink[i-nbopb])
                            printeq(system[i])
                            printstyled(" rup failed \n"; color = :red)
                            return cone
                        end
                    elseif tlink >= -3 || (tlink == -30 && length(systemlink[i-nbopb])>1)   # pol and ia statements and unchecked assertions without rup
                        antecedants .= false
                        fixante(systemlink,antecedants,i-nbopb)
                        fixconelits(conelits,system,i,antecedants,systemlink[i-nbopb])
                        removetrivialantecedants(system,antecedants,conelits,systemlink[i-nbopb],i)                        # enlever les antecedants triviaux de la formules
                        fixfront(front,antecedants)
                    elseif tlink == -10                 # (end of subproof)
                        red = redwitness[i]
                        front[red.range.start] = true
                        for subr in red.pgranges
                            if systemlink[subr.start-nbopb] == -8 && !(front[subr.start]||cone[subr.start])
                                push!(pfgl,subr)
                            else
                                front[subr.start] = true
                                front[subr.stop] = true
                            end
                        end
                    elseif tlink == -5                  # subproof rup
                        subran = findfirst(x->i in x,red.pgranges)
                        antecedants .=false ; assi.=0
                        if rup(system,invsys,antecedants,i,assi,front,cone,prism,red.pgranges[subran])
                            antecedants[i] = false
                            append!(systemlink[i-nbopb],findall(antecedants))
                            fixfront(front,antecedants) 
                        else printstyled("\n subproof rup failed \n"; color = :red)
                        end
                    elseif tlink == -6 || tlink == -8   # subproof pol and proofgoal of a previous eq
                        antecedants .= false
                        fixante(systemlink,antecedants,i-nbopb)
                        fixfront(front,antecedants)
                    elseif tlink == -7
                    end
                end
            end
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
    print("\r\033[$(d)G  ")
    # print("\033[K\033[A                   ")  # Efface la ligne et remonte d'une ligne
    fixredsystemlink(systemlink,cone,prism,nbopb)
    # printeqlink(935,system,systemlink)
    # ids = keys(conelits)
    # p = sortperm(ids)
    # sort!(conelits)
    # for (id,conelit) in conelits
        # print(id,"   ")
        # printeqconelit(system[id],conelit)
    # end 
    return cone,conelits
end
function rup(system,invsys,antecedants,init,assi,front,cone,conelits,prism,subrange)# I am putting back cone and front together because they will both end up in the cone at the end.
    que = ones(Bool,init)
    rev = reverse(system[init])
    prio = true
    r0 = i = 1
    r1 = init+1
    implgraph = Dict{Int,Tuple{Int,Int}}()
    @inbounds while i<=init
        if que[i] && (!prio || (prio&&(front[i]||cone[i]))) && (!inprism(i,prism) || (i in subrange))
            eq = i==init ? rev : system[i]
            s = slack(eq,assi)
            if s<0
                implgraph[0] = i,getlvl(implgraph,eq,assi)
                conflictanalysisque(0,implgraph,antecedants,assi,system,conelits,init)
                # antecedants[i] = true
                return true
            else
                r0,r1 = updateprioquebit(eq,cone,front,que,invsys,s,i,init,assi,antecedants,implgraph,r0,r1)
            end
            que[i] = false
            i+=1
            if prio
                i = min(i,r1)
                r1 = init+1
            else
                if r1<init+1
                    prio = true
                    r0 = min(i,r0)
                    i = r1
                    r1 = init+1
                else
                    i = min(i,r0)
                    r0 = init+1
                end
            end
        else
            i+=1
        end
        if prio && i==init+1
            prio=false
            i=r0
            r0=init+1
        end
    end
    return false
end
function slack(eq::Eq,assi::Vector{Int8}) # slack is the difference between the space left to catch the bound and the space catchable by the unaffected variables.
    c=0
    val = zero(Int8)
    @inbounds for l in eq.t
        val = assi[l.var]
        if val == 0 || 
            (l.sign && val == 1) || 
            (!l.sign && val == 2) 
            c+=l.coef
        end
    end
    if length(eq.t) > 0
        c-= eq.b
    end
    return c
end
function slackconelits(eq::Eq,assi::Vector{Int8},conelit) # slack is the difference between the space left to catch the bound and the space catchable by the unaffected variables.
    c=0
    val = zero(Int8)
    @inbounds for l in eq.t
        if !(l.var in conelit) # non coonelit variables are weakened, so always count
            c+=l.coef
        else
            val = assi[l.var]
            if val == 0 || 
                (l.sign && val == 1) || 
                (!l.sign && val == 2) 
                c+=l.coef
            end
        end
    end
    if length(eq.t) > 0
        c-= eq.b
    end
    return c
end
function istrivial(eq::Eq,conelits,id::Int)
    a = 0
    if haskey(conelits,id)
        for l in eq.t
            if !(l.var in conelits[id])
                a+= l.coef
            end
        end
    end
    return eq.b-a<=0
end
function removetrivialantecedants(system,antecedants,conelits,link,init)
    # printeqconelit(system[init],conelits[init])
    # printstyled("removing trivial antecedants from $init ",link,"\n"; color = :cyan)
    for i in findall(antecedants)
        # println("check if $i is trivial ",istrivial(system[i],conelits,i))
        # printeqconelit(system[i],conelits[i])
        if istrivial(system[i],conelits,i)
            # printstyled(" $i is trivial "; color = :green)
            # printeqconelit(system[i],conelits[i])
            j = findfirst(x->x==i,link) # look for the antecedant in the link and remove it
            if j===nothing
                println("antecedant $i not found in link $link")
                continue
            end
            k0 = findfirst(x->x==-1,link[j+1:end])
            if k0 === nothing
                println("antecedant $i's addition not found in link $link")
                deleteat!(link,j)
                antecedants[i] = false
                continue
            end
            k = k0+j #TODO make it so the removed id is indeed directly added to the pol ant htink of what to do otherwise
            deleteat!(link,(j,k)) # remove the antecedant and its plus from the link
            antecedants[i] = false
            # println("pol or ia link modified: ", link[j]," ",link)
        end
    end
    # printeqconelit(system[init],conelits[init])
end
function isobjlb(eq::Eq,obj::Vector{Lit},lowerbound::Int)
    if eq.b!=lowerbound || length(eq.t) != length(obj)
        return false
    end
    for i in eachindex(eq.t)
        if eq.t[i].coef != obj[i].coef || eq.t[i].sign != obj[i].sign || eq.t[i].var != obj[i].var # I can do that because both are sorted
            return false
        end 
    end
    return true
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
function getinvsys(system,systemlink,varmap)
    invsys = Vector{Vector{Int}}(undef,length(varmap))
    for i in eachindex(system)
        addinvsys(invsys,system[i],i)
    end # arrays should be sorted at this point
    return invsys
end
function setconelits(conelits,v,id)
    if haskey(conelits,id)
        push!(conelits[id],v)
    else
        conelits[id] = Set([v])
    end
end
function conflictanalysisque(var,implgraph,antecedants,assi,system,conelits,rev=-1)
    pq = PriorityQueue{Int, Int}()                      # we use a priority queue to store the variables to be explained and their conflict level
    id,lvl = implgraph[var]
    lastlvl = lvl+1
    enqueue!(pq,var,lastlvl - lvl)                                    # we add the variable to the queue with its level
    while !isempty(pq)
        # println(pq)
        var,prio = dequeue_pair!(pq)                                                      # we get the variable with the highest level
        # println("dequeueing $var with prio $prio")
        id,lvl = implgraph[var]
        if var>0 assi[var] = 0 end                                                           # on desaffecte la var
        implgraph[var] = -1,lvl                                      # we set the explanation to 0 because things are propagated only once and we dont like loops
        antecedants[id] = true                                                      # we add the variable to the antecedants set and we explain it
        eq = system[id]                                                        # we get the equation that is used to fix the variable        
        lits = getcontrib(eq,assi)                                                # we get the variables that were assigned
        if id==rev
            eq = reverse(eq)
        end
        sort!(lits,by = x -> implgraph[x.var][2],rev=true)                     # we sort the variables by their level in the implgraph (the higher the level, the more recent the propagation)
        b = eq.b                                                                # the bound of the eq
        #TODO remove from lits and add to the sum all the lits already in use
        somme = sum(l.coef for l in eq.t if l.var != var; init = 0) # we get the sum of the coefficients of the variables
        # print(id,"  ","   ");printeqcontributeslack(eq,assi)
        setconelits(conelits,var,id)
        for l in lits
            if somme < b
                break # we stop the loop if the sum is already less than the bound
            end
            v = l.var

            if lastlvl - implgraph[v][2] < prio # the variable is in a lower layer of the graph so I unassign it to forget about it.
                assi[v] = 0
                # plvl = lastlvl - prio
                # printstyled("skipping $v with prio $prio because implgraph level $plvl -> $(implgraph[v][2])\n"; color = :light_blue)
                continue # ignore this litteral
            end
            # on a un cas ou l'analyse de conflict veux remonter aux variables des niveaux inferieurs pace que c'est mieux et que je ne maintiens pas l'assignement dans chaque noeud et que je ne le met pas a jour en fonction des niveaux.
            if haskey(implgraph,v) && implgraph[v][1]>0 && !haskey(pq,v) # we check if the variable is not already explained
                enqueue!(pq,v,lastlvl - implgraph[v][2]) # we add the variable to the queue with its level
            elseif  haskey(pq,v)
                # printstyled(" $v in pq \n"; color = :blue)
            elseif implgraph[v][1]>=0
                # printstyled(" $v already explained \n"; color = :yellow)
            else
                printstyled(" $v not in implgraph or pq \n"; color = :red)
            end
            setconelits(conelits,v,id)
            somme -= l.coef # the variable does not contribute to the sum anymore
        end
        if var in [-1]   
            printstyled("\n explain var $var in eq $id at lvl $lvl \n"; color = :yellow)
            printeqcontributeslack(eq,assi)
            printeqconelit(eq,conelits[id])
        end

        if somme >= b
            printstyled("Could not explain var $var in eq $id at lvl $lvl \n"; color = :red)
            printeqcontributeslack(eq,assi)
            printeqconelit(eq,conelits[id])
            throw(ErrorException("Could not explain $var with eq $id at lvl $lvl")) 
        end
    end
end
# depreciated and wrong
function conflictanalysisordered(var,implgraph,antecedants,assi,system,conelits)
    id,lvl = implgraph[var]
    if id > 0 
        tmp = 4
        if var>0 
            tmp = assi[var]
            assi[var] = 0
        end                             # we set the variable to 0 because it is propagated and does cannot contribute to any other sum
        implgraph[var] = 0,lvl                                      # we set the explanation to 0 because things are propagated only once and we dont like loops
        antecedants[id] = true                                  # we add the variable to the antecedants set and we explain it
        lits = getcontrib(system[id],assi)                      # we get the variables that were assigned and contributed negativelly in the sum in the eq for this propagation.
        sort!(lits,by = x -> implgraph[x.var][2],rev=true)               # we sort the variables by their level in the implgraph (the higher the level, the more recent the propagation)
        b = system[id].b                                        # the bound of the eq
        somme = sum(l.coef for l in system[id].t if l.var != var; init = 0) # we get the sum of the coefficients of the variables
        # printeqcontributeslack(system[id],assi)
        for l in lits
            # sign = assi[l.var] == 1 ? -1 : 1  # we check the sign of the lit
            if conflictanalysisordered(l.var,implgraph,antecedants,assi,system,conelits)
                if haskey(conelits,id) # we check if the lit is in the conelits
                    push!(conelits[id],l.var)
                else
                    conelits[id] = Set([l.var])
                end
                somme -= l.coef # the variable does not contribute to the sum anymore
                if somme<b
                    # implgraph[var] = id
                    if var>0 assi[var] = tmp end # we restore the variable to its previous value
                    # printstyled(" conflict analysis for $var reached conflict \n"; color = :green)
                    return true # we reached the point where we need to propagate var to keep the eq sat
                end
            else 
                # verifier que les var innexpliquees ne contribuent pas.
                printeqcontributeslack(system[id],assi)
                printstyled("$var conflict analysis for $l.var could not reach conflict \n"; color = :red)
            end
        end
        if (findfirst(l->l.var == var,system[id].t)===nothing) || slack(system[id],assi) < system[id].t[findfirst(l->l.var == var,system[id].t)].coef # we check if the eq is still sat
            if var>0 assi[var] = tmp end # we restore the variable to its previous value
            return true
        else
            if var>0 assi[var] = tmp end # we restore the variable to its previous value
            implgraph[var] = id,lvl
            printstyled(" conflict analysis for $var could not reach conflict \n"; color = :red)
            return false # we did not reach the point where we need to propagate var to keep the eq sat
        end
    end
    return false
end
function contributenegatively(lit::Lit,assi::Vector{Int8})
    return (!lit.sign && assi[lit.var] == 1) || (lit.sign && assi[lit.var] == 2)
end
function getcontrib(eq::Eq,assi::Vector{Int8}) # get the lits that contribute negatively to the slack. they may become reasons of propagations.
    return [l for l in eq.t if contributenegatively(l,assi)]
end
function getlvl(implgraph,eq,assi::Vector{Int8})
    m = -1
    for l in eq.t
        if contributenegatively(l,assi)
            if haskey(implgraph,l.var)
                m = max(m,implgraph[l.var][2])
            end
        end
    end
    if m==-1 return 0 else
        return m+1
    end
end
function updatequebit(eq,que,invsys,s,i,assi::Vector{Int8},antecedants,implgraph)
    rewind = i+1
    lvl = getlvl(implgraph,eq,assi) # we get the level of the eq in the implgraph
    for l in eq.t
        if l.coef > s && assi[l.var]==0
            # if i == 10997 && l.var in [25,109,171]   
            #     printstyled(" propagate $l in eq $i at lvl $lvl with s=$s \n"; color = :magenta)
            #     printeqcontributeslack(eq,assi)
            # end
            implgraph[l.var] = i,lvl # we store the id of the eq that is used to fix the variable and the lvl of propagation
            assi[l.var] = l.sign ? 1 : 2
            for id in invsys[l.var]
                rewind = min(rewind,id)
                que[id] = true
            end
        end
    end
    return rewind
end
function upquebit(system,invsys,assi::Vector{Int8},antecedants,prism,conelits)
    que = ones(Bool,length(system))
    i = 1
    implgraph = Dict{Int,Tuple{Int,Int}}()
    @inbounds while i<=length(system)
        if que[i] && !inprism(i,prism)
            eq = system[i]
            s = slack(eq,assi)
            if s<0
                implgraph[0] = i,getlvl(implgraph,eq,assi)
                return conflictanalysisque(0,implgraph,antecedants,assi,system,conelits) # this is the best one
            else
                rewind = updatequebit(eq,que,invsys,s,i,assi,antecedants,implgraph)
                que[i] = false
                i = min(i,rewind-1)
            end
        end
        i+=1
    end
    printstyled(" upQueBit empty \n "; color = :red)
end
function upquebitrestrained(system,invsys,assi::Vector{Int8},antecedants,prism)
    que = ones(Bool,length(system))
    i = 1
    # implgraph = Dict{Int,Tuple{Vararg{Int}}}() # for the implication graph of the rup process. maps a variable to the id of the eq that is used to fix it and the involved variables in the tuple (id,var,var,...)
    implgraph = Dict{Int,Tuple{Int,Int}}() # for the implication graph of the rup process. maps a variable to the id of the eq that is used to fix it and the involved variables in the tuple (id,var,var,...)
    @inbounds while i<=length(system)
        if que[i] && !inprism(i,prism) && antecedants[i] # we only check the antecedants
            eq = system[i]
            s = slack(eq,assi)
            if s<0
                # implgraph[0] = i
                # implgraph[0] = (i,[l.var for l in eq.t if assi[l.var]!=0]...)
                # antecedants[i] = true
                printstyled(" V "; color = :green)
                return 
            else
                rewind = updatequebit(eq,que,invsys,s,i,assi,antecedants,implgraph)
                que[i] = false
                i = min(i,rewind-1)
            end
        end
        i+=1
    end
    printstyled(" upQueBit conflict analysis test failed \n "; color = :red)
end
function upquebitrestrainedconelits(system,invsys,assi::Vector{Int8},antecedants,prism,conelits)
    que = ones(Bool,length(system))
    i = 1
    # implgraph = Dict{Int,Tuple{Vararg{Int}}}() # for the implication graph of the rup process. maps a variable to the id of the eq that is used to fix it and the involved variables in the tuple (id,var,var,...)
    implgraph = Dict{Int,Tuple{Int,Int}}() # for the implication graph of the rup process. maps a variable to the id of the eq that is used to fix it and the involved variables in the tuple (id,var,var,...)
    @inbounds while i<=length(system)
        if que[i] && !inprism(i,prism) && antecedants[i] # we only check the antecedants
            eq = system[i]
            s = 0
            if haskey(conelits,i)
                s = slackconelits(eq,assi,conelits[i])
            else
                s = slack(eq,assi)
            end
            if s<0
                # implgraph[0] = i
                # implgraph[0] = (i,[l.var for l in eq.t if assi[l.var]!=0]...)
                # antecedants[i] = true
                printstyled(" V "; color = :green)
                return 
            else
                rewind = updatequebit(eq,que,invsys,s,i,assi,antecedants,implgraph)
                que[i] = false
                i = min(i,rewind-1)
            end
        end
        i+=1
    end
    printstyled(" upQueBit conflict analysis test failed \n "; color = :red)
end
function ruprestrained(system,invsys,antecedants,init,assi,front,cone,conelits,prism,subrange)
    que = ones(Bool,init)
    rev = reverse(system[init])
    prio = true
    r0 = i = 1
    r1 = init+1
    implgraph = Dict{Int,Tuple{Int,Int}}()
    @inbounds while i<=init
        if que[i] &&  antecedants[i] && (!prio || (prio&&(front[i]||cone[i]))) && (!inprism(i,prism) || (i in subrange))
            eq = i==init ? rev : system[i]
            s = slack(eq,assi)
            if s<0
                # implgraph[0] = i,getlvl(implgraph,eq,assi)
                # conflictanalysisque(0,implgraph,antecedants,assi,system,conelits)
                # antecedants[i] = true
                printstyled(" V "; color = :green)
                return true
            else
                r0,r1 = updateprioquebit(eq,cone,front,que,invsys,s,i,init,assi,antecedants,implgraph,r0,r1)
            end
            que[i] = false
            i+=1
            if prio
                i = min(i,r1)
                r1 = init+1
            else
                if r1<init+1
                    prio = true
                    r0 = min(i,r0)
                    i = r1
                    r1 = init+1
                else
                    i = min(i,r0)
                    r0 = init+1
                end
            end
        else
            i+=1
        end
        if prio && i==init+1
            prio=false
            i=r0
            r0=init+1
        end
    end
    printstyled(" rup conflict analysis test failed \n "; color = :red)
    return false
end
function ruprestrainedconelits(system,invsys,antecedants,init,assi,front,cone,conelits,prism,subrange)
    que = ones(Bool,init)
    rev = reverse(system[init])
    prio = true
    r0 = i = 1
    r1 = init+1
    implgraph = Dict{Int,Tuple{Int,Int}}()
    @inbounds while i<=init
        if que[i] &&  antecedants[i] && (!prio || (prio&&(front[i]||cone[i]))) && (!inprism(i,prism) || (i in subrange))
            eq = i==init ? rev : system[i]
            if haskey(conelits,i)
                s = slackconelits(eq,assi,conelits[i])
            else
                s = slack(eq,assi)
            end
            if s<0
                # implgraph[0] = i,getlvl(implgraph,eq,assi)
                # conflictanalysisque(0,implgraph,antecedants,assi,system,conelits)
                # antecedants[i] = true
                printstyled(" V "; color = :green)
                return true
            else
                r0,r1 = updateprioquebit(eq,cone,front,que,invsys,s,i,init,assi,antecedants,implgraph,r0,r1)
            end
            que[i] = false
            i+=1
            if prio
                i = min(i,r1)
                r1 = init+1
            else
                if r1<init+1
                    prio = true
                    r0 = min(i,r0)
                    i = r1
                    r1 = init+1
                else
                    i = min(i,r0)
                    r0 = init+1
                end
            end
        else
            i+=1
        end
        if prio && i==init+1
            prio=false
            i=r0
            r0=init+1
        end
    end
    printstyled(" rup conflict analysis test failed \n "; color = :red)
    return false
end
function updateprioquebit(eq,cone,front,que,invsys,s,i,init,assi::Vector{Int8},antecedants,implgraph,r0,r1)
    lvl = getlvl(implgraph,eq,assi) # we get the level of the eq in the implgraph
    @inbounds for l in eq.t
        if l.coef > s && assi[l.var]==0
            # if i == 10997 && l.var in [25,109,171]   
            #     printstyled(" propagate $l in eq $i at lvl $lvl with s=$s \n"; color = :magenta)
            #     printeqcontributeslack(eq,assi)
            # end
            assi[l.var] = l.sign ? 1 : 2
            implgraph[l.var] = i,lvl # we store the id of the eq that is used to fix the variable to use conflict analysis and find the antecedants later.
            for id in invsys[l.var]
                if id<=init && id!=i
                    que[id] = true
                    if cone[id] || front[id]
                        r1 = min(r1,id)
                    else
                        r0 = min(r0,id)
                    end
                end
            end
        end
    end
    return r0,r1
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
function fixconelits(conelits,system,i,antecedants,link) # TODO be more precise ?
    takeall = false
    if !takeall && !(-3 in link[2:end])# && !(-4 in link) # we prevent deletions pol to be conelits propag
        eq = system[i]
        myconelit = haskey(conelits,i) ? conelits[i] : Set([l.var for l in eq.t ])
        poslits = Set{Int}()
        neglits = Set{Int}()
        for j in findall(antecedants) # TODO replace findall by more effeicient 
            for l in system[j].t
                if l.sign
                    push!(poslits,l.var)
                else
                    push!(neglits,l.var)
                end
            end
            if haskey(conelits,j)
                myconelit = conelits[j] ∪ myconelit 
            end
        end
        myconelit = myconelit ∪ (poslits ∩ neglits) # we add the cacelling lits in the mandatory conelit
        for j in findall(antecedants)
            conelits[j] =  myconelit ∩ Set([l.var for l in system[j].t])
            # conelits[j] = Set([l.var for l in system[j].t])
        end
        conelits[i] = myconelit ∩ Set([l.var for l in eq.t])
    else
        for j in findall(antecedants)
            conelits[j] = Set([l.var for l in system[j].t])
        end
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
function fixredsystemlink(systemlink,cone,prism,nbopb)
    for range in prism
        for i in range
            if cone[i]
                for j in eachindex(systemlink[i-nbopb])
                    k = systemlink[i-nbopb][j]
                    if isid(systemlink[i-nbopb],j) && !(k in systemlink[range.start-nbopb]) && k<range.start-nbopb
                        push!(systemlink[range.start-nbopb],k)
                    end
                end
            end
        end
        sort!(systemlink[range.start-nbopb])
    end
end
function inprism(n,prism)
    for r in prism
        if n in r return true end
    end
    return false
end
function availableranges(redwitness)                   # build the prism, a range colections of all the red subproofs
    prism = [a.range for (_,a) in redwitness if a.range!=0:0]
    return prism
end
module LP
    using JuMP,HiGHS
    export LPpol
    function LPpol(a,b,asol,bsol,obj)
        # TODO on a besoin du lazy pol generation sinon on retrouve avec des LP le fait que des tas de trucs sont inutiles.
        # TODO retier de l'objectif les equations qui sont dans le opb ? (on peux garder comme ca si on veux une preuve le plus petite possible ? en esperant que ca passe mieux oiu on peux utiliser l'ordre et le mettre dans l'obj)
        nbctr = size(a,1)
        nbvar = size(a,2)
        bigM = max(maximum(abs.(a)),maximum(abs.(b)),maximum(abs.(asol)),abs(bsol))+1 # 2^20
        # println("x moi",bigM)
        # pour highs on a un bug a partir de big m = 2^27 
        # pour glpk  on a un big a partir de big m = 2^18 
        m = Model(HiGHS.Optimizer)
        set_optimizer_attribute(m,"output_flag",false)

        @variable(m,lambda[i = 1:nbctr] >=0,Int)            # I dont specify int here to make it faster. maybe we can use deletions in a smart manner here 
        @variable(m,lambdaBin[i = 1:nbctr], Bin)
        
        @constraint(m, ctr_milp1[j in 1:nbvar], sum(a[i,j]*lambda[i] for i in 1:nbctr) <= asol[j]) # on peut remplir la colone avec des axiomes
        @constraint(m, ctr_milp2, sum(lambda[i] * b[i] for i in 1:nbctr) == bsol)
        @constraint(m, ctr_milp_flag[i in 1:nbctr], lambda[i] <= lambdaBin[i] * bigM)  
        
        @objective(m, Min, sum(obj[i]*lambdaBin[i] for i in 1:nbctr))

        # print(m)
        optimize!(m)
        if termination_status(m) == MOI.OPTIMAL# && objective_value(m) < nbctr
            simpler = false
            for i in 1:nbctr
                simpler |= round(Int,value(lambda[i]))==0
            end
            if simpler
                println()
                for i in 1:nbctr
                    print(round(Int,value(lambda[i])),' ')
                end
                print('B')
                return true , [round(Int,value(lambda[i])) for i in 1:nbctr]
            else
                print('T')
            end
        else
            print('F')
        end
        return false , Int[]
    end
    # add litteral axioms for negative variables. add objective wheights for the order  and deactivate the lambdabin for the opb
end 
if CONFIG.LPsimplif
    using .LP
end
function simplepol(res,system,link,nbopb)
    varset = Vector{Int}()
    ctrset = [link[i] for i in eachindex(link) if isid(link,i)]
    nbctr = length(ctrset)
    for i in ctrset
        for l in system[i].t
            if !(l.var in varset)
                push!(varset,l.var)
            end
        end
    end
    sort!(varset)
    nbvar = length(varset)
    obj = zeros(Int,nbctr)
    cobj = 1
    a = zeros(Int,nbctr,nbvar)
    b = zeros(Int,nbctr)
    eq0 = Eq([Lit(0,true,v) for v in varset],0)
    for i in eachindex(ctrset)
        id = ctrset[i]
        eq = system[id]
        eq = addeq(eq,eq0)
        for l in eq.t
            a[i,findfirst(x->x==l.var,varset)] = l.coef
        end
        if id>nbopb
            obj[i] = cobj += 1
        end
        b[i] = eq.b
    end
    aeq = addeq(res,eq0)
    avars = [l.var for l in aeq.t]
    asol = zeros(Int,nbvar)
    for i in eachindex(varset)
        v = varset[i]
        j = findfirst(x->x==v,avars)
        if !(j === nothing)
            asol[i] = aeq.t[j].coef
        end
    end
    bsol = aeq.b
    # println(a)
    # println(asol)
    # println(b)
    # println(bsol)
    # a = [ 1 0 0 4; -2 3 0 -5; 1 0 0 4; 0 -1 0 1]
    # b = [1,-2,1,2]
    # asol = [0 0 0 3]
    # bsol = 6
    f,link2 = LPpol(a,b,asol,bsol,obj)
    if f
        println()
        for i in eachindex(link2)
            print(ctrset[i],"  ")
            printeq(system[ctrset[i]])
        end
        println(link2)
        printeq(res)
        println(link)
        println()
    else
        return link
    end
end
function remakelink()
    # TODO
end



# =============== Justifyer ===============


function justify(f,eq,i,asserthint,index,varmap)
    st = split(asserthint,keepempty=false)
    extrai = 0
    if st[1] == "deg" # assert degree proof
        extrai = justifydeg(f,eq,i,st[2:end],index,varmap)
    end
    return extrai
end
function justifydeg(f,eq,i,hints,index,varmap)
    link = [-2,parse(Int,hints[1])]
    for i in 2:length(hints)-1
        push!(link,parse(Int,hints[i]))
        push!(link,-1)
    end
    push!(link,parse(Int,hints[end]))
    push!(link,-1,-4)
    write(f,writepol(link,index,varmap))
    write(f, string("ia ",writeeq(eq,varmap)[1:end-2],": -1 ;\n"))
    write(f,string("del id -2 ;\n"))
    return 1 # number of extra lines
end



# ================ Printer ================


function writeconedel(path,file,version,system,cone,conelits,systemlink,redwitness,solirecord,assertrecord,nbopb,
                        varmap,ctrmap,invctrmap,output,conclusion,obj,prism)
    index = zeros(Int,length(system))
    lastindex = 0
    open(string(path,"/smol.",file,".opb"),"w") do f
        if length(obj)>0
            write(f,"min: ")
            write(f,writelits(obj,varmap))
            write(f," ;\n")
        end
        for i in 1:nbopb
            if cone[i]
                if CONFIG.keeplabels && haskey(invctrmap,i) write(f,"@"*invctrmap[i]*" ") end # write label if it exists
                lastindex += 1
                index[i] = lastindex
                eq = system[i]
                if haskey(conelits,i)
                    write(f,writeeqconelits(eq,varmap,conelits[i]))
                else
                    write(f,writeeq(eq,varmap))
                end
            end
        end
    end
    succ = Vector{Vector{Int}}(undef,length(system))
    dels = zeros(Bool,length(system))
    # dels = ones(Bool,length(system)) # uncomment to have no deletions
    dels[1:nbopb].=true #we dont delete in the opb
    for p in prism
        dels[p].=true # we dont delete red and supproofs because veripb is already doing it
    end
    invlink(systemlink,succ,cone,nbopb)
    todel = Vector{Int}()
    open(string(path,"/smol.",file,extention),"w") do f
        write(f,string("pseudo-Boolean proof version ",version,"\n"))
        write(f,string("f ",sum(cone[1:nbopb])," ;\n"))
        for i in nbopb+1:length(system)
            if cone[i]
                if CONFIG.keeplabels && haskey(invctrmap,i) write(f,"@"*invctrmap[i]*" ") end # write label if it exists
                lastindex += 1
                index[i] = lastindex
                eq = system[i]
                tlink = systemlink[i-nbopb][1]
                if tlink == -1               # rup
                    if haskey(conelits,i)
                        write(f,writeuconelits(eq,varmap,conelits[i]))
                    else
                        write(f,writeu(eq,varmap))
                    end
                    if length(eq.t)>0 
                        writedel(f,systemlink,i,succ,index,nbopb,dels)
                    end
                elseif tlink == -2           # pol
                    write(f,writepol(systemlink[i-nbopb],index,varmap))
                    writedel(f,systemlink,i,succ,index,nbopb,dels)
                elseif tlink == -3           # ia
                    if haskey(conelits,i)
                        write(f,writeiaconelits(eq,systemlink[i-nbopb][2],index,varmap,conelits[i]))
                    else
                        write(f,writeia(eq,systemlink[i-nbopb][2],index,varmap))
                    end
                    writedel(f,systemlink,i,succ,index,nbopb,dels)
                elseif tlink == -4           # red alone
                    write(f,writered(eq,varmap,redwitness[i],"")) # since simple red have no antecedants, they cannot trigger deletions ie they cannot be the last successor of a previous eq
                    dels[i] = true           # we dont delete red statements
                elseif tlink == -5           # rup in subproof
                    write(f,"    ")
                    write(f,writeu(eq,varmap))
                    push!(todel,i)
                elseif tlink == -6           # pol in subproofs
                    write(f,"    ")
                    write(f,writepol(systemlink[i-nbopb],index,varmap))
                    push!(todel,i)
                elseif tlink == -9           # red with begin initial reverse equation (will be followed by subproof)
                    write(f,writered(reverse(eq),varmap,redwitness[i]," ; begin"))
                    todel = [i]
                    dels[i] = true           # we dont delete red statements
                elseif tlink == -7           # red proofgoal 
                    write(f,"    proofgoal #1\n")
                elseif tlink == -8           # red proofgoal normal
                    write(f,string("    proofgoal ",index[systemlink[i-nbopb][2]],"\n"))
                    push!(todel,i)
                elseif tlink == -10          # red proofgoal end
                    lastindex -= 1
                    write(f,"    end -1\n")
                    next = systemlink[i-nbopb][1]
                    if next != -7 && next !=8  # if no more proofgoals, end the subproof
                        lastindex += 1
                        write(f,"end\n") 
                        for ii in todel
                            writedel(f,systemlink,ii,succ,index,nbopb,dels)
                        end
                    end
                elseif tlink == -20           # solx
                    write(f,writesolx(eq,varmap))
                    dels[i] = true # do not delete sol
                elseif tlink == -21           # soli
                    write(f,writesoli(solirecord[i]),varmap)
                    # dels[i] = true # do not delete sol
                elseif tlink == -30           # unchecked assumption
                    if haskey(assertrecord,i)
                        lastindex += justify(f,eq,i,assertrecord[i],index,varmap)
                    else
                        write(f,string("a ",writeeq(eq,varmap)))
                    end
                else
                    println("ERROR tlink = ",tlink)
                    lastindex -= 1
                end
            end
        end
        write(f,string("output ",output," ;\n"))
        if conclusion == "SAT"
            write(f,string("conclusion ",conclusion," ;\n"))
        elseif conclusion == "UNSAT"
            write(f,string("conclusion ",conclusion," : -1 ;\n"))
        else # conclusion == "NONE" or "BOUNDS"
            write(f,string(replace(conclusion,";"=>"")," ;\n"))
        end
        write(f,"end pseudo-Boolean proof ;")
    end
end
function invlink(systemlink,succ::Vector{Vector{Int}},cone,nbopb)
    for i in eachindex(systemlink)
        if isassigned(systemlink,i)
            link = systemlink[i]
            for k in eachindex(link)
                j = link[k]
                if isid(link,k) && cone[i+nbopb]
                    if isassigned(succ,j)
                        if !(i+nbopb in succ[j])
                            push!(succ[j],i+nbopb)
                        end
                    else
                        succ[j] = [i+nbopb]
                    end
                end
            end
        end
    end
end
function findallindexfirst(index,cone)
    lastindex = 0
    for i in eachindex(cone)
        if cone[i]
            lastindex += 1
            index[i] = lastindex
        end
    end
end
function mkdir2(p) if !isdir(p) mkdir(p) end end
function printorder(file,cone,invsys,varmap)
    dir = string(proofs,"/cone_var_order/")
    mkdir2(dir)
    open(string(dir,file,".cc"),"w") do f
        write(f,"map<string,int> order { "   )
        varocc = [sum(cone[j] for j in i) for i in invsys] # order from var usage in cone
        p = sortperm(varocc,rev=true)
        occ = 0
        maxocc = length(varmap)
        for (i,var) in varmap
            occ+=1
            j = p[i]
            occ = varocc[j]
            if occ != maxocc
                write(f,string("{\"",var,"\",",occ,"}, "))
            else
                write(f,string("{\"",var,"\",",occ,"}"))
            end
        end
        write(f,"};")
    end
end
function writeu(e,varmap)
    return string("rup ",writeeq(e,varmap))
end
function writeuconelits(e,varmap,conelit)
    return string("rup ",writeeqconelits(e,varmap,conelit))
end
function writeia(e,link,index,varmap)
    return string("ia ",writeeq(e,varmap)[1:end-2],": ",index[link]," ;\n")
end
function writeiaconelits(e,link,index,varmap,conelit)
    return string("ia ",writeeqconelits(e,varmap,conelit)[1:end-2],": ",index[link]," ;\n")
end
function writesolx(e,varmap)
    s = "solx"
    for l in e.t
        s = string(s,if l.sign " ~" else " " end, varmap[l.var])
    end
    return string(s," ;\n")
end
function writesoli(sol,varmap)
    s = "soli"
    for l in sol
        s = string(s,if l.sign " " else " ~" end, varmap[l.var])
    end
    return string(s," ;\n")
end
function writewitness(s,witness,varmap)
    for l in witness.w
        if l.var>0
            s = string(s,if !l.sign " ~" else " " end, varmap[l.var])
        else
            s = string(s," ",-l.var)
        end
    end
    return s
end
function writered(e,varmap,witness,beg)
    s = "red"
    for l in e.t
        s = string(s," ",l.coef,if !l.sign " ~" else " " end, varmap[l.var])
    end
    s = string(s," >= ",e.b," ;")
    s = writewitness(s,witness,varmap)
    return string(s,beg,"\n")
end
function writepol(link,index,varmap)
    s = string("pol")
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
        elseif t==-5
            s = string(s," w")
        elseif t>0
            if link[i+1] in [-2,-3]
                s = string(s," ",t)
            else
                s = string(s," ",index[t])
            end
        elseif t<=-100
            sign = mod((-t),100)!=1
            s = string(s,if sign " " else " ~" end,varmap[(-t) ÷ 100])
        end
    end
    return string(s," ;\n")
end
function writedel(f,systemlink,i,succ,index,nbopb,dels)
    isdel = false
    link = systemlink[i-nbopb]
    for k in eachindex(link)
        p = link[k]
        if isid(link,k) && !dels[p] 
            m = maximum(succ[p])
            if m == i
                if !isdel
                    write(f,string("del id "))
                    isdel = true
                end
                dels[p] = true
                if index[p] == 0
                    println(p," in ",systemlink[p-nbopb])
                    printstyled(string("del index is 0 for ",p," => ",index[p],"\n"); color = :red)                
                else
                    write(f,string(index[p]," "))
                end
            end
        end
    end
    if isdel
        write(f,string(" ;\n"))
    end
end
function writelits(lits,varmap)
    s = ""
    for l in lits
        s = string(s,writelit(l,varmap)," ")
    end
    return s
end
function writelitsconelits(lits,varmap,conelit)
    b=0
    s = ""
    for l in lits
        if l.var in conelit || -l.var in conelit 
            s = string(s,writelit(l,varmap)," ")
        else
            b+=l.coef
        end
    end
    return s,b
end
function writeeq(e,varmap)
    s = writelits(e.t,varmap)
    return string(s,">= ",e.b," ;\n")
end
function writeeqconelits(e,varmap,conelit)
    s,b = writelitsconelits(e.t,varmap,conelit)
    return string(s,">= ",max(0,e.b-b)," ;\n")
end
function writelit(l,varmap)
    return string(l.coef," ",if l.sign "" else "~" end, varmap[l.var])
end
function isid(link,k)                 # dont put mult and div coefficients as id and weakned variables too
    return link[k]>0 && (k==length(link)||(link[k+1] != -2 && link[k+1] != -3))
end
function isequal(a,b) # equality between lits
    return a.coef==b.coef && a.sign==b.sign && a.var==b.var
end
function isequal(e,f) # equality between eq
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
    end
end
function printlit(l)
    if l.coef!=1 printstyled(l.coef; color = :blue) end
    if !l.sign printstyled('~'; color = :red) else print(" ") end
    printstyled(l.var; color = :green)
end
function printlitcolor(l,color)
    if l.coef!=1 printstyled(l.coef; color = :blue) end
    if !l.sign printstyled('~'; color = :red) else print(" ") end
    printstyled(l.var; color = color)
end
function printlit(l,varmap)
    printstyled(l.coef; color = :blue)
    if !l.sign printstyled('~'; color = :red) else print(' ') end
    printstyled(varmap[l.var]; color = :green)
end
function printeq(e)
    for l in e.t
        print(" ")
        printlit(l)
    end
    println(" >= ",e.b)
end
function printeqconelit(e,conelit)
    s=0
    for l in e.t
        print(" ")
        if l.var in conelit || -l.var in conelit
            printlitcolor(l,:yellow)
        else
            printlitcolor(l,:magenta)
            s+=l.coef
        end
    end
    if s==0
        println(" >= ",e.b)
    else
        println(" >= ",e.b," - ",s," >= ",e.b-s)
    end
end
function printeqcontributeslack(e,assi)
    for l in e.t
        print(" ")
        if assi[l.var] == 0
            printlitcolor(l,:yellow)
        elseif assi[l.var] == 1 && l.sign || assi[l.var] == 2 && !l.sign
            printlitcolor(l,:green)
        else
            printlitcolor(l,:red)
        end
    end
    println(" >= ", e.b)
end
function printeq(e,varmap)
    for l in e.t
        print(" ")
        printlit(l,varmap)
    end
    println(" >= ",e.b)
end
function printeqlink(i,system,systemlink)
    nbopb = length(system)-length(systemlink)
    print(i,"  ")
    printeq(system[i])
    println(systemlink[i-nbopb])
end
function showadjacencymatrixsimple(file,cone,index,systemlink,succ,nbopb)
    M,D,n = computeMD(file,cone,index,systemlink,succ,nbopb)
    dir = string(proofs,"/cone_mat/")
    mkdir2(dir)
    open(string(dir,file,".html"),"w") do f
        write(f,"<!DOCTYPE html><head>
  <meta charset=\"UTF-8\">
  <meta name=\"viewport\" content=\"width=device-width, initial-scale=1.0\">
  <title>$file</title>
  <style>
    canvas {
      border: 1px solid #ccc;
    }
    .cell {
      stroke: #ccc;
      shape-rendering: crispEdges;
    }
    .label {
      font-size: 14px;
      font-family: Arial, sans-serif;
      text-anchor: middle;
    }
  </style>
</head>
<body>
  <script>")

    writematjs("matrix",M,n,f)

    write(f,"const size = 20; // Cell size
    const n = matrix.length;
    
    // Flatten the matrix
    const flattenedMatrix = matrix.flat();

    // Create Canvas
    const canvas = document.createElement(\"canvas\");
    canvas.width = n * size;
    canvas.height = n * size;
    document.body.appendChild(canvas);
    const context = canvas.getContext(\"2d\");
    // Function to draw the matrix
    function drawMatrix() {
      for (let i = 0; i < flattenedMatrix.length; i++) {
        const value = flattenedMatrix[i];
        // Calculate row and column from the index
        const row = Math.floor(i / n);
        const col = i % n;
        // Determine the cell color
        context.fillStyle = value ? \"steelblue\" : \"white\";
        // Draw the cell
        context.fillRect(col * size, row * size, size, size);
        context.strokeStyle = \"#ccc\";
        context.strokeRect(col * size, row * size, size, size);
      }
    }
    // Initial draw
    drawMatrix();
  </script>
</body>
</html>
")
end
end
function showadjacencymatrix(file,cone,index,systemlink,succ,nbopb)
    M,D,n = computeMD(file,cone,index,systemlink,succ,nbopb)
    dir = string(proofs,"/cone_mat/")
    mkdir2(dir)
    open(string(dir,file,".html"),"w") do f
        write(f,"<!DOCTYPE html><head>
  <title> $file </title>
  <script src=\"https://d3js.org/d3.v7.min.js\"></script>
  <style>
    .cell {
      stroke: #ccc;
      shape-rendering: crispEdges;
    }
    .label {
      font-size: 14px;
      font-family: Arial, sans-serif;
      text-anchor: middle;
    }
  </style>
</head>
<body>
  <script>")

    writematjs("matrix",M,n,f)
    writematjs("dist",D,n,f)
    max = maximum(D)

    write(f,"const size = 20; // Cell size
    const n = matrix.length;
    const max = $max;

    // Create SVG
    const svg = d3.select(\"body\")
      .append(\"svg\")
      .attr(\"width\", n * size+size)
      .attr(\"height\", n * size+size);
    let isHighlighted = false; // Track if the matrix is highlighted
    // Draw cells
    for (let row = 0; row < n; row++) {
      for (let col = 0; col < n; col++) {
        svg.append(\"rect\")
          .datum({ value: matrix[row][col], row, col }) // Bind data directly
          .attr(\"class\", \"cell\")
          .attr(\"x\", col * size+size)
          .attr(\"y\", row * size+size)
          .attr(\"width\", size)
          .attr(\"height\", size)
          .attr(\"fill\", matrix[row][col] ? \"steelblue\" : \"white\")
          .on(\"click\", function (event, d) {
            if (isHighlighted) {
          // Reset all cells
          d3.selectAll(\".cell\")
            .attr(\"fill\", d => d.value ? \"steelblue\" : \"white\");
          isHighlighted = false; // Unset highlight
        } else {
            d3.selectAll(\".cell\")
              .attr(\"fill\",  cell => {
                const val = dist[cell.row][cell.col];
                if (val>0&& cell!=d && d.value>0) {
                    if (cell.row==row){
                        return `rgb(0,\${55+val*200/max},0)`;
                    }else if(cell.col==col) {
                        return `rgb(\${55+val*200/max},0,0)`;
                    }else{
                        return matrix[cell.row][cell.col] ? \"steelblue\" : \"white\"
                    }
                }else{
                        return matrix[cell.row][cell.col] ? \"steelblue\" : \"white\"
                    }
              });
            isHighlighted = true; // Set highlight
            }
          });
      }
    }

    // Add row labels
    svg.selectAll(\".row-label\")
      .data(d3.range(n))
      .enter()
      .append(\"text\")
      .attr(\"class\", \"label\")
      .attr(\"x\", size/2-2*size/10) // Offset for the label
      .attr(\"y\", d => d * size + size + 2*size/10 + size / 2)
      .text(d => d + 1); // Row numbers start from 1

    // Add column labels
    svg.selectAll(\".col-label\")
      .data(d3.range(n))
      .enter()
      .append(\"text\")
      .attr(\"class\", \"label\")
      .attr(\"x\", d => d * size + size + size / 2)
      .attr(\"y\", 8*size/10) // Offset for the label
      .text(d => d + 1);

  </script>
  </body>
</html>
")
    end
end
function writematjs(name,a,n,f)
    write(f,"const $name = [\n")
    for i in 1:n
        write(f,"[")
        for j in 1:n
            write(f,string(Int(a[i,j])))
            if j<n write(f,", ") end
        end
        if i<n write(f,"],\n") else write(f,"]];\n") end
    end
end
function distrec(M,i,n,D,rank)
    for j in 1:n
        if M[i,j] && D[i,j] > rank
            D[i,j] = rank
            distrec(M,j,n,D,rank+1)
        end
    end
end
function computeMD(file,cone,index,systemlink,succ,nbopb)
    n = sum(cone)
    M = zeros(Bool,n,n)
    for i in findall(cone)
        if isassigned(succ,i)
            for j in succ[i]
                M[index[i],index[j]] = true
            end
        end
    end
    D = fill(n+1,(n,n))
    distrec(M,1,n,D,1)
    for i in eachindex(D)
        if D[i]==n+1 D[i] = 0 end
    end
    return M,D,n
end
# reprint the proof with colors for ciaran
function printpred(i,link,nbpred,maxpred,index,nbopb)
    if length(link)<=1
        return ""
    else
        s = string( "<span style=\"color: rgb(",Int(round(200*nbpred[i-nbopb]/maxpred))+55,",0,0)\">Pred (",nbpred[i-nbopb],") ")
        for k in eachindex(link)
            if isid(link,k)
                s = string(s,lid(index[link[k]]))
            end
        end
        return string(s,"</span>\n")
    end
end
function printsucc(i,succ,nbsucc,maxsucc,index)
    s = string( "<span style=\"color: rgb(0,",Int(round(150*nbsucc[i]/maxsucc))+55,",0)\">Succ (",nbsucc[i],") ")
    for j in succ
        s = string(s,lid(index[j]))
    end
    return string(s,"</span>\n")
end
function writelitcolor(l,varmap,varocc,m,r)
    return string(l.coef," ",if l.sign "" else "~" end, "<span style=\"color: rgb(",Int(round(255*(varocc[l.var]-m)/r)),",0,255)\">",varmap[l.var],"</span>")
end
function writeeqcolor(e,varmap,varocc,m,r)
    s = ""
    for l in e.t
        s = string(s,writelitcolor(l,varmap,varocc,m,r)," ")
    end
    return string(s,">= ",e.b," ;\n")
end
function writedelcolor(f,systemlink,i,succ,index,nbopb,dels)
    isdel = false
    link = systemlink[i-nbopb]
    for k in eachindex(link)
        p = link[k]
        if isid(link,k) && !dels[p] 
            m = maximum(succ[p])
            if m == i
                if !isdel
                    write(f,string("del id "))
                    isdel = true
                end
                dels[p] = true
                write(f,lid(index[p]))
                if index[p] == 0
                    printstyled(string(" index is 0 for ",p," => ",index[p],"\n"); color = :red)                end
            end
        end
    end
    if isdel
        write(f,string("\n"))
    end
end
function makelinefit(len,s)
    if length(s)<len
        return s
    else 
        s = s[1:len-3]
        lastbr1 = findlast('{',s)
        lastbr2 = findlast('}',s)
        if lastbr1===nothing || !(lastbr2===nothing) && lastbr1<lastbr2
            return string(s,"...\n")
        else
            return string(s,"}...\n")
        end
    end
end
function findallindexfirst(index,cone)
    lastindex = 0
    for i in eachindex(cone)
        if cone[i]
            lastindex += 1
            index[i] = lastindex
        end
    end
end
function wid(i)
    return string("<span style=\"background-color: rgb(160,160,0)\" id=\"",i,"\">Id ",i,"</span> ")
end
function lid(i)
    return string("<a href=\"#",i,"\">",i,"</a> ")
end
function writeredcolor(e,varmap,witness,beg,varocc,m,r)
    s = "red "
    for l in e.t
        s = string(s,writelitcolor(l,varmap,varocc,m,r)," ")
    end
    s = string(s,">= ",e.b," ;")
    for l in witness.w
        if l.var>0
            s = string(s,if !l.sign " ~" else " " end, "<span style=\"color: rgb(",Int(round(255*(varocc[l.var]-m)/r)),",0,255)\">",varmap[l.var],"</span>")
        else
            s = string(s," ",-l.var)
        end
    end
    return string(s,beg,"\n")
end
function ciaranshow(path,file,version,system,cone,index,systemlink,succ,redwitness,nbopb,varmap,output,conclusion,obj,prism,varocc)
    dels = zeros(Bool,length(system))
    dels[1:nbopb].=true
    for p in prism
        dels[p].=true # we dont delete red and supproofs because veripb is already doing it
    end
    # dels = ones(Bool,length(system)) # uncomment if you dont want deletions.
    todel = Vector{Int}()
    nbsucc = [if isassigned(succ,i) length(succ[i]) else 0 end for i in eachindex(succ)]
    maxsucc = maximum(nbsucc)
    nbpred = [sum(Int(isid(link,k)) for k in eachindex(link)) for link in systemlink]
    maxpred = maximum(nbpred)
    ID = [i for i in eachindex(cone)]
    m = minimum(varocc)
    r = maximum(varocc) - m
    lastindex = 0
    dir = string(proofs,"/ciaran_show/")
    mkdir2(dir)
    open(string(dir,file,".html"),"w") do f
        write(f,"<html><head><style> a {color: inherit;text-decoration: none;}</style></head><body style=\"font-family: Courier, monospace; background-color:#a9a9a9 \"><pre>\n")
        write(f,"======================   ",file,".opb   ======================   <a href=\"#pbp\" style=\"color: blue;\">Go to pbp</a>\n")
        write(f,obj)
        for i in 1:nbopb
            eq = system[i]
            if cone[i]
                lastindex += 1
                write(f,string(wid(lastindex),writeeqcolor(eq,varmap,varocc,m,r)))
                write(f,printsucc(i,succ[i],nbsucc,maxsucc,index))
            else
                write(f,writeeq(eq,varmap))
            end
        end
        write(f,"<span id=\"pbp\">======================   ",file,".pbp   ======================</span>\n")
        for i in nbopb+1:length(system)
            eq = system[i]
            tlink = systemlink[i-nbopb][1]
            if cone[i]
                lastindex += 1
                if tlink == -1               # rup
                    write(f,string(wid(lastindex),"u ",writeeqcolor(eq,varmap,varocc,m,r)))
                    write(f,printpred(i,systemlink[i-nbopb],nbpred,maxpred,index,nbopb))
                    if length(eq.t)>0 
                        write(f,printsucc(i,succ[i],nbsucc,maxsucc,index))
                        writedelcolor(f,systemlink,i,succ,index,nbopb,dels)
                    end
                elseif tlink == -2           # pol
                    write(f,string(wid(lastindex),writepol(systemlink[i-nbopb],index,varmap)))
                    write(f,writeeqcolor(eq,varmap,varocc,m,r))
                    write(f,printpred(i,systemlink[i-nbopb],nbpred,maxpred,index,nbopb))
                    write(f,printsucc(i,succ[i],nbsucc,maxsucc,index))
                    writedelcolor(f,systemlink,i,succ,index,nbopb,dels)
                elseif tlink == -3           # ia
                    write(f,string(wid(lastindex),"ia ",writeeqcolor(eq,varmap,varocc,m,r)[1:end-1]," ",lid(index[systemlink[i-nbopb][2]]),"\n"))
                    write(f,printpred(i,systemlink[i-nbopb],nbpred,maxpred,index,nbopb))
                    write(f,printsucc(i,succ[i],nbsucc,maxsucc,index))
                    writedelcolor(f,systemlink,i,succ,index,nbopb,dels)
                elseif tlink == -4           # red alone
                    write(f,string(wid(lastindex),writeredcolor(eq,varmap,redwitness[i],"",varocc,m,r)))
                    write(f,printpred(i,systemlink[i-nbopb],nbpred,maxpred,index,nbopb))
                    write(f,printsucc(i,succ[i],nbsucc,maxsucc,index)) # since simple red have no antecedants, they cannot trigger deletions ie they cannot be the last successor of a previous eq
                    dels[i] = true  # we dont delete red statements
                elseif tlink == -5           # rup in subproof
                    write(f,"    ")
                    write(f,string(wid(lastindex),"u ",writeeqcolor(eq,varmap,varocc,m,r)))
                    write(f,"    ",printpred(i,systemlink[i-nbopb],nbpred,maxpred,index,nbopb))
                    if isassigned(succ,i) write(f,"    ",printsucc(i,succ[i],nbsucc,maxsucc,index)) end
                    push!(todel,i)
                elseif tlink == -6           # pol in subproofs
                    write(f,"    ")
                    write(f,string(wid(lastindex),writepol(systemlink[i-nbopb],index,varmap)))
                    write(f,"    ",writeeqcolor(eq,varmap,varocc,m,r))
                    write(f,"    ",printpred(i,systemlink[i-nbopb],nbpred,maxpred,index,nbopb))
                    if isassigned(succ,i) write(f,"    ",printsucc(i,succ[i],nbsucc,maxsucc,index)) end
                    push!(todel,i)
                elseif tlink == -9           # red with begin initial reverse equation (will be followed by subproof)
                    write(f,string(wid(lastindex),writeredcolor(reverse(eq),varmap,redwitness[i]," ; begin",varocc,m,r)))
                    write(f,"    ",printpred(i,systemlink[i-nbopb],nbpred,maxpred,index,nbopb))
                    if isassigned(succ,i) write(f,"    ",printsucc(i,succ[i],nbsucc,maxsucc,index)) end
                    todel = [i]
                    dels[i] = true  # we dont delete red statements
                elseif tlink == -7           # red proofgoal #
                    write(f,"    ",wid(lastindex),"proofgoal #1\n")
                    write(f,"    ",writeeqcolor(eq,varmap,varocc,m,r))
                    write(f,"    ",printpred(i,systemlink[i-nbopb],nbpred,maxpred,index,nbopb))
                    write(f,"    ",printsucc(i,succ[i],nbsucc,maxsucc,index))
                elseif tlink == -8           # red proofgoal normal
                    write(f,string("    ",wid(lastindex),"proofgoal ",lid(index[systemlink[i-nbopb][2]]),"\n"))
                    write(f,"    ",writeeqcolor(eq,varmap,varocc,m,r))
                    write(f,"    ",printpred(i,systemlink[i-nbopb],nbpred,maxpred,index,nbopb))
                    if isassigned(succ,i) write(f,"    ",printsucc(i,succ[i],nbsucc,maxsucc,index)) end
                    push!(todel,i)
                elseif tlink == -10          # red proofgoal end
                    lastindex -= 1
                    write(f,"    end -1\n")
                    next = systemlink[i-nbopb][1]
                    if next != -7 && next !=8  # if no more proofgoals, end the subproof
                        lastindex += 1
                        write(f,"end\n") 
                        for ii in todel
                            writedelcolor(f,systemlink,ii,succ,index,nbopb,dels)
                        end
                    end
                elseif tlink == -20           # solx
                    write(f,string(wid(lastindex),writesol(eq,varmap)))
                    dels[i] = true # do not delete sol
                # elseif tlink == -6           # soli
                    # write(f,writesol(eq,varmap)) #TODO
                    # dels[i] = true # do not delete sol
                else
                    println("ERROR tlink = ",tlink)
                    lastindex -= 1
                end
            else
                if tlink == -1               # rup
                    write(f,writeu(eq,varmap))
                elseif tlink == -2           # pol
                    write(f,writepol(systemlink[i-nbopb],ID,varmap))
                elseif tlink == -3           # ia
                    write(f,writeia(eq,systemlink[i-nbopb][2],ID,varmap))
                elseif tlink == -4           # red alone
                    write(f,writered(eq,varmap,redwitness[i],""))
                elseif tlink == -5           # rup in subproof
                    write(f,"    ")
                    write(f,writeu(eq,varmap))
                elseif tlink == -6           # pol in subproofs
                    write(f,"    ")
                    write(f,writepol(systemlink[i-nbopb],ID,varmap))
                elseif tlink == -9           # red with begin initial reverse equation (will be followed by subproof)
                    write(f,writered(reverse(eq),varmap,redwitness[i]," ; begin"))
                elseif tlink == -7           # red proofgoal #
                    write(f,"    proofgoal #1\n")
                elseif tlink == -8           # red proofgoal normal
                    write(f,string("    proofgoal ",ID[systemlink[i-nbopb][2]],"\n"))
                elseif tlink == -10          # red proofgoal end
                    write(f,"    end -1\n")
                    next = systemlink[i-nbopb][1]
                    if next != -7 && next !=8  # if no more proofgoals, end the subproof
                        write(f,"end\n") 
                    end
                elseif tlink == -20           # solx
                    write(f,writesol(eq,varmap))
                else
                    println("ERROR tlink = ",tlink)
                end
            end
        end
        write(f,"</pre></body></html>")
    end
end
function printtabular(t)
    for i in t 
        println(
        round(Int,i[1])," & ",
        round(Int,i[2])," & ",
        prettybytes(i[3])," & ",
        prettybytes(i[4])," &   ",
        prettypourcent(i[5]),"   & ",
        prettytime(i[6])," & ",
        prettytime(i[7])," &   ",
        prettypourcent(i[8]),"   & ",
        prettytime(i[9])," & ",
        prettytime(i[10])," & ",
        prettytime(i[11])," \\\\\\hline"
        )
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
function plotresultstable()
    table = Vector{Vector{Float64}}()
    open(string(proofs,"/atable"), "r") do f
        for line in eachline(f)
            st = split(line[2:end-2],',')
            t = zeros(Float64,length(st))
            for i in eachindex(st)
                t[i] = parse(Float64,st[i])
            end
            push!(table,t)
        end
    end
    # println(table)
    for t in table # fast times
        print(t[6],'/',t[7],',')
    end
    println()
    for t in table # small times
        print(t[6],'/',min(t[8],20),',')
    end
    println()
    for t in table # fast sizes
        print(t[3]/10^6,'/',t[4]/10^6,',')
    end
    println()
    for t in table # small sizes
        print(t[3]/10^6,'/',t[5]/10^6,',')
    end
    println()
    for t in table # small compared veri times
        print(t[6],'/',t[12],',')
    end
    println()
end
# Print meta comment information (additionnal comments dedicated to analysis)
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
    ti = sort!(collect(keys(com)))
    for i in ti#eachindex(com)
        s = com[i]
        st = split(s,keepempty=false)
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
            # if cone[i] 
            #     if type[1:3] == "hal" println("     ",s) end
            #     if type[1:3] == "deg" println("     ",s) end
            # else
            #     if type[1:3] == "hal" println(s) end
            #     if type[1:3] == "deg" println(s) end
            # end
            if type[1:3] == "adj"
                lastadj = i
                v1 = parse(Int,st[2])
                println(v1," ")
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
# graph and analysis section
function weneedbyid(prefix,map,cone,r,cordvertex=0,vertexdomains=Set{String}())
    cond = x->length(x)>length(prefix) && x[1:length(prefix)]==prefix
    println("\nFor ",prefix," WE NEED:")
    for id in r
        if haskey(map,id)
            if cond(map[id])
                if cone[id]
                    printstyled(map[id],"  "; color = :green)
                end end end end
    println("\n    "," "^length(prefix)," WE DONT NEED:",if cordvertex>0 "  (restrained to D)" else "" end)
    for id in r
        if haskey(map,id)
            if cond(map[id])
                if !cone[id]
                    name = map[id]
                    if cordvertex==0 || name[cordvertex:findlast('e',name)-1] in vertexdomains
                        if (findlast('i',name)===nothing) || name[findlast('i',name)+1:end] in vertexdomains
                        printstyled(map[id],"  "; color = :red)
                end end end end end end
end
function setsfromlabels(cone,invctrmap)
    P = Set{Int}()
    T = Set{Int}()
    for i in eachindex(cone)
        if cone[i]
            if haskey(invctrmap,i)
                s = invctrmap[i]
                if s[1]=='D'
                    if s[end]=='m' 
                        push!(P,parse(Int,s[2:end-1])+1)
                    else
                        push!(P,parse(Int,s[2:end])+1) # We cannot do that becaust it fails on instance LVg6g12 --> we only take the at least one constraint from the verticves 
                    end
                elseif length(s)>3 && s[1:3]=="inj" 
                    push!(T,parse(Int,s[4:end])+1)
                end
            else
                # printstyled("",i,"  "; color = :blue)
            end
        end
    end
    return P,T
end
function verticesfromnames(cone,conelits,system,varmap)
    pp = Set{Int}()
    tt = Set{Int}()
    for i in eachindex(system)
        if cone[i]
            for l in system[i].t
                if !haskey(conelits,i) || l.var in conelits[i]
                    name = varmap[l.var]
                    u = findfirst('_',name)
                    push!(pp,parse(Int,name[2:u-1])+1) # 2 becaust var looks like x1_2
                    push!(tt,parse(Int,name[u+1:end])+1)
                end
            end
        end
    end
    return pp,tt
end
function edgesfromnames(cone,conelits,system,varmap)
    ep = Set{Tuple{Int,Int}}()
    et = Set{Tuple{Int,Int}}()
    pp = Set{Int}()
    tt = Set{Int}()
    for i in eachindex(system)
        if cone[i]
            for l in system[i].t
                if !haskey(conelits,i) || l.var in conelits[i]
                    name = varmap[l.var]
                    u = findfirst('_',name)
                    push!(pp,parse(Int,name[2:u-1])+1) # 2 becaust var looks like x1_2
                    push!(tt,parse(Int,name[u+1:end])+1)
                end
            end
        end
    end
    for p in pp
        for p2 in pp
            if p!=p2
                push!(ep,(p,p2))
                push!(ep,(p2,p))
            end
        end
    end
    for t in tt
        for t2 in tt
            if t!=t2
                push!(et,(t,t2))
                push!(et,(t2,t))
            end
        end
    end
    return pp,tt,ep,et
end
# using Graphs,GraphPlot,Compose,Cairo,Colors # we may not need all that
using Graphs,GraphPlot,Colors
function comparegraphs(file,system,nbopb,cone,conelits,varmap,ctrmap,invctrmap)    
    pattern = target = ""
    path = ""
    ext = ""
    pre = ""
    gp = gt = nothing
    if file[1:3] == "bio"
        pattern = file[4:end-3]
        target = file[end-2:end]
        path = SIPgraphpath*"biochemicalReactions"
        ext = ".txt"
    elseif file[1:2] == "LV"
        i = findlast(x->x=='g',file)
        pattern = file[4:i-1]
        target = file[i+1:end]
        pre = "g"
        path = SIPgraphpath*"LV"
    else
        println("ERROR: cannot compare graphs for file ",file,". The file name should start with bio or LV.")
        return
    end
    gp = ladtograph(path,pre*pattern*ext)
    # gt = ladtograph(path,pre*target*ext)

    P,T,EP,ET = edgesfromnames(cone,conelits,system,varmap)

    # P,T = setsfromlabels(cone,invctrmap) # we cannot do that as we have a counter example that mandatory vertices may have no domain ctrs labels
    np = [i for i in 1:nv(gp)]
    nprgb = [if i in P RGBA(0.0,0.8,0,0.8) else RGBA(0.8,0.0,0.0,0.8) end for i in 1:nv(gp)]
    ewp = [if (src(e),dst(e)) in EP || (dst(e),src(e)) in EP RGBA(0.5,1,0.5,1) else RGBA(0.1,0.1,0.1,0.1) end for e in edges(gp)]
    saveplot(gplot(gp;layout = circular_layout, nodelabel = np, nodefillc = nprgb, edgestrokec  = ewp, plot_size = (16cm, 16cm)),
     visualisationpath*"gp"*file*".svg")
    # nt = [i for i in 1:nv(gt)]
    # ntrgb = [if i in T RGBA(0.0,0.8,0,0.8) else RGBA(0.8,0.0,0.0,0.8) end for i in 1:nv(gt)]
    # ewt = [if (src(e),dst(e)) in ET || (dst(e),src(e)) in ET RGBA(0.5,1,0.5,1) else RGBA(0.1,0.1,0.1,0.1) end for e in edges(gt)]
    # saveplot(gplot(gt;layout = circular_layout, nodelabel = nt, nodefillc = ntrgb, edgestrokec  = ewt, plot_size = (16cm, 16cm)),
    #  visualisationpath*"gt"*file*".svg")
    # gg = makegkwin(gp,4)
    # for (k0,g0) in enumerate(gg)
    #     ec = [if src(e) in P && dst(e) in P RGBA(0.5,1,0.5,1) else RGBA(0.1,0.1,0.1,0.1) end for e in edges(g0)]
    #     saveplot(gplot(g0;layout = circular_layout, nodelabel = np, nodefillc = nprgb, edgestrokec  = ec, plot_size = (16cm, 16cm)), string("gp",k0,".svg"))
    # end
    # gg = makegkwin(gt,4)
    # for (k0,g0) in enumerate(gg)
    #     ec = [if src(e) in T && dst(e) in T RGBA(0.5,1,0.5,1) else RGBA(0.1,0.1,0.1,0.1) end for e in edges(g0)]
    #     saveplot(gplot(g0;layout = circular_layout, nodelabel = nt, nodefillc = ntrgb, edgestrokec  = ec, plot_size = (16cm, 16cm)), string("gt",k0,".svg"))
    # end

    createconegraph(path,pre*pattern*pattern*target*ext,gp,P)
    # createconegraph(path,pre*target*pattern*target*ext,gt,T)

    # println()
end
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
                    add_edge!(g, l, n+1) # +1 because the first node is 0
                end
            end
        end
    end
    return g
end
function add_nei(deb,cur,l,g,A)
    if l == 0 if deb!=cur A[deb,cur] +=1 end
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
function createconegraph(path,file,G,S) #G:graph S:set of mandatory vertices
    IS = [i for i in 1:nv(G) if !(i in S)] # set of absented vertices
    for i in length(IS):-1:1
        rem_vertex!(G,IS[i])
    end
    open(string(path,'/',file),"w"; lock = false) do f
        write(f,string(nv(G),"\n"))
        for i in 1:nv(G)
            st = string(degree(G,i))
            for j in neighbors(G,i)
                st *= " "*string(j-1) # -1 because the first node is 0
            end
            write(f,st,"\n")
        end
    end
end


# ================ Parser ================


function readinstance(path,file)
    system,varmap,ctrmap,obj = readopb(path,file)
    nbopb = length(system)
    system,systemlink,redwitness,solirecord,assertrecord,output,conclusion,version = readveripb(path,file,system,varmap,ctrmap,obj)
    return system,systemlink,redwitness,solirecord,assertrecord,nbopb,varmap,ctrmap,output,conclusion,version,obj
end
function readvar(s,varmap)
    tmp = s[1]=='~' ? s[2:end] : s
    # tmp = split(s,'~')[end]
    if haskey(varmap,tmp)
        return varmap[tmp]
    end
    varmap[tmp] = length(varmap)+1
    return length(varmap)
end
function readeq(st,varmap)
    return readeq(st,varmap,1:2:length(st)-4)
end
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
    return lits,c
end
function readlits(st,varmap,range)
    lits = Vector{Lit}(undef,(length(range)))
    for i in range
        coef = parse(Int,st[i])
        sign = st[i+1][1]!='~'
        var = readvar(st[i+1],varmap)
        lits[(i - range.start)÷range.step+1] = Lit(coef,sign,var)
    end
    sort!(lits,by=x->x.var)
    return lits
end
function readeq(st,varmap,range)
    lits = readlits(st,varmap,range)
    bid = range.start-1+2length(lits)+2
    lits,c = merge(lits)
    eq = Eq(lits,parse(Int,st[bid])-c)
    return eq
end
function readobj(st,varmap)
    return readlits(st,varmap,2:2:length(st)-1)
end
function remove(s,st)
    r = findall(x->x==s,st)
    deleteat!(st,r)
end
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
    return system,varmap,ctrmap,obj
end
function readopb2(path,file)
    system = Eq[]
    varmap = Dict{String,Int}()
    obj = ""
    open(string(path,'/',file,".opb"),"r"; lock = false) do f
        while !eof(f)
            c = peek(f,Char)
            while c == ' ' || c == '\t' || c == '\n'
                if eof(f) break end
                read(f,Char)
                if eof(f) break end
                c = peek(f,Char)
            end
            if eof(f) break end
            if c == '*'
                readuntil(f,'\n',keep=false)
            else
                ss = readuntil(f,';',keep=true)
                st = split(ss,keepempty=false)              # structure of a line is: int var int var ... >= int ; 
                if ss[1] == 'm'
                    obj = readobj(st,varmap)
                else
                    eq = readeq(st,varmap)
                    if length(eq.t)==0 && eq.b==1
                        printstyled(" !opb"; color = :blue)
                    end
                    normcoefeq(eq)
                    push!(system, eq)
                end
            end
        end
    end
    return system,varmap,obj
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
function normlit(l)
    if !l.sign
        return Lit(-l.coef,true,l.var),l.coef
    end
    return l,0
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
    sort!(lits,by=x->x.var)
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
    normcoefeq(eq)
    lits = copy(eq.t)
    for l in lits
        l.coef = ceil(Int,l.coef/d)
    end
    return Eq(lits,ceil(Int,eq.b/d))
end
function weaken(eq,var)                                            # coef should be > 0
    lits = copy(eq.t)
    b = eq.b
    for l in lits
        if l.var==var
            b-=l.coef
            l.coef = 0
        end
    end
    lits = removenulllits(lits) 
    return Eq(lits,b)
end
function saturate(eq)
    for l in eq.t
        l.coef = min(l.coef,eq.b)
    end
end
function copyeq(eq)
    return Eq([Lit(l.coef,l.sign,l.var) for l in eq.t], eq.b)
end
function solvepol(st,system,link,init,varmap,ctrmap,nbopb)
    i = st[2]
    id = i[1]=='@' ? ctrmap[i[2:end]] : parse(Int,i)
    if id<1
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
    if CONFIG.LPsimplif
        p2 = simplepol(res,system,link,nbopb)
    end
    if lastsaturate
        normcoefeq(res)
        saturate(res)
    end
    return res
end
function findfullassi(system,st,init,varmap,prism)
    lits = Vector{Lit}(undef,length(st)-1)
    for i in 2:length(st)
        var = readvar(st[i],varmap)# add the new vars in the varmap
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
        for i in 1:init-1 # can be replaced with efficient unit propagation
            if !inprism(i,prism)
                eq = system[i]
                s = slack(eq,assi)
                if s<0
                    printstyled(" !sol"; color = :red)
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
                        end
                    end
                end
            end
        end
    end
    return assi
end
function solbreakingctr(system,st,init,varmap,prism)
    assi = findfullassi(system,st,init,varmap,prism)
    lits = Vector{Lit}(undef,length(assi))
    for i in eachindex(assi)
        if assi[i]==0
            printstyled(" !FA"; color = :blue)
        else
            lits[i] = Lit(1,assi[i]!=1,i) # we add the negation of the assignement
        end
    end
    return Eq(lits,1)
end
function findbound(system,st,c,varmap,prism,obj,solirecord)
    assi = findfullassi(system,st,c,varmap,prism)
    lits = Vector{Lit}(undef,length(assi))
    for i in eachindex(assi)
        if assi[i]==0
            printstyled(" !FA"; color = :blue)
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
    return Eq(negobj,-b+1)  # -b+1 because we want the bound to be strictly lower
end
function readwitnessvar(s,varmap)
    if s=="0"
        return 0
    elseif s=="1"
        return -1
    else 
        return readvar(s,varmap)
    end
end
function lparse(f)
    ss = readline(f)
    while length(ss)==0 || ss[1]=='*'
        ss = readline(f)
    end
    st = split(ss,keepempty=false)
    type = st[1]
    return type,st
end
function readwitness(st,varmap)
    remove("->",st)
    remove(";",st)
    t = Vector{Lit}(undef,length(st))
    k = 1
    for i in 1:2:length(st)
        j = i+1
        t[i] = Lit(0,st[i][1]!='~',readwitnessvar(st[i],varmap))
        t[j] = Lit(0,st[j][1]!='~',readwitnessvar(st[j],varmap))
    end
    return t
end
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
    return Eq(t,b)
end
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
                    eq = readeq(st,varmap,2:2:length(st)-4)     # can fail if space is missing omg
                    push!(systemlink,[-5])
                elseif type == "p" || type == "pol"
                    push!(systemlink,[-6])
                    eq = solvepol(st,system,systemlink[end],c,varmap,ctrmap,nbopb)
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
    return redid:c-1,pgranges,c
end
function readred(system,systemlink,st,varmap,ctrmap,redwitness,redid,f,prism)
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
    return c+1
end
function readia(st,varmap,ctrmap,eq,c)
    if st[end-2] != ":" 
        eq = readeq(st,varmap,2:2:length(st)-5)
        printstyled("missing ia ID ";color = :red)
    else
        eq = readeq(st,varmap,2:2:length(st)-6)
        l = st[end-1]
        l = l[1]=='@' ? ctrmap[l[2:end]] : parse(Int,l)
        if l<0
            l = c+l
        end
    end
    return eq,l
end
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
            if length(ss)>0
                i = findfirst(x->x=='%',ss)
                if !isnothing(i) # if the comment is at the beginning of the line
                    if ss[1]=='a'
                        # justifyable assertion
                        assertrecord[c] = ss[i+1:end]
                    end
                    if i>1 ss = ss[1:i-1] end # remove the comment
                end
                st = split(ss,keepempty=false)
                if st[1][1]=='@'
                    ctrmap[st[1][2:end]] = c
                    st = st[2:end] # remove the @label
                end
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
    end
    return system,systemlink,redwitness,solirecord,assertrecord,output,conclusion,version
end


# profiling became slow so deactivated by default
# using StatProfilerHTML, ProfileSVG;             # activate this line to unable profiling
# using Profile, PProf
if CONFIG.profile
    # @pprof main()
    # @profilehtml main()             # activate this line to unable profiling
else
    main()
end

# scp arthur@fataepyc-01.dcs.gla.ac.uk:/scratch/matthew/huub2/word_equations_01_track_140-int-.smol.pbp word_equations_01_track_140-int-.smol.pbp
