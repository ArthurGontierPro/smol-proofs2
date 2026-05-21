# This is a PB trimmer made to analyse proofs. If problem, ask arthur.pro.gontier@gmail.com
# julia GlasgowTrimnalyser.jl [options] [instance name or directory of instances]   options: atable sort rand clean verif profile bfs
    const opb = ".opb"
    const pbp = ".pbp"
    const smol = ".smol"
    const version = "3.0"
    const abspath = "/home/arthur_gla/veriPB/subgraphsolver/"
    const proofs = (i = findfirst(x -> isdir(x), ARGS)) === nothing ? abspath*"proofs/" : ARGS[i]
    const inst   = (i = findfirst(x -> isfile(proofs*x*pbp) && isfile(proofs*x*opb), ARGS)) !== nothing ? ARGS[i] : nothing # search for proof
    const BFS    = "bfs"    in ARGS  # BFS propagation: best-reason selection across same-level constraints
    const CLIT   = "clit"   in ARGS  # Clit mode: cone-first conflict analysis with two-pass filter (see conflicttrail(::Clit))
    const ATABLE = "atable" in ARGS  # print TikZ scatter plot from existing .out files
    const CLEAN  = "clean"  in ARGS  # delete all .out/.err files and vis intermediates (keeps .svg)
    const RAND   = "rand"   in ARGS  # shuffle instance order
    const SORT   = "sort"   in ARGS  # sort instances by file size (ascending)
    const VERIF  = "verif"  in ARGS  # run VeriPB on trimmed output after each instance
    const PROFILE = "profile" in ARGS  # enable StatProfilerHTML profiling
    const NONORM  = "no"     in ARGS  # does not run normal (not official)
    const CORE    = "core"   in ARGS  # write unsat core graph files and reduced LAD files
    const SOLVE   = "solve"  in ARGS  # run SIP solver on original graphs before trimming
    const RESOLV  = "resolv" in ARGS  # re-solve on core reduced graphs after trimming (implies CORE)
    const SIPgraphpath  = "/home/arthur_gla/veriPB/newSIPbenchmarks/"
    const sipsolverpath = "/home/arthur_gla/veriPB/subgraphsolver/glasgow-subgraph-solver/build/glasgow_subgraph_solver"
    const solvertimeout = 300  # seconds
    using Random,DataStructures
# =============== main stuff =============
    const argflags = Set(["bfs","clit","core","verif","no","rand","sort","clean","atable","profile","solve","resolv"])

    function main()
        if ATABLE plotresultstable(); return
        elseif CLEAN
            rm.(filter(f -> endswith(f, ".out") || endswith(f, ".err"), readdir(proofs; join=true)))
            visdir = proofs * "vis/"
            if isdir(visdir)
                rm.(filter(f -> any(endswith(f, e) for e in (".lad", ".dot")), readdir(visdir; join=true)))
            end
            return
        elseif inst !== nothing
            trimnalyseandcie(inst); return
        elseif SOLVE || RESOLV
            # proof files don't exist yet: find instance name by bio/LV prefix in ARGS
            j = findfirst(x -> x ∉ argflags && !isdir(x) &&
                               (startswith(x,"LV") || startswith(x,"bio")), ARGS)
            if j !== nothing
                trimnalyseandcie(ARGS[j]); return
            end
        end
        println(tabhead)
        for ins in getinstancesfromdir(proofs)
            trimnalyseandcie(ins)
        end
        println(tabfoot) end

    function getinstancesfromdir(proofs)
        list = onlyname.(filter(x -> ext(x)==opb && isfile(noext(x)*pbp), readdir(proofs, join=true)))
        if RAND shuffle!(list)
        elseif SORT sort!(list, by = x -> inssize(x)) end
        println("%Found ", length(list), " instances in ", proofs)
        return list end
        
    function trimnalyseandcie(ins)
            tryrm(proofs*ins*".out")
            if SOLVE
                patfile, tarfile = parsegraphfiles(ins)
                if patfile === nothing
                    printstyled("  solve: cannot parse graph paths for $ins\n"; color=:red)
                    return
                end
                t = @elapsed ok = runsipsolver(ins, patfile, tarfile)
                if !ok
                    printstyled("  solve failed or timed out for $ins ($(round(t;digits=1))s)\n"; color=:red)
                    return
                end
                printstyled("  solved $(round(t;digits=1))s\n"; color=:cyan)
            end
            if !NONORM
                printabline(ins)
                t1,t2,t3 = trimnalyse(ins; mode=Grim())
                t4,t5 = VERIF ? verify(ins) : (-1,-1)
                printabline2(ins,t1,t2,t3,t4,t5)
                writeout_verif(ins,t4,t5)
                RESOLV && resolvecore(ins)
            end
            if CLIT
                printabline(ins)
                tc1,tc2,tc3 = trimnalyse(ins; mode=Clit())
                tc4,tc5 = VERIF ? verify(ins) : (-1,-1)
                printabline2(ins,tc1,tc2,tc3,tc4,tc5)
                writeout_verif(ins,tc4,tc5)
            end
            if BFS
                printabline(ins)
                tb1,tb2,tb3 = trimnalyse(ins; mode=Bfs())
                tb4,tb5 = VERIF ? verify(ins) : (-1,-1)
                printabline2(ins,tb1,tb2,tb3,tb4,tb5)
                writeout_verif(ins,tb4,tb5)
            end end

        # mode: Grim(), Clit(), or Bfs() — see mode structs
    function trimnalyse(ins; mode=Grim())
        prefix = mode isa Bfs ? "gbfs" : mode isa Clit ? "gclt" : "grim"
        t1 = t2 = t3 = 0 ; file = ins
        # if "load" in ARGS file,system,systemlink,redwitness,solirecord,assertrecord,nbopb,varmap,ctrmap,output,conclusion,obj,invsys,prism,cone,conelits,invctrmap,succ,index = loadsys(file); @goto skiped end # using goto because I was told not to
        t1 = @elapsed begin
            system,systemlink,redwitness,solirecord,assertrecord,nbopb,varmap,ctrmap,output,conclusion,obj,prism = readinstance(proofs,file)
        end
        inp_lits = sum(length(eq.t) for eq in system; init=0)
        writeout_parse(ins, t1, nbopb, length(systemlink), inp_lits, length(varmap), prefix)
        sys = PBSystem(system, length(varmap))
        n = length(sys.rhs)
        cone     = zeros(Bool, n)
        conelits = Dict{Int,Set{Int}}()
        t2 = @elapsed begin
            getcone!(cone, conelits, sys, systemlink, nbopb, prism, redwitness, conclusion, obj, mode)
        end
        # for (i,_) in conelits # nullify the conelits
        #     conelits[i] = Set{Int}(Int(sys.vars[k]) for k in eqrange(sys, i))
        # end
        writeout_trim(ins, t2, cone, nbopb, prefix)
        writeout_conelits(ins, sys, cone, conelits, prefix)
        printconestat(cone, sys, conelits)
        # @label skiped
        varmap_inv = Vector{String}(undef, length(varmap))
        for (k, v) in varmap; varmap_inv[v] = k; end
        mode isa Grim && (CORE || RESOLV) && writeunsatcore(ins, sys, cone, conelits, varmap_inv, nbopb)
        t3 = @elapsed begin
            writeconedel(proofs,file,sys,cone,conelits,systemlink,redwitness,solirecord,assertrecord,nbopb,varmap_inv,ctrmap,output,conclusion,obj,prism)
        end
        writeout_write(ins, t1, t2, t3, prefix)
        return trunc(Int,t1),trunc(Int,t2),trunc(Int,t3) end

    function writeout_parse(ins, t1, nbopb, n_pbp, inp_lits, inp_vars, prefix)
        opb_sz = filesize(proofs*ins*opb)
        pbp_sz = filesize(proofs*ins*pbp)
        open(proofs*ins*".out", "a") do f
            println(f, "inp OPB SIZE ",   opb_sz)
            println(f, "inp PBP SIZE ",   pbp_sz)
            println(f, "inp SIZE ",       opb_sz + pbp_sz)
            println(f, "inp LIT ",        inp_lits)
            println(f, "inp VAR ",        inp_vars)
            println(f, prefix, " PARSE TIME ", t1)
            println(f, prefix, " OPB NBEQ ",  nbopb)
            println(f, prefix, " PBP NBEQ ",  n_pbp)
            println(f, prefix, " NBEQ ",      nbopb + n_pbp)
        end end

    function writeout_trim(ins, t2, cone, nbopb, prefix)
        cone_opb = sum(cone[1:nbopb])
        cone_pbp = sum(cone[nbopb+1:end])
        open(proofs*ins*".out", "a") do f
            println(f, prefix, " TRIM TIME ", t2)
            println(f, prefix, " OPB CONE ",  cone_opb)
            println(f, prefix, " PBP CONE ",  cone_pbp)
            println(f, prefix, " CONE ",      cone_opb + cone_pbp)
        end end

    function conelits_stats(sys, cone, conelits)
        lits_cone = 0; lits_smol = 0
        used_vars = falses(length(sys.var_ptr) - 1)
        for i in eachindex(cone)
            cone[i] || continue
            nl = length(eqrange(sys, i))
            lits_cone += nl
            lits_smol += haskey(conelits, i) ? length(conelits[i]) : nl
            haskey(conelits, i) && for v in conelits[i]; used_vars[v] = true; end
        end
        return (lits_cone=lits_cone, lits_smol=lits_smol, vars_used=sum(used_vars), vars_total=length(used_vars)) end

    function writeout_conelits(ins, sys, cone, conelits, prefix)
        s = conelits_stats(sys, cone, conelits)
        open(proofs*ins*".out", "a") do f
            println(f, prefix, " CONE LIT ", s.lits_cone)
            println(f, prefix, " SMOL LIT ", s.lits_smol)
            println(f, prefix, " CONE VAR ", s.vars_used)
        end end

    function writeout_write(ins, t1, t2, t3, prefix)
        open(proofs*ins*".out", "a") do f
            println(f, prefix, " WRITE TIME ", t3)
            println(f, prefix, " TIME ",       t1+t2+t3)
            println(f, prefix, " OPB SIZE ",   filesize(proofs*ins*opb*smol))
            println(f, prefix, " PBP SIZE ",   filesize(proofs*ins*pbp*smol))
            println(f, prefix, " SIZE ",       filesize(proofs*ins*opb*smol) + filesize(proofs*ins*pbp*smol))
        end end

    function writeout_verif(ins, t4, t5)
        t4 < 0 && t5 < 0 && return
        open(proofs*ins*".out", "a") do f
            t4 >= 0 && println(f, "veri smol TIME ", t4)
            t5 >= 0 && println(f, "veri TIME ",      t5)
        end end

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
        tryrm(ins31); tryrm(ins32)
        t4 = @elapsed try run(pipeline(`$veripb $ins2$opb$smol $ins2$pbp$smol`,stdout=ins31,stderr=ins32)) catch e println("\nerr ",ins32) end
        tryrm(ins41); tryrm(ins42)
        t5 = @elapsed try run(pipeline(`$veripb $ins2$opb $ins2$pbp`,stdout=ins41,stderr=ins42)) catch e println("\nerr ",ins42) end
        return trunc(Int,t4),trunc(Int,t5) end


# ======================================= plotting  ======================================= #
    # Column index constants for the results table
        const T_FILE       =  1
        const T_GRIM_TIME  =  2
        const T_GRIM_OSIZ  =  3
        const T_GRIM_PSIZ  =  4
        const T_GRIM_SIZE  =  5
        const T_VERI_STIME =  6
        const T_VERI_TIME  =  7
        const T_VERI_OSIZ  =  8
        const T_VERI_PSIZ  =  9
        const T_VERI_SIZE  = 10
        const T_BRIM_TIME  = 11
        const T_BRIM_OSIZ  = 12
        const T_BRIM_PSIZ  = 13
        const T_BRIM_SIZE  = 14
        const T_GRIM_PTIME = 15  # parse time
        const T_GRIM_TTIME = 16  # trim (getcone) time
        const T_GRIM_WTIME = 17  # write time
        const T_GRIM_OCONE = 18  # OPB constraints in cone
        const T_GRIM_PCONE = 19  # proof steps in cone
        const T_GRIM_CONE  = 20  # total constraints in cone
        const T_GRIM_ONBEQ = 21  # total OPB constraints (input)
        const T_GRIM_PNBEQ = 22  # total proof steps (input)
        const T_INP_OSIZ   = 23  # input OPB file size
        const T_INP_PSIZ   = 24  # input PBP file size
        const T_INP_SIZE   = 25  # input total file size
        const T_GRIM_NBEQ  = 26  # total equations (OPB + PBP)
        const T_GBFS_TTIME = 27  # BFS trim (getcone) time
        const T_GBFS_OCONE = 28  # BFS OPB constraints in cone
        const T_GBFS_PCONE = 29  # BFS proof steps in cone
        const T_GBFS_CONE  = 30  # BFS total constraints in cone
        const T_GRIM_CLIT  = 31  # total literals in grim cone constraints
        const T_GRIM_SLIT  = 32  # total literals kept after conelits weakening (grim)
        const T_GBFS_CLIT  = 33  # total literals in gbfs cone constraints
        const T_GBFS_SLIT  = 34  # total literals kept after conelits weakening (gbfs)
        const T_INP_LIT    = 35  # total literals in all input constraints
        const T_INP_VAR    = 36  # total variables in input
        const T_GRIM_CVAR  = 37  # distinct variables in union of grim conelits
        const T_GBFS_CVAR  = 38  # distinct variables in union of gbfs conelits
        const T_GCLT_TTIME = 39  # clit trim (getcone) time
        const T_GCLT_OCONE = 40  # clit OPB constraints in cone
        const T_GCLT_PCONE = 41  # clit proof steps in cone
        const T_GCLT_CONE  = 42  # clit total constraints in cone
        const T_GCLT_CLIT  = 43  # total literals in clit cone constraints
        const T_GCLT_SLIT  = 44  # total literals kept after conelits weakening (clit)
        const T_GCLT_CVAR  = 45  # distinct variables in union of clit conelits
        const T_NCOLS      = 45

    function plotresultstable()
        list = filter(x -> ext(x)==".out" && !endswith(x,".smolverif.out") && !endswith(x,".verif.out"), readdir(proofs))
        list = onlyname.(list)
        table = Vector{Vector{Any}}()
        for file in list
            res = Any[file; fill(nothing, T_NCOLS - 1)]
            for line in eachline(proofs*file*".out")
                    if occursin("grim PARSE TIME ", line)    res[T_GRIM_PTIME]= tryparse(Int, split(line)[end])
                elseif occursin("grim TRIM TIME ", line)     res[T_GRIM_TTIME]= tryparse(Int, split(line)[end])
                elseif occursin("grim WRITE TIME ", line)    res[T_GRIM_WTIME]= tryparse(Int, split(line)[end])
                elseif occursin("grim TIME ", line)          res[T_GRIM_TIME] = tryparse(Int, split(line)[end])
                elseif occursin("grim OPB SIZE ", line)      res[T_GRIM_OSIZ] = tryparse(Int, split(line)[end])
                elseif occursin("grim PBP SIZE ", line)      res[T_GRIM_PSIZ] = tryparse(Int, split(line)[end])
                elseif occursin("grim SIZE ", line)          res[T_GRIM_SIZE] = tryparse(Int, split(line)[end])
                elseif occursin("grim OPB CONE ", line)      res[T_GRIM_OCONE]= tryparse(Int, split(line)[end])
                elseif occursin("grim PBP CONE ", line)      res[T_GRIM_PCONE]= tryparse(Int, split(line)[end])
                elseif occursin("grim CONE LIT ", line)      res[T_GRIM_CLIT] = tryparse(Int, split(line)[end])
                elseif occursin("grim SMOL LIT ", line)      res[T_GRIM_SLIT] = tryparse(Int, split(line)[end])
                elseif occursin("grim CONE VAR ", line)      res[T_GRIM_CVAR] = tryparse(Int, split(line)[end])
                elseif occursin("grim CONE ", line)          res[T_GRIM_CONE] = tryparse(Int, split(line)[end])
                elseif occursin("grim OPB NBEQ ", line)      res[T_GRIM_ONBEQ]= tryparse(Int, split(line)[end])
                elseif occursin("grim PBP NBEQ ", line)      res[T_GRIM_PNBEQ]= tryparse(Int, split(line)[end])
                elseif occursin("inp OPB SIZE ", line)       res[T_INP_OSIZ]  = tryparse(Int, split(line)[end])
                elseif occursin("inp PBP SIZE ", line)       res[T_INP_PSIZ]  = tryparse(Int, split(line)[end])
                elseif occursin("inp SIZE ", line)           res[T_INP_SIZE]  = tryparse(Int, split(line)[end])
                elseif occursin("inp LIT ", line)            res[T_INP_LIT]   = tryparse(Int, split(line)[end])
                elseif occursin("inp VAR ", line)            res[T_INP_VAR]   = tryparse(Int, split(line)[end])
                elseif occursin("grim NBEQ ", line)          res[T_GRIM_NBEQ] = tryparse(Int, split(line)[end])
                elseif occursin("gclt TRIM TIME ", line)     res[T_GCLT_TTIME]= tryparse(Int, split(line)[end])
                elseif occursin("gclt OPB CONE ", line)      res[T_GCLT_OCONE]= tryparse(Int, split(line)[end])
                elseif occursin("gclt PBP CONE ", line)      res[T_GCLT_PCONE]= tryparse(Int, split(line)[end])
                elseif occursin("gclt CONE LIT ", line)      res[T_GCLT_CLIT] = tryparse(Int, split(line)[end])
                elseif occursin("gclt SMOL LIT ", line)      res[T_GCLT_SLIT] = tryparse(Int, split(line)[end])
                elseif occursin("gclt CONE VAR ", line)      res[T_GCLT_CVAR] = tryparse(Int, split(line)[end])
                elseif occursin("gclt CONE ", line)          res[T_GCLT_CONE] = tryparse(Int, split(line)[end])
                elseif occursin("gbfs TRIM TIME ", line)     res[T_GBFS_TTIME]= tryparse(Int, split(line)[end])
                elseif occursin("gbfs OPB CONE ", line)      res[T_GBFS_OCONE]= tryparse(Int, split(line)[end])
                elseif occursin("gbfs PBP CONE ", line)      res[T_GBFS_PCONE]= tryparse(Int, split(line)[end])
                elseif occursin("gbfs CONE LIT ", line)      res[T_GBFS_CLIT] = tryparse(Int, split(line)[end])
                elseif occursin("gbfs SMOL LIT ", line)      res[T_GBFS_SLIT] = tryparse(Int, split(line)[end])
                elseif occursin("gbfs CONE VAR ", line)      res[T_GBFS_CVAR] = tryparse(Int, split(line)[end])
                elseif occursin("gbfs CONE ", line)          res[T_GBFS_CONE] = tryparse(Int, split(line)[end])
                elseif occursin("veri smol TIME ", line)     res[T_VERI_STIME]= tryparse(Int, split(line)[end])
                elseif occursin("veri TIME ", line)          res[T_VERI_TIME] = tryparse(Int, split(line)[end])
                elseif occursin("veri OPB SIZE ", line)      res[T_VERI_OSIZ] = tryparse(Int, split(line)[end])
                elseif occursin("veri PBP SIZE ", line)      res[T_VERI_PSIZ] = tryparse(Int, split(line)[end])
                elseif occursin("veri SIZE ", line)          res[T_VERI_SIZE] = tryparse(Int, split(line)[end])
                elseif occursin("brim TIME ", line)          res[T_BRIM_TIME] = tryparse(Int, split(line)[end])
                elseif occursin("brim OPB SIZE ", line)      res[T_BRIM_OSIZ] = tryparse(Int, split(line)[end])
                elseif occursin("brim PBP SIZE ", line)      res[T_BRIM_PSIZ] = tryparse(Int, split(line)[end])
                elseif occursin("brim SIZE ", line)          res[T_BRIM_SIZE] = tryparse(Int, split(line)[end])
                end
            end
            push!(table,res)
        end
        printpoints2Dlog(table, T_GRIM_CONE, T_GBFS_CONE, "grim CONE", "gbfs CONE")
        printratios(table) end

        # 1-shifted geometric mean of a column: exp(mean(log(v + 1))) - 1.
    function col_sgm(table, col)
        valid = [t[col] for t in table if t[col] !== nothing && t[col] > 0]
        isempty(valid) && return nothing
        exp(sum(log(v + 1) for v in valid) / length(valid)) - 1 end

        # Ratio of the 1-shifted geomeans of two columns, restricted to rows where both are present.
        # This gives "ratio of averages" rather than "average of ratios".
    function ros(table, col_num, col_den)
        valid = [t for t in table if t[col_num] !== nothing && t[col_den] !== nothing && t[col_num] > 0 && t[col_den] > 0]
        isempty(valid) && return nothing
        sgm_num = exp(sum(log(t[col_num] + 1) for t in valid) / length(valid)) - 1
        sgm_den = exp(sum(log(t[col_den] + 1) for t in valid) / length(valid)) - 1
        sgm_den == 0 && return nothing
        sgm_num / sgm_den end

    function printratios(table)
        # "X times smaller, Y% of original" — for reductions where bigger ratio = better
        fmt_r(x) = x === nothing ? "N/A" :
            "$(rpad(string(round(x; digits=1))*"x smaller,", 14)) $(round(100/x; digits=1))% of original"
        # plain percentage — for the trim-time fraction (already a ratio ≤ 1)
        fmt_p(x) = x === nothing ? "N/A" : "$(round(100*x; digits=1))% of total time"
        n = count(t -> t[T_GRIM_SIZE] !== nothing, table)
        println("\n── Proof reduction (ratio of 1-shifted geomeans, n=", n, ") ──")
        println("  size        : ", fmt_r(ros(table, T_INP_SIZE,  T_GRIM_SIZE)))
        println("  constraints : ", fmt_r(ros(table, T_GRIM_NBEQ, T_GRIM_CONE)))
        println("  literals    : ", fmt_r(ros(table, T_GRIM_CLIT, T_GRIM_SLIT)))
        println("  variables   : ", fmt_r(ros(table, T_INP_VAR,   T_GRIM_CVAR)))
        # println("  trim time   : ", fmt_p(ros(table, T_GRIM_TTIME, T_GRIM_TIME)))
        any(t -> t[T_GCLT_SLIT] !== nothing, table) && begin
            # println("  clit lits   : ", fmt_r(ros(table, T_GRIM_SLIT, T_GCLT_SLIT)), "  vs grim")
            # println("  clit vars   : ", fmt_r(ros(table, T_GRIM_CVAR, T_GCLT_CVAR)), "  vs grim")
        end
        any(t -> t[T_VERI_TIME] !== nothing, table) && begin
            println("  verif speed : ", fmt_r(ros(table, T_VERI_TIME, T_VERI_STIME)))
        end
        println() end

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
    function printconestat(cone, sys, conelits)
        s = conelits_stats(sys, cone, conelits)
        printgray("\r\033[99G% "*string(sum(cone))*"/"*string(length(cone))*" "
                                *string(s.vars_used)*"/"*string(s.vars_total)) end

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

    struct Lit
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
        c = 0
        for i in eachindex(eq.t)
            l = eq.t[i]
            if l.coef < 0
                eq.t[i] = Lit(-l.coef, !l.sign, l.var)
                c += -l.coef
            end
        end
        eq.b = c + eq.b end
 
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

    mutable struct Red
        w::Vector{Lit}                      # flat pairs: w[2k-1]=source var, w[2k]=target var (var=0 → const-0, var=-1 → const-1)
        range::UnitRange{Int64}             # system id range of the entire red block (reversed negation → conclusion)
        pgranges::Vector{UnitRange{Int64}} end  # id ranges of individual proof goals inside the block

    function processrup(st,varmap,systemlink)
        push!(systemlink,[-1])
        return readeq(st,varmap,2:2:length(st)) end

    function processpol(st,varmap,system,systemlink,c,ctrmap,nbopb)
        push!(systemlink,[-2])
        eq = solvepol(st,system,systemlink[end],c,varmap,ctrmap,nbopb)
        if !(length(eq.t)!=0 || eq.b!=0) throw("POL empty") end
        return eq end 

        # Evaluates a pol (polynomial combination) line and records its structure in `link`.
        # link encoding: positive values = constraint ids; negative sentinels below:
        #   -1=+  -2=*  -3=d  -4=s  -5=w  -(100v+99)=literal axiom var v positive  -(100v+100)=negative
        # (The -(100v+99/100) scheme reserves negatives ≤ -99 for literals, leaving -1..-5 for operators.)
    function solvepol(st,system,link,init,varmap,ctrmap,nbopb)
        i = st[2]
        id = i[1]=='@' ? ctrmap[i[2:end]] : parse(Int,i)
        if id<0
            id = init+id                               # negative ids are relative to current position
        end
        eq = copyeq(system[id])
        stack = Vector{Eq}()
        weakvar = ""
        push!(stack,eq)
        push!(link,id)
        lastsaturate = false                           # defer final saturate: apply after null-lit removal
        for j in 3:length(st)
            i=st[j]
            if i == ";"
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
                    lastsaturate = true                # last op: defer so null lits are removed first
                else
                    normcoefeq(first(stack))
                    saturate(first(stack))
                end
                push!(link,-4)
            elseif i=="w"
                push!(stack,weaken(pop!(stack),weakvar))
                push!(link,-5)
            elseif !isdigit(i[1]) && i[1]!='@' && i[1]!='-'  # literal axiom: push unit constraint for this var
                if length(st)>j && st[j+1] == "w"
                    weakvar = readvar(i,varmap)
                    push!(link,-100weakvar-99)         # encode as weakening target (no stack push)
                else
                    sign = i[1]!='~'
                    var = readvar(i,varmap)
                    push!(stack,Eq([Lit(1,sign,var)],0))
                    push!(link,-100var-99sign)         # encode literal: -(100v+99) if positive, -(100v+100) if negative
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
            link[1] = -3                               # pol with single antecedent and no ops is really an ia
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
        lits = [Lit(l.coef*d, l.sign, l.var) for l in eq.t]
        return Eq(lits,eq.b*d) end

    function divide(eq,d)
        normcoefeq(eq)
        lits = [Lit(ceil(Int,l.coef/d), l.sign, l.var) for l in eq.t]
        return Eq(lits,ceil(Int,eq.b/d)) end

    function saturate(eq)
        for i in eachindex(eq.t)
            l = eq.t[i]
            l.coef > eq.b && (eq.t[i] = Lit(eq.b, l.sign, l.var))
        end end

    function weaken(eq,var)
        lits = Lit[]
        b = eq.b
        for l in eq.t
            if l.var==var
                b -= l.coef
            else
                push!(lits, l)
            end
        end
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
        if i==j                                        # no second ':' means no witness range — witness ends at "begin"
            j=length(st)
        end
        w = readwitness(st[i+1:j],varmap)
        c = redid
        range = 0:0
        pgranges = Vector{UnitRange{Int64}}()
        if st[end] == "begin"
            rev = reverse(eq)
            normcoefeq(rev)
            push!(system,rev)                          # slot redid: reversed negation of eq (tlink -9), hidden in prism
            push!(systemlink,[-9])
            c+=1
            range,pgranges,c = readsubproof(system,systemlink,eq,w,c,f,varmap,ctrmap)
            push!(prism,range)                         # mark entire subproof range as internal (invisible to cone outside)
            push!(systemlink,[-10])                    # slot before conclusion: end-of-subproof marker
        else
            push!(systemlink,[-4])                     # inline red (no subproof)
        end
        normcoefeq(eq)
        push!(system,eq)                               # final slot: the red conclusion itself
        redwitness[redid] = Red(w,range,pgranges)      # keyed at redid (start of block) for subproof lookups
        redwitness[length(system)] = Red(w,range,pgranges)  # also keyed at conclusion slot (used by getcone via tlink -10)
        return c+1,Eq([],0) end

        # Witness is stored as flat pairs: t[2k-1]=source variable, t[2k]=target variable.
        # sign on source encodes polarity of the substitution; sign on target encodes direction.
    function readwitness(st,varmap)
        st = remove(st,"->")
        st = remove(st,";")
        t = Vector{Lit}(undef,length(st))
        for i in 1:2:length(st)
            j = i+1
            t[i] = Lit(0,st[i][1]!='~',readwitnessvar(st[i],varmap))  # source
            t[j] = Lit(0,st[j][1]!='~',readwitnessvar(st[j],varmap))  # target
        end
        return t end

    function readwitnessvar(s,varmap)
        if s=="0"
            return 0           # constant 0
        elseif s=="1"
            return -1          # constant 1 (negative sentinel, not a real var id)
        else
            return readvar(s,varmap)
        end end
            
        # Reads the body of a "red ... begin ... end" block.
        # Each proof goal must derive a contradiction from: formula constraints + ~C (negated red eq) + witness substitutions.
        # proofgoal i  = i-th formula constraint with witness applied
        # proofgoal #1 = the red constraint itself with witness applied
        # within a proof goal, id -1 refers to the constraint declared by the proofgoal line (after witness substitution)
    function readsubproof(system,systemlink,eq,w,c,f,varmap,ctrmap)
        nbopb = length(system)-length(systemlink)  # invariant: system has nbopb more entries than systemlink (the opb constraints)
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
                        eq = processrup(st,varmap,systemlink)
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

        # Substitutes witness w into eq: mapped variables are evaluated to 0 or 1 and absorbed into the RHS.
        # If target var > 0: literal is mapped to a variable (handled elsewhere); here we just adjust b.
        # If target var ≤ 0: literal is mapped to a constant — subtract coef from b if the literal is satisfied by the constant.
    function applywitness(eq, w)
        witness_idx = Dict{Int,Int}(w[i].var => i for i in 1:2:length(w))  # source var → index in w
        t = Lit[]
        b = eq.b
        for l in eq.t
            idx = get(witness_idx, l.var, 0)
            if idx != 0
                if w[idx+1].var > 0                    # target is a variable: literal survives (sign may flip)
                    l.sign != w[idx].sign && (b -= l.coef)
                else                                   # target is a constant: evaluate and fold into b
                    l.sign == w[idx].sign && (b -= l.coef)
                end
            else
                push!(t, l)                            # unmapped variable: keep as-is
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
        var_eqs ::Vector{Int32} end # flat list of equation ids

    mutable struct Trail
        var  ::Vector{Int32}    # variables in propagation order
        eq   ::Vector{Int32}    # reason equation for each entry
        pos  ::Vector{Int}      # pos[v] = index in var/eq (0 = unassigned)
        assi ::Vector{Int8} end # current assignment (1=true, 2=false, 0=unset)

# ======================================== Trimmer =====================================
    Trail(n_vars::Int) = Trail(Int32[], Int32[], zeros(Int, n_vars), zeros(Int8, n_vars))
    @inline function reset!(t::Trail)
        empty!(t.var); empty!(t.eq)
        fill!(t.pos, 0); fill!(t.assi, 0) end

        # Level-0 base propagation: single forward pass through all constraints (OPB then PBP).
        # Monotone index order guarantees that if Cⱼ depends on a variable forced by Cᵢ (i<j),
        # then reason(v) = Cᵢ < Cⱼ. This makes init-based filtering in reset_to_base! safe:
        # including an entry with reason ≤ init implies all its dependencies also have reason ≤ init.
        # No fixpoint loop: chained OPB propagations are intentionally excluded — they commit to
        # reason chains that may not be needed for trimming and are better resolved by minimize_reasons!
    function propagate_level0!(sys::PBSystem, t::Trail)
        for i in 1:length(sys.rhs)
            s = slack(sys, i, t.assi)
            s < 0 && return
            @inbounds for k in eqrange(sys, i)
                v = Int(sys.vars[k])
                t.assi[v] != 0 && continue
                sys.coefs[k] > s || continue
                pushtrail!(t, Int32(v), Int32(i), sys.signs[k] ? Int8(1) : Int8(2))
            end
        end end

        # Reset trail to base state, filtering out entries whose reason >= init.
        # OPB entries (reason ≤ nbopb ≤ any init) are always included.
        # PBP entries with reason < init are included; reason == init is excluded because
        # constraint init is the one being proved (using it as a reason is circular).
    @inline function reset_to_base!(t::Trail, base::Trail, init::Int)
        empty!(t.var); empty!(t.eq)
        fill!(t.pos, 0); fill!(t.assi, 0)
        for k in 1:length(base.var)
            Int(base.eq[k]) >= init && continue            # exclude init itself and anything beyond
            pushtrail!(t, base.var[k], base.eq[k], base.assi[Int(base.var[k])])
        end end

    struct Ante
        flags::Vector{Bool}   # O(1) membership
        list ::Vector{Int} end# O(k) iteration; may contain stale (false) entries

    Ante(n::Int) = Ante(zeros(Bool, n), Int[])

    struct RupState                                    # reusable scratch buffers — allocated once in getcone
        que           ::BitVector                      # ruptrail equation queue
        pq_prio       ::BinaryMinHeap{Int}             # priority equations (cone/on_frontier)
        pq_nonprio    ::BinaryMinHeap{Int}             # non-priority equations
        to_explain    ::BinaryMaxHeap{Int}             # conflicttrail: trail positions still needing explanation
        is_to_explain ::BitVector                      # membership guard for to_explain (self-cleaning)
        falsified_lits::Vector{Tuple{Int,Int,Int,Int32}} # conflicttrail: reused per-iteration buffer
        essentials    ::Dict{Int,Set{Int}} end           # forward-pass: essential vars per constraint (Clit only)

    # Trimming mode — passed through getcone! → ruptrail → process_eq! → conflicttrail.
    # To add a new mode: define a new struct + a conflicttrail method. Nothing else changes.
    struct Grim end        # standard: proof-index sort in conflict analysis
    struct Clit end        # cone-first sort + essentials-aware filter in conflict analysis
    struct Bfs  end        # BFS propagation with wave-level reason selection (ruptrail_bfs)

    RupState(n_eqs::Int, n_vars::Int) = RupState(
        falses(n_eqs),
        BinaryMinHeap{Int}(),
        BinaryMinHeap{Int}(),
        BinaryMaxHeap{Int}(),
        falses(n_vars + 1),
        Tuple{Int,Int,Int,Int32}[],
        Dict{Int,Set{Int}}())
    # Forward pass: variable w is essential in constraint e if removing it makes e infeasible
    # (total coef - coef_w < rhs[e]). Essential vars must stay in conelits — weakening them out
    # would make the constraint unsatisfiable and break the proof. Only called for Clit mode.
    function compute_essentials!(essentials::Dict{Int,Set{Int}}, sys::PBSystem)
        for e in 1:length(sys.rhs)
            total = sum(sys.coefs[k] for k in eqrange(sys, e); init=zero(Int32))
            for k in eqrange(sys, e)
                if total - sys.coefs[k] < sys.rhs[e]
                    push!(get!(Set{Int}, essentials, e), Int(sys.vars[k]))
                end
            end
        end end

    @inline function ante_set!(a::Ante, i::Int)
        a.flags[i] && return                          # already registered: avoid list duplicate
        a.flags[i] = true; push!(a.list, i) end

    @inline ante_remove!(a::Ante, i::Int) = (a.flags[i] = false)  # O(1): leave stale entry in list
    @inline function ante_clear!(a::Ante)
        for i in a.list; a.flags[i] = false; end; empty!(a.list) end  # walk list to unset flags, then truncate

    @inline function pushtrail!(t::Trail, v::Int32, eq::Int32, val::Int8)
        push!(t.var, v); push!(t.eq, eq)
        iv = Int(v)
        @inbounds t.pos[iv] = length(t.var)   # trail index of v (0 = unassigned)
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
    function slack(eq::Eq, assi::Vector{Int8})
        c = 0
        for l in eq.t
            val = assi[l.var]
            (val == 0 || (l.sign && val == 1) || (!l.sign && val == 2)) && (c += l.coef)
        end
        return c - eq.b end

    @inline function slack(sys::PBSystem, e::Int, assi::Vector{Int8})
        c = zero(Int32)
        @inbounds for i in eqrange(sys, e)
            val  = assi[Int(sys.vars[i])]
            sign = sys.signs[i]
            unaffected = (val == 0) | (sign & (val == 1)) | (!sign & (val == 2))
            c += unaffected ? sys.coefs[i] : zero(Int32)
        end
        return c - sys.rhs[e] end

    inprism(n, prism::BitVector) = n <= length(prism) && prism[n]
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

    function printeq(eq::Eq)
        for l in eq.t
            print(" ")
            printlitcolor(l.coef, l.sign, l.var, :green)
        end
        println(" >= ", eq.b) end

    function printeq(sys::PBSystem, e::Int)
        for k in eqrange(sys, e)
            print(" ")
            printlitcolor(sys.coefs[k], sys.signs[k], Int(sys.vars[k]), :green)
        end
        println(" >= ", sys.rhs[e]) end

    function fixante(systemlink::Vector{Vector{Int}}, ante::Ante, i)
        for j in eachindex(systemlink[i])
            t = systemlink[i][j]
            if t > 0 && !(j < length(systemlink[i]) && systemlink[i][j+1] in (-2,-3))  # skip multiplicands/divisors (not constraint refs)
                ante_set!(ante, t)
            end
        end end

        # After getcone, any constraint inside a red subproof that references an external antecedent
        # must have that antecedent visible from outside the block. This bubbles those references up
        # to the red declaration's systemlink so the writer emits them as del targets correctly.
    function fixredsystemlink(systemlink, cone, prism, nbopb)
        for range in prism
            for i in range
                if cone[i]
                    for j in eachindex(systemlink[i-nbopb])
                        k = systemlink[i-nbopb][j]
                        if k > 0 && !(k in systemlink[range.start-nbopb]) && k < range.start - nbopb
                            push!(systemlink[range.start-nbopb], k)  # bubble external ref up to red declaration
                        end
                    end
                end
            end
            sort!(systemlink[range.start-nbopb])  # keep link sorted so writedel processes ids in order
        end end

    function eqvars(sys::PBSystem, e::Int)
        Set{Int}(Int(sys.vars[k]) for k in eqrange(sys, e)) end

        # A constraint is trivial if, after assigning its non-cone literals to their worst case (all 0),
        # the remaining cone-lit coefs already satisfy the RHS — so the constraint adds nothing to the proof.
    function istrivial(sys::PBSystem, e::Int, conelits)
        cl = get(conelits, e, nothing)
        cl === nothing && return sys.rhs[e] <= 0       # no cone lits at all: trivial iff RHS ≤ 0
        a = zero(Int32)
        for k in eqrange(sys, e)
            !(sys.vars[k] in cl) && (a += sys.coefs[k])  # sum coefs of non-cone literals
        end
        return sys.rhs[e] - a <= 0 end                 # trivial if RHS minus non-cone coefs ≤ 0

    function fixconelits(sys::PBSystem, conelits, i::Int, ante::Ante, link)
        # if -3 in link[2:end] # deactivate lit trimming. when div is there
            # for j in ante.list; ante.flags[j] || continue
                # conelits[j] = eqvars(sys, j)
            # end
            # return
        # end
        ivars     = eqvars(sys, i)
        cl        = get(conelits, i, nothing)
        myconelit = cl !== nothing ? cl : ivars            # start from known cone lits, or all vars
        poslits = Set{Int}()   # vars appearing positive across antecedent eqs
        neglits = Set{Int}()   # vars appearing negative across antecedent eqs
        for j in ante.list
            ante.flags[j] || continue
            for k in eqrange(sys, j)
                sys.signs[k] ? push!(poslits, Int(sys.vars[k])) : push!(neglits, Int(sys.vars[k]))
            end
            cj = get(conelits, j, nothing)
            cj !== nothing && (myconelit = myconelit ∪ cj)  # inherit cone lits from antecedent
        end
        myconelit = myconelit ∪ (poslits ∩ neglits)   # vars with both signs are needed (resolution)
        conelits[i] = myconelit ∩ ivars               # restrict to vars actually in this constraint
        for j in ante.list
            ante.flags[j] || continue
            conelits[j] = myconelit ∩ eqvars(sys, j)  # propagate back to each antecedent
        end end

    function removetrivialantecedants(sys::PBSystem, ante::Ante, conelits, link, init::Int)
        for i in ante.list
            ante.flags[i] || continue
            istrivial(sys, i, conelits) || continue   # antecedent became trivial after lit trimming
            j = findfirst(x -> x == i, link)
            if j === nothing
                println("antecedant $i not found in link $link")
                continue
            end
            k0 = findfirst(x -> x == -1, @view link[j+1:end])  # find the '+' following this antecedent in the pol link
            if k0 === nothing
                printeqconelit(sys, init, conelits)
                println(link)
                for jj in ante.list
                    ante.flags[jj] || continue
                    printeqconelit(sys, jj, conelits)
                end
                println("antecedant $i's addition not found in link $link")
                deleteat!(link, j)
                ante_remove!(ante, i)
                continue
            end
            deleteat!(link, (j, k0 + j))  # remove antecedent id and its '+' from the pol link
            ante_remove!(ante, i)
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
        return c - (total - sys.rhs[e] + 1) end  # slack of ~eq: used to RUP-check the negated constraint

        # TODO incorporate lvl0 propag to hotstart trail without compromising order and cone rup first heuristics
        # Grim conflict analysis: proof-index sort only.
    function conflicttrail(ceq::Int, sys::PBSystem, t::Trail,
                           ante::Ante, conelits, rs::RupState, ::Grim, cone::Vector{Bool}; rev_init::Int=-1)
        to_explain    = rs.to_explain     # self-cleaning: empty after each normal exit
        is_to_explain = rs.is_to_explain  # self-cleaning: all-false after each normal exit
        ante_set!(ante, ceq)
        push!(t.var, Int32(0)); push!(t.eq, Int32(ceq))  # fake var 0 represents the conflict eq itself
        push!(to_explain, length(t.var)); is_to_explain[1] = true
        falsified_lits = rs.falsified_lits
        while !isempty(to_explain)
            vtp = pop!(to_explain)
            v   = Int(t.var[vtp])
            is_to_explain[v+1] = false
            v != 0 && (t.assi[v] = Int8(0))
            eq     = Int(t.eq[vtp])
            ante_set!(ante, eq)
            eq_rev = (eq == rev_init)
            b      = eq_rev ? (sum(sys.coefs[k] for k in eqrange(sys, eq); init=zero(Int32)) - sys.rhs[eq] + 1) :
                              sys.rhs[eq]
            empty!(falsified_lits)
            somme = zero(Int32)
            @inbounds for k in eqrange(sys, eq)
                w = Int(sys.vars[k])
                w == v && continue
                coef = sys.coefs[k]
                somme += coef
                wtp  = t.pos[w]
                wtp > vtp && continue
                wval = t.assi[w]; wsign = sys.signs[k]
                falsified_w = eq_rev ? ((wsign & (wval == Int8(1))) | (!wsign & (wval == Int8(2)))) :
                                       ((wsign & (wval == Int8(2))) | (!wsign & (wval == Int8(1))))
                falsified_w && push!(falsified_lits, (wtp > 0 ? @inbounds(Int(t.eq[wtp])) : 0, wtp, w, coef))
            end
            sort!(falsified_lits; by = x -> x[1])
            v != 0 && setconelits(conelits, v, eq)
            for (_, wtp, w, coef) in falsified_lits
                somme < b && break
                if wtp > 0 && !is_to_explain[w+1]
                    push!(to_explain, wtp); is_to_explain[w+1] = true
                end
                setconelits(conelits, w, eq)
                somme -= coef
            end
            if somme >= b
                printstyled("conflicttrail: could not explain var $v in eq $eq\n"; color = :red)
                printeq(sys, eq); printeqconelit(sys, eq, conelits)
                throw(ErrorException("conflicttrail: could not explain $v with eq $eq"))
            end
        end end

        # Clit conflict analysis: essentials-aware filter + cone-first sort.
        # x = (eq_id, trail_pos, var, coef) — falsified literal tuple.
        # x[1] = proof index of the reason constraint (0 = level-0 assignment, free to include).
        # x[3] = variable index.   x[4] = coefficient in the equation being explained.
        # Essential vars (rs.essentials[eq]): removing them makes the constraint infeasible — must keep.
        # Cone/lvl0 vars: their reason is already in the cone or has no cost — free to include.
        # Filter: if essential+cone vars alone explain the slack, drop all others.
        # Sort: essential first, then cone/lvl0, then proof depth (ascending).
    function conflicttrail(ceq::Int, sys::PBSystem, t::Trail,
                           ante::Ante, conelits, rs::RupState, ::Clit, cone::Vector{Bool}; rev_init::Int=-1)
        to_explain    = rs.to_explain
        is_to_explain = rs.is_to_explain
        ante_set!(ante, ceq)
        push!(t.var, Int32(0)); push!(t.eq, Int32(ceq))
        push!(to_explain, length(t.var)); is_to_explain[1] = true
        falsified_lits = rs.falsified_lits
        while !isempty(to_explain)
            vtp = pop!(to_explain)
            v   = Int(t.var[vtp])
            is_to_explain[v+1] = false
            v != 0 && (t.assi[v] = Int8(0))
            eq     = Int(t.eq[vtp])
            ante_set!(ante, eq)
            eq_rev = (eq == rev_init)
            b      = eq_rev ? (sum(sys.coefs[k] for k in eqrange(sys, eq); init=zero(Int32)) - sys.rhs[eq] + 1) :
                              sys.rhs[eq]
            empty!(falsified_lits)
            somme = zero(Int32)
            @inbounds for k in eqrange(sys, eq)
                w = Int(sys.vars[k])
                w == v && continue
                coef = sys.coefs[k]
                somme += coef
                wtp  = t.pos[w]
                wtp > vtp && continue
                wval = t.assi[w]; wsign = sys.signs[k]
                falsified_w = eq_rev ? ((wsign & (wval == Int8(1))) | (!wsign & (wval == Int8(2)))) :
                                       ((wsign & (wval == Int8(2))) | (!wsign & (wval == Int8(1))))
                falsified_w && push!(falsified_lits, (wtp > 0 ? @inbounds(Int(t.eq[wtp])) : 0, wtp, w, coef))
            end
            ess_set  = get(rs.essentials, eq, nothing)
            prio_sum = zero(Int32)                             # sum of essential+cone/lvl0 vars
            for (eq_id, _, w, coef) in falsified_lits
                ((ess_set !== nothing && w in ess_set) || eq_id == 0 || cone[eq_id]) && (prio_sum += coef)
            end
            if prio_sum > somme - b                            # high-priority vars alone explain the slack
                filter!(x -> x[1] == 0 || cone[x[1]] || (ess_set !== nothing && x[3] in ess_set), falsified_lits)
            end
            sort!(falsified_lits; by = x -> (ess_set !== nothing && x[3] in ess_set ? 0 : 1,
                                             x[1] == 0 || cone[x[1]] ? 0 : 1, x[1]))
            v != 0 && setconelits(conelits, v, eq)
            for (_, wtp, w, coef) in falsified_lits
                somme < b && break
                if wtp > 0 && !is_to_explain[w+1]
                    push!(to_explain, wtp); is_to_explain[w+1] = true
                end
                setconelits(conelits, w, eq)
                somme -= coef
            end
            if somme >= b
                printstyled("conflicttrail: could not explain var $v in eq $eq\n"; color = :red)
                printeq(sys, eq); printeqconelit(sys, eq, conelits)
                throw(ErrorException("conflicttrail: could not explain $v with eq $eq"))
            end
        end end

        # BFS variant: cone-first sort + replaces non-cone trail reasons with cone ones.
        # TODO search in the trail (=implication graph) while mimicking order and cone rup first heuristics.
    function conflicttrail_bfs(ceq::Int, sys::PBSystem, t::Trail,
                               ante::Ante, conelits, rs::RupState,
                               cone::Vector{Bool}, on_frontier::Vector{Bool}; rev_init::Int=-1)
        to_explain    = rs.to_explain
        is_to_explain = rs.is_to_explain

        ante_set!(ante, ceq)
        push!(t.var, Int32(0)); push!(t.eq, Int32(ceq))
        push!(to_explain, length(t.var)); is_to_explain[1] = true

        assi_temp = zeros(Int8, length(rs.is_to_explain) - 1)
        for p in 1:length(t.var)
            w = Int(t.var[p]); w != 0 && (assi_temp[w] = t.assi[w])
        end
        last_vtp = length(t.var) + 1

        falsified_lits = rs.falsified_lits
        while !isempty(to_explain)
            vtp = pop!(to_explain)
            v   = Int(t.var[vtp])
            is_to_explain[v+1] = false
            v_val = v != 0 ? t.assi[v] : Int8(0)
            v != 0 && (t.assi[v] = Int8(0))
            for p in vtp:last_vtp-1
                w = Int(t.var[p]); w != 0 && (assi_temp[w] = Int8(0))
            end
            last_vtp = vtp
            eq = Int(t.eq[vtp])
            if v != 0 && !cone[eq]
                for j in varrange(sys, v)
                    eid = Int(sys.var_eqs[j])
                    cone[eid]                                || continue
                    (rev_init == -1 || eid < rev_init)       || continue
                    s = slack(sys, eid, assi_temp)
                    @inbounds for kk in eqrange(sys, eid)
                        Int(sys.vars[kk]) == v || continue
                        if sys.coefs[kk] > s && (sys.signs[kk] ? Int8(1) : Int8(2)) == v_val
                            t.eq[vtp] = Int32(eid); eq = eid
                        end
                        break
                    end
                    cone[eq] && break
                end
            end
            ante_set!(ante, eq)
            eq_rev = (eq == rev_init)
            b      = eq_rev ? (sum(sys.coefs[k] for k in eqrange(sys, eq); init=zero(Int32)) - sys.rhs[eq] + 1) :
                              sys.rhs[eq]
            empty!(falsified_lits)
            somme = zero(Int32)
            @inbounds for k in eqrange(sys, eq)
                w = Int(sys.vars[k])
                w == v && continue
                coef = sys.coefs[k]
                somme += coef
                wtp  = t.pos[w]
                wtp > vtp && continue
                wval = t.assi[w]; wsign = sys.signs[k]
                falsified_w = eq_rev ? ((wsign & (wval == Int8(1))) | (!wsign & (wval == Int8(2)))) :
                                       ((wsign & (wval == Int8(2))) | (!wsign & (wval == Int8(1))))
                falsified_w && push!(falsified_lits, (wtp > 0 ? @inbounds(Int(t.eq[wtp])) : 0, wtp, w, coef))
            end
            sort!(falsified_lits; by = x -> (cone[x[1]] ? 0 : 1, x[1]))
            v != 0 && setconelits(conelits, v, eq)
            for (_, wtp, w, coef) in falsified_lits
                somme < b && break
                if wtp > 0 && !is_to_explain[w+1]
                    push!(to_explain, wtp); is_to_explain[w+1] = true
                end
                setconelits(conelits, w, eq)
                somme -= coef
            end
            if somme >= b
                printstyled("conflicttrail: could not explain var $v in eq $eq\n"; color = :red)
                printeq(sys, eq); printeqconelit(sys, eq, conelits)
                throw(ErrorException("conflicttrail: could not explain $v with eq $eq"))
            end
        end
        for p in 1:length(t.var)
            w = Int(t.var[p]); w != 0 && (assi_temp[w] = Int8(0))
        end end

        # Trail-based unit propagation.
    function propagate!(sys::PBSystem, t::Trail, prism, ante::Ante, conelits, rs::RupState, cone::Vector{Bool})
        i = 1; n = length(sys.rhs)
        que = trues(n)                                # all constraints initially pending
        while i <= n
            if !inprism(i, prism) && que[i]
                s = slack(sys, i, t.assi)
                if s < 0                               # falsified: record conflict and stop
                    conflicttrail(i, sys, t, ante, conelits, rs, Grim(), cone)
                    return
                end
                que[i] = false
                rewind = i + 1                         # will jump back to earliest newly-triggered eq
                @inbounds for k in eqrange(sys, i)
                    v = Int(sys.vars[k])
                    t.assi[v] != 0 && continue         # already assigned
                    sys.coefs[k] > s || continue       # coef too small to force propagation
                    pushtrail!(t, Int32(v), Int32(i), sys.signs[k] ? Int8(1) : Int8(2))
                    for j in varrange(sys, v)
                        eid = Int(sys.var_eqs[j])
                        que[eid] = true
                        rewind = min(rewind, eid)      # re-scan from earliest affected constraint
                    end
                end
                i = rewind
            else
                i += 1
            end
        end
        printstyled("propagate! found no conflict\n"; color = :red) end

        # Linear-scan RUP (kept for comparison). Two rewind pointers (r0/r1) + que BitVector guard.
    function deprecated_ruptrail(sys::PBSystem, init::Int, t::Trail,
                      ante::Ante, on_frontier::Vector{Bool},
                      cone::Vector{Bool}, conelits, prism, subrange)
        prio = true
        r0   = 1           # non-priority rewind; starts at 1 so non-prio pass sweeps from eq 1
        r1   = init + 1    # priority rewind; init+1 = sentinel "none"
        i    = 1
        que  = trues(init)
        while i <= init
            in_queue = !inprism(i, prism) || (i in subrange)
            if que[i] && in_queue && (!prio || cone[i])
                rev = (i == init)
                s   = rev ? slack_reversed(sys, i, t.assi) : slack(sys, i, t.assi)
                if s < 0
                    conflicttrail(i, sys, t, ante, conelits, rs_placeholder, Grim(); rev_init=init)  # BROKEN: rs not available here — deprecated function, kept for reference only
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
                        if cone[eid]; r1 = min(r1, eid)
                        else         r0 = min(r0, eid)
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

        # Walk the trail forward and substitute non-cone reasons with cone ones where possible.
    function deprecated_minimize_reasons!(t::Trail, sys::PBSystem, cone::Vector{Bool}, on_frontier::Vector{Bool}, assi_temp::Vector{Int8}, init::Int)
        for k in 1:length(t.var)
            v      = Int(t.var[k])
            reason = Int(t.eq[k])
            if !cone[reason]
                for j in varrange(sys, v)
                    eid = Int(sys.var_eqs[j])
                    cone[eid] || continue
                    eid < init || continue
                    s = slack(sys, eid, assi_temp)
                    @inbounds for kk in eqrange(sys, eid)
                        Int(sys.vars[kk]) == v || continue
                        if sys.coefs[kk] > s && (sys.signs[kk] ? Int8(1) : Int8(2)) == t.assi[v]
                            t.eq[k] = Int32(eid)
                        end
                        break
                    end
                    cone[Int(t.eq[k])] && break
                end
            end
            assi_temp[v] = t.assi[v]
        end
        for k in 1:length(t.var); assi_temp[Int(t.var[k])] = Int8(0); end end

    # Push eid into the right heap if not already queued.
    @inline function activate!(eid, rs::RupState, cone, on_frontier)
        rs.que[eid] && return              # already in a heap, skip
        rs.que[eid] = true
        if cone[eid]; push!(rs.pq_prio, eid)                         # priority: already in cone
        else                        push!(rs.pq_nonprio, eid)  # non-priority: new to cone
        end end

    # Compute slack, propagate, re-activate triggered equations. Return true on conflict.
    @inline function process_eq!(i, init, sys, t, ante, conelits, cone, on_frontier, rs::RupState, mode)
        rev = (i == init)                  # reversed constraint for RUP check of init
        s   = rev ? slack_reversed(sys, i, t.assi) : slack(sys, i, t.assi)
        if s < 0                           # falsified: conflict found
            conflicttrail(i, sys, t, ante, conelits, rs, mode, cone; rev_init=init)
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
                activate!(eid, rs, cone, on_frontier)               # re-queue equations containing v
            end
        end
        rs.que[i] = false                  # done: remove from queue
        return false end

        # Heap-based RUP check. Same algorithm as ruptrail_deprecated but replaces the linear scan
        # with two BinaryMinHeap{Int}: pq_prio (cone/on_frontier equations) and pq_nonprio (others).
        # Priority pass drains pq_prio fully before taking one step from pq_nonprio.
    function ruptrail(sys::PBSystem, init::Int, t::Trail,
                      ante::Ante, on_frontier::Vector{Bool},
                      cone::Vector{Bool}, conelits, prism, subrange, rs::RupState, mode=Grim())
        fill!(rs.que, false)               # reset queue (may have stale trues from early return)
        empty!(rs.pq_prio.valtree); empty!(rs.pq_nonprio.valtree)  # BinaryHeap has no empty!, clear the internal vector
        for i in 1:init                    # seed both heaps with all eligible equations
            (!inprism(i, prism) || (i in subrange)) || continue
            activate!(i, rs, cone, on_frontier)
        end
        while true
            while !isempty(rs.pq_prio)     # drain priority equations first
                i = pop!(rs.pq_prio)
                rs.que[i] || continue      # stale pop guard (safety net)
                process_eq!(i, init, sys, t, ante, conelits, cone, on_frontier, rs, mode) && return true
            end
            isempty(rs.pq_nonprio) && break  # nothing left: no conflict found
            i = pop!(rs.pq_nonprio)          # take one non-priority equation
            rs.que[i] || continue            # stale pop guard (safety net)
            process_eq!(i, init, sys, t, ante, conelits, cone, on_frontier, rs, mode) && return true
        end
        return false end

        # BFS-level RUP. Processes an entire propagation wave before committing any assignment,
        # enabling best-reason selection: when multiple constraints at the same level force the same
        # variable, the one already in cone/on_frontier is preferred as the Trail reason.
        # Among conflicts found in the same wave, the cone/on_frontier one is selected.
    function ruptrail_bfs(sys::PBSystem, init::Int, t::Trail,
                          ante::Ante, on_frontier::Vector{Bool},
                          cone::Vector{Bool}, conelits, prism, subrange, rs::RupState)
        n_vars = length(rs.is_to_explain) - 1
        pending_reason = zeros(Int,  n_vars)               # best reason eq per variable (0 = none)
        pending_value  = zeros(Int8, n_vars)               # forced value per variable
        pending_vars   = Int[]                             # variables with a pending reason
        fill!(rs.que, false)
        current_wave = Int[]
        next_wave    = Int[]
        for i in 1:init
            (!inprism(i, prism) || (i in subrange)) || continue
            rs.que[i] = true; push!(current_wave, i)
        end
        while !isempty(current_wave)
            best_conflict = 0
            for i in current_wave
                !rs.que[i] && continue                         # stale guard
                rev = (i == init)
                s = rev ? slack_reversed(sys, i, t.assi) : slack(sys, i, t.assi)
                if s < 0
                    if best_conflict == 0 || (!cone[best_conflict] && cone[i])
                        best_conflict = i                      # prefer cone conflict
                    end
                    rs.que[i] = false; continue
                end
                @inbounds for k in eqrange(sys, i)
                    v = Int(sys.vars[k])
                    t.assi[v] != 0 && continue
                    sys.coefs[k] > s || continue
                    sign = sys.signs[k]
                    val  = rev ? (sign ? Int8(2) : Int8(1)) :
                                 (sign ? Int8(1) : Int8(2))
                    cur = pending_reason[v]
                    if cur == 0
                        pending_reason[v] = i; pending_value[v] = val
                        push!(pending_vars, v)                 # register for commit phase
                    elseif !cone[cur] && cone[i]
                        pending_reason[v] = i; pending_value[v] = val  # upgrade to cone reason
                    end
                end
                rs.que[i] = false
            end
            if best_conflict != 0
                for v in pending_vars; pending_reason[v] = 0; end
                empty!(pending_vars)                           # clean pending state before conflicttrail
                conflicttrail_bfs(best_conflict, sys, t, ante, conelits, rs, cone, on_frontier; rev_init=init)
                return true
            end
            empty!(current_wave)
            for v in pending_vars                              # commit all pending propagations
                if t.assi[v] == 0
                    pushtrail!(t, Int32(v), Int32(pending_reason[v]), pending_value[v])
                    for j in varrange(sys, v)
                        eid = Int(sys.var_eqs[j])
                        (eid <= init && eid != pending_reason[v]) || continue
                        rs.que[eid] && continue
                        rs.que[eid] = true; push!(next_wave, eid)
                    end
                end
                pending_reason[v] = 0                         # self-clean
            end
            empty!(pending_vars)
            current_wave, next_wave = next_wave, current_wave
            empty!(next_wave)
        end
        return false end

    @inline function push_frontier!(frontier, on_frontier::Vector{Bool}, cone::Vector{Bool}, j::Int)
        cone[j] && return                             # already in cone (scheduled or processed)
        on_frontier[j] = true; cone[j] = true; push!(frontier, j) end

    # Expand the frontier with all active antecedents; optionally record them in systemlink.
    @inline function ante_into_frontier!(ante::Ante, frontier, on_frontier, cone)
        for j in ante.list; ante.flags[j] || continue; push_frontier!(frontier, on_frontier, cone, j); end end
    @inline function ante_into_frontier!(ante::Ante, frontier, on_frontier, cone, link)
        for j in ante.list; ante.flags[j] || continue; push!(link, j); push_frontier!(frontier, on_frontier, cone, j); end end  # push!(link,j): record antecedent for the writer

    function getcone!(cone, conelits, sys::PBSystem, systemlink, nbopb::Int,
                      prism::Vector{UnitRange{Int64}}, redwitness, conclusion::String, obj, mode)
        n    = length(sys.rhs)
        prism_bv = falses(n)
        for r in prism, i in r
            1 <= i <= n && (prism_bv[i] = true)       # bitvector version of prism for O(1) inprism checks
        end
        on_frontier = zeros(Bool, n)                   # true = constraint is scheduled in frontier
        trail      = Trail(length(sys.var_ptr) - 1)    # var_ptr has length n_vars+1 (CSR convention)
        # Bfs uses a pre-computed level-0 base trail (propagations forced from the empty assignment)
        # so that each RUP call starts from a common fixed point rather than from scratch.
        # Grim/Clit do not use this — the cone-first priority queue handles reason selection directly.
        base_trail = mode isa Bfs ? Trail(length(sys.var_ptr) - 1) : trail  # alias to trail for Grim/Clit
        mode isa Bfs && propagate_level0!(sys, base_trail)

        firstcontradiction = 0                         # root of the backward reachability
        if conclusion == "UNSAT"
            firstcontradiction = getfirstcontradiction(sys, prism_bv)
        elseif occursin("BOUNDS", conclusion)
            firstcontradiction = getfirstboundeq(sys, obj, conclusion, cone)
        end
        if firstcontradiction == 0
            conclusion == "UNSAT" && printstyled("\nUNSAT contradiction not found\n"; color = :red)
            return
        end

        ante = Ante(n)
        rs   = RupState(n, length(sys.var_ptr) - 1)   # reusable scratch buffers for rup/conflict analysis
        mode isa Clit && compute_essentials!(rs.essentials, sys)  # forward pass: essential vars per constraint
        frontier = BinaryMaxHeap{Int}()                # max-heap: process highest-indexed eq first (backwards)

        # Local function: clear ante, reset trail, run rup. i and subrange are parameters (not captured)
        # to avoid Julia boxing mutable loop variables. Everything else is captured from getcone! scope.
        function do_rup!(i, subrange)
            ante_clear!(ante)
            mode isa Bfs ? reset_to_base!(trail, base_trail, i) : reset!(trail)
            mode isa Bfs ? ruptrail_bfs(sys, i, trail, ante, on_frontier, cone, conelits, prism_bv, subrange, rs) :
                           ruptrail(sys, i, trail, ante, on_frontier, cone, conelits, prism_bv, subrange, rs, mode)
        end

        cone[firstcontradiction] = true
        if systemlink[firstcontradiction - nbopb][1] == -2   # contradiction is a pol: antecedents explicit in link
            for j in systemlink[firstcontradiction - nbopb]
                j > 0 && push_frontier!(frontier, on_frontier, cone, j)
            end
        else                                           # contradiction is rup/ia: run propagation to find antecedents
            if conclusion == "UNSAT" || conclusion == "NONE"
                propagate!(sys, trail, prism_bv, ante, conelits, rs, cone)
            elseif occursin("BOUNDS", conclusion)
                if !do_rup!(firstcontradiction, 0:0) printstyled("initial rup for bound contradiction failed\n"; color = :red) end
            end
            ante_into_frontier!(ante, frontier, on_frontier, cone, systemlink[firstcontradiction - nbopb])
        end
        red     = Red([], 0:0, [])                     # current red block being processed
        pfgl    = UnitRange{Int64}[]                   # deferred proof goals (ref not yet known to be in cone)
        newpfgl = true
        while newpfgl                                  # outer loop: retry deferred proof goals until stable
            newpfgl = false
            while !isempty(frontier)
                i = pop!(frontier)
                on_frontier[i] || continue             # stale pop guard
                on_frontier[i] = false                 # remove from queue (cone[i] already true since push)
                if i > nbopb
                    tlink = systemlink[i - nbopb][1]   # rule type: -1=rup, -2=pol, -3=ia, -4=red, ...
                    if tlink == -1                              # rup
                        if do_rup!(i, 0:0)
                            ante_remove!(ante, i)              # i itself is not its own antecedent
                            ante_into_frontier!(ante, frontier, on_frontier, cone, systemlink[i - nbopb])
                        else
                            printstyled("rup failed at $i\n"; color = :red)
                            return
                        end
                    elseif tlink >= -3 || (tlink == -30 && length(systemlink[i - nbopb]) > 1)  # pol / ia / assumption with hints
                        ante_clear!(ante)
                        fixante(systemlink, ante, i - nbopb)
                        fixconelits(sys, conelits, i, ante, systemlink[i - nbopb])
                        removetrivialantecedants(sys, ante, conelits, systemlink[i - nbopb], i)
                        ante_into_frontier!(ante, frontier, on_frontier, cone)
                    elseif tlink == -10                         # end of red subproof
                        red = redwitness[i]
                        push_frontier!(frontier, on_frontier, cone, red.range.start)  # red declaration itself
                        for subr in red.pgranges
                            if systemlink[subr.start - nbopb][1] == -8 && !cone[subr.start]
                                push!(pfgl, subr)              # defer: ref constraint not yet in cone
                            else
                                push_frontier!(frontier, on_frontier, cone, subr.start)
                                push_frontier!(frontier, on_frontier, cone, subr.stop)
                            end
                        end
                    elseif tlink == -5                          # subproof rup
                        subran_idx = findfirst(x -> i in x, red.pgranges)
                        if do_rup!(i, red.pgranges[subran_idx])
                            ante_remove!(ante, i)
                            ante_into_frontier!(ante, frontier, on_frontier, cone, systemlink[i - nbopb])
                        else
                            printstyled("subproof rup failed\n"; color = :red)
                        end
                    elseif tlink == -6 || tlink == -8           # subproof pol / proofgoal ref
                        ante_clear!(ante)
                        fixante(systemlink, ante, i - nbopb)
                        ante_into_frontier!(ante, frontier, on_frontier, cone)
                    elseif tlink == -7                          # proofgoal #1: no external antecedents
                    end
                end
            end
            for r in pfgl                              # revisit deferred proof goals now that more cone is known
                id = systemlink[r.start - nbopb][2]
                if cone[id] && !cone[r.start]          # ref is now in cone: safe to schedule this proof goal
                    push_frontier!(frontier, on_frontier, cone, r.start)
                    push_frontier!(frontier, on_frontier, cone, r.stop)
                    newpfgl = true
                end
            end
        end
        fixredsystemlink(systemlink, cone, prism, nbopb)  # propagate subproof antecedents up to red declarations
    end

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

    function getfirstboundeq(sys::PBSystem, obj, conclusion::String, cone::Vector{Bool})
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
        lits = [Lit(-l.coef, l.sign, l.var) for l in eq.t]
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
    @inline function fixon_frontier(on_frontier::Vector{Bool}, cone::Vector{Bool}, antecedants::Vector{Bool})
        for i in eachindex(antecedants)
            if antecedants[i]; on_frontier[i] = true; cone[i] = true; end
        end end

    @inline function fixon_frontier(on_frontier::Vector{Bool}, cone::Vector{Bool}, antecedants::Vector{Int})
        for i in antecedants
            if i > 0; on_frontier[i] = true; cone[i] = true; end
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

# ======================================= unsat core graphs ======================================= #

    # Returns (pattern_file_path, target_file_path) for an instance name.
    # For ins.coreN, returns the LAD files written by the previous iteration.
    # For original bio*/LV* instances, returns the benchmark graph files.
    function parsegraphfiles(ins)
        m = match(r"^(.+)\.core(\d+)$", ins)
        if m !== nothing
            prev_ins = m.captures[1]
            return proofs * "vis/" * prev_ins * ".core.pat.lad",
                   proofs * "vis/" * prev_ins * ".core.tar.lad"
        end
        if startswith(ins, "bio")
            pat = ins[4:end-3]
            tar = ins[end-2:end]
            base = SIPgraphpath * "biochemicalReactions/"
            return base * pat * ".txt", base * tar * ".txt"
        elseif startswith(ins, "LV")
            i   = findlast('g', ins)
            pat = ins[4:i-1]
            tar = ins[i+1:end]
            base = SIPgraphpath * "LV/"
            return base * "g" * pat, base * "g" * tar
        end
        return nothing, nothing
    end

    # Reads a LAD format graph: first line = n, then n lines of "degree nb1 nb2 ..." (0-indexed neighbors).
    # Returns 1-indexed adjacency list Vector{Vector{Int}}.
    function readlad(path)
        adj = Vector{Vector{Int}}()
        open(path, "r") do f
            n = parse(Int, readline(f))
            for _ in 1:n
                parts = filter(!isempty, split(readline(f)))
                push!(adj, [parse(Int, p) + 1 for p in parts[2:end]])
            end
        end
        return adj
    end

    # Parses "x{p}_{t}" (0-indexed) → (p+1, t+1). Returns nothing if name doesn't match.
    function parsevarname(name)
        length(name) < 3 && return nothing
        name[1] == 'x'   || return nothing
        u = findfirst('_', name)
        u === nothing     && return nothing
        p = tryparse(Int, name[2:u-1])
        t = tryparse(Int, name[u+1:end])
        (p === nothing || t === nothing) && return nothing
        return p + 1, t + 1
    end

    # Extracts core pattern nodes P and target nodes T from OPB cone constraints,
    # restricted to variables kept by conelits (weakened-out variables are excluded).
    function corenodes(sys::PBSystem, cone::Vector{Bool}, varmap_inv::Vector{String},
                       conelits::Dict{Int,Set{Int}}, nbopb::Int)
        P = Set{Int}(); T = Set{Int}()
        for i in 1:nbopb
            cone[i] || continue
            clit = get(conelits, i, nothing)
            for k in eqrange(sys, i)
                v = Int(sys.vars[k])
                clit !== nothing && v ∉ clit && continue
                pt = parsevarname(varmap_inv[v])
                pt === nothing && continue
                push!(P, pt[1]); push!(T, pt[2])
            end
        end
        return sort!(collect(P)), sort!(collect(T))
    end

    # Writes a DOT file for a graph. core_set nodes are green, others red.
    # LAD format stores each edge once (asymmetric) — symmetrise before writing.
    # For graphs with many nodes, node labels are hidden to reduce clutter.
    function writedot(path, adj, core_set)
        n = length(adj)
        large = n > 300
        edges = Set{Tuple{Int,Int}}()
        for i in 1:n, j in adj[i]
            push!(edges, (min(i,j), max(i,j)))
        end
        open(path, "w") do f
            println(f, "graph G {")
            println(f, "  layout=circo; overlap=false; node [shape=circle, width=0.2, fixedsize=true];")
            for i in 1:n
                color = i in core_set ? "#44bb44" : "#cc4444"
                label = large ? "" : string(i)
                println(f, "  $i [label=\"$label\", style=filled, fillcolor=\"$color\", fontsize=7];")
            end
            for (i, j) in edges
                ec = (i in core_set && j in core_set) ? "#44bb44" : "#aaaaaa"
                println(f, "  $i -- $j [color=\"$ec\"];")
            end
            println(f, "}")
        end
    end

    # Writes a LAD file for the induced subgraph on core (sorted 1-indexed node list).
    function writecoreladfile(path, adj, core)
        core_set = Set(core)
        old2new  = Dict(v => i - 1 for (i, v) in enumerate(core))  # 0-indexed for LAD format
        open(path, "w") do f
            println(f, length(core))
            for v in core
                neighbors = [old2new[u] for u in adj[v] if u in core_set]
                println(f, length(neighbors), " ", join(neighbors, " "))
            end
        end
    end

    # Runs the Glasgow SIP solver on pat_lad/tar_lad, writing proof to proofs/out_prefix.{opb,pbp}.
    # Returns true if both output files were produced.
    function runsipsolver(out_prefix, pat_lad, tar_lad)
        isfile(sipsolverpath) || (printstyled("  solver not found: $sipsolverpath\n"; color=:red); return false)
        redirect_stdio(stdout=devnull, stderr=devnull) do
            run(ignorestatus(`timeout $solvertimeout $sipsolverpath
                --prove $(proofs*out_prefix) --no-clique-detection --format lad $pat_lad $tar_lad`))
        end
        return isfile(proofs*out_prefix*opb) && isfile(proofs*out_prefix*pbp)
    end

    # Runs the solver on the core LAD files produced by writeunsatcore, then trims the result.
    # Iterates until fixpoint (core node counts stop shrinking) or solver fails.
    # Instances are named ins.core1, ins.core2, ... ; LADs chain naturally from each trim.
    function resolvecore(ins)
        cur_pat = proofs * "vis/" * ins * ".core.pat.lad"
        cur_tar = proofs * "vis/" * ins * ".core.tar.lad"
        prev_np = prev_nt = -1
        iter = 0
        while true
            iter += 1
            if !isfile(cur_pat) || !isfile(cur_tar)
                printstyled("  resolv: core LADs missing at iter $iter\n"; color=:red); return
            end
            np = parse(Int, readline(cur_pat))
            nt = parse(Int, readline(cur_tar))
            if np == prev_np && nt == prev_nt
                printstyled("  resolv: fixpoint after $(iter-1) iteration(s) ($np pat, $nt tar nodes)\n"; color=:green); return
            end
            prev_np, prev_nt = np, nt
            core_ins = ins * ".core$iter"
            t = @elapsed ok = runsipsolver(core_ins, cur_pat, cur_tar)
            if !ok
                printstyled("  resolv: solver failed/timeout at iter $iter ($(round(t;digits=1))s)\n"; color=:red); return
            end
            printstyled("  resolv iter $iter: $np pat / $nt tar → solved $(round(t;digits=1))s\n"; color=:cyan)
            printabline(core_ins)
            tr1,tr2,tr3 = trimnalyse(core_ins; mode=Grim())
            tr4,tr5 = VERIF ? verify(core_ins) : (-1,-1)
            printabline2(core_ins, tr1, tr2, tr3, tr4, tr5)
            writeout_verif(core_ins, tr4, tr5)
            cur_pat = proofs * "vis/" * core_ins * ".core.pat.lad"
            cur_tar = proofs * "vis/" * core_ins * ".core.tar.lad"
        end
    end

    function writeunsatcore(ins, sys::PBSystem, cone::Vector{Bool},
                            conelits::Dict{Int,Set{Int}}, varmap_inv::Vector{String}, nbopb::Int)
        patfile, tarfile = parsegraphfiles(ins)
        (patfile === nothing || !isfile(patfile) || !isfile(tarfile)) && return
        P, T = corenodes(sys, cone, varmap_inv, conelits, nbopb)
        isempty(P) && return
        adj_p = readlad(patfile)
        adj_t = readlad(tarfile)
        dir = proofs * "vis/"
        isdir(dir) || mkdir(dir)
        P_set = Set(P); T_set = Set(T)
        writedot(dir * ins * ".pat.dot",  adj_p, P_set)
        writedot(dir * ins * ".tar.dot",  adj_t, T_set)
        writecoreladfile(dir * ins * ".core.pat.lad", adj_p, P)
        writecoreladfile(dir * ins * ".core.tar.lad", adj_t, T)
        for (base, layout) in [(ins*".pat", "circo"), (ins*".tar", "neato")]
            dot = dir * base * ".dot"
            svg = dir * base * ".svg"
            run(ignorestatus(`neato -Tsvg -K$layout -o$svg $dot`))
        end
        println("\ncore: $(length(P))/$(length(adj_p)) pat nodes, $(length(T))/$(length(adj_t)) tar nodes → $dir")
    end

# ======================================= main code ======================================= #

using StatProfilerHTML
if PROFILE
    throw("uncomment here to enable profiling")
    @profilehtml main()
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


#= interresting instances:
bio161153      (big opb)
LVg6g12        (small lv)
bio108139
bio035151       big bio
LVg39g72        big opb
bio096087       bit but small time

=#