#= This is a PB trimmer made to analyse proofs. If problem, ask arthur.pro.gontier@gmail.com
julia trimnalyser.jl [options] [instance name or directory of instances]   options: atable sort rand clean verif profile bfs
julia --threads 196,1 trimnalyser.jl solve resolv allgraphs maxnodes=50
julia --threads 8,1 trimnalyser.jl solve resolv verif allgraphs maxnodes=30 st=8 tt=60 rand
julia --threads 192,1 trimnalyser.jl solve resolv verif allgraphs maxnodes=3000 st=180 tt=6000 rand maxparse=192
julia -t192 trimnalyser.jl solve resolv verif allgraphs maxnodes=3000 st=180 tt=6000 rand
julia -t92,1 trimnalyser.jl solve resolv verif allgraphs maxnodes=3000 st=180 tt=6000 rand
julia -t4,1 trimnalyser.jl solve resolv verif allgraphs maxnodes=3000 st=180 tt=6000 rand maxmem=2
=#
    const opb = ".opb"
    const pbp = ".pbp"
    const smol = ".smol"
    const version = "3.0"
    const _cluster = contains(gethostname(), "dcs.gla.ac.uk") || startswith(gethostname(), "fataepyc")
    const abspath       = _cluster ? "/users/grad/arthur/"                                                              : "/home/arthur_gla/veriPB/subgraphsolver/"
    const SIPgraphpath  = _cluster ? "/scratch/arthur/newSIPbenchmarks/"                                               : "/home/arthur_gla/veriPB/newSIPbenchmarks/"
    const sipsolverpath = _cluster ? "/scratch/arthur/glasgow_subgraph_solver"                                         : "/home/arthur_gla/veriPB/subgraphsolver/glasgow-subgraph-solver/build/glasgow_subgraph_solver"
    const _defaultproofs = _cluster ? "/scratch/arthur/proofs/" : abspath*"proofs/"
    const proofs = (i = findfirst(x -> isdir(x), ARGS)) === nothing ? _defaultproofs : ARGS[i]
    const inst   = begin  # prefer proof-file match; fall back to LV/bio name pattern for solve mode (no files yet)
        i = findfirst(x -> isfile(proofs*x*pbp) && isfile(proofs*x*opb), ARGS)
        i === nothing && (i = findfirst(x -> !isdir(x) && (startswith(x,"LV") || startswith(x,"bio")), ARGS))
        i !== nothing ? ARGS[i] : nothing end
    const BFS    = "bfs"    in ARGS  # BFS propagation: best-reason selection across same-level constraints
    const CLIT   = "clit"   in ARGS  # Clit mode: cone-first conflict analysis with two-pass filter (see conflicttrail(::Clit))
    const ATABLE = "atable" in ARGS  # print TikZ scatter plot from existing .out files
    const CLEAN  = "clean"  in ARGS  # delete all .out/.err files and vis intermediates (keeps .svg)
    const RAND   = "rand"   in ARGS  # shuffle instance order
    const SORT   = "sort"   in ARGS  # sort instances by file size (ascending)
    const VERIF  = "verif"  in ARGS  # run VeriPB on trimmed output after each instance
    const PROFILE = "profile" in ARGS  # enable StatProfilerHTML profiling
    const NONORM  = "no"     in ARGS  # does not run normal (not official)
    const CORE      = "core"      in ARGS  # write unsat core graph files and reduced LAD files
    const SOLVE     = "solve"     in ARGS  # run SIP solver on original graphs before trimming
    const RESOLV    = "resolv"    in ARGS  # re-solve on core reduced graphs after trimming (implies CORE)
    const ALLGRAPHS = "allgraphs" in ARGS  # enumerate all instances from benchmark graph directories
    const PACK      = "pack"      in ARGS  # tar.gz all .dot files in vis/ → vis.tar.gz (for cluster transfer)
    const RENDER    = "render"    in ARGS  # extract vis.tar.gz and render all .dot → .svg with neato
    const OVERWRITE = "overwrite" in ARGS  # re-trim even if .smol files are already complete
    argval(prefix, T, default) = (i = findfirst(x -> startswith(x, prefix), ARGS); i !== nothing ? parse(T, ARGS[i][length(prefix)+1:end]) : default)
    const MAXNODES      = argval("maxnodes=", Int,     typemax(Int))
    const solvertimeout = argval("st=",       Int,     5)                            # st=N
    const trimtimeout   = argval("tt=",       Int,     45)                           # tt=N
    const minfreemem    = argval("minmem=",   Int,     _cluster ? 100 : 4) * 1024^3 # minmem=N GB
    const maxinstmem_gb = argval("maxmem=",   Float64, _cluster ? 50.0 : 8.0)       # maxmem=N GB per subprocess
    using Random,DataStructures,Dates,Printf,Mmap


# ══ Entry point ══════════════════════════════════════════════════════════════════════════
    function packdots()
        visdir = proofs * "vis/"
        archive = proofs * "vis.tar.gz"
        dots = filter(f -> endswith(f, ".dot"), readdir(visdir; join=true))
        isempty(dots) && (println("No .dot files to pack."); return)
        run(`tar -czf $archive -C $visdir .`)
        println("Packed $(length(dots)) .dot files → $archive") end

    function renderdots()
        archive = proofs * "vis.tar.gz"
        visdir  = proofs * "vis/"
        isfile(archive) && run(`tar -xzf $archive -C $visdir`)
        dots = filter(f -> endswith(f, ".dot"), readdir(visdir; join=true))
        isempty(dots) && (println("No .dot files to render."); return)
        for dot in dots
            svg = dot[1:end-4] * ".svg"
            content = read(dot, String)
            m = match(r"layout=(\w+)", content)
            layout = m !== nothing ? m.captures[1] : "neato"
            try run(ignorestatus(`neato -Tsvg -K$layout -o$svg $dot`))
            catch; #printstyled("  neato not found — install graphviz\n"; color=:yellow); 
                return
            end
        end
        println("Rendered $(length(dots)) SVGs in $visdir") end

    function main()
        if PACK   packdots();   return
        elseif RENDER renderdots(); return
        elseif ATABLE plotresultstable(); return
        elseif CLEAN
            rm.(filter(f -> endswith(f, ".out") || endswith(f, ".err"), readdir(proofs; join=true)))
            visdir = proofs * "vis/"
            if isdir(visdir)
                rm.(filter(f -> any(endswith(f, e) for e in (".lad", ".dot")), readdir(visdir; join=true)))
            end
            return
        elseif inst !== nothing
            # Each subprocess starts with a cold JIT. Without warmup, JIT compilation time
            # is charged to the first instance's parse/trim phases, skewing measurements.
            # We skip warmup when the instance is already done — no real work, no point.
            if !smol_complete(inst) || OVERWRITE
                warmup_jit()
            end
            trimnalyseandcie(inst); return
        elseif (SOLVE || RESOLV) && !ALLGRAPHS
            # proof files don't exist yet: find instance name by bio/LV prefix in ARGS
            j = findfirst(x -> x ∉ argflags && !isdir(x) &&
                               (startswith(x,"LV") || startswith(x,"bio")), ARGS)
            if j !== nothing
                trimnalyseandcie(ARGS[j]); return
            end
        end
        list = ALLGRAPHS ? allgraphinstances() : getinstancesfromdir(proofs)
        n = length(list)
        println("%Running ", n, " instances on ", Threads.nthreads(), " thread(s)")
        done    = Threads.Atomic{Int}(0)
        t_start = time()
        # Each instance runs in its own julia subprocess (single-threaded) so GC heaps are isolated:
        # no stop-the-world across instances. The outer @threads loop provides parallelism.
        # maxparse= and allgraphs are stripped: subprocess handles one instance, not a batch.
        # Directory paths are stripped and proofs_abs is passed explicitly (absolute, cluster-safe).
        subargs = filter(a -> a in Set(["solve","resolv","verif","render","profile"]), ARGS)
        script   = basename(@__FILE__) #Base.abspath(@__FILE__)
        wall = @elapsed Threads.@threads :greedy for ins in list
            try
                while available_memory() < minfreemem
                    sleep(5)
                end
                # -t1,1: 1 worker thread + 1 GC thread. Without ,1, Julia 1.10+ spawns
                # nCPUs/4 GC threads by default — 48 per subprocess on a 192-core machine,
                # which adds up to ~18k OS threads with 192 concurrent subprocesses.
                # addenv overrides JULIA_NUM_THREADS in case -t doesn't fully shadow it.
                subout = proofs * ins * ".subout"
                proc = run(pipeline(addenv(`julia -t1,1 $script $ins $subargs`,
                                          "JULIA_NUM_THREADS" => "1"),
                                   stdout=subout, stderr=subout),
                           wait=false)
                # Kill the subprocess if it exceeds the per-instance RAM limit.
                # @async creates a lightweight task; wait(proc) yields so the task can run.
                @async begin
                    while process_running(proc)
                        sleep(10)
                        process_running(proc) || break
                        rss = process_rss_gb(getpid(proc))
                        if rss > maxinstmem_gb
                            kill(proc, 9)
                            msg = "OOM killed: $(round(rss; digits=1)) GB > $maxinstmem_gb GB"
                            printstyled("  OOM KILL $ins: $msg\n"; color=:red)
                            open(proofs*ins*".err", "a") do f; println(f, msg) end
                            break
                        end
                    end
                end
                wait(proc)
                if isfile(subout)
                    out = read(subout, String)
                    !isempty(out) && (print(out); flush(stdout))
                    rm(subout)
                end
            catch e
                msg = sprint(showerror, e, catch_backtrace())
                printstyled("  ERROR $ins: $msg\n"; color=:red)
                open(proofs*ins*".err", "a") do f; println(f, msg) end
            end
            d = Threads.atomic_add!(done, 1) + 1
            if d % 100 == 0 || d == n
                elapsed = time() - t_start
                rate    = d / elapsed * 60
                eta     = rate > 0 ? (n - d) / rate : Inf
                printstyled("\n\n\n[", d, "/", n, "] ",
                        round(rate; digits=1), " inst/min  ETA ",
                        round(Int, eta), "min\n\n"; color=:magenta)
            end
        end
        println("%Wall time: ", round(wall; digits=1), "s")
        end

    function getinstancesfromdir(proofs)
        list = onlyname.(filter(x -> ext(x)==opb && isfile(noext(x)*pbp), readdir(proofs, join=true)))
        if RAND shuffle!(list)
        elseif SORT sort!(list, by = x -> inssize(x)) end
        println("%Found ", length(list), " instances in ", proofs)
        return list end

    # Enumerates all (pattern, target) instance names from the benchmark graph directories.
    # Filters pairs where both graphs have <= MAXNODES nodes and pattern_size <= target_size.
    function allgraphinstances()
        list = String[]
        mkpath(proofs)
        for (dir, pre, fext, fmt) in [
                (SIPgraphpath*"LV/",                    "g",  "",     (p,t) -> "LVg$(p)g$(t)"),
                (SIPgraphpath*"biochemicalReactions/",  "",   ".txt", (p,t) -> "bio$(p)$(t)") ]
            isdir(dir) || continue
            files = readdir(dir)
            # strip prefix and extension to get the numeric identifier
            ids = [f[length(pre)+1 : end-length(fext)] for f in files
                   if startswith(f, pre) && endswith(f, fext) && !isdir(dir*f)]
            # read node counts, filter by MAXNODES
            sizes = Dict{String,Int}()
            for id in ids
                n = ladnodes(dir * pre * id * fext)
                n !== nothing && n <= MAXNODES && (sizes[id] = n)
            end
            valid = collect(keys(sizes))
            RAND ? shuffle!(valid) : sort!(valid)
            for p in valid, t in valid
                p == t && continue
                sizes[p] > sizes[t] && continue  # only embed smaller into larger
                push!(list, fmt(p, t))
            end
        end
        RAND && shuffle!(list)
        println("%Generated ", length(list), " instances from benchmark graphs (maxnodes=", MAXNODES, ")")
        return list
    end

# ══ Instance pipeline ══════════════════════════════════════════════════════════════════════════
    function pbpconclusion(ins, suffix="")
        f = proofs*ins*pbp*suffix
        isfile(f) || return ""
        sz = filesize(f)
        open(f) do io
            seek(io, max(0, sz - 500))
            tail = read(io, String)
            m = match(r"conclusion\s+(\w+)", tail)
            m === nothing ? "" : m.captures[1]
        end end

    smol_complete(ins) = isfile(proofs*ins*opb*smol) && !isempty(pbpconclusion(ins, smol))

    # Parse and trim a small proof to trigger JIT compilation of all hot paths before the
    # real instance runs. Without this, JIT time is charged to the first instance's timings.
    # Uses the smallest available opb+pbp pair; skips silently if none exists or if warmup fails.
    # .smol files count as valid warmup targets — they are tiny and exercise the same code paths.
    function warmup_jit()
        candidates = filter(f -> ext(f)==opb && isfile(noext(f)*pbp), readdir(proofs, join=true))
        isempty(candidates) && return
        sort!(candidates, by=f -> filesize(f) + filesize(noext(f)*pbp))
        warm = onlyname(first(candidates))
        # don't warm up on the real instance — its timings would include warmup parse time
        if warm == inst
            length(candidates) < 2 && return
            warm = onlyname(candidates[2])
        end
        try
            store,systemlink,redwitness,_,_,nbopb,varmap,_,_,conclusion,obj,prism = readinstance(proofs, warm)
            sys = PBSystem(store, length(varmap))
            getcone!(zeros(Bool,length(sys.rhs)), Dict{Int,Set{Int}}(), sys, systemlink,
                     nbopb, prism, redwitness, conclusion, obj, Grim())
        catch
            # warmup failure is silent; real work proceeds regardless
        end
    end

    function trimnalyseandcie(ins)
        # resume: if trimmed output already exists and the pbp tail confirms a complete write, skip entirely.
        # checked before the memory wait so finished instances never contend for RAM.
        if !OVERWRITE && smol_complete(ins)
            printstyled("  $ins already done — skipping\n"; color=:blue)
            return
        end
        tryrm(proofs*ins*".out")
        tryrm(proofs*ins*".err")
        if SOLVE
            patfile, tarfile = parsegraphfiles(ins)
            if patfile === nothing
                printstyled("  solve: cannot parse graph paths for $ins\n"; color=:red)
                return
            end
            # resume: proof files already exist and pbp tail confirms a complete write — skip solver.
            if isfile(proofs*ins*opb) && !isempty(pbpconclusion(ins))
                printstyled("  $ins proof exists — skipping solve\n"; color=:blue)
            else
                t = @elapsed ok = runsipsolver(ins, patfile, tarfile)
                if !ok
                    out_content = isfile(proofs*ins*".out") ? read(proofs*ins*".out", String) : ""
                    if occursin("SATISFIABLE", out_content) && !occursin("UNSATISFIABLE", out_content)
                        printstyled("  $ins SAT — skipping\n"; color=:yellow)
                    else
                        printstyled("  $ins solve failed or timed out ($(round(t;digits=1))s)\n"; color=:red)
                    end
                    return
                end
                printstyled("  $ins solved $(round(t;digits=1))s\n"; color=:cyan)
            end
        end
        let c = pbpconclusion(ins)
            if c == "SAT" || c == "NONE"
                printstyled("  $ins $c — skipping\n"; color=:yellow); return
            end
            if isempty(c)
                printstyled("  $ins: no conclusion (truncated proof) — skipping\n"; color=:red)
                open(proofs*ins*".err", "a") do f; println(f, "proof truncated: no conclusion") end
                return
            end
        end
        # size guard: skip instances whose combined opb+pbp exceeds 50 GB to avoid OOM during parsing.
        # checked after SOLVE so the size reflects the freshly generated proof, not a stale file.
        let sz = (isfile(proofs*ins*opb) ? filesize(proofs*ins*opb) : 0) +
                    (isfile(proofs*ins*pbp) ? filesize(proofs*ins*pbp) : 0)
            if sz > 50 * 1024^3
                printstyled("  $ins too large ($(round(sz/1024^3; digits=1)) GB) — skipping\n"; color=:yellow)
                return
            end
        end
        if !NONORM
            printabline(ins)
            parse_time,trim_time,write_time,cone_stats,coremsg = trimnalyse(ins; mode=Grim())
            smol_verif_time,full_verif_time = VERIF ? verify(ins) : (-1,-1)
            printabline2(ins,parse_time,trim_time,write_time,smol_verif_time,full_verif_time,cone_stats)
            !isempty(coremsg) && println(coremsg)
            writeout_verif(ins,smol_verif_time,full_verif_time)
            RESOLV && resolvecore(ins)
        end
        if CLIT
            printabline(ins)
            parse_time,trim_time,write_time,cone_stats,_ = trimnalyse(ins; mode=Clit())
            smol_verif_time,full_verif_time = VERIF ? verify(ins) : (-1,-1)
            printabline2(ins,parse_time,trim_time,write_time,smol_verif_time,full_verif_time,cone_stats)
            writeout_verif(ins,smol_verif_time,full_verif_time)
        end
        if BFS
            printabline(ins)
            parse_time,trim_time,write_time,cone_stats,_ = trimnalyse(ins; mode=Bfs())
            smol_verif_time,full_verif_time = VERIF ? verify(ins) : (-1,-1)
            printabline2(ins,parse_time,trim_time,write_time,smol_verif_time,full_verif_time,cone_stats)
            writeout_verif(ins,smol_verif_time,full_verif_time)
        end end

        # mode: Grim(), Clit(), or Bfs() — see mode structs
    function trimnalyse(ins; mode=Grim())
        prefix = mode isa Bfs ? "gbfs" : mode isa Clit ? "gclt" : "grim"
        parse_time = trim_time = write_time = 0 ; file = ins ; cone_stats = nothing
        parse_time = @elapsed begin
            store,systemlink,redwitness,solirecord,assertrecord,nbopb,varmap,ctrmap,output,conclusion,obj,prism = readinstance(proofs,file)
        end
        inp_lits = length(store.vars)
        writeout_parse(ins, parse_time, nbopb, length(systemlink), inp_lits, length(varmap), prefix)
        sys = PBSystem(store, length(varmap))  # zero-copy: PBSystem reuses FlatEqStore's flat arrays directly
        n = length(sys.rhs)
        cone     = zeros(Bool, n)
        conelits = Dict{Int,Set{Int}}()
        trim_time = @elapsed begin
            cone_timeout = getcone!(cone, conelits, sys, systemlink, nbopb, prism, redwitness, conclusion, obj, mode) === true
        end
        if cone_timeout
            open(proofs*ins*".err", "a") do f; println(f, "getcone timeout after $(trimtimeout)s") end
            return trunc(Int,parse_time),trunc(Int,trim_time),0,cone_stats,""
        end
        writeout_trim(ins, trim_time, cone, nbopb, prefix)
        writeout_conelits(ins, sys, cone, conelits, prefix)
        cone_stats = conelits_stats(sys, cone, conelits)
        printconestat(cone, cone_stats)
        varmap_inv = Vector{String}(undef, length(varmap))
        for (k, v) in varmap; varmap_inv[v] = String(copy(k)); end
        if isempty(output)
            printstyled("  $ins: proof truncated (no output line) — skipping write\n"; color=:red)
            open(proofs*ins*".err", "a") do f; println(f, "proof truncated: output line missing") end
            return trunc(Int,parse_time),trunc(Int,trim_time),0,cone_stats,""
        end
        coremsg = (mode isa Grim && (CORE || RESOLV)) ? writeunsatcore(ins, sys, cone, conelits, varmap_inv, nbopb) : ""
        let expected = nbopb + length(systemlink), actual = length(sys.rhs)
            if expected != actual
                printstyled("  SYNC ERROR $ins: nbopb=$nbopb + systemlink=$(length(systemlink)) = $expected but sys.rhs=$actual (diff=$(expected-actual))\n"; color=:red)
            end
        end
        write_time = @elapsed begin
            writeconedel(proofs,file,sys,cone,conelits,systemlink,redwitness,solirecord,assertrecord,nbopb,varmap_inv,ctrmap,output,conclusion,obj,prism)
        end
        writeout_write(ins, parse_time, trim_time, write_time, prefix)
        return trunc(Int,parse_time),trunc(Int,trim_time),trunc(Int,write_time),cone_stats,coremsg end

# ══ Output & display ══════════════════════════════════════════════════════════════════════════
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

    function writeout_verif(ins, smol_verif_time, full_verif_time)
        smol_verif_time < 0 && full_verif_time < 0 && return
        open(proofs*ins*".out", "a") do f
            smol_verif_time >= 0 && println(f, "veri smol TIME ", smol_verif_time)
            full_verif_time >= 0 && println(f, "veri TIME ",      full_verif_time)
        end end

    const veripbpath = _cluster ?
        "/scratch/arthur/veripb" :
        "/home/arthur_gla/veriPB/trim/VeriPB/target/release/veripb"

    function verify(ins)
        smol_verif_time = full_verif_time = 0
        isfile(veripbpath) || (printstyled("  veripb not found at $veripbpath — skipping verif\n"; color=:yellow); return smol_verif_time,full_verif_time)
        ins2 = proofs*ins
        ins3 = ins2*".smolverif"
        ins4 = ins2*".verif"
        ins31 = ins3*".out"; ins32 = ins3*".err"
        ins41 = ins4*".out"; ins42 = ins4*".err"
        tryrm(ins31); tryrm(ins32)
        smol_verif_time = @elapsed try run(pipeline(ignorestatus(`timeout $trimtimeout $veripbpath $ins2$opb$smol $ins2$pbp$smol`),stdout=ins31,stderr=ins32)) catch e println("\nerr ",ins32) end
        isfile(ins32) && isempty(strip(read(ins32,String))) && tryrm(ins32)
        tryrm(ins41); tryrm(ins42)
        full_verif_time = @elapsed try run(pipeline(ignorestatus(`timeout $trimtimeout $veripbpath $ins2$opb $ins2$pbp`),stdout=ins41,stderr=ins42)) catch e println("\nerr ",ins42) end
        isfile(ins42) && isempty(strip(read(ins42,String))) && tryrm(ins42)
        return trunc(Int,smol_verif_time),trunc(Int,full_verif_time) end

    printgray(s)  = printstyled(s, color=:light_black)
    printyellow(s)= printstyled(s, color=:yellow)
    printred(s)   = printstyled(s, color=:red)
    printgreen(s) = printstyled(s, color=:green)
    printblue(s)  = printstyled(s, color=:blue)
    printcyan(s)  = printstyled(s, color=:cyan)
    function leftcarriage(c,s)
        carriage = string(c-length(s))
        return "\r\033["*carriage*"G"*s end

    # True when output can't use cursor positioning: either multiple threads in the same process
    # (would interleave), or a single-threaded subprocess handling one instance in a batch run.
    par() = Threads.nthreads() > 1 || inst !== nothing

    function printabline(f)
        par() && return  # parallel: skip placeholder, full line printed atomically in printabline2
        printgray("         &          &          &          &      (                   ) &      & ")
        printyellow(f)
        printgray(" \\\\\\hline")
        printcyan(leftcarriage(9, prettybytes(filesize(proofs*f*opb))))
        printcyan(leftcarriage(20,prettybytes(filesize(proofs*f*pbp)))) end

    function printabline2(f, parse_time, trim_time, write_time, smol_verif_time, full_verif_time, cone_stats=nothing)
        if par()
            pb(file) = isfile(file) ? prettybytes(filesize(file)) : "?"
            cone_s = cone_stats !== nothing ? " $(cone_stats.lits_smol)/$(cone_stats.lits_cone) $(cone_stats.vars_used)/$(cone_stats.vars_total)" : ""
            println(rpad(pb(proofs*f*opb),8),           " & ", rpad(pb(proofs*f*pbp),9),
                    " & ", rpad(pb(proofs*f*opb*smol),9)," & ", rpad(pb(proofs*f*pbp*smol),9),
                    " & ", rpad(parse_time+trim_time+write_time+max(0,smol_verif_time),5),
                    " (", rpad(parse_time,4), rpad(trim_time,4), rpad(write_time,4), rpad(smol_verif_time,5), ")",
                    " & ", rpad(full_verif_time,5), " & ", f, " \\\\\\hline%", cone_s)
            flush(stdout)
            return
        end
        printgreen(leftcarriage(31,prettybytes(filesize(proofs*f*opb*smol))))
        printgreen(leftcarriage(42,prettybytes(filesize(proofs*f*pbp*smol))))
        printgreen(leftcarriage(49,string(parse_time+trim_time+write_time+max(0,smol_verif_time))))
        printblue(leftcarriage(54,string(parse_time)))
        printgreen(leftcarriage(59,string(trim_time)))
        printblue(leftcarriage(64,string(write_time)))
        printcyan(leftcarriage(69,string(smol_verif_time)))
        printcyan(leftcarriage(78,string(full_verif_time)))
        println() end

    function printconestat(cone, cone_stats)
        par() && return  # cursor-based stat doesn't compose with parallel output
        printgray("\r\033[99G% "*string(sum(cone))*"/"*string(length(cone))*" "
                                *string(cone_stats.vars_used)*"/"*string(cone_stats.vars_total)*"\n") end

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

# ══ Statistics ══════════════════════════════════════════════════════════════════════════
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

    # Counts how many resolv iterations ran for ins by checking coreN .out files.
    function countresolveiters(ins)
        n = 0
        while isfile(proofs * ins * ".core$(n+1)" * ".out"); n += 1 end
        return n end

    # Parses solver-written fields from the top of ins.out (appended by runsipsolver).
    function parsesolverstats(ins)
        outfile = proofs * ins * ".out"
        isfile(outfile) || return nothing
        content = read(outfile, String)
        gi(r) = (m = match(r, content)) !== nothing ? parse(Int, m.captures[1]) : nothing
        gs(r) = (m = match(r, content)) !== nothing ? m.captures[1] : nothing
        (pat_vertices = gi(r"pattern_vertices\s*=\s*(\d+)"),
         tar_vertices = gi(r"target_vertices\s*=\s*(\d+)"),
         runtime_ms   = gi(r"runtime\s*=\s*(\d+)"),
         status       = gs(r"status\s*=\s*(\w+)")) end

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
        printpoints2Dlog(table, T_GRIM_CONE, T_GRIM_NBEQ, "grim CONE", "grim NBEQ")
        printratios(table)
        # resolv iteration counts — inferred from coreN .out file existence
        iters = [countresolveiters(t[1]) for t in table if !occursin(".core", t[1])]
        if any(i -> i > 0, iters)
            println("── Resolv iterations ──")
            println("  max   : ", maximum(iters))
            println("  mean  : ", round(sum(iters) / length(iters); digits=2))
            maxiters = maximum(iters)
            for k in 0:maxiters
                c = count(==(k), iters)
                c > 0 && println("  iter=", k, " : ", c, " instance(s)")
            end
            maxins = [t[1] for t in table if !occursin(".core", t[1]) && countresolveiters(t[1]) == maxiters]
            println("  max instances: ", join(maxins, ", "))
            println()
        end
        walltxt = proofs * "wall.txt"
        if isfile(walltxt)
            wall = parse(Float64, readline(walltxt))
            println("── Wall time ──")
            println("  ", round(wall; digits=1), "s")
            println()
        end end

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

# ══ Utilities ══════════════════════════════════════════════════════════════════════════
    # MemAvailable from /proc/meminfo includes reclaimable page cache, unlike Sys.free_memory() (MemFree only).
    # On a busy cluster reading large proof files, page cache can consume hundreds of GB, making MemFree
    # appear critically low while the system actually has plenty of usable memory.
    function available_memory()
        if isfile("/proc/meminfo")
            for line in eachline("/proc/meminfo")
                startswith(line, "MemAvailable:") && return parse(Int, split(line)[2]) * 1024
            end
        end
        return Sys.free_memory()  # fallback for non-Linux
    end

    # Read the resident set size of a subprocess from /proc/PID/status (Linux only).
    # Returns GB; 0.0 if the process already exited or on non-Linux.
    function process_rss_gb(pid::Int)
        try
            for line in eachline("/proc/$pid/status")
                startswith(line, "VmRSS:") && return parse(Int, split(line)[2]) / 1024^2
            end
        catch end
        return 0.0
    end

    const argflags = Set(["bfs","clit","core","verif","no","rand","sort","clean","atable",
                          "profile","solve","resolv","allgraphs"])
    onlyname(x) = splitext(basename(x))[1]
    ext(x) = splitext(basename(x))[2]
    noext(x) = splitext(x)[1]
    filesize(file) = stat(file).size
    inssize(file) = filesize(proofs*file*opb) + filesize(proofs*file*pbp)
    tryrm(s) = if isfile(s) rm(s) end
    remove(s,c) = replace(s,c=>"")
    const tabhead = "\\begin{tabular}{|cc|cc|c|c|c|}\\hline sizes & & &  & times (s) & & Instance\\\\\\hline\nopb & pbp & smol o & smol p & grim time (parse trim write verif) & veri time & \\\\\\hline"
    const tabfoot = "\\end{tabular}\\\\\n"

# ══ Debug ══════════════════════════════════════════════════════════════════════════════
module Dumping
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
# ══ Data structures ═════════════════════════════════════════════════════════════════════
    struct Lit
        coef::Int
        sign::Bool
        var::Int end

    mutable struct Eq
        lits::Vector{Lit}   # literals (coef, sign, var triples), sorted by var
        rhs::Int end        # right-hand side constant (sum of satisfied lits >= rhs)

    # Growable flat CSR store for equations parsed from .opb and .pbp files.
    # Replaces Vector{Eq} as the persistent representation, eliminating millions of
    # Eq/Vector{Lit}/Lit heap allocations. Processing functions (solvepol, processred, etc.)
    # still use temporary Eq values for arithmetic — those are short-lived and collected quickly.
    mutable struct FlatEqStore
        vars    :: Vector{Int32}   # flat literal variable indices
        coefs   :: Vector{Int32}   # flat literal coefficients
        signs   :: BitVector       # flat literal signs
        rhs     :: Vector{Int64}   # one rhs per equation
        row_ptr :: Vector{Int32}   # CSR row pointers, length = n_eqs+1; row_ptr[i]:row_ptr[i+1]-1 is eq i
    end
    FlatEqStore() = FlatEqStore(Int32[], Int32[], BitVector(), Int64[], Int32[1])

    function push_eq!(s::FlatEqStore, eq::Eq)
        for l in eq.lits
            push!(s.vars,  Int32(l.var))
            push!(s.coefs, Int32(l.coef))
            push!(s.signs, l.sign)
        end
        push!(s.rhs,     Int64(eq.rhs))
        push!(s.row_ptr, Int32(s.row_ptr[end] + length(eq.lits)))
    end

    # Normalises lits in-place (make all coefs positive) and pushes directly into the store.
    # Replaces the normcoefeq(eq) + push_eq!(store, eq) pair without allocating an Eq object.
    function push_eq_normalized!(s::FlatEqStore, lits::Vector{Lit}, b::Int)
        b2 = 0
        for l in lits
            if l.coef < 0; b2 += -l.coef; end
        end
        b += b2
        for l in lits
            if l.coef < 0
                push!(s.vars, Int32(l.var)); push!(s.coefs, Int32(-l.coef)); push!(s.signs, !l.sign)
            else
                push!(s.vars, Int32(l.var)); push!(s.coefs, Int32(l.coef)); push!(s.signs, l.sign)
            end
        end
        push!(s.rhs,     Int64(b))
        push!(s.row_ptr, Int32(s.row_ptr[end] + length(lits)))
    end

    function get_eq(s::FlatEqStore, i::Int)
        r = Int(s.row_ptr[i]):Int(s.row_ptr[i+1])-1
        Eq([Lit(Int(s.coefs[k]), s.signs[k], Int(s.vars[k])) for k in r], Int(s.rhs[i]))
    end

    Base.length(s::FlatEqStore)      = length(s.rhs)
    last_eq(s::FlatEqStore)          = get_eq(s, length(s))
    # replicates isequal(system[end], Eq([],1)): last eq has zero lits and rhs==1
    store_last_empty(s::FlatEqStore) = length(s) > 0 &&
                                       s.row_ptr[end] == s.row_ptr[end-1] &&
                                       s.rhs[end] == 1

    mutable struct Red
        witness::Vector{Lit}                # flat pairs: witness[2k-1]=source var, witness[2k]=target var (var=0 → const-0, var=-1 → const-1)
        range::UnitRange{Int64}             # system id range of the entire red block (reversed negation → conclusion)
        proof_goal_ranges::Vector{UnitRange{Int64}} end  # id ranges of individual proof goals inside the block

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

    Trail(n_vars::Int) = Trail(Int32[], Int32[], zeros(Int, n_vars), zeros(Int8, n_vars))
    @inline function reset!(t::Trail)
        empty!(t.var); empty!(t.eq)
        fill!(t.pos, 0); fill!(t.assi, 0) end

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

    function PBSystem(store::FlatEqStore, n_vars::Int)
        # Forward arrays are reused directly from the store — zero copy.
        # Only the inverse index (var_ptr, var_eqs) needs to be computed fresh.
        vars    = store.vars
        coefs   = store.coefs
        signs   = store.signs
        rhs     = store.rhs
        row_ptr = store.row_ptr
        n_lits  = length(vars)

        var_count = zeros(Int32, n_vars)
        for v in vars; var_count[v] += 1; end
        var_ptr = Vector{Int32}(undef, n_vars + 1)
        var_ptr[1] = 1
        for v in 1:n_vars
            var_ptr[v+1] = var_ptr[v] + var_count[v]
        end
        var_eqs = Vector{Int32}(undef, n_lits)
        fill!(var_count, 0)
        n_eqs = length(rhs)
        for e in 1:n_eqs
            for k in Int(row_ptr[e]):Int(row_ptr[e+1])-1
                v = vars[k]
                var_eqs[var_ptr[v] + var_count[v]] = e
                var_count[v] += 1
            end
        end

        return PBSystem(vars, coefs, signs, rhs, row_ptr, var_ptr, var_eqs) end

    eqrange(sys::PBSystem, e) = Int(sys.row_ptr[e]):Int(sys.row_ptr[e+1])-1
    varrange(sys::PBSystem, v) = Int(sys.var_ptr[v]):Int(sys.var_ptr[v+1])-1
    function slack(eq::Eq, assi::Vector{Int8})
        c = 0
        for l in eq.lits
            val = assi[l.var]
            (val == 0 || (l.sign && val == 1) || (!l.sign && val == 2)) && (c += l.coef)
        end
        return c - eq.rhs end

    @inline function slack(sys::PBSystem, e::Int, assi::Vector{Int8})
        c = zero(Int32)
        @inbounds for i in eqrange(sys, e)
            val  = assi[Int(sys.vars[i])]
            sign = sys.signs[i]
            unaffected = (val == 0) | (sign & (val == 1)) | (!sign & (val == 2))
            c += unaffected ? sys.coefs[i] : zero(Int32)
        end
        return c - sys.rhs[e] end

    inprism(n, prism::BitVector)             = n <= length(prism) && prism[n]
    inprism(n, prism::Vector{UnitRange{Int64}}) = any(n in r for r in prism)
    @inline function setconelits(conelits, v, id)
        push!(get!(Set{Int}, conelits, id), v) end

    # CSR storage for proof step link data — zero allocation per step during parsing.
    # idx[i] encodes entry type:  k>0 → flat data at ptr[k]:ptr[k+1]-1
    #                              k<0 → singleton rule type (shared const, never mutated)
    #                              k=0 → mutable entry in extra (RUP cone + RED with refs)
    mutable struct SystemLink
        data::Vector{Int}             # flat concatenated link payloads for non-singleton steps
        ptr::Vector{Int}              # ptr[k]:ptr[k+1]-1 = k-th flat entry range in data
        idx::Vector{Int}              # one per proof step — see encoding above
        extra::Dict{Int,Vector{Int}}  # mutable per-step vectors (RUP cone-visited, RED refs)
    end
    SystemLink() = SystemLink(Int[], Int[1], Int[], Dict{Int,Vector{Int}}())
    Base.length(sl::SystemLink) = length(sl.idx)
    Base.eachindex(sl::SystemLink) = 1:length(sl.idx)
    Base.isassigned(sl::SystemLink, i::Int) = 1 <= i <= length(sl.idx)

    @inline function _sl_singleton(t::Int)
        t == -1  ? _LINK_RUP  :
        t == -4  ? _LINK_RED  :
        t == -3  ? _LINK_IARES :
        t == -10 ? _LINK_END  :
        t == -7  ? _LINK_PG7  :
        t == -21 ? _LINK_SOLI :
        t == -20 ? _LINK_SOLX : error("unknown singleton type $t") end

    # Read: zero allocation — returns a view into flat data or a shared singleton const.
    function Base.getindex(sl::SystemLink, i::Int)
        k = @inbounds sl.idx[i]
        k > 0 ? (@inbounds @view sl.data[sl.ptr[k]:sl.ptr[k+1]-1]) :
        k < 0 ? _sl_singleton(k) :
                 sl.extra[i] end

    # Push singleton (RUP, RED, SOLI, SOLX, …): one Int stored, no heap allocation.
    sl_push_singleton!(sl::SystemLink, type::Int) = push!(sl.idx, type)

    # Push non-singleton link with pre-built data vector (POL, IA, assumption-with-hints).
    # Appends the data in-place — no copy of the source vector.
    function sl_push_data!(sl::SystemLink, link::AbstractVector{Int})
        k = length(sl.ptr)
        append!(sl.data, link)
        push!(sl.ptr, length(sl.data) + 1)
        push!(sl.idx, k) end

    # Specialised two-element push (IA: [-3, antecedent]) — avoids a temp Vector{Int}.
    function sl_push_2!(sl::SystemLink, a::Int, b::Int)
        k = length(sl.ptr)
        push!(sl.data, a, b)
        push!(sl.ptr, length(sl.data) + 1)
        push!(sl.idx, k) end

    # Return (creating if needed) the mutable Vector for step i (RUP cone / RED refs).
    function sl_get_mut!(sl::SystemLink, i::Int)
        k = sl.idx[i]
        k == 0 && return sl.extra[i]
        vec = k < 0 ? Int[k] : collect(@inbounds @view sl.data[sl.ptr[k]:sl.ptr[k+1]-1])
        sl.extra[i] = vec
        sl.idx[i] = 0
        return vec end

# ══ Parser ══════════════════════════════════════════════════════════════════════════════
    # Pre-allocated singleton link vectors for rule types whose systemlink entries need no antecedents.
    # Singletons are safe to share ONLY if nothing pushes into them. _LINK_RUP is the exception:
    # ante_into_frontier! lazily replaces a RUP entry with a fresh vector on first cone visit,
    # so the singleton is only ever observed (never mutated) during parsing.
    const _LINK_RUP  = Int[-1]   # rup — sentinel; replaced lazily by ante_into_frontier! for cone steps
    const _LINK_RED  = Int[-4]   # inline red (no subproof)
    const _LINK_IARES = Int[-3]  # ia (single-antecedent pol) result
    const _LINK_END  = Int[-10]  # end-of-subproof marker
    const _LINK_PG7  = Int[-7]   # proofgoal #1
    const _LINK_SOLI = Int[-21]  # soli
    const _LINK_SOLX = Int[-20]  # solx

    # Contiguous byte view into the mmap'd file buffer — the token type returned by tokenize!.
    # Safe as long as the mmap array stays alive (it is kept alive by readopb/readproof's local ref).
    const ByteSpan = SubArray{UInt8,1,Vector{UInt8},Tuple{UnitRange{Int64}},true}

    # Byte-level token comparison against a compile-time String literal (avoids String allocation).
    @inline function tok_eq(v::AbstractVector{UInt8}, s::String)
        n = ncodeunits(s)
        length(v) == n || return false
        @inbounds for i in 1:n
            v[i] == codeunit(s, i) || return false
        end
        return true
    end

    @inline tok_in(v::AbstractVector{UInt8}, ss) = any(s -> tok_eq(v, s), ss)

    # Parse a signed decimal integer from raw bytes — no String allocation on the hot path.
    @inline function parse_int_bytes(v::AbstractVector{UInt8})
        i = 1
        @inbounds neg = v[1] == UInt8('-')
        neg && (i = 2)
        n = 0
        @inbounds while i <= length(v)
            n = n * 10 + (v[i] - UInt8('0'))
            i += 1
        end
        return neg ? -n : n
    end

    # Zero-allocation line tokenizer. Replaces both remove(ss,";") and split(ss,keepempty=false).
    # Skips ';' characters inline so no intermediate allocation is needed for semicolon stripping.
    # Uses task_local_storage so the buffer persists across all iterations on the same task
    # (safe with @threads :greedy — each task owns its buffer and never shares it).
    # Returns a reference to the task-local buffer — valid only until the next tokenize! call on this task.
    function tokenize!(ss::AbstractVector{UInt8})
        buf = get!(task_local_storage(), :tokbuf, ByteSpan[])
        empty!(buf)
        i = 1
        n = length(ss)
        while i <= n
            while i <= n
                @inbounds b = ss[i]
                b == UInt8(' ') || b == UInt8('\t') || b == UInt8(';') ? i += 1 : break
            end
            i > n && break
            j = i
            while j <= n
                @inbounds b = ss[j]
                b == UInt8(' ') || b == UInt8('\t') || b == UInt8(';') ? break : (j += 1)
            end
            push!(buf, @view ss[i:j-1])
            i = j
        end
        return buf
    end

    # Iterate over lines of content as byte views — zero copy per line.
    # Uses mmap'd Vector{UInt8} to avoid the file→heap memcpy that read(file,String) incurs.
    function _scan_lines(cb, content::AbstractVector{UInt8})
        i = 1
        n = length(content)
        while i <= n
            j = findnext(==(UInt8('\n')), content, i)
            last = j === nothing ? n : j - 1
            cb(@view content[i:last])
            i = j === nothing ? n + 1 : j + 1
        end
    end

    function readinstance(path,file)
        store,varmap,ctrmap,obj = readopb(path,file)
        nbopb = length(store)
        store,systemlink,redwitness,solirecord,assertrecord,output,conclusion = readproof(path,file,store,varmap,ctrmap,obj)
        prism = availableranges(redwitness)
        return store,systemlink,redwitness,solirecord,assertrecord,nbopb,varmap,ctrmap,output,conclusion,obj,prism end

    function readopb(path,file)
        store = FlatEqStore()
        varmap = Dict{Vector{UInt8},Int}()
        ctrmap = Dict{String, Int}()
        obj = ""
        # mmap the file: maps OS page cache directly into virtual address space — zero memcpy.
        # Avoids the file→heap copy that read(file,String) incurs. minfreemem already gates this.
        content_opb = Mmap.mmap(path*file*opb)
        c = 1
        _scan_lines(content_opb) do ss
            if isempty(ss) || ss[1]==UInt8('*') return end
            st = tokenize!(ss)
            if st[1][1]==UInt8('@')
                ctrmap[String(view(st[1], 2:length(st[1])))] = c
                st = st[2:end]
            end
            if ss[1] == UInt8('m')
                obj = readobj(st,varmap)
            else
                readeq_push!(store, st, varmap, 1:2:length(st))
                c+=1
            end
        end
        return store,varmap,ctrmap,obj end

    # readobj stores its result permanently (as obj), so it needs its own copy.
    # All other callers (readeq → normcoefeq → push_eq!) are done with lits before the next readlits call.
    readobj(st,varmap) = copy(readlits(st,varmap,2:2:length(st)))

    function readlits(st,varmap,range)
        # reuse a task-local buffer — safe because callers consume lits before the next readlits call.
        lits = get!(task_local_storage(), :litbuf, Lit[])
        n = length(range)
        resize!(lits, n)
        for i in range
            coef = parse_int_bytes(st[i])
            sign = st[i+1][1]!=UInt8('~')
            var = readvar(st[i+1],varmap)
            lits[(i - range.start)÷range.step+1] = Lit(coef,sign,var)
        end
        sort!(lits,by=x->x.var)
        return lits end

    function readvar(s,varmap)
        if s[1]==UInt8(';') throw("; added as variable") end
        # Strip '~' prefix; both branches stay as AbstractVector{UInt8} — zero allocation.
        # Dict{Vector{UInt8},Int} lookup with ByteSpan key works via generic array hash/isequal.
        tmp = s[1]==UInt8('~') ? @view(s[2:end]) : s
        if haskey(varmap,tmp)
            return varmap[tmp]
        end
        varmap[copy(tmp)] = length(varmap)+1   # copy once per unique variable name
        return length(varmap) end

    readeq(st,varmap) = readeq(st,varmap,1:2:length(st))
    function readeq(st,varmap,r)
        lits = readlits(st,varmap,r.start:r.step:(r.stop-2))
        lits,b_corr = merge(lits)
        return Eq(lits, parse_int_bytes(st[r.start+2length(r)-1])-b_corr) end

    # Like readeq but pushes directly into the store without allocating an Eq.
    # Used in readopb and hot proof-step paths where the eq is never needed as an object.
    # Always pushes — an empty equation (no lits) IS the contradiction (e.g. >= 1 with no vars)
    # and must occupy a slot in the store so that store and systemlink stay in sync.
    function readeq_push!(store::FlatEqStore, st, varmap, r)
        lits = readlits(st, varmap, r.start:r.step:(r.stop-2))
        lits, b_corr = merge(lits)
        b = parse_int_bytes(st[r.start+2length(r)-1]) - b_corr
        if isempty(lits) && b != 1
            printstyled("  warning: unexpected empty eq with b=$b (expected contradiction b=1)\n"; color=:yellow)
        end
        push_eq_normalized!(store, lits, b)
        return true end

    function merge(lits)
        b_corr=0
        to_delete = get!(task_local_storage(), :delbuf, Int[])
        empty!(to_delete)
        i=j=1
        while i<length(lits)
            j = i
            while j<length(lits) && lits[i].var==lits[j+1].var
                j+=1
                lits[i],cc = add(lits[i],lits[j])
                b_corr+=cc
                push!(to_delete,j)
            end
            i = j+1
        end
        if !isempty(to_delete)
            deleteat!(lits,to_delete)
        end
        return lits,b_corr end

    function add(lit1,lit2)
        lit1,c1 = normlit(lit1)
        lit2,c2 = normlit(lit2)
        return Lit(lit1.coef+lit2.coef,true,lit1.var),c1+c2 end

    normlit(l) = !l.sign ? (Lit(-l.coef,true,l.var),l.coef) : (l,0)
    function normcoefeq(eq)
        c = 0
        for i in eachindex(eq.lits)
            l = eq.lits[i]
            if l.coef < 0
                eq.lits[i] = Lit(-l.coef, !l.sign, l.var)
                c += -l.coef
            end
        end
        eq.rhs = c + eq.rhs end
 
    function readproof(path,file,store,varmap,ctrmap,obj)
        systemlink = SystemLink()
        redwitness = Dict{Int, Red}()
        solirecord = Dict{Int, Vector{Lit}}()
        assertrecord = Dict{Int, String}()
        prism = Vector{UnitRange{Int64}}()
        output = conclusion = ""
        c = length(store)+1
        nbopb = length(store)
        # mmap the proof file: same rationale as readopb — zero memcpy from OS page cache.
        content_pbp = Mmap.mmap(path*file*pbp)
        _scan_lines(content_pbp) do ss
            if isempty(ss) return end
            i = findfirst(==(UInt8('%')), ss)
            if i !== nothing
                if i<3 return end
                if ss[1]==UInt8('a')
                    assertrecord[c] = String(@view ss[i+1:end])
                end
                ss = @view ss[1:i-1]
            end
            st = tokenize!(ss)
            if st[1][1]==UInt8('@')
                ctrmap[String(view(st[1], 2:length(st[1])))] = c
                st = st[2:end]
            end
            type = st[1]
            pushed = false
                if tok_eq(type,"rup") || tok_eq(type,"u") pushed = processrup_push!(store,st,varmap,systemlink)
            elseif tok_eq(type,"pol") || tok_eq(type,"p") pushed = processpol_push!(store,st,varmap,systemlink,c,ctrmap,nbopb)
            elseif tok_eq(type,"a")                        pushed = processassumption_push!(store,st,varmap,systemlink,assertrecord,c)
            elseif tok_eq(type,"ia")                       pushed = processia_push!(store,st,varmap,ctrmap,c,systemlink)
            elseif tok_eq(type,"red")                      c,_ = processred(store,systemlink,st,varmap,redwitness,c); pushed = true
            elseif tok_eq(type,"sol")                      throw("trimmed SAT is the solution")
            elseif tok_eq(type,"soli")                     pushed = processsoli_push!(store,st,varmap,systemlink,c,prism,obj,solirecord)
            elseif tok_eq(type,"solx")                     pushed = processsolx_push!(store,st,varmap,systemlink,c,prism)
            elseif tok_eq(type,"output")                   output = String(st[2])
            elseif tok_eq(type,"conclusion")
                conclusion = String(st[2])
                if conclusion == "BOUNDS"
                    conclusion = String(ss)
                elseif !store_last_empty(store) && (conclusion == "SAT" || conclusion == "NONE")
                    throw("SAT Not supported..")
                end
            elseif !tok_in(type, ["%","*","wiplvl","w","setlvl","#","f","d","del","end","pseudo-Boolean"])
                printstyled("  [warn] unknown line head (skipped): $(String(ss))\n"; color=:yellow)
            end
            pushed && (c+=1)
        end
        return store,systemlink,redwitness,solirecord,assertrecord,output,conclusion end

    # Hot-path version: pushes directly into the store without allocating an Eq.
    # Always returns true: every systemlink push must have a matching store push to keep indices in sync.
    # Uses _LINK_RUP singleton — zero allocation per RUP step during parsing (~millions per large file).
    # ante_into_frontier! replaces the singleton with a fresh vector on first cone visit (lazy allocation).
    function processrup_push!(store,st,varmap,systemlink)
        sl_push_singleton!(systemlink, -1)
        readeq_push!(store, st, varmap, 2:2:length(st))
        return true end

    # Hot-path version: pushes directly into the store without allocating a final Eq.
    # Uses a task-local link buffer so solvepol can extend it without repeated reallocation;
    # one copy() at the end replaces the old pattern of capacity-doubling from [-2] to [-2,x,...].
    function processpol_push!(store,st,varmap,systemlink,c,ctrmap,nbopb)
        linkbuf = get!(task_local_storage(), :linkbuf, Int[])
        empty!(linkbuf); push!(linkbuf, -2)
        lits,b = solvepol(st,store,linkbuf,c,varmap,ctrmap,nbopb)
        if isempty(lits) && b==0; throw("POL empty"); end
        sl_push_data!(systemlink, linkbuf)  # append in-place: no copy of linkbuf needed
        push_eq_normalized!(store, lits, b)
        push!(get_lit_pool(), lits)        # return final lits buffer to pool for reuse by next pol step
        return true end

        # Evaluates a pol (polynomial combination) line and records its structure in `link`.
        # link encoding: positive values = constraint ids; negative sentinels below:
        #   -1=+  -2=*  -3=d  -4=s  -5=w  -(100v+99)=literal axiom var v positive  -(100v+100)=negative
        # (The -(100v+99/100) scheme reserves negatives ≤ -99 for literals, leaving -1..-5 for operators.)
    function solvepol(st,store,link,init,varmap,ctrmap,nbopb)
        i = st[2]
        id = i[1]==UInt8('@') ? ctrmap[String(view(i,2:length(i)))] : parse_int_bytes(i)
        if id<0
            id = init+id                               # negative ids are relative to current position
        end
        eq = get_eq(store,id)
        # reuse a task-local stack vector across pol calls to avoid per-call Vector{Eq} allocation
        stack = get!(task_local_storage(), :solvestack, Eq[])
        empty!(stack)
        weakvar = ""
        push!(stack,eq)
        push!(link,id)
        lastsaturate = false                           # defer final saturate: apply after null-lit removal
        for j in 3:length(st)
            i=st[j]
            if tok_eq(i,";")
                continue
            elseif tok_eq(i,"+")
                push!(stack,addeq(pop!(stack),pop!(stack)))
                push!(link,-1)
            elseif tok_eq(i,"*")
                multiply!(first(stack),link[end])      # in-place: no new Eq/Vector{Lit} allocation
                push!(link,-2)
            elseif tok_eq(i,"d")
                divide!(first(stack),link[end])        # in-place: no new Eq/Vector{Lit} allocation
                push!(link,-3)
            elseif tok_eq(i,"s")
                if j == length(st)
                    lastsaturate = true                # last op: defer so null lits are removed first
                else
                    normcoefeq(first(stack))
                    saturate(first(stack))
                end
                push!(link,-4)
            elseif tok_eq(i,"w")
                weaken!(first(stack),weakvar)          # in-place: no new Eq/Vector{Lit} allocation
                push!(link,-5)
            elseif !isdigit(Char(i[1])) && i[1]!=UInt8('@') && i[1]!=UInt8('-')  # literal axiom
                if length(st)>j && tok_eq(st[j+1],"w")
                    weakvar = readvar(i,varmap)
                    push!(link,-100weakvar-99)         # encode as weakening target (no stack push)
                else
                    sign = i[1]!=UInt8('~')
                    var = readvar(i,varmap)
                    push!(stack,Eq([Lit(1,sign,var)],0))
                    push!(link,-100var-99sign)         # encode literal: -(100v+99) if positive, -(100v+100) if negative
                end
            elseif !tok_eq(i,"0")
                id = i[1]==UInt8('@') ? ctrmap[String(view(i,2:length(i)))] : parse_int_bytes(i)
                if id<1
                    id = init+id
                end
                push!(link,id)
                if !tok_in(st[j+1],["*","d"])
                    push!(stack,get_eq(store,id))
                end
            end
        end
        eq = pop!(stack)
        lits2 = removenulllits(eq.lits)
        if length(link)==2
            link[1] = -3                               # pol with single antecedent and no ops is really an ia
        end
        b = eq.rhs
        if lastsaturate                                # apply normcoefeq+saturate inline to avoid Eq allocation
            b2 = 0
            for i in eachindex(lits2)
                l = lits2[i]; if l.coef < 0; lits2[i] = Lit(-l.coef,!l.sign,l.var); b2 += -l.coef; end
            end
            b += b2
            for i in eachindex(lits2)
                l = lits2[i]; l.coef > b && (lits2[i] = Lit(b,l.sign,l.var))
            end
        end
        return lits2, b end

    # Task-local pool of reusable Lit vectors for addeq intermediate results.
    # After warmup (a few pol steps), the pool holds enough buffers for the max concurrent
    # stack depth and allocation rate drops to near zero for addeq.
    get_lit_pool() = get!(task_local_storage(), :lit_pool, Vector{Lit}[])

    function addeq(eq1, eq2)
        lit_pool = get_lit_pool()
        lits1 = eq1.lits; lits2 = eq2.lits
        # take output buffer from pool (or allocate on first use)
        out = isempty(lit_pool) ? Lit[] : pop!(lit_pool)
        empty!(out); sizehint!(out, length(lits1) + length(lits2))
        c = 0
        i = j = 1
        while i <= length(lits1) && j <= length(lits2)
            if lits1[i].var < lits2[j].var
                push!(out, lits1[i]); i += 1
            elseif lits1[i].var > lits2[j].var
                push!(out, lits2[j]); j += 1
            else
                tmplit, tmpc = add(lits1[i], lits2[j])
                c += tmpc
                tmplit.coef != 0 && push!(out, tmplit)
                i += 1; j += 1
            end
        end
        while i <= length(lits1); push!(out, lits1[i]); i += 1 end
        while j <= length(lits2); push!(out, lits2[j]); j += 1 end
        # both input Lit vectors are now consumed — return them to the pool
        push!(lit_pool, lits1)
        push!(lit_pool, lits2)
        return Eq(out, eq1.rhs + eq2.rhs - c) end

    removenulllits(lits) = filter!(x->x.coef!=0,lits)
    function multiply!(eq,d)
        for i in eachindex(eq.lits)
            l = eq.lits[i]; eq.lits[i] = Lit(l.coef*d, l.sign, l.var)
        end
        eq.rhs *= d end

    function divide!(eq,d)
        normcoefeq(eq)
        for i in eachindex(eq.lits)
            l = eq.lits[i]; eq.lits[i] = Lit(ceil(Int,l.coef/d), l.sign, l.var)
        end
        eq.rhs = ceil(Int,eq.rhs/d) end

    function saturate(eq)
        for i in eachindex(eq.lits)
            l = eq.lits[i]
            l.coef > eq.rhs && (eq.lits[i] = Lit(eq.rhs, l.sign, l.var))
        end end

    function weaken!(eq,var)
        b = eq.rhs
        i = 1
        while i <= length(eq.lits)
            l = eq.lits[i]
            if l.var == var; b -= l.coef; deleteat!(eq.lits, i)
            else i += 1 end
        end
        eq.rhs = b end

    function processassumption_push!(store,st,varmap,systemlink,assertrecord,c)
        eq = readeq(st,varmap,2:2:length(st))
        if haskey(assertrecord,c)
            hints = split(assertrecord[c],keepempty=false)[2:end]
            link = [-30]
            for i in eachindex(hints)
                push!(link,parse(Int,hints[i]))
            end
            sl_push_data!(systemlink,link)
        else
            sl_push_singleton!(systemlink,-30)
        end
        normcoefeq(eq); push_eq!(store,eq)
        return true end

    function processia_push!(store,st,varmap,ctrmap,c,systemlink)
        eq,l = readia(st,varmap,ctrmap,Eq([],0),c)
        sl_push_2!(systemlink,-3,l)
        normcoefeq(eq); push_eq!(store,eq)
        return true end

    function readia(st,varmap,ctrmap,eq,c)
        if !tok_eq(st[end-1],":") # coef lit coef lit >= b : id
            eq = Eq([],0)
            printstyled("  [warn] missing ia ID: constraint will be ignored\n"; color=:yellow)
        else
            eq = readeq(st,varmap,2:2:length(st)-3)
            l = st[end]
            l = l[1]==UInt8('@') ? ctrmap[String(view(l,2:length(l)))] : parse_int_bytes(l)
            if l<0
                l = c+l
            end
        end
        return eq,l end

    function processred(store,systemlink,st,varmap,redwitness,redid)
        i = findfirst(x->tok_eq(x,":"),st)
        eq = readeq(st[2:i],varmap)
        j = findlast(x->tok_eq(x,":"),st)
        if i==j                                        # no second ':' means no witness range — witness ends at "begin"
            j=length(st)
        end
        w = readwitness(st[i+1:j],varmap)
        sl_push_singleton!(systemlink, -4)
        normcoefeq(eq)
        push_eq!(store,eq)
        redwitness[redid] = Red(w,0:0,[])
        redwitness[length(store)] = Red(w,0:0,[])
        return redid+1,Eq([],0) end

        # Witness is stored as flat pairs: t[2k-1]=source variable, t[2k]=target variable.
        # sign on source encodes polarity of the substitution; sign on target encodes direction.
    function readwitness(st,varmap)
        st = filter(x -> !tok_eq(x,"->") && !tok_eq(x,";"), st)
        t = Vector{Lit}(undef,length(st))
        for i in 1:2:length(st)
            j = i+1
            t[i] = Lit(0,st[i][1]!=UInt8('~'),readwitnessvar(st[i],varmap))  # source
            t[j] = Lit(0,st[j][1]!=UInt8('~'),readwitnessvar(st[j],varmap))  # target
        end
        return t end

    function readwitnessvar(s,varmap)
        if tok_eq(s,"0")
            return 0           # constant 0
        elseif tok_eq(s,"1")
            return -1          # constant 1 (negative sentinel, not a real var id)
        else
            return readvar(s,varmap)
        end end
            

    function processsoli_push!(store,st,varmap,systemlink,c,prism,obj,solirecord)
        sl_push_singleton!(systemlink, -21)
        eq = findbound(store,st,c,varmap,prism,obj,solirecord)
        normcoefeq(eq); push_eq!(store,eq)
        return true end

    function findbound(store,st,c,varmap,prism,obj,solirecord)
        assi = findfullassi(store,st,c,varmap,prism)
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

    function findfullassi(store,st,init,varmap,prism)
        lits = Vector{Lit}(undef,length(st)-2)
        for i in 2:length(st)-1 # sol var var var ; — stop before ";"
            _ = readvar(st[i],varmap)
        end
        assi = zeros(Int8,length(varmap))
        for i in 2:length(st)-1
            sign = st[i][1]!=UInt8('~')
            var = readvar(st[i],varmap)
            lits[i-1] = Lit(1,!sign,var)
            assi[var] = sign ? 1 : 2
        end
        changes = true
        while changes
            changes = false
            for i in 1:init-1 # TODO can be replaced with efficient unit propagation
                if !inprism(i,prism)
                    eq = get_eq(store,i)
                    s = slack(eq,assi)
                    if s<0
                        printstyled("  [warn] sol propagated assignment to contradiction at ctr $i: $st\n"; color=:yellow)
                        printeq(eq)
                        lits = [Lit(l.coef,!l.sign,l.var) for l in lits]
                        return assi
                    else
                        for l in eq.lits                    
                            if l.coef > s && assi[l.var]==0
                                assi[l.var] = l.sign ? 1 : 2 # assi == 1 if l is true, 2 if l is false 0 if l is not assigned
                                changes = true
                            end end end end end end
        return assi end

    function processsolx_push!(store,st,varmap,systemlink,c,prism)
        sl_push_singleton!(systemlink, -20)
        eq = solbreakingctr(store,st,c,varmap,prism)
        normcoefeq(eq); push_eq!(store,eq)
        return true end

    function solbreakingctr(store,st,init,varmap,prism)
        assi = findfullassi(store,st,init,varmap,prism)
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

# ══ Trimmer ═════════════════════════════════════════════════════════════════════════════

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

    function fixante(systemlink::SystemLink, ante::Ante, i)
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
            red_link = sl_get_mut!(systemlink, range.start-nbopb)
            for i in range
                if cone[i]
                    inner = systemlink[i-nbopb]
                    for j in eachindex(inner)
                        k = inner[j]
                        if k > 0 && !(k in red_link) && k < range.start - nbopb
                            push!(red_link, k)   # bubble external ref up to red declaration
                        end
                    end
                end
            end
            sort!(red_link)
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

    function removetrivialantecedents(sys::PBSystem, ante::Ante, conelits, link, init::Int)
        for i in ante.list
            ante.flags[i] || continue
            istrivial(sys, i, conelits) || continue   # antecedent became trivial after lit trimming
            j = findfirst(x -> x == i, link)
            if j === nothing
                printstyled("  [warn] antecedent $i not found in link $link\n"; color=:yellow)
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
                printstyled("  [warn] antecedent $i's addition not found in link $link\n"; color=:yellow)
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
            slack_sum = zero(Int32)
            @inbounds for k in eqrange(sys, eq)
                w = Int(sys.vars[k])
                w == v && continue
                coef = sys.coefs[k]
                slack_sum += coef
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
                slack_sum < b && break
                if wtp > 0 && !is_to_explain[w+1]
                    push!(to_explain, wtp); is_to_explain[w+1] = true
                end
                setconelits(conelits, w, eq)
                slack_sum -= coef
            end
            if slack_sum >= b
                printstyled("  [error] conflicttrail: could not explain var $v in eq $eq\n"; color=:red)
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
            slack_sum = zero(Int32)
            @inbounds for k in eqrange(sys, eq)
                w = Int(sys.vars[k])
                w == v && continue
                coef = sys.coefs[k]
                slack_sum += coef
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
            if prio_sum > slack_sum - b                            # high-priority vars alone explain the slack
                filter!(x -> x[1] == 0 || cone[x[1]] || (ess_set !== nothing && x[3] in ess_set), falsified_lits)
            end
            sort!(falsified_lits; by = x -> (ess_set !== nothing && x[3] in ess_set ? 0 : 1,
                                             x[1] == 0 || cone[x[1]] ? 0 : 1, x[1]))
            v != 0 && setconelits(conelits, v, eq)
            for (_, wtp, w, coef) in falsified_lits
                slack_sum < b && break
                if wtp > 0 && !is_to_explain[w+1]
                    push!(to_explain, wtp); is_to_explain[w+1] = true
                end
                setconelits(conelits, w, eq)
                slack_sum -= coef
            end
            if slack_sum >= b
                printstyled("  [error] conflicttrail: could not explain var $v in eq $eq\n"; color=:red)
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
            slack_sum = zero(Int32)
            @inbounds for k in eqrange(sys, eq)
                w = Int(sys.vars[k])
                w == v && continue
                coef = sys.coefs[k]
                slack_sum += coef
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
                slack_sum < b && break
                if wtp > 0 && !is_to_explain[w+1]
                    push!(to_explain, wtp); is_to_explain[w+1] = true
                end
                setconelits(conelits, w, eq)
                slack_sum -= coef
            end
            if slack_sum >= b
                printstyled("  [error] conflicttrail: could not explain var $v in eq $eq\n"; color=:red)
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
        printstyled("  [error] propagate! found no conflict\n"; color=:red) end

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
    # Variant that records antecedents in systemlink[idx] for the writer.
    # sl_get_mut! lazily upgrades the singleton idx entry to a mutable extra vector on first visit,
    # so parsing pays zero allocation per RUP step and only cone steps (a tiny fraction) allocate.
    @inline function ante_into_frontier!(ante::Ante, frontier, on_frontier, cone, systemlink, idx)
        link = sl_get_mut!(systemlink, idx)
        for j in ante.list; ante.flags[j] || continue; push!(link, j); push_frontier!(frontier, on_frontier, cone, j); end end

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
            conclusion == "UNSAT" && printstyled("  [error] UNSAT contradiction not found\n"; color=:red)
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
                if !do_rup!(firstcontradiction, 0:0) printstyled("  [error] initial rup for bound contradiction failed\n"; color=:red) end
            end
            ante_into_frontier!(ante, frontier, on_frontier, cone, systemlink, firstcontradiction - nbopb)
        end
        red     = Red([], 0:0, [])                     # current red block being processed
        pfgl    = UnitRange{Int64}[]                   # deferred proof goals (ref not yet known to be in cone)
        newpfgl = true
        t_cone_start = time()
        while newpfgl                                  # outer loop: retry deferred proof goals until stable
            newpfgl = false
            while !isempty(frontier)
                if time() - t_cone_start > trimtimeout
                    printstyled("  getcone timeout after $(trimtimeout)s — partial cone\n"; color=:red)
                    return true
                end
                i = pop!(frontier)
                on_frontier[i] || continue             # stale pop guard
                on_frontier[i] = false                 # remove from queue (cone[i] already true since push)
                if i > nbopb
                    rule_type = systemlink[i - nbopb][1]   # rule type: -1=rup, -2=pol, -3=ia, -4=red, ...
                    if rule_type == -1                              # rup
                        if do_rup!(i, 0:0)
                            ante_remove!(ante, i)              # i itself is not its own antecedent
                            ante_into_frontier!(ante, frontier, on_frontier, cone, systemlink, i - nbopb)
                        else
                            printstyled("  [error] rup failed at $i\n"; color=:red)
                            return
                        end
                    elseif rule_type >= -3 || (rule_type == -30 && length(systemlink[i - nbopb]) > 1)  # pol / ia / assumption with hints
                        ante_clear!(ante)
                        fixante(systemlink, ante, i - nbopb)
                        let lnk = sl_get_mut!(systemlink, i - nbopb)
                            fixconelits(sys, conelits, i, ante, lnk)
                            removetrivialantecedents(sys, ante, conelits, lnk, i)
                        end
                        ante_into_frontier!(ante, frontier, on_frontier, cone)
                    elseif rule_type == -10                         # end of red subproof
                        red = redwitness[i]
                        push_frontier!(frontier, on_frontier, cone, red.range.start)  # red declaration itself
                        for subr in red.proof_goal_ranges
                            if systemlink[subr.start - nbopb][1] == -8 && !cone[subr.start]
                                push!(pfgl, subr)              # defer: ref constraint not yet in cone
                            else
                                push_frontier!(frontier, on_frontier, cone, subr.start)
                                push_frontier!(frontier, on_frontier, cone, subr.stop)
                            end
                        end
                    elseif rule_type == -5                          # subproof rup
                        subran_idx = findfirst(x -> i in x, red.proof_goal_ranges)
                        if do_rup!(i, red.proof_goal_ranges[subran_idx])
                            ante_remove!(ante, i)
                            ante_into_frontier!(ante, frontier, on_frontier, cone, systemlink, i - nbopb)
                        else
                            printstyled("  [error] subproof rup failed\n"; color=:red)
                        end
                    elseif rule_type == -6 || rule_type == -8           # subproof pol / proofgoal ref
                        ante_clear!(ante)
                        fixante(systemlink, ante, i - nbopb)
                        ante_into_frontier!(ante, frontier, on_frontier, cone)
                    elseif rule_type == -7                          # proofgoal #1: no external antecedents
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
        sys.rhs[e] != eq.rhs && return false
        r = eqrange(sys, e)
        length(r) != length(eq.lits) && return false
        for (i, lit) in zip(r, eq.lits)
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
        lits = [Lit(-l.coef, l.sign, l.var) for l in eq.lits]
        return Eq(lits,-eq.rhs) end



# ══ Writer ══════════════════════════════════════════════════════════════════════════════
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

    function writewitness(f::IO, red_block, varmap)
        for l in red_block.witness
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
                        printstyled("  [error] del index is 0 for $p (link: $(systemlink[p - nbopb]))\n"; color=:red)
                    else
                        write(f, string(index[p], " "))
                    end
                end
            end
        end
        if isdel write(f, " ;\n") end end

    function invlink(systemlink, succ::Vector{Vector{Int}}, cone, nbopb)
        for i in eachindex(systemlink)
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
        # size by nbopb + all proof steps (including any empty equations) so that
        # constraint IDs in pol links — which count every systemlink entry — are always in range.
        succ = Vector{Vector{Int}}(undef, nbopb + length(systemlink))
        dels = zeros(Bool, length(sys.rhs))
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
                    rule_type = systemlink[i - nbopb][1]
                    if rule_type == -1               # rup
                        cl = get(conelits, i, nothing)
                        if cl !== nothing; writeuconelits(f, sys, i, varmap, cl)
                        else              writeu(f, sys, i, varmap) end
                        if !isempty(eqrange(sys, i))
                            writedel(f, systemlink, i, succ, index, nbopb, dels)
                        end
                    elseif rule_type == -2           # pol
                        writepol(f, systemlink[i - nbopb], index, varmap)
                        writedel(f, systemlink, i, succ, index, nbopb, dels)
                    elseif rule_type == -3           # ia
                        cl = get(conelits, i, nothing)
                        if cl !== nothing; writeiaconelits(f, sys, i, systemlink[i - nbopb][2], index, varmap, cl)
                        else              writeia(f, sys, i, systemlink[i - nbopb][2], index, varmap) end
                        writedel(f, systemlink, i, succ, index, nbopb, dels)
                    elseif rule_type == -4           # red alone
                        writered(f, sys, i, varmap, redwitness[i], "")
                        dels[i] = true
                    elseif rule_type == -5           # rup in subproof
                        print(f, "    "); writeu(f, sys, i, varmap)
                        push!(todel, i)
                    elseif rule_type == -6           # pol in subproof
                        print(f, "    "); writepol(f, systemlink[i - nbopb], index, varmap)
                        push!(todel, i)
                    elseif rule_type == -9           # red with begin (reversed initial equation)
                        writered(f, sys, i, varmap, redwitness[i], " ; begin"; reversed=true)
                        todel = [i]; dels[i] = true
                    elseif rule_type == -7           # red proofgoal #1
                        write(f, "    proofgoal #1\n")
                    elseif rule_type == -8           # red proofgoal normal
                        print(f, "    proofgoal ", index[systemlink[i - nbopb][2]], "\n")
                        push!(todel, i)
                    elseif rule_type == -10          # red proofgoal end
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
                    elseif rule_type == -20          # solx
                        writesolx(f, sys, i, varmap); dels[i] = true
                    elseif rule_type == -21          # soli
                        writesoli(f, solirecord[i], varmap)
                    elseif rule_type == -30          # unchecked assumption
                        if haskey(assertrecord, i)
                            lastindex += justify(f, sys, i, assertrecord[i], index, varmap)
                        else
                            print(f, "a "); writeeq(f, sys, i, varmap)
                        end
                    else
                        printstyled("  [error] unknown rule_type=$rule_type\n"; color=:red)
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
        for l in eq.lits
            print(" ")
            printlitcolor(l.coef, l.sign, l.var, :green)
        end
        println(" >= ", eq.rhs) end

    function printeq(sys::PBSystem, e::Int)
        for k in eqrange(sys, e)
            print(" ")
            printlitcolor(sys.coefs[k], sys.signs[k], Int(sys.vars[k]), :green)
        end
        println(" >= ", sys.rhs[e]) end

# ══ Solver & UNSAT core ═════════════════════════════════════════════════════════════════

    # Returns (node_count, path) for a LAD file, or nothing if unreadable.
    function ladnodes(path)
        isfile(path) || return nothing
        n = tryparse(Int, readline(path))
        n === nothing && return nothing
        return n
    end

    # Returns (pattern_file_path, target_file_path) for an instance name.
    # For ins.coreN, returns the LAD files written by the previous iteration.
    # For original bio*/LV* instances, returns the benchmark graph files.
    function parsegraphfiles(ins)
        m = match(r"^(.+)\.core(\d+)$", ins)
        if m !== nothing
            base, n = m.captures[1], parse(Int, m.captures[2])
            prev_ins = n == 1 ? base : base * ".core$(n-1)"
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
    # Solver stdout/stderr are appended to out_prefix.{out,err} (tryrm clears them beforehand for the original instance).
    # Returns true if both output files were produced.
    function runsipsolver(out_prefix, pat_lad, tar_lad)
        isfile(sipsolverpath) || (printstyled("  solver not found: $sipsolverpath\n"; color=:red); return false)
        errfile = proofs*out_prefix*".err"
        open(proofs*out_prefix*".out", "a") do fout
            open(errfile, "a") do ferr
                run(pipeline(
                    ignorestatus(`timeout $solvertimeout $sipsolverpath
                        --prove $(proofs*out_prefix) --no-clique-detection --format lad $pat_lad $tar_lad`),
                    stdout=fout, stderr=ferr))
            end
        end
        if isfile(errfile)
            err = read(errfile, String)
            if !isempty(strip(err))
                printstyled("  $out_prefix solver stderr: $err"; color=:red)
            else
                tryrm(errfile)
            end
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
                tryrm(cur_pat); tryrm(cur_tar)
                printstyled("  $ins resolv: fixpoint after $(iter-1) iteration(s) ($np pat, $nt tar nodes)\n"; color=:green); return
            end
            prev_np, prev_nt = np, nt
            core_ins = ins * ".core$iter"
            tryrm(proofs*core_ins*".out")
            tryrm(proofs*core_ins*".err")
            t = @elapsed ok = runsipsolver(core_ins, cur_pat, cur_tar)
            if !ok
                tryrm(cur_pat); tryrm(cur_tar)
                printstyled("  resolv: solver failed/timeout at iter $iter ($(round(t;digits=1))s)\n"; color=:red); return
            end
            printstyled("  $ins resolv iter $iter: $np pat / $nt tar → solved $(round(t;digits=1))s\n"; color=:cyan)
            printabline(core_ins)
            parse_time,trim_time,write_time,cone_stats,coremsg = trimnalyse(core_ins; mode=Grim())
            smol_verif_time,full_verif_time = VERIF ? verify(core_ins) : (-1,-1)
            printabline2(core_ins, parse_time, trim_time, write_time, smol_verif_time, full_verif_time, cone_stats)
            !isempty(coremsg) && println(coremsg)
            writeout_verif(core_ins, smol_verif_time, full_verif_time)
            cur_pat = proofs * "vis/" * core_ins * ".core.pat.lad"
            cur_tar = proofs * "vis/" * core_ins * ".core.tar.lad"
        end
    end

    function writeunsatcore(ins, sys::PBSystem, cone::Vector{Bool},
                            conelits::Dict{Int,Set{Int}}, varmap_inv::Vector{String}, nbopb::Int)
        patfile, tarfile = parsegraphfiles(ins)
        (patfile === nothing || !isfile(patfile) || !isfile(tarfile)) && return ""
        P, T = corenodes(sys, cone, varmap_inv, conelits, nbopb)
        isempty(P) && return ""
        adj_p = readlad(patfile)
        adj_t = readlad(tarfile)
        dir = proofs * "vis/"
        mkpath(dir)
        P_set = Set(P); T_set = Set(T)
        writedot(dir * ins * ".pat.dot",  adj_p, P_set)
        writedot(dir * ins * ".tar.dot",  adj_t, T_set)
        writecoreladfile(dir * ins * ".core.pat.lad", adj_p, P)
        writecoreladfile(dir * ins * ".core.tar.lad", adj_t, T)
        for (base, layout) in [(ins*".pat", "circo"), (ins*".tar", "neato")]
            dot = dir * base * ".dot"
            svg = dir * base * ".svg"
            try run(ignorestatus(`neato -Tsvg -K$layout -o$svg $dot`))
            catch; 
                # printstyled("  neato not found — install graphviz to render $svg\n"; color=:yellow) 
            end
        end
        return "  $ins core: $(length(P))/$(length(adj_p)) pat nodes, $(length(T))/$(length(adj_t)) tar nodes"
    end

# ══ Run ══════════════════════════════════════════════════════════════════════════════════

using StatProfilerHTML
if PROFILE
    throw("uncomment here to enable profiling")
    @profilehtml main()
elseif inst !== nothing
    # Subprocess mode: this process was spawned by the batch loop to handle one instance.
    # Output goes directly to the inherited stdout (parent's pipe → parent's tee → terminal + logfile).
    # No second tee needed — adding one would double-buffer and prevent output from flushing.
    main()
else
    logfile = open(joinpath(@__DIR__, "output.log"), "a")
    println(logfile, "\n% run started ", Dates.now())
    flush(logfile)
    orig_out = Base.stdout
    orig_err = Base.stderr
    rd, wr = redirect_stdout()  # redirects stdout fd to a pipe; returns (read_end, write_end)
    redirect_stderr(wr)         # stderr goes to the same pipe
    # drain pipe on a dedicated interactive thread so it never competes with compute threads for scheduling.
    # @async would deadlock: if all compute threads block on pipe writes the async task can never run.
    tee_task = Threads.@spawn :interactive while !eof(rd)
        data = readavailable(rd)
        write(orig_out, data)
        flush(orig_out)
        write(logfile, data)
        flush(logfile)
    end
    try
        main()
    finally
        redirect_stdout(orig_out)
        redirect_stderr(orig_err)
        close(wr)       # signals EOF to the tee task
        wait(tee_task)  # drain remaining data before closing
        close(logfile)
    end
end


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