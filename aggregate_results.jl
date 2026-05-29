#!/usr/bin/env julia
# Aggregate trimming results into a CSV file

using Printf

# Column names for the CSV
const CSV_COLUMNS = [
    "instance",
    # Input stats
    "inp_opb_size", "inp_pbp_size", "inp_total_size",
    "inp_literals", "inp_variables",
    "inp_opb_nbeq", "inp_pbp_nbeq", "inp_total_nbeq",
    # Grim (DFS) results
    "grim_parse_time", "grim_trim_time", "grim_write_time", "grim_total_time",
    "grim_opb_cone", "grim_pbp_cone", "grim_total_cone",
    "grim_cone_literals", "grim_smol_literals", "grim_cone_variables",
    "grim_opb_size", "grim_pbp_size", "grim_total_size",
    # Gclt (clit) results
    "gclt_trim_time",
    "gclt_opb_cone", "gclt_pbp_cone", "gclt_total_cone",
    "gclt_cone_literals", "gclt_smol_literals", "gclt_cone_variables",
    # Gbfs (BFS) results
    "gbfs_trim_time",
    "gbfs_opb_cone", "gbfs_pbp_cone", "gbfs_total_cone",
    "gbfs_cone_literals", "gbfs_smol_literals", "gbfs_cone_variables",
    # Verification
    "veri_smol_time", "veri_total_time",
    "veri_opb_size", "veri_pbp_size", "veri_total_size",
    # Brim
    "brim_time",
    "brim_opb_size", "brim_pbp_size", "brim_total_size",
    # Solver stats (if available)
    "pattern_vertices", "target_vertices", "runtime_ms", "status",
    # Instance classification
    "is_sat", "is_unsat", "has_proof",
    # Error tracking
    "has_error", "error_type", "error_details",
    # Resolv iterations
    "resolv_iterations"
]

function parse_out_file(filepath)
    data = Dict{String, Any}()
    isfile(filepath) || return data

    for line in eachline(filepath)
        # Input stats
        occursin("inp OPB SIZE ", line)      && (data["inp_opb_size"] = tryparse(Int, split(line)[end]))
        occursin("inp PBP SIZE ", line)      && (data["inp_pbp_size"] = tryparse(Int, split(line)[end]))
        occursin("inp SIZE ", line)          && (data["inp_total_size"] = tryparse(Int, split(line)[end]))
        occursin("inp LIT ", line)           && (data["inp_literals"] = tryparse(Int, split(line)[end]))
        occursin("inp VAR ", line)           && (data["inp_variables"] = tryparse(Int, split(line)[end]))

        # Grim stats
        occursin("grim PARSE TIME ", line)   && (data["grim_parse_time"] = tryparse(Float64, split(line)[end]))
        occursin("grim TRIM TIME ", line)    && (data["grim_trim_time"] = tryparse(Float64, split(line)[end]))
        occursin("grim WRITE TIME ", line)   && (data["grim_write_time"] = tryparse(Float64, split(line)[end]))
        occursin("grim TIME ", line)         && (data["grim_total_time"] = tryparse(Float64, split(line)[end]))
        occursin("grim OPB NBEQ ", line)     && (data["inp_opb_nbeq"] = tryparse(Int, split(line)[end]))
        occursin("grim PBP NBEQ ", line)     && (data["inp_pbp_nbeq"] = tryparse(Int, split(line)[end]))
        occursin("grim NBEQ ", line)         && (data["inp_total_nbeq"] = tryparse(Int, split(line)[end]))
        # Use exact matching with regex to avoid substring conflicts
        match(r"^grim CONE LIT (\d+)", line) !== nothing   && (data["grim_cone_literals"] = tryparse(Int, match(r"^grim CONE LIT (\d+)", line).captures[1]))
        match(r"^grim CONE VAR (\d+)", line) !== nothing   && (data["grim_cone_variables"] = tryparse(Int, match(r"^grim CONE VAR (\d+)", line).captures[1]))
        match(r"^grim OPB CONE (\d+)", line) !== nothing   && (data["grim_opb_cone"] = tryparse(Int, match(r"^grim OPB CONE (\d+)", line).captures[1]))
        match(r"^grim PBP CONE (\d+)", line) !== nothing   && (data["grim_pbp_cone"] = tryparse(Int, match(r"^grim PBP CONE (\d+)", line).captures[1]))
        match(r"^grim CONE (\d+)$", line) !== nothing      && (data["grim_total_cone"] = tryparse(Int, match(r"^grim CONE (\d+)$", line).captures[1]))
        match(r"^grim SMOL LIT (\d+)", line) !== nothing   && (data["grim_smol_literals"] = tryparse(Int, match(r"^grim SMOL LIT (\d+)", line).captures[1]))
        occursin("grim OPB SIZE ", line)     && (data["grim_opb_size"] = tryparse(Int, split(line)[end]))
        occursin("grim PBP SIZE ", line)     && (data["grim_pbp_size"] = tryparse(Int, split(line)[end]))
        occursin("grim SIZE ", line)         && (data["grim_total_size"] = tryparse(Int, split(line)[end]))

        # Gclt stats
        occursin("gclt TRIM TIME ", line)    && (data["gclt_trim_time"] = tryparse(Float64, split(line)[end]))
        match(r"^gclt CONE LIT (\d+)", line) !== nothing   && (data["gclt_cone_literals"] = tryparse(Int, match(r"^gclt CONE LIT (\d+)", line).captures[1]))
        match(r"^gclt CONE VAR (\d+)", line) !== nothing   && (data["gclt_cone_variables"] = tryparse(Int, match(r"^gclt CONE VAR (\d+)", line).captures[1]))
        match(r"^gclt OPB CONE (\d+)", line) !== nothing   && (data["gclt_opb_cone"] = tryparse(Int, match(r"^gclt OPB CONE (\d+)", line).captures[1]))
        match(r"^gclt PBP CONE (\d+)", line) !== nothing   && (data["gclt_pbp_cone"] = tryparse(Int, match(r"^gclt PBP CONE (\d+)", line).captures[1]))
        match(r"^gclt CONE (\d+)$", line) !== nothing      && (data["gclt_total_cone"] = tryparse(Int, match(r"^gclt CONE (\d+)$", line).captures[1]))
        match(r"^gclt SMOL LIT (\d+)", line) !== nothing   && (data["gclt_smol_literals"] = tryparse(Int, match(r"^gclt SMOL LIT (\d+)", line).captures[1]))

        # Gbfs stats
        occursin("gbfs TRIM TIME ", line)    && (data["gbfs_trim_time"] = tryparse(Float64, split(line)[end]))
        match(r"^gbfs CONE LIT (\d+)", line) !== nothing   && (data["gbfs_cone_literals"] = tryparse(Int, match(r"^gbfs CONE LIT (\d+)", line).captures[1]))
        match(r"^gbfs CONE VAR (\d+)", line) !== nothing   && (data["gbfs_cone_variables"] = tryparse(Int, match(r"^gbfs CONE VAR (\d+)", line).captures[1]))
        match(r"^gbfs OPB CONE (\d+)", line) !== nothing   && (data["gbfs_opb_cone"] = tryparse(Int, match(r"^gbfs OPB CONE (\d+)", line).captures[1]))
        match(r"^gbfs PBP CONE (\d+)", line) !== nothing   && (data["gbfs_pbp_cone"] = tryparse(Int, match(r"^gbfs PBP CONE (\d+)", line).captures[1]))
        match(r"^gbfs CONE (\d+)$", line) !== nothing      && (data["gbfs_total_cone"] = tryparse(Int, match(r"^gbfs CONE (\d+)$", line).captures[1]))
        match(r"^gbfs SMOL LIT (\d+)", line) !== nothing   && (data["gbfs_smol_literals"] = tryparse(Int, match(r"^gbfs SMOL LIT (\d+)", line).captures[1]))

        # Verification
        occursin("veri smol TIME ", line)    && (data["veri_smol_time"] = tryparse(Float64, split(line)[end]))
        occursin("veri TIME ", line)         && (data["veri_total_time"] = tryparse(Float64, split(line)[end]))
        occursin("veri OPB SIZE ", line)     && (data["veri_opb_size"] = tryparse(Int, split(line)[end]))
        occursin("veri PBP SIZE ", line)     && (data["veri_pbp_size"] = tryparse(Int, split(line)[end]))
        occursin("veri SIZE ", line)         && (data["veri_total_size"] = tryparse(Int, split(line)[end]))

        # Brim
        occursin("brim TIME ", line)         && (data["brim_time"] = tryparse(Float64, split(line)[end]))
        occursin("brim OPB SIZE ", line)     && (data["brim_opb_size"] = tryparse(Int, split(line)[end]))
        occursin("brim PBP SIZE ", line)     && (data["brim_pbp_size"] = tryparse(Int, split(line)[end]))
        occursin("brim SIZE ", line)         && (data["brim_total_size"] = tryparse(Int, split(line)[end]))

        # Solver stats
        occursin("pattern_vertices", line)   && (data["pattern_vertices"] = tryparse(Int, match(r"=\s*(\d+)", line).captures[1]))
        occursin("target_vertices", line)    && (data["target_vertices"] = tryparse(Int, match(r"=\s*(\d+)", line).captures[1]))
        occursin("runtime", line)            && (data["runtime_ms"] = tryparse(Int, match(r"=\s*(\d+)", line).captures[1]))
        occursin("status", line)             && (data["status"] = match(r"=\s*(\w+)", line).captures[1])
    end

    return data
end

function parse_err_file(filepath)
    isfile(filepath) || return (false, "", "")

    content = read(filepath, String)
    isempty(strip(content)) && return (false, "", "")

    # Check for OOM
    m = match(r"OOM at ([\d.]+G)", content)
    if m !== nothing
        return (true, "OOM", m.captures[1])
    end

    # Check for timeout
    if occursin("Timeout", content)
        m = match(r"Timeout after (\d+s)", content)
        details = m !== nothing ? m.captures[1] : "unknown"
        return (true, "Timeout", details)
    end

    # Check for trunc error
    if occursin("trunc(Int32", content)
        m = match(r"trunc\(Int32, (\d+)\)", content)
        details = m !== nothing ? "value=$(m.captures[1])" : "unknown"
        return (true, "Int32Overflow", details)
    end

    # Check for bounds error
    if occursin("BoundsError", content)
        return (true, "BoundsError", "")
    end

    # Generic error
    return (true, "Unknown", strip(content)[1:min(100, end)])
end

function count_resolv_iterations(proofdir, instance)
    n = 0
    while isfile(joinpath(proofdir, instance * ".core$(n+1)" * ".out"))
        n += 1
    end
    return n
end

function aggregate_results(proofdir::String, output_csv::String)
    println("Scanning directory: $proofdir")

    # Find all .out files (excluding verification files)
    all_files = readdir(proofdir)
    out_files = filter(f -> endswith(f, ".out") &&
                           !endswith(f, ".smolverif.out") &&
                           !endswith(f, ".verif.out"), all_files)

    instances = [splitext(f)[1] for f in out_files]

    println("Found $(length(instances)) instances")

    # Open CSV file
    open(output_csv, "w") do io
        # Write header
        println(io, join(CSV_COLUMNS, ","))

        # Process each instance
        for (i, instance) in enumerate(instances)
            if i % 100 == 0
                println("Processing $i/$(length(instances))...")
            end

            # Parse .out file
            out_file = joinpath(proofdir, instance * ".out")
            data = parse_out_file(out_file)

            # Parse .err file
            err_file = joinpath(proofdir, instance * ".err")
            has_error, error_type, error_details = parse_err_file(err_file)

            # Count resolv iterations
            resolv_iters = count_resolv_iterations(proofdir, instance)

            # Build row
            row = []
            push!(row, "\"$instance\"")  # instance name

            # Input stats
            push!(row, get(data, "inp_opb_size", ""))
            push!(row, get(data, "inp_pbp_size", ""))
            push!(row, get(data, "inp_total_size", ""))
            push!(row, get(data, "inp_literals", ""))
            push!(row, get(data, "inp_variables", ""))
            push!(row, get(data, "inp_opb_nbeq", ""))
            push!(row, get(data, "inp_pbp_nbeq", ""))
            push!(row, get(data, "inp_total_nbeq", ""))

            # Grim stats
            push!(row, get(data, "grim_parse_time", ""))
            push!(row, get(data, "grim_trim_time", ""))
            push!(row, get(data, "grim_write_time", ""))
            push!(row, get(data, "grim_total_time", ""))
            push!(row, get(data, "grim_opb_cone", ""))
            push!(row, get(data, "grim_pbp_cone", ""))
            push!(row, get(data, "grim_total_cone", ""))
            push!(row, get(data, "grim_cone_literals", ""))
            push!(row, get(data, "grim_smol_literals", ""))
            push!(row, get(data, "grim_cone_variables", ""))
            push!(row, get(data, "grim_opb_size", ""))
            push!(row, get(data, "grim_pbp_size", ""))
            push!(row, get(data, "grim_total_size", ""))

            # Gclt stats
            push!(row, get(data, "gclt_trim_time", ""))
            push!(row, get(data, "gclt_opb_cone", ""))
            push!(row, get(data, "gclt_pbp_cone", ""))
            push!(row, get(data, "gclt_total_cone", ""))
            push!(row, get(data, "gclt_cone_literals", ""))
            push!(row, get(data, "gclt_smol_literals", ""))
            push!(row, get(data, "gclt_cone_variables", ""))

            # Gbfs stats
            push!(row, get(data, "gbfs_trim_time", ""))
            push!(row, get(data, "gbfs_opb_cone", ""))
            push!(row, get(data, "gbfs_pbp_cone", ""))
            push!(row, get(data, "gbfs_total_cone", ""))
            push!(row, get(data, "gbfs_cone_literals", ""))
            push!(row, get(data, "gbfs_smol_literals", ""))
            push!(row, get(data, "gbfs_cone_variables", ""))

            # Verification
            push!(row, get(data, "veri_smol_time", ""))
            push!(row, get(data, "veri_total_time", ""))
            push!(row, get(data, "veri_opb_size", ""))
            push!(row, get(data, "veri_pbp_size", ""))
            push!(row, get(data, "veri_total_size", ""))

            # Brim
            push!(row, get(data, "brim_time", ""))
            push!(row, get(data, "brim_opb_size", ""))
            push!(row, get(data, "brim_pbp_size", ""))
            push!(row, get(data, "brim_total_size", ""))

            # Solver stats
            push!(row, get(data, "pattern_vertices", ""))
            push!(row, get(data, "target_vertices", ""))
            push!(row, get(data, "runtime_ms", ""))
            status_val = get(data, "status", "")
            push!(row, status_val == "" ? "" : "\"$status_val\"")

            # Instance classification
            # is_sat: solver found SAT
            # is_unsat: solver found UNSAT
            # has_proof: proof file exists (has trimming stats)
            is_sat = (status_val == "SAT")
            is_unsat = (status_val == "UNSAT")
            has_proof = haskey(data, "grim_total_time")  # if trimmer ran, we have proof
            push!(row, is_sat ? "true" : "false")
            push!(row, is_unsat ? "true" : "false")
            push!(row, has_proof ? "true" : "false")

            # Error tracking
            push!(row, has_error ? "true" : "false")
            push!(row, has_error ? "\"$error_type\"" : "")
            push!(row, has_error && !isempty(error_details) ? "\"$error_details\"" : "")

            # Resolv iterations
            push!(row, resolv_iters)

            # Write row
            println(io, join(row, ","))
        end
    end

    println("Done! Results written to: $output_csv")
end

# Main
if length(ARGS) < 1
    println("Usage: julia aggregate_results.jl <proofs_directory> [output_csv]")
    println()
    println("Example: julia aggregate_results.jl /home/arthur_gla/veriPB/subgraphsolver/proofs/ results.csv")
    exit(1)
end

proofdir = ARGS[1]
output_csv = length(ARGS) >= 2 ? ARGS[2] : "results.csv"

aggregate_results(proofdir, output_csv)
