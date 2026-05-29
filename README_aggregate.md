# Results Aggregation Script

## Usage

```bash
julia aggregate_results.jl <proofs_directory> [output_csv]
```

## Example

```bash
# Aggregate results from cluster run
julia aggregate_results.jl /scratch/arthur/proofs/ cluster_results.csv

# Or use local proofs directory
julia aggregate_results.jl /home/arthur_gla/veriPB/subgraphsolver/proofs/ results.csv
```

## Output Columns

The script generates a CSV file with the following columns:

### Instance Info
- `instance` - Instance name

### Input Statistics
- `inp_opb_size` - Input OPB file size (bytes)
- `inp_pbp_size` - Input PBP file size (bytes)
- `inp_total_size` - Total input size (bytes)
- `inp_literals` - Total literals in input
- `inp_variables` - Total variables in input
- `inp_opb_nbeq` - Number of OPB constraints
- `inp_pbp_nbeq` - Number of PBP proof steps
- `inp_total_nbeq` - Total constraints (OPB + PBP)

### Grim (DFS Trimming) Results
- `grim_parse_time` - Parse time (seconds)
- `grim_trim_time` - Trim/cone extraction time (seconds)
- `grim_write_time` - Write time (seconds)
- `grim_total_time` - Total grim time (seconds)
- `grim_opb_cone` - OPB constraints in cone
- `grim_pbp_cone` - PBP steps in cone
- `grim_total_cone` - Total cone size
- `grim_cone_literals` - Literals in cone (before weakening)
- `grim_smol_literals` - Literals after weakening
- `grim_cone_variables` - Variables in cone
- `grim_opb_size` - Output OPB size (bytes)
- `grim_pbp_size` - Output PBP size (bytes)
- `grim_total_size` - Total output size (bytes)

### Gclt (ConeLits Trimming) Results
- `gclt_trim_time` - Trim time (seconds)
- `gclt_opb_cone` - OPB constraints in cone
- `gclt_pbp_cone` - PBP steps in cone
- `gclt_total_cone` - Total cone size
- `gclt_cone_literals` - Literals in cone
- `gclt_smol_literals` - Literals after weakening
- `gclt_cone_variables` - Variables in cone

### Gbfs (BFS Trimming) Results
- `gbfs_trim_time` - Trim time (seconds)
- `gbfs_opb_cone` - OPB constraints in cone
- `gbfs_pbp_cone` - PBP steps in cone
- `gbfs_total_cone` - Total cone size
- `gbfs_cone_literals` - Literals in cone
- `gbfs_smol_literals` - Literals after weakening
- `gbfs_cone_variables` - Variables in cone

### Verification Results
- `veri_smol_time` - Smol verification time (seconds)
- `veri_total_time` - Total verification time (seconds)
- `veri_opb_size` - Verification OPB size (bytes) - from .opb.smol file
- `veri_pbp_size` - Verification PBP size (bytes) - from .pbp.smol file
- `veri_total_size` - Total verification size (bytes)

### Solver Statistics (if available)
- `pattern_vertices` - Pattern graph vertices
- `target_vertices` - Target graph vertices
- `runtime_ms` - Solver runtime (milliseconds)
- `status` - Solver status (SAT/UNSAT/TIMEOUT/etc.)

### UNSAT Core Statistics
- `core_pattern_nodes` - Number of pattern nodes in UNSAT core (from vis/*.core.pat.lad)
- `core_target_nodes` - Number of target nodes in UNSAT core (from vis/*.core.tar.lad)
- `core_pattern_total` - Total pattern nodes (from vis/*.pat.lad)
- `core_target_total` - Total target nodes (from vis/*.tar.lad)

### Instance Classification
- `is_sat` - Boolean: true if solver found SAT (no proof to trim)
- `is_unsat` - Boolean: true if solver found UNSAT (proof should exist)
- `has_proof` - Boolean: true if proof exists and was trimmed (has grim_total_time)
- `skip_reason` - Reason instance was skipped: SAT, truncated_no_conclusion, truncated_no_output, truncated, no_proof_generated
- `proof_truncated` - Boolean: true if proof file was incomplete/truncated
- `truncation_reason` - Specific truncation reason if proof_truncated is true

### Error Tracking
- `has_error` - Boolean: true if instance had an error
- `error_type` - Type of error (OOM, Timeout, Int32Overflow, BoundsError, Unknown)
- `error_details` - Error details (memory usage for OOM, timeout duration, etc.)

### Other
- `resolv_iterations` - Number of resolv iterations (0 if none)

## Data Sources

The script reads:
- `.out` files - Main output statistics
- `.err` files - Error messages, diagnostics, and skip reasons
- `.coreN.out` files - Resolv iteration detection
- `.opb.smol` / `.pbp.smol` files - Verification file sizes
- `vis/*.core.pat.lad` / `vis/*.core.tar.lad` - UNSAT core sizes
- `vis/*.pat.lad` / `vis/*.tar.lad` - Original graph sizes

## Notes

- Empty cells indicate missing data
- Times are in seconds (floating point)
- Sizes are in bytes
- All cone statistics refer to the reduced/trimmed proof
