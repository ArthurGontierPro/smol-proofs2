# Smol-Proofs2 Project Summary

**Last Updated**: 2026-06-01

## Project Overview

Analysis pipeline for proof trimming experiments on Subgraph Isomorphism Problems (SIP). Processes cluster results to understand UNSAT core extraction quality and solver behavior.

## Main Components

### 1. Core Trimming Tool
- **File**: `trimnalyser.jl`
- **Purpose**: Trims PB proofs using cone extraction and conflict analysis
- **Features**:
  - DFS (Grim), ConeLits (Gclt), BFS (Gbfs) trimming modes
  - Recursive core extraction (resolv iterations)
  - Integrates with Glasgow Subgraph Solver
  - Parallel processing with OOM/timeout protection
  - Per-iteration tracking of proof sizes and constraints

### 2. Results Aggregation
- **File**: `aggregate_results.jl`
- **Purpose**: Parses cluster .out/.err files into structured CSV
- **Input**: Directory of proof files with .out/.err
- **Output**: `cluster_results.csv` with 60+ columns
- **Key Metrics**:
  - Input/output sizes (bytes, constraints, variables, literals)
  - Timing breakdowns (parse, trim, write, verification)
  - Solver statistics (nodes explored, propagations)
  - Error tracking (OOM, timeout, truncation)
  - Resolv iterations with per-iteration metrics
  - UNSAT core graph statistics

### 3. Interactive Analysis
- **File**: `analyze_results.py`
- **Purpose**: Generate interactive HTML reports from CSV
- **Features**:
  - 9 reduction scatter plots (sizes, constraints, variables, literals, cores)
  - Separate analysis for instances with solver search
  - Correlation analysis (search effort vs iterations/reduction)
  - Per-iteration outlier detection
  - Top 10 lists (slowest, best/worst reductions)
  - Self-contained HTML (no server needed)

## Recent Updates (2026-05-29 to 2026-06-01)

### Per-Iteration Tracking
- Added `iter_nbeq`, `iter_var`, `iter_lit` columns (JSON arrays)
- Tracks constraint/variable/literal evolution across resolv iterations
- Enables detection of unusual growth patterns

### Correlation Analysis
- **Research Question**: Do instances with more solver search require more core iterations?
- Pearson and Spearman correlation coefficients
- Visual scatter plots:
  - solver_nodes vs resolv_iterations
  - solver_propagations vs resolv_iterations
  - solver_nodes/propagations vs pattern graph reduction
- Tests hypothesis about relationship between search and core quality

### Solver Search Statistics
- Added `solver_nodes` and `solver_propagations` columns
- Parsed from Glasgow solver output (nodes/propagations counts)
- Enables analysis of search effort impact on proof quality

### Timeout Signal Handling
- **Problem**: SIGTERM signal from timeout interrupted @inbounds code, causing spurious crashes
- **Solution**: Custom SIGTERM handler exits cleanly with code 124
- **Result**: No more checkbounds errors from hard instances timing out

## Key Files

### Scripts
- `trimnalyser.jl` - Main proof trimming tool (3282 lines)
- `aggregate_results.jl` - CSV generation (440 lines)
- `analyze_results.py` - HTML report generation (1280 lines)
- `quick_stats.py` - Fast CSV statistics viewer

### Documentation
- `README_aggregate.md` - CSV column reference
- `ANALYSIS_README.md` - Analysis workflow guide
- `RESEARCH_DIRECTION.md` - Publication strategy and research goals
- `PROJECT_SUMMARY.md` - This file

### Data Files
- `cluster_results.csv` - Main results (14,127 instances)
- `cluster_analysis.html` - Interactive analysis report
- `stats_summary.txt` - Quick statistics snapshot

## Workflow

### On Cluster
```bash
# Run trimming with solver + resolv on all graphs
julia --threads 192,1 trimnalyser.jl solve resolv verif allgraphs maxnodes=3000 st=180 tt=6000 rand
```

### Local Analysis
```bash
# 1. Aggregate cluster results
julia aggregate_results.jl /scratch/arthur/proofs/ cluster_results.csv

# 2. Generate HTML report
python3 analyze_results.py cluster_results.csv cluster_analysis.html

# 3. View statistics
python3 quick_stats.py cluster_results.csv
```

## Research Direction

### Primary Goal
First systematic study of UNSAT core extraction for Subgraph Isomorphism problems.

### Novel Contributions
1. **New extraction method**: Uses CP solver propagation statistics for core analysis
2. **Large-scale evaluation**: 14k+ instances with systematic metrics
3. **Correlation analysis**: Relationship between search effort and core quality
4. **Iterative refinement**: Multiple resolv passes improve cores

### Key Questions
- Do instances with more solver search need more/fewer core iterations?
- Can we predict core quality from solver statistics?
- How do graph constraint cores differ from SAT clause cores?

### Publication Target
- **Primary**: CP Conference (Constraint Programming)
- **Alternative**: SAT Conference, SEA (Experimental Algorithms)
- **Workshop**: ModRef (CP), POS (SAT) for preliminary results

See `RESEARCH_DIRECTION.md` for detailed publication strategy.

## Statistics (Current Run)

From cluster_results.csv:
- **Total instances**: 14,127
- **Successfully trimmed**: 10,368 (73.4%)
- **With solver search**: 2,371 (16.8%)
- **With resolv iterations**: 5,206 (36.9%)
- **Max resolv iterations**: Varies per run

## Dependencies

### Julia Packages
- DataStructures
- Random
- Printf
- Dates
- Mmap
- StatProfilerHTML (optional, for profiling)

### Python Packages
- pandas
- numpy
- plotly
- scipy (optional, for correlation analysis)

### External Tools
- VeriPB (proof verification)
- Glasgow Subgraph Solver (SIP solving)

## Common Tasks

### Check if scipy is installed
```bash
python3 -c "import scipy; print('scipy OK')"
```

### Quick CSV overview
```bash
python3 quick_stats.py cluster_results.csv
```

### Find instances with most resolv iterations
```bash
julia -e 'using CSV, DataFrames; df = CSV.read("cluster_results.csv", DataFrame); sort(df, :resolv_iterations, rev=true)[1:10, [:instance, :resolv_iterations]]'
```

### Filter to search instances
```bash
# In Python
import pandas as pd
df = pd.read_csv('cluster_results.csv')
search = df[df['solver_nodes'] > 0]
print(f"Search instances: {len(search)}")
```

## Git Integration

Tag important runs:
```bash
git add cluster_results.csv cluster_analysis.html
git commit -m "results: supplemental graphs experiment 2026-06-01

- 14,127 instances
- 10,368 with proofs (73.4%)
- Added per-iteration constraint/variable tracking
- Added correlation analysis

See cluster_analysis.html for interactive report"
git tag cluster-supp-2026-06-01
```

## Known Issues / Notes

1. **Timeout handling**: SIGTERM handler added to prevent spurious crashes
2. **Memory**: Cluster jobs limited to 50GB per instance
3. **Scipy optional**: Correlation analysis gracefully skipped if scipy not installed
4. **Boolean format**: CSV uses lowercase "true"/"false" strings
5. **JSON arrays**: Per-iteration data stored as "[val1,val2,...]" strings in CSV

## Future Work

### Analysis Enhancements
- [ ] Instance clustering by behavior patterns
- [ ] Prediction model: solver stats → trimming difficulty
- [ ] Cross-benchmark comparison
- [ ] Visualization of per-iteration trajectories

### Tool Improvements
- [ ] Incremental CSV updates (append mode)
- [ ] Real-time monitoring dashboard
- [ ] Automated outlier investigation
- [ ] LaTeX table generation for papers

### Research Questions
- [ ] Does supplemental graph usage correlate with search/cores?
- [ ] Can we identify "hard to trim" instance classes?
- [ ] What's the theoretical relationship between propagation and cores?

## Contact

Arthur Gontier - arthur.pro.gontier@gmail.com

For questions about:
- Trimming algorithm: See `flat_pol_design.md`
- CSV format: See `README_aggregate.md`
- Analysis workflow: See `ANALYSIS_README.md`
- Publication strategy: See `RESEARCH_DIRECTION.md`
