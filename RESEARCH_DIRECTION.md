# Research Direction: UNSAT Cores for Subgraph Isomorphism

## Core Research Question
**How do UNSAT cores for graph constraint problems (specifically Subgraph Isomorphism) differ from traditional SAT/SMT cores?**

## Novel Contributions

### 1. First Systematic Study of SIP UNSAT Cores
- UNSAT core extraction is well-studied for SAT/SMT
- Constraint programming (especially graph constraints) remains underexplored
- **Gap**: No prior systematic study of UNSAT cores for subgraph isomorphism problems

### 2. Novel Extraction Method
- Uses Glasgow CP solver's constraint propagation statistics
- Leverages `solver_nodes` and `solver_propagations` for core analysis
- Iterative refinement via repeated core extraction (resolv iterations)
- **Different from SAT**: Graph constraints have richer structure than Boolean clauses

### 3. Large-Scale Empirical Evaluation
- 14,127+ instances with systematic analysis
- Metrics: constraint reduction, variable reduction, literal reduction, proof sizes
- Correlation analysis between search effort and core quality

## Key Hypotheses to Test

### H1: Search Effort vs Core Quality
**Hypothesis**: Instances with more solver search require more/different core iterations

**Why interesting**:
- In SAT: search effort often correlates with proof complexity
- In SIP: Graph structure may matter more than search behavior
- **Even negative result is valuable**: Shows graph constraints ≠ SAT

### H2: Propagation Statistics Predict Core Quality
**Hypothesis**: Propagation count/pattern predicts how well cores can be minimized

**Metrics to analyze**:
- solver_nodes vs resolv_iterations
- solver_propagations vs constraint_reduction_ratio
- Pattern graph vertices reduction vs search effort

### H3: Iterative Refinement Benefits
**Hypothesis**: Multiple resolv iterations improve core quality

**To measure**:
- Per-iteration size changes (already tracking)
- Diminishing returns after N iterations
- Cases where iterations increase size (outliers)

## Expected Findings (Regardless of Correlation)

### If Strong Correlation Exists:
- "Solver search statistics predict core minimization potential"
- Could guide heuristics for which instances to invest more trimming effort
- Theory: explain why search correlates with core structure

### If Weak/No Correlation Exists:
- "Graph constraint cores fundamentally different from SAT cores"
- Problem topology/structure matters more than solver behavior
- Requires domain-specific heuristics (not transferable from SAT)
- **This is also a contribution!**

## Publication Strategy

### Potential Venues (Priority Order)

1. **CP Conference** (Best fit)
   - Main track: Principles and Practice of Constraint Programming
   - Novel CP technique for graph constraints
   - Community appreciates nogood/core distinction

2. **SAT Conference**
   - Theory and Applications of Satisfiability Testing
   - UNSAT core community, proof trimming angle
   - May need stronger "why SAT community cares" angle

3. **Workshop Path** (Recommended first step)
   - ModRef (Modeling and Reformulation at CP)
   - POS (Pragmatics of SAT)
   - CP Doctoral Program
   - Lower barrier, faster feedback, build to full paper

4. **Graph Algorithms**
   - SEA (Symposium on Experimental Algorithms)
   - ALENEX
   - SIP as graph problem, algorithmic contribution

5. **Verification** (Higher bar)
   - TACAS, CAV, FMCAD
   - Need strong proof certification story

### Suggested Title Ideas
- "Extracting UNSAT Cores for Subgraph Isomorphism: A Propagation-Based Approach"
- "Understanding UNSAT Core Quality in Graph Constraint Problems"
- "From Search to Cores: Analyzing Constraint Propagation in Subgraph Isomorphism"

## Literature to Cover

### UNSAT Core Extraction (Foundation)
- **SAT cores**: Zhang & Malik, Belov et al. (MiniSat/MUS extraction)
- **Resolution-based cores**: For comparison with propagation-based approach
- **Deletion-based minimization**: If applicable to your method
- **Contrast**: "Graph constraints require different strategies than clause-based cores"

### Subgraph Isomorphism Solvers
- **Glasgow Subgraph Solver** (McCreesh et al.) - base solver
  - CP approach, nogood learning, propagation
- **VF2, VF3** (Cordella et al.) - classical algorithms
- **LAD** (Solnon) - if using LAD format
- **Key point**: "Glasgow's propagation enables constraint analysis unlike pure backtracking"

### Constraint Programming & UNSAT Cores
- **CP nogood learning** (Ohrimenko et al., Gange et al.)
  - Propagation failures → cores
- **Explanation-based learning in CP**
- **Gap identification**: "UNSAT cores for graph constraints understudied vs SAT/SMT"

### Proof Trimming/Minimization
- **SAT proof trimming** (Wetzler et al. - DRAT proofs)
- **VeriPB** (Gocht et al.) - PB proof checking
- **Contrast**: "Graph isomorphism proofs have unique structure needing domain-specific trimming"

### Graph Constraints in CP
- **Global constraints** (Régin's alldifferent with graph reasoning)
- **Symmetry breaking** in graph problems
- **Relevance**: Show graph constraints are special case

## Story Arc for Paper

### Introduction Hook
> "UNSAT cores are fundamental to SAT/SMT solving, enabling conflict analysis, MUS extraction,
> and proof certification. However, constraint programming—particularly for graph constraints—
> remains largely unexplored territory for core extraction.
>
> We present the first systematic study of UNSAT core extraction for Subgraph Isomorphism Problems (SIP),
> a fundamental NP-complete graph problem. Unlike clause-based cores, graph constraint cores must
> account for complex propagation interactions..."

### Key Narrative Points
1. **Problem**: SIP is important but UNSAT cores unstudied
2. **Challenge**: Graph constraints ≠ Boolean clauses (structural difference)
3. **Approach**: Novel propagation-based extraction + iterative refinement
4. **Evaluation**: 14k+ instances, systematic analysis
5. **Finding**: [Correlation result] suggests graph constraints behave [differently/similarly] to SAT
6. **Impact**: Enables better proof certification, informs future CP core extraction

## What's Still Missing (TODO for Publication)

### Experimental Gaps
- [ ] **Baseline comparison**: What happens without trimming? Random constraint deletion?
- [ ] **Clear algorithm description**: Formalize the extraction procedure
- [ ] **Case studies**: 2-3 instances explaining *why* cores differ (manual analysis)
- [ ] **Theoretical insight**: Why do patterns emerge (or not)?
- [ ] **Practical impact**: Does smaller core → faster verification? Better learning?

### Technical Depth Needed
- [ ] Formalize graph constraint representation
- [ ] Define "core" for SIP precisely (minimal infeasible constraint set?)
- [ ] Explain resolv iteration algorithm clearly
- [ ] Justify why propagation statistics are the right metric

### Writing Components
- [ ] Related work section (see literature above)
- [ ] Clear contribution bullets
- [ ] Reproducibility: benchmark suite, code availability
- [ ] Limitations section (be honest about what you don't know)

## Potential Extensions (Future Work)

1. **Core-guided nogood learning**: Use cores to improve solver performance
2. **Cross-domain transfer**: Do insights apply to other graph problems (clique, coloring)?
3. **Heuristic development**: Predict trimming difficulty from instance features
4. **Theoretical characterization**: When do graph cores correlate with search?
5. **Interactive exploration**: Tool for researchers to analyze their own instances

## Key Insight to Remember

**Even if there's NO clear correlation between search and cores, that's publishable!**

Why? Because it shows:
- Graph constraints are fundamentally different from SAT
- Intuitions from SAT don't transfer directly
- Need domain-specific approaches for CP core extraction
- Opens research direction: "What DOES predict core quality for graph constraints?"

Negative results are valuable when they challenge assumptions and redirect research.

## Experimental Results to Highlight

Once experiments complete, focus on:
1. **Reduction statistics**: X% median constraint reduction, Y% variable reduction
2. **Correlation coefficients**: Pearson/Spearman values + p-values + interpretation
3. **Outliers**: Interesting cases (143x proof growth, extreme reductions)
4. **Per-iteration analysis**: How many iterations needed? Diminishing returns?
5. **Instance clusters**: Do certain problem types behave differently?

## Timeline (Flexible)

- **Now**: Experiments running, collect data
- **After results**: Decide workshop vs conference based on strength
- **Workshop option**: Submit to ModRef or POS (faster turnaround)
  - Get community feedback
  - Refine for full conference paper
- **Conference option**: Target CP 2026 or SAT 2026
  - Need stronger theoretical contribution
  - More comprehensive evaluation

## Questions to Answer Before Submission

1. What's the "so what?" - Why should CP/SAT community care?
2. What's the algorithmic contribution beyond "we ran experiments"?
3. Can we predict anything useful from the correlations (or lack thereof)?
4. Does this enable better solvers? Better verification? Better understanding?
5. What's the one key insight someone should remember from this paper?

---

**Remember**: You have novel heuristics for SIP and novel UNSAT core extraction. That's already interesting. The correlation analysis will either:
- Confirm intuitions → predictive model
- Reject intuitions → fundamental insight about graph constraints

Both paths lead to publishable results!
