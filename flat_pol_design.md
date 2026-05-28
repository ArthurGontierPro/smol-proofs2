# Flat POL API Design - Zero-Copy Equation Arithmetic

## Goal
Eliminate all `Eq` and `Lit` struct allocations in POL processing by operating directly on flat CSR arrays. For 40k-literal POL steps, this eliminates millions of allocations.

## Core Data Structure: PolScratch

```julia
mutable struct PolScratch
    # Working buffers for equation arithmetic (reused across POL steps)
    vars  ::Vector{Int32}
    coefs ::Vector{Int32}
    signs ::BitVector
    rhs   ::Int64

    # Stack for POL expression evaluation (stores equation IDs + scratch indices)
    # Each stack entry is either:
    #   - Positive: equation ID in store
    #   - Negative: scratch buffer index (for intermediate results)
    stack ::Vector{Int32}
    stack_depth ::Int

    # Pool of scratch buffers for intermediate results during complex POL expressions
    # (e.g., "1 + 2 + 3 * 4" needs temp storage for "1+2" while computing "3*4")
    scratch_pool ::Vector{Tuple{Vector{Int32}, Vector{Int32}, BitVector, Int64}}
    next_scratch ::Int
end

PolScratch() = PolScratch(
    Int32[], Int32[], BitVector(), 0,
    Int32[], 0,
    [], 1
)

# Get thread-local PolScratch (one per worker)
get_pol_scratch() = get!(task_local_storage(), :pol_scratch, PolScratch())
```

## Helper: eqrange for FlatEqStore

```julia
eqrange(s::FlatEqStore, e::Int) = Int(s.row_ptr[e]):Int(s.row_ptr[e+1])-1
```

## Flat Operations

### 1. Push equation from store onto stack
```julia
function pol_push_eq!(ps::PolScratch, store::FlatEqStore, id::Int)
    push!(ps.stack, Int32(id))
    ps.stack_depth += 1
end
```

### 2. Push literal axiom onto stack
```julia
function pol_push_literal!(ps::PolScratch, var::Int, sign::Bool)
    # Create single-literal equation in scratch
    resize!(ps.vars, 1); ps.vars[1] = Int32(var)
    resize!(ps.coefs, 1); ps.coefs[1] = Int32(1)
    resize!(ps.signs, 1); ps.signs[1] = sign
    ps.rhs = 0

    # Move to scratch pool and push index onto stack
    idx = _allocate_scratch!(ps)
    push!(ps.stack, Int32(-idx))  # negative = scratch index
    ps.stack_depth += 1
end
```

### 3. Addition (pop 2, push result)
```julia
function pol_add!(ps::PolScratch, store::FlatEqStore)
    ps.stack_depth >= 2 || error("pol stack underflow")

    id2 = pop!(ps.stack); ps.stack_depth -= 1
    id1 = pop!(ps.stack); ps.stack_depth -= 1

    # Get source ranges
    r1, rhs1 = _get_eq_range(ps, store, id1)
    r2, rhs2 = _get_eq_range(ps, store, id2)
    v1, c1, s1 = _get_arrays(ps, store, id1)
    v2, c2, s2 = _get_arrays(ps, store, id2)

    # Merge sorted arrays into ps.{vars,coefs,signs}
    resize!(ps.vars, 0); resize!(ps.coefs, 0); resize!(ps.signs, 0)
    sizehint!(ps.vars, length(r1) + length(r2))

    i, j = r1.start, r2.start
    rhs_adj = 0

    while i <= r1.stop && j <= r2.stop
        if v1[i] < v2[j]
            push!(ps.vars, v1[i])
            push!(ps.coefs, c1[i])
            push!(ps.signs, s1[i])
            i += 1
        elseif v1[i] > v2[j]
            push!(ps.vars, v2[j])
            push!(ps.coefs, c2[j])
            push!(ps.signs, s2[j])
            j += 1
        else  # same variable
            var = v1[i]
            # Add coefficients (accounting for signs)
            # Positive lit: coef contributes +coef to slack
            # Negative lit: coef contributes +coef to slack (when falsified)
            # If signs match: coefficients add
            # If signs differ: need to normalize first
            sign1, sign2 = s1[i], s2[j]
            coef1, coef2 = c1[i], c2[j]

            if sign1 == sign2
                c = coef1 + coef2
                if c != 0
                    push!(ps.vars, var)
                    push!(ps.coefs, c)
                    push!(ps.signs, sign1)
                end
            else
                # ~x + x with coef c1, c2 → need to normalize
                # x >= 0  becomes  ~x >= -1  (norm: x >= 1, rhs adjusted)
                # This case: different signs mean they partially cancel
                if coef1 > coef2
                    push!(ps.vars, var)
                    push!(ps.coefs, coef1 - coef2)
                    push!(ps.signs, sign1)
                    rhs_adj += coef2
                elseif coef2 > coef1
                    push!(ps.vars, var)
                    push!(ps.coefs, coef2 - coef1)
                    push!(ps.signs, sign2)
                    rhs_adj += coef1
                else
                    # Complete cancellation
                    rhs_adj += coef1
                end
            end
            i += 1; j += 1
        end
    end

    # Tail loops
    while i <= r1.stop
        push!(ps.vars, v1[i]); push!(ps.coefs, c1[i]); push!(ps.signs, s1[i]); i += 1
    end
    while j <= r2.stop
        push!(ps.vars, v2[j]); push!(ps.coefs, c2[j]); push!(ps.signs, s2[j]); j += 1
    end

    ps.rhs = rhs1 + rhs2 - rhs_adj

    # Free inputs if they were scratch
    _free_scratch!(ps, id1)
    _free_scratch!(ps, id2)

    # Push result onto stack
    idx = _allocate_scratch!(ps)
    push!(ps.stack, Int32(-idx))
    ps.stack_depth += 1
end
```

### 4. Multiplication (pop multiplier, mutate top)
```julia
function pol_multiply!(ps::PolScratch, store::FlatEqStore, multiplier::Int)
    ps.stack_depth >= 1 || error("pol stack underflow")

    id = ps.stack[end]

    # If referencing store, need to materialize into scratch
    if id > 0
        _materialize_to_scratch!(ps, store, id)
        ps.stack[end] = Int32(-ps.next_scratch + 1)
    end

    # Now mutate scratch in-place
    idx = -ps.stack[end]
    scratch = ps.scratch_pool[idx]

    for i in eachindex(scratch[2])  # coefs
        scratch[2][i] *= Int32(multiplier)
    end
    scratch[4] *= multiplier  # rhs
end
```

### 5. Division (ceil divide, mutate top)
```julia
function pol_divide!(ps::PolScratch, store::FlatEqStore, divisor::Int)
    ps.stack_depth >= 1 || error("pol stack underflow")

    id = ps.stack[end]
    if id > 0
        _materialize_to_scratch!(ps, store, id)
        ps.stack[end] = Int32(-ps.next_scratch + 1)
    end

    idx = -ps.stack[end]
    scratch = ps.scratch_pool[idx]
    vars, coefs, signs, rhs = scratch

    # First normalize (make all coefs positive)
    rhs_adj = 0
    for i in eachindex(coefs)
        if coefs[i] < 0
            coefs[i] = -coefs[i]
            signs[i] = !signs[i]
            rhs_adj += coefs[i]
        end
    end
    rhs = rhs + rhs_adj

    # Then divide
    for i in eachindex(coefs)
        coefs[i] = Int32(ceil(coefs[i] / divisor))
    end
    scratch[4] = ceil(Int, rhs / divisor)
end
```

### 6. Saturate (mutate top)
```julia
function pol_saturate!(ps::PolScratch, store::FlatEqStore)
    ps.stack_depth >= 1 || error("pol stack underflow")

    id = ps.stack[end]
    if id > 0
        _materialize_to_scratch!(ps, store, id)
        ps.stack[end] = Int32(-ps.next_scratch + 1)
    end

    idx = -ps.stack[end]
    scratch = ps.scratch_pool[idx]
    coefs = scratch[2]
    rhs = scratch[4]

    for i in eachindex(coefs)
        coefs[i] > rhs && (coefs[i] = Int32(rhs))
    end
end
```

### 7. Weaken (remove variable, mutate top)
```julia
function pol_weaken!(ps::PolScratch, store::FlatEqStore, var::Int)
    ps.stack_depth >= 1 || error("pol stack underflow")

    id = ps.stack[end]
    if id > 0
        _materialize_to_scratch!(ps, store, id)
        ps.stack[end] = Int32(-ps.next_scratch + 1)
    end

    idx = -ps.stack[end]
    scratch = ps.scratch_pool[idx]
    vars, coefs, signs, rhs = scratch

    # Find and remove var
    i = 1
    while i <= length(vars)
        if vars[i] == var
            rhs -= coefs[i]
            deleteat!(vars, i)
            deleteat!(coefs, i)
            deleteat!(signs, i)
            break
        else
            i += 1
        end
    end
    scratch[4] = rhs
end
```

### 8. Finalize: pop result and push to store
```julia
function pol_finalize_push!(ps::PolScratch, store::FlatEqStore,
                            normalize::Bool=true, saturate_final::Bool=false)
    ps.stack_depth >= 1 || error("pol stack underflow")

    id = pop!(ps.stack)
    ps.stack_depth -= 1

    # Get final result
    r, rhs = _get_eq_range(ps, store, id)
    v, c, s = _get_arrays(ps, store, id)

    # Remove null lits + optional normalize + optional saturate
    # Write directly into store.{vars,coefs,signs}
    start_idx = length(store.vars) + 1
    rhs_adj = 0

    if normalize
        # Pass 1: normalize (make positive) and compute rhs adjustment
        for i in r
            c[i] == 0 && continue  # skip null
            if c[i] < 0
                push!(store.vars, v[i])
                push!(store.coefs, -c[i])
                push!(store.signs, !s[i])
                rhs_adj += -c[i]
            else
                push!(store.vars, v[i])
                push!(store.coefs, c[i])
                push!(store.signs, s[i])
            end
        end
        rhs += rhs_adj

        # Pass 2: saturate if requested
        if saturate_final
            for i in start_idx:length(store.coefs)
                store.coefs[i] > rhs && (store.coefs[i] = Int32(rhs))
            end
        end
    else
        # Just copy non-null lits
        for i in r
            c[i] == 0 && continue
            push!(store.vars, v[i])
            push!(store.coefs, c[i])
            push!(store.signs, s[i])
        end
    end

    push!(store.rhs, Int64(rhs))
    push!(store.row_ptr, Int32(length(store.vars) + 1))

    # Free scratch if used
    _free_scratch!(ps, id)

    # Reset for next POL
    ps.next_scratch = 1
end
```

## Helper Functions

```julia
# Get equation range - returns (range, rhs)
function _get_eq_range(ps::PolScratch, store::FlatEqStore, id::Int)
    if id > 0
        # Reference to store
        return eqrange(store, id), store.rhs[id]
    else
        # Reference to scratch
        idx = -id
        scratch = ps.scratch_pool[idx]
        return 1:length(scratch[1]), scratch[4]
    end
end

# Get arrays - returns (vars, coefs, signs)
function _get_arrays(ps::PolScratch, store::FlatEqStore, id::Int)
    if id > 0
        return store.vars, store.coefs, store.signs
    else
        idx = -id
        scratch = ps.scratch_pool[idx]
        return scratch[1], scratch[2], scratch[3]
    end
end

# Allocate a scratch buffer and copy ps.{vars,coefs,signs,rhs} into it
function _allocate_scratch!(ps::PolScratch)
    idx = ps.next_scratch
    ps.next_scratch += 1

    # Grow pool if needed
    if idx > length(ps.scratch_pool)
        push!(ps.scratch_pool, (
            copy(ps.vars),
            copy(ps.coefs),
            copy(ps.signs),
            ps.rhs
        ))
    else
        # Reuse existing scratch
        s = ps.scratch_pool[idx]
        resize!(s[1], length(ps.vars)); copyto!(s[1], ps.vars)
        resize!(s[2], length(ps.coefs)); copyto!(s[2], ps.coefs)
        resize!(s[3], length(ps.signs)); copyto!(s[3], ps.signs)
        ps.scratch_pool[idx] = (s[1], s[2], s[3], ps.rhs)
    end

    return idx
end

# Free scratch buffer (mark as reusable)
function _free_scratch!(ps::PolScratch, id::Int)
    # If id is negative (scratch), we don't actually free it - just mark for reuse
    # The scratch pool persists across POL steps for reuse
end

# Materialize store equation into scratch
function _materialize_to_scratch!(ps::PolScratch, store::FlatEqStore, id::Int)
    r = eqrange(store, id)
    resize!(ps.vars, length(r))
    resize!(ps.coefs, length(r))
    resize!(ps.signs, length(r))

    for (i, k) in enumerate(r)
        ps.vars[i] = store.vars[k]
        ps.coefs[i] = store.coefs[k]
        ps.signs[i] = store.signs[k]
    end
    ps.rhs = store.rhs[id]
end
```

## Main POL Entry Point (replaces solvepol)

```julia
function solvepol_flat!(store::FlatEqStore, st, link::Vector{Int}, init::Int,
                        varmap, ctrmap, nbopb)
    ps = get_pol_scratch()

    # Reset scratch state
    ps.stack_depth = 0
    empty!(ps.stack)
    ps.next_scratch = 1

    # Parse initial equation ID
    i = st[2]
    id = i[1]==UInt8('@') ? ctrmap[String(view(i,2:length(i)))] : parse_int_bytes(i)
    if id < 0
        id = init + id
    end

    pol_push_eq!(ps, store, id)
    push!(link, id)

    weakvar = 0
    lastsaturate = false

    # Process POL operations
    for j in 3:length(st)
        i = st[j]
        tok_eq(i, ";") && continue

        if tok_eq(i, "+")
            pol_add!(ps, store)
            push!(link, -1)
        elseif tok_eq(i, "*")
            multiplier = link[end]
            pol_multiply!(ps, store, multiplier)
            push!(link, -2)
        elseif tok_eq(i, "d")
            divisor = link[end]
            pol_divide!(ps, store, divisor)
            push!(link, -3)
        elseif tok_eq(i, "s")
            if j == length(st)
                lastsaturate = true  # defer to finalize
            else
                pol_saturate!(ps, store)
            end
            push!(link, -4)
        elseif tok_eq(i, "w")
            pol_weaken!(ps, store, weakvar)
            push!(link, -5)
        elseif !isdigit(Char(i[1])) && i[1] != UInt8('@') && i[1] != UInt8('-')
            # Literal axiom
            if length(st) > j && tok_eq(st[j+1], "w")
                weakvar = readvar(i, varmap)
                push!(link, -100 * weakvar - 99)
            else
                sign = i[1] != UInt8('~')
                var = readvar(i, varmap)
                pol_push_literal!(ps, var, sign)
                push!(link, -100 * var - 99 - (sign ? 0 : 1))
            end
        elseif !tok_eq(i, "0")
            # Constraint ID
            id = i[1]==UInt8('@') ? ctrmap[String(view(i,2:length(i)))] : parse_int_bytes(i)
            if id < 1
                id = init + id
            end
            push!(link, id)
            if !tok_in(st[j+1], ["*", "d"])
                pol_push_eq!(ps, store, id)
            end
        end
    end

    # Special case: single antecedent with no ops = ia
    if length(link) == 2
        link[1] = -3
    end

    # Finalize and push to store
    pol_finalize_push!(ps, store, true, lastsaturate)
end
```

## Usage in processpol_push!

```julia
function processpol_push!(store, st, varmap, systemlink, c, ctrmap, nbopb)
    linkbuf = get!(task_local_storage(), :linkbuf, Int[])
    empty!(linkbuf); push!(linkbuf, -2)

    # NEW: flat version pushes directly to store (no return value)
    solvepol_flat!(store, st, linkbuf, c, varmap, ctrmap, nbopb)

    sl_push_data!(systemlink, linkbuf)
    # No push_eq_normalized! needed - already in store
    return true
end
```

## Performance Characteristics

**Before (Eq/Lit):**
- 40k lit POL with 10 additions: ~500k Lit allocations
- ~10 Vector{Lit} allocations per addition
- GC pressure from millions of short-lived objects

**After (Flat):**
- 40k lit POL: 0 Lit allocations (eliminated)
- Scratch pool grows to max depth (~5-10 buffers), then stable
- Only final result copied into store
- Cache-friendly: flat arrays, sequential access

**Expected speedup on 40k-lit POL steps: 5-10×**
