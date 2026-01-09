# Assembly Theory: Dependencies

This document lists the dependencies and version requirements.

## Lean Toolchain

```
leanprover/lean4:v4.15.0
```

(Check `lean-toolchain` for exact version)

## Lake Dependencies

| Package | Version | Purpose |
|---------|---------|---------|
| mathlib | pinned | Standard mathematical library |

## Mathlib Imports Used

### Core Data Structures

- `Mathlib.Data.Nat.Basic` - Natural number operations
- `Mathlib.Data.Nat.Find` - `Nat.find` for infimum
- `Mathlib.Data.Nat.Log` - Logarithm for bounds
- `Mathlib.Data.Set.Lattice` - Set operations
- `Mathlib.Data.Finset.Basic` - Finite sets
- `Mathlib.Data.Finset.Card` - Cardinality
- `Mathlib.Data.Finset.Filter` - Filtered finsets
- `Mathlib.Data.List.Basic` - List operations

### Analysis (for Selection)

- `Mathlib.Data.Real.Basic` - Real numbers
- `Mathlib.Analysis.SpecialFunctions.Exp` - Exponential function

### Graph Theory (for Molecular)

- `Mathlib.Combinatorics.SimpleGraph.Basic` - Simple graphs
- `Mathlib.Combinatorics.SimpleGraph.Maps` - Graph homomorphisms
- `Mathlib.Combinatorics.SimpleGraph.Operations` - Graph operations
- `Mathlib.Combinatorics.SimpleGraph.Sum` - Disjoint union

## No Custom Axioms

The formalization uses only standard Lean kernel axioms:

| Axiom | Source | Purpose |
|-------|--------|---------|
| `propext` | Lean kernel | Propositional extensionality |
| `Classical.choice` | Classical logic | Axiom of choice |
| `Quot.sound` | Quotient types | Quotient soundness |

## Version Locking

All versions are locked in `lake-manifest.json` for reproducibility.

To update dependencies:
```bash
lake update
```

To restore pinned versions:
```bash
lake exe cache get  # If using mathlib cache
lake build
```

## Building Without Network

If dependencies are already fetched:
```bash
lake build --offline
```
