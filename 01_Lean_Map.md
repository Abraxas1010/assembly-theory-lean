# Assembly Theory: Concept to Lean Mapping

This document maps concepts from "The Physics of Causation" to their Lean 4 formalizations.

## Core Concepts

| Paper Concept | Paper Symbol | Lean Namespace | Lean Name |
|--------------|--------------|----------------|-----------|
| Assembly Space | (Ω, U, J) | `Paper.AssemblySpace` | `AssemblySpace` |
| Object Space | Ω | `AssemblySpace.Ω` | Type parameter |
| Primitives | U | `AssemblySpace.U` | `Set Ω` |
| Join Predicate | J | `AssemblySpace.J` | `Ω → Ω → Ω → Prop` |
| Assembly Path | π | `Paper.AssemblySpace` | `AssemblyPath` |
| Path Length | |π| | `AssemblyPath.len` | `Nat` |
| Assembly Index | a(x) | `Paper.AssemblySpace.AssemblyIndex` | `assemblyIndex` |
| Closure | Ω = closure(U, J) | `Paper.AssemblySpace` | `Closed` |

## Concrete Models

| Model | Description | Lean Module | Key Type |
|-------|-------------|-------------|----------|
| Syntax Trees | Binary trees over alphabet | `AssemblyCore` | `Obj α` |
| ObjSyntax.space | Canonical closed assembly space | `Paper.AssemblyIndex` | `AssemblySpace` |
| Molecular | Bonds as primitives | `Paper.MolecularSpace` | `Bond Atom` |
| String | Lists with permutation join | `Paper.StringPermSpace` | `List Atom` |
| B-Hypergraph | Directed hypergraph view | `Paper.HypergraphSpace` | `Graph` |

## Path Semantics

| Concept | Description | Lean Definition |
|---------|-------------|-----------------|
| Step | Single join operation | `Step` (structure with x, y, z, ok) |
| Usable | Both inputs available | `Step.usable A s` |
| Well-formed | All steps usable sequentially | `WellFormedFrom A steps` |
| Available After | Set of objects after path | `availableAfter A steps` |
| Assembly Path | Well-formed path to target | `AssemblyPath z` |

## Complexity Measures

| Measure | Description | Lean Definition |
|---------|-------------|-----------------|
| Join Count | Number of join nodes (no reuse) | `Obj.joinCount` |
| DAG Join Count | Distinct join subobjects (with reuse) | `Obj.dagJoinCount` |
| Size | Number of primitive leaves | `Obj.size` |
| Assembly Index | Minimum path length | `assemblyIndex` |

## Bounds

| Bound | Statement | Lean Lemma |
|-------|-----------|------------|
| Lower | AI >= log2(size) | `assemblyIndex_ge_log2` |
| Upper | AI <= size - 1 | `assemblyIndex_le_size_sub_one` |
| Equality | AI = dagJoinCount (syntax) | `assemblyIndex_eq_dagJoinCount` |
| Quotient | AI(q) <= AI(z) | `assemblyIndex_quotient_le` |

## Selection

| Concept | Description | Lean Definition |
|---------|-------------|-----------------|
| Copy Number | Abundance function | `CopyNumber.n` |
| Weight | Secondary abundance | `CopyNumber.μ` |
| Assembly Functional | Combined score | `Assembly idx μ v` |
| Selection Predicate | High AI + high abundance | `selected Θ τ vset idx μ` |
| Ensemble | Multi-object score | `AssemblyEnsemble idx n vset` |

## Module Dependencies

```
AssemblyCore
    │
    ├── Paper/AssemblySpace
    │       │
    │       └── Paper/AssemblyPath
    │               │
    │               └── Paper/AssemblyIndex
    │                       │
    │                       ├── Paper/AssemblyBounds
    │                       │
    │                       ├── Paper/AssemblyQuotient
    │                       │       │
    │                       │       └── Paper/MolecularSpace
    │                       │
    │                       ├── Paper/HypergraphSpace
    │                       │
    │                       └── Paper/StringPermSpace
    │
    └── CopyNumberSelection
```
