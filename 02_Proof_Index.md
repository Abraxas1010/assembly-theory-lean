# Assembly Theory: Proof Index

This document indexes the key theorems and lemmas in the Assembly Theory formalization.

## Core Definitions

### AssemblyCore.lean

| Declaration | Type | Line | Description |
|-------------|------|------|-------------|
| `Obj` | inductive | 34 | Syntax trees: `base` or `join` |
| `Obj.subobjects` | def | 47 | All syntactic subobjects |
| `Obj.isJoin` | def | 52 | Predicate: is a join node |
| `Obj.joinCount` | def | 61 | Total join nodes (no reuse) |
| `Obj.dagJoinCount` | def | 73 | Distinct join nodes (with reuse) |
| `dagJoinCount_le_joinCount` | theorem | 76 | dagJoinCount <= joinCount |

### Paper/AssemblySpace.lean

| Declaration | Type | Line | Description |
|-------------|------|------|-------------|
| `AssemblySpace` | structure | 17 | Core (Ω, U, J) data |

### Paper/AssemblyPath.lean

| Declaration | Type | Line | Description |
|-------------|------|------|-------------|
| `Step` | structure | 14 | Single join step with evidence |
| `Step.usable` | def | 22 | Both inputs available |
| `WellFormedFrom` | def | 31 | Path well-formedness |
| `availableAfter` | def | 38 | Objects available after path |
| `wellFormedFrom_append` | lemma | 47 | Append preserves well-formedness |
| `wellFormedFrom_mono` | lemma | 60 | Monotonicity in available set |
| `availableAfter_append` | lemma | 75 | Append distributes |
| `subset_availableAfter` | lemma | 83 | Original set preserved |
| `availableAfter_mono` | lemma | 92 | Monotonicity |
| `AssemblyPath` | structure | 125 | Complete assembly path |
| `AssemblyPath.len` | def | 135 | Path length |
| `AssemblyPath.primitive` | def | 141 | Trivial path for primitives |
| `AssemblyPath.mem_availableAfter` | lemma | 149 | Target is available after path |
| `Closed` | structure | 165 | Closure witness |

## Assembly Index

### Paper/AssemblyIndex.lean

| Declaration | Type | Line | Description |
|-------------|------|------|-------------|
| `HasPathLen` | def | 18 | Path of given length exists |
| `exists_len_of_closed` | lemma | 21 | Closed spaces have paths |
| `assemblyIndex` | def | 26 | Minimum path length |
| `assemblyIndex_spec` | lemma | 29 | AI achieves minimum |
| `assemblyIndex_le_of_hasLen` | lemma | 33 | AI is minimum |
| `assemblyIndex_le_of_path` | lemma | 38 | AI bounded by any path |
| `assemblyIndex_eq_zero_iff` | lemma | 42 | AI = 0 iff primitive |
| `ObjSyntax.space` | def | 82 | Canonical syntax space |
| `ObjSyntax.space.closed` | lemma | 589 | Syntax space is closed |
| `assemblyIndex_le_joinCount` | lemma | 593 | AI <= joinCount |
| `assemblyIndex_le_dagJoinCount` | lemma | 609 | AI <= dagJoinCount |
| `assemblyIndex_eq_dagJoinCount` | lemma | 803 | **AI = dagJoinCount** |

## Bounds

### Paper/AssemblyBounds.lean

| Declaration | Type | Line | Description |
|-------------|------|------|-------------|
| `Obj.size` | def | 13 | Number of primitive leaves |
| `size_eq_joinCount_add_one` | lemma | 27 | size = joinCount + 1 |
| `assemblyIndex_le_size_sub_one` | lemma | 63 | **AI <= size - 1** |
| `assemblyIndex_ge_log2` | lemma | 145 | **AI >= log2(size)** |
| `dagJoinCount_bounds` | lemma | 183 | Combined bounds |
| `greedyIndex` | def | 206 | Computable approximation |
| `greedyIndex_ge_assemblyIndex` | lemma | 209 | Greedy is upper bound |

## Quotients

### Paper/AssemblyQuotient.lean

| Declaration | Type | Line | Description |
|-------------|------|------|-------------|
| `AssemblySpace.quotient` | def | 17 | Quotient assembly space |
| `Quotient.mk_mem_U` | lemma | 31 | Primitives lift |
| `Quotient.mapPath` | def | 123 | Lift paths to quotient |
| `Closed.quotient` | def | 139 | Closure preserved |
| `assemblyIndex_quotient_le` | lemma | 153 | **AI(q) <= AI(z)** |

## Molecular Assembly

### Paper/MolecularSpace.lean

| Declaration | Type | Line | Description |
|-------------|------|------|-------------|
| `Bond` | structure | 47 | Unique bond primitive |
| `MolGraph` | structure | 75 | Labelled simple graph |
| `MolIso` | def | 86 | Label-preserving isomorphism |
| `molIso_refl` | lemma | 89 | Reflexivity |
| `molIso_symm` | lemma | 94 | Symmetry |
| `molIso_trans` | lemma | 103 | Transitivity |
| `MolGraph.disjointUnion` | def | 133 | Disjoint union |
| `MolGraph.identify` | def | 138 | Vertex identification |
| `MolGraph.IsJoinAtom` | def | 159 | Join at atom vertices |
| `evalObj` | def | 217 | Syntax -> graph |
| `evalIsoSetoid` | def | 240 | Isomorphism equivalence |
| `molSpace` | def | 250 | Molecular assembly space |
| `closed` | def | 255 | Molecular space is closed |
| `assemblyIndex_syntax_eq_dagJoinCount` | lemma | 270 | Syntax equality |
| `assemblyIndex_mol_le_dagJoinCount` | lemma | 278 | **Molecular bound** |

## B-Hypergraph

### Paper/HypergraphSpace.lean

| Declaration | Type | Line | Description |
|-------------|------|------|-------------|
| `BHypergraph.Graph` | structure | 34 | B-hypergraph data |
| `toAssemblySpace` | def | 40 | Convert to assembly space |
| `HyperPath` | abbrev | 49 | Hyperpath = assembly path |
| `HasHyperPathLen` | def | 57 | Hyperpath length exists |
| `hyperIndex` | def | 61 | Minimal hyperpath length |
| `hyperIndex_spec` | lemma | 64 | Achieves minimum |
| `hyperIndex_le_of_path` | lemma | 78 | Bounded by any path |
| `ofAssemblySpace` | def | 88 | Convert from assembly space |
| `hyperIndex_ofAssemblySpace_eq` | lemma | 98 | **Equivalence theorem** |

## Selection

### CopyNumberSelection.lean

| Declaration | Type | Line | Description |
|-------------|------|------|-------------|
| `CopyNumber` | structure | 28 | Copy number data |
| `nullTail` | def | 39 | Null model tail |
| `Assembly` | def | 49 | Assembly functional |
| `Assembly.monotone_in_mu` | lemma | 57 | Monotone in weight |
| `Assembly.monotone_in_idx` | lemma | 67 | Monotone in index |
| `selected` | def | 81 | Selection predicate |
| `selected.mono_in_Theta` | lemma | 92 | Monotone in AI threshold |
| `selected.mono_in_tau` | lemma | 101 | Monotone in abundance |
| `AssemblyEnsemble` | def | 116 | Ensemble score |
| `AssemblyEnsemble_empty` | lemma | 130 | Empty ensemble = 0 |
| `AssemblyEnsemble_zero_total` | lemma | 135 | Zero total = 0 |

## String Space

### Paper/StringPermSpace.lean

| Declaration | Type | Line | Description |
|-------------|------|------|-------------|
| `StringPerm.space` | def | 46 | String assembly space |
| `StringPerm.closed` | def | 127 | Space is closed |
| `flatten` | def | 134 | Syntax -> string |
| `mapPath` | def | 231 | Lift paths |
| `assemblyIndex_flatten_le_dagJoinCount` | lemma | 242 | String bound |
