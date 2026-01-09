import Lake
open Lake DSL

package assemblyTheory where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib HeytingLean where
  roots := #[`HeytingLean.ATheory.Paper.AssemblyBounds,
             `HeytingLean.ATheory.Paper.MolecularSpace,
             `HeytingLean.ATheory.Paper.HypergraphSpace,
             `HeytingLean.ATheory.Paper.StringPermSpace,
             `HeytingLean.ATheory.CopyNumberSelection]
