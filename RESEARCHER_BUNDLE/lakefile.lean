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
  -- Build all modules under HeytingLean (no explicit roots = auto-discover)
  globs := #[.submodules `HeytingLean]
