/-!
# Axiom Audit Script

This script prints the axioms used by key theorems in the Assembly Theory formalization.
Expected axioms are standard Lean kernel axioms only:
- `propext` (propositional extensionality)
- `Classical.choice` (axiom of choice)
- `Quot.sound` (quotient soundness)
-/

import HeytingLean.ATheory.Paper.AssemblyBounds
import HeytingLean.ATheory.Paper.MolecularSpace
import HeytingLean.ATheory.Paper.HypergraphSpace
import HeytingLean.ATheory.CopyNumberSelection

#print axioms HeytingLean.ATheory.Paper.AssemblyBounds.dagJoinCount_bounds
#print axioms HeytingLean.ATheory.Paper.ObjSyntax.space.assemblyIndex_eq_dagJoinCount
#print axioms HeytingLean.ATheory.Paper.Molecular.assemblyIndex_mol_le_dagJoinCount
