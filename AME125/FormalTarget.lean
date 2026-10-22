/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import AME125.Certificate

/-!
# The headline: an AME(12,5) state exists

The witness is the graph state of the matrix of S. Bevins and Y. Bidav (arXiv:2608.05781):
twelve five-level parties, amplitude `5⁻⁶ · χ(xᵀ U x)` with `U` the upper triangle of their graph
matrix. It is AME by the general graph-state criterion (`AME125.graphState_isAME`) and the
kernel-checked cut certificates (`AME125.cutInj_all`). The statement is Formal Conjectures' own
`OpenQuantumProblem35.ame_12_5_open`.
-/

namespace AME125

open OpenQuantumProblem35

/-- The witness: the graph state of the authors' graph over `ZMod 5`. -/
noncomputable def ame125State : StateVector 12 5 := graphState U

/-- The witness is absolutely maximally entangled. -/
theorem ame125State_isAME : IsAME ame125State :=
  graphState_isAME ⟨6, rfl⟩ U fun A hA ↦ cutInj_all A (by simpa using hA)

/-- An AME(12,5) state exists. -/
theorem ame_12_5_open : ExistsAME 12 5 :=
  ⟨ame125State, ame125State_isAME⟩

end AME125
