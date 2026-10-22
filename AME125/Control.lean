/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import AME125.Certificate

/-!
# Control: a broken graph is not AME

Delete the six edges between party `0` and parties `6, …, 11` from the authors' graph. Then
party `0` is invisible to the other half of the first cut, so the reduction to the first six
parties has a non-zero entry off the diagonal (`controlState_not_isAME`). The proof goes through
the same reduction formula as the headline result and uses none of the certificates, so it
shows the formula really separates AME states from others.
-/

namespace AME125

open OpenQuantumProblem35
open scoped Matrix

/-- The authors' upper triangle with the edges between party `0` and parties `6, …, 11`
removed. -/
def controlU : Matrix (Fin 12) (Fin 12) (ZMod 5) :=
  fun i j ↦ if i.1 = 0 ∧ 6 ≤ j.1 then 0 else U i j

/-- The control state: the graph state of the broken graph. -/
noncomputable def controlState : StateVector 12 5 := graphState controlU

/-- The level-`1` configuration of party `0` and level `0` elsewhere, on the first six parties. -/
def e0 : Config 6 5 := fun i ↦ if i.1 = 0 then 1 else 0

/-- No traced level is coupled to the difference `e0 - 0`. -/
lemma coeff_e0 :
    coeff (Nat.div_le_self 12 2) (controlU + controlUᵀ) (toZ e0 - toZ (0 : Config 6 5)) = 0 := by
  funext k
  simp only [coeff, Pi.zero_apply]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  by_cases hi : i.1 = 0
  · have hk : 6 ≤ (rightIndex (Nat.div_le_self 12 2) k).1 := by simp [rightIndex]
    have hne : rightIndex (Nat.div_le_self 12 2) k ≠ 0 := fun h ↦ by simp [h] at hk
    simp [controlU, U, hi, hk, hne, Matrix.add_apply, Matrix.transpose_apply]
  · have : lift (n := 12) (toZ e0 - toZ (0 : Config 6 5)) i = 0 := by
      simp only [lift]
      split_ifs with h
      · rw [Pi.sub_apply]
        have h1 : toZ e0 ⟨i.1, h⟩ = 0 := by
          simp only [toZ, e0, hi, if_false]
          rfl
        have h2 : toZ (0 : Config 6 5) ⟨i.1, h⟩ = 0 := rfl
        rw [h1, h2, sub_zero]
      · rfl
    simp [this]

/-- **The control state is not AME.** -/
theorem controlState_not_isAME : ¬ IsAME controlState := by
  intro h
  have hred := h.2 (Equiv.refl _)
  rw [permuteState_refl] at hred
  have hentry := congrFun (congrFun hred e0) 0
  obtain ⟨K, -, hK⟩ := reduced_graphState (Nat.div_le_self 12 2) controlU e0 0
  have hne : e0 ≠ 0 := fun h0 ↦ by simpa [e0] using congrFun h0 ⟨0, by norm_num⟩
  rw [maximallyMixed_apply, if_neg hne] at hentry
  rw [controlState, hK, coeff_e0, if_pos rfl] at hentry
  have hχ : χ K ≠ 0 := fun h0 ↦ by simpa [h0] using AddChar.norm_apply χ K
  simp [hχ] at hentry

end AME125
