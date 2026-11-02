/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import AME125.Defs

/-!
# Qudit graph states over `ZMod 5`

A matrix `U` over `ZMod 5` on `n` parties defines the state whose amplitude at a configuration
`x` is `5^(-(n/2)) · χ(xᵀ U x)`, with `χ(k) = exp(2πik/5)` and integer division in `n/2` (`n` is
even in the main theorem). Write `S = U + Uᵀ`. For parties split
into a kept set `A` and the rest, the reduction to `A` is a character sum over the levels of the
other parties, and it is maximally mixed exactly when no non-zero vector supported on `A` is
killed by the block `S[A, Aᶜ]` (`CutInj`). So the state is AME when that holds for every set
of `n/2` parties (`graphState_isAME`).

A configuration of `Fin 5` levels is a vector over `ZMod 5`: the two types are the same.
-/

@[expose] public section

namespace AME125

open OpenQuantumProblem35
open scoped Matrix

/-- The additive character `k ↦ exp(2πik/5)` of `ZMod 5`. -/
noncomputable abbrev χ : AddChar (ZMod 5) ℂ := ZMod.stdAddChar

/-- The quadratic form `xᵀ U x` over `ZMod 5`. -/
def quad {n : ℕ} (U : Matrix (Fin n) (Fin n) (ZMod 5)) (x : Fin n → ZMod 5) : ZMod 5 :=
  ∑ i, ∑ j, U i j * x i * x j

/-- A configuration read as a vector over `ZMod 5`. The types `Fin 5` and `ZMod 5` are the same;
this names the identification so that every term stays well typed. -/
def toZ {n : ℕ} (x : Config n 5) : Fin n → ZMod 5 := x

/-- Configurations and vectors over `ZMod 5` are the same thing. -/
def configEquiv (n : ℕ) : Config n 5 ≃ (Fin n → ZMod 5) where
  toFun := toZ
  invFun v := v
  left_inv _ := rfl
  right_inv _ := rfl

/-- The graph state of `U`: amplitude `5^(-(n/2)) · χ(xᵀ U x)` at every configuration `x`. -/
noncomputable def graphState {n : ℕ} (U : Matrix (Fin n) (Fin n) (ZMod 5)) : StateVector n 5 :=
  mkStateVector fun x ↦ ((5 : ℂ) ^ (n / 2))⁻¹ * χ (quad U (toZ x))

/-- The cut condition for a set `A` of parties and a matrix `S`: a vector supported on `A` whose
products with the columns of `S` outside `A` all vanish is zero. For `S = U + Uᵀ` this says the
map `w ↦ wᵀ S[A, Aᶜ]` is injective on vectors supported on `A`, that is, the block has full
row rank. For a square block this is the same as the block being invertible. -/
def CutInj {n : ℕ} (S : Matrix (Fin n) (Fin n) (ZMod 5)) (A : Finset (Fin n)) : Prop :=
  ∀ w : Fin n → ZMod 5, (∀ i ∉ A, w i = 0) → (∀ j ∉ A, ∑ i, w i * S i j = 0) → w = 0

/-- A character of a sum is the product of the characters. -/
lemma χ_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 5) : χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

/-- The character sum over one level: `∑ t, χ(t · e)` is `5` if `e = 0` and `0` otherwise. -/
lemma sum_χ_mul (e : ZMod 5) : ∑ t : ZMod 5, χ (t * e) = if e = 0 then 5 else 0 := by
  rw [AddChar.sum_mulShift e (ZMod.isPrimitive_stdAddChar 5)]
  split_ifs <;> simp

/-- The character sum over many levels: `∑ z, χ(∑ k, z k · e k)` is `5^k` if `e = 0` and `0`
otherwise. -/
lemma sum_χ_dot {k : ℕ} (e : Fin k → ZMod 5) :
    ∑ z : Fin k → ZMod 5, χ (∑ j, z j * e j) = if e = 0 then (5 : ℂ) ^ k else 0 := by
  simp_rw [χ_sum]
  rw [← Fintype.prod_sum (fun j t ↦ χ (t * e j))]
  simp_rw [sum_χ_mul]
  split_ifs with he
  · simp [he]
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp he
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

/-- `xᵀ U x` at `y + w`, expanded: the cross terms are `∑ j, (∑ i, w i · S i j) · y j` with
`S = U + Uᵀ`. -/
lemma quad_add {n : ℕ} (U : Matrix (Fin n) (Fin n) (ZMod 5)) (y w : Fin n → ZMod 5) :
    quad U (y + w) = quad U y + quad U w + ∑ j, (∑ i, w i * (U + Uᵀ) i j) * y j := by
  simp only [quad, Pi.add_apply, Matrix.add_apply, Matrix.transpose_apply]
  have h1 : ∑ j, (∑ i, w i * (U i j + U j i)) * y j =
      ∑ i, ∑ j, U i j * w i * y j + ∑ i, ∑ j, U i j * y i * w j := by
    simp_rw [Finset.sum_mul, mul_add, add_mul, Finset.sum_add_distrib]
    rw [Finset.sum_comm]
    congr 1
    · exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
    · exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [h1]
  simp_rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-- A sum over `Fin n` splits into the first `m` indices and the last `n - m`. -/
lemma sum_split {n m : ℕ} (hm : m ≤ n) {M : Type*} [AddCommMonoid M] (f : Fin n → M) :
    ∑ i, f i = ∑ i : Fin m, f (leftIndex hm i) + ∑ j : Fin (n - m), f (rightIndex hm j) := by
  have e : m + (n - m) = n := by omega
  rw [← Fin.sum_congr' f e, Fin.sum_univ_add]
  rfl

/-- The graph state is normalised when `n` is even. -/
theorem graphState_isNormalized {n : ℕ} (hn : Even n) (U : Matrix (Fin n) (Fin n) (ZMod 5)) :
    IsNormalized (graphState U) := by
  rw [isNormalized_iff_norm_sq_eq_one, EuclideanSpace.norm_sq_eq]
  have h : ∀ x : Config n 5, ‖(graphState U).ofLp x‖ ^ 2 = ((5 : ℝ) ^ n)⁻¹ := by
    intro x
    obtain ⟨k, rfl⟩ := hn
    simp only [graphState, ← two_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      mul_div_cancel_left₀, mkStateVector_apply, Complex.norm_mul, norm_inv, norm_pow,
      Complex.norm_ofNat, AddChar.norm_apply, mul_one, inv_pow, pow_mul, inv_inj]
    rw [← pow_mul, ← pow_mul, mul_comm]
  simp_rw [h]
  simp

/-- The quadratic form of a permuted configuration is the form of the permuted matrix. -/
lemma quad_perm {n : ℕ} (U : Matrix (Fin n) (Fin n) (ZMod 5)) (π : Equiv.Perm (Fin n))
    (x : Fin n → ZMod 5) : quad U (fun i ↦ x (π i)) = quad (U.submatrix π.symm π.symm) x := by
  symm
  unfold quad
  rw [← Equiv.sum_comp π]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Equiv.sum_comp π]
  simp

/-- Permuting the parties of a graph state gives the graph state of the permuted matrix. -/
theorem permuteState_graphState {n : ℕ} (π : Equiv.Perm (Fin n))
    (U : Matrix (Fin n) (Fin n) (ZMod 5)) :
    permuteState π (graphState U) = graphState (U.submatrix π.symm π.symm) := by
  ext x
  rw [permuteState_apply]
  simp only [graphState, mkStateVector_apply]
  rw [show toZ (permuteConfig π x) = fun i ↦ toZ x (π i) from rfl, quad_perm]

/-- Permuting the matrix moves the cut: the cut condition for `A` and the permuted matrix
follows from the cut condition for the image of `A`. -/
lemma CutInj.submatrix {n : ℕ} {S : Matrix (Fin n) (Fin n) (ZMod 5)} (π : Equiv.Perm (Fin n))
    {A : Finset (Fin n)} (h : CutInj S (A.map π.symm.toEmbedding)) :
    CutInj (S.submatrix π.symm π.symm) A := by
  intro w hw hcol
  have hz := h (fun k ↦ w (π k)) (fun k hk ↦ hw (π k) fun h' ↦ hk (by
      simpa using Finset.mem_map_of_mem π.symm.toEmbedding h')) (fun j hj ↦ by
      have hj' : π j ∉ A := fun h' ↦ hj (by
        simpa using Finset.mem_map_of_mem π.symm.toEmbedding h')
      have hc := hcol (π j) hj'
      simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply] at hc
      rw [← hc, ← Equiv.sum_comp π (fun i ↦ w i * S (π.symm i) j)]
      simp)
  funext i
  simpa using congrFun hz (π.symm i)

/-- The first `m` parties. -/
def firstHalf (n m : ℕ) : Finset (Fin n) := Finset.univ.filter fun i ↦ i.1 < m

/-- A vector on the first `m` parties, extended by zero. -/
def lift {n m : ℕ} (v : Fin m → ZMod 5) : Fin n → ZMod 5 :=
  fun i ↦ if hi : i.1 < m then v ⟨i.1, hi⟩ else 0

lemma lift_leftIndex {n m : ℕ} (hm : m ≤ n) (v : Fin m → ZMod 5) (i : Fin m) :
    lift (n := n) v (leftIndex hm i) = v i := by
  simp [lift, leftIndex, i.2]

lemma toZ_combineFirst_left {n m : ℕ} (hm : m ≤ n) (a : Config m 5) (z : Config (n - m) 5)
    (i : Fin m) : toZ (combineFirst m hm a z) (leftIndex hm i) = toZ a i :=
  combineFirst_leftIndex hm a z i

lemma toZ_combineFirst_right {n m : ℕ} (hm : m ≤ n) (a : Config m 5) (z : Config (n - m) 5)
    (j : Fin (n - m)) : toZ (combineFirst m hm a z) (rightIndex hm j) = toZ z j :=
  combineFirst_rightIndex hm a z j

lemma toZ_combineFirst_apply {n m : ℕ} (hm : m ≤ n) (a : Config m 5) (z : Config (n - m) 5)
    (i : Fin n) : toZ (combineFirst m hm a z) i =
      if hi : i.1 < m then toZ a ⟨i.1, hi⟩
      else toZ z ⟨i.1 - m, Nat.sub_lt_sub_right (Nat.le_of_not_lt hi) i.2⟩ :=
  rfl

/-- Changing the kept levels from `b` to `a` adds the difference, extended by zero. -/
lemma toZ_combineFirst_eq {n m : ℕ} (hm : m ≤ n) (a b : Config m 5) (z : Config (n - m) 5) :
    toZ (combineFirst m hm a z) = toZ (combineFirst m hm b z) + lift (toZ a - toZ b) := by
  funext i
  rw [Pi.add_apply, toZ_combineFirst_apply, toZ_combineFirst_apply]
  unfold lift
  split_ifs <;> simp

/-- The coefficient vector of the traced levels in `xᵀ U x - yᵀ U y`. -/
def coeff {n m : ℕ} (hm : m ≤ n) (S : Matrix (Fin n) (Fin n) (ZMod 5)) (d : Fin m → ZMod 5) :
    Fin (n - m) → ZMod 5 :=
  fun k ↦ ∑ i, lift d i * S i (rightIndex hm k)

/-- The entries of the first-`m` reduction of a graph state, as a character sum evaluated:
a phase depending only on `a, b`, times `5^(n-m)` if the traced coefficients vanish and `0`
otherwise. -/
theorem reduced_graphState {n m : ℕ} (hm : m ≤ n) (U : Matrix (Fin n) (Fin n) (ZMod 5))
    (a b : Config m 5) :
    ∃ K : ZMod 5, (toZ a = toZ b → K = 0) ∧ reducedDensityFirst m hm (graphState U) a b =
      ((5 : ℂ) ^ (n / 2))⁻¹ ^ 2 * χ K *
        (if coeff hm (U + Uᵀ) (toZ a - toZ b) = 0 then (5 : ℂ) ^ (n - m) else 0) := by
  set d := toZ a - toZ b
  refine ⟨quad U (lift d) + ∑ i : Fin m, (∑ l, lift d l * (U + Uᵀ) l (leftIndex hm i)) * toZ b i,
    fun hab ↦ ?_, ?_⟩
  · have hd : d = 0 := sub_eq_zero.mpr hab
    have hl : lift (n := n) d = 0 := by
      funext i
      simp [lift, hd]
    simp [hl, quad]
  have hdiff : ∀ z : Config (n - m) 5,
      quad U (toZ (combineFirst m hm a z)) - quad U (toZ (combineFirst m hm b z)) =
        (quad U (lift d) + ∑ i : Fin m, (∑ l, lift d l * (U + Uᵀ) l (leftIndex hm i)) * toZ b i) +
          ∑ k, toZ z k * coeff hm (U + Uᵀ) d k := by
    intro z
    rw [toZ_combineFirst_eq hm a b z, quad_add, sum_split hm]
    simp only [toZ_combineFirst_left, toZ_combineFirst_right, coeff]
    rw [Finset.sum_congr rfl fun k _ ↦ mul_comm (∑ l, lift d l * (U + Uᵀ) l (rightIndex hm k))
      (toZ z k)]
    ring
  have hterm : ∀ z : Config (n - m) 5,
      graphState U (combineFirst m hm a z) * star (graphState U (combineFirst m hm b z)) =
        ((5 : ℂ) ^ (n / 2))⁻¹ ^ 2 *
          χ ((quad U (lift d) +
              ∑ i : Fin m, (∑ l, lift d l * (U + Uᵀ) l (leftIndex hm i)) * toZ b i) +
            ∑ k, toZ z k * coeff hm (U + Uᵀ) d k) := by
    intro z
    rw [← hdiff z, sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj]
    simp only [graphState, mkStateVector_apply, star_mul', starRingEnd_apply]
    have hc : star ((5 : ℂ) ^ (n / 2))⁻¹ = ((5 : ℂ) ^ (n / 2))⁻¹ := by simp
    rw [hc]
    ring
  have hsum : ∑ z : Config (n - m) 5, χ (∑ k, toZ z k * coeff hm (U + Uᵀ) d k) =
      ∑ v : Fin (n - m) → ZMod 5, χ (∑ k, v k * coeff hm (U + Uᵀ) d k) :=
    Fintype.sum_equiv (configEquiv (n - m)) _ _ fun _ ↦ rfl
  rw [reducedDensityFirst]
  simp_rw [hterm, AddChar.map_add_eq_mul, ← Finset.mul_sum]
  rw [hsum, sum_χ_dot]
  ring

lemma card_firstHalf {n m : ℕ} (hm : m ≤ n) : (firstHalf n m).card = m := by
  simp [firstHalf, Fin.card_filter_val_lt, hm]

/-- The first-half reduction of a graph state on an even number of parties is maximally mixed
when the cut condition holds for the first half. -/
theorem graphState_firstHalf {n : ℕ} (hn : Even n) (U : Matrix (Fin n) (Fin n) (ZMod 5))
    (h : CutInj (U + Uᵀ) (firstHalf n (n / 2))) :
    HasMaximallyMixedFirstReduction (n / 2) (Nat.div_le_self n 2) (graphState U) := by
  have hm := Nat.div_le_self n 2
  have hk : n - n / 2 = n / 2 := by
    obtain ⟨k, rfl⟩ := hn
    omega
  ext a b
  obtain ⟨K, hK0, hK⟩ := reduced_graphState hm U a b
  rw [hK, maximallyMixed_apply, card_config]
  by_cases hab : a = b
  · subst hab
    have h0 : coeff hm (U + Uᵀ) (toZ a - toZ a) = 0 := by
      funext k
      simp [coeff, lift]
    have h5 : ((5 : ℂ) ^ (n / 2)) ≠ 0 := pow_ne_zero _ (by norm_num)
    rw [hK0 rfl, ite_eq_left h0, ite_eq_left rfl, hk]
    field_simp
    simp
  · have hne : coeff hm (U + Uᵀ) (toZ a - toZ b) ≠ 0 := by
      intro hc
      apply hab
      have hw := h (lift (toZ a - toZ b)) (fun i hi ↦ by
          simp only [firstHalf, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          simp [lift, hi]) (fun j hj ↦ by
          simp only [firstHalf, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hj
          have hjk : rightIndex hm ⟨j.1 - n / 2, by omega⟩ = j := by
            ext
            simp [rightIndex]
            omega
          have := congrFun hc ⟨j.1 - n / 2, by omega⟩
          simpa [coeff, hjk] using this)
      funext i
      have hi := congrFun hw (leftIndex hm i)
      rw [lift_leftIndex] at hi
      exact sub_eq_zero.mp hi
    rw [ite_eq_right hne, ite_eq_right hab]
    ring

/-- **A graph state over `ZMod 5` on an even number of parties is AME** when, for every set `A`
of half the parties, the block of `U + Uᵀ` between `A` and the rest is injective. -/
theorem graphState_isAME {n : ℕ} (hn : Even n) (U : Matrix (Fin n) (Fin n) (ZMod 5))
    (h : ∀ A : Finset (Fin n), A.card = n / 2 → CutInj (U + Uᵀ) A) : IsAME (graphState U) := by
  refine ⟨graphState_isNormalized hn U, fun π ↦ ?_⟩
  rw [permuteState_graphState]
  apply graphState_firstHalf hn
  have e : U.submatrix π.symm π.symm + (U.submatrix π.symm π.symm)ᵀ =
      (U + Uᵀ).submatrix π.symm π.symm := by
    ext i j
    simp
  rw [e]
  exact CutInj.submatrix π (h _ (by rw [Finset.card_map, card_firstHalf (Nat.div_le_self n 2)]))

end AME125
