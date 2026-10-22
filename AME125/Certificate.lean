/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import AME125.Data
import AME125.GraphState

/-!
# The finite core: every cut of the AME(12,5) graph is injective

`theta` is the authors' graph matrix and `U` its upper triangle, so that `U + Uᵀ` agrees with
`theta` off the diagonal and the graph state of `U` has edge weight `theta i j` between parties
`i` and `j`. For a set `A` of six parties the block of `theta` between `A` and the rest has an
explicit inverse, stored in `certs`. The kernel checks, in natural-number arithmetic mod 5, that
every certificate is an inverse (`certs_ok`) and that `certs` has one entry for every set of six
parties out of twelve (`certs_masks`). Indices are natural numbers and the certificates are
checked in chunks of a hundred, which keeps the kernel work to about two minutes. `certOK_sum`
carries a passed check over to a sum in `ZMod 5`; an inverse makes the block injective
(`cutInj_of_inverse`), which gives the cut condition for every set of six parties
(`cutInj_all`).
-/

namespace AME125

open scoped Matrix

/-- Entry `(i, j)` of the graph matrix, as a natural number. -/
def thetaN (i j : ℕ) : ℕ := (thetaRows.getD i []).getD j 0

/-- The authors' graph matrix over `ZMod 5`. -/
def theta : Matrix (Fin 12) (Fin 12) (ZMod 5) := fun i j ↦ (thetaN i.1 j.1 : ZMod 5)

/-- The upper triangle of `theta`, diagonal included: the matrix of the quadratic form. -/
def U : Matrix (Fin 12) (Fin 12) (ZMod 5) := fun i j ↦ if i.1 ≤ j.1 then theta i j else 0

theorem thetaN_symm : ∀ i < 12, ∀ j < 12, thetaN i j = thetaN j i := by
  decide

/-- `theta` is symmetric, so `U + Uᵀ` agrees with it off the diagonal. -/
theorem U_add_transpose (i j : Fin 12) (h : i ≠ j) : (U + Uᵀ) i j = theta i j := by
  simp only [Matrix.add_apply, Matrix.transpose_apply, U]
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne h) with hij | hij
  · simp [hij.le, not_le.mpr hij]
  · simp [hij.le, not_le.mpr hij, theta, thetaN_symm i.1 i.2 j.1 j.2]

/-- The position of party `k` among the parties in mask `m`. -/
def posIn (m k : ℕ) : ℕ := ((List.range k).filter fun i ↦ m.testBit i).length

/-- The position of party `j` among the parties outside mask `m`. -/
def posOut (m j : ℕ) : ℕ := ((List.range j).filter fun i ↦ !m.testBit i).length

/-- Entry `(j, k)` of a certificate, for `j` outside the mask and `k` in it. -/
def certN (m : ℕ) (L : List ℕ) (j k : ℕ) : ℕ := L.getD (6 * posOut m j + posIn m k) 0

/-- Entry `(i, k)` of the product of the block and the certificate, as a natural number. -/
def entryN (m : ℕ) (L : List ℕ) (i k : ℕ) : ℕ :=
  ((List.range 12).map fun j ↦ if m.testBit j then 0 else thetaN i j * certN m L j k).sum

/-- A certificate is good when the product is the identity mod 5 on the parties in the mask. -/
def certOK (c : ℕ × List ℕ) : Bool :=
  (List.range 12).all fun i ↦ (List.range 12).all fun k ↦
    !(c.1.testBit i && c.1.testBit k) || entryN c.1 c.2 i k % 5 == if i = k then 1 else 0

/- The kernel checks the certificates in the ten chunks they are stored in: one check over the
whole list grows faster than its length, while ten checks of about a hundred each take about
ten seconds apiece. -/

theorem certs0_ok : certs0.all certOK = true := by
  decide +kernel

theorem certs1_ok : certs1.all certOK = true := by
  decide +kernel

theorem certs2_ok : certs2.all certOK = true := by
  decide +kernel

theorem certs3_ok : certs3.all certOK = true := by
  decide +kernel

theorem certs4_ok : certs4.all certOK = true := by
  decide +kernel

theorem certs5_ok : certs5.all certOK = true := by
  decide +kernel

theorem certs6_ok : certs6.all certOK = true := by
  decide +kernel

theorem certs7_ok : certs7.all certOK = true := by
  decide +kernel

theorem certs8_ok : certs8.all certOK = true := by
  decide +kernel

theorem certs9_ok : certs9.all certOK = true := by
  decide +kernel

/-- **The kernel check**: every certificate is an inverse of its block. -/
theorem certs_ok : certs.all certOK = true := by
  simp only [certs, List.all_append, certs0_ok, certs1_ok, certs2_ok, certs3_ok, certs4_ok,
    certs5_ok, certs6_ok, certs7_ok, certs8_ok, certs9_ok, Bool.and_self]

/-- The number of the twelve parties in mask `m`. -/
def popcount (m : ℕ) : ℕ := ((List.range 12).filter fun i ↦ m.testBit i).length

/-- **The kernel check**: the masks in `certs` are exactly the 924 sets of six parties, in
increasing order. -/
theorem certs_masks : certs.map Prod.fst = (List.range 4096).filter fun m ↦ popcount m = 6 := by
  decide +kernel

/-- A sum over `List.range 12` is a sum over `Fin 12`. -/
lemma sum_range_twelve {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ((List.range 12).map f).sum = ∑ j : Fin 12, f j := by
  rw [← List.sum_toFinset f List.nodup_range, List.toFinset_range, Finset.sum_range]

/-- A passed certificate check, as an identity in `ZMod 5`. -/
lemma certOK_sum {c : ℕ × List ℕ} (hc : certOK c = true) (i k : Fin 12)
    (hi : c.1.testBit i.1 = true) (hk : c.1.testBit k.1 = true) :
    ∑ j : Fin 12, (if c.1.testBit j.1 then 0 else theta i j * (certN c.1 c.2 j k : ZMod 5)) =
      if i = k then 1 else 0 := by
  have h : entryN c.1 c.2 i k % 5 = if i.1 = k.1 then 1 else 0 := by
    simp only [certOK, List.all_eq_true, List.mem_range] at hc
    simpa [hi, hk] using hc i.1 i.2 k.1 k.2
  have hcast : ((entryN c.1 c.2 i k : ℕ) : ZMod 5) =
      ∑ j : Fin 12, (if c.1.testBit j.1 then 0 else theta i j * (certN c.1 c.2 j k : ZMod 5)) := by
    rw [entryN, sum_range_twelve, Nat.cast_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs <;> simp [theta]
  rw [← hcast, ← ZMod.natCast_mod, h]
  by_cases hik : i = k
  · simp [hik]
  · simp [hik, Fin.val_ne_iff.mpr hik]

/-- A block with a right inverse is injective: the cut condition follows. -/
theorem cutInj_of_inverse {n : ℕ} (S : Matrix (Fin n) (Fin n) (ZMod 5)) (A : Finset (Fin n))
    (R : Fin n → Fin n → ZMod 5)
    (h : ∀ i ∈ A, ∀ k ∈ A, ∑ j, (if j ∈ A then 0 else S i j * R j k) = if i = k then 1 else 0) :
    CutInj S A := by
  intro w hw hcol
  funext k
  by_cases hk : k ∈ A
  · calc w k = ∑ i, w i * (if i = k then 1 else 0) := by simp
      _ = ∑ i, w i * ∑ j, (if j ∈ A then 0 else S i j * R j k) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        by_cases hi : i ∈ A
        · rw [h i hi k hk]
        · simp [hw i hi]
      _ = ∑ j, (if j ∈ A then 0 else (∑ i, w i * S i j) * R j k) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        split_ifs <;> simp [Finset.sum_mul, mul_assoc]
      _ = 0 := by
        refine Finset.sum_eq_zero fun j _ ↦ ?_
        split_ifs with hj
        · rfl
        · simp [hcol j hj]
  · exact hw k hk

/-- The mask of a set of parties: the sum of `2 ^ i` over its members. -/
def maskOf (A : Finset (Fin 12)) : ℕ := ∑ i ∈ A.map Fin.valEmbedding, 2 ^ i

lemma testBit_maskOf (A : Finset (Fin 12)) (i : Fin 12) :
    (maskOf A).testBit i.1 = true ↔ i ∈ A := by
  rw [← Nat.mem_bitIndices, ← List.mem_toFinset, maskOf, Finset.toFinset_bitIndices_sum_two_pow]
  simp [Fin.val_inj]

lemma maskOf_lt (A : Finset (Fin 12)) : maskOf A < 4096 := by
  calc maskOf A ≤ ∑ i ∈ Finset.range 12, 2 ^ i := by
        refine Finset.sum_le_sum_of_subset fun x hx ↦ ?_
        obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
        simp [a.2]
    _ < 4096 := by decide

lemma popcount_maskOf (A : Finset (Fin 12)) : popcount (maskOf A) = A.card := by
  have hnd : ((List.range 12).filter fun i ↦ (maskOf A).testBit i).Nodup :=
    List.nodup_range.filter _
  rw [popcount, ← List.toFinset_card_of_nodup hnd, List.toFinset_filter, List.toFinset_range,
    ← Finset.card_map Fin.valEmbedding]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_map, Fin.valEmbedding_apply]
  constructor
  · rintro ⟨hx, hb⟩
    exact ⟨⟨x, hx⟩, (testBit_maskOf A ⟨x, hx⟩).mp hb, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.2, (testBit_maskOf A a).mpr ha⟩

/-- **Every set of six parties satisfies the cut condition** for the authors' graph. -/
theorem cutInj_all (A : Finset (Fin 12)) (hA : A.card = 6) : CutInj (U + Uᵀ) A := by
  have hm : maskOf A ∈ certs.map Prod.fst := by
    rw [certs_masks, List.mem_filter, List.mem_range]
    exact ⟨maskOf_lt A, by simp [popcount_maskOf, hA]⟩
  obtain ⟨⟨m, L⟩, hc, hmL⟩ := List.mem_map.mp hm
  simp only at hmL
  subst hmL
  have hok : certOK (maskOf A, L) = true := List.all_eq_true.mp certs_ok _ hc
  refine cutInj_of_inverse _ A (fun j k ↦ (certN (maskOf A) L j k : ZMod 5)) fun i hi k hk ↦ ?_
  rw [← certOK_sum hok i k ((testBit_maskOf A i).mpr hi) ((testBit_maskOf A k).mpr hk)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  by_cases hj : j ∈ A
  · simp [hj, (testBit_maskOf A j).mpr hj]
  · have hb : (maskOf A).testBit j.1 = false :=
      Bool.eq_false_iff.mpr (mt (testBit_maskOf A j).mp hj)
    rw [if_neg hj, hb, if_neg Bool.false_ne_true,
      U_add_transpose i j fun h ↦ hj (h ▸ hi)]

end AME125
