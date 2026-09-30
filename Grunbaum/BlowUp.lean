/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import Grunbaum.Fan
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# The blow-up lemma ([JFA, Lemma 2.2])

For `A ∈ 𝒜_d` and `1 ≤ i ≤ d` the *blow-up* `bl_i(A) ∈ 𝒜_{d+1}` of [JFA, Section 2] is obtained
by appending a copy of the `i`-th row and column of `A`.

> **Lemma 2.2** ([JFA]). Let `A' ∈ 𝒜_{d-1}`, let `A := bl_i(A')` for some `1 ≤ i ≤ d - 1` and let
> `D := Diag(d₁, …, d_d) ∈ 𝒟_d` be invertible. We set
> `D' := Diag(d₁, …, d_{i-1}, dᵢ + d_d, d_{i+1}, …, d_{d-1})`. Then `D' ∈ 𝒟_{d-1}` is invertible,
> `λ(AD)` has a zero entry and `λ(A'D')` is obtained from `λ(AD)` by deleting a zero entry.

We prove a version for arbitrary blow-ups, in terms of characteristic polynomials. A map
`f : ι → κ` and `T ∈ 𝒜_κ` give the blow-up `S = T(f, f) = (t_{f(i) f(j)})ᵢⱼ ∈ 𝒜_ι`. For weights
`w` on `ι`, the merged weights on `κ` are `w'ₐ = ∑_{f(i) = a} wᵢ` (`Grunbaum.mergeWeight`). Then
(`Grunbaum.charpoly_weightedMatrix_submatrix`)

`X^{|κ|} · χ(√D S √D) = X^{|ι|} · χ(√D' T √D')`.

Indeed, `√D S √D = (√D E)(T Eᵀ √D)` for the `0/1`-matrix `E` of `f`, and
`(T Eᵀ √D)(√D E) = T D'`; so this is the identity `X^{|κ|} χ(AB) = X^{|ι|} χ(BA)` for
rectangular matrices (`Matrix.charpoly_mul_comm'`).

For the errata we need the case of twins (`Grunbaum.charpoly_weightedMatrix_eq_X_mul`): if the
rows `i ≠ j` of `S` coincide, then `S` is the blow-up of its principal submatrix `S'` on
`ι ∖ {j}`, and merging the weight of `j` into `i` gives `χ(√D S √D) = X · χ(√D' S' √D')`. Hence
the spectrum of `√D' S' √D'` is that of `√D S √D` with one zero removed, and
`π₂(√D' S' √D') = π₂(√D S √D)` as soon as the second largest eigenvalue of `√D S √D` is positive
(`Grunbaum.sumTopTwo_eq_of_charpoly_eq_X_mul`).

## References

* [JFA] G. Basso, *Computation of maximal projection constants*, J. Funct. Anal. 277 (2019).
-/

open Finset Matrix Polynomial

namespace Grunbaum

variable {ι κ : Type*}

/-! ### Merging weights -/

section Merge

variable [Fintype ι] [DecidableEq κ]

/-- The merged weights `w'ₐ = ∑_{f(i) = a} wᵢ` on `κ`. -/
def mergeWeight (f : ι → κ) (w : ι → ℝ) : κ → ℝ :=
  fun a => ∑ i ∈ univ.filter fun i => f i = a, w i

lemma mergeWeight_nonneg (f : ι → κ) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (a : κ) :
    0 ≤ mergeWeight f w a :=
  sum_nonneg fun i _ => hw i

lemma isWeight_mergeWeight [Fintype κ] (f : ι → κ) {w : ι → ℝ} (hw : IsWeight w) :
    IsWeight (mergeWeight f w) :=
  ⟨mergeWeight_nonneg f hw.nonneg, by rw [← hw.sum_eq]; exact sum_fiberwise univ f w⟩

/-- The `0/1`-matrix `E` of a map `f : ι → κ`, with `Eᵢₐ = 1` iff `f(i) = a`. -/
def blowUpMatrix (f : ι → κ) : Matrix ι κ ℝ := of fun i a => if f i = a then 1 else 0

variable [Fintype κ]

omit [Fintype ι] in
lemma submatrix_eq_mul (T : Matrix κ κ ℝ) (f : ι → κ) :
    T.submatrix f f = blowUpMatrix f * T * (blowUpMatrix f)ᵀ := by
  ext i j
  simp [blowUpMatrix, mul_apply]

omit [Fintype κ] in
lemma transpose_blowUpMatrix_mul_diagonal [DecidableEq ι] (f : ι → κ) (w : ι → ℝ) :
    (blowUpMatrix f)ᵀ * diagonal w * blowUpMatrix f = diagonal (mergeWeight f w) := by
  ext a b
  rw [mul_apply]
  simp only [mul_diagonal, transpose_apply, blowUpMatrix, of_apply, diagonal_apply, mergeWeight,
    sum_filter]
  by_cases hab : a = b
  · subst hab
    simp only [ite_true]
    refine sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  · rw [ite_eq_right hab]
    refine sum_eq_zero fun k _ => ?_
    by_cases hk : f k = a
    · simp [hk, hab]
    · simp [hk]

end Merge

/-! ### The blow-up lemma -/

section BlowUp

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- **The blow-up lemma** ([JFA, Lemma 2.2], for arbitrary blow-ups): for `S = T(f, f)` and the
merged weights `w'` of `w`, `X^{|κ|} χ(√D S √D) = X^{|ι|} χ(√D' T √D')`. -/
theorem charpoly_weightedMatrix_submatrix (T : Matrix κ κ ℝ) (f : ι → κ) {w : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) :
    X ^ Fintype.card κ * (weightedMatrix (T.submatrix f f) w).charpoly =
      X ^ Fintype.card ι * (weightedMatrix T (mergeWeight f w)).charpoly := by
  set E := blowUpMatrix f
  set Dw : Matrix ι ι ℝ := diagonal fun i => √(w i)
  set Dv : Matrix κ κ ℝ := diagonal fun a => √(mergeWeight f w a)
  have hM : weightedMatrix (T.submatrix f f) w = (Dw * E) * (T * Eᵀ * Dw) := by
    rw [weightedMatrix_eq_diagonal_mul, submatrix_eq_mul]
    simp only [Dw, E, Matrix.mul_assoc]
  have hDD : Dw * Dw = diagonal w := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    exact Real.mul_self_sqrt (hw i)
  have hN : (T * Eᵀ * Dw) * (Dw * E) = T * diagonal (mergeWeight f w) := by
    calc (T * Eᵀ * Dw) * (Dw * E) = T * (Eᵀ * (Dw * Dw) * E) := by
          simp only [Matrix.mul_assoc]
      _ = T * diagonal (mergeWeight f w) := by
          rw [hDD, transpose_blowUpMatrix_mul_diagonal]
  have hvv : Dv * Dv = diagonal (mergeWeight f w) := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext a
    exact Real.mul_self_sqrt (mergeWeight_nonneg f hw a)
  have hW : (weightedMatrix T (mergeWeight f w)).charpoly =
      (T * diagonal (mergeWeight f w)).charpoly := by
    rw [weightedMatrix_eq_diagonal_mul, Matrix.mul_assoc, charpoly_mul_comm, Matrix.mul_assoc,
      hvv]
  rw [hM, charpoly_mul_comm', hN, hW]

end BlowUp

/-! ### Deleting a twin -/

section Twin

variable [Fintype ι] [DecidableEq ι]

/-- The map `ι → ι ∖ {j}` sending `j` to `i` and fixing all other indices. -/
def foldTo (i j : ι) (hij : i ≠ j) : ι → {k // k ≠ j} :=
  fun k => if h : k = j then ⟨i, hij⟩ else ⟨k, h⟩

omit [Fintype ι] in
lemma foldTo_val (i j : ι) (hij : i ≠ j) (k : ι) :
    (foldTo i j hij k : ι) = if k = j then i else k := by
  unfold foldTo
  split_ifs <;> rfl

lemma card_subtype_ne_add_one (j : ι) : Fintype.card {k // k ≠ j} + 1 = Fintype.card ι := by
  rw [Fintype.card_subtype, filter_ne' univ j, card_erase_of_mem (mem_univ j), card_univ]
  have : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨j⟩
  omega

/-- **[JFA, Lemma 2.2]** for twins. If the rows `i ≠ j` of the symmetric matrix `S` coincide,
then `S` is the blow-up of its principal submatrix `S'` on `ι ∖ {j}`, and merging the weight of
`j` into `i` gives `χ(√D S √D) = X · χ(√D' S' √D')`. -/
theorem charpoly_weightedMatrix_eq_X_mul {S : Matrix ι ι ℝ} (hS : ∀ k l, S l k = S k l)
    {i j : ι} (hij : i ≠ j) (hrow : ∀ k, S j k = S i k) {w : ι → ℝ} (hw : ∀ k, 0 ≤ w k) :
    (weightedMatrix S w).charpoly =
      X * (weightedMatrix (S.submatrix (↑) (↑) : Matrix {k // k ≠ j} {k // k ≠ j} ℝ)
        (mergeWeight (foldTo i j hij) w)).charpoly := by
  have hS' : S = (S.submatrix (↑) (↑) : Matrix {k // k ≠ j} {k // k ≠ j} ℝ).submatrix
      (foldTo i j hij) (foldTo i j hij) := by
    ext k l
    simp only [submatrix_apply, foldTo_val]
    by_cases hk : k = j <;> by_cases hl : l = j
    · subst hk hl
      rw [ite_eq_left rfl, hrow, hS, hrow]
    · subst hk
      rw [ite_eq_left rfl, ite_eq_right hl, hrow]
    · subst hl
      rw [ite_eq_right hk, ite_eq_left rfl, ← hS, hrow, hS]
    · rw [ite_eq_right hk, ite_eq_right hl]
  have key := charpoly_weightedMatrix_submatrix
    (S.submatrix (↑) (↑) : Matrix {k // k ≠ j} {k // k ≠ j} ℝ) (foldTo i j hij) hw
  rw [← hS', ← card_subtype_ne_add_one j, pow_succ, mul_assoc] at key
  exact mul_left_cancel₀ (pow_ne_zero _ X_ne_zero) key

end Twin

/-! ### Deleting a zero eigenvalue does not change `π₂` -/

section Spectrum

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] in
/-- The number of indices at which `f` takes the value `x`, as a multiplicity. -/
lemma card_filter_eq_count (f : ι → ℝ) (x : ℝ) :
    (univ.filter fun i => x = f i).card = Multiset.count x (Multiset.map f univ.val) := by
  rw [Multiset.count_map, ← Finset.filter_val, Finset.card_val]

omit [DecidableEq ι] [DecidableEq κ] in
/-- If `g` takes the values `f a` and `f b` at least as often as `f` does, then they are values of
`g` at two distinct indices. -/
lemma exists_pair_of_card_filter_le {f : ι → ℝ} {g : κ → ℝ} {a b : ι} (hab : a ≠ b)
    (ha : (univ.filter fun i => f a = f i).card ≤ (univ.filter fun k => f a = g k).card)
    (hb : (univ.filter fun i => f b = f i).card ≤ (univ.filter fun k => f b = g k).card) :
    ∃ a' b', a' ≠ b' ∧ g a' = f a ∧ g b' = f b := by
  by_cases hfab : f a = f b
  · have h2 : 1 < (univ.filter fun i => f a = f i).card :=
      one_lt_card.mpr ⟨a, by simp, b, by simp [hfab], hab⟩
    obtain ⟨a', ha', b', hb', hne⟩ := one_lt_card.mp (h2.trans_le ha)
    simp only [mem_filter, mem_univ, true_and] at ha' hb'
    exact ⟨a', b', hne, ha'.symm, hb'.symm.trans hfab⟩
  · obtain ⟨a', ha'⟩ := card_pos.mp (lt_of_lt_of_le (card_pos.mpr ⟨a, by simp⟩) ha)
    obtain ⟨b', hb'⟩ := card_pos.mp (lt_of_lt_of_le (card_pos.mpr ⟨b, by simp⟩) hb)
    simp only [mem_filter, mem_univ, true_and] at ha' hb'
    exact ⟨a', b', fun h => hfab (by rw [ha', hb', h]), ha'.symm, hb'.symm⟩

/-- **Deleting a zero eigenvalue.** If `χ_A = X · χ_B` for symmetric matrices `A` and `B`, i.e.
the spectrum of `B` is that of `A` with one zero removed, and the second largest eigenvalue of
`A` is positive, then `π₂ B = π₂ A`. -/
theorem sumTopTwo_eq_of_charpoly_eq_X_mul {A : Matrix ι ι ℝ} {B : Matrix κ κ ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A.charpoly = X * B.charpoly) {a b : ι}
    (hab : a ≠ b) (ha : ∀ j, hA.eigenvalues j ≤ hA.eigenvalues a)
    (hb : ∀ j, j ≠ a → hA.eigenvalues j ≤ hA.eigenvalues b) (hpos : 0 < hA.eigenvalues b) :
    π₂ B = π₂ A := by
  -- the multisets of eigenvalues: `λ(A) = 0 :: λ(B)`
  have hroots : Multiset.map hA.eigenvalues univ.val =
      0 ::ₘ Multiset.map hB.eigenvalues univ.val := by
    have e1 := hA.roots_charpoly_eq_eigenvalues
    have e2 := hB.roots_charpoly_eq_eigenvalues
    rw [h, roots_mul (mul_ne_zero X_ne_zero (charpoly_monic B).ne_zero), roots_X, e2] at e1
    simp only [RCLike.ofReal_real_eq_id, Function.id_comp] at e1
    rw [← e1, Multiset.singleton_add]
  have hcount : ∀ x, x ≠ 0 → (univ.filter fun i => x = hA.eigenvalues i).card =
      (univ.filter fun k => x = hB.eigenvalues k).card := by
    intro x hx
    rw [card_filter_eq_count, card_filter_eq_count, hroots, Multiset.count_cons_of_ne hx]
  have hcount' : ∀ x, (univ.filter fun k => x = hB.eigenvalues k).card ≤
      (univ.filter fun i => x = hA.eigenvalues i).card := by
    intro x
    rw [card_filter_eq_count, card_filter_eq_count, hroots]
    exact Multiset.count_le_count_cons x 0 _
  have hposa : 0 < hA.eigenvalues a := lt_of_lt_of_le hpos (ha b)
  -- the two largest eigenvalues of `A` are eigenvalues of `B`
  obtain ⟨a', b', hab', ha', hb'⟩ := exists_pair_of_card_filter_le hab
    (hcount _ hposa.ne').le (hcount _ hpos.ne').le
  have hge : π₂ A ≤ π₂ B := by
    rw [sumTopTwo_eq_top_two hA hab ha hb, ← ha', ← hb']
    exact add_le_sumTopTwo hB hab'
  -- conversely, any two eigenvalues of `B` are eigenvalues of `A`
  refine le_antisymm ?_ hge
  refine sumTopTwo_le_of_forall_add_le hB (Fintype.one_lt_card_iff.mpr ⟨a', b', hab'⟩)
    fun i j hij => ?_
  obtain ⟨i', j', hij', hi', hj'⟩ := exists_pair_of_card_filter_le hij (hcount' _) (hcount' _)
  rw [← hi', ← hj']
  exact add_le_sumTopTwo hA hij'

end Spectrum

end Grunbaum
