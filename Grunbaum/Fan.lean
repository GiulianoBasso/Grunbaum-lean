/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import Grunbaum.Basic
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Fan's maximum principle for `π₂`

Let `A` be a symmetric matrix. We prove

* **Stationarity** (`Grunbaum.stationary`, `Grunbaum.mulVec_eq_of_isMax`): if an orthonormal
  pair `u, v` maximizes `xᵀAx + yᵀAy` among all orthonormal pairs, then the plane spanned by
  `u, v` is invariant under `A`. For `P = uuᵀ + vvᵀ` this is `AP = PA`, the equality case of
  Fan's maximum principle ([AMOP, Lemma 3.1]).
* **Fan's maximum principle** ([Fan 1949], [AMOP, (3.1)]): `π₂(A) = λ₁ + λ₂` is the sum of the
  two largest eigenvalues of `A` (`Grunbaum.sumTopTwo_eq_top_two`,
  `Grunbaum.sumTopTwo_eq_eigenvalues₀`), and the supremum defining `π₂(A)` is attained by a pair
  of eigenvectors (`Grunbaum.exists_fanValue_eq_sumTopTwo`).

In [JFA] the second statement is used to write `π_n(M) = max {Tr(MP) : P ∈ 𝒫_{n,d}}`; in the
proofs of [JFA, Theorem 1.2] and [AMOP, Lemma 3.2] the first statement replaces the equality case
of von Neumann's trace inequality (see [Theobald 1975] and [Carlsson 2021]).

## References

* K. Fan, *On a theorem of Weyl concerning eigenvalues of linear transformations I*, 1949.
* [AMOP] G. Basso, *Almost minimal orthogonal projections*, Israel J. Math. 243 (2021).
* C. M. Theobald, *An inequality for the trace of the product of two symmetric matrices*,
  Math. Proc. Cambridge Philos. Soc. 77 (1975).
* M. Carlsson, *von Neumann's trace inequality for Hilbert–Schmidt operators*,
  Expo. Math. 39 (2021).

This file is adapted from `ProjectionConstants/Grunbaum/{Stationary,Fan}.lean` of the library
*Projection constants in Lean*.
-/

open Finset Matrix

namespace Grunbaum

variable {ι : Type*} [Fintype ι]

/-! ### Quadratic forms of symmetric matrices -/

/-- For a symmetric matrix `A`, `xᵀAy = yᵀAx`. -/
lemma dotProduct_mulVec_comm {A : Matrix ι ι ℝ} (hA : ∀ i j, A j i = A i j) (x y : ι → ℝ) :
    x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (A *ᵥ x) := by
  simp only [dotProduct, mulVec, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [hA]; ring

lemma quad_add_smul {A : Matrix ι ι ℝ} (hA : ∀ i j, A j i = A i j) (x z : ι → ℝ) (a b : ℝ) :
    (a • x + b • z) ⬝ᵥ (A *ᵥ (a • x + b • z))
      = a ^ 2 * (x ⬝ᵥ (A *ᵥ x)) + 2 * a * b * (z ⬝ᵥ (A *ᵥ x)) + b ^ 2 * (z ⬝ᵥ (A *ᵥ z)) := by
  have h := dotProduct_mulVec_comm hA x z
  simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul] at h ⊢
  rw [h]
  ring

lemma eq_zero_of_dotProduct_self_eq_zero {z : ι → ℝ} (h : z ⬝ᵥ z = 0) : z = 0 :=
  dotProduct_self_eq_zero.mp h

/-- If `2 t β + t² c ≤ 0` for all real `t`, then `β = 0`. -/
lemma eq_zero_of_forall_quad {β c : ℝ} (h : ∀ t : ℝ, 2 * t * β + t ^ 2 * c ≤ 0) : β = 0 := by
  have hK : 0 < |c| + 1 := by positivity
  have h1 := h (β / (|c| + 1))
  have key : 2 * (β / (|c| + 1)) * β + (β / (|c| + 1)) ^ 2 * c
      = β ^ 2 * (2 * (|c| + 1) + c) / (|c| + 1) ^ 2 := by
    field_simp
  rw [key] at h1
  have hpos : 0 < 2 * (|c| + 1) + c := by have := neg_abs_le c; linarith
  have h2 : β ^ 2 * (2 * (|c| + 1) + c) ≤ 0 := by
    have hden : 0 < (|c| + 1) ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right h1 hden.le
    rwa [div_mul_cancel₀ _ hden.ne', zero_mul] at this
  have hb2 : β ^ 2 = 0 := by nlinarith [sq_nonneg β]
  exact pow_eq_zero_iff two_ne_zero |>.mp hb2

/-! ### Stationarity of maximizing orthonormal pairs -/

section Stationary

variable {A : Matrix ι ι ℝ} {u v : ι → ℝ}

/-- **Stationarity.** If `u, v` maximizes `xᵀAx + yᵀAy` and `z ⊥ u, v`, then `z ⊥ Au`. -/
theorem stationary (hA : ∀ i j, A j i = A i j) (h : IsOrthonormalPair u v)
    (hmax : ∀ x y, IsOrthonormalPair x y → fanValue A x y ≤ fanValue A u v) {z : ι → ℝ}
    (hzu : z ⬝ᵥ u = 0) (hzv : z ⬝ᵥ v = 0) : z ⬝ᵥ (A *ᵥ u) = 0 := by
  set n := z ⬝ᵥ z with hn_def
  have hn0 : 0 ≤ n := dotProduct_self_nonneg' z
  refine eq_zero_of_forall_quad (c := z ⬝ᵥ (A *ᵥ z) - u ⬝ᵥ (A *ᵥ u) * n) fun t => ?_
  -- the unit vector `x = (u + t z) / √(1 + t² n)`
  have hpos : 0 < 1 + t ^ 2 * n := by positivity
  set s := 1 / √(1 + t ^ 2 * n) with hs_def
  have hs2 : s ^ 2 = 1 / (1 + t ^ 2 * n) := by
    rw [hs_def, div_pow, Real.sq_sqrt hpos.le, one_pow]
  set x : ι → ℝ := s • u + (s * t) • z with hx_def
  have hux : u ⬝ᵥ z = 0 := by rw [dotProduct_comm]; exact hzu
  have hxx : x ⬝ᵥ x = 1 := by
    simp only [hx_def, dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct,
      smul_eq_mul, h.norm_left, hux, hzu, ← hn_def]
    have : s ^ 2 * (1 + t ^ 2 * n) = 1 := by rw [hs2]; field_simp
    linear_combination this
  have hxv : x ⬝ᵥ v = 0 := by
    simp only [hx_def, add_dotProduct, smul_dotProduct, smul_eq_mul, h.orth, hzv]
    ring
  have hle := hmax x v ⟨hxx, h.norm_right, hxv⟩
  simp only [fanValue] at hle
  have hq : x ⬝ᵥ (A *ᵥ x) = s ^ 2 * (u ⬝ᵥ (A *ᵥ u) + 2 * t * (z ⬝ᵥ (A *ᵥ u))
      + t ^ 2 * (z ⬝ᵥ (A *ᵥ z))) := by
    rw [hx_def, quad_add_smul hA]
    ring
  rw [hq, hs2] at hle
  have hle' : u ⬝ᵥ (A *ᵥ u) + 2 * t * (z ⬝ᵥ (A *ᵥ u)) + t ^ 2 * (z ⬝ᵥ (A *ᵥ z))
      ≤ u ⬝ᵥ (A *ᵥ u) * (1 + t ^ 2 * n) := by
    have := mul_le_mul_of_nonneg_left (by linarith : 1 / (1 + t ^ 2 * n) *
      (u ⬝ᵥ (A *ᵥ u) + 2 * t * (z ⬝ᵥ (A *ᵥ u)) + t ^ 2 * (z ⬝ᵥ (A *ᵥ z))) ≤ u ⬝ᵥ (A *ᵥ u))
      hpos.le
    rw [← mul_assoc, mul_one_div_cancel hpos.ne', one_mul] at this
    linarith
  nlinarith [hle']

/-- **Invariance.** A maximizing orthonormal pair spans an `A`-invariant plane:
`Au = ⟨u, Au⟩ u + ⟨v, Au⟩ v`. -/
theorem mulVec_eq_of_isMax (hA : ∀ i j, A j i = A i j) (h : IsOrthonormalPair u v)
    (hmax : ∀ x y, IsOrthonormalPair x y → fanValue A x y ≤ fanValue A u v) :
    A *ᵥ u = (u ⬝ᵥ (A *ᵥ u)) • u + (v ⬝ᵥ (A *ᵥ u)) • v := by
  set r : ι → ℝ := A *ᵥ u - (u ⬝ᵥ (A *ᵥ u)) • u - (v ⬝ᵥ (A *ᵥ u)) • v with hr_def
  have hlin : ∀ y : ι → ℝ, r ⬝ᵥ y = (A *ᵥ u) ⬝ᵥ y - (u ⬝ᵥ (A *ᵥ u)) * (u ⬝ᵥ y)
      - (v ⬝ᵥ (A *ᵥ u)) * (v ⬝ᵥ y) := by
    intro y
    simp only [hr_def, sub_dotProduct, smul_dotProduct, smul_eq_mul]
  have hru : r ⬝ᵥ u = 0 := by
    rw [hlin, h.norm_left, dotProduct_comm v u, h.orth, dotProduct_comm (A *ᵥ u) u]; ring
  have hrv : r ⬝ᵥ v = 0 := by
    rw [hlin, h.norm_right, h.orth, dotProduct_comm (A *ᵥ u) v]; ring
  have hst := stationary hA h hmax hru hrv
  have hrr : r ⬝ᵥ r = 0 := by
    have e : r ⬝ᵥ r = r ⬝ᵥ (A *ᵥ u) - (u ⬝ᵥ (A *ᵥ u)) * (r ⬝ᵥ u)
        - (v ⬝ᵥ (A *ᵥ u)) * (r ⬝ᵥ v) := by
      rw [dotProduct_comm r (A *ᵥ u), dotProduct_comm r u, dotProduct_comm r v]
      exact hlin r
    rw [e, hst, hru, hrv]; ring
  have := eq_zero_of_dotProduct_self_eq_zero hrr
  rw [hr_def, sub_sub, sub_eq_zero] at this
  exact this

/-- The same for `v`. -/
theorem mulVec_eq_of_isMax' (hA : ∀ i j, A j i = A i j) (h : IsOrthonormalPair u v)
    (hmax : ∀ x y, IsOrthonormalPair x y → fanValue A x y ≤ fanValue A u v) :
    A *ᵥ v = (u ⬝ᵥ (A *ᵥ v)) • u + (v ⬝ᵥ (A *ᵥ v)) • v := by
  have hmax' : ∀ x y, IsOrthonormalPair x y → fanValue A x y ≤ fanValue A v u := fun x y hxy =>
    (fanValue_symm A v u) ▸ hmax x y hxy
  exact (mulVec_eq_of_isMax hA h.symm hmax').trans (add_comm _ _)

end Stationary

/-! ### Fan's maximum principle -/

section Fan

variable [DecidableEq ι] {A : Matrix ι ι ℝ}

/-- The `k`-th eigenvector of a symmetric matrix (the `k`-th column of the eigenvector matrix). -/
noncomputable def eigenvector (hA : A.IsHermitian) (k : ι) : ι → ℝ :=
  fun i => (hA.eigenvectorUnitary : Matrix ι ι ℝ) i k

lemma eigenvector_dotProduct (hA : A.IsHermitian) (k l : ι) :
    eigenvector hA k ⬝ᵥ eigenvector hA l = if k = l then 1 else 0 := by
  have h := Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2
  have := congrFun (congrFun h k) l
  simp only [Matrix.mul_apply, Matrix.star_apply, star_trivial, Matrix.one_apply] at this
  rw [← this]
  simp only [dotProduct, eigenvector]

lemma sum_eigenvector_mul (hA : A.IsHermitian) (i j : ι) :
    ∑ k, eigenvector hA k i * eigenvector hA k j = if i = j then 1 else 0 := by
  have h := Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
  have := congrFun (congrFun h i) j
  simp only [Matrix.mul_apply, Matrix.star_apply, star_trivial, Matrix.one_apply] at this
  rw [← this]
  simp only [eigenvector]

lemma mulVec_eigenvector (hA : A.IsHermitian) (k : ι) :
    A *ᵥ eigenvector hA k = hA.eigenvalues k • eigenvector hA k := by
  have h := hA.mulVec_eigenvectorBasis k
  ext i
  have hi := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢
  simp only [eigenvector, Matrix.IsHermitian.eigenvectorUnitary_apply]
  exact hi

/-- Expansion in the eigenbasis. -/
lemma eq_sum_eigenvector (hA : A.IsHermitian) (x : ι → ℝ) (i : ι) :
    x i = ∑ k, (eigenvector hA k ⬝ᵥ x) * eigenvector hA k i := by
  have : ∑ k, (eigenvector hA k ⬝ᵥ x) * eigenvector hA k i
      = ∑ j, x j * ∑ k, eigenvector hA k j * eigenvector hA k i := by
    simp only [dotProduct, sum_mul, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun j _ => sum_congr rfl fun k _ => by ring
  rw [this]
  simp only [sum_eigenvector_mul, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true]

/-- Parseval's identity. -/
lemma sum_eigenvector_dotProduct_mul (hA : A.IsHermitian) (x y : ι → ℝ) :
    ∑ k, (eigenvector hA k ⬝ᵥ x) * (eigenvector hA k ⬝ᵥ y) = x ⬝ᵥ y := by
  calc ∑ k, (eigenvector hA k ⬝ᵥ x) * (eigenvector hA k ⬝ᵥ y)
      = ∑ k, ∑ i, ∑ j, (eigenvector hA k i * x i) * (eigenvector hA k j * y j) := by
        refine sum_congr rfl fun k _ => ?_
        rw [dotProduct, dotProduct, sum_mul_sum]
    _ = ∑ i, ∑ j, ∑ k, (eigenvector hA k i * x i) * (eigenvector hA k j * y j) := by
        rw [sum_comm]
        refine sum_congr rfl fun i _ => ?_
        rw [sum_comm]
    _ = ∑ i, ∑ j, x i * y j * (∑ k, eigenvector hA k i * eigenvector hA k j) := by
        refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
        rw [mul_sum]
        exact sum_congr rfl fun k _ => by ring
    _ = ∑ i, x i * y i := by
        refine sum_congr rfl fun i _ => ?_
        simp only [sum_eigenvector_mul, mul_ite, mul_one, mul_zero]
        simp
    _ = x ⬝ᵥ y := rfl

/-- `xᵀAx = ∑ₖ λₖ ⟨eₖ, x⟩²`. -/
lemma dotProduct_mulVec_eq_sum_eigenvalues (hA : A.IsHermitian) (x : ι → ℝ) :
    x ⬝ᵥ (A *ᵥ x) = ∑ k, hA.eigenvalues k * (eigenvector hA k ⬝ᵥ x) ^ 2 := by
  have hx : x = ∑ k, (eigenvector hA k ⬝ᵥ x) • eigenvector hA k := by
    ext i
    rw [eq_sum_eigenvector hA x i, Finset.sum_apply]
    simp
  have hAx : A *ᵥ x = ∑ k, (eigenvector hA k ⬝ᵥ x) • (hA.eigenvalues k • eigenvector hA k) := by
    conv_lhs => rw [hx]
    rw [mulVec_sum]
    simp only [mulVec_smul, mulVec_eigenvector]
  rw [hAx, dotProduct_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [dotProduct_smul, dotProduct_smul, dotProduct_comm, smul_eq_mul, smul_eq_mul]
  ring

/-- **Fan's inequality** for two vectors: `uᵀAu + vᵀAv ≤ λ_a + λ_b` for the two largest
eigenvalues `λ_a ≥ λ_b`. -/
theorem fanValue_le_top_two (hA : A.IsHermitian) {u v : ι → ℝ} (huv : IsOrthonormalPair u v)
    {a b : ι} (ha : ∀ j, hA.eigenvalues j ≤ hA.eigenvalues a)
    (hb : ∀ j, j ≠ a → hA.eigenvalues j ≤ hA.eigenvalues b) :
    fanValue A u v ≤ hA.eigenvalues a + hA.eigenvalues b := by
  have hsum : fanValue A u v = ∑ k, hA.eigenvalues k *
      ((eigenvector hA k ⬝ᵥ u) ^ 2 + (eigenvector hA k ⬝ᵥ v) ^ 2) := by
    simp only [fanValue, dotProduct_mulVec_eq_sum_eigenvalues hA, mul_add, sum_add_distrib]
  rw [hsum]
  have h1 : ∀ k, (eigenvector hA k ⬝ᵥ u) ^ 2 + (eigenvector hA k ⬝ᵥ v) ^ 2 ≤ 1 := by
    intro k
    have := bessel huv (eigenvector hA k)
    rw [dotProduct_comm u, dotProduct_comm v, eigenvector_dotProduct] at this
    simpa using this
  have h2 : ∑ k, ((eigenvector hA k ⬝ᵥ u) ^ 2 + (eigenvector hA k ⬝ᵥ v) ^ 2) = 2 := by
    rw [sum_add_distrib]
    have e1 := sum_eigenvector_dotProduct_mul hA u u
    have e2 := sum_eigenvector_dotProduct_mul hA v v
    simp only [sq]
    rw [e1, e2, huv.norm_left, huv.norm_right]
    norm_num
  exact sum_mul_le_top_two _ _ (fun k => by positivity) h1 h2 ha hb

/-- The eigenvectors attain Fan's bound. -/
theorem fanValue_eigenvector (hA : A.IsHermitian) {a b : ι} (hab : a ≠ b) :
    IsOrthonormalPair (eigenvector hA a) (eigenvector hA b) ∧
      fanValue A (eigenvector hA a) (eigenvector hA b)
        = hA.eigenvalues a + hA.eigenvalues b := by
  refine ⟨⟨by simp [eigenvector_dotProduct], by simp [eigenvector_dotProduct],
    by simp [eigenvector_dotProduct, hab]⟩, ?_⟩
  simp only [fanValue, mulVec_eigenvector, dotProduct_smul, eigenvector_dotProduct, ite_true,
    smul_eq_mul, mul_one]

/-- **Fan's maximum principle** for `π₂`: `π₂(A)` is the sum of the two largest eigenvalues. -/
theorem sumTopTwo_eq_top_two (hA : A.IsHermitian) {a b : ι} (hab : a ≠ b)
    (ha : ∀ j, hA.eigenvalues j ≤ hA.eigenvalues a)
    (hb : ∀ j, j ≠ a → hA.eigenvalues j ≤ hA.eigenvalues b) :
    π₂ A = hA.eigenvalues a + hA.eigenvalues b := by
  obtain ⟨hon, hval⟩ := fanValue_eigenvector hA hab
  apply le_antisymm
  · exact sumTopTwo_le ⟨_, _, _, hon, rfl⟩ fun u v huv => fanValue_le_top_two hA huv ha hb
  · rw [← hval]; exact fanValue_le_sumTopTwo A hon

/-- If every sum of two eigenvalues (with distinct indices) is at most `c`, then `π₂ A ≤ c`. -/
theorem sumTopTwo_le_of_forall_add_le (hA : A.IsHermitian) (h2 : 1 < Fintype.card ι) {c : ℝ}
    (h : ∀ i j, i ≠ j → hA.eigenvalues i + hA.eigenvalues j ≤ c) : π₂ A ≤ c := by
  obtain ⟨a, b, hab, ha, hb⟩ := exists_top_two hA.eigenvalues h2
  rw [sumTopTwo_eq_top_two hA hab ha hb]
  exact h a b hab

/-- Every sum of two eigenvalues with distinct indices is at most `π₂ A`. -/
theorem add_le_sumTopTwo (hA : A.IsHermitian) {i j : ι} (hij : i ≠ j) :
    hA.eigenvalues i + hA.eigenvalues j ≤ π₂ A := by
  obtain ⟨hon, hval⟩ := fanValue_eigenvector hA hij
  rw [← hval]
  exact fanValue_le_sumTopTwo A hon

/-- **Fan's maximum principle** in terms of Mathlib's list `eigenvalues₀` of the eigenvalues in
decreasing order: `π₂(A) = λ₁(A) + λ₂(A)`. -/
theorem sumTopTwo_eq_eigenvalues₀ (hA : A.IsHermitian) (h2 : 2 ≤ Fintype.card ι) :
    π₂ A = hA.eigenvalues₀ ⟨0, by omega⟩ + hA.eigenvalues₀ ⟨1, by omega⟩ := by
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι)) with he
  have hev : ∀ i, hA.eigenvalues i = hA.eigenvalues₀ (e.symm i) := fun i => rfl
  set k0 : Fin (Fintype.card ι) := ⟨0, by omega⟩ with hk0
  set k1 : Fin (Fintype.card ι) := ⟨1, by omega⟩ with hk1
  have hk01 : k0 ≠ k1 := by simp [hk0, hk1, Fin.ext_iff]
  have hab : e k0 ≠ e k1 := fun h => hk01 (e.injective h)
  have ha : ∀ j, hA.eigenvalues j ≤ hA.eigenvalues (e k0) := by
    intro j
    rw [hev, hev, e.symm_apply_apply]
    exact hA.eigenvalues₀_antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
  have hb : ∀ j, j ≠ e k0 → hA.eigenvalues j ≤ hA.eigenvalues (e k1) := by
    intro j hj
    rw [hev, hev, e.symm_apply_apply]
    apply hA.eigenvalues₀_antitone
    have h1 : e.symm j ≠ k0 := fun h => hj (by rw [← h, e.apply_symm_apply])
    have h2 : (e.symm j).val ≠ 0 := fun h => h1 (Fin.ext h)
    change (1 : ℕ) ≤ (e.symm j).val
    omega
  rw [sumTopTwo_eq_top_two hA hab ha hb, hev, hev, e.symm_apply_apply, e.symm_apply_apply]

end Fan

/-- The supremum defining `π₂(A)` is attained, for symmetric `A` and `|ι| ≥ 2`. -/
theorem exists_fanValue_eq_sumTopTwo {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (h2 : 1 < Fintype.card ι) : ∃ u v, IsOrthonormalPair u v ∧ fanValue A u v = π₂ A := by
  classical
  obtain ⟨a, b, hab, ha, hb⟩ := exists_top_two hA.eigenvalues h2
  obtain ⟨hon, hval⟩ := fanValue_eigenvector hA hab
  exact ⟨_, _, hon, by rw [hval, sumTopTwo_eq_top_two hA hab ha hb]⟩

end Grunbaum
