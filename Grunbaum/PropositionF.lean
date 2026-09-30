/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import Grunbaum.Maximizer
import Grunbaum.Polygon
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Roots

/-!
# The remaining computation: `Π(2, R₅) = 4/3`

By (R2) we may take `R₅ = 𝟙₅ + S(C₅) = J₅ - 2E` (`Grunbaum.R5`), where `E` is the adjacency matrix
of the cycle `0 - 1 - 2 - 3 - 4 - 0` (the errata labels the vertices by `1, …, 5`). The coherent
triples are the triples containing exactly one edge of `C₅`, namely `{0, 1, 3}`, `{1, 2, 4}`,
`{0, 2, 3}`, `{1, 3, 4}` and `{0, 2, 4}`.

> **Lemma E.** Let `D = Diag(d₁, …, d₅) ∈ 𝒟₅`. Then
> `det(x 𝟙₅ - √D R₅ √D) = x⁵ - x⁴ + 4τx² - 16δ`, where `δ := d₁d₂d₃d₄d₅` and
> `τ := ∑_{{i, j, k} coherent} dᵢ dⱼ dₖ`.

> **Proposition F.** `Π(2, R₅) = 4/3`. Moreover, `π₂(√D R₅ √D) = 4/3` only if `D` is singular.

*Proof of the errata.* For `D = ⅓ Diag(1, 1, 0, 1, 0)`, supported on the coherent triple
`{1, 2, 4}`, Lemma E gives the characteristic polynomial `x² (x - 2/3)² (x + 1/3)`, so
`Π(2, R₅) ≥ 4/3`. Conversely, let `x₁ ≥ ⋯ ≥ x₅` be the eigenvalues of `M = √D R₅ √D`. Since
`|M| ≤ √D J₅ √D`, `x₁ ≤ 1`. If `x₂ ≤ 0`, then `π₂(M) ≤ 1`. Otherwise put `s = x₁ + x₂ > 0` and
`q = x₁x₂ > 0`. Factoring the characteristic polynomial as `(x² - sx + q)(x³ + ax² + bx + e)` and
comparing coefficients gives `a - s = -1`, `b - sa + q = 0`, `qb - se = 0`, `qe = -16δ`. Hence
`b = s(s - 1) - q` and `q²b = -16sδ ≤ 0`, so `b ≤ 0` and `s(s - 1) ≤ q ≤ s²/4`, which gives
`s ≤ 4/3`. If `s = 4/3`, both inequalities are equalities, so `b = 0` and `δ = 0`.

In the formal proof we work with the characteristic polynomial `∏ (X - xᵢ)` of `M` (spectral
theorem, `Matrix.IsHermitian.charpoly_eq`), and read off the elementary symmetric functions of
its roots by evaluating at `0, ±1, ±2` (`Grunbaum.PropF.pair01`). The Vieta argument is
`Grunbaum.PropF.pair_bound`.

This file is adapted from `ProjectionConstants/Grunbaum/PropF/{Core,Main}.lean` of the library
*Projection constants in Lean*.
-/

open Matrix
open Polynomial (X C)

namespace Grunbaum

/-! ### Lemma E -/

/-- `τ = ∑ dᵢ dⱼ dₖ` over the coherent triples `{0,1,3}, {1,2,4}, {0,2,3}, {1,3,4}, {0,2,4}` of
`R₅`. -/
def tauR5 (d : Fin 5 → ℝ) : ℝ :=
  d 0 * d 1 * d 3 + d 1 * d 2 * d 4 + d 2 * d 3 * d 0 + d 3 * d 4 * d 1 + d 4 * d 0 * d 2

namespace PropF

/-- `diag(s) R₅ diag(s)`; for `s = (√d₀, …, √d₄)` this is `√D R₅ √D`. -/
def weightedR5 (s : Fin 5 → ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  of fun i j => s i * R5 i j * s j

/-- The matrix `x 𝟙 - diag(s) R₅ diag(s)`, written out explicitly. -/
theorem scalar_sub_weightedR5 (s : Fin 5 → ℝ) (x : ℝ) :
    scalar (Fin 5) x - weightedR5 s =
      !![x - s 0 * s 0, s 0 * s 1, -(s 0 * s 2), -(s 0 * s 3), s 0 * s 4;
         s 1 * s 0, x - s 1 * s 1, s 1 * s 2, -(s 1 * s 3), -(s 1 * s 4);
         -(s 2 * s 0), s 2 * s 1, x - s 2 * s 2, s 2 * s 3, -(s 2 * s 4);
         -(s 3 * s 0), -(s 3 * s 1), s 3 * s 2, x - s 3 * s 3, s 3 * s 4;
         s 4 * s 0, -(s 4 * s 1), -(s 4 * s 2), s 4 * s 3, x - s 4 * s 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weightedR5, R5, scalar_apply]

/-- `det(x 𝟙 - diag(s) R₅ diag(s)) = x⁵ - (∑ sᵢ²) x⁴ + 4τ x² - 16δ` with `dᵢ = sᵢ²`. -/
theorem det_scalar_sub_weightedR5 (s : Fin 5 → ℝ) (x : ℝ) :
    (scalar (Fin 5) x - weightedR5 s).det
      = x ^ 5 - (s 0 ^ 2 + s 1 ^ 2 + s 2 ^ 2 + s 3 ^ 2 + s 4 ^ 2) * x ^ 4
          + 4 * tauR5 (fun i => s i ^ 2) * x ^ 2 - 16 * (s 0 * s 1 * s 2 * s 3 * s 4) ^ 2 := by
  rw [scalar_sub_weightedR5]
  simp [det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, tauR5]
  ring

/-! ### The Vieta argument -/

/-- The Vieta argument for one pair `a, b` of roots of `x⁵ - x⁴ + 4τx² - 16δ` with remaining
roots `c, d, e`: then `a + b ≤ 4/3`, strictly if `δ > 0`. -/
theorem pair_bound (a b c d e δ : ℝ) (hδ : 0 ≤ δ)
    (H1 : a + b + c + d + e = 1)
    (H2 : a * b + a * c + a * d + a * e + b * c + b * d + b * e + c * d + c * e + d * e = 0)
    (H4 : a * b * c * d + a * b * c * e + a * b * d * e + a * c * d * e + b * c * d * e = 0)
    (H5 : a * b * c * d * e = 16 * δ) :
    a + b ≤ 4 / 3 ∧ (0 < δ → a + b < 4 / 3) := by
  -- the squares of the roots sum to `1`, so each root is at most `1`
  have hsq : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 = 1 := by
    linear_combination (a + b + c + d + e + 1) * H1 - 2 * H2
  have ha1 : a ≤ 1 := by
    nlinarith [sq_nonneg b, sq_nonneg c, sq_nonneg d, sq_nonneg e, sq_nonneg (a - 1)]
  have hb1 : b ≤ 1 := by
    nlinarith [sq_nonneg a, sq_nonneg c, sq_nonneg d, sq_nonneg e, sq_nonneg (b - 1)]
  rcases le_or_gt a 0 with ha | ha
  · exact ⟨by linarith, fun _ => by linarith⟩
  rcases le_or_gt b 0 with hb | hb
  · exact ⟨by linarith, fun _ => by linarith⟩
  -- now `s = a + b > 0` and `q = a b > 0`; write `B = cd + ce + de`
  have hs : 0 < a + b := by linarith
  have hq2 : 0 < (a * b) ^ 2 := pow_pos (mul_pos ha hb) 2
  have hB : c * d + c * e + d * e = -(a * b) - (a + b) * (1 - (a + b)) := by
    linear_combination H2 - (a + b) * H1
  have key : (a * b) ^ 2 * (c * d + c * e + d * e) = -16 * (a + b) * δ := by
    linear_combination (a * b) * H4 - (a + b) * H5
  have hamgm : 4 * (a * b) ≤ (a + b) ^ 2 := by nlinarith [sq_nonneg (a - b)]
  refine ⟨?_, fun hδpos => ?_⟩
  · -- `q² B = -16 s δ ≤ 0`, hence `B ≤ 0`, hence `s(s-1) ≤ q ≤ s²/4`
    have hBle : c * d + c * e + d * e ≤ 0 := by
      by_contra hcon
      push Not at hcon
      have h1 : 0 < (a * b) ^ 2 * (c * d + c * e + d * e) := mul_pos hq2 hcon
      nlinarith [mul_nonneg hs.le hδ]
    have h34 : (a + b) * (3 * (a + b) - 4) ≤ 0 := by nlinarith [hB, hBle, hamgm]
    by_contra hcon
    push Not at hcon
    have : 0 < (a + b) * (3 * (a + b) - 4) := mul_pos hs (by linarith)
    linarith
  · -- if `δ > 0`, then `B < 0` and all inequalities are strict
    have hBlt : c * d + c * e + d * e < 0 := by
      by_contra hcon
      push Not at hcon
      have h1 : 0 ≤ (a * b) ^ 2 * (c * d + c * e + d * e) := mul_nonneg hq2.le hcon
      nlinarith [mul_pos hs hδpos]
    have h34 : (a + b) * (3 * (a + b) - 4) < 0 := by nlinarith [hB, hBlt, hamgm]
    by_contra hcon
    push Not at hcon
    have : 0 ≤ (a + b) * (3 * (a + b) - 4) := mul_nonneg hs.le (by linarith)
    linarith

/-- Vieta for the pair `μ 0, μ 1`: the coefficients are read off by evaluating at `0, ±1, ±2`. -/
theorem pair01 (μ : Fin 5 → ℝ) (t δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ x : ℝ, ∏ i, (x - μ i) = x ^ 5 - x ^ 4 + 4 * t * x ^ 2 - 16 * δ) :
    μ 0 + μ 1 ≤ 4 / 3 ∧ (0 < δ → μ 0 + μ 1 < 4 / 3) := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h (-1)
  have h3 := h 2
  have h4 := h (-2)
  simp only [Fin.prod_univ_five] at h0 h1 h2 h3 h4
  apply pair_bound (μ 0) (μ 1) (μ 2) (μ 3) (μ 4) δ hδ
  · linear_combination (-1 / 24 : ℝ) * (h3 + h4 - 4 * h1 - 4 * h2 + 6 * h0)
  · linear_combination (h3 - h4 - 2 * (h1 - h2)) / 12
  · linear_combination (8 * (h1 - h2) - (h3 - h4)) / 12
  · linear_combination (-1 : ℝ) * h0

/-- Any two distinct indices can be moved to `0, 1` by a permutation. -/
theorem exists_perm (i j : Fin 5) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin 5), σ 0 = i ∧ σ 1 = j := by
  have h01 : (0 : Fin 5) ≠ 1 := by decide
  have hj : Equiv.swap 0 i j ≠ 0 := by
    intro h
    apply hij
    have := congrArg (Equiv.swap 0 i) h
    rw [Equiv.swap_apply_self, Equiv.swap_apply_left] at this
    exact this.symm
  refine ⟨Equiv.swap 0 i * Equiv.swap 1 (Equiv.swap 0 i j), ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h01 hj.symm, Equiv.swap_apply_left]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_self]

/-- Vieta for an arbitrary pair of roots. -/
theorem pair_all (μ : Fin 5 → ℝ) (t δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ x : ℝ, ∏ i, (x - μ i) = x ^ 5 - x ^ 4 + 4 * t * x ^ 2 - 16 * δ)
    (i j : Fin 5) (hij : i ≠ j) :
    μ i + μ j ≤ 4 / 3 ∧ (0 < δ → μ i + μ j < 4 / 3) := by
  obtain ⟨σ, hσ0, hσ1⟩ := exists_perm i j hij
  have h' : ∀ x : ℝ, ∏ k, (x - (μ ∘ σ) k) = x ^ 5 - x ^ 4 + 4 * t * x ^ 2 - 16 * δ := by
    intro x
    rw [← h x]
    exact Equiv.prod_comp σ (fun k => x - μ k)
  have := pair01 (μ ∘ σ) t δ hδ h'
  simp only [Function.comp_apply, hσ0, hσ1] at this
  exact this

end PropF

/-- `√D R₅ √D = diag(√d) R₅ diag(√d)`. -/
lemma weightedMatrix_R5 (d : Fin 5 → ℝ) :
    weightedMatrix R5 d = PropF.weightedR5 fun i => √(d i) :=
  rfl

/-- **Lemma E.** For `D ∈ 𝒟₅`, `det(x 𝟙₅ - √D R₅ √D) = x⁵ - x⁴ + 4τx² - 16δ`, where
`δ = d₁ ⋯ d₅` and `τ = ∑_{{i, j, k} coherent} dᵢ dⱼ dₖ`. -/
theorem charpoly_weightedMatrix_R5 {d : Fin 5 → ℝ} (hd : IsWeight d) :
    (weightedMatrix R5 d).charpoly =
      X ^ 5 - X ^ 4 + C (4 * tauR5 d) * X ^ 2 - C (16 * ∏ i, d i) := by
  have hsq : ∀ i, √(d i) ^ 2 = d i := fun i => Real.sq_sqrt (hd.nonneg i)
  have hsum : d 0 + d 1 + d 2 + d 3 + d 4 = 1 := by
    simpa [Fin.sum_univ_five] using hd.sum_eq
  apply Polynomial.funext
  intro x
  rw [Matrix.eval_charpoly, weightedMatrix_R5, PropF.det_scalar_sub_weightedR5]
  simp only [hsq, mul_pow, hsum, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Fin.prod_univ_five]
  ring

/-! ### Proposition F -/

/-- Any two eigenvalues of `√D R₅ √D` sum to at most `4/3`, strictly if `D` is positive
definite. -/
theorem eigenvalues_add_le_R5 {d : Fin 5 → ℝ} (hd : IsWeight d)
    (hA : (weightedMatrix R5 d).IsHermitian) (i j : Fin 5) (hij : i ≠ j) :
    hA.eigenvalues i + hA.eigenvalues j ≤ 4 / 3 ∧
      ((∀ k, 0 < d k) → hA.eigenvalues i + hA.eigenvalues j < 4 / 3) := by
  have hc : (weightedMatrix R5 d).charpoly = ∏ k, (X - C (hA.eigenvalues k)) := by
    rw [hA.charpoly_eq]
    simp
  have h : ∀ x : ℝ, ∏ k, (x - hA.eigenvalues k) =
      x ^ 5 - x ^ 4 + 4 * tauR5 d * x ^ 2 - 16 * ∏ k, d k := by
    intro x
    have := congrArg (Polynomial.eval x) hc
    rw [charpoly_weightedMatrix_R5 hd, Polynomial.eval_prod] at this
    simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at this
    linear_combination -this
  have hδ : 0 ≤ ∏ k, d k := Finset.prod_nonneg fun k _ => hd.nonneg k
  have H := PropF.pair_all _ (tauR5 d) (∏ k, d k) hδ h i j hij
  exact ⟨H.1, fun hk => H.2 (Finset.prod_pos fun k _ => hk k)⟩

/-- `π₂(√D R₅ √D) ≤ 4/3` for all `D ∈ 𝒟₅`. -/
theorem sumTopTwo_weightedMatrix_R5_le {d : Fin 5 → ℝ} (hd : IsWeight d) :
    π₂ (weightedMatrix R5 d) ≤ 4 / 3 := by
  have hA := isHermitian_weightedMatrix isSignMatrix_R5 d
  exact sumTopTwo_le_of_forall_add_le hA (by simp) fun i j hij =>
    (eigenvalues_add_le_R5 hd hA i j hij).1

/-- **Proposition F, strictness**: `π₂(√D R₅ √D) < 4/3` if `D` is positive definite. -/
theorem sumTopTwo_weightedMatrix_R5_lt {d : Fin 5 → ℝ} (hd : IsWeight d) (hpos : ∀ k, 0 < d k) :
    π₂ (weightedMatrix R5 d) < 4 / 3 := by
  classical
  have hA := isHermitian_weightedMatrix isSignMatrix_R5 d
  obtain ⟨a, b, hab, ha, hb⟩ := exists_top_two hA.eigenvalues (by simp)
  rw [sumTopTwo_eq_top_two hA hab ha hb]
  exact (eigenvalues_add_le_R5 hd hA a b hab).2 hpos

/-- The weights `D₀ = ⅓ Diag(1, 1, 0, 1, 0)`, supported on the coherent triple `{0, 1, 3}`. -/
noncomputable def weightR5 : Fin 5 → ℝ := ![1 / 3, 1 / 3, 0, 1 / 3, 0]

lemma isWeight_weightR5 : IsWeight weightR5 := by
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> norm_num [weightR5]
  · norm_num [weightR5, Fin.sum_univ_five]

/-- For `D₀ = ⅓ Diag(1, 1, 0, 1, 0)`, `χ(√D₀ R₅ √D₀) = X² (X - 2/3)² (X + 1/3)`, so
`π₂(√D₀ R₅ √D₀) ≥ 4/3`. -/
theorem le_sumTopTwo_weightedMatrix_R5 : 4 / 3 ≤ π₂ (weightedMatrix R5 weightR5) := by
  have hA := isHermitian_weightedMatrix isSignMatrix_R5 weightR5
  have hchar : (weightedMatrix R5 weightR5).charpoly =
      X ^ 2 * (X - C (2 / 3)) ^ 2 * (X - C (-1 / 3)) := by
    have h1 : tauR5 weightR5 = 1 / 27 := by
      simp only [tauR5, weightR5]
      norm_num
    have h2 : ∏ i, weightR5 i = 0 := by
      simp [weightR5, Fin.prod_univ_five]
    rw [charpoly_weightedMatrix_R5 isWeight_weightR5, h1, h2]
    apply Polynomial.funext
    intro x
    simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    ring
  have hμ : (weightedMatrix R5 weightR5).charpoly = ∏ k, (X - C (hA.eigenvalues k)) := by
    rw [hA.charpoly_eq]
    simp
  have hne1 : (X ^ 2 * (X - C (2 / 3)) ^ 2 : Polynomial ℝ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _))
  have hne2 : (X ^ 2 * (X - C (2 / 3)) ^ 2 * (X - C (-1 / 3)) : Polynomial ℝ) ≠ 0 :=
    mul_ne_zero hne1 (Polynomial.X_sub_C_ne_zero _)
  -- the roots of `∏ (X - μᵢ)` are the `μᵢ`, and `2/3` is a double root
  have hroots : (weightedMatrix R5 weightR5).charpoly.roots =
      Finset.univ.val.map hA.eigenvalues := by
    rw [hμ, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have hcount : Multiset.count (2 / 3 : ℝ) (Finset.univ.val.map hA.eigenvalues) = 2 := by
    rw [← hroots, hchar, Polynomial.roots_mul hne2, Polynomial.roots_mul hne1]
    norm_num [Polynomial.roots_pow, Polynomial.roots_X, Polynomial.roots_X_sub_C,
      Multiset.count_singleton]
  rw [Multiset.count_map, ← Finset.filter_val, Finset.card_val] at hcount
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by rw [hcount]; norm_num)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  have := add_le_sumTopTwo hA hab
  rw [← ha, ← hb] at this
  linarith

/-- **Proposition F.** `Π(2, R₅) = 4/3`. -/
theorem supWeights_R5 : supWeights R5 = 4 / 3 :=
  le_antisymm (supWeights_le (by norm_num) fun _ hd => sumTopTwo_weightedMatrix_R5_le hd)
    (le_sumTopTwo_weightedMatrix_R5.trans (sumTopTwo_le_supWeights isSignMatrix_R5
      isWeight_weightR5))

end Grunbaum
