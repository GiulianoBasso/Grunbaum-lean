/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import Grunbaum.KMMP
import Grunbaum.LemmaB

/-!
# Lemma C: cloning

> **Lemma C** (Cloning [KMMP]). Let `m > n`, let `(S, D)` be a maximizer of `Π(n, m)` with `D`
> positive definite, and let `u₁, …, u_m ∈ ℝⁿ` be as in Lemma B. Let `C ⊂ {1, …, m}` be such that
> `⟨uᵢ, uⱼ⟩ ≥ 0` for all `i, j ∈ C`. Let `c₁, …, c_m ≥ 0` with `cᵢ = 1` for `i ∉ C` and
> `∑_{i ∈ C} cᵢ uᵢ uᵢᵗ = ∑_{i ∈ C} uᵢ uᵢᵗ`. Then `D' := Diag(c₁d₁, …, c_m d_m)` lies in `𝒟_m`,
> and `(S, D')` is again a maximizer of `Π(n, m)`.

We prove Lemma C for `n = 2`, as a translation of Claim 2.4 of Kumar, Mohar, Mojallal and
Pragada (`Grunbaum.KMMP.IsMaximizingPair.clone`). As in `Grunbaum.LemmaB`, the vectors
`xᵢ = (uᵢ, vᵢ) ∈ ℝ²` (the `uᵢ` of the errata) are the rows of the matrix
`U = [u v] = Grunbaum.pairMatrix u v`, where `u, v` is an orthonormal pair with
`uᵀMu + vᵀMv = π₂(M)` for `M = √D S √D`.

* By Lemma B(b), (c) and the formula of Chalmers and Lewicki, `(U, (√dᵢ)ᵢ)` is a maximizing pair
  in the sense of KMMP (`Grunbaum.isMaximizingPair_pairMatrix`): `σ(U, √d) = π₂(M) = Π(2, m)`.
* Claim 2.4 of KMMP gives the maximizing pair `(Ũ, w̃)` with rows `√cᵢ xᵢ` and weights
  `√(cᵢ dᵢ)`. Its columns form an orthonormal pair `ũ, ṽ` with
  `ũᵀM'ũ + ṽᵀM'ṽ = σ(Ũ, w̃) = Π(2, m)` for `M' = √D' S √D'`, again by Lemma B(b).
-/

open Finset Matrix ProjectionConstants

namespace Grunbaum

variable {ι : Type*}

/-- The matrix `U = [u v] ∈ ℝ^{ι×2}`, whose rows are the vectors `xᵢ = (uᵢ, vᵢ) ∈ ℝ²`. -/
def pairMatrix (u v : ι → ℝ) : Matrix ι (Fin 2) ℝ := of fun i => ![u i, v i]

lemma pairMatrix_apply (u v : ι → ℝ) (i : ι) : pairMatrix u v i = ![u i, v i] := rfl

lemma pairMatrix_dotProduct (u v : ι → ℝ) (i j : ι) :
    pairMatrix u v i ⬝ᵥ pairMatrix u v j = u i * u j + v i * v j := by
  simp [pairMatrix, dotProduct, Fin.sum_univ_two]

lemma transpose_pairMatrix_mul [Fintype ι] {u v : ι → ℝ} (huv : IsOrthonormalPair u v) :
    (pairMatrix u v)ᵀ * pairMatrix u v = 1 := by
  ext a b
  fin_cases a <;> fin_cases b
  · simpa [pairMatrix, mul_apply, dotProduct] using huv.norm_left
  · simpa [pairMatrix, mul_apply, dotProduct] using huv.orth
  · simpa [pairMatrix, mul_apply, dotProduct, mul_comm] using huv.orth
  · simpa [pairMatrix, mul_apply, dotProduct] using huv.norm_right

variable {m : ℕ} {S : Matrix (Fin m) (Fin m) ℝ} {w u v : Fin m → ℝ}

/-- A maximizer `(S, D)` of `Π(2, m)` with `D` positive definite, together with a maximizing
orthonormal pair `u, v` for `M = √D S √D`, gives the maximizing pair `(U, √D)` of KMMP. -/
theorem isMaximizingPair_pairMatrix (hmax : IsMaximizer S w) (hpos : ∀ i, 0 < w i)
    (hm : 2 < m) (huv : IsOrthonormalPair u v)
    (hval : fanValue (weightedMatrix S w) u v = π₂ (weightedMatrix S w)) :
    KMMP.IsMaximizingPair (pairMatrix u v) fun i => √(w i) := by
  refine ⟨transpose_pairMatrix_mul huv, isUnitWeight_sqrt hmax.isWeight, ?_⟩
  have hsign := hmax.mul_projPair_pos hpos (by simpa using hm) huv hval
  rw [maxRelProjConst_two_eq_supConfigs, ← hmax.sumTopTwo_eq,
    sumTopTwo_eq_sum_abs hmax.isSignMatrix hval hsign]
  simp only [KMMP.sigma, pairMatrix_dotProduct]

/-- **Lemma C** (Cloning [KMMP, Claim 2.4]) for `n = 2`. Let `(S, D)` be a maximizer of `Π(2, m)`
with `D` positive definite, `m > 2`, and let `xᵢ = (uᵢ, vᵢ)` for a maximizing orthonormal pair
`u, v` of `√D S √D`. Let `C` be such that `⟨xᵢ, xⱼ⟩ ≥ 0` for `i, j ∈ C`, and let `c ≥ 0` with
`cᵢ = 1` for `i ∉ C` and `∑_{i ∈ C} cᵢ xᵢ xᵢᵀ = ∑_{i ∈ C} xᵢ xᵢᵀ`. Then `(S, D')` with
`D' = Diag(cᵢ dᵢ)` is again a maximizer of `Π(2, m)` (in particular `D' ∈ 𝒟_m`). -/
theorem IsMaximizer.clone (hmax : IsMaximizer S w) (hpos : ∀ i, 0 < w i) (hm : 2 < m)
    (huv : IsOrthonormalPair u v)
    (hval : fanValue (weightedMatrix S w) u v = π₂ (weightedMatrix S w)) {C : Finset (Fin m)}
    (hC : ∀ i ∈ C, ∀ j ∈ C, 0 ≤ u i * u j + v i * v j) {c : Fin m → ℝ} (hc : ∀ i, 0 ≤ c i)
    (hc1 : ∀ i, i ∉ C → c i = 1)
    (hcC : ∑ i ∈ C, c i • vecMulVec ![u i, v i] ![u i, v i] =
      ∑ i ∈ C, vecMulVec ![u i, v i] ![u i, v i]) :
    IsMaximizer S fun i => c i * w i := by
  have hsign := hmax.mul_projPair_pos hpos (by simpa using hm) huv hval
  have hP := isMaximizingPair_pairMatrix hmax hpos hm huv hval
  have hQ := hP.clone two_pos (C := C) (fun i hi j hj => by
      rw [pairMatrix_dotProduct]; exact hC i hi j hj) hc hc1 hcC
  -- the cloned orthonormal pair
  set u' : Fin m → ℝ := fun i => √(c i) * u i with hu'
  set v' : Fin m → ℝ := fun i => √(c i) * v i with hv'
  have hsq : ∀ i, √(c i) * √(c i) = c i := fun i => Real.mul_self_sqrt (hc i)
  have hon : IsOrthonormalPair u' v' := by
    have h := hQ.transpose_mul_self
    refine ⟨?_, ?_, ?_⟩
    · have := congrFun (congrFun h 0) 0
      simpa [KMMP.cloneMatrix, pairMatrix, mul_apply, dotProduct, hu'] using this
    · have := congrFun (congrFun h 1) 1
      simpa [KMMP.cloneMatrix, pairMatrix, mul_apply, dotProduct, hv'] using this
    · have := congrFun (congrFun h 0) 1
      simpa [KMMP.cloneMatrix, pairMatrix, mul_apply, dotProduct, hu', hv'] using this
  -- the new weights
  have hw' : IsWeight fun i => c i * w i := by
    refine ⟨fun i => mul_nonneg (hc i) (hmax.isWeight.nonneg i), ?_⟩
    rw [← hQ.isUnitWeight.sum_sq]
    refine sum_congr rfl fun i _ => ?_
    simp only [KMMP.cloneWeight, mul_pow, Real.sq_sqrt (hc i),
      Real.sq_sqrt (hmax.isWeight.nonneg i)]
  refine isMaximizer_of_le hmax.isSignMatrix hw' ?_
  -- `Π(2, m) = σ(Ũ, w̃) = u'ᵀM'u' + v'ᵀM'v' ≤ π₂(M')`
  rw [← maxRelProjConst_two_eq_supConfigs, ← hQ.sigma_eq]
  refine le_trans (le_of_eq ?_) (fanValue_le_sumTopTwo _ hon)
  rw [fanValue_eq_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  have hd : KMMP.cloneMatrix (pairMatrix u v) c i ⬝ᵥ KMMP.cloneMatrix (pairMatrix u v) c j =
      √(c i) * √(c j) * (u i * u j + v i * v j) := by
    simp only [KMMP.cloneMatrix, pairMatrix, dotProduct, of_apply, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have habs : S i j * (u i * u j + v i * v j) = |u i * u j + v i * v j| := by
    simpa only [projPair_apply] using
      mul_eq_abs_of_pos hmax.isSignMatrix (P := projPair u v) (hsign i j)
  rw [hd, abs_mul, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)), ← habs]
  simp only [KMMP.cloneWeight, weightedMatrix_apply, hu', hv',
    Real.sqrt_mul (hc i), Real.sqrt_mul (hc j)]
  ring

end Grunbaum
