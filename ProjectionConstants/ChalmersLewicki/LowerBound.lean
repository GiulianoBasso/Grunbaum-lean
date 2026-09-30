/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.ChalmersLewicki.UpperBound
import ProjectionConstants.Foundations.Commute

/-!
# The Chalmers–Lewicki formula: the lower bound

* `re_trace_le_relProjConst` (**trace duality in `ℓ∞`**): if `P₀² = P₀`, `A P₀ = P₀ A` and the
  columns of `A` satisfy `|Aⱼᵢ| ≤ αᵢ` with `∑ αᵢ ≤ 1`, then `Re tr(A P₀) ≤ λ(range P₀, ℓ∞)`.
* `exists_le_relProjConst` : for weights `t > 0` and `P ∈ 𝒫ₘ` there is an `m`-dimensional
  `Y ⊆ ℓ∞^ι` with `∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| ≤ λ(Y, ℓ∞^ι)`.

Proof of the second statement: let `Q` maximize `∑ᵢⱼ tᵢ tⱼ |Qᵢⱼ|` over `𝒫ₘ` (compactness) and let
`S = sgn(Q)` be its sign pattern. Then `Q` also maximizes `Re tr(B ·)` for `B = D S D`,
`D = diag(t)`, hence `B Q = Q B` (`commute_of_isMaxOn`). The subspace `Y = D⁻¹ range(Q)` and the
certificate `A = S D²` satisfy the hypotheses of trace duality.
-/

open Matrix Finset

namespace ProjectionConstants

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Sign patterns -/

/-- The sign `z / |z|` of a scalar (and `0` for `z = 0`). -/
noncomputable def rsgn (z : 𝕜) : 𝕜 := ((‖z‖⁻¹ : ℝ) : 𝕜) * z

lemma norm_rsgn_le (z : 𝕜) : ‖rsgn z‖ ≤ 1 := by
  rw [rsgn, norm_mul, RCLike.norm_ofReal, abs_inv, abs_norm]
  by_cases hz : z = 0
  · simp [hz]
  · rw [inv_mul_cancel₀ (norm_ne_zero_iff.2 hz)]

lemma rsgn_mul_conj (z : 𝕜) : rsgn z * star z = (‖z‖ : 𝕜) := by
  rw [rsgn, mul_assoc, RCLike.star_def, RCLike.mul_conj]
  by_cases hz : z = 0
  · simp [hz]
  · have : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
    push_cast
    field_simp

lemma star_rsgn (z : 𝕜) : star (rsgn z) = rsgn (star z) := by
  simp [rsgn, RCLike.star_def]

/-- The sign pattern `sgn(P) = (Pᵢⱼ / |Pᵢⱼ|)ᵢⱼ` of a matrix. -/
noncomputable def sgnMat (P : Matrix ι ι 𝕜) : Matrix ι ι 𝕜 := Matrix.of fun i j => rsgn (P i j)

omit [Fintype ι] [DecidableEq ι] in
/-- For a Hermitian matrix, `Pⱼᵢ = conj Pᵢⱼ`. -/
lemma apply_eq_star_of_herm {P : Matrix ι ι 𝕜} (hP : Pᴴ = P) (i j : ι) :
    P j i = star (P i j) := by
  conv_lhs => rw [← hP]
  rfl

omit [Fintype ι] [DecidableEq ι] in
lemma sgnMat_conjTranspose {P : Matrix ι ι 𝕜} (hP : Pᴴ = P) : (sgnMat P)ᴴ = sgnMat P := by
  ext i j
  simp only [sgnMat, conjTranspose_apply, of_apply, star_rsgn]
  rw [← apply_eq_star_of_herm hP]

omit [Fintype ι] [DecidableEq ι] in
lemma norm_sgnMat_le (P : Matrix ι ι 𝕜) (i j : ι) : ‖sgnMat P i j‖ ≤ 1 := norm_rsgn_le _

/-! ### Trace duality -/

/-- **Trace duality in `ℓ∞`.** If `P₀` is idempotent, `A` commutes with `P₀`, and the columns
of `A` are bounded by `αᵢ` with `∑ αᵢ ≤ 1`, then `Re tr(A P₀) ≤ λ(range P₀, ℓ∞)`. -/
theorem re_trace_le_relProjConst {P₀ A : Matrix ι ι 𝕜} (hP₀ : P₀ * P₀ = P₀)
    (hAP : A * P₀ = P₀ * A) {α : ι → ℝ} (hα : ∀ i j, ‖A j i‖ ≤ α i) (hsum : ∑ i, α i ≤ 1) :
    RCLike.re (A * P₀).trace ≤ relProjConst (LinearMap.range (Matrix.toLin' P₀)) := by
  refine le_relProjConst_of_rowSumNorm _ fun R hR => ?_
  have hRP : R * P₀ = P₀ := by
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    simp only [Matrix.toLin'_apply, ← mulVec_mulVec]
    exact hR.map_id _ ⟨v, rfl⟩
  have hPR : P₀ * R = R := by
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    simp only [Matrix.toLin'_apply]
    obtain ⟨w, hw⟩ := hR.mem v
    rw [Matrix.toLin'_apply] at hw
    rw [← mulVec_mulVec, ← hw, mulVec_mulVec, hP₀]
  have htr : (A * P₀).trace = (A * R).trace := by
    calc (A * P₀).trace = (A * R * P₀).trace := by rw [Matrix.mul_assoc, hRP]
      _ = (P₀ * (A * R)).trace := by rw [Matrix.trace_mul_comm]
      _ = (A * P₀ * R).trace := by rw [← Matrix.mul_assoc, ← hAP]
      _ = (A * R).trace := by rw [Matrix.mul_assoc, hPR]
  have hα0 : ∀ i, 0 ≤ α i := fun i => (norm_nonneg _).trans (hα i i)
  rw [htr]
  calc RCLike.re (A * R).trace ≤ ‖(A * R).trace‖ := RCLike.re_le_norm _
    _ = ‖∑ j, ∑ i, A j i * R i j‖ := by simp [Matrix.trace, Matrix.mul_apply]
    _ ≤ ∑ j, ∑ i, ‖A j i‖ * ‖R i j‖ := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp
    _ = ∑ i, ∑ j, ‖A j i‖ * ‖R i j‖ := Finset.sum_comm
    _ ≤ ∑ i, α i * ∑ j, ‖R i j‖ := by
        refine sum_le_sum fun i _ => ?_
        rw [mul_sum]
        exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hα i j) (norm_nonneg _)
    _ ≤ ∑ i, α i * rowSumNorm R :=
        sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (row_le_rowSumNorm R i) (hα0 i)
    _ = (∑ i, α i) * rowSumNorm R := by rw [sum_mul]
    _ ≤ 1 * rowSumNorm R := mul_le_mul_of_nonneg_right hsum (rowSumNorm_nonneg R)
    _ = rowSumNorm R := one_mul _

/-! ### The weighted lower bound -/

omit [DecidableEq ι] in
lemma continuous_weightedAbsSum (t : ι → ℝ) :
    Continuous fun P : Matrix ι ι 𝕜 => weightedAbsSum t P :=
  continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_const.mul (continuous_apply_apply i j).norm

omit [DecidableEq ι] in
lemma trace_mul_eq_sum (B Q : Matrix ι ι 𝕜) : (B * Q).trace = ∑ i, ∑ j, B i j * Q j i := by
  simp [Matrix.trace, Matrix.mul_apply]

lemma diag_mul_mul_diag_apply (t : ι → ℝ) (S : Matrix ι ι 𝕜) (i j : ι) :
    (diagonal (fun i => (t i : 𝕜)) * S * diagonal (fun i => (t i : 𝕜))) i j =
      (t i : 𝕜) * S i j * (t j : 𝕜) := by
  rw [mul_diagonal, diagonal_mul]

/-- `Re tr(D S D Q) ≤ ∑ᵢⱼ tᵢ tⱼ |Qᵢⱼ|` for `|Sᵢⱼ| ≤ 1`, `t ≥ 0` and Hermitian `Q`. -/
lemma re_trace_diag_mul_le {t : ι → ℝ} (ht : ∀ i, 0 ≤ t i) {S Q : Matrix ι ι 𝕜}
    (hS : ∀ i j, ‖S i j‖ ≤ 1) (hQ : Qᴴ = Q) :
    RCLike.re (diagonal (fun i => (t i : 𝕜)) * S * diagonal (fun i => (t i : 𝕜)) * Q).trace ≤
      weightedAbsSum t Q := by
  rw [trace_mul_eq_sum, map_sum]
  refine sum_le_sum fun i _ => ?_
  rw [map_sum]
  refine sum_le_sum fun j _ => ?_
  rw [diag_mul_mul_diag_apply]
  refine (RCLike.re_le_norm _).trans ?_
  rw [norm_mul, norm_mul, norm_mul, RCLike.norm_ofReal, RCLike.norm_ofReal, abs_of_nonneg (ht i),
    abs_of_nonneg (ht j), apply_eq_star_of_herm hQ, norm_star]
  have := hS i j
  have := ht i
  have := ht j
  have := norm_nonneg (Q i j)
  have : t i * ‖S i j‖ * t j * ‖Q i j‖ ≤ t i * 1 * t j * ‖Q i j‖ := by gcongr
  linarith

lemma re_trace_diag_sgnMat {t : ι → ℝ} {Q : Matrix ι ι 𝕜} (hQ : Qᴴ = Q) :
    RCLike.re (diagonal (fun i => (t i : 𝕜)) * sgnMat Q * diagonal (fun i => (t i : 𝕜)) * Q).trace =
      weightedAbsSum t Q := by
  rw [trace_mul_eq_sum, map_sum, weightedAbsSum]
  refine sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [diag_mul_mul_diag_apply, apply_eq_star_of_herm hQ]
  have h := rsgn_mul_conj (Q i j)
  have e : (t i : 𝕜) * sgnMat Q i j * (t j : 𝕜) * star (Q i j) =
      ((t i * t j * ‖Q i j‖ : ℝ) : 𝕜) := by
    simp only [sgnMat, of_apply]
    push_cast
    calc (t i : 𝕜) * rsgn (Q i j) * (t j : 𝕜) * star (Q i j)
        = (t i : 𝕜) * (t j : 𝕜) * (rsgn (Q i j) * star (Q i j)) := by ring
      _ = _ := by rw [h]
  rw [e, RCLike.ofReal_re]

/-- **Chalmers–Lewicki, lower bound (positive weights).** For weights `t > 0` with `∑ tᵢ² = 1`
and `P ∈ 𝒫ₘ(ι)` there is an `m`-dimensional subspace `Y ⊆ ℓ∞^ι` with
`∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| ≤ λ(Y, ℓ∞^ι)`. -/
theorem exists_le_relProjConst {m : ℕ} {t : ι → ℝ} (ht : ∀ i, 0 < t i)
    (ht1 : ∑ i, t i ^ 2 = 1) {P : Matrix ι ι 𝕜} (hP : P ∈ orthProjs 𝕜 ι m) :
    ∃ Y : Submodule 𝕜 (ι → 𝕜), Module.finrank 𝕜 Y = m ∧ weightedAbsSum t P ≤ relProjConst Y := by
  -- a maximizer `Q` of `∑ tᵢ tⱼ |Qᵢⱼ|`
  obtain ⟨Q, hQ, hQmax⟩ := (isCompact_orthProjs (𝕜 := 𝕜) (ι := ι) m).exists_isMaxOn ⟨P, hP⟩
    (continuous_weightedAbsSum t).continuousOn
  set D : Matrix ι ι 𝕜 := diagonal fun i => (t i : 𝕜) with hD
  set Dinv : Matrix ι ι 𝕜 := diagonal fun i => ((t i)⁻¹ : 𝕜) with hDinv
  have htne : ∀ i, (t i : 𝕜) ≠ 0 := fun i => by exact_mod_cast (ht i).ne'
  have hDD : Dinv * D = 1 := by
    rw [hDinv, hD, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; ext i; field_simp [htne i]
  have hDD' : D * Dinv = 1 := by
    rw [hDinv, hD, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; ext i; field_simp [htne i]
  set S := sgnMat Q with hS
  set B := D * S * D with hB
  have hDh : Dᴴ = D := by
    rw [hD, diagonal_conjTranspose]
    congr 1
    ext i
    simp
  have hBh : Bᴴ = B := by
    rw [hB, conjTranspose_mul, conjTranspose_mul, hDh, sgnMat_conjTranspose hQ.1.herm,
      Matrix.mul_assoc]
  -- `Q` maximizes `Re tr(B ·)`, hence commutes with `B`
  have hBQ : B * Q = Q * B := by
    refine commute_of_isMaxOn hBh hQ fun Q' hQ' => ?_
    calc RCLike.re (B * Q').trace ≤ weightedAbsSum t Q' :=
          re_trace_diag_mul_le (fun i => (ht i).le) (norm_sgnMat_le Q) hQ'.1.herm
      _ ≤ weightedAbsSum t Q := hQmax hQ'
      _ = RCLike.re (B * Q).trace := (re_trace_diag_sgnMat hQ.1.herm).symm
  -- conjugation by `D`
  have hconj : ∀ X Y : Matrix ι ι 𝕜, Dinv * X * D * (Dinv * Y * D) = Dinv * (X * Y) * D := by
    intro X Y
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc D Dinv, hDD', Matrix.one_mul]
  have htrconj : ∀ X : Matrix ι ι 𝕜, (Dinv * X * D).trace = X.trace := by
    intro X
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hDD', Matrix.mul_one]
  -- the subspace `Y = D⁻¹ range(Q)` and the certificate `A = S D²`
  set P₀ := Dinv * Q * D with hP₀
  have hP₀P₀ : P₀ * P₀ = P₀ := by rw [hP₀, hconj, hQ.1.idem]
  have htrP₀ : P₀.trace = m := by rw [hP₀, htrconj, hQ.2]
  set A := S * D * D with hA
  have hA' : A = Dinv * B * D := by
    rw [hA, hB, ← Matrix.mul_assoc Dinv, ← Matrix.mul_assoc Dinv, hDD, Matrix.one_mul]
  have hAP : A * P₀ = P₀ * A := by
    rw [hA', hP₀, hconj, hconj, hBQ]
  have htrA : (A * P₀).trace = (B * Q).trace := by
    rw [hA', hP₀, hconj, htrconj]
  have hαA : ∀ i j, ‖A j i‖ ≤ t i ^ 2 := by
    intro i j
    rw [hA, mul_diagonal, mul_diagonal, norm_mul, norm_mul, RCLike.norm_ofReal, abs_of_pos (ht i)]
    have h1 := norm_sgnMat_le Q j i
    have := ht i
    nlinarith
  refine ⟨LinearMap.range (Matrix.toLin' P₀), ?_, ?_⟩
  · have h := finrank_range_eq_trace hP₀P₀
    rw [htrP₀] at h
    exact_mod_cast h
  · calc weightedAbsSum t P ≤ weightedAbsSum t Q := hQmax hP
      _ = RCLike.re (B * Q).trace := (re_trace_diag_sgnMat hQ.1.herm).symm
      _ = RCLike.re (A * P₀).trace := by rw [htrA]
      _ ≤ _ := re_trace_le_relProjConst hP₀P₀ hAP hαA (le_of_eq ht1)

/-! ### From positive weights to all weights -/

/-- **Chalmers–Lewicki, lower bound.** `sup ∑ tᵢ tⱼ |Pᵢⱼ| ≤ λ_𝕜(m, N)`. -/
theorem clConst_le_maxRelProjConst (m N : ℕ) : clConst 𝕜 (Fin N) m ≤ maxRelProjConst 𝕜 m N := by
  refine clConst_le (maxRelProjConst_nonneg m N) fun t P ht hP => ?_
  set L := maxRelProjConst 𝕜 m N
  have hL := maxRelProjConst_nonneg (𝕜 := 𝕜) m N
  -- positive weights
  have hpos : ∀ s : Fin N → ℝ, (∀ i, 0 < s i) → ∑ i, s i ^ 2 = 1 → weightedAbsSum s P ≤ L := by
    intro s hs hs1
    obtain ⟨Y, hY, hle⟩ := exists_le_relProjConst hs hs1 hP
    exact hle.trans (relProjConst_le_maxRelProjConst Y hY)
  -- perturb `t` to `t + ε` and normalize
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set n : ℝ := (N : ℝ)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  set ε : ℝ := min 1 (δ / (3 * n * L + 1)) with hε_def
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hε2 : ε * (3 * n * L + 1) ≤ δ := by
    have := min_le_right 1 (δ / (3 * n * L + 1))
    rw [← hε_def] at this
    calc ε * (3 * n * L + 1) ≤ δ / (3 * n * L + 1) * (3 * n * L + 1) := by gcongr
      _ = δ := div_mul_cancel₀ _ (by positivity)
  set u : Fin N → ℝ := fun i => t i + ε
  set c : ℝ := ∑ i, u i ^ 2 with hc
  have hu : ∀ i, 0 < u i := fun i => by have := ht.nonneg i; positivity
  have hti1 : ∀ i, t i ≤ 1 := fun i => by
    have h := single_le_sum (f := fun i => t i ^ 2) (fun j _ => sq_nonneg (t j)) (mem_univ i)
    rw [ht.sum_sq] at h
    nlinarith [ht.nonneg i]
  have hc1 : 1 ≤ c := by
    rw [hc, ← ht.sum_sq]
    exact sum_le_sum fun i _ => by have := ht.nonneg i; nlinarith
  have hc2 : c ≤ 1 + 3 * n * ε := by
    have h : ∀ i, u i ^ 2 ≤ t i ^ 2 + 3 * ε := fun i => by
      have := ht.nonneg i; have := hti1 i; nlinarith
    calc c ≤ ∑ i, (t i ^ 2 + 3 * ε) := sum_le_sum fun i _ => h i
      _ = 1 + 3 * n * ε := by
          rw [sum_add_distrib, ht.sum_sq]; simp [n]; ring
  have hc0 : 0 < c := by linarith
  -- the normalized weights `s = u / √c`
  set s : Fin N → ℝ := fun i => u i / √c
  have hs : ∀ i, 0 < s i := fun i => div_pos (hu i) (Real.sqrt_pos.2 hc0)
  have hs1 : ∑ i, s i ^ 2 = 1 := by
    simp only [s, div_pow, Real.sq_sqrt hc0.le, ← sum_div, ← hc, div_self hc0.ne']
  have h1 : weightedAbsSum t P ≤ c * weightedAbsSum s P := by
    have e : c * weightedAbsSum s P = weightedAbsSum u P := by
      simp only [weightedAbsSum, mul_sum, s]
      refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
      have hsq : √c ^ 2 = c := Real.sq_sqrt hc0.le
      have hsc : √c ≠ 0 := (Real.sqrt_pos.2 hc0).ne'
      field_simp
      rw [hsq]
      ring
    rw [e]
    refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
    have := ht.nonneg i; have := ht.nonneg j
    have : t i * t j ≤ u i * u j := by
      simp only [u]; nlinarith
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  calc weightedAbsSum t P ≤ c * weightedAbsSum s P := h1
    _ ≤ (1 + 3 * n * ε) * L := by
        have := hpos s hs hs1
        have := weightedAbsSum_nonneg (fun i => (hs i).le) P
        nlinarith
    _ ≤ L + δ := by nlinarith

end ProjectionConstants
