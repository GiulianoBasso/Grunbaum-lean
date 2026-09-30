/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import Grunbaum.ChalmersLewicki
import Grunbaum.Fan
import ProjectionConstants.Foundations.Commute

/-!
# The cloning lemma of Kumar, Mohar, Mojallal and Pragada

We formalize Claims 2.1–2.4 of

* [KMMP] H. Kumar, B. Mohar, S. A. Mojallal, S. Pragada, *Stability of maximal relative projection
  constants*, arXiv:2609.03200,

in their notation. Fix `r, n ∈ ℕ` and let `λ(r, n) = ProjectionConstants.maxRelProjConst ℝ r n`
be the maximal relative projection constant of `r`-dimensional subspaces of `ℓ∞^n`. A matrix
`U ∈ ℝ^{n×r}` is *feasible* if `UᵀU = I_r`; its rows are denoted `xᵢ ∈ ℝ^r`. A vector
`w ∈ ℝⁿ` is *feasible* if it is a unit non-negative vector (`ProjectionConstants.IsUnitWeight`).
For feasible `U` and `w`,

`σ(U, w) = ∑ᵢⱼ wᵢ wⱼ |⟨xᵢ, xⱼ⟩|`   (`Grunbaum.KMMP.sigma`).

By the theorem of Chalmers and Lewicki ([KMMP, Theorem 2.1];
`ProjectionConstants.maxRelProjConst_eq_clConst`), `λ(r, n)` is the maximum of `σ(U, w)`. A
*maximizing pair* is a feasible pair `(U, w)` with `σ(U, w) = λ(r, n)`
(`Grunbaum.KMMP.IsMaximizingPair`).

## Main results

* `Grunbaum.KMMP.sigma_le` : **Theorem 2.1**, the inequality `σ(U, w) ≤ λ(r, n)`;
* `Grunbaum.KMMP.one_le_maxRelProjConst` : **Remark 2.2**, `λ(r, n) ≥ 1` for `r ≥ 1`;
* `Grunbaum.KMMP.IsMaximizingPair.absGram_mulVec` : **Claim 2.1**, `w` is a
  `λ(r, n)`-eigenvector of `B = (|⟨xᵢ, xⱼ⟩|)ᵢⱼ`, and `λ(r, n) = λ₁(B)`;
* `Grunbaum.KMMP.IsMaximizingPair.mul_eq_mul` : **Claim 2.2**, `M(G, w) U = U H` for the graph
  `G` given by the signs of `⟨xᵢ, xⱼ⟩` and the symmetric matrix `H = Uᵀ M(G, w) U`;
* `Grunbaum.KMMP.IsMaximizingPair.dotProduct_mulVec_H` : **Claim 2.3**,
  `xᵢᵀ H xᵢ = λ(r, n) wᵢ²`;
* `Grunbaum.KMMP.IsMaximizingPair.clone` : **Claim 2.4 (Cloning)**.

## Implementation notes

* In the proof of Claim 2.1, KMMP use the Perron–Frobenius theorem to see that `λ₁(B)` has a
  non-negative unit eigenvector. We use instead that `xᵀBx ≤ |x|ᵀB|x|` for the entrywise
  absolute value `|x|`, so that `w` maximizes the Rayleigh quotient of `B` over all unit vectors;
  the eigenvector equation is its first-order condition.
* In the proof of Claim 2.2, KMMP use the equality case of the Ky Fan maximum principle. We use
  instead that a maximizer `P` of `Q ↦ Tr(MQ)` over the orthogonal projections of rank `r`
  commutes with `M` (`ProjectionConstants.commute_of_isMaxOn`); for `P = UUᵀ` this is
  `MU = U (UᵀMU)`.
-/

open Finset Matrix ProjectionConstants

namespace Grunbaum.KMMP

variable {n r : ℕ}

/-- `σ(U, w) = ∑ᵢⱼ wᵢ wⱼ |⟨xᵢ, xⱼ⟩|`, where `xᵢ` is the `i`-th row of `U`. -/
noncomputable def sigma (U : Matrix (Fin n) (Fin r) ℝ) (w : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, w i * w j * |U i ⬝ᵥ U j|

/-- A **maximizing pair** `(U, w)`: `U` is feasible (`UᵀU = I_r`), `w` is a unit non-negative
vector, and `σ(U, w) = λ(r, n)`. -/
structure IsMaximizingPair (U : Matrix (Fin n) (Fin r) ℝ) (w : Fin n → ℝ) : Prop where
  transpose_mul_self : Uᵀ * U = 1
  isUnitWeight : IsUnitWeight w
  sigma_eq : sigma U w = maxRelProjConst ℝ r n

/-! ### Theorem 2.1 and Remark 2.2 -/

/-- `∑ᵢⱼ yᵢ yⱼ ⟨xᵢ, xⱼ⟩ = |Uᵀy|² = ∑ₐ (∑ᵢ yᵢ Uᵢₐ)²`. -/
lemma sum_mul_dotProduct_eq_sum_sq (U : Matrix (Fin n) (Fin r) ℝ) (y : Fin n → ℝ) :
    ∑ i, ∑ j, y i * y j * (U i ⬝ᵥ U j) = ∑ a, (∑ i, y i * U i a) ^ 2 := by
  symm
  simp only [sq, sum_mul_sum]
  simp only [dotProduct, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]
  exact sum_congr rfl fun j _ => sum_congr rfl fun a _ => by ring

section Feasible

variable {U : Matrix (Fin n) (Fin r) ℝ}

lemma mul_transpose_apply (U : Matrix (Fin n) (Fin r) ℝ) (i j : Fin n) :
    (U * Uᵀ) i j = U i ⬝ᵥ U j := by
  simp [mul_apply, dotProduct]

/-- For feasible `U`, the Gram matrix `UUᵀ = (⟨xᵢ, xⱼ⟩)ᵢⱼ` is an orthogonal projection of rank
`r`. -/
lemma mul_transpose_mem_orthProjs (hU : Uᵀ * U = 1) : U * Uᵀ ∈ orthProjs ℝ (Fin n) r := by
  have h := conjTranspose_mul_self_mem_orthProjs (U := Uᵀ)
    (by rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose]; exact hU)
  rwa [conjTranspose_eq_transpose_of_trivial, transpose_transpose] at h

lemma weightedAbsSum_mul_transpose (U : Matrix (Fin n) (Fin r) ℝ) (w : Fin n → ℝ) :
    weightedAbsSum w (U * Uᵀ) = sigma U w := by
  simp only [weightedAbsSum, sigma, mul_transpose_apply, Real.norm_eq_abs]

/-- **Theorem 2.1** (Chalmers–Lewicki): `σ(U, w) ≤ λ(r, n)` for feasible `U` and `w`. -/
theorem sigma_le (hU : Uᵀ * U = 1) {w : Fin n → ℝ} (hw : IsUnitWeight w) :
    sigma U w ≤ maxRelProjConst ℝ r n := by
  rw [maxRelProjConst_eq_clConst, ← weightedAbsSum_mul_transpose]
  exact le_clConst hw (mul_transpose_mem_orthProjs hU)

/-- **Remark 2.2**: `λ(r, n) ≥ 1` if there is a feasible `U ∈ ℝ^{n×r}` with `r ≥ 1`. Indeed, for
the first column `y` of `U` and `wᵢ = |yᵢ|` we have `σ(U, w) ≥ ∑ᵢⱼ yᵢ yⱼ ⟨xᵢ, xⱼ⟩ = 1`. -/
theorem one_le_maxRelProjConst (hU : Uᵀ * U = 1) (hr : 0 < r) : 1 ≤ maxRelProjConst ℝ r n := by
  set a : Fin r := ⟨0, hr⟩
  set y : Fin n → ℝ := fun i => U i a with hy
  -- `∑ᵢ yᵢ U i b = (UᵀU) a b`
  have hcol : ∀ b, ∑ i, y i * U i b = if a = b then 1 else 0 := by
    intro b
    have := congrFun (congrFun hU a) b
    simp only [mul_apply, transpose_apply, one_apply] at this
    rw [← this]
  have hyy : ∑ i, y i ^ 2 = 1 := by
    simpa [sq] using hcol a
  have ht : IsUnitWeight fun i => |y i| := ⟨fun _ => abs_nonneg _, by simpa [sq_abs] using hyy⟩
  refine le_trans ?_ (sigma_le hU ht)
  have h1 : ∑ i, ∑ j, y i * y j * (U i ⬝ᵥ U j) = 1 := by
    rw [sum_mul_dotProduct_eq_sum_sq]
    simp only [hcol]
    simp
  rw [← h1]
  refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
  calc y i * y j * (U i ⬝ᵥ U j) ≤ |y i * y j * (U i ⬝ᵥ U j)| := le_abs_self _
    _ = |y i| * |y j| * |U i ⬝ᵥ U j| := by rw [abs_mul, abs_mul]

end Feasible

/-! ### Claim 2.1 -/

/-- The matrix `B = (|⟨xᵢ, xⱼ⟩|)ᵢⱼ`. -/
noncomputable def absGram (U : Matrix (Fin n) (Fin r) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i j => |U i ⬝ᵥ U j|

lemma absGram_symm (U : Matrix (Fin n) (Fin r) ℝ) (i j : Fin n) :
    absGram U j i = absGram U i j := by
  simp only [absGram, of_apply, dotProduct_comm]

lemma sigma_eq_dotProduct_mulVec (U : Matrix (Fin n) (Fin r) ℝ) (w : Fin n → ℝ) :
    sigma U w = w ⬝ᵥ (absGram U *ᵥ w) := by
  rw [dotProduct_mulVec_eq_sum, sigma]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by simp only [absGram, of_apply]; ring

/-- For feasible `U`, `xᵀBx ≤ λ(r, n) |x|²` for all `x ∈ ℝⁿ`: compare with `σ(U, |x|/|x|)`. -/
theorem dotProduct_mulVec_absGram_le {U : Matrix (Fin n) (Fin r) ℝ} (hU : Uᵀ * U = 1)
    (x : Fin n → ℝ) : x ⬝ᵥ (absGram U *ᵥ x) ≤ maxRelProjConst ℝ r n * (x ⬝ᵥ x) := by
  set a : Fin n → ℝ := fun i => |x i| with ha
  have h1 : x ⬝ᵥ (absGram U *ᵥ x) ≤ a ⬝ᵥ (absGram U *ᵥ a) := by
    rw [dotProduct_mulVec_eq_sum, dotProduct_mulVec_eq_sum]
    refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
    simp only [absGram, of_apply, ha]
    calc |U i ⬝ᵥ U j| * x i * x j ≤ abs (|U i ⬝ᵥ U j| * x i * x j) := le_abs_self _
      _ = |U i ⬝ᵥ U j| * |x i| * |x j| := by rw [abs_mul, abs_mul, abs_abs]
  have haa : a ⬝ᵥ a = x ⬝ᵥ x := by
    simp only [dotProduct, ha, abs_mul_abs_self]
  rcases (dotProduct_self_nonneg' x).lt_or_eq with hpos | hzero
  · -- normalize `a`
    obtain ⟨s, hs⟩ : ∃ s, x ⬝ᵥ x = s := ⟨_, rfl⟩
    rw [hs] at hpos haa ⊢
    have hsq : √s * √s = s := Real.mul_self_sqrt hpos.le
    set t : Fin n → ℝ := fun i => a i / √s with ht_def
    have htt : ∀ i j, t i * t j = a i * a j / s := by
      intro i j
      rw [ht_def, div_mul_div_comm, hsq]
    have ht : IsUnitWeight t := by
      refine ⟨fun i => div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _), ?_⟩
      have : ∑ i, t i ^ 2 = (a ⬝ᵥ a) / s := by
        rw [dotProduct, sum_div]
        exact sum_congr rfl fun i _ => by rw [sq, htt]
      rw [this, haa, div_self hpos.ne']
    have h2 := sigma_le hU ht
    rw [sigma_eq_dotProduct_mulVec] at h2
    have e : t ⬝ᵥ (absGram U *ᵥ t) = (a ⬝ᵥ (absGram U *ᵥ a)) / s := by
      rw [dotProduct_mulVec_eq_sum, dotProduct_mulVec_eq_sum, sum_div]
      refine sum_congr rfl fun i _ => ?_
      rw [sum_div]
      refine sum_congr rfl fun j _ => ?_
      rw [mul_assoc, htt]
      ring
    rw [e, div_le_iff₀ hpos] at h2
    linarith
  · -- `x = 0`
    have hx : x = 0 := dotProduct_self_eq_zero.mp hzero.symm
    subst hx
    simp

/-- **Claim 2.1** of KMMP: for a maximizing pair `(U, w)`, `w` is an eigenvector of `B` for the
eigenvalue `λ(r, n)`: `B w = λ(r, n) w`. Together with `Grunbaum.KMMP.dotProduct_mulVec_absGram_le`
and `wᵀBw = σ(U, w) = λ(r, n)`, this says `λ(r, n) = λ₁(B)`. -/
theorem IsMaximizingPair.absGram_mulVec {U : Matrix (Fin n) (Fin r) ℝ} {w : Fin n → ℝ}
    (h : IsMaximizingPair U w) : absGram U *ᵥ w = maxRelProjConst ℝ r n • w := by
  set L := maxRelProjConst ℝ r n
  set B := absGram U
  have hB : ∀ i j, B j i = B i j := absGram_symm U
  have hww : w ⬝ᵥ w = 1 := by simpa [dotProduct, sq] using h.isUnitWeight.sum_sq
  have hwB : w ⬝ᵥ (B *ᵥ w) = L := by rw [← sigma_eq_dotProduct_mulVec]; exact h.sigma_eq
  -- the first-order condition for the maximum of `x ↦ xᵀBx - λ |x|²` at `w`
  have key : ∀ z, z ⬝ᵥ (B *ᵥ w) = L * (z ⬝ᵥ w) := by
    intro z
    have := eq_zero_of_forall_quad (β := z ⬝ᵥ (B *ᵥ w) - L * (z ⬝ᵥ w))
      (c := z ⬝ᵥ (B *ᵥ z) - L * (z ⬝ᵥ z)) fun t => by
        have h1 := dotProduct_mulVec_absGram_le h.transpose_mul_self ((1 : ℝ) • w + t • z)
        rw [quad_add_smul hB] at h1
        have e : ((1 : ℝ) • w + t • z) ⬝ᵥ ((1 : ℝ) • w + t • z)
            = w ⬝ᵥ w + 2 * t * (z ⬝ᵥ w) + t ^ 2 * (z ⬝ᵥ z) := by
          simp only [one_smul, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
            smul_eq_mul, dotProduct_comm w z]
          ring
        rw [e, hww, hwB] at h1
        linear_combination h1
    linarith
  ext i
  have := key (Pi.single i 1)
  simpa [single_dotProduct] using this

/-- **Claim 2.1** in coordinates: `∑ⱼ |⟨xᵢ, xⱼ⟩| wⱼ = λ(r, n) wᵢ`. -/
theorem IsMaximizingPair.sum_abs_mul {U : Matrix (Fin n) (Fin r) ℝ} {w : Fin n → ℝ}
    (h : IsMaximizingPair U w) (i : Fin n) :
    ∑ j, |U i ⬝ᵥ U j| * w j = maxRelProjConst ℝ r n * w i :=
  congrFun h.absGram_mulVec i

/-! ### Claims 2.2 and 2.3 -/

section Claims

variable {U : Matrix (Fin n) (Fin r) ℝ} {w : Fin n → ℝ}

/-- The matrix `M(G, w) = D_w (I + S(G)) D_w`, where `G` is the graph of Claim 2.2:
`(I + S(G))ᵢⱼ = 1` if `⟨xᵢ, xⱼ⟩ ≥ 0` and `-1` otherwise. -/
noncomputable def weightedSign (U : Matrix (Fin n) (Fin r) ℝ) (w : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  of fun i j => w i * signPattern (U * Uᵀ) i j * w j

lemma weightedSign_symm (U : Matrix (Fin n) (Fin r) ℝ) (w : Fin n → ℝ) (i j : Fin n) :
    weightedSign U w j i = weightedSign U w i j := by
  simp only [weightedSign, signPattern, of_apply, mul_transpose_apply, dotProduct_comm (U j)]
  ring

lemma trace_weightedSign_mul_le {Q : Matrix (Fin n) (Fin n) ℝ} (hw : ∀ i, 0 ≤ w i)
    (hQ : IsOrthProj Q) : (weightedSign U w * Q).trace ≤ weightedAbsSum w Q := by
  simp only [trace, diag_apply, mul_apply, weightedAbsSum, Real.norm_eq_abs]
  refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
  have hQs : Q j i = Q i j := by rw [hQ.apply_symm, star_trivial]
  rw [hQs]
  have hs : signPattern (U * Uᵀ) i j * Q i j ≤ |Q i j| := by
    simp only [signPattern, of_apply]
    split_ifs
    · rw [one_mul]; exact le_abs_self _
    · rw [neg_one_mul]; exact neg_le_abs _
  have hww : 0 ≤ w i * w j := mul_nonneg (hw i) (hw j)
  calc weightedSign U w i j * Q i j = w i * w j * (signPattern (U * Uᵀ) i j * Q i j) := by
        simp only [weightedSign, of_apply]; ring
    _ ≤ w i * w j * |Q i j| := mul_le_mul_of_nonneg_left hs hww

lemma trace_weightedSign_mul_transpose (U : Matrix (Fin n) (Fin r) ℝ) (w : Fin n → ℝ) :
    (weightedSign U w * (U * Uᵀ)).trace = sigma U w := by
  simp only [trace, diag_apply, mul_apply, sigma]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  have hsym : (U * Uᵀ) j i = (U * Uᵀ) i j := by
    rw [mul_transpose_apply, mul_transpose_apply, dotProduct_comm]
  have := signPattern_mul_self (U * Uᵀ) i j
  rw [mul_transpose_apply] at this
  simp only [weightedSign, of_apply, ← mul_apply]
  rw [hsym, mul_transpose_apply, ← this]
  ring

/-- `P = UUᵀ` maximizes `Q ↦ Tr(M(G, w) Q)` over the orthogonal projections of rank `r`. -/
theorem IsMaximizingPair.trace_mul_le (h : IsMaximizingPair U w) {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q ∈ orthProjs ℝ (Fin n) r) :
    (weightedSign U w * Q).trace ≤ (weightedSign U w * (U * Uᵀ)).trace := by
  rw [trace_weightedSign_mul_transpose, h.sigma_eq, maxRelProjConst_eq_clConst]
  exact (trace_weightedSign_mul_le h.isUnitWeight.nonneg hQ.1).trans
    (le_clConst h.isUnitWeight hQ)

/-- **Claim 2.2**, projection form: `M(G, w)` commutes with `P = UUᵀ`. -/
theorem IsMaximizingPair.commute (h : IsMaximizingPair U w) :
    weightedSign U w * (U * Uᵀ) = (U * Uᵀ) * weightedSign U w := by
  refine commute_of_isMaxOn (𝕜 := ℝ) (m := r) ?_ (mul_transpose_mem_orthProjs h.transpose_mul_self)
    fun Q hQ => ?_
  · rw [conjTranspose_eq_transpose_of_trivial]
    ext i j
    rw [transpose_apply]
    exact weightedSign_symm U w i j
  · simpa only [RCLike.re_to_real] using h.trace_mul_le hQ

/-- **Claim 2.2** of KMMP: `M(G, w) U = U H` with `H = Uᵀ M(G, w) U`. -/
theorem IsMaximizingPair.mul_eq_mul (h : IsMaximizingPair U w) :
    weightedSign U w * U = U * (Uᵀ * weightedSign U w * U) := by
  have hU := h.transpose_mul_self
  calc weightedSign U w * U = weightedSign U w * (U * (Uᵀ * U)) := by rw [hU, Matrix.mul_one]
    _ = (weightedSign U w * (U * Uᵀ)) * U := by simp only [Matrix.mul_assoc]
    _ = ((U * Uᵀ) * weightedSign U w) * U := by rw [h.commute]
    _ = U * (Uᵀ * weightedSign U w * U) := by simp only [Matrix.mul_assoc]

/-- The matrix `H = Uᵀ M(G, w) U` of Claim 2.2 is symmetric. -/
lemma transpose_H (U : Matrix (Fin n) (Fin r) ℝ) (w : Fin n → ℝ) :
    (Uᵀ * weightedSign U w * U)ᵀ = Uᵀ * weightedSign U w * U := by
  have hM : (weightedSign U w)ᵀ = weightedSign U w := by
    ext i j
    rw [transpose_apply]
    exact weightedSign_symm U w i j
  rw [transpose_mul, transpose_mul, transpose_transpose, hM, Matrix.mul_assoc]

/-- **Claim 2.3** of KMMP: `xᵢᵀ H xᵢ = λ(r, n) wᵢ²`. -/
theorem IsMaximizingPair.dotProduct_mulVec_H (h : IsMaximizingPair U w) (i : Fin n) :
    U i ⬝ᵥ ((Uᵀ * weightedSign U w * U) *ᵥ U i) = maxRelProjConst ℝ r n * w i ^ 2 := by
  set M := weightedSign U w
  set H := Uᵀ * M * U
  -- `xᵢᵀ H xᵢ = (U H Uᵀ)ᵢᵢ` and `U H Uᵀ = P M P = M P`
  have e1 : U i ⬝ᵥ (H *ᵥ U i) = (U * H * Uᵀ) i i := by
    simp only [dotProduct, mulVec, mul_apply, transpose_apply, mul_sum, sum_mul]
    rw [sum_comm]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
  have hP : (U * Uᵀ) * (U * Uᵀ) = U * Uᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, h.transpose_mul_self, Matrix.one_mul]
  have e2 : U * H * Uᵀ = M * (U * Uᵀ) := by
    calc U * H * Uᵀ = (U * Uᵀ) * M * (U * Uᵀ) := by simp only [H, Matrix.mul_assoc]
      _ = M * ((U * Uᵀ) * (U * Uᵀ)) := by rw [← h.commute, Matrix.mul_assoc]
      _ = M * (U * Uᵀ) := by rw [hP]
  -- `(M P)ᵢᵢ = wᵢ ∑ⱼ |⟨xᵢ, xⱼ⟩| wⱼ = λ wᵢ²` by Claim 2.1
  have hB := h.sum_abs_mul i
  rw [e1, e2, mul_apply]
  have e3 : ∀ j, M i j * (U * Uᵀ) j i = w i * (|U i ⬝ᵥ U j| * w j) := by
    intro j
    have hs := signPattern_mul_self (U * Uᵀ) i j
    have hsym : (U * Uᵀ) j i = (U * Uᵀ) i j := by
      rw [mul_transpose_apply, mul_transpose_apply, dotProduct_comm]
    rw [mul_transpose_apply] at hs
    simp only [M, weightedSign, of_apply]
    rw [hsym, mul_transpose_apply, ← hs]
    ring
  simp only [e3, ← mul_sum, hB]
  ring

end Claims

/-! ### Claim 2.4: cloning -/

section Cloning

variable {U : Matrix (Fin n) (Fin r) ℝ} {w : Fin n → ℝ}

/-- The cloned matrix `Ũ` with rows `x̃ᵢ = √cᵢ xᵢ`. -/
noncomputable def cloneMatrix (U : Matrix (Fin n) (Fin r) ℝ) (c : Fin n → ℝ) :
    Matrix (Fin n) (Fin r) ℝ :=
  of fun i a => √(c i) * U i a

/-- The cloned weights `w̃ᵢ = √cᵢ wᵢ`. -/
noncomputable def cloneWeight (w c : Fin n → ℝ) : Fin n → ℝ := fun i => √(c i) * w i

/-- Condition (ii) of Claim 2.4, entrywise: `∑ᵢ (cᵢ - 1) xᵢ xᵢᵀ = 0`. -/
lemma sum_sub_one_mul_eq_zero {C : Finset (Fin n)} {c : Fin n → ℝ} (hc1 : ∀ i, i ∉ C → c i = 1)
    (hcC : ∑ i ∈ C, c i • vecMulVec (U i) (U i) = ∑ i ∈ C, vecMulVec (U i) (U i))
    (a b : Fin r) : ∑ i, (c i - 1) * (U i a * U i b) = 0 := by
  have h := congrFun (congrFun hcC a) b
  simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul] at h
  rw [← sum_subset (subset_univ C) fun i _ hi => by rw [hc1 i hi]; ring]
  simp only [sub_mul, one_mul, sum_sub_distrib, h, sub_self]

/-- **Claim 2.4 (Cloning)** of KMMP. Let `(U, w)` be a maximizing pair, `r ≥ 1`, and let
`C ⊆ [n]` be such that

1. `⟨xᵢ, xⱼ⟩ ≥ 0` for all `i, j ∈ C`, and
2. there is `c ∈ ℝⁿ_{≥0}` with `cᵢ = 1` for `i ∉ C` and `∑_{i ∈ C} cᵢ xᵢ xᵢᵀ = ∑_{i ∈ C} xᵢ xᵢᵀ`.

Put `w̃ᵢ = √cᵢ wᵢ` and `x̃ᵢ = √cᵢ xᵢ`, and let `Ũ` be the matrix with rows `x̃ᵢ`. Then
`(Ũ, w̃)` is a maximizing pair. -/
theorem IsMaximizingPair.clone (h : IsMaximizingPair U w) (hr : 0 < r) {C : Finset (Fin n)}
    (hC : ∀ i ∈ C, ∀ j ∈ C, 0 ≤ U i ⬝ᵥ U j) {c : Fin n → ℝ} (hc : ∀ i, 0 ≤ c i)
    (hc1 : ∀ i, i ∉ C → c i = 1)
    (hcC : ∑ i ∈ C, c i • vecMulVec (U i) (U i) = ∑ i ∈ C, vecMulVec (U i) (U i)) :
    IsMaximizingPair (cloneMatrix U c) (cloneWeight w c) := by
  set L := maxRelProjConst ℝ r n with hL
  have hsq : ∀ i, √(c i) * √(c i) = c i := fun i => Real.mul_self_sqrt (hc i)
  have hii := sum_sub_one_mul_eq_zero hc1 hcC
  have hw := h.isUnitWeight
  -- `Ũ` is feasible
  have hU' : (cloneMatrix U c)ᵀ * cloneMatrix U c = 1 := by
    rw [← h.transpose_mul_self]
    ext a b
    simp only [mul_apply, transpose_apply, cloneMatrix, of_apply]
    have := hii a b
    have e : ∑ i, √(c i) * U i a * (√(c i) * U i b)
        = ∑ i, U i a * U i b + ∑ i, (c i - 1) * (U i a * U i b) := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun i _ => by linear_combination (U i a * U i b) * hsq i
    rw [e, this, add_zero]
  -- `∑ᵢ (cᵢ - 1) wᵢ² = 0`, by Claim 2.3 and condition (ii)
  have hL1 : 1 ≤ L := one_le_maxRelProjConst h.transpose_mul_self hr
  have hsumw : ∑ i, (c i - 1) * w i ^ 2 = 0 := by
    set H := Uᵀ * weightedSign U w * U
    have e : L * ∑ i, (c i - 1) * w i ^ 2 =
        ∑ a, ∑ b, H a b * ∑ i, (c i - 1) * (U i a * U i b) := by
      rw [mul_sum]
      have e1 : ∀ i, L * ((c i - 1) * w i ^ 2) =
          (c i - 1) * (U i ⬝ᵥ (H *ᵥ U i)) := by
        intro i
        rw [h.dotProduct_mulVec_H i]
        ring
      simp only [e1, dotProduct, mulVec, mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun a _ => ?_
      rw [sum_comm]
      exact sum_congr rfl fun b _ => sum_congr rfl fun i _ => by ring
    simp only [hii, mul_zero, sum_const_zero] at e
    exact (mul_eq_zero.mp e).resolve_left (by linarith)
  -- `w̃` is feasible
  have hw' : IsUnitWeight (cloneWeight w c) := by
    refine ⟨fun i => mul_nonneg (Real.sqrt_nonneg _) (hw.nonneg i), ?_⟩
    have e : ∑ i, cloneWeight w c i ^ 2 = ∑ i, w i ^ 2 + ∑ i, (c i - 1) * w i ^ 2 := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun i _ => by
        simp only [cloneWeight]
        linear_combination (w i ^ 2) * hsq i
    rw [e, hsumw, hw.sum_sq, add_zero]
  refine ⟨hU', hw', le_antisymm (sigma_le hU' hw') ?_⟩
  -- `σ(Ũ, w̃) ≥ σ(U, w)`
  set B := absGram U
  have hB : ∀ i j, B j i = B i j := absGram_symm U
  have hBw' : ∀ i, ∑ j, B i j * w j = L * w i := h.sum_abs_mul
  have e1 : sigma (cloneMatrix U c) (cloneWeight w c) =
      ∑ i, ∑ j, c i * c j * (w i * w j * B i j) := by
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    have hd : cloneMatrix U c i ⬝ᵥ cloneMatrix U c j = √(c i) * √(c j) * (U i ⬝ᵥ U j) := by
      simp only [cloneMatrix, dotProduct, of_apply, mul_sum]
      exact sum_congr rfl fun a _ => by ring
    rw [hd, abs_mul, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    simp only [cloneWeight, B, absGram, of_apply]
    linear_combination (√(c j) * √(c j) * (w i * w j * |U i ⬝ᵥ U j|)) * hsq i
      + (c i * (w i * w j * |U i ⬝ᵥ U j|)) * hsq j
  -- the linear terms vanish by Claim 2.1
  have hlin : ∑ i, ∑ j, (c i - 1) * (w i * w j * B i j) = 0 := by
    have e : ∀ i, ∑ j, (c i - 1) * (w i * w j * B i j) = L * ((c i - 1) * w i ^ 2) := by
      intro i
      have : ∑ j, (c i - 1) * (w i * w j * B i j) = (c i - 1) * w i * ∑ j, B i j * w j := by
        rw [mul_sum]
        exact sum_congr rfl fun j _ => by ring
      rw [this, hBw' i]
      ring
    simp only [e, ← mul_sum, hsumw, mul_zero]
  have hlin' : ∑ i, ∑ j, (c j - 1) * (w i * w j * B i j) = 0 := by
    rw [sum_comm]
    simpa only [hB, mul_comm (w _) (w _)] using hlin
  -- the quadratic term is a square, by condition (i)
  set y : Fin n → ℝ := fun i => (c i - 1) * w i with hy
  have hy0 : ∀ i, i ∉ C → y i = 0 := fun i hi => by simp [hy, hc1 i hi]
  have hquad : 0 ≤ ∑ i, ∑ j, (c i - 1) * (c j - 1) * (w i * w j * B i j) := by
    have e : ∀ i j, (c i - 1) * (c j - 1) * (w i * w j * B i j) = y i * y j * (U i ⬝ᵥ U j) := by
      intro i j
      by_cases hi : i ∈ C
      · by_cases hj : j ∈ C
        · simp only [hy, B, absGram, of_apply, abs_of_nonneg (hC i hi j hj)]
          ring
        · have hcj : c j - 1 = 0 := by rw [hc1 j hj]; ring
          simp [hy, hcj]
      · have hci : c i - 1 = 0 := by rw [hc1 i hi]; ring
        simp [hy, hci]
    simp only [e]
    rw [sum_mul_dotProduct_eq_sum_sq]
    exact sum_nonneg fun a _ => sq_nonneg _
  have hsig : sigma U w = ∑ i, ∑ j, w i * w j * B i j := rfl
  have hexp : sigma (cloneMatrix U c) (cloneWeight w c) - sigma U w =
      ∑ i, ∑ j, (c i - 1) * (w i * w j * B i j) + ∑ i, ∑ j, (c j - 1) * (w i * w j * B i j)
        + ∑ i, ∑ j, (c i - 1) * (c j - 1) * (w i * w j * B i j) := by
    rw [e1, hsig]
    simp only [← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  rw [hlin, hlin', zero_add, zero_add] at hexp
  rw [← h.sigma_eq]
  linarith

end Cloning

end Grunbaum.KMMP
