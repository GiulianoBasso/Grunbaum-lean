/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.ChalmersLewicki.Defs
import Mathlib.Topology.Sion
import Mathlib.Topology.Semicontinuity.Basic

/-!
# The Chalmers–Lewicki formula: the upper bound

**Theorem.** If `Y ⊆ ℓ∞^ι` is a subspace of dimension `m`, then
`λ(Y, ℓ∞^ι) ≤ sup { ∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| : t ≥ 0, ‖t‖ = 1, P ∈ 𝒫ₘ(ι) }` (`relProjConst_le_clConst`).

Proof. The norm of a projection `R` onto `Y` is `maxᵢ rᵢ(R)` with `rᵢ(R) = ∑ⱼ |Rᵢⱼ|`, which is
`max { ∑ᵢ wᵢ rᵢ(R) : w ∈ Δ }` over the simplex `Δ`. The function `(w, R) ↦ ∑ᵢ wᵢ rᵢ(R)` is linear in
`w` and convex in `R`, and `Δ` is compact, so by **Sion's minimax theorem**
`λ(Y) = inf_R max_w = sup_w inf_R ∑ᵢ wᵢ rᵢ(R)`.
For fixed `w`, rescale: with `sᵢ² = (wᵢ + ε)/(1 + Nε)` and `D = diag(s)`, let `Q` be the orthogonal
projection onto `DY`. Then `R = D⁻¹ Q D` is a projection onto `Y` with
`∑ᵢ wᵢ rᵢ(R) ≤ (1 + Nε) ∑ᵢⱼ sᵢ sⱼ |Qᵢⱼ|`.
Letting `ε → 0` gives the claim.
-/

open Matrix Finset

namespace ProjectionConstants

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The simplex -/

variable (ι) in
/-- The probability simplex `Δ = { w ≥ 0 : ∑ wᵢ = 1 }`. -/
def probSimplex : Set (ι → ℝ) := {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}

omit [DecidableEq ι] in
lemma convex_probSimplex : Convex ℝ (probSimplex ι) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hx.1 i; have := hy.1 i; positivity
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum, hx.2, hy.2,
      mul_one, hab]

omit [DecidableEq ι] in
lemma isCompact_probSimplex : IsCompact (probSimplex ι) := by
  have hsub : probSimplex ι ⊆ Set.univ.pi fun _ : ι => Set.Icc (0 : ℝ) 1 := by
    intro w hw i _
    refine ⟨hw.1 i, ?_⟩
    rw [← hw.2]
    exact single_le_sum (fun j _ => hw.1 j) (mem_univ i)
  refine (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset ?_ hsub
  have h1 : IsClosed {w : ι → ℝ | ∀ i, 0 ≤ w i} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have h2 : IsClosed {w : ι → ℝ | ∑ i, w i = 1} :=
    isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
  exact h1.inter h2

lemma single_mem_probSimplex (i : ι) : (Pi.single i 1 : ι → ℝ) ∈ probSimplex ι :=
  ⟨fun j => by by_cases h : j = i <;> simp [h], by simp⟩

/-! ### The weighted row sums -/

/-- `∑ᵢ wᵢ ∑ⱼ |Pᵢⱼ|`. -/
noncomputable def rowWeighted (w : ι → ℝ) (P : Matrix ι ι 𝕜) : ℝ := ∑ i, w i * ∑ j, ‖P i j‖

omit [DecidableEq ι] in
lemma rowWeighted_nonneg {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (P : Matrix ι ι 𝕜) :
    0 ≤ rowWeighted w P :=
  sum_nonneg fun i _ => mul_nonneg (hw i) (sum_nonneg fun _ _ => norm_nonneg _)

omit [DecidableEq ι] in
lemma rowWeighted_le_rowSumNorm {w : ι → ℝ} (hw : w ∈ probSimplex ι) (P : Matrix ι ι 𝕜) :
    rowWeighted w P ≤ rowSumNorm P := by
  calc rowWeighted w P ≤ ∑ i, w i * rowSumNorm P :=
        sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (row_le_rowSumNorm P i) (hw.1 i)
    _ = rowSumNorm P := by rw [← sum_mul, hw.2, one_mul]

lemma isLUB_rowWeighted [Nonempty ι] (P : Matrix ι ι 𝕜) :
    IsLUB {x | ∃ w ∈ probSimplex ι, rowWeighted w P = x} (rowSumNorm P) := by
  obtain ⟨i, hi⟩ := exists_row_eq_rowSumNorm P
  refine IsGreatest.isLUB ⟨⟨Pi.single i 1, single_mem_probSimplex i, ?_⟩, ?_⟩
  · rw [← hi, rowWeighted, Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [hj]
    · simp
  · rintro _ ⟨w, hw, rfl⟩
    exact rowWeighted_le_rowSumNorm hw P

/-! ### Convexity -/

omit [DecidableEq ι] in
lemma convexOn_rowWeighted {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) {K : Set (Matrix ι ι 𝕜)}
    (hK : Convex ℝ K) : ConvexOn ℝ K (rowWeighted w) := by
  refine ⟨hK, fun P _ Q _ a b ha hb _ => ?_⟩
  simp only [rowWeighted, smul_eq_mul, mul_sum]
  rw [← sum_add_distrib]
  refine sum_le_sum fun i _ => ?_
  rw [← sum_add_distrib]
  refine sum_le_sum fun j _ => ?_
  have h : ‖(a • P + b • Q) i j‖ ≤ a * ‖P i j‖ + b * ‖Q i j‖ := by
    simp only [Matrix.add_apply, Matrix.smul_apply]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
  have := hw i
  nlinarith

omit [DecidableEq ι] in
lemma continuous_rowWeighted_left (P : Matrix ι ι 𝕜) :
    Continuous fun w : ι → ℝ => rowWeighted w P :=
  continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const

omit [DecidableEq ι] in
lemma continuous_rowWeighted_right (w : ι → ℝ) :
    Continuous fun P : Matrix ι ι 𝕜 => rowWeighted w P :=
  continuous_finsetSum _ fun i _ => continuous_const.mul
    (continuous_finsetSum _ fun j _ => (continuous_apply_apply i j).norm)

/-! ### Projections onto `Y` form a convex set -/

variable (Y : Submodule 𝕜 (ι → 𝕜))

/-- The (matrix) projections onto `Y`. -/
def matProjs : Set (Matrix ι ι 𝕜) := {P | IsMatrixProjOnto Y P}

omit [DecidableEq ι] in
lemma convex_matProjs : Convex ℝ (matProjs Y) := by
  intro P hP Q hQ a b _ _ hab
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
    refine Y.add_mem ?_ ?_
    · rw [RCLike.real_smul_eq_coe_smul (K := 𝕜)]; exact Y.smul_mem _ (hP.mem x)
    · rw [RCLike.real_smul_eq_coe_smul (K := 𝕜)]; exact Y.smul_mem _ (hQ.mem x)
  · rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, hP.map_id y hy,
      hQ.map_id y hy, ← add_smul, hab, one_smul]

lemma matProjs_nonempty : (matProjs Y).Nonempty := exists_isMatrixProjOnto Y

/-! ### The rescaling step -/

/-- For every weight `w ∈ Δ` there are projections onto `Y` whose weighted row sums are at most
`(1 + Nε) · clConst`. -/
theorem exists_matProj_rowWeighted_le {m : ℕ} (hm : Module.finrank 𝕜 Y = m)
    {w : ι → ℝ} (hw : w ∈ probSimplex ι) {ε : ℝ} (hε : 0 < ε) :
    ∃ P ∈ matProjs Y, rowWeighted w P ≤ (1 + Fintype.card ι * ε) * clConst 𝕜 ι m := by
  set N : ℝ := (Fintype.card ι : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hNε : 0 < 1 + N * ε := by positivity
  -- the rescaling weights `sᵢ = √((wᵢ + ε)/(1 + Nε))`
  set s : ι → ℝ := fun i => √((w i + ε) / (1 + N * ε)) with hs_def
  have hs_pos : ∀ i, 0 < s i := fun i => Real.sqrt_pos.2 (div_pos (by linarith [hw.1 i]) hNε)
  have hs_sq : ∀ i, s i ^ 2 = (w i + ε) / (1 + N * ε) := fun i =>
    Real.sq_sqrt (div_nonneg (by linarith [hw.1 i]) hNε.le)
  have hs_unit : IsUnitWeight s := by
    refine ⟨fun i => (hs_pos i).le, ?_⟩
    simp only [hs_sq, ← sum_div, sum_add_distrib, hw.2, sum_const, card_univ, nsmul_eq_mul]
    rw [div_self hNε.ne']
  -- the diagonal matrices
  set D : Matrix ι ι 𝕜 := diagonal fun i => (s i : 𝕜) with hD
  set Dinv : Matrix ι ι 𝕜 := diagonal fun i => ((s i)⁻¹ : 𝕜) with hDinv
  have hDD : Dinv * D = 1 := by
    rw [hDinv, hD, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext i
    have : (s i : 𝕜) ≠ 0 := by exact_mod_cast (hs_pos i).ne'
    field_simp
  have hDD' : D * Dinv = 1 := by
    rw [hDinv, hD, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext i
    have : (s i : 𝕜) ≠ 0 := by exact_mod_cast (hs_pos i).ne'
    field_simp
  -- the rescaled subspace `Y' = D Y` and its orthogonal projection `Q`
  set Y' := Y.map (Matrix.toLin' D) with hY'
  have hinj : Function.Injective (Matrix.toLin' D) := by
    intro x y hxy
    have := congrArg (fun z => Dinv *ᵥ z) hxy
    simpa [Matrix.mulVec_mulVec, hDD] using this
  have hm' : Module.finrank 𝕜 Y' = m := by
    rw [hY', ← hm]
    exact (Submodule.equivMapOfInjective _ hinj Y).finrank_eq.symm
  obtain ⟨Q, hQ, hQrange⟩ := exists_mem_orthProjs_range Y' hm'
  -- the projection `P = D⁻¹ Q D` onto `Y`
  refine ⟨Dinv * Q * D, ⟨fun x => ?_, fun y hy => ?_⟩, ?_⟩
  · have hmem : Q *ᵥ (D *ᵥ x) ∈ Y' := by rw [← hQrange]; exact ⟨D *ᵥ x, by simp⟩
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 hmem
    rw [Matrix.toLin'_apply] at hyx
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← hyx, mulVec_mulVec, hDD, one_mulVec]
    exact hy
  · have hmem : D *ᵥ y ∈ LinearMap.range (Matrix.toLin' Q) := by
      rw [hQrange]; exact ⟨y, hy, by simp⟩
    obtain ⟨z, hz⟩ := hmem
    rw [Matrix.toLin'_apply] at hz
    have hQQ : Q *ᵥ (Q *ᵥ z) = Q *ᵥ z := by rw [mulVec_mulVec, hQ.1.idem]
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← hz, hQQ, hz, mulVec_mulVec, hDD, one_mulVec]
  · -- the estimate
    have hentry : ∀ i j, (Dinv * Q * D) i j = ((s i)⁻¹ : 𝕜) * Q i j * (s j : 𝕜) := by
      intro i j
      rw [hDinv, hD, mul_diagonal, diagonal_mul]
    have hnorm : ∀ i j, ‖(Dinv * Q * D) i j‖ = (s i)⁻¹ * s j * ‖Q i j‖ := by
      intro i j
      rw [hentry, norm_mul, norm_mul, norm_inv, RCLike.norm_ofReal, RCLike.norm_ofReal,
        abs_of_pos (hs_pos i), abs_of_pos (hs_pos j)]
      ring
    have hw_le : ∀ i, w i ≤ (1 + N * ε) * s i ^ 2 := by
      intro i
      rw [hs_sq, mul_div_cancel₀ _ hNε.ne']
      linarith
    calc rowWeighted w (Dinv * Q * D)
        ≤ ∑ i, (1 + N * ε) * s i ^ 2 * ∑ j, ‖(Dinv * Q * D) i j‖ :=
          sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hw_le i)
            (sum_nonneg fun _ _ => norm_nonneg _)
      _ = (1 + N * ε) * weightedAbsSum s Q := by
          rw [weightedAbsSum, mul_sum]
          refine sum_congr rfl fun i _ => ?_
          simp only [hnorm, mul_sum]
          refine sum_congr rfl fun j _ => ?_
          have := (hs_pos i).ne'
          field_simp
      _ ≤ (1 + N * ε) * clConst 𝕜 ι m :=
          mul_le_mul_of_nonneg_left (le_clConst hs_unit hQ) hNε.le

/-! ### Sion's minimax theorem -/

/-- The inner infimum `g(w) = inf { ∑ᵢ wᵢ rᵢ(P) : P projection onto Y }`. -/
noncomputable def innerInf (w : ι → ℝ) : ℝ := sInf ((rowWeighted w) '' matProjs Y)

lemma isGLB_innerInf {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) :
    IsGLB ((rowWeighted w) '' matProjs Y) (innerInf Y w) :=
  isGLB_csInf ((matProjs_nonempty Y).image _)
    ⟨0, by rintro _ ⟨P, -, rfl⟩; exact rowWeighted_nonneg hw P⟩

lemma innerInf_le_clConst {m : ℕ} (hm : Module.finrank 𝕜 Y = m) {w : ι → ℝ}
    (hw : w ∈ probSimplex ι) : innerInf Y w ≤ clConst 𝕜 ι m := by
  have hC := clConst_nonneg (𝕜 := 𝕜) (ι := ι) (m := m)
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set N : ℝ := (Fintype.card ι : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  set ε := δ / (N * clConst 𝕜 ι m + 1) with hε_def
  have hε : 0 < ε := div_pos hδ (by positivity)
  obtain ⟨P, hP, hle⟩ := exists_matProj_rowWeighted_le Y hm hw hε
  have h1 : innerInf Y w ≤ rowWeighted w P := (isGLB_innerInf Y hw.1).1 ⟨P, hP, rfl⟩
  have h2 : N * ε * clConst 𝕜 ι m ≤ δ := by
    rw [hε_def]
    rw [show N * (δ / (N * clConst 𝕜 ι m + 1)) * clConst 𝕜 ι m =
      δ * (N * clConst 𝕜 ι m / (N * clConst 𝕜 ι m + 1)) by ring]
    have : N * clConst 𝕜 ι m / (N * clConst 𝕜 ι m + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    nlinarith
  nlinarith

/-- A negated version of `IsGLB`, for use with the minimax theorem. -/
lemma isLUB_neg_image {α : Type*} {F : α → ℝ} {K : Set α} {a : ℝ} (h : IsGLB (F '' K) a) :
    IsLUB {x | ∃ P ∈ K, -F P = x} (-a) := by
  refine ⟨?_, fun b hb => ?_⟩
  · rintro _ ⟨P, hP, rfl⟩
    exact neg_le_neg (h.1 ⟨P, hP, rfl⟩)
  · have : -b ≤ a := h.2 fun _ ⟨P, hP, hy⟩ => by
      rw [← hy]; have := hb ⟨P, hP, rfl⟩; linarith
    linarith

lemma isGLB_neg_image {α : Type*} {F : α → ℝ} {K : Set α} {a : ℝ} (h : IsLUB (F '' K) a) :
    IsGLB {x | ∃ P ∈ K, -F P = x} (-a) := by
  refine ⟨?_, fun b hb => ?_⟩
  · rintro _ ⟨P, hP, rfl⟩
    exact neg_le_neg (h.1 ⟨P, hP, rfl⟩)
  · have : a ≤ -b := h.2 fun _ ⟨P, hP, hy⟩ => by
      rw [← hy]; have := hb ⟨P, hP, rfl⟩; linarith
    linarith

/-- **Minimax**: `inf_P maxᵢ rᵢ(P) = sup_w inf_P ∑ᵢ wᵢ rᵢ(P)`. -/
theorem sInf_rowSumNorm_eq_sSup_innerInf [Nonempty ι] :
    sInf (rowSumNorm '' matProjs Y) = sSup (innerInf Y '' probSimplex ι) := by
  obtain ⟨P₀, hP₀⟩ := matProjs_nonempty Y
  have hne : (probSimplex ι).Nonempty := ⟨_, single_mem_probSimplex (Classical.arbitrary ι)⟩
  -- the sup over `w` of the inner infima is attained as an `IsLUB`
  have hbdd : BddAbove (innerInf Y '' probSimplex ι) :=
    ⟨rowSumNorm P₀, by
      rintro _ ⟨w, hw, rfl⟩
      exact ((isGLB_innerInf Y hw.1).1 ⟨P₀, hP₀, rfl⟩).trans (rowWeighted_le_rowSumNorm hw P₀)⟩
  have hLUB : IsLUB (innerInf Y '' probSimplex ι) (sSup (innerInf Y '' probSimplex ι)) :=
    isLUB_csSup (hne.image _) hbdd
  have hGLB : IsGLB (rowSumNorm '' matProjs Y) (sInf (rowSumNorm '' matProjs Y)) :=
    isGLB_csInf ((matProjs_nonempty Y).image _)
      ⟨0, by rintro _ ⟨P, -, rfl⟩; exact rowSumNorm_nonneg P⟩
  have key := Sion.minimax (E := ι → ℝ) (F := Matrix ι ι 𝕜) (β := ℝ)
    (X := probSimplex ι) (Y := matProjs Y) (f := fun w P => -rowWeighted w P)
    hne isCompact_probSimplex
    (fun P _ => (continuous_rowWeighted_left P).neg.lowerSemicontinuous.lowerSemicontinuousOn _)
    (fun P _ => by
      refine ConvexOn.quasiconvexOn ⟨convex_probSimplex, fun x _ y _ a b _ _ hab => le_of_eq ?_⟩
      simp only [rowWeighted, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, sum_add_distrib,
        mul_assoc, ← mul_sum]
      ring)
    (convex_matProjs Y)
    (fun w _ => (continuous_rowWeighted_right w).neg.upperSemicontinuous.upperSemicontinuousOn _)
    (fun w hw => ((convexOn_rowWeighted hw.1 (convex_matProjs Y)).neg).quasiconcaveOn)
    convex_probSimplex
    (fun w => -innerInf Y w) (fun w hw => isLUB_neg_image (isGLB_innerInf Y hw.1))
    (-sSup (innerInf Y '' probSimplex ι)) (isGLB_neg_image hLUB)
    (fun P => -rowSumNorm P) (fun P _ => by
      have := isGLB_neg_image (F := fun w => rowWeighted w P) (K := probSimplex ι)
        (a := rowSumNorm P) (by simpa [Set.image] using isLUB_rowWeighted P)
      simpa using this)
    (-sInf (rowSumNorm '' matProjs Y)) (isLUB_neg_image hGLB)
  linarith

/-- **Chalmers–Lewicki, upper bound.** For every `m`-dimensional `Y ⊆ ℓ∞^ι`,
`λ(Y, ℓ∞^ι) ≤ sup { ∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| }`. -/
theorem relProjConst_le_clConst {m : ℕ} (hm : Module.finrank 𝕜 Y = m) :
    relProjConst Y ≤ clConst 𝕜 ι m := by
  cases isEmpty_or_nonempty ι
  · -- in the trivial space every projection is zero
    have h0 : IsMatrixProjOnto Y (0 : Matrix ι ι 𝕜) :=
      ⟨fun x => by rw [Subsingleton.elim (0 *ᵥ x) 0]; exact Y.zero_mem,
        fun y _ => Subsingleton.elim _ _⟩
    refine (relProjConst_le_rowSumNorm Y h0).trans ?_
    rw [show rowSumNorm (0 : Matrix ι ι 𝕜) = 0 by simp [rowSumNorm]]
    exact clConst_nonneg
  · have h1 : relProjConst Y ≤ sInf (rowSumNorm '' matProjs Y) :=
      le_csInf ((matProjs_nonempty Y).image _) (by
        rintro _ ⟨P, hP, rfl⟩; exact relProjConst_le_rowSumNorm Y hP)
    rw [sInf_rowSumNorm_eq_sSup_innerInf] at h1
    refine h1.trans (csSup_le ?_ ?_)
    · exact ⟨_, _, single_mem_probSimplex (Classical.arbitrary ι), rfl⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact innerInf_le_clConst Y hm hw

end ProjectionConstants
