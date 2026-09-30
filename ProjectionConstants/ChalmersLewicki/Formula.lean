/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.ChalmersLewicki.LowerBound

/-!
# The formula of Chalmers and Lewicki (Theorem 1.1)

**Theorem 1.1** ([Chalmers–Lewicki 2009, Thms 2.1–2.2], [Foucart–Skrzypek 2017, App. A]).
For all integers `m, N`,
`λ_𝕜(m, N) = max { ∑ᵢⱼ tᵢ tⱼ |(Uᴴ U)ᵢⱼ| : t ∈ ℝ^N_+, ‖t‖ = 1, U ∈ 𝕜^{m×N}, U Uᴴ = I_m }`.

In Lean: `maxRelProjConst_eq_clConst` (with orthogonal projections `P = Uᴴ U`), and
`maxRelProjConst_eq_sSup_parseval` in the literal form of the paper. The maximum is attained
(`exists_clConst_eq`).

Consequences recorded here:
* `maxRelProjConst_le_sqrt` : `λ(m, N) ≤ √m`;
* `quasiRelConst_le_maxRelProjConst` : `μ(m, N) ≤ λ(m, N)`.
-/

open Matrix Finset

namespace ProjectionConstants

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Theorem 1.1 (Chalmers–Lewicki).** `λ_𝕜(m, N) = sup { ∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| }`, the supremum over
unit weights `t ≥ 0` and orthogonal projections `P` of rank `m`. -/
theorem maxRelProjConst_eq_clConst (m N : ℕ) : maxRelProjConst 𝕜 m N = clConst 𝕜 (Fin N) m :=
  le_antisymm (Real.iSup_le (fun Y => relProjConst_le_clConst Y.1 Y.2) clConst_nonneg)
    (clConst_le_maxRelProjConst m N)

/-- **Theorem 1.1**, in the formulation of the paper. -/
theorem maxRelProjConst_eq_sSup_parseval (m N : ℕ) :
    maxRelProjConst 𝕜 m N = sSup {x | ∃ (t : Fin N → ℝ) (U : Matrix (Fin m) (Fin N) 𝕜),
      (∀ i, 0 ≤ t i) ∧ ∑ i, t i ^ 2 = 1 ∧ U * Uᴴ = 1 ∧
        x = ∑ i, ∑ j, t i * t j * ‖(Uᴴ * U) i j‖} := by
  rw [maxRelProjConst_eq_clConst, clConst_eq_sSup_parseval]

lemma maxRelProjConst_le_sqrt (m N : ℕ) : maxRelProjConst 𝕜 m N ≤ √m := by
  rw [maxRelProjConst_eq_clConst]; exact clConst_le_sqrt

lemma quasiRelConst_le_maxRelProjConst (m N : ℕ) :
    quasiRelConst 𝕜 (Fin N) m ≤ maxRelProjConst 𝕜 m N := by
  rw [maxRelProjConst_eq_clConst]; exact quasiRelConst_le_clConst

/-! ### The maximum is attained -/

section Attained

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (ι) in
/-- The set of unit weights `{t ≥ 0 : ‖t‖ = 1}`. -/
def unitWeights : Set (ι → ℝ) := {t | IsUnitWeight t}

omit [DecidableEq ι] in
lemma isCompact_unitWeights : IsCompact (unitWeights ι) := by
  have hsub : unitWeights ι ⊆ Set.univ.pi fun _ : ι => Set.Icc (0 : ℝ) 1 := by
    intro t ht i _
    refine ⟨ht.nonneg i, ?_⟩
    have h := single_le_sum (f := fun i => t i ^ 2) (fun j _ => sq_nonneg (t j)) (mem_univ i)
    rw [ht.sum_sq] at h
    nlinarith [ht.nonneg i]
  refine (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset ?_ hsub
  have h1 : IsClosed {t : ι → ℝ | ∀ i, 0 ≤ t i} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have h2 : IsClosed {t : ι → ℝ | ∑ i, t i ^ 2 = 1} :=
    isClosed_eq (continuous_finsetSum _ fun i _ => (continuous_apply i).pow 2) continuous_const
  have : unitWeights ι = {t : ι → ℝ | ∀ i, 0 ≤ t i} ∩ {t | ∑ i, t i ^ 2 = 1} := by
    ext t; exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [this]
  exact h1.inter h2

/-- The supremum in Theorem 1.1 is a maximum. -/
theorem exists_clConst_eq {m : ℕ} (hm : m ≤ Fintype.card ι) [Nonempty ι] :
    ∃ t P, IsUnitWeight t ∧ P ∈ orthProjs 𝕜 ι m ∧ weightedAbsSum t P = clConst 𝕜 ι m := by
  obtain ⟨P₀, hP₀⟩ := orthProjs_nonempty (𝕜 := 𝕜) hm
  have hK : IsCompact (unitWeights ι ×ˢ orthProjs 𝕜 ι m) :=
    isCompact_unitWeights.prod (isCompact_orthProjs m)
  have hcont : Continuous fun p : (ι → ℝ) × Matrix ι ι 𝕜 => weightedAbsSum p.1 p.2 :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (((continuous_apply i).comp continuous_fst).mul ((continuous_apply j).comp continuous_fst)).mul
        ((continuous_apply_apply i j).comp continuous_snd).norm
  obtain ⟨⟨t, P⟩, ⟨ht, hP⟩, hmax⟩ := hK.exists_isMaxOn
    ⟨(_, P₀), isUnitWeight_uniform, hP₀⟩ hcont.continuousOn
  refine ⟨t, P, ht, hP, le_antisymm (le_clConst ht hP) (clConst_le ?_ fun t' P' ht' hP' => ?_)⟩
  · exact weightedAbsSum_nonneg ht.nonneg P
  · exact hmax (Set.mk_mem_prod ht' hP')

/-- The supremum defining `μ(m, N)` is a maximum. -/
theorem exists_quasiRelConst_eq {m : ℕ} (hm : m ≤ Fintype.card ι) :
    ∃ P ∈ orthProjs 𝕜 ι m, absSum P / Fintype.card ι = quasiRelConst 𝕜 ι m := by
  obtain ⟨P₀, hP₀⟩ := orthProjs_nonempty (𝕜 := 𝕜) hm
  have hcont : Continuous fun P : Matrix ι ι 𝕜 => absSum P / Fintype.card ι :=
    (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (continuous_apply_apply i j).norm).div_const _
  obtain ⟨P, hP, hmax⟩ := (isCompact_orthProjs m).exists_isMaxOn ⟨P₀, hP₀⟩ hcont.continuousOn
  exact ⟨P, hP, le_antisymm (le_quasiRelConst hP)
    (quasiRelConst_le (div_nonneg (absSum_nonneg P) (Nat.cast_nonneg _)) fun P' hP' => hmax hP')⟩

end Attained

end ProjectionConstants
