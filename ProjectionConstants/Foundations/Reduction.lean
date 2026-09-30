/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.Foundations.OrthProj
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Reduction to finite-dimensional `ℓ∞`-spaces

To compute the maximal absolute projection constant it suffices to consider subspaces of
`ℓ∞^N` ([Wojtaszczyk, III.B.5]):

* `relProjConst_le_of_maxRelProjConst_le` : if `λ(m, N) ≤ L` for all `N`, then `λ(Y, X) ≤ L` for
  every `m`-dimensional subspace `Y` of every normed space `X`;
* `absProjConst_le_of_maxRelProjConst_le`, `maxProjConst_le_of_maxRelProjConst_le` : the same for
  `λ(Y)` and `λ(m)`;
* `relProjConst_le_maxProjConst` : conversely, `λ(Y, ℓ∞^N) ≤ λ(m)` for `Y ⊆ ℓ∞^N`, `dim Y = m`.

Proof of the first statement. Let `ε > 0`, take a finite `ε`-net `φ₁, …, φ_N` of the unit sphere
of `Y*` and put `J y = (φₖ(y))ₖ`. Then `(1 - ε)‖y‖ ≤ ‖J y‖ ≤ ‖y‖`. Extend each `φₖ` to `X` with the
same norm (Hahn–Banach) to get `J̃ : X → ℓ∞^N` with `‖J̃‖ ≤ 1`. If `Q` is a projection of
`ℓ∞^N` onto `J(Y)`, then `J⁻¹ Q J̃` is a projection of `X` onto `Y` of norm at most
`‖Q‖/(1 - ε)`.
-/

open scoped NNReal

namespace ProjectionConstants

universe u

variable {𝕜 : Type*} [RCLike 𝕜]

section Reduction

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- **Reduction to `ℓ∞^N`.** If `λ_𝕜(m, N) ≤ L` for every `N`, then `λ(Y, X) ≤ L` for every
`m`-dimensional subspace `Y` of any normed space `X`. -/
theorem relProjConst_le_of_maxRelProjConst_le {m : ℕ} {L : ℝ}
    (hL : ∀ N, maxRelProjConst 𝕜 m N ≤ L) (Y : Submodule 𝕜 X) [FiniteDimensional 𝕜 Y]
    (hY : Module.finrank 𝕜 Y = m) : relProjConst Y ≤ L := by
  have hL0 : 0 ≤ L := (maxRelProjConst_nonneg m 0).trans (hL 0)
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  -- the accuracy `ε`
  set ε : ℝ := min (1 / 2) (δ / (2 * (L + 1))) with hε_def
  have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε ≤ 1 / 2 := min_le_left _ _
  have hε2 : ε * (2 * (L + 1)) ≤ δ := by
    have h := min_le_right (1 / 2 : ℝ) (δ / (2 * (L + 1)))
    rw [← hε_def] at h
    calc ε * (2 * (L + 1)) ≤ δ / (2 * (L + 1)) * (2 * (L + 1)) := by gcongr
      _ = δ := div_mul_cancel₀ _ (by positivity)
  -- a finite `ε`-net of the dual sphere
  have : ProperSpace (StrongDual 𝕜 Y) := FiniteDimensional.proper_rclike 𝕜 _
  obtain ⟨T, hTS, hTfin, hTcov⟩ := finite_cover_balls_of_compact
    (isCompact_sphere (0 : StrongDual 𝕜 Y) 1) hε0
  have : Fintype T := hTfin.fintype
  set N := Fintype.card T
  let e : Fin N ≃ T := (Fintype.equivFin T).symm
  let φ : Fin N → StrongDual 𝕜 Y := fun k => (e k).1
  have hφ1 : ∀ k, ‖φ k‖ = 1 := fun k => by simpa using hTS (e k).2
  have hφcov : ∀ ψ : StrongDual 𝕜 Y, ‖ψ‖ = 1 → ∃ k, ‖ψ - φ k‖ < ε := by
    intro ψ hψ
    have hψS : ψ ∈ Metric.sphere (0 : StrongDual 𝕜 Y) 1 := by simpa using hψ
    obtain ⟨χ, hχT, hχ⟩ := Set.mem_iUnion₂.1 (hTcov hψS)
    refine ⟨e.symm ⟨χ, hχT⟩, ?_⟩
    simpa [φ, dist_eq_norm] using hχ
  -- the embedding `J : Y → ℓ∞^N`
  let J : Y →L[𝕜] (Fin N → 𝕜) := ContinuousLinearMap.pi fun k => φ k
  have hJ_le : ∀ y, ‖J y‖ ≤ ‖y‖ := by
    intro y
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg y)).2 fun k => ?_
    calc ‖φ k y‖ ≤ ‖φ k‖ * ‖y‖ := (φ k).le_opNorm y
      _ = ‖y‖ := by rw [hφ1, one_mul]
  have hJ_ge : ∀ y, (1 - ε) * ‖y‖ ≤ ‖J y‖ := by
    intro y
    by_cases hy : y = 0
    · simp [hy]
    obtain ⟨ψ, hψ1, hψy⟩ := exists_dual_vector 𝕜 y (norm_ne_zero_iff.2 hy)
    obtain ⟨k, hk⟩ := hφcov ψ hψ1
    have h1 : ‖φ k y‖ ≤ ‖J y‖ := norm_le_pi_norm (J y) k
    have h2 : ‖(ψ - φ k) y‖ ≤ ε * ‖y‖ :=
      ((ψ - φ k).le_opNorm y).trans (mul_le_mul_of_nonneg_right hk.le (norm_nonneg y))
    have h3 : ‖ψ y‖ = ‖y‖ := by rw [hψy]; simp
    have h4 : ‖ψ y‖ ≤ ‖φ k y‖ + ‖(ψ - φ k) y‖ := by
      have hsub : (ψ - φ k) y = ψ y - φ k y := rfl
      rw [hsub]
      calc ‖ψ y‖ = ‖φ k y + (ψ y - φ k y)‖ := by rw [add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    nlinarith
  have hJinj : Function.Injective J := by
    intro y₁ y₂ h
    have h' : J (y₁ - y₂) = 0 := by rw [map_sub, h, sub_self]
    have := hJ_ge (y₁ - y₂)
    rw [h', norm_zero] at this
    have hpos : 0 < 1 - ε := by linarith
    have : ‖y₁ - y₂‖ ≤ 0 := by nlinarith [norm_nonneg (y₁ - y₂)]
    exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
  -- the Hahn–Banach extensions and `J̃ : X → ℓ∞^N`
  choose Φ hΦ hΦnorm using fun k => exists_extension_norm_eq Y (φ k)
  let Jt : X →L[𝕜] (Fin N → 𝕜) := ContinuousLinearMap.pi Φ
  have hJt_le : ∀ x, ‖Jt x‖ ≤ ‖x‖ := by
    intro x
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun k => ?_
    calc ‖Φ k x‖ ≤ ‖Φ k‖ * ‖x‖ := (Φ k).le_opNorm x
      _ = ‖x‖ := by rw [hΦnorm, hφ1, one_mul]
  have hJt_Y : ∀ y : Y, Jt y = J y := by
    intro y
    ext k
    exact hΦ k y
  -- the subspace `Z = J(Y) ⊆ ℓ∞^N` and a good projection `Q` onto it
  let Z : Submodule 𝕜 (Fin N → 𝕜) := LinearMap.range (J : Y →ₗ[𝕜] (Fin N → 𝕜))
  have hZ : Module.finrank 𝕜 Z = m := by
    rw [LinearMap.finrank_range_of_inj hJinj, hY]
  obtain ⟨Q, hQ, hQlt⟩ := exists_isProjectionOnto_norm_lt Z hε0
  have hQL : ‖Q‖ ≤ L + ε := by
    have := relProjConst_le_maxRelProjConst Z hZ
    linarith [hL N]
  -- the inverse of `J` on `Z`
  let eJ : Y ≃ₗ[𝕜] Z := LinearEquiv.ofInjective (J : Y →ₗ[𝕜] (Fin N → 𝕜)) hJinj
  let Jinv : Z →L[𝕜] Y := LinearMap.toContinuousLinearMap eJ.symm.toLinearMap
  have hJJinv : ∀ z : Z, J (Jinv z) = z := by
    intro z
    have h := LinearEquiv.ofInjective_apply (J : Y →ₗ[𝕜] (Fin N → 𝕜)) (h := hJinj) (eJ.symm z)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  have hJinv_le : ∀ z : Z, (1 - ε) * ‖Jinv z‖ ≤ ‖(z : Fin N → 𝕜)‖ := by
    intro z
    have := hJ_ge (Jinv z)
    rwa [hJJinv] at this
  have hJinvJ : ∀ y : Y, Jinv ⟨J y, ⟨y, rfl⟩⟩ = y := by
    intro y
    show eJ.symm _ = y
    rw [LinearEquiv.symm_apply_eq]
    ext1
    rw [LinearEquiv.ofInjective_apply]
    rfl
  -- the projection `P = J⁻¹ Q J̃` of `X` onto `Y`
  let Qc : (Fin N → 𝕜) →L[𝕜] Z := Q.codRestrict Z hQ.mem
  let P : X →L[𝕜] X := Y.subtypeL.comp (Jinv.comp (Qc.comp Jt))
  have hP : IsProjectionOnto Y P := by
    refine ⟨fun x => (Jinv (Qc (Jt x))).2, fun y hy => ?_⟩
    have h1 : Jt y = J ⟨y, hy⟩ := hJt_Y ⟨y, hy⟩
    have h2 : Qc (Jt y) = ⟨J ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩⟩ := by
      ext1
      simp only [Qc, ContinuousLinearMap.coe_codRestrict_apply, h1]
      exact hQ.map_id _ ⟨⟨y, hy⟩, rfl⟩
    simp only [P, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, h2, hJinvJ]
  have hpos : 0 < 1 - ε := by linarith
  have hPnorm : ‖P‖ ≤ (L + ε) / (1 - ε) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
    have h1 := hJinv_le (Qc (Jt x))
    have h2 : ‖((Qc (Jt x) : Z) : Fin N → 𝕜)‖ ≤ ‖Q‖ * ‖x‖ := by
      simp only [Qc, ContinuousLinearMap.coe_codRestrict_apply]
      exact (Q.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hJt_le x) (norm_nonneg _))
    have h3 : ‖P x‖ = ‖Jinv (Qc (Jt x))‖ := by simp [P]
    rw [h3, div_mul_eq_mul_div, le_div_iff₀ hpos]
    have := norm_nonneg x
    nlinarith
  calc relProjConst Y ≤ ‖P‖ := relProjConst_le Y hP
    _ ≤ (L + ε) / (1 - ε) := hPnorm
    _ ≤ L + δ := by
        rw [div_le_iff₀ hpos]
        nlinarith

end Reduction

section Absolute

/-- If `λ_𝕜(m, N) ≤ L` for all `N`, then `λ(Y) ≤ L` for every `m`-dimensional normed space. -/
theorem absProjConst_le_of_maxRelProjConst_le {m : ℕ} {L : ℝ}
    (hL : ∀ N, maxRelProjConst 𝕜 m N ≤ L) (Y : Type u) [NormedAddCommGroup Y]
    [NormedSpace 𝕜 Y] [FiniteDimensional 𝕜 Y] (hY : Module.finrank 𝕜 Y = m) :
    absProjConst 𝕜 Y ≤ L := by
  have hL0 : 0 ≤ L := (maxRelProjConst_nonneg m 0).trans (hL 0)
  refine Real.iSup_le (fun X => ?_) hL0
  have hinj : Function.Injective X.emb.toLinearMap := X.emb.injective
  have hfin : Module.finrank 𝕜 (LinearMap.range X.emb.toLinearMap) = m := by
    rw [LinearMap.finrank_range_of_inj hinj, hY]
  exact relProjConst_le_of_maxRelProjConst_le hL _ hfin

/-- If `λ_𝕜(m, N) ≤ L` for all `N`, then `λ_𝕜(m) ≤ L`. -/
theorem maxProjConst_le_of_maxRelProjConst_le {m : ℕ} {L : ℝ}
    (hL : ∀ N, maxRelProjConst 𝕜 m N ≤ L) : maxProjConst 𝕜 m ≤ L := by
  have hL0 : 0 ≤ L := (maxRelProjConst_nonneg m 0).trans (hL 0)
  exact Real.iSup_le (fun Y => absProjConst_le_of_maxRelProjConst_le hL Y.carrier Y.finrank_eq) hL0

variable {m : ℕ} {L : ℝ}

/-- `λ(Y, X) ≤ λ(Y)`: `X` is one of the superspaces of `Y`. -/
theorem relProjConst_le_absProjConst (hL : ∀ N, maxRelProjConst 𝕜 m N ≤ L) {X : Type u}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] (Y : Submodule 𝕜 X) [FiniteDimensional 𝕜 Y]
    (hY : Module.finrank 𝕜 Y = m) : relProjConst Y ≤ absProjConst 𝕜 Y := by
  have hbdd : BddAbove (Set.range fun X' : Superspace 𝕜 Y =>
      relProjConst (LinearMap.range X'.emb.toLinearMap)) :=
    ⟨L, by
      rintro _ ⟨X', rfl⟩
      have hfin : Module.finrank 𝕜 (LinearMap.range X'.emb.toLinearMap) = m := by
        rw [LinearMap.finrank_range_of_inj X'.emb.injective, hY]
      exact relProjConst_le_of_maxRelProjConst_le hL _ hfin⟩
  have h := le_ciSup hbdd (Superspace.ofSubmodule Y)
  rwa [Superspace.range_ofSubmodule] at h

/-- `λ(Y, ℓ∞^N) ≤ λ(m)` for every `m`-dimensional `Y ⊆ ℓ∞^N`. -/
theorem relProjConst_le_maxProjConst {𝕜 : Type} [RCLike 𝕜] {m : ℕ} {L : ℝ}
    (hL : ∀ N, maxRelProjConst 𝕜 m N ≤ L) {N : ℕ} (Y : Submodule 𝕜 (Fin N → 𝕜))
    (hY : Module.finrank 𝕜 Y = m) : relProjConst Y ≤ maxProjConst 𝕜 m := by
  have hbdd : BddAbove (Set.range fun Y' : FinDimNormedSpace 𝕜 m => absProjConst 𝕜 Y'.carrier) :=
    ⟨L, by
      rintro _ ⟨Y', rfl⟩
      exact absProjConst_le_of_maxRelProjConst_le hL Y'.carrier Y'.finrank_eq⟩
  have h := le_ciSup hbdd ⟨Y, hY⟩
  exact (relProjConst_le_absProjConst hL Y hY).trans h

lemma absProjConst_nonneg (Y : Type u) [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] :
    0 ≤ absProjConst 𝕜 Y :=
  Real.iSup_nonneg fun _ => relProjConst_nonneg _

lemma maxProjConst_nonneg (m : ℕ) : 0 ≤ maxProjConst 𝕜 m :=
  Real.iSup_nonneg fun Y => absProjConst_nonneg Y.carrier

/-- **Reduction to `ℓ∞^N`.** `λ_𝕜(m) = sup_N λ_𝕜(m, N)`. -/
theorem maxProjConst_eq_iSup {𝕜 : Type} [RCLike 𝕜] {m : ℕ} {L : ℝ}
    (hL : ∀ N, maxRelProjConst 𝕜 m N ≤ L) :
    maxProjConst 𝕜 m = ⨆ N, maxRelProjConst 𝕜 m N := by
  have hbdd : BddAbove (Set.range fun N => maxRelProjConst 𝕜 m N) :=
    ⟨L, by rintro _ ⟨N, rfl⟩; exact hL N⟩
  refine le_antisymm (maxProjConst_le_of_maxRelProjConst_le fun N => le_ciSup hbdd N) ?_
  exact Real.iSup_le (fun N => Real.iSup_le (fun Y => relProjConst_le_maxProjConst hL Y.1 Y.2)
    (maxProjConst_nonneg m)) (maxProjConst_nonneg m)

end Absolute

end ProjectionConstants
