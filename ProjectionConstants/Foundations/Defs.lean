/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Authors: Giuliano Basso, Claude
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Complemented
import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.RCLike.Basic

/-!
# Projection constants

Let `X` be a normed space over `𝕜 = ℝ` or `ℂ` and let `Y ⊆ X` be a finite-dimensional subspace.

* `IsProjectionOnto Y P` : the bounded operator `P : X → X` is a projection onto `Y`,
  i.e. `P(X) ⊆ Y` and `P|_Y = id`.
* `relProjConst Y` : the **relative projection constant** `λ(Y, X) = inf ‖P‖`, the infimum over
  all projections of `X` onto `Y`.
* `absProjConst 𝕜 Y` : the **absolute projection constant** `λ(Y) = sup λ(Y, X)`, the supremum over
  all normed spaces `X` containing `Y` isometrically (`Superspace`).
* `maxProjConst 𝕜 m` : the **maximal absolute projection constant**
  `λ_𝕜(m) = sup { λ(Y) : dim Y = m }`, the supremum over all `m`-dimensional normed spaces.

These are the notions of [Deręgowska–Lewandowska, §1]. The fact that the suprema are finite, and
the reduction to finite-dimensional `ℓ∞`-spaces, are proved in `Foundations/Reduction.lean`.
-/

open scoped NNReal

namespace ProjectionConstants

universe u

section Relative

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- `P` is a (bounded linear) **projection of `X` onto `Y`**: `P(X) ⊆ Y` and `P y = y` for
`y ∈ Y`. -/
structure IsProjectionOnto (Y : Submodule 𝕜 X) (P : X →L[𝕜] X) : Prop where
  mem : ∀ x, P x ∈ Y
  map_id : ∀ y ∈ Y, P y = y

/-- The **relative projection constant** `λ(Y, X) = inf { ‖P‖ : P projection of X onto Y }`. -/
noncomputable def relProjConst (Y : Submodule 𝕜 X) : ℝ :=
  sInf ((fun P : X →L[𝕜] X => ‖P‖) '' {P | IsProjectionOnto Y P})

variable (Y : Submodule 𝕜 X)

/-- Finite-dimensional subspaces are complemented: there is a projection onto `Y`. -/
theorem exists_isProjectionOnto [FiniteDimensional 𝕜 Y] :
    ∃ P : X →L[𝕜] X, IsProjectionOnto Y P := by
  obtain ⟨f, hf⟩ := Submodule.ClosedComplemented.of_finiteDimensional Y
  refine ⟨Y.subtypeL.comp f, ⟨fun x => (f x).2, fun y hy => ?_⟩⟩
  simpa using congrArg Subtype.val (hf ⟨y, hy⟩)

lemma relProjConst_nonneg : 0 ≤ relProjConst Y :=
  Real.sInf_nonneg (by rintro _ ⟨P, -, rfl⟩; exact norm_nonneg _)

lemma relProjConst_le {P : X →L[𝕜] X} (hP : IsProjectionOnto Y P) : relProjConst Y ≤ ‖P‖ :=
  csInf_le ⟨0, by rintro _ ⟨Q, -, rfl⟩; exact norm_nonneg _⟩ ⟨P, hP, rfl⟩

lemma le_relProjConst [FiniteDimensional 𝕜 Y] {c : ℝ}
    (h : ∀ P : X →L[𝕜] X, IsProjectionOnto Y P → c ≤ ‖P‖) : c ≤ relProjConst Y := by
  obtain ⟨P, hP⟩ := exists_isProjectionOnto Y
  exact le_csInf ⟨_, P, hP, rfl⟩ (by rintro _ ⟨Q, hQ, rfl⟩; exact h Q hQ)

/-- For every `ε > 0` there is a projection of norm at most `λ(Y, X) + ε`. -/
lemma exists_isProjectionOnto_norm_lt [FiniteDimensional 𝕜 Y] {ε : ℝ} (hε : 0 < ε) :
    ∃ P : X →L[𝕜] X, IsProjectionOnto Y P ∧ ‖P‖ < relProjConst Y + ε := by
  obtain ⟨P, hP⟩ := exists_isProjectionOnto Y
  have hne : ((fun P : X →L[𝕜] X => ‖P‖) '' {P | IsProjectionOnto Y P}).Nonempty :=
    ⟨_, P, hP, rfl⟩
  obtain ⟨_, ⟨Q, hQ, rfl⟩, h⟩ := exists_lt_of_csInf_lt hne
    (lt_add_of_pos_right (relProjConst Y) hε)
  exact ⟨Q, hQ, h⟩

/-- A nonzero subspace has relative projection constant at least `1`. -/
lemma one_le_relProjConst [FiniteDimensional 𝕜 Y] (hY : Y ≠ ⊥) : 1 ≤ relProjConst Y := by
  refine le_relProjConst Y fun P hP => ?_
  obtain ⟨y, hyY, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY
  have h := P.le_opNorm y
  rw [hP.map_id y hyY] at h
  exact le_of_mul_le_mul_right (by simpa using h) (norm_pos_iff.2 hy0)

end Relative

section Absolute

/-- A **superspace** of a normed space `Y`: a normed space `X` together with a linear isometric
embedding `Y → X`. -/
structure Superspace (𝕜 : Type*) [RCLike 𝕜] (Y : Type u) [NormedAddCommGroup Y]
    [NormedSpace 𝕜 Y] where
  /-- The ambient space. -/
  carrier : Type u
  [normedAddCommGroup : NormedAddCommGroup carrier]
  [normedSpace : NormedSpace 𝕜 carrier]
  /-- The isometric embedding of `Y` into the ambient space. -/
  emb : Y →ₗᵢ[𝕜] carrier

attribute [instance] Superspace.normedAddCommGroup Superspace.normedSpace

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The **absolute projection constant** `λ(Y) = sup { λ(Y, X) : Y ⊆ X }`, the supremum over all
normed spaces `X` containing `Y` isometrically. -/
noncomputable def absProjConst (Y : Type u) [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] : ℝ :=
  ⨆ X : Superspace 𝕜 Y, relProjConst (LinearMap.range X.emb.toLinearMap)

/-- A finite-dimensional normed space of dimension `m` (bundled). -/
structure FinDimNormedSpace (m : ℕ) where
  /-- The underlying type. -/
  carrier : Type
  [normedAddCommGroup : NormedAddCommGroup carrier]
  [normedSpace : NormedSpace 𝕜 carrier]
  [finiteDimensional : FiniteDimensional 𝕜 carrier]
  finrank_eq : Module.finrank 𝕜 carrier = m

attribute [instance] FinDimNormedSpace.normedAddCommGroup FinDimNormedSpace.normedSpace
  FinDimNormedSpace.finiteDimensional

/-- The **maximal absolute projection constant** `λ_𝕜(m) = sup { λ(Y) : dim Y = m }`. -/
noncomputable def maxProjConst (m : ℕ) : ℝ :=
  ⨆ Y : FinDimNormedSpace 𝕜 m, absProjConst 𝕜 Y.carrier

variable {𝕜}

/-- The subspace `Y ⊆ X`, regarded as a superspace of the normed space `Y`. -/
def Superspace.ofSubmodule {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (Y : Submodule 𝕜 X) : Superspace 𝕜 Y :=
  ⟨X, Y.subtypeₗᵢ⟩

@[simp] lemma Superspace.range_ofSubmodule {X : Type u} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (Y : Submodule 𝕜 X) :
    LinearMap.range (Superspace.ofSubmodule Y).emb.toLinearMap = Y :=
  Submodule.range_subtype Y

end Absolute

end ProjectionConstants
