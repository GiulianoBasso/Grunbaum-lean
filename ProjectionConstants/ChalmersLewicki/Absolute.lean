/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.ChalmersLewicki.Formula
import ProjectionConstants.Foundations.Reduction

/-!
# The maximal absolute projection constant via the Chalmers–Lewicki formula

Combining Theorem 1.1 with the reduction to `ℓ∞^N`:

* `maxProjConst_eq_iSup_maxRelProjConst` : `λ_𝕜(m) = sup_N λ_𝕜(m, N)`;
* `maxProjConst_eq_iSup_clConst` : `λ_𝕜(m) = sup_N sup { ∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| }`;
* `relProjConst_le_sqrt`, `absProjConst_le_sqrt`, `maxProjConst_le_sqrt` : the
  **Kadec–Snobar theorem** `λ(Y) ≤ √m` for every `m`-dimensional normed space;
* `weightedAbsSum_le_maxProjConst` : every configuration gives a lower bound for `λ_𝕜(m)`.
-/

namespace ProjectionConstants

universe u

variable {𝕜 : Type*} [RCLike 𝕜]

lemma maxRelProjConst_le_sqrt' (m : ℕ) : ∀ N, maxRelProjConst 𝕜 m N ≤ √m :=
  fun N => maxRelProjConst_le_sqrt m N

/-- **Kadec–Snobar.** `λ(Y, X) ≤ √m` for every `m`-dimensional subspace of a normed space. -/
theorem relProjConst_le_sqrt {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (Y : Submodule 𝕜 X) [FiniteDimensional 𝕜 Y] {m : ℕ} (hY : Module.finrank 𝕜 Y = m) :
    relProjConst Y ≤ √m :=
  relProjConst_le_of_maxRelProjConst_le (maxRelProjConst_le_sqrt' m) Y hY

/-- **Kadec–Snobar.** `λ(Y) ≤ √m` for every `m`-dimensional normed space `Y`. -/
theorem absProjConst_le_sqrt (Y : Type u) [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [FiniteDimensional 𝕜 Y] {m : ℕ} (hY : Module.finrank 𝕜 Y = m) : absProjConst 𝕜 Y ≤ √m :=
  absProjConst_le_of_maxRelProjConst_le (maxRelProjConst_le_sqrt' m) Y hY

/-- **Kadec–Snobar.** `λ_𝕜(m) ≤ √m`. -/
theorem maxProjConst_le_sqrt (m : ℕ) : maxProjConst 𝕜 m ≤ √m :=
  maxProjConst_le_of_maxRelProjConst_le (maxRelProjConst_le_sqrt' m)

section Type0

variable {𝕜 : Type} [RCLike 𝕜]

/-- `λ_𝕜(m) = sup_N λ_𝕜(m, N)`. -/
theorem maxProjConst_eq_iSup_maxRelProjConst (m : ℕ) :
    maxProjConst 𝕜 m = ⨆ N, maxRelProjConst 𝕜 m N :=
  maxProjConst_eq_iSup (maxRelProjConst_le_sqrt' m)

/-- `λ_𝕜(m) = sup_N sup { ∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| : t ≥ 0, ‖t‖ = 1, P ∈ 𝒫ₘ(N) }`. -/
theorem maxProjConst_eq_iSup_clConst (m : ℕ) :
    maxProjConst 𝕜 m = ⨆ N, clConst 𝕜 (Fin N) m := by
  rw [maxProjConst_eq_iSup_maxRelProjConst]
  simp_rw [maxRelProjConst_eq_clConst]

lemma maxRelProjConst_le_maxProjConst (m N : ℕ) : maxRelProjConst 𝕜 m N ≤ maxProjConst 𝕜 m := by
  rw [maxProjConst_eq_iSup_maxRelProjConst]
  exact le_ciSup ⟨√m, by rintro _ ⟨N, rfl⟩; exact maxRelProjConst_le_sqrt m N⟩ N

lemma clConst_le_maxProjConst (m N : ℕ) : clConst 𝕜 (Fin N) m ≤ maxProjConst 𝕜 m := by
  rw [← maxRelProjConst_eq_clConst]; exact maxRelProjConst_le_maxProjConst m N

/-- Every `m`-dimensional `Y ⊆ ℓ∞^N` gives a lower bound `λ(Y, ℓ∞^N) ≤ λ_𝕜(m)`. -/
lemma relProjConst_le_maxProjConst' {m N : ℕ} (Y : Submodule 𝕜 (Fin N → 𝕜))
    (hY : Module.finrank 𝕜 Y = m) : relProjConst Y ≤ maxProjConst 𝕜 m :=
  relProjConst_le_maxProjConst (maxRelProjConst_le_sqrt' m) Y hY

/-- Every configuration `(t, P)` gives a lower bound for `λ_𝕜(m)`. -/
lemma weightedAbsSum_le_maxProjConst {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {t : ι → ℝ} (ht : IsUnitWeight t) {P : Matrix ι ι 𝕜} (hP : P ∈ orthProjs 𝕜 ι m) :
    weightedAbsSum t P ≤ maxProjConst 𝕜 m := by
  -- relabel `ι` as `Fin N`
  let e := (Fintype.equivFin ι).symm
  have hP' := submatrix_mem_orthProjs e hP
  have ht' : IsUnitWeight (t ∘ e) :=
    ⟨fun i => ht.nonneg _, by rw [← ht.sum_sq]; exact e.sum_comp (fun i => t i ^ 2)⟩
  have h1 : weightedAbsSum (t ∘ e) (P.submatrix e e) = weightedAbsSum t P := by
    simp only [weightedAbsSum, Function.comp_apply, Matrix.submatrix_apply]
    rw [e.sum_comp (fun i => ∑ j, t i * t (e j) * ‖P i (e j)‖)]
    exact Finset.sum_congr rfl fun i _ => e.sum_comp (fun j => t i * t j * ‖P i j‖)
  rw [← h1]
  exact (le_clConst ht' hP').trans (clConst_le_maxProjConst m _)

/-- `μ(m, ι) ≤ λ(m)`. -/
lemma quasiRelConst_le_maxProjConst {m : ℕ} (N : ℕ) :
    quasiRelConst 𝕜 (Fin N) m ≤ maxProjConst 𝕜 m :=
  (quasiRelConst_le_maxRelProjConst m N).trans (maxRelProjConst_le_maxProjConst m N)

/-- `μ(m) ≤ λ(m)`. -/
lemma quasiMaxConst_le_maxProjConst (m : ℕ) : quasiMaxConst 𝕜 m ≤ maxProjConst 𝕜 m :=
  quasiMaxConst_le (maxProjConst_nonneg m) fun N => quasiRelConst_le_maxProjConst N

end Type0

end ProjectionConstants
