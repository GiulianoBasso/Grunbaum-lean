/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import Grunbaum.CorollaryG

/-!
# Main results

This file restates the results of the new proof of `Π₂ = 4/3` in item 5) of Section 3 of

* G. Basso, *Errata to the single-author papers of Giuliano Basso*, Section 3
  (*Computation of maximal projection constants*, J. Funct. Anal. 277 (2019)),

in the order in which they appear there. All results are proved in the other files of the
library; here we only give the statements, in the notation of the errata.

Notation (errata → Lean):

* `S ∈ 𝒜_d` : `Grunbaum.IsSignMatrix S`;
* `D = Diag(d₁, …, d_d) ∈ 𝒟_d` : `Grunbaum.IsWeight d`;
* `√D S √D` : `Grunbaum.weightedMatrix S d`;
* `π₂(M)` : `π₂ M`, i.e. `Grunbaum.sumTopTwo M`;
* `Π(2, S)` : `Grunbaum.supWeights S`;
* `Π(2, d)` : `ProjectionConstants.maxRelProjConst ℝ 2 d`;
* `Π₂` : `ProjectionConstants.maxProjConst ℝ 2`;
* a maximizer `(S, D)` of `Π(2, d)` : `Grunbaum.IsMaximizer S d`;
* the two-graph `[S]` : `Grunbaum.twoGraph S`;
* coherent triples, cocliques, cliques of order `4` and twins : `Grunbaum.Coherent`,
  `Grunbaum.IsCoclique`, `Grunbaum.K4Free`, `Grunbaum.IsTwin`;
* `R_{2N+1}` : the block matrix `Grunbaum.blockR N` of [JFA, Section 4.1], which after
  relabelling and switching is `Grunbaum.polygonMatrix N` (the version used in the proofs);
* `R₃`, `R₅`, `A₆` : `Grunbaum.R3`, `Grunbaum.R5` (`= 𝟙₅ + S(C₅)`, see (R2)), `Grunbaum.A6`;
* the vectors `uᵢ ∈ ℝ²` of Lemma B (the rows of `U`, where `P = UUᵗ`) : the pairs `(u i, v i)`
  for an orthonormal pair `u, v` of top eigenvectors.

The indices of `R₅` and `A₆` run over `0, …, 4` and `0, …, 5`, respectively.
-/

open Finset Matrix ProjectionConstants

namespace Grunbaum.Errata

/-! ### Basic notation and results -/

/-- The formula of Chalmers and Lewicki ([JFA, Theorem 2.1] for `n = 2`):
`Π(2, d) = max { π₂(√D S √D) : S ∈ 𝒜_d, D ∈ 𝒟_d }`. -/
theorem chalmers_lewicki (d : ℕ) : maxRelProjConst ℝ 2 d = supConfigs (Fin d) :=
  maxRelProjConst_two_eq_supConfigs d

/-- `Π₂ = sup_d Π(2, d)`. -/
theorem maxProjConst_two_eq : maxProjConst ℝ 2 = ⨆ d : ℕ, supConfigs (Fin d) :=
  maxProjConst_two_eq_iSup

/-- **Fan's maximum principle**: `π₂(M)` is the sum of the two largest eigenvalues of `M`. -/
theorem fan {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℝ} (hM : M.IsHermitian)
    (h2 : 2 ≤ Fintype.card ι) :
    π₂ M = hM.eigenvalues₀ ⟨0, by omega⟩ + hM.eigenvalues₀ ⟨1, by omega⟩ :=
  sumTopTwo_eq_eigenvalues₀ hM h2

/-- Switching and relabelling: `Π(2, QᵗSQ) = Π(2, S)` for a signed permutation matrix `Q`. -/
theorem supWeights_switch_relabel {ι κ : Type*} [Fintype ι] [Fintype κ] {S : Matrix ι ι ℝ}
    {T : Matrix κ κ ℝ} (hS : IsSignMatrix S) (hT : IsSignMatrix T) (e : ι ≃ κ) {ε : ι → ℝ}
    (hε : IsSignVector ε) (hST : ∀ i j, S i j = ε i * ε j * T (e i) (e j)) :
    supWeights S = supWeights T :=
  supWeights_eq_of_equiv hS hT e hε.mul_self hST

/-- If `B` is a principal submatrix of `S` (up to switching and permutation), then
`Π(2, B) ≤ Π(2, S)`: extend the weights by zero. -/
theorem supWeights_principal {ι κ : Type*} [Fintype ι] [Fintype κ] {B : Matrix ι ι ℝ}
    {S : Matrix κ κ ℝ} (hS : IsSignMatrix S) {f : ι → κ} (hf : Function.Injective f)
    {ε : ι → ℝ} (hε : IsSignVector ε) (hBS : ∀ i j, B i j = ε i * ε j * S (f i) (f j)) :
    supWeights B ≤ supWeights S :=
  supWeights_le_of_transfer hS hf hε.mul_self hBS

/-- A coclique of `[S]`: equivalently, after switching, `S[C, C] = J_C`. -/
theorem coclique_iff {ι : Type*} {S : Matrix ι ι ℝ} (hS : IsSignMatrix S) (C : Set ι) :
    IsCoclique S C ↔ ∃ ε : ι → ℝ, IsSignVector ε ∧ ∀ i ∈ C, ∀ j ∈ C, S i j = ε i * ε j :=
  isCoclique_iff_exists_switch hS C

/-- A clique: equivalently, after switching, all off-diagonal entries of `S` on it equal `-1`. -/
theorem clique_iff {ι : Type*} {S : Matrix ι ι ℝ} (hS : IsSignMatrix S) (C : Set ι) :
    IsClique S C ↔ ∃ ε : ι → ℝ, IsSignVector ε ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y → ε x * ε y * S x y = -1 :=
  isClique_iff_exists_switch hS C

/-- Twins: after switching `j`, the rows of `i` and `j` coincide. -/
theorem twins_switch {ι : Type*} {S : Matrix ι ι ℝ} (hS : IsSignMatrix S)
    {i j : ι} (h : IsTwin S i j) :
    ∃ ε : ι → ℝ, IsSignVector ε ∧ (∀ k, k ≠ j → ε k = 1) ∧
      ∀ k, switch S ε j k = switch S ε i k :=
  h.exists_switch hS

/-- `[R_{2N+1}] = T_{2N+1}`: a triple is coherent iff the centre of the regular `(2N+1)`-gon lies
in the convex hull of the corresponding vertices. -/
theorem twoGraph_R (N : ℕ) :
    twoGraph (polygonMatrix N) = FranklFuredi.circleGraph (regularPolygon N) :=
  twoGraph_polygonMatrix N

/-- "By Section 4.1, we may label the indices of `R_{2N+1}` by `p₀, …, p_{2N}` such that
`[R_{2N+1}] = T_{2N+1}`", for the block matrix `R_{2N+1}` of [JFA, Section 4.1] (with the
misprint of item 8) corrected). -/
theorem twoGraph_R_JFA (N : ℕ) :
    twoGraph (blockR N) =
      (FranklFuredi.circleGraph (regularPolygon N)).pullback (blockLabel N) :=
  twoGraph_blockR N

/-- **(R1)** `{p₀, …, p_N}` is a coclique of `[R_{2N+1}]` with `N + 1` elements. -/
theorem fact_R1 (N : ℕ) :
    IsCoclique (polygonMatrix N) (Set.range (Fin.castLE (by omega : N + 1 ≤ 2 * N + 1))) :=
  isCoclique_polygonMatrix N

/-- **(R2)** `R₅ = 𝟙₅ + S(C₅)` up to switching. -/
theorem fact_R2 : SwitchEquiv (polygonMatrix 2) R5 :=
  switchEquiv_polygonMatrix_two

/-- **(A1)** Every `5 × 5` principal submatrix of `A₆` equals `R₅` up to switching and
permutation. -/
theorem fact_A1 (k : Fin 6) :
    ∃ (f : Fin 6 → Fin 5) (ε : Fin 6 → ℝ), (∀ a b, a ≠ k → b ≠ k → f a = f b → a = b) ∧
      IsSignVector ε ∧ ∀ a b, a ≠ k → b ≠ k → A6 a b = ε a * ε b * R5 (f a) (f b) := by
  refine ⟨certMap k, certSign k, fun a b ha hb h => certMap_injective k a b ha hb h,
    fun a => ?_, fun a b ha hb => A6_eq_certificate k a b ha hb⟩
  fin_cases k <;> fin_cases a <;> simp [certSign]

/-- **(FF)** Every `K₄`-free two-graph with at least one coherent triple is, up to switching and
permutation, a blow-up of `R_{2N+1}` for some `N ≥ 1`, or of a principal submatrix of `A₆`. -/
theorem fact_FF {ι : Type*} [Finite ι] {S : Matrix ι ι ℝ} (hS : IsSignMatrix S)
    (hK4 : K4Free S) (hcoh : HasCoherent S) :
    (∃ (N : ℕ) (f : ι → Fin (2 * N + 1)), 1 ≤ N ∧ Function.Surjective f ∧
        SwitchEquiv S ((polygonMatrix N).submatrix f f)) ∨
      ∃ f : ι → Fin 6, SwitchEquiv S (A6.submatrix f f) :=
  classification hS hK4 hcoh

/-! ### Theorem A -/

/-- **Theorem A** (Reduction). `Π₂ = max {Π(2, R₃), Π(2, R₅)}`. -/
theorem theorem_A : maxProjConst ℝ 2 = max (supWeights R3) (supWeights R5) :=
  maxProjConst_two_eq_max

/-- **Theorem A**, with `R₃` and `R₅` the block matrices of [JFA, Section 4.1]. -/
theorem theorem_A' :
    maxProjConst ℝ 2 = max (supWeights (blockR 1)) (supWeights (blockR 2)) :=
  maxProjConst_two_eq_max_blockR

/-! ### Three lemmas -/

/-- **Lemma B** (Structure of maximizers), for `n = 2`. Let `d > 2` and let `(S, D)` be a
maximizer of `Π(2, d)` with `D` positive definite. Put `M := √D S √D`, let `u, v` be an
orthonormal pair of top eigenvectors of `M` (more generally, any orthonormal pair with
`uᵀMu + vᵀMv = π₂(M)`), `P := uuᵀ + vvᵀ`, and `xᵢ := (uᵢ, vᵢ) ∈ ℝ²`, so that
`Pᵢⱼ = ⟨xᵢ, xⱼ⟩`. Then:
a) `PM = MP` and `Tr(MP) = π₂(M) = Π(2, d)`;
b) `sᵢⱼ = sgn⟨xᵢ, xⱼ⟩ ≠ 0` for all `i, j`;
c) `Π(2, d) = ∑ᵢⱼ √dᵢ √dⱼ |⟨xᵢ, xⱼ⟩|`;
d) the two-graph `[S]` is `K₄`-free. -/
theorem lemma_B {d : ℕ} (hd : 2 < d) {S : Matrix (Fin d) (Fin d) ℝ} {w : Fin d → ℝ}
    (hmax : IsMaximizer S w) (hpos : ∀ i, 0 < w i) {u v : Fin d → ℝ}
    (huv : IsOrthonormalPair u v)
    (hval : fanValue (weightedMatrix S w) u v = π₂ (weightedMatrix S w)) :
    (projPair u v * weightedMatrix S w = weightedMatrix S w * projPair u v ∧
      (weightedMatrix S w * projPair u v).trace = π₂ (weightedMatrix S w) ∧
      π₂ (weightedMatrix S w) = maxRelProjConst ℝ 2 d) ∧
    (∀ i j, 0 < S i j * (u i * u j + v i * v j)) ∧
    maxRelProjConst ℝ 2 d = ∑ i, ∑ j, √(w i) * √(w j) * |u i * u j + v i * v j| ∧
    K4Free S := by
  have hsign := hmax.mul_projPair_pos hpos (by simpa using hd) huv hval
  have hPi : π₂ (weightedMatrix S w) = maxRelProjConst ℝ 2 d := by
    rw [maxRelProjConst_two_eq_supConfigs, hmax.sumTopTwo_eq]
  refine ⟨⟨(mul_projPair_comm (weightedMatrix_symm hmax.isSignMatrix w) huv
      fun x y hxy => hval ▸ fanValue_le_sumTopTwo _ hxy).symm,
    by rw [trace_mul_projPair, hval], hPi⟩, hsign, ?_,
    k4Free_of_mul_projPair_pos hmax.isSignMatrix hsign⟩
  rw [← hPi, sumTopTwo_eq_sum_abs hmax.isSignMatrix hval hsign]

/-- **Lemma C** (Cloning [KMMP, Claim 2.4]), for `n = 2`. Let `m > 2`, let `(S, D)` be a
maximizer of `Π(2, m)` with `D` positive definite, and let `xᵢ = (uᵢ, vᵢ)` be as in Lemma B.
Let `C ⊆ {0, …, m - 1}` be such that `⟨xᵢ, xⱼ⟩ ≥ 0` for all `i, j ∈ C`. Let `c₁, …, c_m ≥ 0` with
`cᵢ = 1` for `i ∉ C` and `∑_{i ∈ C} cᵢ xᵢ xᵢᵀ = ∑_{i ∈ C} xᵢ xᵢᵀ`. Then
`D' := Diag(c₁d₁, …, c_m d_m)` lies in `𝒟_m`, and `(S, D')` is again a maximizer of `Π(2, m)`. -/
theorem lemma_C {m : ℕ} (hm : 2 < m) {S : Matrix (Fin m) (Fin m) ℝ} {w : Fin m → ℝ}
    (hmax : IsMaximizer S w) (hpos : ∀ i, 0 < w i) {u v : Fin m → ℝ}
    (huv : IsOrthonormalPair u v)
    (hval : fanValue (weightedMatrix S w) u v = π₂ (weightedMatrix S w)) {C : Finset (Fin m)}
    (hC : ∀ i ∈ C, ∀ j ∈ C, 0 ≤ u i * u j + v i * v j) {c : Fin m → ℝ} (hc : ∀ i, 0 ≤ c i)
    (hc1 : ∀ i, i ∉ C → c i = 1)
    (hcC : ∑ i ∈ C, c i • vecMulVec ![u i, v i] ![u i, v i] =
      ∑ i ∈ C, vecMulVec ![u i, v i] ![u i, v i]) :
    IsWeight (fun i => c i * w i) ∧ IsMaximizer S fun i => c i * w i :=
  have h := hmax.clone hpos hm huv hval hC hc hc1 hcC
  ⟨h.isWeight, h⟩

/-- **Lemma D.** `A₆` is not, up to switching and permutation, the sign pattern
`(sgn⟨xᵢ, xⱼ⟩)ᵢⱼ` of six vectors `xᵢ = (uᵢ, vᵢ) ∈ ℝ²` with pairwise non-zero inner products. -/
theorem lemma_D (u v : Fin 6 → ℝ) (σ : Equiv.Perm (Fin 6)) {ε : Fin 6 → ℝ}
    (hε : IsSignVector ε) :
    ¬∀ i j, 0 < ε i * ε j * A6 (σ i) (σ j) * (u i * u j + v i * v j) := by
  intro h
  refine not_signPattern_A6_of_switch (S := fun i j => ε i * ε j * A6 (σ i) (σ j)) h σ.symm
    (fun a => ε (σ.symm a)) (fun a => hε.mul_self _) fun a b => ?_
  simp

/-! ### Proof of Theorem A -/

/-- **Step 1**: a maximizer of `Π(2, m) > 1` lives on at least three indices. -/
theorem step_1 {m : ℕ} {S : Matrix (Fin m) (Fin m) ℝ} {w : Fin m → ℝ} (hmax : IsMaximizer S w)
    (h1 : 1 < supConfigs (Fin m)) : 3 ≤ m :=
  three_le_of_isMaximizer hmax h1

/-- **Step 2** (no twins). -/
theorem step_2 {m : ℕ} {S : Matrix (Fin m) (Fin m) ℝ} {w : Fin m → ℝ} (hmax : IsMaximizer S w)
    (h1 : 1 < supConfigs (Fin m))
    (hmin : ∀ (S' : Matrix (Fin m) (Fin m) ℝ) (w' : Fin m → ℝ), IsMaximizer S' w' → ∀ i, 0 < w' i)
    (i j : Fin m) : ¬IsTwin S i j :=
  not_isTwin_of_minimal hmax h1 hmin i j

/-- **Step 3** (no coclique of order `4`). -/
theorem step_3 {m : ℕ} {S : Matrix (Fin m) (Fin m) ℝ} {w : Fin m → ℝ} (hmax : IsMaximizer S w)
    (hpos : ∀ i, 0 < w i) (hm : 2 < m)
    (hmin : ∀ (S' : Matrix (Fin m) (Fin m) ℝ) (w' : Fin m → ℝ), IsMaximizer S' w' → ∀ i, 0 < w' i)
    {C : Finset (Fin m)} (hC : IsCoclique S (C : Set (Fin m))) : C.card ≤ 3 :=
  card_le_three_of_isCoclique hmax hpos hm hmin hC

/-- **Step 4** (classification). -/
theorem step_4 {m : ℕ} {S : Matrix (Fin m) (Fin m) ℝ} (hS : IsSignMatrix S) (hm : 2 < m)
    (hK4 : K4Free S) (htw : ∀ i j, ¬IsTwin S i j)
    (hcocl : ∀ C : Finset (Fin m), IsCoclique S (C : Set (Fin m)) → C.card ≤ 3) {u v : Fin m → ℝ}
    (hsign : ∀ i j, 0 < S i j * (u i * u j + v i * v j)) :
    supWeights S ≤ max (supWeights R3) (supWeights R5) :=
  supWeights_le_max_of_minimal hS hm hK4 htw hcocl hsign

/-- The blow-up lemma [JFA, Lemma 2.2], used in Step 2: for `S = T(f, f)` and the merged weights
`D'` of `D`, `X^{|κ|} χ(√D S √D) = X^{|ι|} χ(√D' T √D')`. -/
theorem blow_up {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (T : Matrix κ κ ℝ) (f : ι → κ) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) :
    Polynomial.X ^ Fintype.card κ * (weightedMatrix (T.submatrix f f) w).charpoly =
      Polynomial.X ^ Fintype.card ι * (weightedMatrix T (mergeWeight f w)).charpoly :=
  charpoly_weightedMatrix_submatrix T f hw

/-- The cloning lemma of Kumar, Mohar, Mojallal and Pragada ([KMMP, Claim 2.4]), for every
rank `r ≥ 1`, used in Lemma C. -/
theorem kmmp_cloning {n r : ℕ} {U : Matrix (Fin n) (Fin r) ℝ} {w : Fin n → ℝ}
    (h : KMMP.IsMaximizingPair U w) (hr : 0 < r) {C : Finset (Fin n)}
    (hC : ∀ i ∈ C, ∀ j ∈ C, 0 ≤ U i ⬝ᵥ U j) {c : Fin n → ℝ} (hc : ∀ i, 0 ≤ c i)
    (hc1 : ∀ i, i ∉ C → c i = 1)
    (hcC : ∑ i ∈ C, c i • vecMulVec (U i) (U i) = ∑ i ∈ C, vecMulVec (U i) (U i)) :
    KMMP.IsMaximizingPair (KMMP.cloneMatrix U c) (KMMP.cloneWeight w c) :=
  h.clone hr hC hc hc1 hcC

/-! ### The remaining computation: `Π(2, R₅)` -/

/-- **Lemma E.** For `D ∈ 𝒟₅`, `det(x 𝟙₅ - √D R₅ √D) = x⁵ - x⁴ + 4τx² - 16δ`, where
`δ = d₁ ⋯ d₅` and `τ = ∑_{{i, j, k} coherent} dᵢ dⱼ dₖ`. -/
theorem lemma_E {d : Fin 5 → ℝ} (hd : IsWeight d) :
    (weightedMatrix R5 d).charpoly = Polynomial.X ^ 5 - Polynomial.X ^ 4 +
      Polynomial.C (4 * tauR5 d) * Polynomial.X ^ 2 - Polynomial.C (16 * ∏ i, d i) :=
  charpoly_weightedMatrix_R5 hd

/-- **Proposition F.** `Π(2, R₅) = 4/3`. Moreover, `π₂(√D R₅ √D) = 4/3` only if `D` is
singular. -/
theorem proposition_F :
    supWeights R5 = 4 / 3 ∧
      ∀ d : Fin 5 → ℝ, IsWeight d → π₂ (weightedMatrix R5 d) = 4 / 3 → ∃ i, d i = 0 := by
  refine ⟨supWeights_R5, fun d hd h => ?_⟩
  by_contra hcon
  push Not at hcon
  have := sumTopTwo_weightedMatrix_R5_lt hd fun i => lt_of_le_of_ne (hd.nonneg i) (hcon i).symm
  linarith

/-- **Corollary G** (Chalmers–Lewicki). `Π₂ = 4/3`. -/
theorem corollary_G : maxProjConst ℝ 2 = 4 / 3 :=
  maxProjConst_two

/-- **Grünbaum's conjecture** (Chalmers–Lewicki): every two-dimensional real normed space has
absolute projection constant at most `4/3`. -/
theorem grunbaum (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (hY : Module.finrank ℝ Y = 2) : absProjConst ℝ Y ≤ 4 / 3 :=
  absProjConst_le_four_thirds Y hY

end Grunbaum.Errata
