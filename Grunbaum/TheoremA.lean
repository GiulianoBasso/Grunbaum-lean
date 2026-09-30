/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import Grunbaum.Classification
import Grunbaum.LemmaC
import Grunbaum.LemmaD
import Grunbaum.BlowUp

/-!
# Theorem A: the reduction to `R₃` and `R₅`

> **Theorem A** (Reduction). `Π₂ = max {Π(2, R₃), Π(2, R₅)}`.

*Strategy of the proof.* Fix `d > 2`. Take a maximizer of `Π(2, d)` of minimal support, and let
`m` be the size of its support. After restricting to the support, it is a weighted configuration
of vectors `u₁, …, u_m ∈ ℝ²` whose sign pattern is the matrix `S₀`. We squeeze `S₀` from two
sides.

* **Step 1.** No clique of order `4`. This comes for free from Lemma B(d).
* **Step 2.** No twins. Twins could be merged by the blow-up lemma, [JFA, Lemma 2.2].
* **Step 3.** No coclique of order `4`. Four vectors in the plane give four rank-one matrices in
  the `3`-dimensional space of symmetric `2 × 2` matrices. By the cloning lemma, their weights can
  then be shifted until one of them vanishes.
* **Step 4.** Classification. By (FF), a `K₄`-free two-graph without twins is some `R_{2N+1}` or
  a principal submatrix of `A₆`. By (R1) and Step 3, `N ≤ 2`. By (A1) and Lemma D, a principal
  submatrix of `A₆` contributes at most `Π(2, R₅)`.

## Main results

* `Grunbaum.R3` : the matrix `R₃`; `Grunbaum.le_sumTopTwo_weightedMatrix_R3` : `π₂(⅓ R₃) ≥ 4/3`;
* `Grunbaum.three_le_of_isMaximizer` : Step 1, `m ≥ 3`;
* `Grunbaum.not_isTwin_of_minimal` : Step 2;
* `Grunbaum.card_le_three_of_isCoclique` : Step 3;
* `Grunbaum.supWeights_le_max_of_minimal` : Step 4;
* `Grunbaum.supConfigs_le_max` : `Π(2, d) ≤ max {Π(2, R₃), Π(2, R₅)}` for all `d`;
* `Grunbaum.maxProjConst_two_eq_max` : **Theorem A**;
* `Grunbaum.maxProjConst_two_eq_max_blockR` : Theorem A for the block matrices `R₃`, `R₅` of
  [JFA, Section 4.1].

The lower bound `π₂(⅓ R₃) ≥ 4/3` is adapted from `ProjectionConstants/Grunbaum/Final.lean` of the
library *Projection constants in Lean*.
-/

open Finset Matrix ProjectionConstants

namespace Grunbaum

/-! ### `R₃` -/

/-- `R₃`, the matrix `R_{2N+1}` of [JFA, Section 4.1] for `N = 1`. It has the eigenvalues
`2, 2, -1`. -/
def R3 : Matrix (Fin 3) (Fin 3) ℝ := !![1, 1, -1; 1, 1, 1; -1, 1, 1]

lemma isSignMatrix_R3 : IsSignMatrix R3 := by
  refine ⟨fun a b => ?_, fun a b => ?_, fun a => ?_⟩
  · fin_cases a <;> fin_cases b <;> simp [R3]
  · fin_cases a <;> fin_cases b <;> simp [R3]
  · fin_cases a <;> simp [R3]

/-- `R₃` is `R_{2·1+1}` with the indices labelled by the vertices of the triangle. -/
lemma supWeights_polygonMatrix_one : supWeights (polygonMatrix 1) = supWeights R3 :=
  supWeights_eq_of_equiv (isSignMatrix_polygonMatrix 1) isSignMatrix_R3 (finCongr rfl)
    (ε := fun _ => 1) (fun _ => by norm_num) fun i j => by
      fin_cases i <;> fin_cases j <;> simp [polygonMatrix, R3]

/-- (R2): `Π(2, R_{2·2+1}) = Π(2, R₅)`. -/
lemma supWeights_polygonMatrix_two : supWeights (polygonMatrix 2) = supWeights R5 :=
  supWeights_eq_of_equiv (isSignMatrix_polygonMatrix 2) isSignMatrix_R5 (finCongr rfl)
    (ε := signsR2) isSignVector_signsR2.mul_self fun i j => polygonMatrix_two_eq i j

/-- The block matrix `R_{2N+1}` of [JFA, Section 4.1] and `Grunbaum.polygonMatrix N` have the same
`Π(2, ·)`, since they agree up to switching and relabelling. -/
lemma supWeights_blockR (N : ℕ) : supWeights (blockR N) = supWeights (polygonMatrix N) :=
  supWeights_eq_of_equiv (isSignMatrix_blockR N) (isSignMatrix_polygonMatrix N)
    (Equiv.ofBijective _ (blockLabel_bijective N)) (isSignVector_blockSign N).mul_self
    (blockR_eq N)

/-- `√D R₃ √D = ⅓ R₃` for `D = ⅓ 𝟙₃`. -/
lemma weightedMatrix_R3_third : weightedMatrix R3 (fun _ => 1 / 3) = (1 / 3 : ℝ) • R3 := by
  ext i j
  simp only [weightedMatrix_apply, Matrix.smul_apply, smul_eq_mul]
  have h : √(1 / 3 : ℝ) * √(1 / 3) = 1 / 3 := Real.mul_self_sqrt (by norm_num)
  linear_combination R3 i j * h

/-- `π₂(⅓ R₃) ≥ 4/3`, since `R₃` has the eigenvalue `2` twice, with the orthonormal eigenvectors
`(1, 1, 0)/√2` and `(1, -1, -2)/√6`. -/
theorem le_sumTopTwo_weightedMatrix_R3 : 4 / 3 ≤ π₂ (weightedMatrix R3 fun _ => 1 / 3) := by
  set a : ℝ := 1 / √2 with ha_def
  set b : ℝ := 1 / √6 with hb_def
  have ha : a * a = 1 / 2 := by
    rw [ha_def, div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num)]
  have hb : b * b = 1 / 6 := by
    rw [hb_def, div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num)]
  set u : Fin 3 → ℝ := ![a, a, 0] with hu
  set v : Fin 3 → ℝ := ![b, -b, -2 * b] with hv
  have hon : IsOrthonormalPair u v := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [hu, dotProduct, Fin.sum_univ_three, Matrix.cons_val]
      linarith
    · simp only [hv, dotProduct, Fin.sum_univ_three, Matrix.cons_val]
      linarith
    · simp only [hu, hv, dotProduct, Fin.sum_univ_three, Matrix.cons_val]
      ring
  have hval : fanValue (weightedMatrix R3 fun _ => 1 / 3) u v = 4 / 3 := by
    rw [weightedMatrix_R3_third, fanValue_smul]
    simp only [fanValue, hu, hv, R3, mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val,
      Matrix.of_apply]
    linear_combination (4 / 3 : ℝ) * ha + (4 : ℝ) * hb
  rw [← hval]
  exact fanValue_le_sumTopTwo _ hon

/-- Up to a permutation, `R₃` is the principal submatrix of `R₅` on `{0, 1, 3}` (the errata's
`{1, 2, 4}`). -/
lemma R3_eq_submatrix_R5 (i j : Fin 3) :
    R3 i j = R5 ((![0, 3, 1] : Fin 3 → Fin 5) i) ((![0, 3, 1] : Fin 3 → Fin 5) j) := by
  fin_cases i <;> fin_cases j <;> simp [R3, R5]

lemma injective_R3_R5 : Function.Injective (![0, 3, 1] : Fin 3 → Fin 5) := by decide

/-- `Π(2, R₃) ≤ Π(2, R₅)`. -/
theorem supWeights_R3_le_R5 : supWeights R3 ≤ supWeights R5 :=
  supWeights_le_of_transfer isSignMatrix_R5 injective_R3_R5 (ε := fun _ => 1)
    (fun _ => by norm_num) fun i j => by rw [R3_eq_submatrix_R5]; ring

/-- `Π(2, d) ≥ 4/3` for `d ≥ 3`: `Π(2, d) ≥ π₂(⅓ R₃) = 4/3`. -/
theorem four_thirds_le_supConfigs {d : ℕ} (hd : 3 ≤ d) : 4 / 3 ≤ supConfigs (Fin d) :=
  le_sumTopTwo_weightedMatrix_R3.trans ((sumTopTwo_le_supConfigs isSignMatrix_R3
    ⟨fun _ => by norm_num, by norm_num⟩).trans
      (supConfigs_le_of_injective (Fin.castLE_injective hd)))

/-! ### Step 1: `m ≥ 3` -/

section Step1

variable {ι : Type*} [Fintype ι]

/-- If `S = εεᵀ` has rank one, then `M = √D S √D = yyᵀ` with `y = √D ε`, which has rank one and
trace `1`; hence `π₂(M) ≤ 1`. -/
theorem sumTopTwo_weightedMatrix_le_one_of_eq_mul {S : Matrix ι ι ℝ} {ε : ι → ℝ}
    (hε : ∀ i, ε i * ε i = 1) (hS : ∀ i j, S i j = ε i * ε j) {w : ι → ℝ} (hw : IsWeight w) :
    π₂ (weightedMatrix S w) ≤ 1 := by
  set y : ι → ℝ := fun i => √(w i) * ε i with hy
  have hyy : y ⬝ᵥ y = 1 := by
    rw [← hw.sum_eq]
    refine sum_congr rfl fun i _ => ?_
    simp only [hy]
    have := Real.mul_self_sqrt (hw.nonneg i)
    linear_combination (w i) * hε i + (ε i * ε i) * this
  have hq : ∀ x, x ⬝ᵥ (weightedMatrix S w *ᵥ x) = (y ⬝ᵥ x) ^ 2 := by
    intro x
    rw [dotProduct_mulVec_eq_sum, sq, dotProduct, sum_mul_sum]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    simp only [weightedMatrix_apply, hS, hy]
    ring
  refine sumTopTwo_le' zero_le_one fun x z hxz => ?_
  have := bessel hxz y
  rw [dotProduct_comm x y, dotProduct_comm z y, hyy] at this
  simp only [fanValue, hq]
  linarith

/-- On at most two indices, every sign matrix has the form `εεᵀ`. -/
theorem exists_eq_mul_of_card_le_two {S : Matrix ι ι ℝ} (hS : IsSignMatrix S)
    (h2 : Fintype.card ι ≤ 2) : ∃ ε : ι → ℝ, IsSignVector ε ∧ ∀ i j, S i j = ε i * ε j := by
  classical
  have hC : IsCoclique S Set.univ := by
    intro i _ j _ k _ hcoh
    have hcard : ({i, j, k} : Finset ι).card = 3 :=
      card_eq_three.mpr ⟨i, j, k, hcoh.ne₁₂ hS, hcoh.ne₁₃ hS, hcoh.ne₂₃ hS, rfl⟩
    have := card_le_univ ({i, j, k} : Finset ι)
    omega
  obtain ⟨ε, hε, h⟩ := (isCoclique_iff_exists_switch hS Set.univ).mp hC
  exact ⟨ε, hε, fun i j => h i trivial j trivial⟩

/-- **Step 1**: `m ≥ 3`. If `m ≤ 2`, then `S₀ = εεᵀ`, so `Π(2, m) = π₂(M) ≤ 1`. -/
theorem three_le_of_isMaximizer {m : ℕ} {S : Matrix (Fin m) (Fin m) ℝ} {w : Fin m → ℝ}
    (hmax : IsMaximizer S w) (h1 : 1 < supConfigs (Fin m)) : 3 ≤ m := by
  by_contra hm
  obtain ⟨ε, hε, hS⟩ := exists_eq_mul_of_card_le_two hmax.isSignMatrix (by simp; omega)
  have := sumTopTwo_weightedMatrix_le_one_of_eq_mul hε.mul_self hS hmax.isWeight
  rw [hmax.sumTopTwo_eq] at this
  linarith

end Step1

/-! ### Step 2: no twins -/

section Step2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `λ₁(M) ≤ 1` for `M = √D S √D`: since `|M| ≤ √D J √D` entrywise, `uᵀMu ≤ |u|²`. -/
theorem eigenvalues_weightedMatrix_le_one {S : Matrix ι ι ℝ} {w : ι → ℝ} (hS : IsSignMatrix S)
    (hw : IsWeight w) (hA : (weightedMatrix S w).IsHermitian) (k : ι) :
    hA.eigenvalues k ≤ 1 := by
  have := dotProduct_mulVec_weightedMatrix_le_one hS hw
    (by simp [eigenvector_dotProduct] : eigenvector hA k ⬝ᵥ eigenvector hA k = 1)
  rwa [mulVec_eigenvector, dotProduct_smul, eigenvector_dotProduct, ite_eq_left rfl,
    smul_eq_mul, mul_one] at this

/-- **Step 2** (no twins). Let `(S₀, D₀)` be a maximizer of `Π(2, m) > 1` such that every
maximizer of `Π(2, m)` has full support. Then `S₀` has no twins.

*Proof of the errata.* First, `λ₂(M) > 0`: `λ₁(M) ≤ 1`, and if `λ₂(M) ≤ 0` then
`Π = λ₁(M) + λ₂(M) ≤ 1`. Now suppose `i, j` were twins. Switching `j` makes the two rows equal, so
`S₀` is a blow-up of a matrix `S' ∈ 𝒜_{m-1}`. Merge the weights of `i` and `j`. By [JFA,
Lemma 2.2], the spectrum of the new maximizing matrix is that of `M` with one zero removed. Since
`λ₂(M) > 0`, this does not change `π₂`. This gives a maximizer with support of size `m - 1`,
contradicting minimality. -/
theorem not_isTwin_of_minimal {m : ℕ} {S : Matrix (Fin m) (Fin m) ℝ} {w : Fin m → ℝ}
    (hmax : IsMaximizer S w) (h1 : 1 < supConfigs (Fin m))
    (hmin : ∀ (S' : Matrix (Fin m) (Fin m) ℝ) (w' : Fin m → ℝ), IsMaximizer S' w' → ∀ i, 0 < w' i)
    (i j : Fin m) : ¬IsTwin S i j := by
  intro htw
  -- switching `j` makes the rows `i` and `j` equal
  obtain ⟨ε, hε, -, hrow⟩ := htw.exists_switch hmax.isSignMatrix
  have hmax₁ := hmax.switch hε
  set S₁ := switch S ε with hS₁_def
  have hS₁ := hmax₁.isSignMatrix
  have hA := isHermitian_weightedMatrix hS₁ w
  -- `λ₂(M) > 0`
  obtain ⟨a, b, hab, ha, hb⟩ := exists_top_two hA.eigenvalues
    (Fintype.one_lt_card_iff.mpr ⟨i, j, htw.1⟩)
  have hval := sumTopTwo_eq_top_two hA hab ha hb
  have hla := eigenvalues_weightedMatrix_le_one hS₁ hmax.isWeight hA a
  have hπ : π₂ (weightedMatrix S₁ w) = supConfigs (Fin m) := hmax₁.sumTopTwo_eq
  have hlb : 0 < hA.eigenvalues b := by linarith
  -- delete `j`, merging its weight into `i` ([JFA, Lemma 2.2])
  have hchar := charpoly_weightedMatrix_eq_X_mul hS₁.symm htw.1 hrow hmax.isWeight.nonneg
  set S' : Matrix {k // k ≠ j} {k // k ≠ j} ℝ := S₁.submatrix (↑) (↑) with hS'_def
  set w' := mergeWeight (foldTo i j htw.1) w with hw'_def
  have hS' : IsSignMatrix S' := hS₁.submatrix _
  have hw' : IsWeight w' := isWeight_mergeWeight _ hmax.isWeight
  have hB := isHermitian_weightedMatrix hS' w'
  have heq : π₂ (weightedMatrix S' w') = π₂ (weightedMatrix S₁ w) :=
    sumTopTwo_eq_of_charpoly_eq_X_mul hA hB hchar hab ha hb hlb
  -- pad with a zero weight at `j`: a maximizer of `Π(2, m)` with support of size `m - 1`
  have hf : Function.Injective (Subtype.val : {k // k ≠ j} → Fin m) := Subtype.val_injective
  set T := extendSign (Subtype.val : {k // k ≠ j} → Fin m) S' with hT_def
  set w'' := Function.extend (Subtype.val : {k // k ≠ j} → Fin m) w' 0 with hw''_def
  have hT : IsSignMatrix T := isSignMatrix_extendSign hf hS'
  have hw'' : IsWeight w'' := isWeight_extend hf hw'
  have hle : π₂ (weightedMatrix S' w') ≤ π₂ (weightedMatrix T w'') :=
    sumTopTwo_weightedMatrix_le_of_transfer hT hw' hf (ε := fun _ => 1) (fun _ => by norm_num)
      fun a b => by rw [hT_def, extendSign_apply hf]; ring
  have hmaxT : IsMaximizer T w'' :=
    isMaximizer_of_le hT hw'' (by rw [← hπ, ← heq]; exact hle)
  have hj : w'' j = 0 := by
    rw [hw''_def, Function.extend_apply' _ _ _ fun ⟨k, hk⟩ => k.2 hk]
    rfl
  exact (hmin T w'' hmaxT j).ne' hj

end Step2

/-! ### Step 3: no coclique of order 4 -/

section Step3

variable {m : ℕ}

/-- Four or more rank-one matrices `xᵢ xᵢᵀ`, `xᵢ = (uᵢ, vᵢ) ∈ ℝ²`, are linearly dependent, since
they lie in the `3`-dimensional space of symmetric `2 × 2` matrices: there is `0 ≠ h`
supported on `C` with `∑_{i ∈ C} hᵢ xᵢ xᵢᵀ = 0`. -/
theorem exists_relation_of_three_lt_card (u v : Fin m → ℝ) {C : Finset (Fin m)}
    (hC : 3 < C.card) :
    ∃ h : Fin m → ℝ, (∀ i, i ∉ C → h i = 0) ∧ (∃ i ∈ C, h i ≠ 0) ∧
      ∑ i ∈ C, h i • vecMulVec ![u i, v i] ![u i, v i] = 0 := by
  classical
  set φ : Fin m → Fin 3 → ℝ := fun i => ![u i * u i, u i * v i, v i * v i] with hφ
  have hnot : ¬LinearIndepOn ℝ φ (C : Set (Fin m)) := by
    intro hli
    have := LinearIndependent.fintype_card_le_finrank hli
    simp only [Module.finrank_fin_fun, Finset.coe_sort_coe, Fintype.card_coe] at this
    omega
  rw [linearIndepOn_finset_iff] at hnot
  push Not at hnot
  obtain ⟨f, hf, i₀, hi₀C, hi₀⟩ := hnot
  set h : Fin m → ℝ := fun i => if i ∈ C then f i else 0 with hh
  have hhf : ∀ i ∈ C, h i = f i := fun i hi => by simp [hh, hi]
  refine ⟨h, fun i hi => by simp [hh, hi], ⟨i₀, hi₀C, by rwa [hhf i₀ hi₀C]⟩, ?_⟩
  have hcomp : ∀ k : Fin 3, ∑ i ∈ C, h i * φ i k = 0 := by
    intro k
    have := congrFun hf k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    rw [← this]
    exact sum_congr rfl fun i hi => by rw [hhf i hi]
  have h0 : ∑ i ∈ C, h i * (u i * u i) = 0 := by simpa [hφ] using hcomp 0
  have h1 : ∑ i ∈ C, h i * (u i * v i) = 0 := by simpa [hφ] using hcomp 1
  have h2 : ∑ i ∈ C, h i * (v i * v i) = 0 := by simpa [hφ] using hcomp 2
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul,
    Matrix.zero_apply]
  fin_cases a <;> fin_cases b
  · simpa using h0
  · simpa using h1
  · simpa [mul_comm (v _) (u _)] using h1
  · simpa using h2

/-- **Step 3** (no coclique of order `4`). Let `(S₀, D₀)` be a maximizer of `Π(2, m)`, `m > 2`,
with `D₀` positive definite, such that every maximizer of `Π(2, m)` has full support. Then every
coclique of `[S₀]` has at most three elements.

*Proof of the errata.* Let `C` be a coclique with `|C| ≥ 4`. After switching, `S₀[C, C] = J_C`,
so `⟨xᵢ, xⱼ⟩ > 0` for `i, j ∈ C` by Lemma B(b). The matrices `xᵢ xᵢᵀ`, `i ∈ C`, are linearly
dependent: `∑_{i ∈ C} hᵢ xᵢ xᵢᵀ = 0` for some `h ≠ 0` supported on `C`. Taking traces gives
`∑ hᵢ |xᵢ|² = 0`, so `h` has a negative entry. Let `t* = min {-1/hᵢ : hᵢ < 0}` and
`c = 1 + t* h`. Then `c ≥ 0`, `cᵢ = 0` where the minimum is attained, `cᵢ = 1` for `i ∉ C`, and
`c` satisfies the identity of Lemma C. By Lemma C, `(S₀, Diag(cᵢ dᵢ))` is a maximizer of
`Π(2, m)` with smaller support, a contradiction. -/
theorem card_le_three_of_isCoclique {S : Matrix (Fin m) (Fin m) ℝ} {w : Fin m → ℝ}
    (hmax : IsMaximizer S w) (hpos : ∀ i, 0 < w i) (hm : 2 < m)
    (hmin : ∀ (S' : Matrix (Fin m) (Fin m) ℝ) (w' : Fin m → ℝ), IsMaximizer S' w' → ∀ i, 0 < w' i)
    {C : Finset (Fin m)} (hC : IsCoclique S (C : Set (Fin m))) : C.card ≤ 3 := by
  classical
  by_contra hC4
  push Not at hC4
  -- after switching, `S₀[C, C] = J_C`
  obtain ⟨ε, hε, hSC⟩ := (isCoclique_iff_exists_switch hmax.isSignMatrix _).mp hC
  have hmax₁ := hmax.switch hε
  have hS₁C : ∀ i ∈ C, ∀ j ∈ C, switch S ε i j = 1 := by
    intro i hi j hj
    simp only [switch, of_apply, hSC i hi j hj]
    linear_combination (ε j * ε j) * hε.mul_self i + hε.mul_self j
  -- the vectors `xᵢ = (uᵢ, vᵢ)` of Lemma B for the switched maximizer
  obtain ⟨u, v, huv, hval⟩ := exists_fanValue_eq_sumTopTwo
    (isHermitian_weightedMatrix hmax₁.isSignMatrix w) (by simp; omega)
  have hsign := hmax₁.mul_projPair_pos hpos (by simpa using hm) huv hval
  have hCpos : ∀ i ∈ C, ∀ j ∈ C, 0 < u i * u j + v i * v j := by
    intro i hi j hj
    have := hsign i j
    rwa [hS₁C i hi j hj, one_mul] at this
  have hdiag : ∀ i, 0 < u i * u i + v i * v i := by
    intro i
    have := hsign i i
    rwa [hmax₁.isSignMatrix.diag, one_mul] at this
  -- a linear relation `∑_{i ∈ C} hᵢ xᵢ xᵢᵀ = 0`
  obtain ⟨h, hsupp, ⟨i₁, hi₁C, hi₁⟩, hrel⟩ := exists_relation_of_three_lt_card u v hC4
  -- taking traces: `∑ hᵢ |xᵢ|² = 0`
  have htr : ∑ i ∈ C, h i * (u i * u i + v i * v i) = 0 := by
    have e00 := congrFun (congrFun hrel 0) 0
    have e11 := congrFun (congrFun hrel 1) 1
    simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul,
      Matrix.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at e00 e11
    calc ∑ i ∈ C, h i * (u i * u i + v i * v i)
        = ∑ i ∈ C, h i * (u i * u i) + ∑ i ∈ C, h i * (v i * v i) := by
          rw [← sum_add_distrib]
          exact sum_congr rfl fun i _ => by ring
      _ = 0 := by rw [e00, e11, add_zero]
  -- so `h` has a negative entry
  obtain ⟨i₂, hi₂C, hi₂⟩ : ∃ i ∈ C, h i < 0 := by
    by_contra hcon
    push Not at hcon
    have hz := (sum_eq_zero_iff_of_nonneg fun i hi =>
      mul_nonneg (hcon i hi) (hdiag i).le).mp htr i₁ hi₁C
    rcases mul_eq_zero.mp hz with h0 | h0
    · exact hi₁ h0
    · exact (hdiag i₁).ne' h0
  -- `t* = min {-1/hᵢ : hᵢ < 0}` and `c = 1 + t* h`
  set N := C.filter fun i => h i < 0 with hN_def
  have hN : N.Nonempty := ⟨i₂, by simp [hN_def, hi₂C, hi₂]⟩
  obtain ⟨i₀, hi₀N, hmin₀⟩ := N.exists_min_image (fun i => -1 / h i) hN
  simp only [hN_def, mem_filter] at hi₀N
  set t : ℝ := -1 / h i₀ with ht_def
  have ht : 0 < t := div_pos_of_neg_of_neg (by norm_num) hi₀N.2
  set c : Fin m → ℝ := fun i => 1 + t * h i with hc_def
  have hc0 : ∀ i, 0 ≤ c i := by
    intro i
    by_cases hi : i ∈ C ∧ h i < 0
    · have hle : t ≤ -1 / h i := hmin₀ i (by simp [hN_def, hi.1, hi.2])
      have e : -1 / h i * h i = -1 := div_mul_cancel₀ _ hi.2.ne
      have : -1 ≤ t * h i := by nlinarith [hi.2]
      simp only [hc_def]
      linarith
    · have : 0 ≤ h i := by
        by_cases hiC : i ∈ C
        · push Not at hi
          exact hi hiC
        · rw [hsupp i hiC]
      simp only [hc_def]
      nlinarith
  have hc1 : ∀ i, i ∉ C → c i = 1 := fun i hi => by simp [hc_def, hsupp i hi]
  have hci₀ : c i₀ = 0 := by
    simp only [hc_def, ht_def]
    field_simp [hi₀N.2.ne]
    ring
  have hcC : ∑ i ∈ C, c i • vecMulVec ![u i, v i] ![u i, v i] =
      ∑ i ∈ C, vecMulVec ![u i, v i] ![u i, v i] := by
    have e : ∀ i, c i • vecMulVec ![u i, v i] ![u i, v i] =
        vecMulVec ![u i, v i] ![u i, v i] + t • (h i • vecMulVec ![u i, v i] ![u i, v i]) := by
      intro i
      simp only [hc_def, add_smul, one_smul, smul_smul]
    rw [sum_congr rfl fun i _ => e i, sum_add_distrib, ← smul_sum, hrel, smul_zero, add_zero]
  -- by Lemma C, `(S₀, Diag(cᵢ dᵢ))` is a maximizer with a vanishing weight
  have hmaxc := hmax₁.clone hpos hm huv hval (C := C) (fun i hi j hj => (hCpos i hi j hj).le)
    hc0 hc1 hcC
  have := hmin _ _ hmaxc i₀
  rw [hci₀, zero_mul] at this
  exact lt_irrefl 0 this

end Step3

/-! ### Step 4: classification -/

section Step4

variable {ι κ : Type*}

/-- Cocliques pull back along blow-ups and switchings. -/
lemma isCoclique_preimage {S : Matrix ι ι ℝ} {T : Matrix κ κ ℝ} {f : ι → κ} {ε : ι → ℝ}
    (hε : IsSignVector ε) (hST : ∀ i j, S i j = ε i * ε j * T (f i) (f j)) {C : Set κ}
    (hC : IsCoclique T C) : IsCoclique S (f ⁻¹' C) := by
  intro i hi j hj k hk hcoh
  apply hC (f i) hi (f j) hj (f k) hk
  unfold Coherent at hcoh ⊢
  rw [hST, hST, hST] at hcoh
  linear_combination hcoh - (T (f i) (f j) * T (f i) (f k) * T (f j) (f k)) *
    ((ε j * ε j) * (ε k * ε k) * hε.mul_self i + (ε k * ε k) * hε.mul_self j + hε.mul_self k)

lemma IsCoclique.subset {S : Matrix ι ι ℝ} {C D : Set ι} (hD : IsCoclique S D) (hCD : C ⊆ D) :
    IsCoclique S C :=
  fun i hi j hj k hk => hD i (hCD hi) j (hCD hj) k (hCD hk)

variable {m : ℕ}

/-- **Step 4** (classification). Let `(S₀, D₀)` be a maximizer of `Π(2, m)`, `m > 2`, such that
`[S₀]` is `K₄`-free, has no twins and no coclique of order `4`, and such that `S₀` is the sign
pattern of vectors `xᵢ = (uᵢ, vᵢ)` in the plane (Lemma B(b)). Then
`Π(2, S₀) ≤ max {Π(2, R₃), Π(2, R₅)}`.

*Proof of the errata.* By (FF), up to switching and permutation, `S₀` is either `R_{2N+1}` for
some `N ≥ 1` or a principal submatrix `B` of `A₆`; the blow-up is trivial because `S₀` has no
twins. If `S₀ = R_{2N+1}`, then by (R1) it has a coclique with `N + 1` elements, and Step 3 gives
`N ≤ 2`. If `S₀ = B`, then `B ≠ A₆` by Lemma B(b) and Lemma D, so `B` is a principal submatrix of
a `5 × 5` principal submatrix of `A₆`, and `Π(2, S₀) ≤ Π(2, R₅)` by (A1). -/
theorem supWeights_le_max_of_minimal {S : Matrix (Fin m) (Fin m) ℝ} (hS : IsSignMatrix S)
    (hm : 2 < m) (hK4 : K4Free S) (htw : ∀ i j, ¬IsTwin S i j)
    (hcocl : ∀ C : Finset (Fin m), IsCoclique S (C : Set (Fin m)) → C.card ≤ 3) {u v : Fin m → ℝ}
    (hsign : ∀ i j, 0 < S i j * (u i * u j + v i * v j)) :
    supWeights S ≤ max (supWeights R3) (supWeights R5) := by
  classical
  rcases classification_of_forall_not_isTwin hS hK4 (by simp; omega) htw with
    ⟨N, e, hN, ε, hε, hSε⟩ | ⟨f, hf, ε, hε, hSε⟩
  · -- `S₀ = R_{2N+1}`: by (R1) and Step 3, `N ≤ 2`
    have hN2 : N + 1 ≤ 3 := by
      set C : Finset (Fin m) :=
        (univ : Finset (Fin (N + 1))).image fun a => e.symm (Fin.castLE (by omega) a) with hC_def
      have hinj : Function.Injective fun a : Fin (N + 1) => e.symm (Fin.castLE (by omega) a) :=
        fun a b hab => Fin.castLE_injective _ (e.symm.injective hab)
      have hcard : C.card = N + 1 := by
        rw [hC_def, card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
      have hCc : IsCoclique S (C : Set (Fin m)) := by
        refine (isCoclique_preimage (T := polygonMatrix N) (f := e) hε hSε
          (isCoclique_polygonMatrix N)).subset ?_
        intro i hi
        simp only [hC_def, coe_image, coe_univ, Set.image_univ, Set.mem_range] at hi
        obtain ⟨a, rfl⟩ := hi
        exact ⟨a, (e.apply_symm_apply _).symm⟩
      exact hcard ▸ hcocl C hCc
    have hSR := supWeights_eq_of_equiv hS (isSignMatrix_polygonMatrix N) e hε.mul_self hSε
    rcases (by omega : N = 1 ∨ N = 2) with rfl | rfl
    · rw [hSR, supWeights_polygonMatrix_one]
      exact le_max_left _ _
    · rw [hSR, supWeights_polygonMatrix_two]
      exact le_max_right _ _
  · -- `S₀` is a principal submatrix of `A₆`
    by_cases hsurj : Function.Surjective f
    · -- `S₀ = A₆` is excluded by Lemma B(b) and Lemma D
      exfalso
      set e := Equiv.ofBijective f ⟨hf, hsurj⟩
      have hfe : ∀ a, f (e.symm a) = a := fun a => Equiv.ofBijective_apply_symm_apply f _ a
      refine not_signPattern_A6_of_switch hsign e.symm (fun a => ε (e.symm a))
        (fun a => hε.mul_self _) fun a b => ?_
      rw [hSε, submatrix_apply, hfe, hfe]
    · -- a principal submatrix of `A₆ ∖ {k}`, which is `R₅` by (A1)
      simp only [Function.Surjective, not_forall, not_exists] at hsurj
      obtain ⟨k, hk⟩ := hsurj
      refine le_trans ?_ (le_max_right _ _)
      refine supWeights_le_of_transfer isSignMatrix_R5 (f := fun i => certMap k (f i))
        (fun i j hij => hf (certMap_injective k (f i) (f j) (hk i) (hk j) hij))
        (ε := fun i => ε i * certSign k (f i)) (fun i => ?_) fun i j => ?_
      · linear_combination (certSign k (f i) * certSign k (f i)) * hε.mul_self i
          + certSign_mul_self k (f i)
      · rw [hSε, submatrix_apply, A6_eq_certificate k (f i) (f j) (hk i) (hk j)]
        ring

end Step4

/-! ### Proof of Theorem A -/

/-- `Π(2, d) ≤ max {Π(2, R₃), Π(2, R₅)}` for `d > 2`: Steps 1–4 applied to a maximizer of minimal
support. -/
theorem supConfigs_le_max_of_two_lt {d : ℕ} (hd : 2 < d) :
    supConfigs (Fin d) ≤ max (supWeights R3) (supWeights R5) := by
  have h43 := four_thirds_le_supConfigs (d := d) (by omega)
  -- a maximizer of `Π(2, d)` of minimal support, restricted to its support
  obtain ⟨m, S₀, w₀, hmax, hpos, hsup, hmin⟩ := exists_minimal_maximizer (ι := Fin d)
    (by linarith)
  rw [← hsup] at h43 ⊢
  have h1 : 1 < supConfigs (Fin m) := by linarith
  -- Step 1: `m ≥ 3`, and Lemma B applies
  have hm := three_le_of_isMaximizer hmax h1
  obtain ⟨u, v, huv, hval⟩ := exists_fanValue_eq_sumTopTwo
    (isHermitian_weightedMatrix hmax.isSignMatrix w₀) (by simp; omega)
  have hsign := hmax.mul_projPair_pos hpos (by simp; omega) huv hval
  have hK4 := k4Free_of_mul_projPair_pos hmax.isSignMatrix hsign
  -- Step 2: no twins
  have htw := not_isTwin_of_minimal hmax h1 hmin
  -- Step 3: no coclique of order `4`
  have hcocl : ∀ C : Finset (Fin m), IsCoclique S₀ (C : Set (Fin m)) → C.card ≤ 3 :=
    fun C hC => card_le_three_of_isCoclique hmax hpos (by omega) hmin hC
  -- Step 4: classification
  calc supConfigs (Fin m) = π₂ (weightedMatrix S₀ w₀) := hmax.sumTopTwo_eq.symm
    _ ≤ supWeights S₀ := sumTopTwo_le_supWeights hmax.isSignMatrix hmax.isWeight
    _ ≤ max (supWeights R3) (supWeights R5) :=
        supWeights_le_max_of_minimal hmax.isSignMatrix (by omega) hK4 htw hcocl hsign

/-- `Π(2, d) ≤ max {Π(2, R₃), Π(2, R₅)}` for all `d`. -/
theorem supConfigs_le_max (d : ℕ) : supConfigs (Fin d) ≤ max (supWeights R3) (supWeights R5) :=
  (supConfigs_le_of_injective (Fin.castLE_injective (by omega : d ≤ d + 3))).trans
    (supConfigs_le_max_of_two_lt (by omega))

/-- **Theorem A** (Reduction). `Π₂ = max {Π(2, R₃), Π(2, R₅)}`. -/
theorem maxProjConst_two_eq_max : maxProjConst ℝ 2 = max (supWeights R3) (supWeights R5) := by
  refine le_antisymm (maxProjConst_two_le supConfigs_le_max) (max_le ?_ ?_)
  · exact (supWeights_le_supConfigs isSignMatrix_R3).trans (supConfigs_le_maxProjConst_two _)
  · exact (supWeights_le_supConfigs isSignMatrix_R5).trans (supConfigs_le_maxProjConst_two _)

/-- **Theorem A**, with `R₃` and `R₅` the block matrices `R_{2N+1}` of [JFA, Section 4.1] for
`N = 1, 2`. -/
theorem maxProjConst_two_eq_max_blockR :
    maxProjConst ℝ 2 = max (supWeights (blockR 1)) (supWeights (blockR 2)) := by
  rw [supWeights_blockR, supWeights_blockR, supWeights_polygonMatrix_one,
    supWeights_polygonMatrix_two]
  exact maxProjConst_two_eq_max

end Grunbaum
