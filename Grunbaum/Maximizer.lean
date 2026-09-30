/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import Grunbaum.Fan
import Grunbaum.Transfer
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# `Π(2, S)`, `Π(2, d)` and maximizers

For a finite index type `ι` we define, in the notation of the errata,

* `Grunbaum.supWeights S = Π(2, S) = sup { π₂(√D S √D) : D ∈ 𝒟 }`;
* `Grunbaum.supConfigs ι = sup { π₂(√D S √D) : S ∈ 𝒜, D ∈ 𝒟 }`. By the formula of Chalmers and
  Lewicki (`Grunbaum.maxRelProjConst_two_eq_supConfigs`), for `ι = Fin d` this is `Π(2, d)`,
  the maximal relative projection constant of two-dimensional subspaces of `ℓ∞^d`;
* `Grunbaum.IsMaximizer S w` : `(S, D)` is a *maximizer* of `Π(2, ι)`.

## Main results

* `Grunbaum.exists_isMaximizer` : maximizers exist, since `w ↦ π₂(√D S √D)` is continuous, the
  simplex is compact and `𝒜` is finite;
* `Grunbaum.supWeights_le_of_transfer`, `Grunbaum.supConfigs_le_of_injective` : principal
  submatrices, switching and relabelling ("extend the weights by zero");
* `Grunbaum.sumTopTwo_le_restrict` : if `π₂(√D S √D) > 1`, then this value is attained after
  restricting `(S, D)` to the support of `D`;
* `Grunbaum.exists_minimal_maximizer` : the first step of the proof of Theorem A in the errata:
  a maximizer of `Π(2, d)` with the smallest possible support, restricted to its support.

The existence of maximizers is adapted from `ProjectionConstants/Grunbaum/Exists.lean` of the
library *Projection constants in Lean*.
-/

open Finset Matrix

namespace Grunbaum

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! ### Definitions -/

/-- `Π(2, S) = sup { π₂(√D S √D) : D ∈ 𝒟 }`. (The errata writes `π₂(SD)`, which has the same
value.) -/
noncomputable def supWeights (S : Matrix ι ι ℝ) : ℝ :=
  sSup ((fun w => π₂ (weightedMatrix S w)) '' {w | IsWeight w})

variable (ι) in
/-- `Π(2, ι) = sup { π₂(√D S √D) : S ∈ 𝒜, D ∈ 𝒟 }`. For `ι = Fin d`, this is `Π(2, d)` by the
formula of Chalmers and Lewicki (`Grunbaum.maxRelProjConst_two_eq_supConfigs`). -/
noncomputable def supConfigs : ℝ :=
  sSup {x | ∃ (S : Matrix ι ι ℝ) (w : ι → ℝ), IsSignMatrix S ∧ IsWeight w ∧
    x = π₂ (weightedMatrix S w)}

/-- `(S, D)` is a **maximizer** of `Π(2, ι)`: `S ∈ 𝒜`, `D ∈ 𝒟` and `π₂(√D S √D)` is maximal. -/
structure IsMaximizer (S : Matrix ι ι ℝ) (w : ι → ℝ) : Prop where
  isSignMatrix : IsSignMatrix S
  isWeight : IsWeight w
  le : ∀ (S' : Matrix ι ι ℝ) (w' : ι → ℝ), IsSignMatrix S' → IsWeight w' →
    π₂ (weightedMatrix S' w') ≤ π₂ (weightedMatrix S w)

/-! ### Bounds -/

/-- `π₂(√D S √D) ≤ 2`, since `uᵀ(√D S √D)u ≤ |u|²`. -/
lemma sumTopTwo_weightedMatrix_le_two {S : Matrix ι ι ℝ} {w : ι → ℝ} (hS : IsSignMatrix S)
    (hw : IsWeight w) : π₂ (weightedMatrix S w) ≤ 2 :=
  sumTopTwo_le' (by norm_num) fun _ _ h => by
    have h1 := dotProduct_mulVec_weightedMatrix_le_one hS hw h.norm_left
    have h2 := dotProduct_mulVec_weightedMatrix_le_one hS hw h.norm_right
    simp only [fanValue]
    linarith

lemma bddAbove_supWeights_set (S : Matrix ι ι ℝ) (hS : IsSignMatrix S) :
    BddAbove ((fun w => π₂ (weightedMatrix S w)) '' {w | IsWeight w}) :=
  ⟨2, by rintro _ ⟨w, hw, rfl⟩; exact sumTopTwo_weightedMatrix_le_two hS hw⟩

lemma bddAbove_supConfigs_set : BddAbove {x | ∃ (S : Matrix ι ι ℝ) (w : ι → ℝ),
    IsSignMatrix S ∧ IsWeight w ∧ x = π₂ (weightedMatrix S w)} :=
  ⟨2, by rintro _ ⟨S, w, hS, hw, rfl⟩; exact sumTopTwo_weightedMatrix_le_two hS hw⟩

lemma sumTopTwo_le_supWeights {S : Matrix ι ι ℝ} {w : ι → ℝ} (hS : IsSignMatrix S)
    (hw : IsWeight w) : π₂ (weightedMatrix S w) ≤ supWeights S :=
  le_csSup (bddAbove_supWeights_set S hS) ⟨w, hw, rfl⟩

lemma sumTopTwo_le_supConfigs {S : Matrix ι ι ℝ} {w : ι → ℝ} (hS : IsSignMatrix S)
    (hw : IsWeight w) : π₂ (weightedMatrix S w) ≤ supConfigs ι :=
  le_csSup bddAbove_supConfigs_set ⟨S, w, hS, hw, rfl⟩

lemma supConfigs_nonneg : 0 ≤ supConfigs ι :=
  Real.sSup_nonneg (by rintro _ ⟨S, w, hS, hw, rfl⟩; exact sumTopTwo_weightedMatrix_nonneg hS hw)

lemma supConfigs_le {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ (S : Matrix ι ι ℝ) (w : ι → ℝ), IsSignMatrix S → IsWeight w →
      π₂ (weightedMatrix S w) ≤ c) : supConfigs ι ≤ c :=
  Real.sSup_le (by rintro _ ⟨S, w, hS, hw, rfl⟩; exact h S w hS hw) hc

lemma supWeights_le {S : Matrix ι ι ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ w, IsWeight w → π₂ (weightedMatrix S w) ≤ c) : supWeights S ≤ c :=
  Real.sSup_le (by rintro _ ⟨w, hw, rfl⟩; exact h w hw) hc

lemma supWeights_le_supConfigs {S : Matrix ι ι ℝ} (hS : IsSignMatrix S) :
    supWeights S ≤ supConfigs ι :=
  supWeights_le supConfigs_nonneg fun _ hw => sumTopTwo_le_supConfigs hS hw

/-- The value of a maximizer is `Π(2, ι)`. -/
lemma IsMaximizer.sumTopTwo_eq {S : Matrix ι ι ℝ} {w : ι → ℝ} (h : IsMaximizer S w) :
    π₂ (weightedMatrix S w) = supConfigs ι :=
  le_antisymm (sumTopTwo_le_supConfigs h.isSignMatrix h.isWeight)
    (supConfigs_le (sumTopTwo_weightedMatrix_nonneg h.isSignMatrix h.isWeight)
      fun S' w' hS' hw' => h.le S' w' hS' hw')

/-- A configuration attaining `Π(2, ι)` is a maximizer. -/
lemma isMaximizer_of_le {S : Matrix ι ι ℝ} {w : ι → ℝ} (hS : IsSignMatrix S) (hw : IsWeight w)
    (h : supConfigs ι ≤ π₂ (weightedMatrix S w)) : IsMaximizer S w :=
  ⟨hS, hw, fun _ _ hS' hw' => (sumTopTwo_le_supConfigs hS' hw').trans h⟩

/-! ### Existence of maximizers -/

/-- `fanValue` is linear in the matrix. -/
lemma fanValue_sub (A B : Matrix ι ι ℝ) (x y : ι → ℝ) :
    fanValue (A - B) x y = fanValue A x y - fanValue B x y := by
  simp only [fanValue, sub_mulVec, dotProduct_sub]
  ring

/-- `π₂` is Lipschitz in the entries. -/
lemma sumTopTwo_le_add (A B : Matrix ι ι ℝ) :
    π₂ A ≤ π₂ B + 2 * ∑ k, ∑ l, |A k l - B k l| := by
  by_cases hne : (fanValues A).Nonempty
  · refine sumTopTwo_le hne fun x y hxy => ?_
    have h1 := fanValue_le_sumTopTwo B hxy
    have h2 := fanValue_le_sum_abs (A - B) hxy
    simp only [Matrix.sub_apply] at h2
    have := fanValue_sub A B x y
    linarith
  · have hne' : ¬(fanValues B).Nonempty := by rwa [← fanValues_nonempty_iff A B]
    rw [sumTopTwo_of_not_nonempty hne, sumTopTwo_of_not_nonempty hne']
    positivity

lemma continuous_sumTopTwo_weightedMatrix (S : Matrix ι ι ℝ) :
    Continuous fun w : ι → ℝ => π₂ (weightedMatrix S w) := by
  rw [Metric.continuous_iff]
  intro w₀ ε hε
  set R : (ι → ℝ) → ℝ :=
    fun w => 2 * ∑ k, ∑ l, |weightedMatrix S w k l - weightedMatrix S w₀ k l| with hRdef
  have hR : Continuous R := by
    simp only [hRdef, weightedMatrix, of_apply]
    fun_prop
  have hR0 : R w₀ = 0 := by simp [hRdef]
  obtain ⟨δ, hδ, hδR⟩ := Metric.continuous_iff.mp hR w₀ ε hε
  refine ⟨δ, hδ, fun w hw => ?_⟩
  have hRw : R w < ε := by
    have := hδR w hw
    rw [hR0, Real.dist_eq, sub_zero] at this
    exact lt_of_abs_lt this
  have h1 := sumTopTwo_le_add (weightedMatrix S w) (weightedMatrix S w₀)
  have h2 := sumTopTwo_le_add (weightedMatrix S w₀) (weightedMatrix S w)
  have hsymm : ∑ k, ∑ l, |weightedMatrix S w₀ k l - weightedMatrix S w k l|
      = ∑ k, ∑ l, |weightedMatrix S w k l - weightedMatrix S w₀ k l| :=
    sum_congr rfl fun k _ => sum_congr rfl fun l _ => abs_sub_comm _ _
  rw [hsymm] at h2
  rw [Real.dist_eq, abs_lt]
  simp only [hRdef] at hRw
  constructor <;> linarith

omit [Fintype ι] in
/-- The sign matrices form a finite set. -/
lemma finite_isSignMatrix [Finite ι] : Set.Finite {S : Matrix ι ι ℝ | IsSignMatrix S} := by
  apply (Set.finite_range fun b : ι → ι → Bool =>
    (of fun i j => if b i j then (1 : ℝ) else -1)).subset
  intro S hS
  refine ⟨fun i j => decide (S i j = 1), ?_⟩
  ext i j
  simp only [of_apply]
  rcases (hS : IsSignMatrix S).sign i j with h | h
  · simp [h]
  · simp [h]; norm_num

/-- The weights form a compact set. -/
lemma isCompact_setOf_isWeight : IsCompact {w : ι → ℝ | IsWeight w} := by
  have hset : {w : ι → ℝ | IsWeight w} = (⋂ i, {w : ι → ℝ | 0 ≤ w i}) ∩ {w | ∑ i, w i = 1} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨fun h => ⟨h.nonneg, h.sum_eq⟩, fun h => ⟨h.1, h.2⟩⟩
  have hclosed : IsClosed {w : ι → ℝ | IsWeight w} := by
    rw [hset]
    exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_eq (by fun_prop) continuous_const)
  refine IsCompact.of_isClosed_subset (isCompact_Icc (a := (0 : ι → ℝ)) (b := 1)) hclosed ?_
  intro w hw
  refine ⟨fun i => (hw : IsWeight w).nonneg i, fun i => ?_⟩
  change w i ≤ 1
  rw [← hw.sum_eq]
  exact single_le_sum (f := w) (fun j _ => hw.nonneg j) (mem_univ i)

lemma exists_isWeight [Nonempty ι] : ∃ w : ι → ℝ, IsWeight w := by
  classical
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact ⟨Pi.single i 1, fun k => by by_cases h : k = i <;> simp [h], by simp⟩

/-- `Π(2, S)` is attained. -/
theorem exists_supWeights_eq [Nonempty ι] (S : Matrix ι ι ℝ) (hS : IsSignMatrix S) :
    ∃ w, IsWeight w ∧ π₂ (weightedMatrix S w) = supWeights S := by
  obtain ⟨w₀, hw₀⟩ := exists_isWeight (ι := ι)
  obtain ⟨w, hw, hmax⟩ := isCompact_setOf_isWeight.exists_isMaxOn ⟨w₀, hw₀⟩
    (continuous_sumTopTwo_weightedMatrix S).continuousOn
  refine ⟨w, hw, le_antisymm (sumTopTwo_le_supWeights hS hw) ?_⟩
  exact supWeights_le (sumTopTwo_weightedMatrix_nonneg hS hw) fun w' hw' => hmax hw'

/-- **Existence of maximizers** of `Π(2, ι)`. -/
theorem exists_isMaximizer [Nonempty ι] :
    ∃ (S : Matrix ι ι ℝ) (w : ι → ℝ), IsMaximizer S w := by
  have hmaxw : ∀ S : Matrix ι ι ℝ, ∃ w, IsWeight w ∧
      ∀ w', IsWeight w' → π₂ (weightedMatrix S w') ≤ π₂ (weightedMatrix S w) := by
    intro S
    obtain ⟨w₀, hw₀⟩ := exists_isWeight (ι := ι)
    obtain ⟨w, hw, hmax⟩ := isCompact_setOf_isWeight.exists_isMaxOn ⟨w₀, hw₀⟩
      (continuous_sumTopTwo_weightedMatrix S).continuousOn
    exact ⟨w, hw, fun w' hw' => hmax hw'⟩
  choose W hW hWmax using hmaxw
  obtain ⟨S, hS, hSmax⟩ := Set.exists_max_image _ (fun S => π₂ (weightedMatrix S (W S)))
    finite_isSignMatrix ⟨_, IsSignMatrix.ones⟩
  exact ⟨S, W S, hS, hW S, fun S' w' hS' hw' => (hWmax S' w' hw').trans (hSmax S' hS')⟩

/-! ### Principal submatrices, switching and relabelling -/

/-- If `S i j = εᵢ εⱼ T (f i) (f j)` with `f` injective, then `Π(2, S) ≤ Π(2, T)`. -/
theorem supWeights_le_of_transfer {S : Matrix ι ι ℝ} {T : Matrix κ κ ℝ} (hT : IsSignMatrix T)
    {f : ι → κ} (hf : Function.Injective f) {ε : ι → ℝ} (hε : ∀ i, ε i * ε i = 1)
    (hST : ∀ i j, S i j = ε i * ε j * T (f i) (f j)) :
    supWeights S ≤ supWeights T := by
  refine supWeights_le ?_ fun w hw => ?_
  · by_cases h : Nonempty κ
    · obtain ⟨w, hw⟩ := exists_isWeight (ι := κ)
      exact (sumTopTwo_weightedMatrix_nonneg hT hw).trans (sumTopTwo_le_supWeights hT hw)
    · rw [not_nonempty_iff] at h
      simp [supWeights, Set.image, show {w : κ → ℝ | IsWeight w} = ∅ from
        Set.eq_empty_of_forall_notMem fun w hw => by simpa using (hw : IsWeight w).sum_eq]
  · exact (sumTopTwo_weightedMatrix_le_of_transfer hT hw hf hε hST).trans
      (sumTopTwo_le_supWeights hT (isWeight_extend hf hw))

/-- `Π(2, S)` is invariant under switching and relabelling. -/
theorem supWeights_eq_of_equiv {S : Matrix ι ι ℝ} {T : Matrix κ κ ℝ} (hS : IsSignMatrix S)
    (hT : IsSignMatrix T) (e : ι ≃ κ) {ε : ι → ℝ} (hε : ∀ i, ε i * ε i = 1)
    (hST : ∀ i j, S i j = ε i * ε j * T (e i) (e j)) : supWeights S = supWeights T := by
  refine le_antisymm (supWeights_le_of_transfer hT e.injective hε hST)
    (supWeights_le_of_transfer hS e.symm.injective (fun k => hε (e.symm k)) fun k l => ?_)
  rw [hST, e.apply_symm_apply, e.apply_symm_apply]
  linear_combination (-(T k l) * ε (e.symm l) * ε (e.symm l)) * hε (e.symm k)
    - T k l * hε (e.symm l)

/-- Extension of a matrix on `κ` to `ι` along a map `f : κ → ι`, by ones outside the range. -/
noncomputable def extendSign (f : κ → ι) (S : Matrix κ κ ℝ) : Matrix ι ι ℝ :=
  of fun i j =>
    Function.extend f (fun a => Function.extend f (fun b => S a b) (fun _ => 1) j) (fun _ => 1) i

omit [Fintype ι] [Fintype κ] in
lemma extendSign_apply {f : κ → ι} (hf : Function.Injective f) (S : Matrix κ κ ℝ) (a b : κ) :
    extendSign f S (f a) (f b) = S a b := by
  simp [extendSign, hf.extend_apply]

omit [Fintype ι] [Fintype κ] in
lemma extendSign_apply_of_notMem_left {f : κ → ι} (S : Matrix κ κ ℝ) {i : ι}
    (hi : ¬∃ a, f a = i) (j : ι) : extendSign f S i j = 1 := by
  simp [extendSign, Function.extend_apply' _ _ _ hi]

omit [Fintype ι] [Fintype κ] in
lemma extendSign_apply_of_notMem_right {f : κ → ι} (hf : Function.Injective f)
    (S : Matrix κ κ ℝ) (i : ι) {j : ι} (hj : ¬∃ b, f b = j) : extendSign f S i j = 1 := by
  by_cases hi : ∃ a, f a = i
  · obtain ⟨a, rfl⟩ := hi
    simp [extendSign, hf.extend_apply, Function.extend_apply' _ _ _ hj]
  · exact extendSign_apply_of_notMem_left S hi j

omit [Fintype ι] [Fintype κ] in
lemma isSignMatrix_extendSign {f : κ → ι} (hf : Function.Injective f) {S : Matrix κ κ ℝ}
    (hS : IsSignMatrix S) : IsSignMatrix (extendSign f S) := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun i => ?_⟩
  · by_cases hi : ∃ a, f a = i
    · by_cases hj : ∃ b, f b = j
      · obtain ⟨a, rfl⟩ := hi
        obtain ⟨b, rfl⟩ := hj
        rw [extendSign_apply hf, extendSign_apply hf, hS.symm]
      · rw [extendSign_apply_of_notMem_left S hj, extendSign_apply_of_notMem_right hf S i hj]
    · rw [extendSign_apply_of_notMem_left S hi, extendSign_apply_of_notMem_right hf S j hi]
  · by_cases hi : ∃ a, f a = i
    · by_cases hj : ∃ b, f b = j
      · obtain ⟨a, rfl⟩ := hi
        obtain ⟨b, rfl⟩ := hj
        rw [extendSign_apply hf]
        exact hS.sign a b
      · exact Or.inl (extendSign_apply_of_notMem_right hf S i hj)
    · exact Or.inl (extendSign_apply_of_notMem_left S hi j)
  · by_cases hi : ∃ a, f a = i
    · obtain ⟨a, rfl⟩ := hi
      rw [extendSign_apply hf]
      exact hS.diag a
    · exact extendSign_apply_of_notMem_left S hi i

/-- Padding with zero weights: `Π(2, κ) ≤ Π(2, ι)` if `κ` embeds into `ι`. -/
theorem supConfigs_le_of_injective {f : κ → ι} (hf : Function.Injective f) :
    supConfigs κ ≤ supConfigs ι := by
  refine supConfigs_le supConfigs_nonneg fun S w hS hw => ?_
  exact (sumTopTwo_weightedMatrix_le_of_transfer (isSignMatrix_extendSign hf hS) hw hf
    (ε := fun _ => 1) (fun _ => by norm_num)
    (fun a b => by rw [extendSign_apply hf]; ring)).trans
    (sumTopTwo_le_supConfigs (isSignMatrix_extendSign hf hS) (isWeight_extend hf hw))

/-- `Π(2, ι)` only depends on the cardinality of `ι`. -/
theorem supConfigs_congr (e : κ ≃ ι) : supConfigs κ = supConfigs ι :=
  le_antisymm (supConfigs_le_of_injective e.injective)
    (supConfigs_le_of_injective e.symm.injective)

/-! ### Restriction to the support -/

/-- If the weights vanish outside `T` and `π₂(√D S √D) > 1`, then the value `π₂(√D S √D)` is
attained by the restriction of `(S, D)` to `T`: the top eigenvectors vanish outside `T`. -/
theorem sumTopTwo_le_restrict {S : Matrix ι ι ℝ} {w : ι → ℝ} (hS : IsSignMatrix S)
    (hw : IsWeight w) (T : Finset ι) (hT : ∀ j, j ∉ T → w j = 0)
    (hgt : 1 < π₂ (weightedMatrix S w)) :
    π₂ (weightedMatrix S w) ≤
      π₂ (weightedMatrix (fun a b : T => S a b) (fun a : T => w a)) := by
  classical
  set M := weightedMatrix S w with hM
  have hA : M.IsHermitian := isHermitian_weightedMatrix hS w
  -- `ι` has at least two elements
  have h2 : 1 < Fintype.card ι := by
    by_contra h
    push Not at h
    have hne : ¬(fanValues M).Nonempty := by
      rintro ⟨_, x, y, hxy, -⟩
      obtain ⟨a, b, hab⟩ := exists_ne_of_isOrthonormalPair hxy
      exact hab (Fintype.card_le_one_iff.mp h a b)
    rw [sumTopTwo_of_not_nonempty hne] at hgt
    norm_num at hgt
  obtain ⟨a, b, hab, ha, hb⟩ := exists_top_two hA.eigenvalues h2
  have hval := sumTopTwo_eq_top_two hA hab ha hb
  -- both eigenvalues are positive, since `λ_a ≤ 1`
  have hla : hA.eigenvalues a ≤ 1 := by
    have := dotProduct_mulVec_weightedMatrix_le_one hS hw
      (by simp [eigenvector_dotProduct] : eigenvector hA a ⬝ᵥ eigenvector hA a = 1)
    rwa [mulVec_eigenvector, dotProduct_smul, eigenvector_dotProduct, ite_eq_left rfl,
      smul_eq_mul, mul_one] at this
  have hlb : 0 < hA.eigenvalues b := by linarith
  have hla' : 0 < hA.eigenvalues a := lt_of_lt_of_le hlb (ha b)
  -- the eigenvectors vanish outside `T`
  have hzero : ∀ k, hA.eigenvalues k ≠ 0 → ∀ j, j ∉ T → eigenvector hA k j = 0 := by
    intro k hk j hj
    have h := congrFun (mulVec_eigenvector hA k) j
    simp only [hM, mulVec, dotProduct, weightedMatrix, of_apply, hT j hj, Real.sqrt_zero,
      zero_mul, sum_const_zero, Pi.smul_apply, smul_eq_mul] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hk
  -- restrict the eigenvectors to `T`
  have hinj : Function.Injective (Subtype.val : T → ι) := Subtype.val_injective
  have hback : ∀ k, hA.eigenvalues k ≠ 0 →
      signedExtend (Subtype.val : T → ι) (fun _ => 1) (fun t => eigenvector hA k t)
        = eigenvector hA k := by
    intro k hk
    funext j
    by_cases hj : j ∈ T
    · rw [show j = ((⟨j, hj⟩ : T) : ι) from rfl, signedExtend_apply hinj]
      ring
    · rw [signedExtend_apply_of_notMem _ _ (by rintro ⟨t, rfl⟩; exact hj t.2), hzero k hk j hj]
  have hMT : ∀ s t : T, weightedMatrix (fun a b : T => S a b) (fun a : T => w a) s t
      = (fun _ : T => (1 : ℝ)) s * (fun _ : T => (1 : ℝ)) t * M s t := by
    intro s t
    simp [hM, weightedMatrix]
  have hon : IsOrthonormalPair (fun t : T => eigenvector hA a t)
      (fun t : T => eigenvector hA b t) := by
    have hε : ∀ _ : T, (1 : ℝ) * 1 = 1 := fun _ => by norm_num
    refine ⟨?_, ?_, ?_⟩
    · rw [← dotProduct_signedExtend hinj hε, hback a hla'.ne']
      simp [eigenvector_dotProduct]
    · rw [← dotProduct_signedExtend hinj hε, hback b hlb.ne']
      simp [eigenvector_dotProduct]
    · rw [← dotProduct_signedExtend hinj hε, hback a hla'.ne', hback b hlb.ne']
      simp [eigenvector_dotProduct, hab]
  refine le_trans (le_of_eq ?_) (fanValue_le_sumTopTwo _ hon)
  rw [hval, ← (fanValue_eigenvector hA hab).2]
  simp only [fanValue]
  rw [← dotProduct_mulVec_signedExtend hinj hMT, ← dotProduct_mulVec_signedExtend hinj hMT,
    hback a hla'.ne', hback b hlb.ne']

/-! ### Maximizers of minimal support -/

/-- If `Π(2, ι) > 0`, then `ι` is nonempty. -/
lemma nonempty_of_supConfigs_pos (h : 0 < supConfigs ι) : Nonempty ι := by
  by_contra hne
  rw [not_nonempty_iff] at hne
  have : supConfigs ι ≤ 0 := supConfigs_le le_rfl fun S w hS hw => by simpa using hw.sum_eq
  linarith

/-- **Maximizers of minimal support.** This is the first step of the proof of Theorem A in the
errata: *choose a maximizer of `Π(2, d)` with the smallest possible support and restrict it to its
support, of size `m`. This gives `S₀ ∈ 𝒜_m` and a positive definite `D₀ ∈ 𝒟_m` such that
`(S₀, D₀)` is a maximizer of `Π(2, m) = Π(2, d)`. Moreover, no maximizer of `Π(2, m)` has smaller
support, since padding with zero weights would give one for `Π(2, d)`.*

The restriction to the support does not change the value, since `Π(2, d) > 1`
(`Grunbaum.sumTopTwo_le_restrict`). -/
theorem exists_minimal_maximizer (h1 : 1 < supConfigs ι) :
    ∃ (m : ℕ) (S₀ : Matrix (Fin m) (Fin m) ℝ) (w₀ : Fin m → ℝ),
      IsMaximizer S₀ w₀ ∧ (∀ i, 0 < w₀ i) ∧ supConfigs (Fin m) = supConfigs ι ∧
      ∀ (S : Matrix (Fin m) (Fin m) ℝ) (w : Fin m → ℝ), IsMaximizer S w → ∀ i, 0 < w i := by
  classical
  have : Nonempty ι := nonempty_of_supConfigs_pos (by linarith)
  -- the sizes of the supports of the maximizers
  have hP : ∃ k, ∃ (S : Matrix ι ι ℝ) (w : ι → ℝ),
      IsMaximizer S w ∧ (univ.filter fun i => w i ≠ 0).card = k := by
    obtain ⟨S, w, h⟩ := exists_isMaximizer (ι := ι)
    exact ⟨_, S, w, h, rfl⟩
  obtain ⟨S, w, hmax, hcard⟩ := Nat.find_spec hP
  set m := Nat.find hP with hm
  set T := univ.filter fun i => w i ≠ 0 with hT
  let e : T ≃ Fin m := T.equivFinOfCardEq hcard
  let f : Fin m → ι := fun a => (e.symm a : ι)
  have hf : Function.Injective f := fun a b hab => e.symm.injective (Subtype.ext hab)
  have hfT : ∀ a, f a ∈ T := fun a => (e.symm a).2
  have hrange : ∀ i, (¬∃ a, f a = i) → w i = 0 := by
    intro i hi
    by_contra hwi
    exact hi ⟨e ⟨i, by simp [hT, hwi]⟩, by simp [f]⟩
  set S₀ : Matrix (Fin m) (Fin m) ℝ := fun a b => S (f a) (f b) with hS₀
  set w₀ : Fin m → ℝ := fun a => w (f a) with hw₀
  have hS₀s : IsSignMatrix S₀ :=
    ⟨fun a b => hmax.isSignMatrix.symm _ _, fun a b => hmax.isSignMatrix.sign _ _,
      fun a => hmax.isSignMatrix.diag _⟩
  have hext : Function.extend f w₀ 0 = w := by
    funext i
    by_cases hi : ∃ a, f a = i
    · obtain ⟨a, rfl⟩ := hi
      rw [hf.extend_apply]
    · rw [Function.extend_apply' _ _ _ hi, hrange i hi]
      rfl
  have hw₀w : IsWeight w₀ := by
    refine ⟨fun a => hmax.isWeight.nonneg _, ?_⟩
    rw [← hmax.isWeight.sum_eq, sum_eq_sum_comp_of_injective hf w hrange]
  have hpos : ∀ a, 0 < w₀ a := fun a =>
    lt_of_le_of_ne (hmax.isWeight.nonneg _) (Ne.symm (by simpa [hT] using hfT a))
  -- the value does not change
  have hval : π₂ (weightedMatrix S₀ w₀) = supConfigs ι := by
    rw [← hmax.sumTopTwo_eq]
    apply le_antisymm
    · have := sumTopTwo_weightedMatrix_le_of_transfer (S := S₀) hmax.isSignMatrix hw₀w hf
        (ε := fun _ => 1) (fun _ => by norm_num) (fun a b => by simp [hS₀])
      rwa [hext] at this
    · have hgt : 1 < π₂ (weightedMatrix S w) := hmax.sumTopTwo_eq ▸ h1
      refine (sumTopTwo_le_restrict hmax.isSignMatrix hmax.isWeight T
        (fun j hj => by simpa [hT] using hj) hgt).trans (le_of_eq ?_)
      refine sumTopTwo_weightedMatrix_eq_of_equiv ⟨fun a b => hmax.isSignMatrix.symm _ _,
        fun a b => hmax.isSignMatrix.sign _ _, fun a => hmax.isSignMatrix.diag _⟩ hS₀s
        ⟨fun a => hmax.isWeight.nonneg _, ?_⟩ e (ε := fun _ => 1) (fun _ => by norm_num)
        (fun a b => by simp [hS₀, f]) |>.trans ?_
      · rw [← hmax.isWeight.sum_eq]
        exact (sum_subtype T (fun i => by simp [hT]) w).symm.trans
          (sum_subset (subset_univ T) fun i _ hi => by simpa [hT] using hi)
      · congr 1
  have hsup : supConfigs (Fin m) = supConfigs ι :=
    le_antisymm (supConfigs_le_of_injective hf) (hval ▸ sumTopTwo_le_supConfigs hS₀s hw₀w)
  refine ⟨m, S₀, w₀, isMaximizer_of_le hS₀s hw₀w (hsup ▸ hval.ge), hpos, hsup, ?_⟩
  -- no maximizer of `Π(2, m)` has a zero weight
  intro S' w' hmax' i
  by_contra hle
  have hzero : w' i = 0 := le_antisymm (not_lt.mp hle) (hmax'.isWeight.nonneg i)
  set S'' := extendSign f S' with hS''
  set w'' := Function.extend f w' 0 with hw''
  have hS''s : IsSignMatrix S'' := isSignMatrix_extendSign hf hmax'.isSignMatrix
  have hw''w : IsWeight w'' := isWeight_extend hf hmax'.isWeight
  have hmax'' : IsMaximizer S'' w'' := by
    refine isMaximizer_of_le hS''s hw''w ?_
    rw [← hsup, ← hmax'.sumTopTwo_eq]
    exact sumTopTwo_weightedMatrix_le_of_transfer hS''s hmax'.isWeight hf (ε := fun _ => 1)
      (fun _ => by norm_num) (fun a b => by rw [hS'', extendSign_apply hf]; ring)
  have hsmall : (univ.filter fun k => w'' k ≠ 0).card < m := by
    calc (univ.filter fun k => w'' k ≠ 0).card
        ≤ ((univ.filter fun a => w' a ≠ 0).image f).card := by
          refine card_le_card fun k hk => ?_
          simp only [mem_filter, mem_univ, true_and] at hk
          by_cases hkf : ∃ a, f a = k
          · obtain ⟨a, rfl⟩ := hkf
            rw [hw'', hf.extend_apply] at hk
            exact mem_image_of_mem f (by simpa using hk)
          · rw [hw'', Function.extend_apply' _ _ _ hkf] at hk
            exact absurd rfl hk
      _ ≤ (univ.filter fun a => w' a ≠ 0).card := card_image_le
      _ ≤ (univ.erase i).card := card_le_card fun a ha => by
          simp only [mem_filter, mem_univ, true_and] at ha
          exact mem_erase.mpr ⟨fun h => ha (h ▸ hzero), mem_univ a⟩
      _ < m := by
          have := Fin.pos i
          rw [card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
          omega
  exact absurd (Nat.find_min' hP ⟨S'', w'', hmax'', rfl⟩) (not_le.mpr hsmall)

end Grunbaum
