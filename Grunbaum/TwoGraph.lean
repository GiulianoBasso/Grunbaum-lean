/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import Grunbaum.Basic
import FranklFuredi.Blowup
import Mathlib.Tactic.LinearCombination

/-!
# Two-graphs of sign matrices

For `S ∈ 𝒜` the errata writes `[S] := δ(S - 𝟙)` for the *two-graph* of `S`; switching does not
change it. A triple `{i, j, k}` is *coherent* if `sᵢⱼ sᵢₖ sⱼₖ = -1`, that is, if it is an edge of
`[S]`. We realize `[S]` as a 3-graph in the sense of the formalization of Frankl and Füredi
(`FranklFuredi.ThreeGraph`), so that their classification can be applied to it.

## Main definitions

* `Grunbaum.Coherent S i j k` : `sᵢⱼ sᵢₖ sⱼₖ = -1`;
* `Grunbaum.twoGraph S` : the two-graph `[S]`, as a `FranklFuredi.ThreeGraph`;
* `Grunbaum.switch S ε` : the matrix `εᵢ εⱼ sᵢⱼ` obtained from `S` by switching;
* `Grunbaum.SwitchEquiv S T` : `S` and `T` are switching equivalent;
* `Grunbaum.IsCoclique S C` : `C` contains no coherent triple;
* `Grunbaum.IsClique4 S a b c d`, `Grunbaum.K4Free S` : cliques of order `4`;
* `Grunbaum.IsTwin S i j` : `i ≠ j` are *twins*, the rows satisfy `sᵢ = ±sⱼ`.

## Main results

* `Grunbaum.switchEquiv_of_coherent_iff` : sign matrices with the same two-graph are switching
  equivalent;
* the equivalent descriptions of the errata: `Grunbaum.isCoclique_iff_exists_switch`
  ("after switching, `S[C, C] = J_C`"), `Grunbaum.isClique4_iff_exists_switch` ("after
  switching, all off-diagonal entries of `S` on it equal `-1`") and `Grunbaum.isTwin_iff`
  (twins are the pairs contained in no coherent triple);
* `Grunbaum.twoGraph_submatrix` : the two-graph of a blow-up `S(f, f)` is the blow-up of the
  two-graph (`FranklFuredi.ThreeGraph.pullback`);
* `Grunbaum.fourPointProperty_twoGraph_iff` : `[S]` is `K₄`-free iff any four indices span `0`
  or `2` coherent triples, the hypothesis of the theorem of Frankl and Füredi.
-/

open Finset Matrix

namespace Grunbaum

variable {ι κ : Type*}

/-! ### Coherent triples -/

/-- The triple `{i, j, k}` is **coherent** for `S`: `sᵢⱼ sᵢₖ sⱼₖ = -1`. -/
def Coherent (S : Matrix ι ι ℝ) (i j k : ι) : Prop := S i j * S i k * S j k = -1

section Coherent

variable {S : Matrix ι ι ℝ}

lemma coherent_swap₁₂ (hS : IsSignMatrix S) {i j k : ι} :
    Coherent S i j k ↔ Coherent S j i k := by
  unfold Coherent
  rw [hS.symm i j]
  constructor <;> intro h <;> linarith

lemma coherent_swap₂₃ {i j k : ι} (hS : IsSignMatrix S) :
    Coherent S i j k ↔ Coherent S i k j := by
  unfold Coherent
  rw [hS.symm j k]
  constructor <;> intro h <;> linarith

lemma coherent_rotate (hS : IsSignMatrix S) {i j k : ι} :
    Coherent S i j k ↔ Coherent S j k i := by
  rw [coherent_swap₁₂ hS, coherent_swap₂₃ hS]

lemma not_coherent_of_eq_left (hS : IsSignMatrix S) (i k : ι) : ¬Coherent S i i k := by
  unfold Coherent
  rw [hS.diag, one_mul, hS.mul_self_apply]
  norm_num

lemma not_coherent_of_eq_right (hS : IsSignMatrix S) (i j : ι) : ¬Coherent S i j j := by
  unfold Coherent
  rw [hS.diag, mul_one, hS.mul_self_apply]
  norm_num

lemma not_coherent_of_eq_mid (hS : IsSignMatrix S) (i j : ι) : ¬Coherent S i j i := by
  rw [coherent_swap₂₃ hS]
  exact not_coherent_of_eq_left hS i j

lemma Coherent.ne₁₂ (hS : IsSignMatrix S) {i j k : ι} (h : Coherent S i j k) : i ≠ j := by
  rintro rfl; exact not_coherent_of_eq_left hS i k h

lemma Coherent.ne₁₃ (hS : IsSignMatrix S) {i j k : ι} (h : Coherent S i j k) : i ≠ k := by
  rintro rfl; exact not_coherent_of_eq_mid hS i j h

lemma Coherent.ne₂₃ (hS : IsSignMatrix S) {i j k : ι} (h : Coherent S i j k) : j ≠ k := by
  rintro rfl; exact not_coherent_of_eq_right hS i j h

/-- For a sign matrix, `sᵢⱼ sᵢₖ sⱼₖ = 1` iff `{i, j, k}` is not coherent. -/
lemma not_coherent_iff (hS : IsSignMatrix S) {i j k : ι} :
    ¬Coherent S i j k ↔ S i j * S i k * S j k = 1 := by
  unfold Coherent
  rcases hS.sign i j with h1 | h1 <;> rcases hS.sign i k with h2 | h2 <;>
    rcases hS.sign j k with h3 | h3 <;> simp [h1, h2, h3] <;> norm_num

end Coherent

/-- Principal submatrices and blow-ups of sign matrices are sign matrices. -/
lemma IsSignMatrix.submatrix {T : Matrix κ κ ℝ} (hT : IsSignMatrix T) (f : ι → κ) :
    IsSignMatrix (T.submatrix f f) :=
  ⟨fun _ _ => hT.symm _ _, fun _ _ => hT.sign _ _, fun _ => hT.diag _⟩

/-! ### The two-graph `[S]` -/

section TwoGraph

variable [Fintype ι] [DecidableEq ι]

open Classical in
/-- The **two-graph** `[S]` of `S`: its edges are the coherent triples. -/
noncomputable def twoGraph (S : Matrix ι ι ℝ) : FranklFuredi.ThreeGraph ι where
  edges := (univ.powersetCard 3).filter fun e =>
    ∃ i ∈ e, ∃ j ∈ e, ∃ k ∈ e, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ Coherent S i j k
  card_eq_three _ he := (mem_powersetCard.mp (mem_filter.mp he).1).2

/-- The edges of `[S]` are the coherent triples. -/
theorem isEdge_twoGraph {S : Matrix ι ι ℝ} (hS : IsSignMatrix S) {a b c : ι} :
    (twoGraph S).IsEdge a b c ↔ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ Coherent S a b c := by
  simp only [FranklFuredi.ThreeGraph.IsEdge, twoGraph, mem_filter, mem_powersetCard,
    subset_univ, true_and, FranklFuredi.card_triple_eq_three]
  constructor
  · rintro ⟨⟨hab, hac, hbc⟩, i, hi, j, hj, k, hk, hij, hik, hjk, hcoh⟩
    refine ⟨hab, hac, hbc, ?_⟩
    simp only [mem_insert, mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl <;> simp_all [coherent_swap₁₂ hS, coherent_swap₂₃ hS]
  · rintro ⟨hab, hac, hbc, hcoh⟩
    exact ⟨⟨hab, hac, hbc⟩, a, by simp, b, by simp, c, by simp, hab, hac, hbc, hcoh⟩

/-- The two-graph of a blow-up `S(f, f)` is the blow-up of the two-graph along `f`. -/
theorem twoGraph_submatrix [Fintype κ] [DecidableEq κ] {T : Matrix κ κ ℝ}
    (hT : IsSignMatrix T) (f : ι → κ) :
    twoGraph (T.submatrix f f) = (twoGraph T).pullback f := by
  have hT' : IsSignMatrix (T.submatrix f f) :=
    ⟨fun i j => hT.symm _ _, fun i j => hT.sign _ _, fun i => hT.diag _⟩
  apply FranklFuredi.ThreeGraph.ext_of_isEdge
  intro a b c hab hac hbc
  rw [isEdge_twoGraph hT', FranklFuredi.ThreeGraph.isEdge_pullback, isEdge_twoGraph hT]
  simp only [hab, hac, hbc, ne_eq, not_false_eq_true, true_and]
  constructor
  · intro h
    exact ⟨h.ne₁₂ hT, h.ne₁₃ hT, h.ne₂₃ hT, h⟩
  · exact fun h => h.2.2.2

end TwoGraph

/-! ### Switching -/

/-- The signs `εᵢ = ±1`. -/
def IsSignVector (ε : ι → ℝ) : Prop := ∀ i, ε i = 1 ∨ ε i = -1

lemma IsSignVector.mul_self {ε : ι → ℝ} (hε : IsSignVector ε) (i : ι) : ε i * ε i = 1 := by
  rcases hε i with h | h <;> simp [h]

/-- The matrix `QᵗSQ` for the diagonal sign matrix `Q = Diag(ε)`: *switching* `S` at the indices
with `εᵢ = -1`. -/
def switch (S : Matrix ι ι ℝ) (ε : ι → ℝ) : Matrix ι ι ℝ := of fun i j => ε i * ε j * S i j

lemma IsSignMatrix.switch {S : Matrix ι ι ℝ} (hS : IsSignMatrix S) {ε : ι → ℝ}
    (hε : IsSignVector ε) : IsSignMatrix (switch S ε) := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun i => ?_⟩
  · simp only [Grunbaum.switch, of_apply, hS.symm]; ring
  · simp only [Grunbaum.switch, of_apply]
    rcases hε i with h1 | h1 <;> rcases hε j with h2 | h2 <;> rcases hS.sign i j with h3 | h3 <;>
      simp [h1, h2, h3]
  · simp only [Grunbaum.switch, of_apply, hS.diag, hε.mul_self, mul_one]

/-- Switching does not change the coherent triples. -/
lemma coherent_switch_iff {S : Matrix ι ι ℝ} {ε : ι → ℝ} (hε : IsSignVector ε) {i j k : ι} :
    Coherent (switch S ε) i j k ↔ Coherent S i j k := by
  unfold Coherent switch
  simp only [of_apply]
  have e : ε i * ε j * S i j * (ε i * ε k * S i k) * (ε j * ε k * S j k)
      = (ε i * ε i) * (ε j * ε j) * (ε k * ε k) * (S i j * S i k * S j k) := by ring
  rw [e, hε.mul_self, hε.mul_self, hε.mul_self]
  simp

/-- `S` and `T` are **switching equivalent**: `S = QᵗTQ` for a diagonal sign matrix `Q`. -/
def SwitchEquiv (S T : Matrix ι ι ℝ) : Prop :=
  ∃ ε : ι → ℝ, IsSignVector ε ∧ ∀ i j, S i j = ε i * ε j * T i j

lemma switchEquiv_switch (S : Matrix ι ι ℝ) {ε : ι → ℝ} (hε : IsSignVector ε) :
    SwitchEquiv (switch S ε) S :=
  ⟨ε, hε, fun _ _ => rfl⟩

lemma SwitchEquiv.symm {S T : Matrix ι ι ℝ} (h : SwitchEquiv S T) : SwitchEquiv T S := by
  obtain ⟨ε, hε, h⟩ := h
  refine ⟨ε, hε, fun i j => ?_⟩
  rw [h]
  linear_combination (-(T i j) * ε j * ε j) * hε.mul_self i - T i j * hε.mul_self j

lemma SwitchEquiv.coherent_iff {S T : Matrix ι ι ℝ} (h : SwitchEquiv S T) {i j k : ι} :
    Coherent S i j k ↔ Coherent T i j k := by
  obtain ⟨ε, hε, h⟩ := h
  have : S = switch T ε := by ext i j; exact h i j
  rw [this, coherent_switch_iff hε]

/-- **Sign matrices with the same two-graph are switching equivalent.** Switch `T` so that it
agrees with `S` in the row of a fixed index `a`; the coherent triples through `a` then determine
all other entries. -/
theorem switchEquiv_of_coherent_iff {S T : Matrix ι ι ℝ} (hS : IsSignMatrix S)
    (hT : IsSignMatrix T) (h : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → (Coherent S i j k ↔
      Coherent T i j k)) : SwitchEquiv S T := by
  classical
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨a⟩⟩
  · exact ⟨fun _ => 1, fun _ => Or.inl rfl, fun i => (hι.false i).elim⟩
  refine ⟨fun x => S a x * T a x, fun x => ?_, fun x y => ?_⟩
  · rcases hS.sign a x with h1 | h1 <;> rcases hT.sign a x with h2 | h2 <;> simp [h1, h2]
  change S x y = S a x * T a x * (S a y * T a y) * T x y
  have hSa := hS.mul_self_apply a
  have hTa := hT.mul_self_apply a
  by_cases hxy : x = y
  · rw [hxy, hS.diag, hT.diag]
    linear_combination (-(T a y * T a y)) * hSa y - hTa y
  by_cases hxa : x = a
  · rw [hxa, hS.diag, hT.diag]
    linear_combination (-(S a y)) * hTa y
  by_cases hya : y = a
  · rw [hya, hS.diag, hT.diag, hS.symm a x, hT.symm a x]
    linear_combination (-(S a x)) * hTa x
  -- the triple `{a, x, y}`
  have hcoh := h a x y (Ne.symm hxa) (Ne.symm hya) hxy
  have hprod : S a x * S a y * S x y = T a x * T a y * T x y := by
    by_cases hc : Coherent S a x y
    · exact hc.trans (hcoh.mp hc).symm
    · rw [(not_coherent_iff hS).mp hc, (not_coherent_iff hT).mp (fun h' => hc (hcoh.mpr h'))]
  linear_combination (S a x * S a y) * hprod - (S x y * S a y * S a y) * hSa x - S x y * hSa y

/-! ### Cocliques, cliques and twins -/

/-- A **coclique** of `[S]`: a set `C` containing no coherent triple. -/
def IsCoclique (S : Matrix ι ι ℝ) (C : Set ι) : Prop :=
  ∀ i ∈ C, ∀ j ∈ C, ∀ k ∈ C, ¬Coherent S i j k

/-- "Equivalently, after switching, `S[C, C] = J_C`." -/
theorem isCoclique_iff_exists_switch {S : Matrix ι ι ℝ} (hS : IsSignMatrix S) (C : Set ι) :
    IsCoclique S C ↔ ∃ ε : ι → ℝ, IsSignVector ε ∧ ∀ i ∈ C, ∀ j ∈ C, S i j = ε i * ε j := by
  constructor
  · intro hC
    by_cases hne : C.Nonempty
    · obtain ⟨a, ha⟩ := hne
      refine ⟨fun x => S a x, fun x => hS.sign a x, fun i hi j hj => ?_⟩
      have := (not_coherent_iff hS).mp (hC a ha i hi j hj)
      linear_combination (S a i * S a j) * this - S i j * S a j * S a j * hS.mul_self_apply a i
        - S i j * hS.mul_self_apply a j
    · exact ⟨fun _ => 1, fun _ => Or.inl rfl, fun i hi => (hne ⟨i, hi⟩).elim⟩
  · rintro ⟨ε, hε, h⟩ i hi j hj k hk
    rw [not_coherent_iff hS, h i hi j hj, h i hi k hk, h j hj k hk]
    linear_combination (ε j * ε j * ε k * ε k) * hε.mul_self i + ε k * ε k * hε.mul_self j
      + hε.mul_self k

/-- A **clique** of `[S]`: a set `C` all of whose triples (of distinct indices) are coherent. -/
def IsClique (S : Matrix ι ι ℝ) (C : Set ι) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, x ≠ y → x ≠ z → y ≠ z → Coherent S x y z

/-- "Equivalently, after switching, all off-diagonal entries of `S` on it equal `-1`." -/
theorem isClique_iff_exists_switch {S : Matrix ι ι ℝ} (hS : IsSignMatrix S) (C : Set ι) :
    IsClique S C ↔ ∃ ε : ι → ℝ, IsSignVector ε ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y → ε x * ε y * S x y = -1 := by
  classical
  constructor
  · intro hC
    by_cases hne : C.Nonempty
    · obtain ⟨a, ha⟩ := hne
      refine ⟨fun x => if x = a then 1 else -S a x, fun x => ?_, fun x hx y hy hxy => ?_⟩
      · by_cases hx : x = a
        · simp [hx]
        · rcases hS.sign a x with h | h <;> simp [hx, h]
      by_cases hxa : x = a
      · have hya : y ≠ a := fun h => hxy (hxa.trans h.symm)
        simp only [hxa, hya, ↓reduceIte]
        linear_combination -(hS.mul_self_apply a y)
      by_cases hya : y = a
      · simp only [hxa, hya, ↓reduceIte]
        rw [hS.symm a x]
        linear_combination -(hS.mul_self_apply a x)
      · simp only [hxa, hya, ↓reduceIte]
        have := hC a ha x hx y hy (Ne.symm hxa) (Ne.symm hya) hxy
        unfold Coherent at this
        linear_combination this
    · exact ⟨fun _ => 1, fun _ => Or.inl rfl, fun x hx => (hne ⟨x, hx⟩).elim⟩
  · rintro ⟨ε, hε, h⟩ x hx y hy z hz hxy hxz hyz
    have e1 := h x hx y hy hxy
    have e2 := h x hx z hz hxz
    have e3 := h y hy z hz hyz
    unfold Coherent
    have e : (ε x * ε y * S x y) * (ε x * ε z * S x z) * (ε y * ε z * S y z)
        = (ε x * ε x) * (ε y * ε y) * (ε z * ε z) * (S x y * S x z * S y z) := by ring
    rw [e1, e2, e3, hε.mul_self, hε.mul_self, hε.mul_self] at e
    linarith

/-- A **clique of order 4**: four distinct indices all of whose triples are coherent. -/
def IsClique4 (S : Matrix ι ι ℝ) (a b c d : ι) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    Coherent S a b c ∧ Coherent S a b d ∧ Coherent S a c d ∧ Coherent S b c d

/-- `[S]` is `K₄`-free: it has no clique of order `4`. -/
def K4Free (S : Matrix ι ι ℝ) : Prop := ∀ a b c d : ι, ¬IsClique4 S a b c d

theorem isClique4_iff {S : Matrix ι ι ℝ} (hS : IsSignMatrix S) {a b c d : ι} :
    IsClique4 S a b c d ↔ (a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) ∧
      IsClique S {a, b, c, d} := by
  constructor
  · rintro ⟨hab, hac, had, hbc, hbd, hcd, h1, h2, h3, h4⟩
    refine ⟨⟨hab, hac, had, hbc, hbd, hcd⟩, fun x hx y hy z hz hxy hxz hyz => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy hz
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      rcases hz with rfl | rfl | rfl | rfl <;>
      simp_all [coherent_swap₁₂ hS, coherent_swap₂₃ hS]
  · rintro ⟨⟨hab, hac, had, hbc, hbd, hcd⟩, h⟩
    exact ⟨hab, hac, had, hbc, hbd, hcd, h a (by simp) b (by simp) c (by simp) hab hac hbc,
      h a (by simp) b (by simp) d (by simp) hab had hbd,
      h a (by simp) c (by simp) d (by simp) hac had hcd,
      h b (by simp) c (by simp) d (by simp) hbc hbd hcd⟩

/-- `i` and `j` are **twins**: `i ≠ j` and the rows satisfy `sᵢ = ±sⱼ`. -/
def IsTwin (S : Matrix ι ι ℝ) (i j : ι) : Prop :=
  i ≠ j ∧ ((∀ k, S j k = S i k) ∨ ∀ k, S j k = -S i k)

/-- Twins are the pairs `{i, j}` contained in no coherent triple. -/
theorem isTwin_iff {S : Matrix ι ι ℝ} (hS : IsSignMatrix S) {i j : ι} :
    IsTwin S i j ↔ i ≠ j ∧ ∀ k, ¬Coherent S i j k := by
  constructor
  · rintro ⟨hij, h | h⟩ <;> refine ⟨hij, fun k => ?_⟩ <;> rw [not_coherent_iff hS]
    · have h1 := h i
      have h2 := h k
      rw [hS.diag, hS.symm] at h1
      rw [h1, h2, one_mul, hS.mul_self_apply]
    · have h1 := h i
      have h2 := h k
      rw [hS.diag, hS.symm] at h1
      rw [h1, h2]
      linear_combination hS.mul_self_apply i k
  · rintro ⟨hij, h⟩
    refine ⟨hij, ?_⟩
    rcases hS.sign i j with hs | hs
    · left
      intro k
      have := (not_coherent_iff hS).mp (h k)
      rw [hs, one_mul] at this
      linear_combination S i k * this - S j k * hS.mul_self_apply i k
    · right
      intro k
      have := (not_coherent_iff hS).mp (h k)
      rw [hs] at this
      linear_combination (-S i k) * this - S j k * hS.mul_self_apply i k

/-- After switching `j`, the rows of twins `i, j` coincide. -/
theorem IsTwin.exists_switch {S : Matrix ι ι ℝ} (hS : IsSignMatrix S) {i j : ι}
    (h : IsTwin S i j) :
    ∃ ε : ι → ℝ, IsSignVector ε ∧ (∀ k, k ≠ j → ε k = 1) ∧
      ∀ k, switch S ε j k = switch S ε i k := by
  classical
  obtain ⟨hij, hrow⟩ := h
  refine ⟨fun k => if k = j then S i j else 1, fun k => ?_, fun k hk => by simp [hk],
    fun k => ?_⟩
  · by_cases hk : k = j
    · simp only [hk, ↓reduceIte]; exact hS.sign i j
    · simp [hk]
  have hsq := hS.mul_self_apply i j
  simp only [switch, of_apply, ↓reduceIte]
  rcases hrow with hr | hr
  · have hsij : S i j = 1 := by rw [← hS.symm, hr i, hS.diag]
    by_cases hk : k = j
    · subst hk; simp [hS.diag, hsij, hij]
    · simp [hk, hsij, hr k, hij]
  · have hsij : S i j = -1 := by rw [← hS.symm, hr i, hS.diag]
    by_cases hk : k = j
    · subst hk; simp [hS.diag, hsij, hij]
    · simp [hk, hsij, hr k, hij]

/-- `[S]` has a coherent triple. -/
def HasCoherent (S : Matrix ι ι ℝ) : Prop := ∃ i j k, Coherent S i j k

/-! ### The four-point property -/

section FourPoint

variable [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- For a sign matrix, among the four triples of four indices an even number is coherent. -/
lemma coherent_parity {S : Matrix ι ι ℝ} (hS : IsSignMatrix S) (a b c d : ι) :
    ((Coherent S a b c ↔ Coherent S a b d) ↔ (Coherent S a c d ↔ Coherent S b c d)) := by
  unfold Coherent
  rcases hS.sign a b with h1 | h1 <;> rcases hS.sign a c with h2 | h2 <;>
    rcases hS.sign a d with h3 | h3 <;> rcases hS.sign b c with h4 | h4 <;>
    rcases hS.sign b d with h5 | h5 <;> rcases hS.sign c d with h6 | h6 <;>
    simp [h1, h2, h3, h4, h5, h6]

/-- If `[S]` is `K₄`-free, then any four points span `0` or `2` coherent triples. -/
theorem good_twoGraph {S : Matrix ι ι ℝ} (hS : IsSignMatrix S) (hK4 : K4Free S) :
    FranklFuredi.Good (twoGraph S).IsEdge := by
  intro a b c d hab hac had hbc hbd hcd
  simp only [FranklFuredi.Good4, isEdge_twoGraph hS, hab, hac, had, hbc, hbd, hcd, ne_eq,
    not_false_eq_true, true_and]
  exact ⟨coherent_parity hS a b c d, fun h => hK4 a b c d
    ⟨hab, hac, had, hbc, hbd, hcd, h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

/-- `[S]` is `K₄`-free iff it has the four-point property of Frankl and Füredi. -/
theorem fourPointProperty_twoGraph_iff {S : Matrix ι ι ℝ} (hS : IsSignMatrix S) :
    (twoGraph S).FourPointProperty ↔ K4Free S := by
  rw [FranklFuredi.ThreeGraph.fourPointProperty_iff]
  constructor
  · rintro h a b c d ⟨hab, hac, had, hbc, hbd, hcd, h1, h2, h3, h4⟩
    have := (h a b c d hab hac had hbc hbd hcd).2
    simp only [isEdge_twoGraph hS, hab, hac, had, hbc, hbd, hcd, ne_eq, not_false_eq_true,
      true_and] at this
    exact this ⟨h1, h2, h3, h4⟩
  · exact good_twoGraph hS

/-- Switching does not change the two-graph. -/
theorem twoGraph_eq_of_switchEquiv {S T : Matrix ι ι ℝ} (hS : IsSignMatrix S)
    (hT : IsSignMatrix T) (h : SwitchEquiv S T) : twoGraph S = twoGraph T := by
  apply FranklFuredi.ThreeGraph.ext_of_isEdge
  intro a b c hab hac hbc
  rw [isEdge_twoGraph hS, isEdge_twoGraph hT, h.coherent_iff]

end FourPoint

end Grunbaum
