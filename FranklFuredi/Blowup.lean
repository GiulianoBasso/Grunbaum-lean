import FranklFuredi.Basic

/-!
# Blow-ups and Example 1 (the 3-graphs `H_S`)

* `ThreeGraph.pullback K f` : the blow-up of a 3-graph `K` along a map `f` (every vertex `i` of
  `K` is replaced by the class `f⁻¹(i)`);
* `S6` : the 3-graph `S(6)` on six points (Fig. 1 of the paper);
* `HS f` : **Example 1**, the blow-up `H_S` of `S(6)` along a partition `V = V₁ ∪ ⋯ ∪ V₆`.

Main results: blow-ups preserve the four-point property (`good_pullback`), any four points of
`S(6)` span exactly two edges (`S6_spanned_four`), hence every `H_S` has the four-point property
(`HS_fourPointProperty`, "in `H_S` any four points span either zero or two edges").
-/

open Finset

namespace FranklFuredi

variable {V β : Type*} [DecidableEq V] [DecidableEq β]

namespace ThreeGraph

/-- The *blow-up* (pull-back) of a 3-graph `K` on `β` along `f : V → β`: a triple of vertices
is an edge iff `f` maps it bijectively onto an edge of `K`. -/
def pullback [Fintype V] (K : ThreeGraph β) (f : V → β) : ThreeGraph V where
  edges := (univ.powersetCard 3).filter (fun e => e.image f ∈ K.edges)
  card_eq_three _ he := (mem_powersetCard.mp (mem_filter.mp he).1).2

variable [Fintype V]

lemma isEdge_pullback {K : ThreeGraph β} {f : V → β} {a b c : V} :
    (K.pullback f).IsEdge a b c ↔ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ K.IsEdge (f a) (f b) (f c) := by
  simp only [IsEdge, pullback, mem_filter, mem_powersetCard, subset_univ, true_and,
    card_triple_eq_three, image_insert, image_singleton, and_assoc]

/-- Blow-ups preserve the four-point property. -/
theorem good_pullback {K : ThreeGraph β} (hK : Good K.IsEdge) (f : V → β) :
    Good (K.pullback f).IsEdge := by
  intro a b c d hab hac had hbc hbd hcd
  simp only [Good4, isEdge_pullback, ne_eq, hab, hac, had, hbc, hbd, hcd, not_false_eq_true,
    true_and]
  by_cases h1 : f a = f b
  · rw [h1]; simp [not_isEdge_eq_12]
  by_cases h2 : f a = f c
  · rw [h2]
    have := isEdge_comm_12 (H := K) (a := f c) (b := f b) (c := f d)
    simp [not_isEdge_eq_12, not_isEdge_eq_13, this]
  by_cases h3 : f a = f d
  · rw [h3]
    have := isEdge_rotate (H := K) (a := f d) (b := f b) (c := f c)
    simp [not_isEdge_eq_13, this]
  by_cases h4 : f b = f c
  · rw [h4]
    simp only [not_isEdge_eq_23, not_isEdge_eq_12, false_iff, iff_false, and_false,
      not_false_eq_true, and_true]
  by_cases h5 : f b = f d
  · rw [h5]
    have := isEdge_comm_23 (H := K) (a := f a) (b := f d) (c := f c)
    simp [not_isEdge_eq_13, not_isEdge_eq_23, this]
  by_cases h6 : f c = f d
  · rw [h6]
    simp [not_isEdge_eq_23]
  exact hK (f a) (f b) (f c) (f d) h1 h2 h3 h4 h5 h6

end ThreeGraph

/-! ### The 3-graph `S(6)` -/

/-- The 3-graph `S(6)` of the paper,
`S(6) = {(123), (124), (345), (346), (561), (562), (135), (146), (236), (245)}`,
with the vertices `1, …, 6` relabelled `0, …, 5`. -/
def S6 : ThreeGraph (Fin 6) where
  edges := {{0, 1, 2}, {0, 1, 3}, {2, 3, 4}, {2, 3, 5}, {4, 5, 0}, {4, 5, 1}, {0, 2, 4},
    {0, 3, 5}, {1, 2, 5}, {1, 3, 4}}
  card_eq_three := by decide

/-- "One can check that any 4 points span 2 edges in `S(6)`." -/
theorem S6_spanned_four : ∀ W : Finset (Fin 6), W.card = 4 → (S6.spanned W).card = 2 := by
  unfold ThreeGraph.spanned; decide

theorem S6_fourPointProperty : S6.FourPointProperty :=
  fun W hW => Or.inr (S6_spanned_four W hW)

theorem S6_good : Good S6.IsEdge := (ThreeGraph.fourPointProperty_iff S6).mp S6_fourPointProperty

/-! ### Example 1 -/

variable [Fintype V]

/-- **Example 1.**  Let `V = V₁ ∪ ⋯ ∪ V₆` be a partition, encoded by `f : V → Fin 6`
(`Vᵢ = f⁻¹(i)`; classes may be empty).  The 3-graph `H_S` has as edges the triples
`{v_{i₁}, v_{i₂}, v_{i₃}}` with `v_{iⱼ} ∈ V_{iⱼ}` and `(i₁ i₂ i₃) ∈ S(6)`. -/
def HS (f : V → Fin 6) : ThreeGraph V := S6.pullback f

lemma isEdge_HS {f : V → Fin 6} {a b c : V} :
    (HS f).IsEdge a b c ↔ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ S6.IsEdge (f a) (f b) (f c) :=
  ThreeGraph.isEdge_pullback

theorem HS_good (f : V → Fin 6) : Good (HS f).IsEdge := ThreeGraph.good_pullback S6_good f

/-- "In `H_S` any four points span either zero or two edges." -/
theorem HS_fourPointProperty (f : V → Fin 6) : (HS f).FourPointProperty :=
  ((HS f).fourPointProperty_iff).mpr (HS_good f)

/-! ### The link of a vertex of `S(6)` is a 5-cycle -/

/-- The link of the vertex `0` of `S(6)` is the 5-cycle `1 - 2 - 4 - 5 - 3 - 1`; `c5 i` is its
`i`-th vertex. -/
def c5 : Fin 5 → Fin 6 := ![1, 2, 4, 5, 3]

theorem S6_link_zero (i j : Fin 5) :
    S6.IsEdge 0 (c5 i) (c5 j) ↔ (j = i + 1 ∨ j = i - 1) := by
  revert i j; decide

theorem S6_c5_ne_zero (i : Fin 5) : c5 i ≠ 0 := by revert i; decide

end FranklFuredi
