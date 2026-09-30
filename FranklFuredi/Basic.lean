import FranklFuredi.Imports

/-!
# 3-graphs and the four-point property

This file sets up the basic notions of

  P. Frankl, Z. Füredi, *An exact result for 3-graphs*,
  Discrete Mathematics 50 (1984) 323–328.

* `ThreeGraph V` : a 3-graph (3-uniform hypergraph) on the vertex type `V`;
* `ThreeGraph.spanned H W` : the family `𝓔_W` of edges spanned by `W`;
* `ThreeGraph.FourPointProperty H` : *any four points span 0 or 2 edges* — the hypothesis of
  Theorems 1 and 2 of the paper.

We also prove the elementary facts that drive the whole proof:

* the four-point property in propositional form (`fourPointProperty_iff`);
* the link `N(u) = {(xy) : (uxy) ∈ 𝓔}` of a vertex is triangle-free (`link_triangle_free`)
  and contains no induced `2K₂` (`link_no_2K2`);
* a 3-graph with the four-point property is determined by the link of any single vertex
  (`eq_of_link_eq`).
-/

open Finset

namespace FranklFuredi

/-- A 3-graph on the vertex type `V`: a finite family of 3-element subsets of `V`.

(In the paper a hypergraph is in addition required to satisfy `⋃ 𝓔 = V`.  We never need this
assumption: all results below hold without it.) -/
@[ext]
structure ThreeGraph (V : Type*) where
  /-- The edges. -/
  edges : Finset (Finset V)
  /-- Every edge has exactly three elements. -/
  card_eq_three : ∀ e ∈ edges, e.card = 3

variable {V : Type*} [DecidableEq V]

lemma card_triple_eq_three {a b c : V} :
    ({a, b, c} : Finset V).card = 3 ↔ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  constructor
  · intro h
    refine ⟨fun hab => ?_, fun hac => ?_, fun hbc => ?_⟩
    · have h1 : ({a, b, c} : Finset V) ⊆ {a, c} := by
        intro x; simp only [mem_insert, mem_singleton]; rintro (rfl | rfl | rfl) <;> simp [hab]
      have := (card_le_card h1).trans card_le_two
      omega
    · have h1 : ({a, b, c} : Finset V) ⊆ {a, b} := by
        intro x; simp only [mem_insert, mem_singleton]; rintro (rfl | rfl | rfl) <;> simp [hac]
      have := (card_le_card h1).trans card_le_two
      omega
    · have h1 : ({a, b, c} : Finset V) ⊆ {a, b} := by
        intro x; simp only [mem_insert, mem_singleton]; rintro (rfl | rfl | rfl) <;> simp [hbc]
      have := (card_le_card h1).trans card_le_two
      omega
  · rintro ⟨hab, hac, hbc⟩
    rw [card_insert_of_notMem (by simp [hab, hac]), card_pair hbc]

namespace ThreeGraph

/-- `𝓔_W = {E ∈ 𝓔 : E ⊆ W}`, the edges *spanned* by `W`. -/
def spanned (H : ThreeGraph V) (W : Finset V) : Finset (Finset V) :=
  H.edges.filter (· ⊆ W)

/-- The hypothesis of the paper: *any four points span either zero or two edges*. -/
def FourPointProperty (H : ThreeGraph V) : Prop :=
  ∀ W : Finset V, W.card = 4 → (H.spanned W).card = 0 ∨ (H.spanned W).card = 2

/-- `H.IsEdge a b c` means that `{a, b, c}` is an edge of `H`. -/
abbrev IsEdge (H : ThreeGraph V) (a b c : V) : Prop :=
  ({a, b, c} : Finset V) ∈ H.edges

variable {H : ThreeGraph V} {a b c d u : V}

lemma isEdge_comm_12 : H.IsEdge a b c ↔ H.IsEdge b a c := by
  unfold IsEdge; rw [insert_comm]

lemma isEdge_comm_23 : H.IsEdge a b c ↔ H.IsEdge a c b := by
  unfold IsEdge; rw [pair_comm]

lemma isEdge_comm_13 : H.IsEdge a b c ↔ H.IsEdge c b a := by
  rw [isEdge_comm_12, isEdge_comm_23, isEdge_comm_12]

lemma isEdge_rotate : H.IsEdge a b c ↔ H.IsEdge b c a := by
  rw [isEdge_comm_12, isEdge_comm_23]

lemma IsEdge.card_eq (h : H.IsEdge a b c) : ({a, b, c} : Finset V).card = 3 :=
  H.card_eq_three _ h

lemma IsEdge.ne_12 (h : H.IsEdge a b c) : a ≠ b := (card_triple_eq_three.mp h.card_eq).1
lemma IsEdge.ne_13 (h : H.IsEdge a b c) : a ≠ c := (card_triple_eq_three.mp h.card_eq).2.1
lemma IsEdge.ne_23 (h : H.IsEdge a b c) : b ≠ c := (card_triple_eq_three.mp h.card_eq).2.2

lemma not_isEdge_eq_12 (H : ThreeGraph V) (x y : V) : ¬H.IsEdge x x y := fun h => h.ne_12 rfl
lemma not_isEdge_eq_13 (H : ThreeGraph V) (x y : V) : ¬H.IsEdge x y x := fun h => h.ne_13 rfl
lemma not_isEdge_eq_23 (H : ThreeGraph V) (x y : V) : ¬H.IsEdge y x x := fun h => h.ne_23 rfl

/-- Two 3-graphs with the same edge triples are equal. -/
lemma ext_of_isEdge {H H' : ThreeGraph V}
    (h : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → (H.IsEdge a b c ↔ H'.IsEdge a b c)) : H = H' := by
  ext e
  constructor
  · intro he
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp (H.card_eq_three e he)
    exact (h x y z hxy hxz hyz).mp he
  · intro he
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp (H'.card_eq_three e he)
    exact (h x y z hxy hxz hyz).mpr he

end ThreeGraph

/-! ### The four-point property in propositional form -/

/-- The four-point condition for the points `a, b, c, d`, in propositional form: among the four
triples `abc, abd, acd, bcd` an even number are edges (this is the parity statement
`(x₁ ↔ x₂) ↔ (x₃ ↔ x₄)`), and not all four of them are edges. -/
def Good4 {α : Type*} (E : α → α → α → Prop) (a b c d : α) : Prop :=
  ((E a b c ↔ E a b d) ↔ (E a c d ↔ E b c d)) ∧ ¬(E a b c ∧ E a b d ∧ E a c d ∧ E b c d)

/-- `Good4` for all quadruples of pairwise distinct points. -/
def Good {α : Type*} (E : α → α → α → Prop) : Prop :=
  ∀ a b c d, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → Good4 E a b c d

namespace ThreeGraph

variable {H : ThreeGraph V}

lemma card_four {a b c d : V} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : ({a, b, c, d} : Finset V).card = 4 := by
  rw [card_insert_of_notMem (by simp [hab, hac, had]),
    card_insert_of_notMem (by simp [hbc, hbd]), card_pair hcd]

lemma spanned_four (H : ThreeGraph V) {a b c d : V} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    H.spanned {a, b, c, d} =
      ({{a, b, c}, {a, b, d}, {a, c, d}, {b, c, d}} : Finset (Finset V)).filter
        (· ∈ H.edges) := by
  ext e
  simp only [spanned, mem_filter, mem_insert, mem_singleton]
  constructor
  · rintro ⟨he, hsub⟩
    refine ⟨?_, he⟩
    have hW := card_four hab hac had hbc hbd hcd
    have he3 := H.card_eq_three e he
    obtain ⟨x, hx⟩ : ∃ x, ({a, b, c, d} : Finset V) \ e = {x} := by
      rw [← card_eq_one, card_sdiff_of_subset hsub, hW, he3]
    have hxmem : x ∈ ({a, b, c, d} : Finset V) \ e := hx ▸ mem_singleton_self x
    have he_eq : e = ({a, b, c, d} : Finset V).erase x := by
      ext y
      constructor
      · intro hy
        rw [mem_erase]
        refine ⟨?_, hsub hy⟩
        rintro rfl
        exact (mem_sdiff.mp hxmem).2 hy
      · intro hy
        rw [mem_erase] at hy
        by_contra hye
        have : y ∈ ({a, b, c, d} : Finset V) \ e := mem_sdiff.mpr ⟨hy.2, hye⟩
        rw [hx, mem_singleton] at this
        exact hy.1 this
    have hxW := (mem_sdiff.mp hxmem).1
    rw [he_eq]
    simp only [mem_insert, mem_singleton] at hxW
    rcases hxW with rfl | rfl | rfl | rfl
    · right; right; right
      rw [erase_insert (by simp [hab, hac, had])]
    · right; right; left
      rw [erase_insert_of_ne hab, erase_insert (by simp [hbc, hbd])]
    · right; left
      rw [erase_insert_of_ne hac, erase_insert_of_ne hbc, erase_insert (by simp [hcd])]
    · left
      rw [erase_insert_of_ne had, erase_insert_of_ne hbd, erase_insert_of_ne hcd,
        erase_singleton, insert_empty]
  · rintro ⟨h, he⟩
    refine ⟨he, ?_⟩
    rcases h with rfl | rfl | rfl | rfl <;> intro y hy <;> simp only [mem_insert,
      mem_singleton] at hy ⊢ <;> tauto

omit [DecidableEq V] in
lemma triple_ne_of_mem {s t : Finset V} (x : V) (hs : x ∉ s) (ht : x ∈ t) : s ≠ t :=
  fun h => hs (h ▸ ht)

lemma card_spanned_four (H : ThreeGraph V) {a b c d : V} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (H.spanned {a, b, c, d}).card =
      (if H.IsEdge a b c then 1 else 0) + (if H.IsEdge a b d then 1 else 0) +
        (if H.IsEdge a c d then 1 else 0) + (if H.IsEdge b c d then 1 else 0) := by
  have n1 : ({a, b, c} : Finset V) ≠ {a, b, d} :=
    triple_ne_of_mem d (by simp [had.symm, hbd.symm, hcd.symm]) (by simp)
  have n2 : ({a, b, c} : Finset V) ≠ {a, c, d} :=
    triple_ne_of_mem d (by simp [had.symm, hbd.symm, hcd.symm]) (by simp)
  have n3 : ({a, b, c} : Finset V) ≠ {b, c, d} :=
    triple_ne_of_mem d (by simp [had.symm, hbd.symm, hcd.symm]) (by simp)
  have n4 : ({a, b, d} : Finset V) ≠ {a, c, d} :=
    triple_ne_of_mem c (by simp [hac.symm, hbc.symm, hcd]) (by simp)
  have n5 : ({a, b, d} : Finset V) ≠ {b, c, d} :=
    triple_ne_of_mem c (by simp [hac.symm, hbc.symm, hcd]) (by simp)
  have n6 : ({a, c, d} : Finset V) ≠ {b, c, d} :=
    triple_ne_of_mem b (by simp [hab.symm, hbc, hbd]) (by simp)
  rw [spanned_four H hab hac had hbc hbd hcd, card_filter,
    sum_insert (by simp [n1, n2, n3]), sum_insert (by simp [n4, n5]),
    sum_insert (by simp [n6]), sum_singleton]
  simp only [IsEdge]
  ring

/-- The four-point property is equivalent to its propositional form `Good`. -/
theorem fourPointProperty_iff (H : ThreeGraph V) : H.FourPointProperty ↔ Good H.IsEdge := by
  constructor
  · intro h a b c d hab hac had hbc hbd hcd
    have := h _ (card_four hab hac had hbc hbd hcd)
    rw [card_spanned_four H hab hac had hbc hbd hcd] at this
    unfold Good4
    by_cases h1 : H.IsEdge a b c <;> by_cases h2 : H.IsEdge a b d <;>
      by_cases h3 : H.IsEdge a c d <;> by_cases h4 : H.IsEdge b c d <;>
      simp [h1, h2, h3, h4] at this ⊢
  · intro h W hW
    obtain ⟨a, t, hat, rfl, ht⟩ := card_eq_succ.mp hW
    obtain ⟨b, c, d, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_three.mp ht
    simp only [mem_insert, mem_singleton, not_or] at hat
    obtain ⟨hab, hac, had⟩ := hat
    rw [card_spanned_four H hab hac had hbc hbd hcd]
    have := h a b c d hab hac had hbc hbd hcd
    unfold Good4 at this
    by_cases h1 : H.IsEdge a b c <;> by_cases h2 : H.IsEdge a b d <;>
      by_cases h3 : H.IsEdge a c d <;> by_cases h4 : H.IsEdge b c d <;>
      simp [h1, h2, h3, h4] at this ⊢

/-! ### Links -/

section PropLemmas

variable {X Y Z W Z' : Prop}

lemma prop_aux1 (h : (X ↔ Y) ↔ (Z ↔ W)) (hx : X) (hy : Y) (hz : Z) : W := by tauto
lemma prop_aux2 (h : (X ↔ Y) ↔ (Z ↔ W)) (hx : X) (hy : ¬Y) (hz : ¬Z) : W := by tauto
lemma prop_aux3 (h : (X ↔ Y) ↔ (Z ↔ W)) (hx : ¬X) (hy : ¬Y) (hz : Z) : W := by tauto
lemma prop_aux4 (h1 : X ↔ (Y ↔ Z)) (h2 : X ↔ (Y ↔ Z')) : Z ↔ Z' := by tauto

end PropLemmas

variable {a b c d u : V}

/-- The link `N(u)` of a vertex is triangle-free. -/
lemma link_triangle_free (hP : Good H.IsEdge) (hab : H.IsEdge u a b) (hbc : H.IsEdge u b c)
    (hac : H.IsEdge u a c) : False := by
  have h := hP u a b c hab.ne_12 hab.ne_13 hbc.ne_13 hab.ne_23 hac.ne_23 hbc.ne_23
  exact h.2 ⟨hab, hac, hbc, prop_aux1 h.1 hab hac hbc⟩

/-- The link `N(u)` of a vertex contains no induced `2K₂` (two disjoint edges with no edge
between them). -/
lemma link_no_2K2 (hP : Good H.IsEdge) (hab : H.IsEdge u a b) (hcd : H.IsEdge u c d)
    (hac : ¬H.IsEdge u a c) (had : ¬H.IsEdge u a d) (hbc : ¬H.IsEdge u b c)
    (hbd : ¬H.IsEdge u b d) : False := by
  have hua := hab.ne_12
  have hub := hab.ne_13
  have hab' := hab.ne_23
  have huc := hcd.ne_12
  have hud := hcd.ne_13
  have hcd' := hcd.ne_23
  have hac' : a ≠ c := by rintro rfl; exact had hcd
  have had' : a ≠ d := by rintro rfl; exact hac (isEdge_comm_23.mp hcd)
  have hbc' : b ≠ c := by rintro rfl; exact hbd hcd
  have hbd' : b ≠ d := by rintro rfl; exact hbc (isEdge_comm_23.mp hcd)
  have h1 := (hP u a b c hua hub huc hab' hac' hbc').1
  have h2 := (hP u a b d hua hub hud hab' had' hbd').1
  have h3 := (hP u a c d hua huc hud hac' had' hcd').1
  have h4 := (hP u b c d hub huc hud hbc' hbd' hcd').1
  have h5 := (hP a b c d hab' hac' had' hbc' hbd' hcd').2
  exact h5 ⟨prop_aux2 h1 hab hac hbc, prop_aux2 h2 hab had hbd, prop_aux3 h3 hac had hcd,
    prop_aux3 h4 hbc hbd hcd⟩

/-- **Reconstruction from one link.**  Two 3-graphs satisfying the four-point condition which
have the same link at some vertex `u` are equal.  (Only the parity half of the condition is
used: the edges not containing `u` are exactly the triples containing an odd number of edges
of `N(u)`.) -/
theorem eq_of_link_eq {H H' : ThreeGraph V} (hP : Good H.IsEdge) (hP' : Good H'.IsEdge) (u : V)
    (hlink : ∀ a b, H.IsEdge u a b ↔ H'.IsEdge u a b) : H = H' := by
  apply ext_of_isEdge
  intro a b c hab hac hbc
  by_cases ha : a = u
  · subst ha; exact hlink b c
  by_cases hb : b = u
  · subst hb
    rw [isEdge_comm_12 (H := H), isEdge_comm_12 (H := H')]
    exact hlink a c
  by_cases hc : c = u
  · subst hc
    rw [isEdge_comm_13 (H := H), isEdge_comm_13 (H := H')]
    exact hlink b a
  have h1 := (hP u a b c (Ne.symm ha) (Ne.symm hb) (Ne.symm hc) hab hac hbc).1
  have h2 := (hP' u a b c (Ne.symm ha) (Ne.symm hb) (Ne.symm hc) hab hac hbc).1
  rw [← hlink a b, ← hlink a c, ← hlink b c] at h2
  exact prop_aux4 h1 h2

end ThreeGraph

end FranklFuredi
