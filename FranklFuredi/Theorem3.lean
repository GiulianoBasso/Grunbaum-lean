import FranklFuredi.Theorem2

/-!
# Theorem 3: bounds for `m(n, 3, 4, 3)`

`m(n, r, k, s)` is the maximum number of edges of an `r`-graph on `n` vertices in which any `k`
vertices span less than `s` edges (`mExtremal`).

> **Theorem 3.**  `(2 + o(1))/7 · C(n,3) ≤ m(n, 3, 4, 3) ≤ (1/3) · C(n,3) · n/(n-2)`.

* **Lower bound** (Section 2 of the paper).  "If one only wants to satisfy the condition: no four
  points span more than 2 edges, then one can add edges to `H_S` iteratively": partition the
  vertices into six nearly equal classes, take the edges of `H_S`, and recurse inside the
  classes.  We show that any four points then span at most two edges (`noThreeAt_compose`) and
  that the construction has at least `(n³ - 3n²)/21` edges (`exists_noThreeAt_large`).
* **Upper bound** (proved by de Caen, cited in the paper).  If any four points span at most two
  edges, then for every edge `abc` the codegrees satisfy `d(ab) + d(ac) + d(bc) ≤ n`; hence
  `∑ d² ≤ n · 2|𝓔|` over ordered pairs, and Cauchy–Schwarz gives `18 |𝓔| ≤ n²(n-1)`
  (`deCaen`).  This is the same argument as the inequality `9 p ≤ n e₂` used for Theorem 2.
-/

open Finset

namespace FranklFuredi

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ### "Any four points span less than three edges" -/

/-- Any four points of `H` span less than three edges. -/
def NoFourSpanThree (H : ThreeGraph V) : Prop :=
  ∀ W : Finset V, W.card = 4 → (H.spanned W).card < 3

/-- Propositional form: no vertex lies in three of the triples of a 4-set. -/
def NoThreeAt {α : Type*} (E : α → α → α → Prop) : Prop :=
  ∀ a b c d, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → ¬(E a b c ∧ E a b d ∧ E a c d)

section Perm

omit [Fintype V]

variable {H : ThreeGraph V} {a b c : V}

lemma isEdge_perm_bac : H.IsEdge b a c ↔ H.IsEdge a b c := ThreeGraph.isEdge_comm_12.symm
lemma isEdge_perm_cab : H.IsEdge c a b ↔ H.IsEdge a b c :=
  ThreeGraph.isEdge_rotate (a := c) (b := a) (c := b)
lemma isEdge_perm_bca : H.IsEdge b c a ↔ H.IsEdge a b c := ThreeGraph.isEdge_rotate.symm
lemma isEdge_perm_acb : H.IsEdge a c b ↔ H.IsEdge a b c := ThreeGraph.isEdge_comm_23.symm
lemma isEdge_perm_cba : H.IsEdge c b a ↔ H.IsEdge a b c := ThreeGraph.isEdge_comm_13.symm

end Perm

omit [Fintype V] in
theorem noFourSpanThree_iff (H : ThreeGraph V) : NoFourSpanThree H ↔ NoThreeAt H.IsEdge := by
  constructor
  · intro h a b c d hab hac had hbc hbd hcd ⟨h1, h2, h3⟩
    have := h _ (ThreeGraph.card_four hab hac had hbc hbd hcd)
    rw [ThreeGraph.card_spanned_four H hab hac had hbc hbd hcd] at this
    simp only [h1, h2, h3, ite_true] at this
    omega
  · intro h W hW
    obtain ⟨a, t, hat, rfl, ht⟩ := card_eq_succ.mp hW
    obtain ⟨b, c, d, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_three.mp ht
    simp only [mem_insert, mem_singleton, not_or] at hat
    obtain ⟨hab, hac, had⟩ := hat
    rw [ThreeGraph.card_spanned_four H hab hac had hbc hbd hcd]
    have h1 := h a b c d hab hac had hbc hbd hcd
    have h2 := h b a c d (Ne.symm hab) hbc hbd hac had hcd
    have h3 := h c a b d (Ne.symm hac) (Ne.symm hbc) hcd hab had hbd
    have h4 := h d a b c (Ne.symm had) (Ne.symm hbd) (Ne.symm hcd) hab hac hbc
    rw [isEdge_perm_bac (a := a) (b := b) (c := c), isEdge_perm_bac (a := a) (b := b) (c := d)] at h2
    rw [isEdge_perm_cab (a := a) (b := b) (c := c), isEdge_perm_bac (a := a) (b := c) (c := d),
      isEdge_perm_bac (a := b) (b := c) (c := d)] at h3
    rw [isEdge_perm_cab (a := a) (b := b) (c := d), isEdge_perm_cab (a := a) (b := c) (c := d),
      isEdge_perm_cab (a := b) (b := c) (c := d)] at h4
    by_cases e1 : H.IsEdge a b c <;> by_cases e2 : H.IsEdge a b d <;>
      by_cases e3 : H.IsEdge a c d <;> by_cases e4 : H.IsEdge b c d <;>
      simp_all

/-! ### The upper bound (de Caen) -/

/-- The codegree of an ordered pair of vertices. -/
def codeg (H : ThreeGraph V) (a b : V) : ℕ := (univ.filter (fun c => H.IsEdge a b c)).card

lemma codeg_eq_sum (H : ThreeGraph V) (a b : V) :
    codeg H a b = ∑ c, if H.IsEdge a b c then 1 else 0 := by
  unfold codeg; rw [card_filter]

/-- Every 3-element set is `{a, b, c}` for exactly six ordered triples `(a, b, c)`. -/
lemma card_triples_eq (e : Finset V) (he : e.card = 3) :
    (univ.filter (fun t : V × V × V => ({t.1, t.2.1, t.2.2} : Finset V) = e)).card = 6 := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp he
  have key : ∀ a b c : V, (({a, b, c} : Finset V) = {x, y, z}) ↔
      (a ∈ ({x, y, z} : Finset V) ∧ b ∈ ({x, y, z} : Finset V) ∧ c ∈ ({x, y, z} : Finset V) ∧
        a ≠ b ∧ a ≠ c ∧ b ≠ c) := by
    intro a b c
    constructor
    · intro h
      have h3 : ({a, b, c} : Finset V).card = 3 := by
        rw [h]; exact card_triple_eq_three.mpr ⟨hxy, hxz, hyz⟩
      obtain ⟨h1, h2, h3'⟩ := card_triple_eq_three.mp h3
      refine ⟨h ▸ by simp, h ▸ by simp, h ▸ by simp, h1, h2, h3'⟩
    · rintro ⟨ha, hb, hc, h1, h2, h3⟩
      apply eq_of_subset_of_card_le
      · intro w hw
        simp only [mem_insert, mem_singleton] at hw
        rcases hw with rfl | rfl | rfl <;> assumption
      · rw [card_triple_eq_three.mpr ⟨hxy, hxz, hyz⟩, card_triple_eq_three.mpr ⟨h1, h2, h3⟩]
  have hset : univ.filter (fun t : V × V × V => ({t.1, t.2.1, t.2.2} : Finset V) = {x, y, z}) =
      {(x, y, z), (x, z, y), (y, x, z), (y, z, x), (z, x, y), (z, y, x)} := by
    ext ⟨a, b, c⟩
    simp only [mem_filter, mem_univ, true_and, key, mem_insert, mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨ha, hb, hc, h1, h2, h3⟩
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
        rcases hc with rfl | rfl | rfl <;> simp_all
    · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;>
        simp [hxy, hxz, hyz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz]
  rw [hset]
  simp [hxy, hxz, hyz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz]

/-- Each edge corresponds to six ordered triples. -/
lemma sum_isEdge (H : ThreeGraph V) :
    ∑ a, ∑ b, ∑ c, (if H.IsEdge a b c then 1 else 0 : ℕ) = 6 * H.edges.card := by
  have h1 : ∑ a, ∑ b, ∑ c, (if H.IsEdge a b c then 1 else 0 : ℕ) =
      (univ.filter (fun t : V × V × V => H.IsEdge t.1 t.2.1 t.2.2)).card := by
    rw [card_filter, Fintype.sum_prod_type]
    apply sum_congr rfl
    intro a _
    rw [Fintype.sum_prod_type]
  rw [h1, card_eq_sum_card_fiberwise
    (s := univ.filter (fun t : V × V × V => H.IsEdge t.1 t.2.1 t.2.2))
    (f := fun t : V × V × V => ({t.1, t.2.1, t.2.2} : Finset V))
    (t := H.edges) (fun t ht => (mem_filter.mp ht).2)]
  rw [sum_congr rfl (fun e he => ?_), sum_const, smul_eq_mul, mul_comm]
  rw [filter_filter]
  have : univ.filter (fun t : V × V × V => H.IsEdge t.1 t.2.1 t.2.2 ∧
      ({t.1, t.2.1, t.2.2} : Finset V) = e) =
      univ.filter (fun t : V × V × V => ({t.1, t.2.1, t.2.2} : Finset V) = e) := by
    ext t
    simp only [mem_filter, mem_univ, true_and, ThreeGraph.IsEdge]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨h ▸ he, h⟩
  rw [this]
  exact card_triples_eq e (H.card_eq_three e he)

/-- The local estimate: for an edge `abc`, `d(ab) + d(ac) + d(bc) ≤ n`. -/
lemma codeg_sum_le {H : ThreeGraph V} (hH : NoThreeAt H.IsEdge) {a b c : V}
    (habc : H.IsEdge a b c) : codeg H a b + codeg H a c + codeg H b c ≤ Fintype.card V := by
  rw [codeg_eq_sum, codeg_eq_sum, codeg_eq_sum, ← sum_add_distrib, ← sum_add_distrib]
  have hab := habc.ne_12
  have hac := habc.ne_13
  have hbc := habc.ne_23
  calc ∑ v, ((if H.IsEdge a b v then 1 else 0) + (if H.IsEdge a c v then 1 else 0) +
        (if H.IsEdge b c v then 1 else 0))
      ≤ ∑ _v : V, 1 := by
        apply sum_le_sum
        intro v _
        by_cases hva : v = a
        · subst hva
          simp only [ThreeGraph.not_isEdge_eq_13, ite_false, zero_add]
          split_ifs <;> norm_num
        by_cases hvb : v = b
        · subst hvb
          simp only [ThreeGraph.not_isEdge_eq_13, ThreeGraph.not_isEdge_eq_23, ite_false,
            zero_add, add_zero]
          split_ifs <;> norm_num
        by_cases hvc : v = c
        · subst hvc
          simp only [ThreeGraph.not_isEdge_eq_23, ite_false, add_zero]
          split_ifs
          norm_num
        have n1 := hH a b c v hab hac (Ne.symm hva) hbc (Ne.symm hvb) (Ne.symm hvc)
        have n2 := hH b a c v (Ne.symm hab) hbc (Ne.symm hvb) hac (Ne.symm hva) (Ne.symm hvc)
        have n3 := hH c a b v (Ne.symm hac) (Ne.symm hbc) (Ne.symm hvc) hab (Ne.symm hva)
          (Ne.symm hvb)
        rw [isEdge_perm_bac, isEdge_perm_bac (a := a) (b := b)] at n2
        rw [isEdge_perm_cab, isEdge_perm_bac (a := a) (b := c) (c := v),
          isEdge_perm_bac (a := b) (b := c) (c := v)] at n3
        by_cases e1 : H.IsEdge a b v <;> by_cases e2 : H.IsEdge a c v <;>
          by_cases e3 : H.IsEdge b c v <;> simp_all
    _ = Fintype.card V := by simp

/-- **de Caen's bound.**  If any four points span at most two edges then
`18 |𝓔| ≤ n² (n - 1)`. -/
theorem deCaen (H : ThreeGraph V) (hH : NoThreeAt H.IsEdge) :
    18 * H.edges.card ≤ Fintype.card V ^ 2 * (Fintype.card V - 1) := by
  set n := Fintype.card V
  set E := H.edges.card
  let I : V → V → V → ℕ := fun a b c => if H.IsEdge a b c then 1 else 0
  have hN : ∑ a, ∑ b, ∑ c, I a b c = 6 * E := sum_isEdge H
  -- `∑_{a,b} d(a,b) = 6E`
  have hS1 : ∑ a, ∑ b, codeg H a b = 6 * E := by
    simp only [codeg_eq_sum]; exact hN
  -- `∑_{a,b} d(a,b)² = ∑_{a,b,c} [abc] d(a,b)`
  have hS2 : ∑ a, ∑ b, codeg H a b ^ 2 = ∑ a, ∑ b, ∑ c, I a b c * codeg H a b := by
    apply sum_congr rfl; intro a _; apply sum_congr rfl; intro b _
    rw [sq, ← sum_mul]
    nth_rewrite 1 [codeg_eq_sum]
    rfl
  have hsymm1 : ∑ a, ∑ b, ∑ c, I a b c * codeg H a c = ∑ a, ∑ b, ∑ c, I a b c * codeg H a b := by
    apply sum_congr rfl; intro a _
    rw [sum_comm]
    apply sum_congr rfl; intro b _; apply sum_congr rfl; intro c _
    simp only [I, isEdge_perm_acb]
  have hsymm2 : ∑ a, ∑ b, ∑ c, I a b c * codeg H b c = ∑ a, ∑ b, ∑ c, I a b c * codeg H a b := by
    calc ∑ a, ∑ b, ∑ c, I a b c * codeg H b c = ∑ b, ∑ a, ∑ c, I a b c * codeg H b c := sum_comm
      _ = ∑ b, ∑ c, ∑ a, I a b c * codeg H b c := sum_congr rfl (fun b _ => sum_comm)
      _ = ∑ a, ∑ b, ∑ c, I a b c * codeg H a b := by
        apply sum_congr rfl; intro b _; apply sum_congr rfl; intro c _; apply sum_congr rfl
        intro a _
        simp only [I, ThreeGraph.isEdge_rotate (H := H) (a := a) (b := b) (c := c)]
  -- `3 ∑ d² ≤ n · 6E`
  have hlocal : ∀ a b c, I a b c * (codeg H a b + codeg H a c + codeg H b c) ≤ I a b c * n := by
    intro a b c
    by_cases h : H.IsEdge a b c
    · simp only [I, h, ite_true, one_mul]; exact codeg_sum_le hH h
    · simp [I, h]
  have h3S2 : 3 * ∑ a, ∑ b, codeg H a b ^ 2 ≤ n * (6 * E) := by
    rw [hS2, ← hN]
    have hsplit : ∑ a, ∑ b, ∑ c, I a b c * (codeg H a b + codeg H a c + codeg H b c) =
        ∑ a, ∑ b, ∑ c, I a b c * codeg H a b + ∑ a, ∑ b, ∑ c, I a b c * codeg H a c +
          ∑ a, ∑ b, ∑ c, I a b c * codeg H b c := by
      simp only [mul_add, sum_add_distrib]
    calc 3 * ∑ a, ∑ b, ∑ c, I a b c * codeg H a b
        = ∑ a, ∑ b, ∑ c, I a b c * (codeg H a b + codeg H a c + codeg H b c) := by
          rw [hsplit, hsymm1, hsymm2]; ring
      _ ≤ ∑ a, ∑ b, ∑ c, I a b c * n :=
          sum_le_sum (fun a _ => sum_le_sum (fun b _ => sum_le_sum (fun c _ => hlocal a b c)))
      _ = n * ∑ a, ∑ b, ∑ c, I a b c := by simp only [← sum_mul]; ring
  -- Cauchy–Schwarz over the ordered pairs of distinct vertices
  have hdiag : ∀ a, codeg H a a = 0 := by
    intro a
    unfold codeg
    rw [card_eq_zero, filter_eq_empty_iff]
    intro c _ h
    exact h.ne_12 rfl
  have hoff : ∀ g : V × V → ℕ, (∀ a, g (a, a) = 0) →
      ∑ p ∈ (univ : Finset V).offDiag, g p = ∑ a, ∑ b, g (a, b) := by
    intro g hg
    rw [← sum_product']
    simp only [Prod.mk.eta]
    apply sum_subset
    · intro p _
      simp
    · intro p _ hp
      simp only [mem_offDiag, mem_univ, true_and, not_not] at hp
      obtain ⟨x, y⟩ := p
      simp only at hp
      rw [hp]
      exact hg y
  have hcs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset V).offDiag)
    (f := fun p => codeg H p.1 p.2)
  rw [hoff (fun p => codeg H p.1 p.2) hdiag,
    hoff (fun p => codeg H p.1 p.2 ^ 2) (fun a => by simp [hdiag a]), offDiag_card, card_univ,
    hS1] at hcs
  -- conclude
  rcases Nat.eq_zero_or_pos E with h0 | hpos
  · rw [h0]; simp
  · have hn1 : 1 ≤ n := by
      by_contra h
      push Not at h
      have : n = 0 := by omega
      have : IsEmpty V := Fintype.card_eq_zero_iff.mp this
      have : H.edges = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro e he
        have := H.card_eq_three e he
        have : e = ∅ := eq_empty_of_isEmpty e
        simp_all
      simp [E, this] at hpos
    have e1 : n * n - n = n * (n - 1) := by
      rw [Nat.mul_sub, mul_one]
    rw [e1] at hcs
    -- `(6E)² ≤ n(n-1) ∑ d²` and `3 ∑ d² ≤ 6 n E`
    have h4 : (6 * E) ^ 2 * 3 ≤ n * (n - 1) * (n * (6 * E)) := by
      calc (6 * E) ^ 2 * 3 ≤ n * (n - 1) * (∑ a, ∑ b, codeg H a b ^ 2) * 3 := by
            exact Nat.mul_le_mul_right 3 hcs
        _ = n * (n - 1) * (3 * ∑ a, ∑ b, codeg H a b ^ 2) := by ring
        _ ≤ n * (n - 1) * (n * (6 * E)) := Nat.mul_le_mul_left _ h3S2
    have h5 : 18 * E * (6 * E) ≤ n ^ 2 * (n - 1) * (6 * E) := by
      calc 18 * E * (6 * E) = (6 * E) ^ 2 * 3 := by ring
        _ ≤ n * (n - 1) * (n * (6 * E)) := h4
        _ = n ^ 2 * (n - 1) * (6 * E) := by ring
    exact Nat.le_of_mul_le_mul_right h5 (by omega)

/-! ### Transporting 3-graphs along embeddings -/

section Map

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- The image of a 3-graph under an injective map of the vertices. -/
def ThreeGraph.map (φ : W ↪ V) (G : ThreeGraph W) : ThreeGraph V where
  edges := G.edges.map (Finset.mapEmbedding φ).toEmbedding
  card_eq_three e he := by
    obtain ⟨e', he', rfl⟩ := mem_map.mp he
    simp [G.card_eq_three e' he']

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
lemma ThreeGraph.card_edges_map (φ : W ↪ V) (G : ThreeGraph W) :
    (G.map φ).edges.card = G.edges.card := card_map _

omit [Fintype V] [Fintype W] in
lemma ThreeGraph.isEdge_map_iff (φ : W ↪ V) (G : ThreeGraph W) {a b c : V} :
    (G.map φ).IsEdge a b c ↔ ∃ x y z, φ x = a ∧ φ y = b ∧ φ z = c ∧ G.IsEdge x y z := by
  constructor
  · intro h
    obtain ⟨e', he', hmap⟩ := mem_map.mp h
    simp only [RelEmbedding.coe_toEmbedding, Finset.mapEmbedding_apply] at hmap
    have ha : a ∈ e'.map φ := by rw [hmap]; simp
    have hb : b ∈ e'.map φ := by rw [hmap]; simp
    have hc : c ∈ e'.map φ := by rw [hmap]; simp
    obtain ⟨x, hx, rfl⟩ := mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hb
    obtain ⟨z, hz, rfl⟩ := mem_map.mp hc
    refine ⟨x, y, z, rfl, rfl, rfl, ?_⟩
    have : e' = {x, y, z} := by
      apply Finset.map_injective φ
      rw [hmap]
      simp
    show ({x, y, z} : Finset W) ∈ G.edges
    rw [← this]
    exact he'
  · rintro ⟨x, y, z, rfl, rfl, rfl, h⟩
    refine mem_map.mpr ⟨{x, y, z}, h, ?_⟩
    simp

omit [Fintype V] [Fintype W] in
lemma ThreeGraph.noThreeAt_map (φ : W ↪ V) (G : ThreeGraph W) (hG : NoThreeAt G.IsEdge) :
    NoThreeAt (G.map φ).IsEdge := by
  intro a b c d hab hac had hbc hbd hcd ⟨h1, h2, h3⟩
  rw [ThreeGraph.isEdge_map_iff] at h1 h2 h3
  obtain ⟨x, y, z, rfl, rfl, rfl, e1⟩ := h1
  obtain ⟨x', y', w, hx', hy', rfl, e2⟩ := h2
  obtain ⟨x'', z', w', hx'', hz', hw', e3⟩ := h3
  rw [φ.injective hx', φ.injective hy'] at e2
  rw [φ.injective hx'', φ.injective hz', φ.injective hw'] at e3
  exact hG x y z w (fun h => hab (congrArg φ h)) (fun h => hac (congrArg φ h))
    (fun h => had (congrArg φ h)) (fun h => hbc (congrArg φ h)) (fun h => hbd (congrArg φ h))
    (fun h => hcd (congrArg φ h)) ⟨e1, e2, e3⟩

end Map

/-! ### The iterated construction -/

section Compose

/-- The composition of `H_S` (for the partition `f`) with 3-graphs `G i` placed inside the
classes `Vᵢ = f⁻¹(i)`. -/
def compose (f : V → Fin 6) (G : ∀ i, ThreeGraph {v // f v = i}) : ThreeGraph V where
  edges := (HS f).edges ∪
    univ.biUnion (fun i => ((G i).map (Function.Embedding.subtype (fun v => f v = i))).edges)
  card_eq_three e he := by
    rcases mem_union.mp he with h | h
    · exact (HS f).card_eq_three e h
    · obtain ⟨i, -, hi⟩ := mem_biUnion.mp h
      exact ThreeGraph.card_eq_three _ e hi

variable {f : V → Fin 6} {G : ∀ i, ThreeGraph {v // f v = i}}

lemma isEdge_compose {a b c : V} :
    (compose f G).IsEdge a b c ↔ (HS f).IsEdge a b c ∨
      ∃ i, ((G i).map (Function.Embedding.subtype (fun v => f v = i))).IsEdge a b c := by
  simp only [ThreeGraph.IsEdge, compose, mem_union, mem_biUnion, mem_univ, true_and]

omit [Fintype V] in
lemma class_eq_of_isEdge_map {i : Fin 6} {a b c : V}
    (h : ((G i).map (Function.Embedding.subtype (fun v => f v = i))).IsEdge a b c) :
    f a = i ∧ f b = i ∧ f c = i := by
  rw [ThreeGraph.isEdge_map_iff] at h
  obtain ⟨x, y, z, rfl, rfl, rfl, -⟩ := h
  exact ⟨x.2, y.2, z.2⟩

lemma classes_ne_of_isEdge_HS {a b c : V} (h : (HS f).IsEdge a b c) :
    f a ≠ f b ∧ f a ≠ f c ∧ f b ≠ f c := by
  rw [isEdge_HS] at h
  have h' := h.2.2.2
  exact ⟨h'.ne_12, h'.ne_13, h'.ne_23⟩

/-- **The iterated construction has no four points spanning three edges.** -/
theorem noThreeAt_compose (hG : ∀ i, NoThreeAt (G i).IsEdge) : NoThreeAt (compose f G).IsEdge := by
  intro a b c d hab hac had hbc hbd hcd ⟨h1, h2, h3⟩
  rw [isEdge_compose] at h1 h2 h3
  rcases h1 with h1 | ⟨i, h1⟩
  · -- `abc` is an edge of `H_S`: then so are `abd` and `acd`
    have n1 := classes_ne_of_isEdge_HS h1
    rcases h2 with h2 | ⟨j, h2⟩
    · rcases h3 with h3 | ⟨k, h3⟩
      · -- three edges of `H_S` in a 4-set: impossible by the four-point property
        have := HS_good f a b c d hab hac had hbc hbd hcd
        unfold Good4 at this
        exact this.2 ⟨h1, h2, h3, (ThreeGraph.prop_aux1 this.1 h1 h2 h3)⟩
      · have := class_eq_of_isEdge_map h3
        exact n1.2.1 (this.1.trans this.2.1.symm)
    · have := class_eq_of_isEdge_map h2
      exact n1.1 (this.1.trans this.2.1.symm)
  · -- `abc` lies in a class: then so do `abd` and `acd`
    obtain ⟨ha, hb, hc⟩ := class_eq_of_isEdge_map h1
    have h2' : ((G i).map (Function.Embedding.subtype (fun v => f v = i))).IsEdge a b d := by
      rcases h2 with h2 | ⟨j, h2⟩
      · exact absurd (ha.trans hb.symm) (classes_ne_of_isEdge_HS h2).1
      · obtain ⟨-, -, hd⟩ := class_eq_of_isEdge_map h2
        have hji : j = i := by
          obtain ⟨ha', -, -⟩ := class_eq_of_isEdge_map h2
          exact ha'.symm.trans ha
        subst hji
        exact h2
    have h3' : ((G i).map (Function.Embedding.subtype (fun v => f v = i))).IsEdge a c d := by
      rcases h3 with h3 | ⟨k, h3⟩
      · exact absurd (ha.trans hc.symm) (classes_ne_of_isEdge_HS h3).1
      · have hki : k = i := by
          obtain ⟨ha', -, -⟩ := class_eq_of_isEdge_map h3
          exact ha'.symm.trans ha
        subst hki
        exact h3
    exact ThreeGraph.noThreeAt_map _ _ (hG i) a b c d hab hac had hbc hbd hcd ⟨h1, h2', h3'⟩

/-- The number of edges of the composition. -/
theorem card_edges_compose :
    (compose f G).edges.card = s6Count (partSizes f) + ∑ i, (G i).edges.card := by
  have hdisj1 : Disjoint (HS f).edges
      (univ.biUnion (fun i => ((G i).map (Function.Embedding.subtype (fun v => f v = i))).edges)) := by
    rw [disjoint_left]
    intro e he1 he2
    obtain ⟨i, -, hi⟩ := mem_biUnion.mp he2
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ :=
      Finset.card_eq_three.mp ((HS f).card_eq_three e he1)
    have h1 : (HS f).IsEdge x y z := he1
    have h2 : ((G i).map (Function.Embedding.subtype (fun v => f v = i))).IsEdge x y z := hi
    have := class_eq_of_isEdge_map h2
    exact (classes_ne_of_isEdge_HS h1).1 (this.1.trans this.2.1.symm)
  have hdisj2 : ((univ : Finset (Fin 6)) : Set (Fin 6)).PairwiseDisjoint
      (fun i => ((G i).map (Function.Embedding.subtype (fun v => f v = i))).edges) := by
    intro i _ j _ hij
    simp only [Function.onFun]
    rw [disjoint_left]
    intro e hei hej
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ :=
      Finset.card_eq_three.mp (ThreeGraph.card_eq_three _ e hei)
    have h1 := class_eq_of_isEdge_map (G := G) (i := i) (a := x) (b := y) (c := z) hei
    have h2 := class_eq_of_isEdge_map (G := G) (i := j) (a := x) (b := y) (c := z) hej
    exact hij (h1.1.symm.trans h2.1)
  simp only [compose]
  rw [card_union_of_disjoint hdisj1, card_biUnion hdisj2, card_edges_HS]
  simp only [ThreeGraph.card_edges_map]

end Compose

/-- **The lower bound construction.**  On every vertex set of size `n` there is a 3-graph in
which any four points span at most two edges, with at least `(n³ - 3n²)/21` edges. -/
theorem exists_noThreeAt_large (n : ℕ) :
    ∀ (V : Type u) [Fintype V] [DecidableEq V], Fintype.card V = n →
      ∃ H : ThreeGraph V, NoThreeAt H.IsEdge ∧ (n : ℤ) ^ 3 - 3 * n ^ 2 ≤ 21 * H.edges.card := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ hV
  by_cases hn : n ≤ 1
  · refine ⟨⟨∅, by simp⟩, fun a b c d _ _ _ _ _ _ h => by simp [ThreeGraph.IsEdge] at h, ?_⟩
    interval_cases n <;> simp
  push Not at hn
  obtain ⟨f, hf⟩ := exists_balanced_partition (V := V)
  have hlt : ∀ i, balanced n i < n := by
    intro i
    simp only [balanced]
    split_ifs <;> omega
  have hcard : ∀ i, Fintype.card {v // f v = i} = balanced n i := by
    intro i
    rw [Fintype.card_subtype, ← hV]
    exact hf i
  have hG : ∀ i, ∃ G : ThreeGraph {v // f v = i}, NoThreeAt G.IsEdge ∧
      ((balanced n i : ℕ) : ℤ) ^ 3 - 3 * (balanced n i : ℕ) ^ 2 ≤ 21 * G.edges.card :=
    fun i => ih _ (hlt i) _ (hcard i)
  choose G hGp hGc using hG
  refine ⟨compose f G, noThreeAt_compose hGp, ?_⟩
  rw [card_edges_compose]
  have hps : partSizes f = balanced n := by
    funext i; rw [hf i, hV]
  rw [hps]
  have hex := exS6_formula n
  have hsum : (∑ i, (((balanced n i : ℕ) : ℤ) ^ 3 - 3 * (balanced n i : ℕ) ^ 2)) ≤
      21 * ∑ i, ((G i).edges.card : ℤ) := by
    rw [mul_sum]
    exact sum_le_sum (fun i _ => hGc i)
  push_cast
  have hq : (n : ℤ) = 6 * ((n / 6 : ℕ) : ℤ) + ((n % 6 : ℕ) : ℤ) := by
    have := Nat.div_add_mod n 6
    omega
  have hr : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
  simp only [exS6] at hex
  simp only [balanced, Fin.sum_univ_six] at hsum hex ⊢
  generalize hq' : n / 6 = q at hsum hex hq ⊢
  interval_cases hr' : n % 6 <;> simp [sig] at hsum hex hq ⊢ <;>
    rw [hq] <;> nlinarith [sq_nonneg (q : ℤ)]

/-! ### `m(n, 3, 4, 3)` -/

/-- `m(n, r, k, s)`: the maximum number of edges of an `r`-graph on `n` vertices in which any
`k` vertices span less than `s` edges. -/
noncomputable def mExtremal (n r k s : ℕ) : ℕ :=
  ((univ : Finset (Finset (Finset (Fin n)))).filter (fun E => (∀ e ∈ E, e.card = r) ∧
    ∀ W : Finset (Fin n), W.card = k → (E.filter (· ⊆ W)).card < s)).sup Finset.card

theorem mExtremal_le (n : ℕ) : 18 * mExtremal n 3 4 3 ≤ n ^ 2 * (n - 1) := by
  unfold mExtremal
  rw [Nat.mul_comm, ← Nat.le_div_iff_mul_le (by norm_num)]
  apply Finset.sup_le
  intro E hE
  simp only [mem_filter, mem_univ, true_and] at hE
  obtain ⟨h3, h4⟩ := hE
  let H : ThreeGraph (Fin n) := ⟨E, h3⟩
  have hH : NoFourSpanThree H := h4
  have := deCaen H ((noFourSpanThree_iff H).mp hH)
  simp only [Fintype.card_fin] at this
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  linarith

theorem le_mExtremal (n : ℕ) : (n : ℤ) ^ 3 - 3 * n ^ 2 ≤ 21 * mExtremal n 3 4 3 := by
  obtain ⟨H, hH, hc⟩ := exists_noThreeAt_large n (Fin n) (Fintype.card_fin n)
  have : H.edges.card ≤ mExtremal n 3 4 3 := by
    unfold mExtremal
    apply Finset.le_sup (f := Finset.card)
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨H.card_eq_three, (noFourSpanThree_iff H).mpr hH⟩
  have : (H.edges.card : ℤ) ≤ mExtremal n 3 4 3 := by exact_mod_cast this
  linarith

/-- **Theorem 3, upper bound** (de Caen): `m(n,3,4,3) ≤ (1/3) C(n,3) n/(n-2)`. -/
theorem theorem3_upper (n : ℕ) (hn : 3 ≤ n) :
    (mExtremal n 3 4 3 : ℝ) ≤ 1 / 3 * (n.choose 3 : ℝ) * (n / (n - 2)) := by
  have h := mExtremal_le n
  have h6 := six_mul_choose_three n
  have h6' : 6 * (n.choose 3 : ℝ) = (n : ℝ) * (n - 1) * (n - 2) := by exact_mod_cast h6
  have hn2 : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h' : 18 * (mExtremal n 3 4 3 : ℝ) ≤ (n : ℝ) ^ 2 * ((n : ℝ) - 1) := by
    have : ((n ^ 2 * (n - 1) : ℕ) : ℝ) = (n : ℝ) ^ 2 * ((n : ℝ) - 1) := by
      push_cast [show 1 ≤ n by omega]; ring
    rw [← this]
    exact_mod_cast h
  have e : 1 / 3 * (n.choose 3 : ℝ) * (n / (n - 2)) = (n : ℝ) ^ 2 * ((n : ℝ) - 1) / 18 := by
    have : (n.choose 3 : ℝ) = (n : ℝ) * (n - 1) * (n - 2) / 6 := by linarith
    rw [this]
    field_simp
    ring
  rw [e]
  linarith

/-- **Theorem 3, lower bound**: `(2 + o(1))/7 · C(n,3) ≤ m(n,3,4,3)`, i.e. for every `ε > 0`
and all large `n`, `(2 - ε)/7 · C(n,3) ≤ m(n,3,4,3)`. -/
theorem theorem3_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, (2 - ε) / 7 * (n.choose 3 : ℝ) ≤ mExtremal n 3 4 3 := by
  refine ⟨⌈4 / ε⌉₊ + 3, fun n hn => ?_⟩
  have h := le_mExtremal n
  have h' : (n : ℝ) ^ 3 - 3 * n ^ 2 ≤ 21 * (mExtremal n 3 4 3 : ℝ) := by exact_mod_cast h
  have h6 := six_mul_choose_three n
  have h6' : 6 * (n.choose 3 : ℝ) = (n : ℝ) * (n - 1) * (n - 2) := by exact_mod_cast h6
  have hceil := Nat.le_ceil (4 / ε)
  have hn' : (⌈4 / ε⌉₊ : ℝ) + 3 ≤ n := by exact_mod_cast hn
  have hn3 : (3 : ℝ) ≤ n := by linarith [Nat.cast_nonneg (α := ℝ) ⌈4 / ε⌉₊]
  have h4 : 4 ≤ ε * ((n : ℝ) - 2) := by
    have : 4 / ε ≤ (n : ℝ) - 2 := by linarith
    rw [div_le_iff₀ hε] at this
    linarith
  -- `(2 - ε) n(n-1)(n-2) ≤ 2(n³ - 3n²)` since `4 ≤ ε (n-1)(n-2)`
  have hkey : (2 - ε) * ((n : ℝ) * (n - 1) * (n - 2)) ≤ 2 * ((n : ℝ) ^ 3 - 3 * n ^ 2) := by
    have h5 : 4 ≤ ε * (((n : ℝ) - 1) * ((n : ℝ) - 2)) := by
      have : ((n : ℝ) - 2) ≤ ((n : ℝ) - 1) * ((n : ℝ) - 2) := by nlinarith
      nlinarith
    nlinarith
  have : (2 - ε) / 7 * (n.choose 3 : ℝ) = (2 - ε) * ((n : ℝ) * (n - 1) * (n - 2)) / 42 := by
    rw [← h6']; ring
  rw [this]
  linarith

end FranklFuredi
