import FranklFuredi.Theorem3

/-!
# Smaller statements of the paper

* the "parity rule" behind Propositions 2 and 5: in a 3-graph with the four-point property the
  triple `abc` (not containing `x`) is an edge iff exactly one of `xab, xac, xbc` is an edge;
* **Proposition 6**: two points `v, w` are equivalent (`N(v) = N(w)`) iff no edge contains both;
* the hypothesis `⋃ 𝓔 = V` of the paper is automatic as soon as there is an edge;
* **Conjecture 1** (Erdős–Sós), stated for reference only (not proved here).
-/

open Finset

namespace FranklFuredi

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- The parity rule (behind Propositions 2 and 5): if any four points span 0 or 2 edges, then
for distinct `x, a, b, c` the triple `abc` is an edge iff exactly one of `xab, xac, xbc` is. -/
theorem isEdge_iff_exactly_one {H : ThreeGraph V} (hP : Good H.IsEdge) {x a b c : V}
    (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    H.IsEdge a b c ↔
      (H.IsEdge x a b ∧ ¬H.IsEdge x a c ∧ ¬H.IsEdge x b c) ∨
      (¬H.IsEdge x a b ∧ H.IsEdge x a c ∧ ¬H.IsEdge x b c) ∨
      (¬H.IsEdge x a b ∧ ¬H.IsEdge x a c ∧ H.IsEdge x b c) := by
  have h := hP x a b c hxa hxb hxc hab hac hbc
  unfold Good4 at h
  generalize H.IsEdge a b c = p at h ⊢
  generalize H.IsEdge x a b = q1 at h ⊢
  generalize H.IsEdge x a c = q2 at h ⊢
  generalize H.IsEdge x b c = q3 at h ⊢
  tauto

omit [Fintype V] in
/-- **Proposition 6.**  Two points `v ≠ w` are equivalent, i.e. `N(v) = N(w)`, iff there is no
edge containing both of them. -/
theorem prop6 {H : ThreeGraph V} (hP : Good H.IsEdge) {v w : V} (hvw : v ≠ w) :
    (∀ a b, H.IsEdge v a b ↔ H.IsEdge w a b) ↔ ∀ z, ¬H.IsEdge v w z := by
  constructor
  · intro h z hz
    have := (h w z).mp hz
    exact this.ne_12 rfl
  · intro h a b
    by_cases ha : a = v
    · subst ha
      constructor
      · intro h'; exact absurd h' (ThreeGraph.not_isEdge_eq_12 H a b)
      · intro h'; exact absurd (ThreeGraph.isEdge_comm_12.mp h') (h b)
    by_cases hb : b = v
    · subst hb
      constructor
      · intro h'; exact absurd h' (ThreeGraph.not_isEdge_eq_13 H b a)
      · intro h'
        exact absurd (ThreeGraph.isEdge_rotate.mp (ThreeGraph.isEdge_rotate.mp h')) (h a)
    by_cases ha' : a = w
    · subst ha'
      constructor
      · intro h'; exact absurd h' (h b)
      · intro h'; exact absurd h' (ThreeGraph.not_isEdge_eq_12 H a b)
    by_cases hb' : b = w
    · subst hb'
      constructor
      · intro h'; exact absurd (ThreeGraph.isEdge_comm_23.mp h') (h a)
      · intro h'; exact absurd h' (ThreeGraph.not_isEdge_eq_13 H b a)
    by_cases hab : a = b
    · subst hab
      constructor
      · intro h'; exact absurd h' (ThreeGraph.not_isEdge_eq_23 H a v)
      · intro h'; exact absurd h' (ThreeGraph.not_isEdge_eq_23 H a w)
    -- the four points `v, w, a, b` span `vab`, `wab` and no edge through `v` and `w`
    have g := hP v w a b hvw (Ne.symm ha) (Ne.symm hb) (Ne.symm ha') (Ne.symm hb') hab
    unfold Good4 at g
    have h1 := h a
    have h2 := h b
    generalize H.IsEdge v a b = p at g ⊢
    generalize H.IsEdge w a b = q at g ⊢
    generalize H.IsEdge v w a = r at g h1
    generalize H.IsEdge v w b = s at g h2
    tauto

omit [Fintype V] in
/-- The hypothesis `⋃ 𝓔 = V` of the paper is automatic: if any four points span 0 or 2 edges
and there is at least one edge, then every vertex lies in an edge. -/
theorem forall_mem_edge {H : ThreeGraph V} (hH : H.FourPointProperty) (hne : H.edges.Nonempty)
    (v : V) : ∃ e ∈ H.edges, v ∈ e := by
  obtain ⟨e, he⟩ := hne
  by_cases hv : v ∈ e
  · exact ⟨e, he, hv⟩
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp (H.card_eq_three e he)
  simp only [mem_insert, mem_singleton, not_or] at hv
  obtain ⟨hva, hvb, hvc⟩ := hv
  have hP := (H.fourPointProperty_iff).mp hH
  have g := hP a b c v hab hac (Ne.symm hva) hbc (Ne.symm hvb) (Ne.symm hvc)
  unfold Good4 at g
  have habc : H.IsEdge a b c := he
  by_cases h1 : H.IsEdge a b v
  · exact ⟨{a, b, v}, h1, by simp⟩
  by_cases h2 : H.IsEdge a c v
  · exact ⟨{a, c, v}, h2, by simp⟩
  have h3 : H.IsEdge b c v := by tauto
  exact ⟨{b, c, v}, h3, by simp⟩

/-- "If we choose a partition satisfying `|Vᵢ| ≥ ⌊n/6⌋`, `H_S` has (at least) `10⌊n/6⌋³`
edges." -/
theorem HS_card_ge (f : V → Fin 6) (hf : ∀ i, Fintype.card V / 6 ≤ partSizes f i) :
    10 * (Fintype.card V / 6) ^ 3 ≤ (HS f).edges.card := by
  rw [card_edges_HS]
  set q := Fintype.card V / 6
  have h0 := hf 0; have h1 := hf 1; have h2 := hf 2; have h3 := hf 3; have h4 := hf 4
  have h5 := hf 5
  unfold s6Count
  calc 10 * q ^ 3 = q * q * q + q * q * q + q * q * q + q * q * q + q * q * q + q * q * q +
      q * q * q + q * q * q + q * q * q + q * q * q := by ring
    _ ≤ _ := by gcongr

/-- "… which is more than `n³/24`, disproving Turán's conjecture" (that `m(n,3,4,3)` is
asymptotic to `n³/24`): for every `n ≥ 25`, `m(n,3,4,3) > n³/24`. -/
theorem turan_conjecture_false (n : ℕ) (hn : 25 ≤ n) :
    (n : ℝ) ^ 3 / 24 < mExtremal n 3 4 3 := by
  have h := le_mExtremal n
  have h' : (n : ℝ) ^ 3 - 3 * n ^ 2 ≤ 21 * (mExtremal n 3 4 3 : ℝ) := by exact_mod_cast h
  have hn' : (25 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith [sq_nonneg (n : ℝ)]

/-- **Conjecture 1** (Erdős and Sós), stated for reference only — it is *not* proved here.
If the link `N(x)` of every vertex of a 3-graph on `n ≥ 1` vertices is bipartite, then
`|𝓔| < n³/24`. -/
def ErdosSosConjecture : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ H : ThreeGraph (Fin n),
    (∀ x, ∃ col : Fin n → Bool, ∀ a b, H.IsEdge x a b → col a ≠ col b) →
      (H.edges.card : ℝ) < (n : ℝ) ^ 3 / 24

end FranklFuredi
