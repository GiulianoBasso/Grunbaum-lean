import FranklFuredi.Optimization
import FranklFuredi.Circle

/-!
# Counting edges

* `card_edges_HS` : `H_S` has `∑_{(ijk) ∈ S(6)} |Vᵢ||Vⱼ||Vₖ|` edges;
* `card_edges_circleGraph` : a circle 3-graph on `n` points in general position has at most
  `(n³ - n)/24` edges.  (The paper's argument — the number of edges is maximised when the
  points are distributed as equally as possible over the vertices of a regular `(2k+1)`-gon —
  is replaced by the classical tournament count: a triangle is an edge iff it is a cyclic
  triangle of the tournament `v → w ⇔ det(p v, p w) > 0`.)
-/

open Finset

namespace FranklFuredi

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The number of edges of `H_S` -/

/-- The sizes `|Vᵢ| = |f⁻¹(i)|` of the classes of the partition `f`. -/
def partSizes (f : V → Fin 6) (i : Fin 6) : ℕ := (univ.filter (fun v => f v = i)).card

omit [DecidableEq V] in
lemma sum_partSizes (f : V → Fin 6) : ∑ i, partSizes f i = Fintype.card V := by
  unfold partSizes
  rw [← card_univ (α := V)]
  exact (card_eq_sum_card_fiberwise (fun v _ => mem_univ (f v))).symm

lemma card_triples_image (f : V → Fin 6) {i j k : Fin 6} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    ((univ.powersetCard 3).filter (fun e : Finset V => e.image f = {i, j, k})).card =
      partSizes f i * partSizes f j * partSizes f k := by
  have key : (univ.powersetCard 3).filter (fun e : Finset V => e.image f = {i, j, k}) =
      (((univ.filter (fun v => f v = i)) ×ˢ (univ.filter (fun v => f v = j))) ×ˢ
        (univ.filter (fun v => f v = k))).image (fun x => ({x.1.1, x.1.2, x.2} : Finset V)) := by
    ext e
    simp only [mem_filter, mem_powersetCard, subset_univ, true_and, mem_image, mem_product,
      mem_univ, Prod.exists]
    constructor
    · rintro ⟨he3, heim⟩
      have hi : i ∈ e.image f := by rw [heim]; simp
      have hj : j ∈ e.image f := by rw [heim]; simp
      have hk : k ∈ e.image f := by rw [heim]; simp
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hi
      obtain ⟨b, hb, rfl⟩ := mem_image.mp hj
      obtain ⟨c, hc, rfl⟩ := mem_image.mp hk
      refine ⟨a, b, c, ⟨⟨rfl, rfl⟩, rfl⟩, ?_⟩
      have hsub : ({a, b, c} : Finset V) ⊆ e := by
        intro y hy
        simp only [mem_insert, mem_singleton] at hy
        rcases hy with rfl | rfl | rfl <;> assumption
      have hcard : ({a, b, c} : Finset V).card = 3 :=
        card_triple_eq_three.mpr ⟨fun h => hij (congrArg f h), fun h => hik (congrArg f h),
          fun h => hjk (congrArg f h)⟩
      exact eq_of_subset_of_card_le hsub (by rw [he3, hcard])
    · rintro ⟨a, b, c, ⟨⟨ha, hb⟩, hc⟩, rfl⟩
      refine ⟨card_triple_eq_three.mpr ⟨?_, ?_, ?_⟩, ?_⟩
      · intro h; apply hij; rw [← ha, ← hb, h]
      · intro h; apply hik; rw [← ha, ← hc, h]
      · intro h; apply hjk; rw [← hb, ← hc, h]
      · simp [image_insert, ha, hb, hc]
  rw [key, card_image_of_injOn, card_product, card_product]
  · rfl
  · rintro ⟨⟨a, b⟩, c⟩ habc ⟨⟨a', b'⟩, c'⟩ habc' heq
    simp only [coe_product, Set.mem_prod, coe_filter, mem_univ, true_and,
      Set.mem_ofPred_eq] at habc habc'
    obtain ⟨⟨ha, hb⟩, hc⟩ := habc
    obtain ⟨⟨ha', hb'⟩, hc'⟩ := habc'
    simp only at heq
    have h1 : a ∈ ({a', b', c'} : Finset V) := heq ▸ (by simp)
    have h2 : b ∈ ({a', b', c'} : Finset V) := heq ▸ (by simp)
    have h3 : c ∈ ({a', b', c'} : Finset V) := heq ▸ (by simp)
    simp only [mem_insert, mem_singleton] at h1 h2 h3
    have e1 : a = a' := by
      rcases h1 with h | h | h
      · exact h
      · exact absurd (ha.symm.trans ((congrArg f h).trans hb')) hij
      · exact absurd (ha.symm.trans ((congrArg f h).trans hc')) hik
    have e2 : b = b' := by
      rcases h2 with h | h | h
      · exact absurd (hb.symm.trans ((congrArg f h).trans ha')) (Ne.symm hij)
      · exact h
      · exact absurd (hb.symm.trans ((congrArg f h).trans hc')) hjk
    have e3 : c = c' := by
      rcases h3 with h | h | h
      · exact absurd (hc.symm.trans ((congrArg f h).trans ha')) (Ne.symm hik)
      · exact absurd (hc.symm.trans ((congrArg f h).trans hb')) (Ne.symm hjk)
      · exact h
    rw [e1, e2, e3]

/-- The number of edges of `H_S`: `∑_{(ijk) ∈ S(6)} |Vᵢ| |Vⱼ| |Vₖ|`. -/
theorem card_edges_HS (f : V → Fin 6) : (HS f).edges.card = s6Count (partSizes f) := by
  rw [s6Count_eq_sum]
  have h1 : (HS f).edges.card =
      ∑ T ∈ S6.edges, ((HS f).edges.filter (fun e => e.image f = T)).card :=
    card_eq_sum_card_fiberwise (fun e he => (mem_filter.mp he).2)
  rw [h1]
  apply sum_congr rfl
  intro T hT
  obtain ⟨i, j, k, hij, hik, hjk, rfl⟩ := Finset.card_eq_three.mp (S6.card_eq_three T hT)
  rw [prod_insert (by simp [hij, hik]), prod_insert (by simp [hjk]), prod_singleton,
    ← mul_assoc, ← card_triples_image f hij hik hjk]
  congr 1
  ext e
  simp only [HS, ThreeGraph.pullback, mem_filter]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    exact ⟨⟨h1, h3 ▸ hT⟩, h3⟩

/-! ### Circle 3-graphs: the tournament count -/

section Tournament

variable {p : V → ℝ × ℝ}

/-- The tournament of a configuration: `v → w` iff `det(p v, p w) > 0`, i.e. `p w` lies on the
open half circle following `p v` counterclockwise. -/
def Beats (p : V → ℝ × ℝ) (v w : V) : Prop := 0 < det2 (p v) (p w)

noncomputable instance : DecidableRel (Beats p) := fun _ _ => Classical.dec _

omit [Fintype V] [DecidableEq V] in
lemma not_beats_self (v : V) : ¬Beats p v v := by simp [Beats, det2_self]

omit [Fintype V] [DecidableEq V] in
lemma beats_asymm {v w : V} (h : Beats p v w) : ¬Beats p w v := by
  unfold Beats at *
  rw [det2_antisymm]
  linarith

omit [Fintype V] [DecidableEq V] in
lemma beats_total (hp : GenPos p) {v w : V} (hvw : v ≠ w) : Beats p v w ∨ Beats p w v := by
  rcases lt_or_gt_of_ne (hp v w hvw) with h | h
  · right
    unfold Beats
    rw [det2_antisymm]
    linarith
  · exact Or.inl h

omit [Fintype V] [DecidableEq V] in
lemma neg_iff_beats {v w : V} : det2 (p v) (p w) < 0 ↔ Beats p w v := by
  unfold Beats
  rw [det2_antisymm (p v) (p w)]
  constructor <;> intro h <;> linarith

/-- The edges of a circle 3-graph are the cyclic triangles of its tournament. -/
lemma isEdge_iff_cyclic (hp : GenPos p) {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (circleGraph p).IsEdge a b c ↔
      (Beats p a b ∧ Beats p b c ∧ Beats p c a) ∨ (Beats p b a ∧ Beats p c b ∧ Beats p a c) := by
  rw [isEdge_circleGraph_iff_cyc hp hab hac hbc]
  simp only [Cyc, neg_iff_beats]
  rfl

/-- The sources of a triple: the vertices beating the two others. -/
noncomputable def sources (p : V → ℝ × ℝ) (e : Finset V) : Finset V :=
  e.filter (fun v => ∀ w ∈ e, w ≠ v → Beats p v w)

lemma card_sources_triple (hp : GenPos p) {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (sources p {a, b, c}).card =
      if ({a, b, c} : Finset V) ∈ (circleGraph p).edges then 0 else 1 := by
  have he := isEdge_iff_cyclic hp hab hac hbc
  simp only [ThreeGraph.IsEdge] at he
  have hsrc : sources p {a, b, c} =
      ({a, b, c} : Finset V).filter (fun v => ∀ w ∈ ({a, b, c} : Finset V), w ≠ v → Beats p v w) :=
    rfl
  rw [hsrc, filter_insert, filter_insert, filter_singleton]
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq, ne_eq, not_true_eq_false,
    IsEmpty.forall_iff, true_and, and_true]
  have t1 := beats_total hp hab
  have t2 := beats_total hp hac
  have t3 := beats_total hp hbc
  have a1 := @beats_asymm _ p a b
  have a2 := @beats_asymm _ p b a
  have a3 := @beats_asymm _ p a c
  have a4 := @beats_asymm _ p c a
  have a5 := @beats_asymm _ p b c
  have a6 := @beats_asymm _ p c b
  by_cases hmem : ({a, b, c} : Finset V) ∈ (circleGraph p).edges
  · rw [ite_eq_left hmem]
    have hc := he.mp hmem
    by_cases h1 : Beats p a b <;> by_cases h2 : Beats p a c <;> by_cases h3 : Beats p b c <;>
      simp_all [Ne.symm hab, Ne.symm hac, Ne.symm hbc]
  · rw [ite_eq_right hmem]
    have hc : ¬((Beats p a b ∧ Beats p b c ∧ Beats p c a) ∨
        (Beats p b a ∧ Beats p c b ∧ Beats p a c)) := fun h => hmem (he.mpr h)
    by_cases h1 : Beats p a b <;> by_cases h2 : Beats p a c <;> by_cases h3 : Beats p b c <;>
      simp_all [Ne.symm hab, Ne.symm hac, Ne.symm hbc]

/-- The number of edges of a circle 3-graph in terms of the out-degrees of its tournament. -/
theorem card_edges_add_sum_choose (hp : GenPos p) :
    (circleGraph p).edges.card + ∑ v, ((univ.filter (Beats p v)).card).choose 2 =
      (Fintype.card V).choose 3 := by
  set S3 : Finset (Finset V) := univ.powersetCard 3 with hS3
  have hsub : (circleGraph p).edges ⊆ S3 := fun e he =>
    mem_powersetCard.mpr ⟨subset_univ _, (circleGraph p).card_eq_three e he⟩
  -- every non-edge has exactly one source, every edge none
  have hsrc : ∀ e ∈ S3, (sources p e).card = if e ∈ (circleGraph p).edges then 0 else 1 := by
    intro e he
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ :=
      Finset.card_eq_three.mp (mem_powersetCard.mp he).2
    exact card_sources_triple hp hab hac hbc
  have hsum1 : ∑ e ∈ S3, (sources p e).card = S3.card - (circleGraph p).edges.card := by
    rw [sum_congr rfl hsrc, sum_ite, sum_const_zero, sum_const, smul_eq_mul, mul_one, zero_add,
      filter_not, filter_mem_eq_inter, inter_eq_right.mpr hsub, card_sdiff_of_subset hsub]
  -- double counting the pairs (source, triple)
  have hsum2 : ∑ e ∈ S3, (sources p e).card =
      ∑ v, (S3.filter (fun e => v ∈ sources p e)).card := by
    simp only [card_eq_sum_ones, sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro e _
    rw [← sum_filter]
    congr 1
    ext v
    simp [sources]
  have hfib : ∀ v, (S3.filter (fun e => v ∈ sources p e)).card =
      ((univ.filter (Beats p v)).card).choose 2 := by
    intro v
    rw [← card_powersetCard]
    apply card_nbij' (fun e => e.erase v) (fun t => insert v t)
    · intro e he
      rw [mem_coe] at he ⊢
      simp only [sources, mem_filter, hS3, mem_powersetCard, subset_univ, true_and] at he
      obtain ⟨he3, hve, hvb⟩ := he
      rw [mem_powersetCard]
      refine ⟨fun w hw => ?_, ?_⟩
      · rw [mem_erase] at hw
        simp only [mem_filter, mem_univ, true_and]
        exact hvb w hw.2 hw.1
      · rw [card_erase_of_mem hve, he3]
    · intro t ht
      rw [mem_coe] at ht ⊢
      rw [mem_powersetCard] at ht
      obtain ⟨hts, ht2⟩ := ht
      have hvt : v ∉ t := fun h => not_beats_self v (by simpa using hts h)
      simp only [sources, mem_filter, hS3, mem_powersetCard, subset_univ, true_and]
      refine ⟨by rw [card_insert_of_notMem hvt, ht2], mem_insert_self v t, fun w hw hwv => ?_⟩
      rw [mem_insert] at hw
      rcases hw with rfl | hw
      · exact absurd rfl hwv
      · simpa using hts hw
    · intro e he
      rw [mem_coe] at he
      simp only [sources, mem_filter] at he
      exact insert_erase he.2.1
    · intro t ht
      rw [mem_coe, mem_powersetCard] at ht
      have hvt : v ∉ t := fun h => not_beats_self v (by simpa using ht.1 h)
      exact erase_insert hvt
  have hS3card : S3.card = (Fintype.card V).choose 3 := by
    rw [hS3, card_powersetCard, card_univ]
  have hle := card_le_card hsub
  rw [← hS3card]
  rw [hsum2, sum_congr rfl (fun v _ => hfib v)] at hsum1
  omega

/-- The out-degrees of a tournament add up to `n(n-1)/2`. -/
theorem sum_outdeg (hp : GenPos p) :
    2 * ∑ v, (univ.filter (Beats p v)).card = Fintype.card V * (Fintype.card V - 1) := by
  have h1 : ∀ v w : V, (if Beats p v w then 1 else 0) + (if Beats p w v then 1 else 0) =
      if v = w then 0 else 1 := by
    intro v w
    by_cases hvw : v = w
    · subst hvw; simp [not_beats_self]
    · rcases beats_total hp hvw with h | h
      · simp [h, beats_asymm h, hvw]
      · simp [h, beats_asymm h, hvw]
  have h2 : ∑ v, ∑ w, ((if Beats p v w then 1 else 0) + (if Beats p w v then 1 else 0)) =
      Fintype.card V * (Fintype.card V - 1) := by
    simp only [h1]
    have : ∀ v : V, ∑ w, (if v = w then 0 else 1) = Fintype.card V - 1 := by
      intro v
      rw [← card_univ, ← card_erase_of_mem (mem_univ v), card_eq_sum_ones, sum_ite]
      simp only [sum_const_zero, zero_add, sum_const, smul_eq_mul, mul_one]
      congr 1
      ext w
      simp [eq_comm]
    rw [sum_congr rfl (fun v _ => this v), sum_const, card_univ, smul_eq_mul]
  simp only [sum_add_distrib] at h2
  rw [sum_comm (f := fun v w => if Beats p w v then 1 else 0)] at h2
  simp only [card_filter]
  omega

omit [Fintype V] [DecidableEq V] in
lemma two_mul_choose_two (m : ℕ) : 2 * (m.choose 2 : ℤ) = (m : ℤ) ^ 2 - m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    linarith

omit [Fintype V] [DecidableEq V] in
lemma six_mul_choose_three (m : ℕ) : 6 * (m.choose 3 : ℤ) = (m : ℤ) * (m - 1) * (m - 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ]
    push_cast
    linear_combination 3 * two_mul_choose_two m + ih

/-- **A circle 3-graph on `n` points in general position has at most `(n³ - n)/24` edges.** -/
theorem card_edges_circleGraph (hp : GenPos p) :
    24 * ((circleGraph p).edges.card : ℤ) ≤ (Fintype.card V : ℤ) ^ 3 - Fintype.card V := by
  set n := Fintype.card V
  set E := (circleGraph p).edges.card
  set d : V → ℕ := fun v => (univ.filter (Beats p v)).card
  have h1 := card_edges_add_sum_choose hp
  have h2 := sum_outdeg hp
  have hcs : (∑ v, (d v : ℤ)) ^ 2 ≤ n * ∑ v, (d v : ℤ) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset V)) (f := fun v => (d v : ℤ))
    simpa [card_univ] using this
  -- `2 · C(d,2) = d² - d` and `6 · C(n,3) = n(n-1)(n-2)`
  have hch2 := two_mul_choose_two
  have hch3 := six_mul_choose_three n
  have h1' : (E : ℤ) + ∑ v, ((d v).choose 2 : ℤ) = (n.choose 3 : ℤ) := by exact_mod_cast h1
  have h2' : 2 * ∑ v, (d v : ℤ) = (n : ℤ) * (n - 1) := by
    rcases Nat.eq_zero_or_pos n with h | h
    · have : IsEmpty V := Fintype.card_eq_zero_iff.mp h
      simp [h]
    · have := h2
      have e : ((n * (n - 1) : ℕ) : ℤ) = (n : ℤ) * (n - 1) := by
        push_cast [show 1 ≤ n by omega]; ring
      rw [← e]
      exact_mod_cast h2
  have hsq : 2 * ∑ v, ((d v).choose 2 : ℤ) = ∑ v, (d v : ℤ) ^ 2 - ∑ v, (d v : ℤ) := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl (fun v _ => hch2 (d v))
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · have : IsEmpty V := Fintype.card_eq_zero_iff.mp h0
    simp [E, h0, circleGraph]
    rfl
  have hn : (0 : ℤ) < n := by exact_mod_cast hpos
  nlinarith [hcs, h1', h2', hsq, hch3]

end Tournament

end FranklFuredi
