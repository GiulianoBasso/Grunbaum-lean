import FranklFuredi.GraphLemma
import FranklFuredi.Circle

/-!
# Theorem 1

> **Theorem 1.** Suppose `H = (V, 𝓔)` is a 3-graph in which any 4 points span 0 or 2 edges.
> Then `H` is isomorphic to one of the 3-graphs in Examples 1 or 2.

Since Examples 1 and 2 are defined on the vertex set `V` itself (with an arbitrary partition,
resp. an arbitrary placement of the points), "isomorphic to" simply becomes "equal to".

## Proof outline (following the paper, with the gaps filled in)

Fix a vertex `u` and let `G = N(u)` be its link.  By `Basic.lean`, `G` is triangle-free and has
no induced `2K₂`, and `H` is determined by `G` (`eq_of_link_eq`).  By `GraphLemma.dichotomy`:

* **(a)** `G` is a blow-up of the 5-cycle `C₅` (this contains the case where `N(u)` has an odd
  cycle, which is then a 5-cycle — Proposition 1).  The link of a vertex of `S(6)` is a 5-cycle,
  so `G` is also the link of `u` in a suitable `H_S`, hence `H = H_S`.
* **(b)** `G` is a bipartite chain graph (Propositions 3–5).  We place `u` at the point `(1,0)`,
  the vertices of the colour class `A` on the upper half circle, those of `B` on the lower half
  circle, at stereographic parameters chosen according to their levels, such that `a ∈ A`,
  `b ∈ B` span a triangle `uab` containing the origin iff `ab ∈ N(u)`.  Then `N(u)` is also the
  link of `u` in the circle 3-graph, hence `H` equals the circle 3-graph.

The paper's standing assumption `⋃ 𝓔 = V` is not needed (a 3-graph with the four-point
property and at least one edge automatically has no isolated vertices).
-/

open Finset

namespace FranklFuredi

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The link graph -/

/-- The link `N(u) = {(ab) : (uab) ∈ 𝓔}` of the vertex `u`, as a relation. -/
def link (H : ThreeGraph V) (u : V) : V → V → Prop := fun a b => H.IsEdge u a b

instance (H : ThreeGraph V) (u : V) : DecidableRel (link H u) :=
  fun a b => inferInstanceAs (Decidable (H.IsEdge u a b))

omit [Fintype V] in
lemma link_tf2k2 {H : ThreeGraph V} (hP : Good H.IsEdge) (u : V) : TF2K2 (link H u) where
  symm h := ThreeGraph.isEdge_comm_23.mp h
  irrefl _ h := h.ne_23 rfl
  triangle hab hbc hac := ThreeGraph.link_triangle_free hP hab hbc hac
  twoK2 hab hcd hac had hbc hbd := ThreeGraph.link_no_2K2 hP hab hcd hac had hbc hbd

/-! ### Case (a): the link is a blow-up of `C₅` -/

/-- The partition of `V` into six classes used in case (a): `u` and the isolated vertices of
its link go to the class of the vertex `0` of `S(6)`, the `i`-th class of the `C₅`-blow-up goes
to the `i`-th vertex of the 5-cycle `c5` (the link of `0` in `S(6)`). -/
def caseAPartition (u : V) (f : V → Option (Fin 5)) (w : V) : Fin 6 :=
  if w = u then 0 else (f w).elim 0 c5

theorem eq_HS_of_link_c5 {H : ThreeGraph V} (hP : Good H.IsEdge) (u : V) (f : V → Option (Fin 5))
    (hf : IsC5Blowup (link H u) f) : H = HS (caseAPartition u f) := by
  apply ThreeGraph.eq_of_link_eq hP (HS_good _) u
  intro a b
  rw [isEdge_HS]
  by_cases ha : a = u
  · subst ha
    simp [ThreeGraph.not_isEdge_eq_12]
  by_cases hb : b = u
  · subst hb
    simp [ThreeGraph.not_isEdge_eq_13]
  have hl := hf a b
  simp only [link] at hl
  rw [hl]
  simp only [caseAPartition, ha, hb, ↓reduceIte, ne_eq, Ne.symm ha, Ne.symm hb,
    not_false_eq_true, true_and]
  rcases hfa : f a with _ | i
  · simp [ThreeGraph.not_isEdge_eq_12]
  rcases hfb : f b with _ | j
  · simp [ThreeGraph.not_isEdge_eq_13]
  simp only [Option.elim_some, Option.some.injEq, exists_eq_left', S6_link_zero]
  constructor
  · intro h
    refine ⟨fun hab => ?_, h⟩
    subst hab
    rw [hfa] at hfb
    cases hfb
    exact (by decide : ∀ i : Fin 5, ¬(i = i + 1 ∨ i = i - 1)) i h
  · exact fun h => h.2

/-! ### Case (b): the link is a chain graph -/

section Realisation

omit [DecidableEq V] in
lemma card_pos_real : (0 : ℝ) < 4 * ((Fintype.card V : ℝ) + 1) := by positivity

/-- A small perturbation `ρ(w)/(4(n+1)) ∈ [0, 1/4)`, injective in `w` (`ρ : V ≃ Fin n`). -/
noncomputable def pert (w : V) : ℝ :=
  ((Fintype.equivFin V w : ℕ) : ℝ) / (4 * ((Fintype.card V : ℝ) + 1))

omit [DecidableEq V] in
lemma pert_nonneg (w : V) : 0 ≤ pert w := by unfold pert; positivity

omit [DecidableEq V] in
lemma pert_add_lt (w : V) : pert w + 1 / (4 * ((Fintype.card V : ℝ) + 1)) < 1 / 4 := by
  unfold pert
  have h1 : ((Fintype.equivFin V w : ℕ) : ℝ) + 1 ≤ Fintype.card V := by
    have := (Fintype.equivFin V w).isLt
    exact_mod_cast this
  have hc := (card_pos_real (V := V))
  rw [← add_div, div_lt_iff₀ hc]
  linarith

omit [DecidableEq V] in
lemma pert_lt (w : V) : pert w < 1 / 4 := by
  have := pert_add_lt w
  have : 0 < 1 / (4 * ((Fintype.card V : ℝ) + 1)) := by positivity
  linarith

omit [DecidableEq V] in
lemma pert_injective {v w : V} (h : pert v = pert w) : v = w := by
  unfold pert at h
  have hc := (card_pos_real (V := V))
  rw [div_left_inj' hc.ne'] at h
  have : (Fintype.equivFin V v : ℕ) = Fintype.equivFin V w := by exact_mod_cast h
  exact (Fintype.equivFin V).injective (Fin.ext this)

/-- The stereographic parameter of `w` in the realisation of case (b). -/
noncomputable def param (u : V) (A B : Finset V) (lev : V → ℕ) (w : V) : ℝ :=
  if w = u then 0
  else if w ∈ A then (lev w : ℝ) + 1 + pert w
  else if w ∈ B then -1 / ((lev w : ℝ) + 1 / 2 + pert w)
  else pert w + 1 / (4 * ((Fintype.card V : ℝ) + 1))

variable {u : V} {A B : Finset V} {lev : V → ℕ}

lemma param_u : param u A B lev u = 0 := by simp [param]

lemma param_A {w : V} (hw : w ≠ u) (hA : w ∈ A) :
    param u A B lev w = (lev w : ℝ) + 1 + pert w := by simp [param, hw, hA]

lemma param_B {w : V} (hw : w ≠ u) (hA : w ∉ A) (hB : w ∈ B) :
    param u A B lev w = -1 / ((lev w : ℝ) + 1 / 2 + pert w) := by simp [param, hw, hA, hB]

lemma param_I {w : V} (hw : w ≠ u) (hA : w ∉ A) (hB : w ∉ B) :
    param u A B lev w = pert w + 1 / (4 * ((Fintype.card V : ℝ) + 1)) := by
  simp [param, hw, hA, hB]

omit [DecidableEq V] in
lemma denom_pos (w : V) : 0 < (lev w : ℝ) + 1 / 2 + pert w := by
  have := pert_nonneg w; positivity

lemma param_A_ge {w : V} (hw : w ≠ u) (hA : w ∈ A) : 1 ≤ param u A B lev w := by
  rw [param_A hw hA]; have := pert_nonneg w; have : (0 : ℝ) ≤ lev w := by positivity
  linarith

lemma param_B_neg {w : V} (hw : w ≠ u) (hA : w ∉ A) (hB : w ∈ B) : param u A B lev w < 0 := by
  rw [param_B hw hA hB]
  have := denom_pos (lev := lev) w
  exact div_neg_of_neg_of_pos (by norm_num) this

lemma param_B_ge {w : V} (hw : w ≠ u) (hA : w ∉ A) (hB : w ∈ B) : -2 ≤ param u A B lev w := by
  rw [param_B hw hA hB]
  have hd := denom_pos (lev := lev) w
  have h2 : (1 : ℝ) / 2 ≤ (lev w : ℝ) + 1 / 2 + pert w := by
    have := pert_nonneg w; have : (0 : ℝ) ≤ lev w := by positivity
    linarith
  rw [le_div_iff₀ hd]
  linarith

lemma param_I_pos {w : V} (hw : w ≠ u) (hA : w ∉ A) (hB : w ∉ B) : 0 < param u A B lev w := by
  rw [param_I hw hA hB]
  have := pert_nonneg w
  have : 0 < 1 / (4 * ((Fintype.card V : ℝ) + 1)) := by positivity
  linarith

lemma param_I_lt {w : V} (hw : w ≠ u) (hA : w ∉ A) (hB : w ∉ B) :
    param u A B lev w < 1 / 4 := by
  rw [param_I hw hA hB]; exact pert_add_lt w

/-- The key computation: for `a ∈ A` and `b ∈ B` the triangle `u a b` contains the origin iff
`lev b ≤ lev a`. -/
lemma key_AB {la lb : ℕ} {ea eb : ℝ} (hea : 0 ≤ ea) (hea' : ea < 1 / 4) (heb : 0 ≤ eb)
    (heb' : eb < 1 / 4) :
    0 < (-1 / ((lb : ℝ) + 1 / 2 + eb) - ((la : ℝ) + 1 + ea)) *
        (1 + ((la : ℝ) + 1 + ea) * (-1 / ((lb : ℝ) + 1 / 2 + eb))) ↔ lb ≤ la := by
  have hd : 0 < (lb : ℝ) + 1 / 2 + eb := by positivity
  have hτ : 0 < (la : ℝ) + 1 + ea := by positivity
  have e : (-1 / ((lb : ℝ) + 1 / 2 + eb) - ((la : ℝ) + 1 + ea)) *
      (1 + ((la : ℝ) + 1 + ea) * (-1 / ((lb : ℝ) + 1 / 2 + eb))) =
      (1 / ((lb : ℝ) + 1 / 2 + eb) + ((la : ℝ) + 1 + ea)) *
        (((la : ℝ) + 1 + ea) - ((lb : ℝ) + 1 / 2 + eb)) / ((lb : ℝ) + 1 / 2 + eb) := by
    field_simp
    ring
  rw [e, div_pos_iff_of_pos_right hd]
  have hpos : 0 < 1 / ((lb : ℝ) + 1 / 2 + eb) + ((la : ℝ) + 1 + ea) := by positivity
  rw [mul_pos_iff_of_pos_left hpos]
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have : (la : ℝ) + 1 ≤ lb := by exact_mod_cast hlt
    linarith
  · intro h
    have : (lb : ℝ) ≤ la := by exact_mod_cast h
    linarith

lemma key_BA {la lb : ℕ} {ea eb : ℝ} (hea : 0 ≤ ea) (hea' : ea < 1 / 4) (heb : 0 ≤ eb)
    (heb' : eb < 1 / 4) :
    (((lb : ℝ) + 1 + eb) - -1 / ((la : ℝ) + 1 / 2 + ea)) *
        (1 + (-1 / ((la : ℝ) + 1 / 2 + ea)) * ((lb : ℝ) + 1 + eb)) < 0 ↔ la ≤ lb := by
  rw [← key_AB (la := lb) (lb := la) heb heb' hea hea']
  constructor <;> intro h <;> nlinarith

lemma gp_AB {la lb : ℕ} {ea eb : ℝ} (hea : 0 ≤ ea) (hea' : ea < 1 / 4) (heb : 0 ≤ eb)
    (heb' : eb < 1 / 4) :
    1 + ((la : ℝ) + 1 + ea) * (-1 / ((lb : ℝ) + 1 / 2 + eb)) ≠ 0 := by
  have hd : 0 < (lb : ℝ) + 1 / 2 + eb := by positivity
  intro h
  have e : ((la : ℝ) + 1 + ea) = (lb : ℝ) + 1 / 2 + eb := by
    field_simp at h
    linarith
  rcases le_or_gt lb la with hle | hlt
  · have : (lb : ℝ) ≤ la := by exact_mod_cast hle
    linarith
  · have : (la : ℝ) + 1 ≤ lb := by exact_mod_cast hlt
    linarith

lemma eq_of_lev_add {la lb : ℕ} {ea eb c : ℝ} (hea : 0 ≤ ea) (hea' : ea < 1 / 4) (heb : 0 ≤ eb)
    (heb' : eb < 1 / 4) (h : (la : ℝ) + c + ea = (lb : ℝ) + c + eb) : ea = eb := by
  rcases lt_trichotomy la lb with hlt | heq | hgt
  · have : (la : ℝ) + 1 ≤ lb := by exact_mod_cast hlt
    linarith
  · subst heq; linarith
  · have : (lb : ℝ) + 1 ≤ la := by exact_mod_cast hgt
    linarith

/-- The parameters are injective and pairwise in general position. -/
lemma param_genPos (hdisj : Disjoint A B) {v w : V} (hvw : v ≠ w) :
    param u A B lev v ≠ param u A B lev w ∧
      1 + param u A B lev v * param u A B lev w ≠ 0 := by
  have hAB : ∀ x, x ∈ A → x ∉ B := fun x hx => disjoint_left.mp hdisj hx
  -- classify both vertices
  have cls : ∀ x : V, x = u ∨ (x ≠ u ∧ x ∈ A) ∨ (x ≠ u ∧ x ∉ A ∧ x ∈ B) ∨
      (x ≠ u ∧ x ∉ A ∧ x ∉ B) := by
    intro x
    by_cases h1 : x = u
    · exact Or.inl h1
    by_cases h2 : x ∈ A
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    by_cases h3 : x ∈ B
    · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, h3⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, h3⟩))
  have pv0 := pert_nonneg v
  have pv1 := pert_lt v
  have pw0 := pert_nonneg w
  have pw1 := pert_lt w
  rcases cls v with rfl | ⟨hv, hvA⟩ | ⟨hv, hvA, hvB⟩ | ⟨hv, hvA, hvB⟩ <;>
    rcases cls w with rfl | ⟨hw, hwA⟩ | ⟨hw, hwA, hwB⟩ | ⟨hw, hwA, hwB⟩
  · exact absurd rfl hvw
  · have := param_A_ge (B := B) (lev := lev) hw hwA
    rw [param_u]; constructor <;> [linarith; simp]
  · have := param_B_neg (lev := lev) hw hwA hwB
    rw [param_u]; constructor <;> [linarith; simp]
  · have := param_I_pos (lev := lev) hw hwA hwB
    rw [param_u]; constructor <;> [linarith; simp]
  · have := param_A_ge (B := B) (lev := lev) hv hvA
    rw [param_u]; constructor <;> [linarith; simp]
  · -- both in `A`
    have h1 := param_A_ge (B := B) (lev := lev) hv hvA
    have h2 := param_A_ge (B := B) (lev := lev) hw hwA
    refine ⟨fun h => hvw (pert_injective ?_), by nlinarith⟩
    rw [param_A hv hvA, param_A hw hwA] at h
    exact eq_of_lev_add pv0 pv1 pw0 pw1 h
  · -- `v ∈ A`, `w ∈ B`
    have h1 := param_A_ge (B := B) (lev := lev) hv hvA
    have h2 := param_B_neg (lev := lev) hw hwA hwB
    refine ⟨by linarith, ?_⟩
    rw [param_A hv hvA, param_B hw hwA hwB]
    exact gp_AB pv0 pv1 pw0 pw1
  · -- `v ∈ A`, `w` isolated
    have h1 := param_A_ge (B := B) (lev := lev) hv hvA
    have h2 := param_I_pos (lev := lev) hw hwA hwB
    have h3 := param_I_lt (lev := lev) hw hwA hwB
    refine ⟨by linarith, by nlinarith⟩
  · have := param_B_neg (lev := lev) hv hvA hvB
    rw [param_u]; constructor <;> [linarith; simp]
  · -- `v ∈ B`, `w ∈ A`
    have h1 := param_B_neg (lev := lev) hv hvA hvB
    have h2 := param_A_ge (B := B) (lev := lev) hw hwA
    refine ⟨by linarith, ?_⟩
    rw [param_B hv hvA hvB, param_A hw hwA, mul_comm]
    exact gp_AB pw0 pw1 pv0 pv1
  · -- both in `B`
    have h1 := param_B_neg (lev := lev) hv hvA hvB
    have h2 := param_B_neg (lev := lev) hw hwA hwB
    refine ⟨fun h => hvw (pert_injective ?_), by nlinarith⟩
    rw [param_B hv hvA hvB, param_B hw hwA hwB] at h
    have hd1 := denom_pos (lev := lev) v
    have hd2 := denom_pos (lev := lev) w
    rw [div_eq_div_iff hd1.ne' hd2.ne'] at h
    exact eq_of_lev_add (la := lev v) (lb := lev w) pv0 pv1 pw0 pw1 (c := 1 / 2) (by linarith)
  · -- `v ∈ B`, `w` isolated
    have h1 := param_B_neg (lev := lev) hv hvA hvB
    have h1' := param_B_ge (lev := lev) hv hvA hvB
    have h2 := param_I_pos (lev := lev) hw hwA hwB
    have h3 := param_I_lt (lev := lev) hw hwA hwB
    refine ⟨by linarith, by nlinarith⟩
  · have := param_I_pos (lev := lev) hv hvA hvB
    rw [param_u]; constructor <;> [linarith; simp]
  · have h1 := param_I_pos (lev := lev) hv hvA hvB
    have h3 := param_I_lt (lev := lev) hv hvA hvB
    have h2 := param_A_ge (B := B) (lev := lev) hw hwA
    refine ⟨by linarith, by nlinarith⟩
  · have h1 := param_I_pos (lev := lev) hv hvA hvB
    have h3 := param_I_lt (lev := lev) hv hvA hvB
    have h2 := param_B_neg (lev := lev) hw hwA hwB
    have h2' := param_B_ge (lev := lev) hw hwA hwB
    refine ⟨by linarith, by nlinarith⟩
  · -- both isolated
    have h1 := param_I_pos (lev := lev) hv hvA hvB
    have h2 := param_I_pos (lev := lev) hw hwA hwB
    refine ⟨fun h => hvw (pert_injective ?_), by nlinarith⟩
    rw [param_I hv hvA hvB, param_I hw hwA hwB] at h
    linarith

lemma cyc_stereo_zero (t r : ℝ) :
    Cyc (det2 (stereo 0) (stereo t)) (det2 (stereo t) (stereo r)) (det2 (stereo r) (stereo 0)) ↔
      Cyc t ((r - t) * (1 + t * r)) (-r) := by
  simp only [Cyc, det2_stereo_pos_iff, det2_stereo_neg_iff, sub_zero, zero_mul, add_zero,
    mul_one, zero_sub, mul_zero]

/-- **Realisation of case (b).**  If the link of `u` is a chain graph, it is also the link of
`u` in a circle 3-graph with points in general position. -/
theorem link_realisation {G : V → V → Prop} (hch : IsChain G A B lev) (hu : ∀ z, ¬G u z)
    (hu' : ∀ z, ¬G z u) :
    GenPos (fun w => stereo (param u A B lev w)) ∧
      ∀ a b, (G a b ↔ (circleGraph (fun w => stereo (param u A B lev w))).IsEdge u a b) := by
  set p := fun w => stereo (param u A B lev w) with hp
  have hgp : GenPos p := by
    intro v w hvw
    obtain ⟨h1, h2⟩ := param_genPos (u := u) (lev := lev) hch.1 hvw
    exact det2_stereo_ne_zero h1 h2
  refine ⟨hgp, fun a b => ?_⟩
  have hAB : ∀ x, x ∈ A → x ∉ B := fun x hx => disjoint_left.mp hch.1 hx
  by_cases ha : a = u
  · subst ha
    simp only [hu, false_iff]
    exact fun h => h.ne_12 rfl
  by_cases hb : b = u
  · subst hb
    simp only [hu', false_iff]
    exact fun h => h.ne_13 rfl
  by_cases hab : a = b
  · subst hab
    have : ¬G a a := by
      rw [hch.2]
      rintro (⟨h1, h2, -⟩ | ⟨h1, h2, -⟩) <;> exact hAB _ ‹_› ‹_›
    simp only [this, false_iff]
    exact fun h => h.ne_23 rfl
  rw [isEdge_circleGraph_iff_cyc hgp (Ne.symm ha) (Ne.symm hb) hab]
  simp only [hp, param_u]
  rw [cyc_stereo_zero, hch.2]
  have pa0 := pert_nonneg a
  have pa1 := pert_lt a
  have pb0 := pert_nonneg b
  have pb1 := pert_lt b
  by_cases haA : a ∈ A
  · have haB := hAB a haA
    have hτa := param_A_ge (B := B) (lev := lev) ha haA
    by_cases hbA : b ∈ A
    · have hbB := hAB b hbA
      have hτb := param_A_ge (B := B) (lev := lev) hb hbA
      simp only [haB, hbB, false_and, and_false, or_self, false_iff, Cyc]
      rintro (⟨-, -, h⟩ | ⟨h, -, -⟩) <;> linarith
    by_cases hbB : b ∈ B
    · have hτb := param_B_neg (lev := lev) hb hbA hbB
      simp only [haA, hbB, true_and, haB, false_and, or_false]
      rw [← key_AB pa0 pa1 pb0 pb1, ← param_A ha haA, ← param_B hb hbA hbB]
      simp only [Cyc]
      constructor
      · intro h; exact Or.inl ⟨by linarith, h, by linarith⟩
      · rintro (⟨-, h, -⟩ | ⟨h, -, -⟩)
        · exact h
        · linarith
    · have hτb := param_I_pos (lev := lev) hb hbA hbB
      simp only [hbA, hbB, false_and, and_false, or_self, false_iff, Cyc]
      rintro (⟨-, -, h⟩ | ⟨h, -, -⟩) <;> linarith
  by_cases haB : a ∈ B
  · have hτa := param_B_neg (lev := lev) ha haA haB
    have hτa' := param_B_ge (lev := lev) ha haA haB
    by_cases hbA : b ∈ A
    · have hbB := hAB b hbA
      have hτb := param_A_ge (B := B) (lev := lev) hb hbA
      simp only [haA, false_and, haB, hbA, true_and, false_or]
      rw [← key_BA pa0 pa1 pb0 pb1, ← param_B ha haA haB, ← param_A hb hbA]
      simp only [Cyc]
      constructor
      · intro h; exact Or.inr ⟨hτa, h, by linarith⟩
      · rintro (⟨h, -, -⟩ | ⟨-, h, -⟩)
        · linarith
        · exact h
    by_cases hbB : b ∈ B
    · have hτb := param_B_neg (lev := lev) hb hbA hbB
      simp only [haA, hbA, false_and, and_false, or_self, false_iff, Cyc]
      rintro (⟨h, -, -⟩ | ⟨-, -, h⟩) <;> linarith
    · have hτb := param_I_pos (lev := lev) hb hbA hbB
      have hτb' := param_I_lt (lev := lev) hb hbA hbB
      simp only [haA, hbA, hbB, false_and, and_false, or_self, false_iff, Cyc]
      rintro (⟨h, -, -⟩ | ⟨-, h, -⟩)
      · linarith
      · have : 0 < (param u A B lev b - param u A B lev a) *
            (1 + param u A B lev a * param u A B lev b) := by
          apply mul_pos <;> nlinarith
        linarith
  · have hτa := param_I_pos (lev := lev) ha haA haB
    have hτa' := param_I_lt (lev := lev) ha haA haB
    simp only [haA, haB, false_and, or_self, false_iff, Cyc]
    by_cases hbB : b ∈ B
    · have hbA := hAB
      have hbA' : b ∉ A := fun h => hAB b h hbB
      have hτb := param_B_neg (lev := lev) hb hbA' hbB
      have hτb' := param_B_ge (lev := lev) hb hbA' hbB
      rintro (⟨-, h, -⟩ | ⟨h, -, -⟩)
      · have : (param u A B lev b - param u A B lev a) *
            (1 + param u A B lev a * param u A B lev b) < 0 := by
          apply mul_neg_of_neg_of_pos <;> nlinarith
        linarith
      · linarith
    · by_cases hbA : b ∈ A
      · have hτb := param_A_ge (B := B) (lev := lev) hb hbA
        rintro (⟨-, -, h⟩ | ⟨h, -, -⟩) <;> linarith
      · have hτb := param_I_pos (lev := lev) hb hbA hbB
        rintro (⟨-, -, h⟩ | ⟨h, -, -⟩) <;> linarith

end Realisation

/-! ### Theorem 1 -/

/-- **Theorem 1** (Frankl–Füredi).  If any four points of the 3-graph `H` span zero or two
edges, then `H` is one of the 3-graphs of Example 1 (a blow-up `H_S` of `S(6)`) or of
Example 2 (points on the unit circle, triangles containing the origin). -/
theorem theorem1 (H : ThreeGraph V) (hH : H.FourPointProperty) :
    (∃ f : V → Fin 6, H = HS f) ∨ (∃ p : V → ℝ × ℝ, IsCircleConfig p ∧ H = circleGraph p) := by
  have hP := (H.fourPointProperty_iff).mp hH
  rcases isEmpty_or_nonempty V with hV | ⟨⟨u⟩⟩
  · left
    refine ⟨fun v => (hV.false v).elim, ThreeGraph.ext_of_isEdge fun a => (hV.false a).elim⟩
  rcases dichotomy (link_tf2k2 hP u) with ⟨f, hf⟩ | ⟨A, B, lev, hch, h5⟩
  · exact Or.inl ⟨_, eq_HS_of_link_c5 hP u f hf⟩
  right
  have hu : ∀ z, ¬link H u u z := fun z h => h.ne_12 rfl
  have hu' : ∀ z, ¬link H u z u := fun z h => h.ne_13 rfl
  obtain ⟨hgp, hlink⟩ := link_realisation hch hu hu'
  set p := fun w => stereo (param u A B lev w) with hp
  have hHp : H = circleGraph p := ThreeGraph.eq_of_link_eq hP (circleGraph_good hgp) u hlink
  refine ⟨p, ⟨fun v w hvw => ?_, fun v => stereo_on_circle _, fun v w hvw => ?_, ?_⟩, hHp⟩
  · by_contra hne
    have := hgp v w hne
    rw [hvw, det2_self] at this
    exact this rfl
  · exact not_mem_line_of_det_ne_zero (stereo_on_circle _) (hgp v w hvw)
  · -- the link has an edge, hence so does the circle 3-graph
    obtain ⟨a, ha⟩ : (nonIsolated (link H u)).Nonempty := by
      rw [← card_pos]; omega
    simp only [nonIsolated, mem_filter, mem_univ, true_and] at ha
    obtain ⟨z, hz⟩ := ha
    have hedge := (hlink a z).mp hz
    rw [isEdge_circleGraph] at hedge
    refine convexHull_mono ?_ hedge.2.2.2
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> exact Set.mem_range_self _

/-- **The converse of Theorem 1:** the 3-graphs of Examples 1 and 2 have the four-point
property. -/
theorem theorem1_converse (H : ThreeGraph V)
    (h : (∃ f : V → Fin 6, H = HS f) ∨ (∃ p : V → ℝ × ℝ, IsCircleConfig p ∧ H = circleGraph p)) :
    H.FourPointProperty := by
  rcases h with ⟨f, rfl⟩ | ⟨p, hp, rfl⟩
  · exact HS_fourPointProperty f
  · exact circleGraph_fourPointProperty hp

/-- Theorem 1 together with its converse: the four-point property characterises the 3-graphs of
Examples 1 and 2. -/
theorem fourPointProperty_iff_examples (H : ThreeGraph V) :
    H.FourPointProperty ↔
      (∃ f : V → Fin 6, H = HS f) ∨ (∃ p : V → ℝ × ℝ, IsCircleConfig p ∧ H = circleGraph p) :=
  ⟨theorem1 H, theorem1_converse H⟩

/-- "For `n ≤ 5` the two examples coincide": on at most five vertices every 3-graph with the
four-point property is of the form `H_S`. -/
theorem eq_HS_of_card_le_five (H : ThreeGraph V) (hH : H.FourPointProperty)
    (hn : Fintype.card V ≤ 5) : ∃ f : V → Fin 6, H = HS f := by
  have hP := (H.fourPointProperty_iff).mp hH
  rcases isEmpty_or_nonempty V with hV | ⟨⟨u⟩⟩
  · exact ⟨fun v => (hV.false v).elim, ThreeGraph.ext_of_isEdge fun a => (hV.false a).elim⟩
  rcases dichotomy (link_tf2k2 hP u) with ⟨f, hf⟩ | ⟨A, B, lev, hch, h5⟩
  · exact ⟨_, eq_HS_of_link_c5 hP u f hf⟩
  exfalso
  have hsub : nonIsolated (link H u) ⊆ univ.erase u := by
    intro w hw
    simp only [nonIsolated, mem_filter, mem_univ, true_and] at hw
    obtain ⟨z, hz⟩ := hw
    exact mem_erase.mpr ⟨fun h => hz.ne_12 h.symm, mem_univ _⟩
  have := card_le_card hsub
  rw [card_erase_of_mem (mem_univ _), card_univ] at this
  omega

end FranklFuredi
