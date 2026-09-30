import FranklFuredi.Basic

/-!
# Triangle-free graphs without induced `2K₂`

This is the graph-theoretic heart of the proof.  By `Basic.lean`, the link `N(x)` of a vertex
of a 3-graph with the four-point property is triangle-free and contains no induced `2K₂`.
We show (`dichotomy`) that such a graph is

* either a blow-up of the 5-cycle, plus isolated vertices (`IsC5Blowup`) — this corresponds to
  case (a) of the paper: `N(v)` contains an odd cycle, and then it contains a 5-cycle
  (Proposition 1);
* or a bipartite *chain graph* (`IsChain`): the two colour classes `A`, `B` carry levels and
  `a ∈ A`, `b ∈ B` are adjacent iff `lev b ≤ lev a`, i.e. the neighbourhoods are nested — this is
  case (b) of the paper (Propositions 3 and 4).  Moreover, in this second case we may assume that
  the graph has at least five non-isolated vertices (otherwise it is also a blow-up of `C₅`);
  this is what makes "the two examples coincide for `n ≤ 5`".
-/

open Finset

namespace FranklFuredi

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A graph (given by a relation) which is symmetric, irreflexive, triangle-free and contains
no induced `2K₂`. -/
structure TF2K2 (G : V → V → Prop) : Prop where
  symm : ∀ {a b}, G a b → G b a
  irrefl : ∀ a, ¬G a a
  triangle : ∀ {a b c}, G a b → G b c → G a c → False
  twoK2 : ∀ {a b c d}, G a b → G c d → ¬G a c → ¬G a d → ¬G b c → ¬G b d → False

/-- `G` is a blow-up of the 5-cycle `0 - 1 - 2 - 3 - 4 - 0` plus isolated vertices:
`f w = some i` puts `w` into the `i`-th class, `f w = none` means that `w` is isolated. -/
def IsC5Blowup (G : V → V → Prop) (f : V → Option (Fin 5)) : Prop :=
  ∀ a b, G a b ↔ ∃ i, f a = some i ∧ (f b = some (i + 1) ∨ f b = some (i - 1))

/-- `G` is a bipartite chain graph with colour classes `A`, `B` and levels `lev`:
`a ∈ A` and `b ∈ B` are adjacent iff `lev b ≤ lev a`, and there are no other edges. -/
def IsChain (G : V → V → Prop) (A B : Finset V) (lev : V → ℕ) : Prop :=
  Disjoint A B ∧
    ∀ a b, G a b ↔ (a ∈ A ∧ b ∈ B ∧ lev b ≤ lev a) ∨ (a ∈ B ∧ b ∈ A ∧ lev a ≤ lev b)

variable {G : V → V → Prop} [DecidableRel G]

/-- The neighbourhood of `w`. -/
def nbhd (G : V → V → Prop) [DecidableRel G] (w : V) : Finset V := univ.filter (G w)

omit [DecidableEq V] in
@[simp] lemma mem_nbhd {w x : V} : x ∈ nbhd G w ↔ G w x := by simp [nbhd]

/-- The non-isolated vertices. -/
def nonIsolated (G : V → V → Prop) [DecidableRel G] : Finset V :=
  univ.filter (fun w => ∃ z, G w z)

/-! ### Case (a): an induced 5-cycle forces a blow-up of `C₅` -/

section Fin5Facts

lemma fin5_key : ∀ T : Finset (Fin 5), (∀ i ∈ T, i + 1 ∉ T) → (∀ i ∈ T, i + 2 ∈ T ∨ i + 3 ∈ T) →
    T = ∅ ∨ ∃ j, T = {j - 1, j + 1} := by decide

lemma fin5_uniq : ∀ j j' : Fin 5, ({j - 1, j + 1} : Finset (Fin 5)) = {j' - 1, j' + 1} → j = j' := by
  decide

lemma fin5_inter : ∀ i j : Fin 5, ¬(j = i + 1 ∨ j = i - 1) →
    ∃ k, k ∈ ({i - 1, i + 1} : Finset (Fin 5)) ∧ k ∈ ({j - 1, j + 1} : Finset (Fin 5)) := by
  decide

end Fin5Facts

omit [Fintype V] [DecidableEq V] in
/-- A triangle-free graph without induced `2K₂` which contains an induced 5-cycle `c` is a
blow-up of the 5-cycle (plus isolated vertices). -/
theorem isC5Blowup_of_c5 (hG : TF2K2 G) (c : Fin 5 → V)
    (hc : ∀ i j, G (c i) (c j) ↔ (j = i + 1 ∨ j = i - 1)) : ∃ f, IsC5Blowup G f := by
  classical
  let S : V → Finset (Fin 5) := fun w => univ.filter (fun i => G w (c i))
  have mem_S : ∀ w i, i ∈ S w ↔ G w (c i) := fun w i => by simp [S]
  have hS1 : ∀ w, ∀ i ∈ S w, i + 1 ∉ S w := by
    intro w i hi hi1
    rw [mem_S] at hi hi1
    exact hG.triangle hi ((hc i (i + 1)).mpr (Or.inl rfl)) hi1
  have f1 : ∀ i : Fin 5, i + 3 = i + 2 + 1 := by decide
  have f2 : ∀ i : Fin 5, ¬(i + 2 = i + 1 ∨ i + 2 = i - 1) := by decide
  have f3 : ∀ i : Fin 5, ¬(i + 3 = i + 1 ∨ i + 3 = i - 1) := by decide
  have hS2 : ∀ w, ∀ i ∈ S w, i + 2 ∈ S w ∨ i + 3 ∈ S w := by
    intro w i hi
    by_contra h
    push Not at h
    rw [mem_S] at hi
    rw [mem_S, mem_S] at h
    exact hG.twoK2 (a := w) (b := c i) (c := c (i + 2)) (d := c (i + 3)) hi
      ((hc _ _).mpr (Or.inl (f1 i))) h.1 h.2 (fun h' => f2 i ((hc _ _).mp h'))
      (fun h' => f3 i ((hc _ _).mp h'))
  have hS : ∀ w, S w = ∅ ∨ ∃ j, S w = {j - 1, j + 1} := fun w => fin5_key _ (hS1 w) (hS2 w)
  have g2 : ∀ j : Fin 5, j + 2 ∉ ({j - 1, j + 1} : Finset (Fin 5)) := by decide
  have g3 : ∀ j : Fin 5, j + 3 ∉ ({j - 1, j + 1} : Finset (Fin 5)) := by decide
  -- vertices seeing nothing of the cycle are isolated
  have hiso : ∀ w, S w = ∅ → ∀ z, ¬G w z := by
    intro w hw z hwz
    have hw' : ∀ i, ¬G w (c i) := fun i hi => by
      have : i ∈ S w := (mem_S w i).mpr hi
      rw [hw] at this
      simp at this
    rcases hS z with hz | ⟨j, hj⟩
    · have hz' : ∀ i, ¬G z (c i) := fun i hi => by
        have : i ∈ S z := (mem_S z i).mpr hi
        rw [hz] at this
        simp at this
      exact hG.twoK2 hwz ((hc 0 1).mpr (Or.inl rfl)) (hw' 0) (hw' 1) (hz' 0) (hz' 1)
    · have hz2 : ¬G z (c (j + 2)) := fun h => g2 j (hj ▸ (mem_S z _).mpr h)
      have hz3 : ¬G z (c (j + 3)) := fun h => g3 j (hj ▸ (mem_S z _).mpr h)
      exact hG.twoK2 hwz ((hc (j + 2) (j + 3)).mpr (Or.inl (f1 j))) (hw' _) (hw' _) hz2 hz3
  -- adjacency between two vertices seeing the cycle
  have h1 : ∀ i : Fin 5, i + 1 + 1 ∉ ({i - 1, i + 1} : Finset (Fin 5)) := by decide
  have h2 : ∀ i : Fin 5, i - 1 ∉ ({i + 1 - 1, i + 1 + 1} : Finset (Fin 5)) := by decide
  have h3 : ∀ i : Fin 5, ¬(i + 1 + 1 = i - 1 + 1 ∨ i + 1 + 1 = i - 1 - 1) := by decide
  have h4 : ∀ i : Fin 5, i - 1 - 1 ∉ ({i - 1, i + 1} : Finset (Fin 5)) := by decide
  have h5 : ∀ i : Fin 5, i + 1 ∉ ({i - 1 - 1, i - 1 + 1} : Finset (Fin 5)) := by decide
  have h6 : ∀ i : Fin 5, ¬(i - 1 - 1 = i + 1 + 1 ∨ i - 1 - 1 = i + 1 - 1) := by decide
  have hadj : ∀ w z i j, S w = {i - 1, i + 1} → S z = {j - 1, j + 1} →
      (G w z ↔ (j = i + 1 ∨ j = i - 1)) := by
    intro w z i j hw hz
    have hwc : ∀ k, G w (c k) ↔ k ∈ ({i - 1, i + 1} : Finset (Fin 5)) := fun k => by
      rw [← hw, mem_S]
    have hzc : ∀ k, G z (c k) ↔ k ∈ ({j - 1, j + 1} : Finset (Fin 5)) := fun k => by
      rw [← hz, mem_S]
    constructor
    · intro hwz
      by_contra hne
      obtain ⟨k, hk1, hk2⟩ := fin5_inter i j hne
      exact hG.triangle hwz ((hzc k).mpr hk2) ((hwc k).mpr hk1)
    · rintro (rfl | rfl)
      · by_contra hwz
        refine hG.twoK2 (a := w) (b := c (i - 1)) (c := z) (d := c (i + 1 + 1))
          ((hwc _).mpr (by simp)) ((hzc _).mpr (by simp)) hwz
          (fun h => ?_) (fun h => ?_) (fun h => ?_)
        · exact h1 i ((hwc _).mp h)
        · exact h2 i ((hzc _).mp (hG.symm h))
        · exact h3 i ((hc _ _).mp h)
      · by_contra hwz
        refine hG.twoK2 (a := w) (b := c (i + 1)) (c := z) (d := c (i - 1 - 1))
          ((hwc _).mpr (by simp)) ((hzc _).mpr (by simp)) hwz
          (fun h => ?_) (fun h => ?_) (fun h => ?_)
        · exact h4 i ((hwc _).mp h)
        · exact h5 i ((hzc _).mp (hG.symm h))
        · exact h6 i ((hc _ _).mp h)
  -- the class map
  let f : V → Option (Fin 5) := fun w =>
    if h : ∃ j, S w = {j - 1, j + 1} then some h.choose else none
  have hf_some : ∀ w j, S w = {j - 1, j + 1} → f w = some j := by
    intro w j hj
    have h : ∃ j, S w = {j - 1, j + 1} := ⟨j, hj⟩
    simp only [f, dite_eq_left h, Option.some.injEq]
    exact fin5_uniq _ _ (h.choose_spec.symm.trans hj)
  have hf_none : ∀ w, S w = ∅ → f w = none := by
    intro w hw
    have h : ¬∃ j, S w = {j - 1, j + 1} := by
      rintro ⟨j, hj⟩
      rw [hw] at hj
      exact (insert_ne_empty _ _) hj.symm
    simp only [f, dite_eq_right h]
  refine ⟨f, fun a b => ?_⟩
  rcases hS a with ha | ⟨i, hi⟩
  · rw [hf_none a ha]
    simp only [reduceCtorEq, false_and, exists_false, iff_false]
    exact hiso a ha b
  rcases hS b with hb | ⟨j, hj⟩
  · rw [hf_none b hb]
    simp only [reduceCtorEq, or_self, and_false, exists_false, iff_false]
    exact fun h => hiso b hb a (hG.symm h)
  rw [hf_some a i hi, hf_some b j hj, hadj a b i j hi hj]
  simp

/-! ### The dichotomy -/

/-- **Dichotomy.**  A triangle-free graph without induced `2K₂` is either a blow-up of the
5-cycle (plus isolated vertices), or a bipartite chain graph with at least five non-isolated
vertices. -/
theorem dichotomy (hG : TF2K2 G) :
    (∃ f, IsC5Blowup G f) ∨ ∃ A B lev, IsChain G A B lev ∧ 5 ≤ (nonIsolated G).card := by
  classical
  by_cases hE : ∃ a b, G a b
  swap
  · push Not at hE
    exact Or.inl ⟨fun _ => none, fun a b => by simp [hE a b]⟩
  obtain ⟨a₀, b₀, h₀⟩ := hE
  obtain ⟨v, -, hv⟩ := exists_max_image univ (fun w => (nbhd G w).card) ⟨a₀, mem_univ _⟩
  have hv' : ∀ w, (nbhd G w).card ≤ (nbhd G v).card := fun w => hv w (mem_univ w)
  by_cases hR : ∃ x y, G x y ∧ ¬G v x ∧ ¬G v y
  · ---------------------------------------------------------------- case (a)
    left
    obtain ⟨x, y, hxy, hvx, hvy⟩ := hR
    have hA : ∀ a, G v a → G a x ∨ G a y := by
      intro a ha
      by_contra h
      push Not at h
      exact hG.twoK2 ha hxy hvx hvy h.1 h.2
    have hax : ∃ a, G v a ∧ G a x := by
      by_contra h
      push Not at h
      have hsub : insert x (nbhd G v) ⊆ nbhd G y := by
        intro z hz
        rw [mem_insert] at hz
        rw [mem_nbhd]
        rcases hz with rfl | hz
        · exact hG.symm hxy
        · rw [mem_nbhd] at hz
          exact hG.symm ((hA z hz).resolve_left (h z hz))
      have hxA : x ∉ nbhd G v := by rw [mem_nbhd]; exact hvx
      have h1 := card_le_card hsub
      rw [card_insert_of_notMem hxA] at h1
      have h2 := hv' y
      omega
    have hay : ∃ a, G v a ∧ G a y := by
      by_contra h
      push Not at h
      have hsub : insert y (nbhd G v) ⊆ nbhd G x := by
        intro z hz
        rw [mem_insert] at hz
        rw [mem_nbhd]
        rcases hz with rfl | hz
        · exact hxy
        · rw [mem_nbhd] at hz
          exact hG.symm ((hA z hz).resolve_right (h z hz))
      have hyA : y ∉ nbhd G v := by rw [mem_nbhd]; exact hvy
      have h1 := card_le_card hsub
      rw [card_insert_of_notMem hyA] at h1
      have h2 := hv' x
      omega
    obtain ⟨a, hva, hax⟩ := hax
    obtain ⟨a', hva', ha'y⟩ := hay
    have hay' : ¬G a y := fun h => hG.triangle hax hxy h
    have ha'x : ¬G a' x := fun h => hG.triangle h hxy ha'y
    have haa' : ¬G a a' := fun h => hG.triangle hva h hva'
    have s1 := hG.symm hva
    have s2 := hG.symm hax
    have s3 := hG.symm hxy
    have s4 := hG.symm ha'y
    have s5 := hG.symm hva'
    have t1 : ¬G x v := fun h => hvx (hG.symm h)
    have t2 : ¬G y v := fun h => hvy (hG.symm h)
    have t3 : ¬G y a := fun h => hay' (hG.symm h)
    have t4 : ¬G x a' := fun h => ha'x (hG.symm h)
    have t5 : ¬G a' a := fun h => haa' (hG.symm h)
    have i1 := hG.irrefl v
    have i2 := hG.irrefl a
    have i3 := hG.irrefl x
    have i4 := hG.irrefl y
    have i5 := hG.irrefl a'
    apply isC5Blowup_of_c5 hG ![v, a, x, y, a']
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp +decide [hva, hax, hxy, ha'y, hva', hvx, hvy, hay', ha'x, haa', s1, s2, s3, s4, s5,
        t1, t2, t3, t4, t5, i1, i2, i3, i4, i5]
  · ---------------------------------------------------------------- case (b)
    push Not at hR
    set A := nbhd G v with hAdef
    have hedge : ∀ x y, G x y → x ∈ A ∨ y ∈ A := by
      intro x y hxy
      by_cases hx : G v x
      · exact Or.inl (mem_nbhd.mpr hx)
      · exact Or.inr (mem_nbhd.mpr (hR x y hxy hx))
    have hAind : ∀ a ∈ A, ∀ a' ∈ A, ¬G a a' := by
      intro a ha a' ha' h
      rw [mem_nbhd] at ha ha'
      exact hG.triangle ha h ha'
    set B : Finset V := univ.filter (fun w => w ∉ A ∧ ∃ z, G w z) with hBdef
    have mem_B : ∀ w, w ∈ B ↔ w ∉ A ∧ ∃ z, G w z := fun w => by simp [hBdef]
    -- the neighbourhoods of the vertices of `A` are nested (Proposition 3)
    have hnest : ∀ a ∈ A, ∀ a' ∈ A, nbhd G a ⊆ nbhd G a' ∨ nbhd G a' ⊆ nbhd G a := by
      intro a ha a' ha'
      by_contra h
      push Not at h
      obtain ⟨b, hb, hb'⟩ := not_subset.mp h.1
      obtain ⟨b', hb'1, hb'2⟩ := not_subset.mp h.2
      rw [mem_nbhd] at hb hb' hb'1 hb'2
      have hbA : b ∉ A := fun hbA => hAind a ha b hbA hb
      have hb'A : b' ∉ A := fun h' => hAind a' ha' b' h' hb'1
      have hbb' : ¬G b b' := fun h => by rcases hedge b b' h with h | h <;> contradiction
      exact hG.twoK2 hb hb'1 (hAind a ha a' ha') hb'2 (fun h => hb' (hG.symm h)) hbb'
    have hmono : ∀ a ∈ A, ∀ a' ∈ A, (nbhd G a).card ≤ (nbhd G a').card →
        nbhd G a ⊆ nbhd G a' := by
      intro a ha a' ha' hle
      rcases hnest a ha a' ha' with h | h
      · exact h
      · exact (eq_of_subset_of_card_le h hle).ge
    -- levels
    let lev : V → ℕ := fun w => if w ∈ A then (nbhd G w).card else
      if h : (nbhd G w).Nonempty then
        ((nbhd G w).image (fun a => (nbhd G a).card)).min' (h.image _) else 0
    have hlevA : ∀ a ∈ A, lev a = (nbhd G a).card := fun a ha => by simp [lev, ha]
    have hlev_le : ∀ w ∉ A, ∀ a, G w a → lev w ≤ (nbhd G a).card := by
      intro w hw a hwa
      have hne : (nbhd G w).Nonempty := ⟨a, mem_nbhd.mpr hwa⟩
      simp only [lev, ite_eq_right hw, dite_eq_left hne]
      exact min'_le _ _ (mem_image_of_mem _ (mem_nbhd.mpr hwa))
    have hlev_mem : ∀ w ∉ A, (∃ z, G w z) → ∃ a, G w a ∧ (nbhd G a).card = lev w := by
      rintro w hw ⟨z, hwz⟩
      have hne : (nbhd G w).Nonempty := ⟨z, mem_nbhd.mpr hwz⟩
      have := min'_mem _ (hne.image (fun a => (nbhd G a).card))
      rw [mem_image] at this
      obtain ⟨a, ha, heq⟩ := this
      refine ⟨a, mem_nbhd.mp ha, ?_⟩
      simp only [lev, ite_eq_right hw, dite_eq_left hne]
      exact heq
    have hdisj : Disjoint A B := by
      rw [disjoint_left]
      intro w hwA hwB
      exact ((mem_B w).mp hwB).1 hwA
    have hchain : IsChain G A B lev := by
      refine ⟨hdisj, fun a b => ⟨fun hab => ?_, ?_⟩⟩
      · rcases hedge a b hab with haA | hbA
        · left
          have hbA : b ∉ A := fun hbA => hAind a haA b hbA hab
          refine ⟨haA, (mem_B b).mpr ⟨hbA, a, hG.symm hab⟩, ?_⟩
          rw [hlevA a haA]
          exact hlev_le b hbA a (hG.symm hab)
        · right
          have haA : a ∉ A := fun haA => hAind b hbA a haA (hG.symm hab)
          refine ⟨(mem_B a).mpr ⟨haA, b, hab⟩, hbA, ?_⟩
          rw [hlevA b hbA]
          exact hlev_le a haA b hab
      · rintro (⟨haA, hbB, hle⟩ | ⟨haB, hbA, hle⟩)
        · obtain ⟨hbA, hbn⟩ := (mem_B b).mp hbB
          obtain ⟨a₁, hba₁, heq⟩ := hlev_mem b hbA hbn
          have ha₁A : a₁ ∈ A := (hedge b a₁ hba₁).resolve_left hbA
          rw [hlevA a haA] at hle
          have hsub := hmono a₁ ha₁A a haA (by omega)
          exact mem_nbhd.mp (hsub (mem_nbhd.mpr (hG.symm hba₁)))
        · obtain ⟨haA, han⟩ := (mem_B a).mp haB
          obtain ⟨b₁, hab₁, heq⟩ := hlev_mem a haA han
          have hb₁A : b₁ ∈ A := (hedge a b₁ hab₁).resolve_left haA
          rw [hlevA b hbA] at hle
          have hsub := hmono b₁ hb₁A b hbA (by omega)
          exact hG.symm (mem_nbhd.mp (hsub (mem_nbhd.mpr (hG.symm hab₁))))
    -- the vertex `v` lies in `B` and is adjacent to all of `A`
    have hvB : v ∈ B := by
      refine (mem_B v).mpr ⟨fun h => hG.irrefl v (mem_nbhd.mp h), ?_⟩
      have h1 : 0 < (nbhd G a₀).card := card_pos.mpr ⟨b₀, mem_nbhd.mpr h₀⟩
      obtain ⟨z, hz⟩ := card_pos.mp (lt_of_lt_of_le h1 (hv' a₀))
      exact ⟨z, mem_nbhd.mp hz⟩
    have hvlev : ∀ a ∈ A, lev v ≤ lev a := by
      intro a ha
      have := (hchain.2 v a).mp (mem_nbhd.mp ha)
      rcases this with ⟨hvA, -, -⟩ | ⟨-, -, hle⟩
      · exact absurd hvA ((mem_B v).mp hvB).1
      · exact hle
    by_cases hcond : ∀ a ∈ A, ∀ b ∈ B, (∃ b' ∈ B, lev a < lev b') → (∃ a' ∈ A, lev a' < lev b) →
        lev a < lev b
    · -------------------------------------------- few levels: still a blow-up of `C₅`
      left
      let f : V → Option (Fin 5) := fun w =>
        if w ∈ A then (if ∀ b ∈ B, lev b ≤ lev w then some 2 else some 0)
        else if w ∈ B then (if ∀ a ∈ A, lev w ≤ lev a then some 1 else some 3) else none
      have hAB : ∀ w, w ∈ A → w ∉ B := fun w hw => disjoint_left.mp hdisj hw
      have hBA : ∀ w, w ∈ B → w ∉ A := fun w hw hwA => hAB w hwA hw
      have hfA : ∀ w ∈ A, f w = if ∀ b ∈ B, lev b ≤ lev w then some 2 else some 0 :=
        fun w hw => by simp only [f, hw, ↓reduceIte]
      have hfB : ∀ w ∈ B, f w = if ∀ a ∈ A, lev w ≤ lev a then some 1 else some 3 :=
        fun w hw => by simp only [f, hBA w hw, hw, ↓reduceIte]
      have hfN : ∀ w, w ∉ A → w ∉ B → f w = none :=
        fun w h1 h2 => by simp only [f, h1, h2, ↓reduceIte]
      refine ⟨f, fun a b => ?_⟩
      rw [hchain.2 a b]
      by_cases haA : a ∈ A
      · have haB := hAB a haA
        by_cases hbA : b ∈ A
        · have hbB := hAB b hbA
          rw [hfA a haA, hfA b hbA]
          by_cases h1 : ∀ b ∈ B, lev b ≤ lev a
          · rw [ite_eq_left h1]
            by_cases h2 : ∀ a ∈ B, lev a ≤ lev b
            · rw [ite_eq_left h2]; simp +decide [haB, hbB]
            · rw [ite_eq_right h2]; simp +decide [haB, hbB]
          · rw [ite_eq_right h1]
            by_cases h2 : ∀ a ∈ B, lev a ≤ lev b
            · rw [ite_eq_left h2]; simp +decide [haB, hbB]
            · rw [ite_eq_right h2]; simp +decide [haB, hbB]
        by_cases hbB : b ∈ B
        · rw [hfA a haA, hfB b hbB]
          by_cases hhi : ∀ b ∈ B, lev b ≤ lev a
          · have := hhi b hbB
            rw [ite_eq_left hhi]
            by_cases hlo : ∀ a ∈ A, lev b ≤ lev a
            · rw [ite_eq_left hlo]; simp +decide [haA, hbB, this]
            · rw [ite_eq_right hlo]; simp +decide [haA, hbB, this]
          · rw [ite_eq_right hhi]
            by_cases hlo : ∀ a ∈ A, lev b ≤ lev a
            · have := hlo a haA
              rw [ite_eq_left hlo]; simp +decide [haA, hbB, this]
            · rw [ite_eq_right hlo]
              have h' := hhi
              have h'' := hlo
              push Not at h' h''
              have := hcond a haA b hbB h' h''
              have hn : ¬ lev b ≤ lev a := by omega
              simp +decide [haB, hbA, hn]
        · rw [hfA a haA, hfN b hbA hbB]
          by_cases h1 : ∀ b ∈ B, lev b ≤ lev a
          · rw [ite_eq_left h1]; simp [hbA, hbB]
          · rw [ite_eq_right h1]; simp [hbA, hbB]
      by_cases haB : a ∈ B
      · by_cases hbA : b ∈ A
        · have hbB := hAB b hbA
          rw [hfB a haB, hfA b hbA]
          by_cases hhi : ∀ a ∈ B, lev a ≤ lev b
          · have := hhi a haB
            rw [ite_eq_left hhi]
            by_cases hlo : ∀ b ∈ A, lev a ≤ lev b
            · rw [ite_eq_left hlo]; simp +decide [haB, hbA, this]
            · rw [ite_eq_right hlo]; simp +decide [haB, hbA, this]
          · rw [ite_eq_right hhi]
            by_cases hlo : ∀ b ∈ A, lev a ≤ lev b
            · have := hlo b hbA
              rw [ite_eq_left hlo]; simp +decide [haB, hbA, this]
            · rw [ite_eq_right hlo]
              have h' := hhi
              have h'' := hlo
              push Not at h' h''
              have := hcond b hbA a haB h' h''
              have hn : ¬ lev a ≤ lev b := by omega
              simp +decide [haA, hbB, hn]
        by_cases hbB : b ∈ B
        · have hbA' := hBA b hbB
          rw [hfB a haB, hfB b hbB]
          by_cases h1 : ∀ b ∈ A, lev a ≤ lev b
          · rw [ite_eq_left h1]
            by_cases h2 : ∀ a ∈ A, lev b ≤ lev a
            · rw [ite_eq_left h2]; simp +decide [haA, hbA']
            · rw [ite_eq_right h2]; simp +decide [haA, hbA']
          · rw [ite_eq_right h1]
            by_cases h2 : ∀ a ∈ A, lev b ≤ lev a
            · rw [ite_eq_left h2]; simp +decide [haA, hbA']
            · rw [ite_eq_right h2]; simp +decide [haA, hbA']
        · rw [hfB a haB, hfN b hbA hbB]
          by_cases h1 : ∀ b ∈ A, lev a ≤ lev b
          · rw [ite_eq_left h1]; simp [hbA, hbB]
          · rw [ite_eq_right h1]; simp [hbA, hbB]
      · rw [hfN a haA haB]
        simp [haA, haB]
    · -------------------------------------------- at least five non-isolated vertices
      right
      refine ⟨A, B, lev, hchain, ?_⟩
      push Not at hcond
      obtain ⟨a, haA, b, hbB, ⟨b', hb'B, hab'⟩, ⟨a', ha'A, ha'b⟩, hba⟩ := hcond
      have hva' := hvlev a' ha'A
      have hAB : ∀ w, w ∈ A → w ∉ B := fun w hw => disjoint_left.mp hdisj hw
      have n1 : a ≠ a' := by rintro rfl; omega
      have n2 : b ≠ b' := by rintro rfl; omega
      have n3 : b ≠ v := by rintro rfl; omega
      have n4 : b' ≠ v := by rintro rfl; omega
      have n5 : a ≠ b := fun h => hAB a haA (h ▸ hbB)
      have n6 : a ≠ b' := fun h => hAB a haA (h ▸ hb'B)
      have n7 : a ≠ v := fun h => hAB a haA (h ▸ hvB)
      have n8 : a' ≠ b := fun h => hAB a' ha'A (h ▸ hbB)
      have n9 : a' ≠ b' := fun h => hAB a' ha'A (h ▸ hb'B)
      have n10 : a' ≠ v := fun h => hAB a' ha'A (h ▸ hvB)
      have hsub : ({a, a', b, b', v} : Finset V) ⊆ nonIsolated G := by
        intro w hw
        simp only [mem_insert, mem_singleton] at hw
        simp only [nonIsolated, mem_filter, mem_univ, true_and]
        rcases hw with rfl | rfl | rfl | rfl | rfl
        · exact ⟨v, hG.symm (mem_nbhd.mp haA)⟩
        · exact ⟨v, hG.symm (mem_nbhd.mp ha'A)⟩
        · exact ((mem_B _).mp hbB).2
        · exact ((mem_B _).mp hb'B).2
        · exact ((mem_B _).mp hvB).2
      have hcard : ({a, a', b, b', v} : Finset V).card = 5 := by
        rw [card_insert_of_notMem (by simp [n1, n5, n6, n7]),
          card_insert_of_notMem (by simp [n8, n9, n10]),
          card_insert_of_notMem (by simp [n2, n3]), card_pair n4]
      exact hcard ▸ card_le_card hsub

end FranklFuredi
