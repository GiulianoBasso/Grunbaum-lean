/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import Grunbaum.Polygon

/-!
# Twin-free circle 3-graphs are regular polygons

Example 2 of Frankl and Füredi is the 3-graph `FranklFuredi.circleGraph p` of points `p v` on
the unit circle, in which a triple is an edge iff its triangle contains the origin. By Remark 1 of
their paper, the points can be moved to a regular `(2N+1)`-gon. We prove this for twin-free
circle 3-graphs, i.e. if any two points lie in a common edge; this is the case needed for (FF).

## Main result

* `Grunbaum.exists_equiv_polygon_of_twinFree` : a twin-free circle 3-graph is `T_{2N+1}`, the
  two-graph `[R_{2N+1}]` of the regular `(2N+1)`-gon, up to relabelling.

## Proof

Replace every point `p v` by `q v = ±p v` in the half-plane `{y > 0} ∪ {y = 0, x > 0}`, and write
`p v = ε v • q v`. The determinant orders these representatives: `v ≺ w` iff `det(q v, q w) > 0`.
For `u ≺ v ≺ w` the triangle `p u p v p w` contains the origin iff `ε u = ε w ≠ ε v`
(`Grunbaum.isEdge_circleGraph_iff_of_precedes`). If two consecutive points have the same sign, or
if the first and the last point have different signs, then these two points are twins. Hence in a
twin-free circle 3-graph the signs alternate and the number of points is odd, `2N + 1`. Finally,
a triple of positions `i < j < k` is an edge iff `j - i` and `k - j` are odd, and the relabelling
`j ↦ j (N + 1) mod (2N + 1)` identifies this 3-graph with `T_{2N+1}`
(`Grunbaum.coherent_polygonMatrix_halve`).
-/

open Finset Matrix FranklFuredi

namespace Grunbaum

/-! ### The half-plane `{y > 0} ∪ {y = 0, x > 0}` -/

/-- The half-plane `{y > 0} ∪ {y = 0, x > 0}`. -/
def UpperHalf (q : ℝ × ℝ) : Prop := 0 < q.2 ∨ (q.2 = 0 ∧ 0 < q.1)

open Classical in
/-- The sign `±1` which moves `q` into `UpperHalf`. -/
noncomputable def halfSign (q : ℝ × ℝ) : ℝ := if UpperHalf q then 1 else -1

lemma halfSign_eq (q : ℝ × ℝ) : halfSign q = 1 ∨ halfSign q = -1 := by
  unfold halfSign; split_ifs <;> simp

lemma halfSign_mul_self (q : ℝ × ℝ) : halfSign q * halfSign q = 1 := by
  rcases halfSign_eq q with h | h <;> rw [h] <;> norm_num

lemma upperHalf_halfSign_smul {q : ℝ × ℝ} (hq : q ≠ 0) : UpperHalf (halfSign q • q) := by
  unfold halfSign
  split_ifs with h
  · simpa using h
  · simp only [UpperHalf, not_or, not_and, not_lt] at h
    simp only [UpperHalf, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, neg_one_mul, neg_pos,
      neg_eq_zero]
    rcases lt_or_eq_of_le h.1 with h2 | h2
    · exact Or.inl h2
    · right
      refine ⟨h2, lt_of_le_of_ne (h.2 h2) fun h1 => hq ?_⟩
      ext <;> simp [h1, h2]

lemma det2_smul_smul (a b : ℝ) (u v : ℝ × ℝ) : det2 (a • u) (b • v) = a * b * det2 u v := by
  simp [det2]; ring

/-- On `UpperHalf`, the determinant defines a transitive relation. -/
lemma det2_pos_trans {u v w : ℝ × ℝ} (hu : UpperHalf u) (hv : UpperHalf v) (hw : UpperHalf w)
    (huv : 0 < det2 u v) (hvw : 0 < det2 v w) : 0 < det2 u w := by
  have hid := congrArg Prod.snd (det2_identity u v w)
  simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, Prod.snd_zero] at hid
  have hu2 : 0 ≤ u.2 := by rcases hu with h | ⟨h, -⟩ <;> linarith
  have hv2 : 0 < v.2 := by
    rcases hv with h | ⟨h0, h1⟩
    · exact h
    · exfalso
      simp only [det2, h0, mul_zero, zero_sub] at huv
      nlinarith
  have hw2 : 0 < w.2 := by
    rcases hw with h | ⟨h0, h1⟩
    · exact h
    · exfalso
      simp only [det2, h0, mul_zero, zero_sub] at hvw
      nlinarith
  have h1 : 0 ≤ det2 v w * u.2 := mul_nonneg hvw.le hu2
  have h2 : 0 < det2 u v * w.2 := mul_pos huv hw2
  have h3 : det2 w u * v.2 < 0 := by linarith
  have h4 : det2 w u < 0 := by
    by_contra h
    push Not at h
    nlinarith
  rw [det2_antisymm] at h4
  linarith

/-! ### The order of the points -/

section Order

variable {V : Type*} {p : V → ℝ × ℝ}

/-- The representative of `p v` in `UpperHalf`. -/
noncomputable def halfRep (p : V → ℝ × ℝ) (v : V) : ℝ × ℝ := halfSign (p v) • p v

/-- The order of the points: `v ≺ w` iff `det(q v, q w) > 0`. -/
def Precedes (p : V → ℝ × ℝ) (v w : V) : Prop := 0 < det2 (halfRep p v) (halfRep p w)

lemma p_eq_halfSign_smul (v : V) : p v = halfSign (p v) • halfRep p v := by
  rw [halfRep, smul_smul, halfSign_mul_self, one_smul]

lemma det2_halfRep (v w : V) :
    det2 (halfRep p v) (halfRep p w) = halfSign (p v) * halfSign (p w) * det2 (p v) (p w) := by
  rw [halfRep, halfRep, det2_smul_smul]

lemma det2_eq_halfSign_mul (v w : V) :
    det2 (p v) (p w) = halfSign (p v) * halfSign (p w) * det2 (halfRep p v) (halfRep p w) := by
  rw [det2_halfRep]
  linear_combination (-(det2 (p v) (p w)) * halfSign (p w) * halfSign (p w)) *
    halfSign_mul_self (p v) - det2 (p v) (p w) * halfSign_mul_self (p w)

variable (hp : GenPos p) (hp0 : ∀ v, p v ≠ 0)
include hp hp0

omit hp in
lemma precedes_trans {u v w : V} (huv : Precedes p u v) (hvw : Precedes p v w) :
    Precedes p u w :=
  det2_pos_trans (upperHalf_halfSign_smul (hp0 u)) (upperHalf_halfSign_smul (hp0 v))
    (upperHalf_halfSign_smul (hp0 w)) huv hvw

omit hp0 in
lemma precedes_or_precedes {v w : V} (hvw : v ≠ w) : Precedes p v w ∨ Precedes p w v := by
  have h := hp v w hvw
  have h' : det2 (halfRep p v) (halfRep p w) ≠ 0 := by
    rw [det2_halfRep]
    exact mul_ne_zero (mul_ne_zero (by rcases halfSign_eq (p v) with h | h <;> simp [h])
      (by rcases halfSign_eq (p w) with h | h <;> simp [h])) h
  rcases lt_or_gt_of_ne h' with h1 | h1
  · right
    unfold Precedes
    rw [det2_antisymm]
    linarith
  · exact Or.inl h1

omit hp hp0 in
lemma not_precedes_self (v : V) : ¬Precedes p v v := by
  simp [Precedes, det2_self]

omit hp hp0 in
lemma not_precedes_of_precedes {v w : V} (h : Precedes p v w) : ¬Precedes p w v := by
  unfold Precedes at *
  rw [det2_antisymm]
  linarith

variable [Fintype V]

omit hp hp0 in
/-- The rank of `v`: the number of points before `v`. -/
noncomputable def rank (p : V → ℝ × ℝ) (v : V) : ℕ :=
  open Classical in (univ.filter fun w => Precedes p w v).card

omit hp in
lemma rank_lt_rank {v w : V} (h : Precedes p v w) : rank p v < rank p w := by
  classical
  unfold rank
  refine card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩
  · simp only [mem_filter, mem_univ, true_and] at hx ⊢
    exact precedes_trans hp0 hx h
  · have : v ∈ univ.filter fun x => Precedes p x v := hsub (by simp [h])
    simp only [mem_filter, mem_univ, true_and] at this
    exact not_precedes_self v this

omit hp hp0 in
lemma rank_lt_card (v : V) : rank p v < Fintype.card V := by
  classical
  unfold rank
  rw [← card_univ]
  exact card_lt_card ⟨subset_univ _, fun h => not_precedes_self (p := p) v (by
    simpa using h (mem_univ v))⟩

lemma rank_injective : Function.Injective (rank p) := by
  intro v w h
  by_contra hvw
  rcases precedes_or_precedes hp hvw with h' | h' <;>
    [exact (rank_lt_rank hp0 h').ne h; exact (rank_lt_rank hp0 h').ne h.symm]

/-- The points in the order `≺`. -/
noncomputable def rankEquiv : V ≃ Fin (Fintype.card V) :=
  Equiv.ofBijective (fun v => ⟨rank p v, rank_lt_card v⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun v w h => rank_injective hp hp0 (Fin.mk.inj_iff.mp h), by simp⟩)

lemma rankEquiv_lt_iff {v w : V} : rankEquiv hp hp0 v < rankEquiv hp hp0 w ↔ Precedes p v w := by
  constructor
  · intro h
    have hvw : v ≠ w := fun e => by rw [e] at h; exact lt_irrefl _ h
    rcases precedes_or_precedes hp hvw with h' | h'
    · exact h'
    · exact absurd (rank_lt_rank hp0 h') (not_lt.mpr (le_of_lt (Fin.lt_def.mp h)))
  · intro h
    exact Fin.lt_def.mpr (rank_lt_rank hp0 h)

end Order

/-! ### The edges in terms of the order and the signs -/

lemma cyc_iff_of_pos {A B C s t r : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) (hr : r = 1 ∨ r = -1) :
    Cyc (s * t * A) (t * r * B) (-(r * s * C)) ↔ s = r ∧ t ≠ s := by
  have hA' : ¬A < 0 := not_lt.mpr hA.le
  have hB' : ¬B < 0 := not_lt.mpr hB.le
  have hC' : ¬C < 0 := not_lt.mpr hC.le
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> rcases hr with rfl | rfl <;>
    norm_num [Cyc, hA, hB, hC, hA', hB', hC']

section Edges

variable {V : Type*} [Fintype V] [DecidableEq V] {p : V → ℝ × ℝ}

/-- For `u ≺ v ≺ w`, the triangle `p u p v p w` contains the origin iff the signs satisfy
`ε u = ε w ≠ ε v`. -/
theorem isEdge_circleGraph_iff_of_precedes (hp : GenPos p) (hp0 : ∀ v, p v ≠ 0) {u v w : V}
    (huv : Precedes p u v) (hvw : Precedes p v w) :
    (circleGraph p).IsEdge u v w ↔
      halfSign (p u) = halfSign (p w) ∧ halfSign (p v) ≠ halfSign (p u) := by
  have huw := precedes_trans hp0 huv hvw
  have hne : ∀ {x y : V}, Precedes p x y → x ≠ y := fun h e => by
    rw [e] at h; exact not_precedes_self _ h
  rw [isEdge_circleGraph_iff_cyc hp (hne huv) (hne huw) (hne hvw)]
  have e1 := det2_eq_halfSign_mul (p := p) u v
  have e2 := det2_eq_halfSign_mul (p := p) v w
  have e3 : det2 (p w) (p u) =
      -(halfSign (p u) * halfSign (p w) * det2 (halfRep p u) (halfRep p w)) := by
    rw [det2_antisymm, det2_eq_halfSign_mul]
  rw [e1, e2, e3, mul_comm (halfSign (p u)) (halfSign (p w))]
  exact cyc_iff_of_pos huv hvw huw (halfSign_eq _) (halfSign_eq _) (halfSign_eq _)

end Edges

/-! ### The relabelling `j ↦ j (N + 1) mod (2N + 1)` -/

/-- The relabelling of positions `j ∈ {0, …, 2N}` by vertices of the regular `(2N+1)`-gon:
`2s ↦ s` and `2s + 1 ↦ s + N + 1`, i.e. `j ↦ j (N + 1) mod (2N + 1)`. -/
def halve (N j : ℕ) : ℕ := if j % 2 = 0 then j / 2 else j / 2 + N + 1

lemma halve_lt {N j : ℕ} (hj : j < 2 * N + 1) : halve N j < 2 * N + 1 := by
  unfold halve; split_ifs <;> omega

lemma halve_injective {N i j : ℕ} (hi : i < 2 * N + 1) (hj : j < 2 * N + 1)
    (h : halve N i = halve N j) : i = j := by
  unfold halve at h; split_ifs at h <;> omega

/-- The relabelling as a permutation of `Fin (2N+1)`. -/
noncomputable def halveEquiv (N : ℕ) : Fin (2 * N + 1) ≃ Fin (2 * N + 1) :=
  Equiv.ofBijective (fun j => ⟨halve N j, halve_lt j.2⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun i j h => Fin.ext (halve_injective i.2 j.2 (Fin.mk.inj_iff.mp h)), rfl⟩)

/-- In the relabelling `Grunbaum.halve`, the positions `i < j < k` form a coherent triple of
`R_{2N+1}` iff `j - i` and `k - j` are odd. -/
theorem coherent_polygonMatrix_halve {N : ℕ} {i j k : Fin (2 * N + 1)} (hij : i < j)
    (hjk : j < k) :
    Coherent (polygonMatrix N) (halveEquiv N i) (halveEquiv N j) (halveEquiv N k) ↔
      (j : ℕ) % 2 ≠ (i : ℕ) % 2 ∧ (k : ℕ) % 2 ≠ (j : ℕ) % 2 := by
  have hij' : (i : ℕ) < j := hij
  have hjk' : (j : ℕ) < k := hjk
  have hk : (k : ℕ) < 2 * N + 1 := k.2
  unfold Coherent polygonMatrix halveEquiv
  simp only [of_apply, Equiv.ofBijective_apply]
  unfold halve
  split_ifs <;> norm_num <;> omega

/-! ### Twin-free circle 3-graphs -/

section TwinFree

variable {V : Type*} [Fintype V] [DecidableEq V] {p : V → ℝ × ℝ}

/-- The edges of a circle 3-graph in terms of the positions `i < j < k` of the points in the order
`≺` and their signs. -/
lemma isEdge_rankEquiv_symm_iff (hp : GenPos p) (hp0 : ∀ v, p v ≠ 0)
    {i j k : Fin (Fintype.card V)} (hij : i < j) (hjk : j < k) :
    (circleGraph p).IsEdge ((rankEquiv hp hp0).symm i) ((rankEquiv hp hp0).symm j)
        ((rankEquiv hp hp0).symm k) ↔
      halfSign (p ((rankEquiv hp hp0).symm i)) = halfSign (p ((rankEquiv hp hp0).symm k)) ∧
        halfSign (p ((rankEquiv hp hp0).symm j)) ≠ halfSign (p ((rankEquiv hp hp0).symm i)) := by
  apply isEdge_circleGraph_iff_of_precedes hp hp0
  · rw [← rankEquiv_lt_iff hp hp0]; simpa using hij
  · rw [← rankEquiv_lt_iff hp hp0]; simpa using hjk

/-- **Twin-free circle 3-graphs are regular polygons.** If any two points of a circle 3-graph lie
in a common edge, then the number of points is odd, `2N + 1`, and after relabelling the 3-graph is
`T_{2N+1} = [R_{2N+1}]`. This is Remark 1 of Frankl and Füredi in the twin-free case. -/
theorem exists_equiv_polygon_of_twinFree [Nonempty V] (hp : GenPos p) (hp0 : ∀ v, p v ≠ 0)
    (htf : ThreeGraph.TwinFree (circleGraph p)) :
    ∃ (N : ℕ) (e : V ≃ Fin (2 * N + 1)),
      circleGraph p = (twoGraph (polygonMatrix N)).pullback e := by
  set n := Fintype.card V with hn_def
  set e₀ := rankEquiv hp hp0 with he₀
  set col : Fin n → ℝ := fun i => halfSign (p (e₀.symm i)) with hcol_def
  have hcol : ∀ i, col i = 1 ∨ col i = -1 := fun i => halfSign_eq _
  have hedge : ∀ i j k : Fin n, i < j → j < k →
      ((circleGraph p).IsEdge (e₀.symm i) (e₀.symm j) (e₀.symm k) ↔
        col i = col k ∧ col j ≠ col i) :=
    fun i j k hij hjk => isEdge_rankEquiv_symm_iff hp hp0 hij hjk
  have htwin : ∀ i j : Fin n, i ≠ j →
      ∃ k, (circleGraph p).IsEdge (e₀.symm i) (e₀.symm j) (e₀.symm k) := by
    intro i j hij
    obtain ⟨z, hz⟩ := htf (e₀.symm i) (e₀.symm j) (e₀.symm.injective.ne hij)
    exact ⟨e₀ z, by simpa using hz⟩
  -- the signs of consecutive points differ
  have halt : ∀ i j : Fin n, (j : ℕ) = i + 1 → col j ≠ col i := by
    intro i j hj hcij
    have hij : i < j := Fin.lt_def.mpr (by omega)
    obtain ⟨k, hk⟩ := htwin i j hij.ne
    rcases lt_trichotomy k i with hki | rfl | hik
    · have := (hedge k i j hki hij).mp (ThreeGraph.isEdge_rotate.mp
        (ThreeGraph.isEdge_rotate.mp hk))
      exact this.2 (this.1.trans hcij).symm
    · exact hk.ne_13 rfl
    · rcases lt_trichotomy k j with hkj | rfl | hjk
      · exact absurd (Fin.lt_def.mp hkj) (by have := Fin.lt_def.mp hik; omega)
      · exact hk.ne_23 rfl
      · exact ((hedge i j k hij hjk).mp hk).2 hcij
  -- hence the sign of a point is determined by the parity of its position
  have hpar : ∀ i j : Fin n, (col i = col j ↔ (i : ℕ) % 2 = (j : ℕ) % 2) := by
    have hstep : ∀ i j : Fin n, (j : ℕ) = i + 1 → col j = -col i := by
      intro i j hj
      have h := halt i j hj
      rcases hcol i with h1 | h1 <;> rcases hcol j with h2 | h2
      · exact absurd (h2.trans h1.symm) h
      · rw [h1, h2]
      · rw [h1, h2]; norm_num
      · exact absurd (h2.trans h1.symm) h
    have hform : ∀ m : ℕ, ∀ (hm : m < n), col ⟨m, hm⟩ = col ⟨0, by omega⟩ * (-1) ^ m := by
      intro m
      induction m with
      | zero => intro hm; simp
      | succ m ih =>
        intro hm
        rw [hstep ⟨m, by omega⟩ ⟨m + 1, hm⟩ rfl, ih (by omega), pow_succ]
        ring
    intro i j
    have hi := hform i i.2
    have hj := hform j j.2
    simp only [Fin.eta] at hi hj
    rw [hi, hj]
    have h0 : col ⟨0, by have := i.2; omega⟩ ≠ 0 := by
      rcases hcol ⟨0, by have := i.2; omega⟩ with h | h <;> rw [h] <;> norm_num
    rw [mul_right_inj' h0, neg_one_pow_eq_pow_mod_two (i : ℕ),
      neg_one_pow_eq_pow_mod_two (j : ℕ)]
    rcases Nat.mod_two_eq_zero_or_one (i : ℕ) with ha | ha <;>
      rcases Nat.mod_two_eq_zero_or_one (j : ℕ) with hb | hb <;> rw [ha, hb] <;> norm_num
  -- the number of points is odd
  have hodd : n % 2 = 1 := by
    by_contra hev
    have hn : 0 < n := Fintype.card_pos
    have hn2 : 2 ≤ n := by omega
    set a : Fin n := ⟨0, by omega⟩
    set b : Fin n := ⟨n - 1, by omega⟩
    have hab : a < b := Fin.lt_def.mpr (by simp [a, b]; omega)
    have hcab : col a ≠ col b := by
      rw [Ne, hpar]
      simp only [a, b]
      omega
    obtain ⟨k, hk⟩ := htwin a b hab.ne
    rcases lt_trichotomy k a with hka | rfl | hak
    · exact absurd (Fin.lt_def.mp hka) (by simp [a])
    · exact hk.ne_13 rfl
    · rcases lt_trichotomy k b with hkb | rfl | hbk
      · exact hcab ((hedge a k b hak hkb).mp (ThreeGraph.isEdge_comm_23.mp hk)).1
      · exact hk.ne_23 rfl
      · exact absurd (Fin.lt_def.mp hbk) (by have := k.2; simp [b]; omega)
  -- relabel by the regular polygon
  set N := n / 2 with hN
  have hnN : n = 2 * N + 1 := by omega
  let e₁ : V ≃ Fin (2 * N + 1) := e₀.trans (finCongr hnN)
  have he₁ : ∀ i : Fin (2 * N + 1), e₁.symm i = e₀.symm (Fin.cast hnN.symm i) := fun i => rfl
  have hH₀ : (circleGraph p).pullback e₁.symm =
      (twoGraph (polygonMatrix N)).pullback (halveEquiv N) := by
    apply ThreeGraph.ext_of_lt
    intro i j k hij hjk
    rw [ThreeGraph.isEdge_pullback, ThreeGraph.isEdge_pullback,
      isEdge_twoGraph (isSignMatrix_polygonMatrix N), coherent_polygonMatrix_halve hij hjk,
      he₁, he₁, he₁,
      hedge _ _ _ (Fin.lt_def.mpr (by simpa using Fin.lt_def.mp hij))
        (Fin.lt_def.mpr (by simpa using Fin.lt_def.mp hjk))]
    simp only [ne_eq, hpar, Fin.val_cast, hij.ne, hjk.ne, (hij.trans hjk).ne, not_false_eq_true,
      true_and, (halveEquiv N).injective.ne hij.ne, (halveEquiv N).injective.ne hjk.ne,
      (halveEquiv N).injective.ne (hij.trans hjk).ne]
    omega
  refine ⟨N, e₁.trans (halveEquiv N), ?_⟩
  calc circleGraph p = ((circleGraph p).pullback e₁.symm).pullback e₁ := by
        rw [ThreeGraph.pullback_pullback]
        simp [ThreeGraph.pullback_id]
    _ = (twoGraph (polygonMatrix N)).pullback (e₁.trans (halveEquiv N)) := by
        rw [hH₀, ThreeGraph.pullback_pullback]
        rfl

end TwinFree

end Grunbaum
