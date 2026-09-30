import FranklFuredi.Blowup

/-!
# Example 2: points on the unit circle

* `circleGraph p` : the vertices are points `p v` of the plane `ℝ × ℝ`; a triple is an edge iff
  the origin lies in the convex hull of its three points (= the triangle formed by them).
* `IsCircleConfig p` : the hypotheses of Example 2 — the points are distinct and lie on the unit
  circle, the origin is on none of the lines joining two of the points, and the origin lies in
  the convex hull of all the points.

Main results:

* `det_criterion` : if no two of `P, Q, R` are collinear with the origin, then the origin lies in
  the triangle `PQR` iff the three determinants `det(P,Q)`, `det(Q,R)`, `det(R,P)` have the same
  sign;
* `circleGraph_good` : "the fact that in this 3-graph any 4 points span 0 or 2 edges can be
  verified easily" — here via the Plücker relation between the six determinants;
* the stereographic parametrisation `stereo t = ((1-t²)/(1+t²), 2t/(1+t²))` of the unit circle,
  for which `det(stereo s, stereo t)` has the sign of `(t - s)(1 + s t)`; it is used in
  `Theorem1.lean` to realise the configurations produced by the proof.
-/

open Finset

namespace FranklFuredi

/-! ### Determinants in the plane -/

/-- The determinant `det(P, Q) = P₁ Q₂ - P₂ Q₁` of two vectors of the plane. -/
def det2 (P Q : ℝ × ℝ) : ℝ := P.1 * Q.2 - P.2 * Q.1

lemma det2_antisymm (P Q : ℝ × ℝ) : det2 Q P = -det2 P Q := by unfold det2; ring

lemma det2_self (P : ℝ × ℝ) : det2 P P = 0 := by unfold det2; ring

/-- The linear relation `det(Q,R) P + det(R,P) Q + det(P,Q) R = 0`. -/
lemma det2_identity (P Q R : ℝ × ℝ) : det2 Q R • P + det2 R P • Q + det2 P Q • R = 0 := by
  ext <;> simp [det2] <;> ring

/-- The Plücker relation between the six determinants of four vectors. -/
lemma plucker (A B C D : ℝ × ℝ) :
    det2 A B * det2 C D - det2 A C * det2 B D + det2 A D * det2 B C = 0 := by
  unfold det2; ring

lemma det2_zero_right (P : ℝ × ℝ) : det2 P 0 = 0 := by simp [det2]

lemma det2_comb (P X Y Z : ℝ × ℝ) (a b c : ℝ) :
    det2 P (a • X + b • Y + c • Z) = a * det2 P X + b * det2 P Y + c * det2 P Z := by
  simp [det2]; ring

/-! ### Triangles containing the origin -/

/-- Membership in the convex hull of three points. -/
lemma mem_convexHull_triple {P Q R X : ℝ × ℝ} :
    X ∈ convexHull ℝ ({P, Q, R} : Set (ℝ × ℝ)) ↔
      ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ a • P + b • Q + c • R = X := by
  constructor
  · intro hX
    let K : Set (ℝ × ℝ) :=
      {X | ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ a • P + b • Q + c • R = X}
    have hK : Convex ℝ K := by
      intro X hX Y hY s t hs ht hst
      obtain ⟨a, b, c, ha, hb, hc, habc, rfl⟩ := hX
      obtain ⟨a', b', c', ha', hb', hc', habc', rfl⟩ := hY
      refine ⟨s * a + t * a', s * b + t * b', s * c + t * c', by positivity, by positivity,
        by positivity, ?_, ?_⟩
      · linear_combination s * habc + t * habc' + hst
      · ext <;> simp <;> ring
    have hsub : ({P, Q, R} : Set (ℝ × ℝ)) ⊆ K := by
      intro Y hY
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hY
      rcases hY with rfl | rfl | rfl
      · exact ⟨1, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩
      · exact ⟨0, 1, 0, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩
      · exact ⟨0, 0, 1, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩
    exact convexHull_min hsub hK hX
  · rintro ⟨a, b, c, ha, hb, hc, habc, rfl⟩
    have := (convex_convexHull ℝ ({P, Q, R} : Set (ℝ × ℝ))).sum_mem (t := Finset.univ)
      (w := ![a, b, c]) (z := ![P, Q, R]) ?_ ?_ ?_
    · simpa [Fin.sum_univ_three] using this
    · intro i _
      fin_cases i <;> simp [ha, hb, hc]
    · simp [Fin.sum_univ_three, habc]
    · intro i _
      fin_cases i <;> simp <;> apply subset_convexHull <;> simp

/-- Three reals of the same (nonzero) sign. -/
def Cyc (u v w : ℝ) : Prop := (0 < u ∧ 0 < v ∧ 0 < w) ∨ (u < 0 ∧ v < 0 ∧ w < 0)

/-- **The determinant criterion.**  If no two of `P, Q, R` are collinear with the origin, the
origin lies in the triangle `PQR` iff `det(P,Q)`, `det(Q,R)`, `det(R,P)` have the same sign. -/
theorem det_criterion {P Q R : ℝ × ℝ} (h1 : det2 P Q ≠ 0) (h2 : det2 Q R ≠ 0)
    (h3 : det2 R P ≠ 0) :
    (0 : ℝ × ℝ) ∈ convexHull ℝ ({P, Q, R} : Set (ℝ × ℝ)) ↔
      Cyc (det2 P Q) (det2 Q R) (det2 R P) := by
  rw [mem_convexHull_triple]
  constructor
  · rintro ⟨a, b, c, ha, hb, hc, habc, hX⟩
    have e1 : b * det2 P Q = c * det2 R P := by
      have := congrArg (det2 P) hX
      rw [det2_comb, det2_self, det2_antisymm R P, det2_zero_right] at this
      linarith
    have e2 : c * det2 Q R = a * det2 P Q := by
      have := congrArg (det2 Q) hX
      rw [det2_comb, det2_self, det2_antisymm P Q, det2_zero_right] at this
      linarith
    have e3 : a * det2 R P = b * det2 Q R := by
      have := congrArg (det2 R) hX
      rw [det2_comb, det2_self, det2_antisymm Q R, det2_zero_right] at this
      linarith
    have ha0 : a ≠ 0 := by
      intro ha0
      rw [ha0, zero_mul] at e2
      have hc0 : c = 0 := (mul_eq_zero.mp e2).resolve_right h2
      rw [hc0, zero_mul] at e1
      have hb0 : b = 0 := (mul_eq_zero.mp e1).resolve_right h1
      rw [ha0, hb0, hc0] at habc
      norm_num at habc
    have hb0 : b ≠ 0 := by
      intro hb0
      rw [hb0, zero_mul] at e3
      have ha0' : a = 0 := (mul_eq_zero.mp e3).resolve_right h3
      exact ha0 ha0'
    have hc0 : c ≠ 0 := by
      intro hc0
      rw [hc0, zero_mul] at e1
      have hb0' : b = 0 := (mul_eq_zero.mp e1).resolve_right h1
      exact hb0 hb0'
    have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hc' : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    rcases lt_or_gt_of_ne h1 with hx | hx
    · right
      refine ⟨hx, ?_, ?_⟩
      · nlinarith
      · nlinarith
    · left
      refine ⟨hx, ?_, ?_⟩
      · nlinarith
      · nlinarith
  · intro h
    have hid := det2_identity P Q R
    have key : ∀ S : ℝ, S = det2 P Q + det2 Q R + det2 R P → S ≠ 0 →
        0 ≤ det2 Q R / S → 0 ≤ det2 R P / S → 0 ≤ det2 P Q / S →
        ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ a • P + b • Q + c • R = 0 := by
      intro S hS hS0 h1 h2 h3
      refine ⟨det2 Q R / S, det2 R P / S, det2 P Q / S, h1, h2, h3, ?_, ?_⟩
      · field_simp
        linarith
      · have : (det2 Q R / S) • P + (det2 R P / S) • Q + (det2 P Q / S) • R =
            S⁻¹ • (det2 Q R • P + det2 R P • Q + det2 P Q • R) := by
          simp only [smul_add, smul_smul, div_eq_inv_mul]
        rw [this, hid, smul_zero]
    rcases h with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
    · have hS : 0 < det2 P Q + det2 Q R + det2 R P := by linarith
      exact key _ rfl hS.ne' (div_nonneg hy.le hS.le) (div_nonneg hz.le hS.le)
        (div_nonneg hx.le hS.le)
    · have hS : det2 P Q + det2 Q R + det2 R P < 0 := by linarith
      exact key _ rfl hS.ne (div_nonneg_of_nonpos hy.le hS.le) (div_nonneg_of_nonpos hz.le hS.le)
        (div_nonneg_of_nonpos hx.le hS.le)

/-! ### The circle 3-graphs -/

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in
/-- **Example 2.**  The vertices are points `p v` of the plane; a triple is an edge iff the
origin lies in the triangle formed by its three points. -/
noncomputable def circleGraph (p : V → ℝ × ℝ) : ThreeGraph V where
  edges := (univ.powersetCard 3).filter
    (fun e => (0 : ℝ × ℝ) ∈ convexHull ℝ (p '' (e : Set V)))
  card_eq_three _ he := (mem_powersetCard.mp (mem_filter.mp he).1).2

lemma isEdge_circleGraph {p : V → ℝ × ℝ} {a b c : V} :
    (circleGraph p).IsEdge a b c ↔
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ (0 : ℝ × ℝ) ∈ convexHull ℝ ({p a, p b, p c} : Set (ℝ × ℝ)) := by
  simp only [ThreeGraph.IsEdge, circleGraph, mem_filter, mem_powersetCard, subset_univ, true_and,
    card_triple_eq_three, coe_insert, coe_singleton, Set.image_insert_eq, Set.image_singleton,
    and_assoc]

/-- The hypotheses of **Example 2**: `n` distinct points on the unit circle such that the
origin is contained in the convex hull of the points but lies on none of the lines joining two
of them. -/
structure IsCircleConfig (p : V → ℝ × ℝ) : Prop where
  injective : Function.Injective p
  on_circle : ∀ v, (p v).1 ^ 2 + (p v).2 ^ 2 = 1
  not_mem_line : ∀ v w, v ≠ w → (0 : ℝ × ℝ) ∉ line[ℝ, p v, p w]
  mem_convexHull : (0 : ℝ × ℝ) ∈ convexHull ℝ (Set.range p)

/-- General position: no two of the points are collinear with the origin. -/
def GenPos (p : V → ℝ × ℝ) : Prop := ∀ v w, v ≠ w → det2 (p v) (p w) ≠ 0

omit [Fintype V] [DecidableEq V] in
lemma IsCircleConfig.genPos {p : V → ℝ × ℝ} (hp : IsCircleConfig p) : GenPos p := by
  intro v w hvw hdet
  have hv := hp.on_circle v
  have hw := hp.on_circle w
  have hdot : ((p v).1 * (p w).1 + (p v).2 * (p w).2) ^ 2 = 1 := by
    have h : ((p v).1 * (p w).1 + (p v).2 * (p w).2) ^ 2 + (det2 (p v) (p w)) ^ 2 =
        ((p v).1 ^ 2 + (p v).2 ^ 2) * ((p w).1 ^ 2 + (p w).2 ^ 2) := by unfold det2; ring
    rw [hdet, hv, hw] at h
    linarith
  have hfac : ((p v).1 * (p w).1 + (p v).2 * (p w).2 - 1) *
      ((p v).1 * (p w).1 + (p v).2 * (p w).2 + 1) = 0 := by ring_nf; linarith
  rcases mul_eq_zero.mp hfac with h | h
  · -- the two points coincide
    apply hvw
    apply hp.injective
    have e : ((p v).1 - (p w).1) ^ 2 + ((p v).2 - (p w).2) ^ 2 = 0 := by nlinarith
    have e1 : (p v).1 - (p w).1 = 0 := by
      nlinarith [sq_nonneg ((p v).1 - (p w).1), sq_nonneg ((p v).2 - (p w).2)]
    have e2 : (p v).2 - (p w).2 = 0 := by
      nlinarith [sq_nonneg ((p v).1 - (p w).1), sq_nonneg ((p v).2 - (p w).2)]
    ext <;> linarith
  · -- the two points are antipodal, so the origin is their midpoint
    apply hp.not_mem_line v w hvw
    have e : ((p v).1 + (p w).1) ^ 2 + ((p v).2 + (p w).2) ^ 2 = 0 := by nlinarith
    have e1 : (p v).1 + (p w).1 = 0 := by
      nlinarith [sq_nonneg ((p v).1 + (p w).1), sq_nonneg ((p v).2 + (p w).2)]
    have e2 : (p v).2 + (p w).2 = 0 := by
      nlinarith [sq_nonneg ((p v).1 + (p w).1), sq_nonneg ((p v).2 + (p w).2)]
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
    refine ⟨1 / 2, ?_⟩
    rw [AffineMap.lineMap_apply]
    ext <;> simp <;> linarith

omit [Fintype V] [DecidableEq V] in
/-- Conversely, points in general position are never collinear with the origin. -/
lemma not_mem_line_of_det_ne_zero {P Q : ℝ × ℝ} (hP : P.1 ^ 2 + P.2 ^ 2 = 1)
    (h : det2 P Q ≠ 0) : (0 : ℝ × ℝ) ∉ line[ℝ, P, Q] := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  rintro ⟨r, hr⟩
  rw [AffineMap.lineMap_apply] at hr
  have h1 : r * (Q.1 - P.1) + P.1 = 0 := by simpa using congrArg Prod.fst hr
  have h2 : r * (Q.2 - P.2) + P.2 = 0 := by simpa using congrArg Prod.snd hr
  -- taking `det(P, ·)` gives `r · det(P,Q) = 0`
  have h3 : r * det2 P Q = 0 := by
    unfold det2
    have : P.1 * (r * (Q.2 - P.2) + P.2) - P.2 * (r * (Q.1 - P.1) + P.1) = 0 := by
      rw [h1, h2]; ring
    linarith
  have hr0 : r = 0 := (mul_eq_zero.mp h3).resolve_right h
  rw [hr0] at h1 h2
  simp at h1 h2
  rw [h1, h2] at hP
  norm_num at hP

/-- The edges of a circle 3-graph in general position: the triangles `abc` whose three
determinants have the same sign. -/
lemma isEdge_circleGraph_iff_cyc {p : V → ℝ × ℝ} (hp : GenPos p) {a b c : V} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) :
    (circleGraph p).IsEdge a b c ↔ Cyc (det2 (p a) (p b)) (det2 (p b) (p c)) (det2 (p c) (p a)) := by
  rw [isEdge_circleGraph, det_criterion (hp a b hab) (hp b c hbc) (hp c a (Ne.symm hac))]
  simp [hab, hac, hbc]

/-! ### The four-point property for circle 3-graphs -/

lemma lt_zero_iff_not_pos {x : ℝ} (h : x ≠ 0) : x < 0 ↔ ¬0 < x := by
  constructor
  · intro hx hx'; linarith
  · intro hx; rcases lt_or_gt_of_ne h with h | h
    · exact h
    · exact absurd h hx

lemma pos_mul_iff_of_ne {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) : 0 < x * y ↔ (0 < x ↔ 0 < y) := by
  rcases lt_or_gt_of_ne hx with hx | hx <;> rcases lt_or_gt_of_ne hy with hy | hy
  · simp [mul_pos_of_neg_of_neg hx hy, not_lt.mpr hx.le, not_lt.mpr hy.le]
  · simp [hy, not_lt.mpr hx.le, not_lt.mpr (mul_neg_of_neg_of_pos hx hy).le]
  · simp [hx, not_lt.mpr hy.le, not_lt.mpr (mul_neg_of_pos_of_neg hx hy).le]
  · simp [mul_pos hx hy, hx, hy]

lemma neg_mul_iff_of_ne {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) : x * y < 0 ↔ ¬(0 < x ↔ 0 < y) := by
  rw [← pos_mul_iff_of_ne hx hy, lt_zero_iff_not_pos (mul_ne_zero hx hy)]

/-- The sign pattern of the six determinants of four points in general position forces the
four-point condition. -/
theorem good4_of_dets {x1 x2 x3 x4 x5 x6 : ℝ} (h1 : x1 ≠ 0) (h2 : x2 ≠ 0) (h3 : x3 ≠ 0)
    (h4 : x4 ≠ 0) (h5 : x5 ≠ 0) (h6 : x6 ≠ 0) (hpl : x1 * x6 - x2 * x5 + x3 * x4 = 0) :
    ((Cyc x1 x4 (-x2) ↔ Cyc x1 x5 (-x3)) ↔ (Cyc x2 x6 (-x3) ↔ Cyc x4 x6 (-x5))) ∧
      ¬(Cyc x1 x4 (-x2) ∧ Cyc x1 x5 (-x3) ∧ Cyc x2 x6 (-x3) ∧ Cyc x4 x6 (-x5)) := by
  have C1 : ¬((0 < x1 ↔ 0 < x6) ∧ ¬(0 < x2 ↔ 0 < x5) ∧ (0 < x3 ↔ 0 < x4)) := by
    rintro ⟨e1, e2, e3⟩
    have := (pos_mul_iff_of_ne h1 h6).mpr e1
    have := (neg_mul_iff_of_ne h2 h5).mpr e2
    have := (pos_mul_iff_of_ne h3 h4).mpr e3
    linarith
  have C2 : ¬(¬(0 < x1 ↔ 0 < x6) ∧ (0 < x2 ↔ 0 < x5) ∧ ¬(0 < x3 ↔ 0 < x4)) := by
    rintro ⟨e1, e2, e3⟩
    have := (neg_mul_iff_of_ne h1 h6).mpr e1
    have := (pos_mul_iff_of_ne h2 h5).mpr e2
    have := (neg_mul_iff_of_ne h3 h4).mpr e3
    linarith
  simp only [Cyc, neg_pos, neg_lt_zero, lt_zero_iff_not_pos h1, lt_zero_iff_not_pos h2,
    lt_zero_iff_not_pos h3, lt_zero_iff_not_pos h4, lt_zero_iff_not_pos h5,
    lt_zero_iff_not_pos h6]
  by_cases p1 : 0 < x1 <;> by_cases p2 : 0 < x2 <;> by_cases p3 : 0 < x3 <;>
    by_cases p4 : 0 < x4 <;> by_cases p5 : 0 < x5 <;> by_cases p6 : 0 < x6 <;>
    simp [p1, p2, p3, p4, p5, p6] at C1 C2 ⊢

/-- "In this 3-graph any 4 points span 0 or 2 edges." -/
theorem circleGraph_good {p : V → ℝ × ℝ} (hp : GenPos p) : Good (circleGraph p).IsEdge := by
  intro a b c d hab hac had hbc hbd hcd
  unfold Good4
  rw [isEdge_circleGraph_iff_cyc hp hab hac hbc, isEdge_circleGraph_iff_cyc hp hab had hbd,
    isEdge_circleGraph_iff_cyc hp hac had hcd, isEdge_circleGraph_iff_cyc hp hbc hbd hcd,
    det2_antisymm (p a) (p c), det2_antisymm (p a) (p d), det2_antisymm (p b) (p d)]
  exact good4_of_dets (hp a b hab) (hp a c hac) (hp a d had) (hp b c hbc) (hp b d hbd)
    (hp c d hcd) (plucker _ _ _ _)

theorem circleGraph_fourPointProperty {p : V → ℝ × ℝ} (hp : IsCircleConfig p) :
    (circleGraph p).FourPointProperty :=
  ((circleGraph p).fourPointProperty_iff).mpr (circleGraph_good hp.genPos)

/-! ### The stereographic parametrisation of the unit circle -/

/-- The point of the unit circle with stereographic parameter `t`. -/
noncomputable def stereo (t : ℝ) : ℝ × ℝ := ((1 - t ^ 2) / (1 + t ^ 2), 2 * t / (1 + t ^ 2))

lemma stereo_on_circle (t : ℝ) : (stereo t).1 ^ 2 + (stereo t).2 ^ 2 = 1 := by
  have : (1 + t ^ 2) ≠ 0 := by positivity
  simp only [stereo]
  field_simp
  ring

lemma det2_stereo (s t : ℝ) :
    det2 (stereo s) (stereo t) = (t - s) * (1 + s * t) * (2 / ((1 + s ^ 2) * (1 + t ^ 2))) := by
  have hs : (1 + s ^ 2) ≠ 0 := by positivity
  have ht : (1 + t ^ 2) ≠ 0 := by positivity
  simp only [det2, stereo]
  field_simp
  ring

lemma det2_stereo_pos_iff (s t : ℝ) :
    0 < det2 (stereo s) (stereo t) ↔ 0 < (t - s) * (1 + s * t) := by
  rw [det2_stereo]
  have : 0 < 2 / ((1 + s ^ 2) * (1 + t ^ 2)) := by positivity
  exact mul_pos_iff_of_pos_right this

lemma det2_stereo_neg_iff (s t : ℝ) :
    det2 (stereo s) (stereo t) < 0 ↔ (t - s) * (1 + s * t) < 0 := by
  rw [det2_stereo]
  have : 0 < 2 / ((1 + s ^ 2) * (1 + t ^ 2)) := by positivity
  constructor
  · intro h
    by_contra h'
    push Not at h'
    have := mul_nonneg h' this.le
    linarith
  · intro h
    exact mul_neg_of_neg_of_pos h this

lemma det2_stereo_ne_zero {s t : ℝ} (hst : s ≠ t) (h : 1 + s * t ≠ 0) :
    det2 (stereo s) (stereo t) ≠ 0 := by
  rw [det2_stereo]
  have : 0 < 2 / ((1 + s ^ 2) * (1 + t ^ 2)) := by positivity
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (Ne.symm hst)) h) this.ne'

end FranklFuredi
