import FranklFuredi.Blowup

/-!
# The optimisation over the blow-ups of `S(6)`

For class sizes `x₀, …, x₅` the 3-graph `H_S` has `s6Count x = ∑_{(ijk) ∈ S(6)} xᵢ xⱼ xₖ` edges.
We determine the maximum of `s6Count x` over all `x` with `∑ xᵢ = n` and all the maximisers.
(The paper takes this for granted.)

* `exS6 n` : the value at the balanced vector `⌊n/6⌋ + [i < n mod 6]`;
* `s6Count_le` : `s6Count x ≤ exS6 n`;
* `balanced_of_s6Count_eq` : for `n ≥ 5` every maximiser is an equipartition;
* `s6Count_eq_iff_of_balanced` : an equipartition is a maximiser iff, when `n ≡ 3 (mod 6)`, the
  three larger classes form a triple of `S(6)`.  (For `n ≡ 3 (mod 6)` the other equipartitions
  have exactly one edge less — so *not every* equipartition is extremal.)

The proof combines
1. the identity `ex(n) - s6Count x = Δ q + σ(r) - C(d)` where `x = q + d`, `n = 6q + r`,
   `Δ = ∑ dᵢ(dᵢ - 1)` and `C(d) = ∑_{(ijk) ∈ S(6)} dᵢ dⱼ dₖ`;
2. the inequality `9 · s6Count x ≤ n · e₂(x)` (`stability`), a Cauchy–Schwarz inequality coming
   from the facts that every pair lies in exactly two triples of `S(6)` and every four points
   span exactly two of them;
3. a finite check for the vectors with `Δ < 4` (`pattern`).
-/

open Finset

namespace FranklFuredi

/-- The number of edges of `H_S` when the six classes have sizes `x 0, …, x 5`. -/
def s6Count (x : Fin 6 → ℕ) : ℕ :=
  x 0 * x 1 * x 2 + x 0 * x 1 * x 3 + x 2 * x 3 * x 4 + x 2 * x 3 * x 5 + x 4 * x 5 * x 0 +
    x 4 * x 5 * x 1 + x 0 * x 2 * x 4 + x 0 * x 3 * x 5 + x 1 * x 2 * x 5 + x 1 * x 3 * x 4

lemma s6Count_eq_sum (x : Fin 6 → ℕ) : s6Count x = ∑ T ∈ S6.edges, ∏ i ∈ T, x i := by
  simp +decide [s6Count, S6]
  ring

/-- The same polynomial over `ℤ`. -/
def s6Z (d : Fin 6 → ℤ) : ℤ :=
  d 0 * d 1 * d 2 + d 0 * d 1 * d 3 + d 2 * d 3 * d 4 + d 2 * d 3 * d 5 + d 4 * d 5 * d 0 +
    d 4 * d 5 * d 1 + d 0 * d 2 * d 4 + d 0 * d 3 * d 5 + d 1 * d 2 * d 5 + d 1 * d 3 * d 4

/-- `σ(r)` : the number of triples of `S(6)` inside `{0, …, r - 1}`. -/
def sig (r : ℤ) : ℤ := if r = 3 then 1 else if r = 4 then 2 else if r = 5 then 5 else 0

/-- The balanced class sizes `⌊n/6⌋ + [i < n mod 6]`. -/
def balanced (n : ℕ) (i : Fin 6) : ℕ := n / 6 + if (i : ℕ) < n % 6 then 1 else 0

/-- `ex(n)`, the number of edges of `H_S` for the balanced class sizes. -/
def exS6 (n : ℕ) : ℕ := s6Count (balanced n)

lemma sum_balanced (n : ℕ) : ∑ i, balanced n i = n := by
  have hr : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have h := Nat.div_add_mod n 6
  simp only [balanced, Fin.sum_univ_six]
  interval_cases hr' : n % 6 <;> simp <;> omega

lemma exS6_formula (n : ℕ) :
    (exS6 n : ℤ) = 10 * ((n / 6 : ℕ) : ℤ) ^ 3 + 5 * ((n % 6 : ℕ) : ℤ) * ((n / 6 : ℕ) : ℤ) ^ 2 +
      (((n % 6 : ℕ) : ℤ) ^ 2 - ((n % 6 : ℕ) : ℤ)) * ((n / 6 : ℕ) : ℤ) + sig ((n % 6 : ℕ) : ℤ) := by
  have hr : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
  simp only [exS6, balanced, s6Count]
  generalize n / 6 = q
  interval_cases hr' : n % 6 <;> simp [sig] <;> ring

/-! ### The expansion around `q` -/

lemma s6Count_expand (x : Fin 6 → ℕ) (q : ℤ) :
    (s6Count x : ℤ) = 10 * q ^ 3 + 5 * (∑ i, ((x i : ℤ) - q)) * q ^ 2 +
      ((∑ i, ((x i : ℤ) - q)) ^ 2 - ∑ i, ((x i : ℤ) - q) ^ 2) * q +
        s6Z (fun i => (x i : ℤ) - q) := by
  simp only [s6Count, s6Z, Fin.sum_univ_six]
  push_cast
  ring

/-! ### The Cauchy–Schwarz inequality `9 · s6Count x ≤ n · e₂(x)` -/

/-- `e₂(x) = ∑_{i < j} xᵢ xⱼ`. -/
def e2 (x : Fin 6 → ℕ) : ℕ :=
  x 0 * x 1 + x 0 * x 2 + x 0 * x 3 + x 0 * x 4 + x 0 * x 5 + x 1 * x 2 + x 1 * x 3 + x 1 * x 4 +
    x 1 * x 5 + x 2 * x 3 + x 2 * x 4 + x 2 * x 5 + x 3 * x 4 + x 3 * x 5 + x 4 * x 5

/-- The 15 pairs `{i, j}` of vertices of `S(6)`, each with the two vertices `k, l` such that
`ijk, ijl ∈ S(6)`. -/
def pairTab : Fin 15 → Fin 6 × Fin 6 × Fin 6 × Fin 6 :=
  ![(0, 1, 2, 3), (0, 2, 1, 4), (0, 3, 1, 5), (0, 4, 2, 5), (0, 5, 3, 4), (1, 2, 0, 5),
    (1, 3, 0, 4), (1, 4, 3, 5), (1, 5, 2, 4), (2, 3, 4, 5), (2, 4, 0, 3), (2, 5, 1, 3),
    (3, 4, 1, 2), (3, 5, 0, 2), (4, 5, 0, 1)]

theorem stability (x : Fin 6 → ℕ) : 9 * s6Count x ≤ (∑ i, x i) * e2 x := by
  let w : Fin 15 → ℕ := fun m => x (pairTab m).1 * x (pairTab m).2.1
  let c : Fin 15 → ℕ := fun m => x (pairTab m).2.2.1 + x (pairTab m).2.2.2
  have hA : ∑ m, w m * c m = 3 * s6Count x := by
    simp [w, c, pairTab, Fin.sum_univ_succ, s6Count]
    ring
  have hB : ∑ m, w m * c m ^ 2 = (∑ i, x i) * s6Count x := by
    simp [w, c, pairTab, Fin.sum_univ_succ, s6Count]
    ring
  have hW : ∑ m, w m = e2 x := by
    simp [w, pairTab, Fin.sum_univ_succ, e2]
    ring
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (s := (univ : Finset (Fin 15)))
    (r := fun m => w m * c m) (f := w) (g := fun m => w m * c m ^ 2)
    (fun _ _ => Nat.zero_le _) (fun _ _ => Nat.zero_le _) (fun m _ => le_of_eq (by ring))
  rw [hA, hW, hB] at hcs
  rcases Nat.eq_zero_or_pos (s6Count x) with h0 | hpos
  · rw [h0]; simp
  · have : 9 * s6Count x * s6Count x ≤ (∑ i, x i) * e2 x * s6Count x := by nlinarith
    exact Nat.le_of_mul_le_mul_right this hpos

lemma sq_sum_eq (x : Fin 6 → ℕ) : (∑ i, x i) ^ 2 = 2 * e2 x + ∑ i, x i ^ 2 := by
  simp only [e2, Fin.sum_univ_six]
  ring

/-! ### The finite check for the vectors close to the balanced one -/

set_option maxRecDepth 100000 in
/-- The finite check: for deviations `dᵢ ∈ {-1, 0, 1, 2}` with `0 ≤ ∑ dᵢ ≤ 5` and
`Δ = ∑ dᵢ(dᵢ - 1) < 4`. -/
theorem pattern : ∀ e0 e1 e2 e3 e4 e5 : Fin 4,
    let d : Fin 6 → ℤ := ![(e0 : ℤ) - 1, (e1 : ℤ) - 1, (e2 : ℤ) - 1, (e3 : ℤ) - 1, (e4 : ℤ) - 1,
      (e5 : ℤ) - 1]
    let r := d 0 + d 1 + d 2 + d 3 + d 4 + d 5
    let D := d 0 * (d 0 - 1) + d 1 * (d 1 - 1) + d 2 * (d 2 - 1) + d 3 * (d 3 - 1) +
      d 4 * (d 4 - 1) + d 5 * (d 5 - 1)
    0 ≤ r → r ≤ 5 → D < 4 → (D = 0 ∨ D = 2) ∧
      (D = 0 → s6Z d ≤ sig r ∧
        (s6Z d = sig r ↔ (r = 3 → (univ.filter (fun i => d i = 1)) ∈ S6.edges))) ∧
      (D = 2 → s6Z d ≤ sig r + 1 ∧ ((∀ i, 0 ≤ d i) → s6Z d ≤ sig r ∧ (r = 5 → s6Z d < 5))) := by
  decide

/-! ### The main estimate -/

section Main

variable (x : Fin 6 → ℕ)

/-- Everything about `x` in terms of `q = ⌊n/6⌋`, `r = n mod 6` and `d = x - q`. -/
theorem main_estimate :
    let n := ∑ i, x i
    let q : ℤ := ((n / 6 : ℕ) : ℤ)
    let r : ℤ := ((n % 6 : ℕ) : ℤ)
    let d : Fin 6 → ℤ := fun i => (x i : ℤ) - q
    let D : ℤ := ∑ i, d i * (d i - 1)
    (∑ i, d i = r) ∧ (0 ≤ D) ∧
      ((exS6 n : ℤ) - s6Count x = D * q + sig r - s6Z d) ∧
      (18 * ((exS6 n : ℤ) - s6Count x) ≥ (n : ℤ) * D -
        (2 * r * (6 - r) * q + r ^ 2 * (r - 1) - 18 * sig r)) := by
  intro n q r d D
  have hn : (n : ℤ) = 6 * q + r := by
    have := Nat.div_add_mod n 6
    simp only [q, r]
    omega
  have hsumd : ∑ i, d i = r := by
    simp only [d, Finset.sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    have : ((∑ i, x i : ℕ) : ℤ) = n := rfl
    rw [← Nat.cast_sum, this, hn]
    ring
  have hD0 : 0 ≤ D := by
    apply Finset.sum_nonneg
    intro i _
    rcases le_or_gt (d i) 0 with h | h
    · nlinarith
    · have : 1 ≤ d i := by omega
      nlinarith
  have hexp := s6Count_expand x q
  have hform := exS6_formula n
  have hstab := stability x
  have hsq := sq_sum_eq x
  have hsumsq : (∑ i, ((x i : ℤ)) ^ 2) = 6 * q ^ 2 + 2 * q * r + ∑ i, d i ^ 2 := by
    have : ∀ i, ((x i : ℤ)) ^ 2 = q ^ 2 + 2 * q * d i + d i ^ 2 := fun i => by
      simp only [d]; ring
    rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, hsumd]
    simp
  have hDdef : D = ∑ i, d i ^ 2 - r := by
    simp only [D, ← hsumd, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  refine ⟨hsumd, hD0, ?_, ?_⟩
  · rw [hform, hexp]
    simp only [← hsumd]
    rw [hDdef]
    simp only [d] at hsumd ⊢
    rw [hsumd]
    ring
  · -- from `9 p ≤ n e₂` and `n² = 2 e₂ + ∑ xᵢ²`
    have h1 : (18 * s6Count x : ℤ) ≤ (n : ℤ) * ((n : ℤ) ^ 2 - ∑ i, ((x i : ℤ)) ^ 2) := by
      have e1 : ((∑ i, x i : ℕ) : ℤ) ^ 2 = 2 * (e2 x : ℤ) + ∑ i, ((x i : ℤ)) ^ 2 := by
        exact_mod_cast hsq
      have e2' : (9 * s6Count x : ℤ) ≤ (n : ℤ) * (e2 x : ℤ) := by exact_mod_cast hstab
      have : ((∑ i, x i : ℕ) : ℤ) = n := rfl
      rw [this] at e1
      nlinarith
    rw [hsumsq] at h1
    rw [hform]
    rw [hDdef]
    rw [hn] at h1 ⊢
    nlinarith

end Main

end FranklFuredi

namespace FranklFuredi

lemma int_mul_pred_nonneg (z : ℤ) : 0 ≤ z * (z - 1) := by
  rcases le_or_gt z 0 with h | h
  · nlinarith
  · have : 1 ≤ z := by omega
    nlinarith

lemma int_bounds_of_mul_pred_lt (z : ℤ) (h : z * (z - 1) < 4) : -1 ≤ z ∧ z ≤ 2 := by
  constructor <;> nlinarith

lemma int_eq_zero_or_one (z : ℤ) (h : z * (z - 1) = 0) : z = 0 ∨ z = 1 := by
  rcases mul_eq_zero.mp h with h' | h'
  · exact Or.inl h'
  · exact Or.inr (by linarith)

/-- Converting the deviations into the format of `pattern`. -/
lemma pattern_apply (d : Fin 6 → ℤ) (hd : ∀ i, -1 ≤ d i ∧ d i ≤ 2) :
    0 ≤ ∑ i, d i → ∑ i, d i ≤ 5 → ∑ i, d i * (d i - 1) < 4 →
      (∑ i, d i * (d i - 1) = 0 ∨ ∑ i, d i * (d i - 1) = 2) ∧
      (∑ i, d i * (d i - 1) = 0 → s6Z d ≤ sig (∑ i, d i) ∧
        (s6Z d = sig (∑ i, d i) ↔
          (∑ i, d i = 3 → (univ.filter (fun i => d i = 1)) ∈ S6.edges))) ∧
      (∑ i, d i * (d i - 1) = 2 → s6Z d ≤ sig (∑ i, d i) + 1 ∧
        ((∀ i, 0 ≤ d i) → s6Z d ≤ sig (∑ i, d i) ∧ (∑ i, d i = 5 → s6Z d < 5))) := by
  let e : Fin 6 → Fin 4 := fun i => ⟨(d i + 1).toNat, by have := hd i; omega⟩
  have he : ∀ i, (((e i : ℕ) : ℤ) - 1) = d i := fun i => by
    have := hd i
    simp only [e]
    omega
  have hV : (![((e 0 : ℕ) : ℤ) - 1, ((e 1 : ℕ) : ℤ) - 1, ((e 2 : ℕ) : ℤ) - 1,
      ((e 3 : ℕ) : ℤ) - 1, ((e 4 : ℕ) : ℤ) - 1, ((e 5 : ℕ) : ℤ) - 1] : Fin 6 → ℤ) = d := by
    funext i
    fin_cases i <;> simp [he]
  have h := pattern (e 0) (e 1) (e 2) (e 3) (e 4) (e 5)
  dsimp only at h
  rw [hV] at h
  simp only [Fin.sum_univ_six]
  exact h

/-- **The optimisation.**  For class sizes `x` with `∑ xᵢ = n`:
`s6Count x ≤ ex(n)`; for `n ≥ 5` equality forces an equipartition; and an equipartition gives
equality iff (for `n ≡ 3 (mod 6)`) its three larger classes form a triple of `S(6)`. -/
theorem opt_core (x : Fin 6 → ℕ) :
    s6Count x ≤ exS6 (∑ i, x i) ∧
      (5 ≤ ∑ i, x i → s6Count x = exS6 (∑ i, x i) →
        ∀ i, (∑ i, x i) / 6 ≤ x i ∧ x i ≤ (∑ i, x i) / 6 + 1) ∧
      ((∀ i, (∑ i, x i) / 6 ≤ x i ∧ x i ≤ (∑ i, x i) / 6 + 1) →
        (s6Count x = exS6 (∑ i, x i) ↔ ((∑ i, x i) % 6 = 3 →
          (univ.filter (fun i => x i = (∑ i, x i) / 6 + 1)) ∈ S6.edges))) := by
  obtain ⟨hsumd, hD0, hid, hstab⟩ := main_estimate x
  set n := ∑ i, x i with hn
  set q : ℤ := ((n / 6 : ℕ) : ℤ) with hq
  set r : ℤ := ((n % 6 : ℕ) : ℤ) with hr
  set d : Fin 6 → ℤ := fun i => (x i : ℤ) - q with hd
  set D : ℤ := ∑ i, d i * (d i - 1) with hD
  have hq0 : 0 ≤ q := by positivity
  have hr0 : 0 ≤ r := by positivity
  have hr5 : r ≤ 5 := by
    have : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
    omega
  have hnqr : (n : ℤ) = 6 * q + r := by
    have := Nat.div_add_mod n 6
    omega
  have hdq : ∀ i, -q ≤ d i := fun i => by simp only [d]; have : (0 : ℤ) ≤ x i := by positivity
                                          linarith
  -- the terms of `D` are nonnegative
  have hterm : ∀ i, 0 ≤ d i * (d i - 1) := fun i => int_mul_pred_nonneg (d i)
  have hterm_le : ∀ i, d i * (d i - 1) ≤ D := fun i =>
    Finset.single_le_sum (fun j _ => hterm j) (mem_univ i)
  -- the case `D ≥ 4`
  have hbig : 4 ≤ D → (exS6 n : ℤ) - s6Count x ≥ 0 ∧ (1 ≤ n → (exS6 n : ℤ) - s6Count x > 0) := by
    intro h4
    have hnD : (n : ℤ) * 4 ≤ (n : ℤ) * D := by
      apply mul_le_mul_of_nonneg_left h4; positivity
    have hr' : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
    constructor
    · rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 by omega) with
        h | h | h | h | h | h <;> simp only [h, sig] at hstab hnqr <;> norm_num at hstab <;>
        linarith
    · intro hn1
      have hn1' : (1 : ℤ) ≤ n := by exact_mod_cast hn1
      rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 by omega) with
        h | h | h | h | h | h <;> simp only [h, sig] at hstab hnqr <;> norm_num at hstab <;>
        linarith
  -- the case `D < 4`
  have hsmall : D < 4 → (∀ i, -1 ≤ d i ∧ d i ≤ 2) := fun h4 i =>
    int_bounds_of_mul_pred_lt (d i) (lt_of_le_of_lt (hterm_le i) h4)
  have hpat := fun h4 => pattern_apply d (hsmall h4)
  rw [hsumd] at hpat
  refine ⟨?_, ?_, ?_⟩
  · -- the bound
    suffices (s6Count x : ℤ) ≤ exS6 n by exact_mod_cast this
    by_cases h4 : 4 ≤ D
    · linarith [(hbig h4).1]
    push Not at h4
    obtain ⟨hD02, hD0', hD2'⟩ := hpat h4 hr0 hr5 h4
    rcases hD02 with h | h
    · have := (hD0' h).1
      rw [show D = 0 from h] at hid
      linarith
    · have := (hD2' h).1
      rw [show D = 2 from h] at hid
      by_cases hneg : ∀ i, 0 ≤ d i
      · have := ((hD2' h).2 hneg).1
        linarith
      · push Not at hneg
        obtain ⟨i, hi⟩ := hneg
        have : 1 ≤ q := by have := hdq i; have := (hsmall h4 i).1; omega
        linarith
  · -- equality forces an equipartition
    intro h5 heq
    have heq' : (exS6 n : ℤ) - s6Count x = 0 := by rw [heq]; ring
    by_cases h4 : 4 ≤ D
    · have := (hbig h4).2 (by omega)
      linarith
    push Not at h4
    obtain ⟨hD02, hD0', hD2'⟩ := hpat h4 hr0 hr5 h4
    rcases hD02 with h | h
    · -- `D = 0`: every `dᵢ ∈ {0, 1}`
      intro i
      have hti : d i * (d i - 1) = 0 := by
        have h1 := hterm_le i
        have h2 := hterm i
        rw [show D = 0 from h] at h1
        omega
      have : d i = 0 ∨ d i = 1 := int_eq_zero_or_one (d i) hti
      simp only [d] at this
      omega
    · exfalso
      rw [show D = 2 from h] at hid
      by_cases hneg : ∀ i, 0 ≤ d i
      · obtain ⟨h1, h2⟩ := (hD2' h).2 hneg
        rcases (show q = 0 ∨ 1 ≤ q by omega) with hq0' | hq1
        · -- `q = 0`, so `n = r ≤ 5`, hence `r = 5`
          have hr5' : r = 5 := by omega
          have := h2 hr5'
          rw [hr5'] at hid
          simp only [sig] at hid
          norm_num at hid
          linarith
        · linarith
      · push Not at hneg
        obtain ⟨i, hi⟩ := hneg
        have : 1 ≤ q := by have := hdq i; have := (hsmall h4 i).1; omega
        have := (hD2' h).1
        linarith
  · -- the equipartitions
    intro hbal
    have hd01 : ∀ i, d i = 0 ∨ d i = 1 := fun i => by
      have := hbal i
      simp only [d]
      omega
    have hDz : D = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rcases hd01 i with h | h <;> simp [h]
    have h4 : D < 4 := by omega
    obtain ⟨-, hD0', -⟩ := hpat h4 hr0 hr5 h4
    obtain ⟨-, hiff⟩ := hD0' hDz
    rw [hDz] at hid
    have hfilt : (univ.filter (fun i => d i = 1)) = univ.filter (fun i => x i = n / 6 + 1) := by
      ext i
      simp only [mem_filter, mem_univ, true_and, d]
      omega
    rw [hfilt] at hiff
    have hr3 : r = 3 ↔ n % 6 = 3 := by omega
    rw [hr3] at hiff
    rw [← hiff]
    constructor
    · intro h; rw [h] at hid; linarith
    · intro h
      have : (s6Count x : ℤ) = exS6 n := by linarith
      exact_mod_cast this

end FranklFuredi
