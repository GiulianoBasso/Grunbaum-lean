import FranklFuredi.Theorem1
import FranklFuredi.Counting

/-!
# Theorem 2

> **Theorem 2.** Suppose that `H = (V, 𝓔)`, `|V| = n ≥ 5` and any 4 points of `V` span 0 or 2
> edges.  Then `max |𝓔|` is attained exactly for `H` of the form `H_S` for some equipartition,
> i.e. `⌊n/6⌋ ≤ |Vᵢ| ≤ ⌈n/6⌉`.

We prove (`theorem2`):

1. `|𝓔| ≤ ex(n)` for every such `H`, where `ex(n)` is the number of edges of `H_S` for the
   balanced class sizes (`exS6`);
2. the bound is attained by `H_S` for an equipartition;
3. every `H` with `|𝓔| = ex(n)` is of the form `H_S` for an equipartition.

A formalisation detail worth pointing out: the converse of 3 fails for `n ≡ 3 (mod 6)`.  An
equipartition then has three classes of size `⌈n/6⌉` and three of size `⌊n/6⌋`, and `H_S` is
extremal iff the three larger classes form a triple of `S(6)` (`HS_extremal_iff`); otherwise it
has exactly one edge less (e.g. `n = 9`: `32` versus `31` edges, see `exS6_nine` and
`s6Count_bad_equipartition_nine`).

The ingredients: Theorem 1; the edge count `card_edges_HS` and the optimisation `opt_core` for
the blow-ups of `S(6)`; the bound `(n³ - n)/24` for the circle 3-graphs
(`card_edges_circleGraph`) and the comparison `(n³ - n)/24 < ex(n)` for `n ≥ 6`; for `n = 5` the
two examples coincide (`eq_HS_of_card_le_five`).
-/

open Finset

namespace FranklFuredi

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `f` is an equipartition: `⌊n/6⌋ ≤ |Vᵢ| ≤ ⌈n/6⌉` for all `i`. -/
def IsEquipartition (f : V → Fin 6) : Prop :=
  ∀ i, Fintype.card V / 6 ≤ partSizes f i ∧ partSizes f i ≤ (Fintype.card V + 5) / 6

omit [DecidableEq V] in
lemma isEquipartition_iff (f : V → Fin 6) :
    IsEquipartition f ↔ ∀ i, Fintype.card V / 6 ≤ partSizes f i ∧
      partSizes f i ≤ Fintype.card V / 6 + 1 := by
  have hs := sum_partSizes f
  simp only [Fin.sum_univ_six] at hs
  constructor
  · intro h i
    have := h i
    omega
  · intro h i
    have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3; have h4 := h 4
    have h5 := h 5
    have := h i
    refine ⟨this.1, ?_⟩
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at this ⊢ <;> omega

/-! ### The balanced partition exists -/

omit [DecidableEq V] in
theorem exists_balanced_partition :
    ∃ f : V → Fin 6, ∀ i, partSizes f i = balanced (Fintype.card V) i := by
  set n := Fintype.card V
  let e := Fintype.equivFin V
  refine ⟨fun v => ⟨((e v : Fin n) : ℕ) % 6, Nat.mod_lt _ (by norm_num)⟩, fun i => ?_⟩
  simp only [partSizes, balanced]
  have himg : (univ.filter (fun v : V =>
      (⟨((e v : Fin n) : ℕ) % 6, Nat.mod_lt _ (by norm_num)⟩ : Fin 6) = i)).image
        (fun v => ((e v : Fin n) : ℕ)) = (range n).filter (fun k => k ≡ (i : ℕ) [MOD 6]) := by
    ext k
    simp only [mem_image, mem_filter, mem_univ, true_and, mem_range, Nat.ModEq,
      Nat.mod_eq_of_lt i.isLt]
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨(e v).isLt, ?_⟩
      rw [← hv]
    · rintro ⟨hk, hmod⟩
      refine ⟨e.symm ⟨k, hk⟩, ?_, by simp⟩
      ext
      simp [hmod]
  have hinj : Function.Injective (fun v => ((e v : Fin n) : ℕ)) :=
    fun v w h => e.injective (Fin.ext h)
  rw [← card_image_of_injective _ hinj, himg, ← Nat.count_eq_card_filter_range,
    Nat.count_modEq_card n (by norm_num) (i : ℕ), Nat.mod_eq_of_lt i.isLt]

omit [DecidableEq V] in
lemma balanced_isEquipartition {f : V → Fin 6}
    (hf : ∀ i, partSizes f i = balanced (Fintype.card V) i) : IsEquipartition f := by
  rw [isEquipartition_iff]
  intro i
  rw [hf i]
  simp only [balanced]
  split_ifs <;> omega

/-! ### Comparing the two examples -/

theorem circle_le_exS6 {n : ℕ} (hn : 5 ≤ n) : (n : ℤ) ^ 3 - n ≤ 24 * exS6 n := by
  have hf := exS6_formula n
  have hq : ((n : ℕ) : ℤ) = 6 * ((n / 6 : ℕ) : ℤ) + ((n % 6 : ℕ) : ℤ) := by
    have := Nat.div_add_mod n 6
    omega
  have hr : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
  rw [hf, hq]
  generalize hqq : ((n / 6 : ℕ) : ℤ) = q
  have hq0 : 0 ≤ q := by rw [← hqq]; positivity
  have hcases : (n % 6 = 5) ∨ (1 ≤ q) := by
    by_contra h
    push Not at h
    have : n / 6 = 0 := by omega
    omega
  have hq3 : 0 ≤ q ^ 3 := pow_nonneg hq0 3
  have hq2 : 0 ≤ q ^ 2 := pow_nonneg hq0 2
  interval_cases hr' : n % 6 <;> simp [sig] <;> ring_nf <;>
    rcases hcases with h | h <;> first | omega | nlinarith

theorem circle_lt_exS6 {n : ℕ} (hn : 6 ≤ n) : (n : ℤ) ^ 3 - n < 24 * exS6 n := by
  have hf := exS6_formula n
  have hq : ((n : ℕ) : ℤ) = 6 * ((n / 6 : ℕ) : ℤ) + ((n % 6 : ℕ) : ℤ) := by
    have := Nat.div_add_mod n 6
    omega
  have hr : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have hq1 : (1 : ℤ) ≤ ((n / 6 : ℕ) : ℤ) := by
    have : 1 ≤ n / 6 := by omega
    exact_mod_cast this
  rw [hf, hq]
  generalize ((n / 6 : ℕ) : ℤ) = q at hq1 ⊢
  have hq3 : 1 ≤ q ^ 3 := one_le_pow₀ hq1
  have hq2 : 1 ≤ q ^ 2 := one_le_pow₀ hq1
  interval_cases hr' : n % 6 <;> simp [sig] <;> ring_nf <;> nlinarith

/-! ### Theorem 2 -/

/-- The extremal `H_S`: for `n ≥ 5`, `H_S` has `ex(n)` edges iff `f` is an equipartition whose
three larger classes form a triple of `S(6)` in case `n ≡ 3 (mod 6)`. -/
theorem HS_extremal_iff (hn : 5 ≤ Fintype.card V) (f : V → Fin 6) :
    (HS f).edges.card = exS6 (Fintype.card V) ↔
      IsEquipartition f ∧ (Fintype.card V % 6 = 3 →
        univ.filter (fun i => partSizes f i = Fintype.card V / 6 + 1) ∈ S6.edges) := by
  have hs := sum_partSizes f
  obtain ⟨-, h2, h3⟩ := opt_core (partSizes f)
  rw [hs] at h2 h3
  rw [card_edges_HS, isEquipartition_iff]
  constructor
  · intro h
    have hb := h2 hn h
    exact ⟨hb, (h3 hb).mp h⟩
  · rintro ⟨hb, hc⟩
    exact (h3 hb).mpr hc

/-- **Theorem 2** (Frankl–Füredi).  Let `|V| = n ≥ 5`.  Among the 3-graphs on `V` in which any
four points span 0 or 2 edges, the maximum number of edges is `ex(n)`; it is attained by `H_S`
for an equipartition, and every 3-graph attaining it is of the form `H_S` for an
equipartition. -/
theorem theorem2 (hn : 5 ≤ Fintype.card V) :
    (∀ H : ThreeGraph V, H.FourPointProperty → H.edges.card ≤ exS6 (Fintype.card V)) ∧
    (∃ f : V → Fin 6, IsEquipartition f ∧ (HS f).edges.card = exS6 (Fintype.card V)) ∧
    (∀ H : ThreeGraph V, H.FourPointProperty → H.edges.card = exS6 (Fintype.card V) →
      ∃ f : V → Fin 6, IsEquipartition f ∧ H = HS f) := by
  set n := Fintype.card V with hn_def
  -- the bound for the blow-ups of `S(6)`
  have hHS : ∀ f : V → Fin 6, (HS f).edges.card ≤ exS6 n := by
    intro f
    rw [card_edges_HS]
    have := (opt_core (partSizes f)).1
    rwa [sum_partSizes] at this
  -- extremal blow-ups are equipartitions
  have hHS_eq : ∀ f : V → Fin 6, (HS f).edges.card = exS6 n → IsEquipartition f :=
    fun f h => ((HS_extremal_iff hn f).mp h).1
  refine ⟨fun H hH => ?_, ?_, fun H hH hmax => ?_⟩
  · rcases theorem1 H hH with ⟨f, rfl⟩ | ⟨p, hp, rfl⟩
    · exact hHS f
    · have h1 := card_edges_circleGraph hp.genPos
      have h2 := circle_le_exS6 hn
      have : 24 * ((circleGraph p).edges.card : ℤ) ≤ 24 * exS6 n := le_trans h1 h2
      have : ((circleGraph p).edges.card : ℤ) ≤ exS6 n := by linarith
      exact_mod_cast this
  · obtain ⟨f, hf⟩ := exists_balanced_partition (V := V)
    refine ⟨f, balanced_isEquipartition hf, ?_⟩
    rw [card_edges_HS]
    have : partSizes f = balanced n := funext hf
    rw [this]
    rfl
  · rcases theorem1 H hH with ⟨f, rfl⟩ | ⟨p, hp, rfl⟩
    · exact ⟨f, hHS_eq f hmax, rfl⟩
    · rcases (show n = 5 ∨ 6 ≤ n by omega) with h5 | h6
      · -- for `n = 5` the two examples coincide
        obtain ⟨f, hf⟩ := eq_HS_of_card_le_five (circleGraph p)
          (circleGraph_fourPointProperty hp) (by omega)
        rw [hf] at hmax
        exact ⟨f, hHS_eq f hmax, hf⟩
      · exfalso
        have h1 := card_edges_circleGraph hp.genPos
        have h2 := circle_lt_exS6 h6
        have : ((circleGraph p).edges.card : ℤ) = exS6 n := by exact_mod_cast hmax
        linarith

/-! ### The case `n ≡ 3 (mod 6)` -/

/-- For `n = 9` the maximum is `32` … -/
theorem exS6_nine : exS6 9 = 32 := by decide

/-- … but the equipartition with class sizes `2, 2, 1, 1, 2, 1` (the three larger classes
`{0, 1, 4}` do not form a triple of `S(6)`) gives only `31` edges.  So not every equipartition
`H_S` is extremal. -/
theorem s6Count_bad_equipartition_nine : s6Count ![2, 2, 1, 1, 2, 1] = 31 := by decide

theorem not_mem_S6_014 : ({0, 1, 4} : Finset (Fin 6)) ∉ S6.edges := by decide

end FranklFuredi
