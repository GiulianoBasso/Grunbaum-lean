/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import Grunbaum.ChalmersLewicki
import Grunbaum.TwoGraph

/-!
# Lemma B: the structure of maximizers

We prove Lemma B of the errata for `n = 2`.

> **Lemma B** (Structure of maximizers). Let `d > n` and let `(S, D)` be a maximizer of `Π(n, d)`
> with `D` positive definite. Put `M := √D S √D`, let `P ∈ 𝒫_{n,d}` be the spectral projection of
> `M` onto its `n` top eigenvectors, and write `P = UUᵗ` with rows `u₁, …, u_d ∈ ℝⁿ`. Then:
> a) `PM = MP` and `Tr(MP) = π_n(M) = Π(n, d)`;
> b) `Sgn(P) = S` and all entries of `P` are non-zero, i.e. `sᵢⱼ = sgn⟨uᵢ, uⱼ⟩ ≠ 0`; in
>    particular `uᵢ ≠ 0` for all `i`, and switching `S` at `i` corresponds to replacing `uᵢ` by
>    `-uᵢ`;
> c) `Π(n, d) = ∑ᵢⱼ √dᵢ √dⱼ |⟨uᵢ, uⱼ⟩|`;
> d) the two-graph `[S]` is `K_{n+2}`-free.

For `n = 2` we write `U = [u v]` for an orthonormal pair `u, v ∈ ℝ^ι` with
`uᵀMu + vᵀMv = π₂(M)`, for instance a pair of eigenvectors for the two largest eigenvalues
(`Grunbaum.exists_fanValue_eq_sumTopTwo`). The rows of `U` are the vectors
`xᵢ = (uᵢ, vᵢ) ∈ ℝ²` (the `uᵢ` of the errata), and `P = uuᵀ + vvᵀ = Grunbaum.projPair u v` has
the entries `Pᵢⱼ = ⟨xᵢ, xⱼ⟩ = uᵢuⱼ + vᵢvⱼ`.

## Main results

* (a) `Grunbaum.mul_projPair_comm`, `Grunbaum.trace_mul_projPair`;
* (b) `Grunbaum.mul_projPair_pos` : `0 < sᵢⱼ ⟨xᵢ, xⱼ⟩` for all `i, j`. This is
  [AMOP, Lemma 3.2]: first `S` maximizes `S' ↦ π₂(√D S' √D)` also over the matrices with entries
  in `[-1, 1]` (flip one pair of entries), and then a vanishing entry of `P` would force `P` to be
  a multiple of the identity;
* switching: `Grunbaum.IsMaximizer.switch`, `Grunbaum.fanValue_switch`;
* (c) `Grunbaum.sumTopTwo_eq_sum_abs`;
* (d) `Grunbaum.k4Free_of_mul_projPair_pos` : four vectors in the plane cannot be pairwise obtuse.

## References

* [AMOP] G. Basso, *Almost minimal orthogonal projections*, Israel J. Math. 243 (2021).
* [JFA] G. Basso, *Computation of maximal projection constants*, J. Funct. Anal. 277 (2019).

This file is adapted from `ProjectionConstants/Grunbaum/{SignPattern,TwoGraph}.lean` of the
library *Projection constants in Lean*.
-/

open Finset Matrix

namespace Grunbaum

variable {ι : Type*} [Fintype ι]

/-! ### Linearity of `fanValue` -/

lemma fanValue_add (A B : Matrix ι ι ℝ) (x y : ι → ℝ) :
    fanValue (A + B) x y = fanValue A x y + fanValue B x y := by
  simp only [fanValue, add_mulVec, dotProduct_add]
  ring

lemma fanValue_smul (c : ℝ) (A : Matrix ι ι ℝ) (x y : ι → ℝ) :
    fanValue (c • A) x y = c * fanValue A x y := by
  simp only [fanValue, smul_mulVec, dotProduct_smul, smul_eq_mul]
  ring

/-- Coefficients of a vector in the plane of an orthonormal pair are inner products. -/
lemma eq_smul_add_smul_of_isOrthonormalPair {u v z : ι → ℝ} (huv : IsOrthonormalPair u v)
    {a b : ℝ} (hz : z = a • u + b • v) : z = (u ⬝ᵥ z) • u + (v ⬝ᵥ z) • v := by
  have ha : u ⬝ᵥ z = a := by
    rw [hz, dotProduct_add, dotProduct_smul, dotProduct_smul, huv.norm_left, huv.orth]
    simp
  have hb : v ⬝ᵥ z = b := by
    rw [hz, dotProduct_add, dotProduct_smul, dotProduct_smul, dotProduct_comm v u, huv.orth,
      huv.norm_right]
    simp
  rw [ha, hb]
  exact hz

/-! ### Lemma B(a) -/

/-- **Lemma B(a)**, commutation: if `u, v` maximizes `xᵀAx + yᵀAy`, then `P = uuᵀ + vvᵀ`
commutes with `A`. -/
theorem mul_projPair_comm {A : Matrix ι ι ℝ} (hA : ∀ i j, A j i = A i j) {u v : ι → ℝ}
    (huv : IsOrthonormalPair u v)
    (hmax : ∀ x y, IsOrthonormalPair x y → fanValue A x y ≤ fanValue A u v) :
    A * projPair u v = projPair u v * A := by
  have hu := mulVec_eq_of_isMax hA huv hmax
  have hv := mulVec_eq_of_isMax' hA huv hmax
  have hsym : v ⬝ᵥ (A *ᵥ u) = u ⬝ᵥ (A *ᵥ v) := dotProduct_mulVec_comm hA v u
  ext i j
  have e1 : (A * projPair u v) i j = (A *ᵥ u) i * u j + (A *ᵥ v) i * v j := by
    simp only [mul_apply, projPair_apply, mulVec, dotProduct, sum_mul, ← sum_add_distrib]
    exact sum_congr rfl fun k _ => by ring
  have e2 : (projPair u v * A) i j = u i * (A *ᵥ u) j + v i * (A *ᵥ v) j := by
    simp only [mul_apply, projPair_apply, mulVec, dotProduct, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun k _ => by rw [hA k j]; ring
  rw [e1, e2, hu, hv]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsym]
  ring

/-- **Lemma B(a)**, trace: `Tr(AP) = uᵀAu + vᵀAv`. -/
theorem trace_mul_projPair (A : Matrix ι ι ℝ) (u v : ι → ℝ) :
    (A * projPair u v).trace = fanValue A u v := by
  rw [fanValue_eq_sum]
  simp only [trace, diag_apply, mul_apply, projPair_apply]
  exact sum_congr rfl fun i _ => sum_congr rfl fun k _ => by ring

/-! ### Flipping one pair of entries -/

section Flip

variable [DecidableEq ι]

/-- The symmetric matrix `Eᵢⱼ + Eⱼᵢ`. -/
def symE (i j : ι) : Matrix ι ι ℝ :=
  of fun k l => (if k = i ∧ l = j then 1 else 0) + (if k = j ∧ l = i then 1 else 0)

omit [Fintype ι] in
lemma symE_symm (i j k l : ι) : symE i j l k = symE i j k l := by
  simp only [symE, of_apply, @and_comm (l = i) (k = j), @and_comm (l = j) (k = i)]
  ring

lemma mulVec_symE (i j : ι) (x : ι → ℝ) (k : ι) :
    (symE i j *ᵥ x) k = (if k = i then x j else 0) + (if k = j then x i else 0) := by
  simp only [mulVec, dotProduct, symE, of_apply, add_mul, sum_add_distrib, ite_mul, one_mul,
    zero_mul]
  congr 1
  · by_cases hk : k = i <;> simp [hk]
  · by_cases hk : k = j <;> simp [hk]

lemma dotProduct_mulVec_symE (i j : ι) (x : ι → ℝ) : x ⬝ᵥ (symE i j *ᵥ x) = 2 * (x i * x j) := by
  simp only [dotProduct, mulVec_symE, mul_add, sum_add_distrib, mul_ite, mul_zero,
    Finset.sum_ite_eq', mem_univ, ite_true]
  ring

lemma fanValue_symE (i j : ι) (x y : ι → ℝ) :
    fanValue (symE i j) x y = 2 * (x i * x j + y i * y j) := by
  simp only [fanValue, dotProduct_mulVec_symE]
  ring

/-- `S` with the two entries `(i, j)` and `(j, i)` replaced by `t`. -/
def updateSymm (S : Matrix ι ι ℝ) (i j : ι) (t : ℝ) : Matrix ι ι ℝ :=
  of fun k l => if (k = i ∧ l = j) ∨ (k = j ∧ l = i) then t else S k l

omit [Fintype ι] in
lemma IsSignMatrix.updateSymm {S : Matrix ι ι ℝ} (hS : IsSignMatrix S) {i j : ι} (hij : i ≠ j)
    {t : ℝ} (ht : t = 1 ∨ t = -1) : IsSignMatrix (Grunbaum.updateSymm S i j t) := by
  refine ⟨fun k l => ?_, fun k l => ?_, fun k => ?_⟩
  · simp only [Grunbaum.updateSymm, of_apply]
    by_cases h : (k = i ∧ l = j) ∨ (k = j ∧ l = i)
    · have h' : (l = i ∧ k = j) ∨ (l = j ∧ k = i) := by tauto
      rw [ite_eq_left h, ite_eq_left h']
    · have h' : ¬((l = i ∧ k = j) ∨ (l = j ∧ k = i)) := by tauto
      rw [ite_eq_right h, ite_eq_right h', hS.symm]
  · simp only [Grunbaum.updateSymm, of_apply]
    split_ifs
    · exact ht
    · exact hS.sign k l
  · simp only [Grunbaum.updateSymm, of_apply]
    have : ¬((k = i ∧ k = j) ∨ (k = j ∧ k = i)) := by
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact hij rfl
    rw [ite_eq_right this, hS.diag]

omit [Fintype ι] in
lemma weightedMatrix_updateSymm {S : Matrix ι ι ℝ} (hS : IsSignMatrix S) {i j : ι} (hij : i ≠ j)
    (t : ℝ) (w : ι → ℝ) :
    weightedMatrix (updateSymm S i j t) w =
      weightedMatrix S w + ((t - S i j) * (√(w i) * √(w j))) • symE i j := by
  ext k l
  simp only [weightedMatrix, updateSymm, symE, of_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  by_cases h1 : k = i ∧ l = j
  · obtain ⟨rfl, rfl⟩ := h1
    have h2 : ¬(k = l ∧ l = k) := fun h => hij h.1
    simp [h2]
    ring
  · by_cases h2 : k = j ∧ l = i
    · obtain ⟨rfl, rfl⟩ := h2
      have h1' : ¬(k = l ∧ l = k) := fun h => hij h.2
      simp [h1', hS.symm]
      ring
    · simp [h1, h2]

end Flip

/-! ### Lemma B(b): the sign pattern of a maximizer -/

/-- `S` maximizes `S' ↦ π₂(√D S' √D)` over `𝒜`, for fixed weights `D`. -/
def IsSignMaximizer (S : Matrix ι ι ℝ) (w : ι → ℝ) : Prop :=
  ∀ S', IsSignMatrix S' → π₂ (weightedMatrix S' w) ≤ π₂ (weightedMatrix S w)

lemma IsMaximizer.isSignMaximizer {S : Matrix ι ι ℝ} {w : ι → ℝ} (h : IsMaximizer S w) :
    IsSignMaximizer S w :=
  fun S' hS' => h.le S' w hS' h.isWeight

section SignPattern

variable [DecidableEq ι] {S : Matrix ι ι ℝ} {w : ι → ℝ} {u v : ι → ℝ}

omit [DecidableEq ι] in
/-- At a maximizer, `sᵢⱼ ⟨xᵢ, xⱼ⟩ ≥ 0`: otherwise flipping the sign of `sᵢⱼ` would increase
`uᵀMu + vᵀMv`. -/
theorem mul_projPair_nonneg (hS : IsSignMatrix S) (hpos : ∀ i, 0 < w i)
    (hmax : IsSignMaximizer S w) (huv : IsOrthonormalPair u v)
    (hval : fanValue (weightedMatrix S w) u v = π₂ (weightedMatrix S w)) {i j : ι}
    (hij : i ≠ j) : 0 ≤ S i j * (u i * u j + v i * v j) := by
  classical
  have hS' := hS.updateSymm hij (t := -S i j) (by rcases hS.sign i j with h | h <;> simp [h])
  have h1 := weightedMatrix_updateSymm hS hij (-S i j) w
  have h2 : fanValue (weightedMatrix (updateSymm S i j (-S i j)) w) u v ≤
      fanValue (weightedMatrix S w) u v :=
    (fanValue_le_sumTopTwo _ huv).trans ((hmax _ hS').trans hval.ge)
  rw [h1, fanValue_add, fanValue_smul, fanValue_symE] at h2
  have hw : 0 < √(w i) * √(w j) := mul_pos (Real.sqrt_pos.2 (hpos i)) (Real.sqrt_pos.2 (hpos j))
  have h3 : 0 ≤ (S i j * (u i * u j + v i * v j)) * (4 * (√(w i) * √(w j))) := by nlinarith
  exact nonneg_of_mul_nonneg_left h3 (by positivity)

/-- At a maximizer, a vanishing entry `Pᵢⱼ = 0` forces the plane of `u, v` to be invariant under
`Eᵢⱼ + Eⱼᵢ`: the pair `u, v` is then also a maximizing pair for the average of the two matrices
obtained by setting `sᵢⱼ = ±1`. -/
theorem mulVec_symE_eq (hS : IsSignMatrix S) (hpos : ∀ i, 0 < w i)
    (hmax : IsSignMaximizer S w) (huv : IsOrthonormalPair u v)
    (hval : fanValue (weightedMatrix S w) u v = π₂ (weightedMatrix S w)) {i j : ι}
    (hij : i ≠ j) (hp : u i * u j + v i * v j = 0) :
    symE i j *ᵥ u = (u ⬝ᵥ (symE i j *ᵥ u)) • u + (v ⬝ᵥ (symE i j *ᵥ u)) • v ∧
      symE i j *ᵥ v = (u ⬝ᵥ (symE i j *ᵥ v)) • u + (v ⬝ᵥ (symE i j *ᵥ v)) • v := by
  set M := weightedMatrix S w with hM
  set c : ℝ := S i j * (√(w i) * √(w j)) with hc
  have hc0 : c ≠ 0 := by
    have hw : 0 < √(w i) * √(w j) :=
      mul_pos (Real.sqrt_pos.2 (hpos i)) (Real.sqrt_pos.2 (hpos j))
    rcases hS.sign i j with h | h <;> rw [hc, h] <;> nlinarith
  set A₀ : Matrix ι ι ℝ := M - c • symE i j with hA₀
  have hMs : ∀ k l, M l k = M k l := fun k l => weightedMatrix_symm hS w k l
  have hA₀s : ∀ k l, A₀ l k = A₀ k l := by
    intro k l
    simp only [hA₀, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, hMs k l, symE_symm]
  -- `(u, v)` maximizes `fanValue M`
  have hmaxM : ∀ x y, IsOrthonormalPair x y → fanValue M x y ≤ fanValue M u v :=
    fun x y hxy => hval ▸ fanValue_le_sumTopTwo M hxy
  -- `(u, v)` maximizes `fanValue A₀`, since `A₀` is the average of two flips of `M`
  have hmaxA : ∀ x y, IsOrthonormalPair x y → fanValue A₀ x y ≤ fanValue A₀ u v := by
    intro x y hxy
    have h1 : fanValue (weightedMatrix (updateSymm S i j 1) w) x y ≤ fanValue M u v :=
      (fanValue_le_sumTopTwo _ hxy).trans
        ((hmax _ (hS.updateSymm hij (Or.inl rfl))).trans hval.ge)
    have h2 : fanValue (weightedMatrix (updateSymm S i j (-1)) w) x y ≤ fanValue M u v :=
      (fanValue_le_sumTopTwo _ hxy).trans
        ((hmax _ (hS.updateSymm hij (Or.inr rfl))).trans hval.ge)
    rw [weightedMatrix_updateSymm hS hij, fanValue_add, fanValue_smul] at h1 h2
    have hx : fanValue A₀ x y = fanValue M x y - c * fanValue (symE i j) x y := by
      rw [hA₀, sub_eq_add_neg, ← neg_smul, fanValue_add, fanValue_smul]
      ring
    have hu : fanValue A₀ u v = fanValue M u v := by
      rw [hA₀, sub_eq_add_neg, ← neg_smul, fanValue_add, fanValue_smul, fanValue_symE, hp]
      ring
    rw [hx, hu, hc]
    linarith
  have hinvM := mulVec_eq_of_isMax hMs huv hmaxM
  have hinvM' := mulVec_eq_of_isMax' hMs huv hmaxM
  have hinvA := mulVec_eq_of_isMax hA₀s huv hmaxA
  have hinvA' := mulVec_eq_of_isMax' hA₀s huv hmaxA
  -- `Eᵢⱼ + Eⱼᵢ = (M - A₀) / c`
  have hdiff : ∀ x, symE i j *ᵥ x = c⁻¹ • (M *ᵥ x - A₀ *ᵥ x) := by
    intro x
    rw [hA₀, sub_mulVec, smul_mulVec, sub_sub_cancel, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  constructor
  · refine eq_smul_add_smul_of_isOrthonormalPair huv
      (a := c⁻¹ * (u ⬝ᵥ (M *ᵥ u) - u ⬝ᵥ (A₀ *ᵥ u)))
      (b := c⁻¹ * (v ⬝ᵥ (M *ᵥ u) - v ⬝ᵥ (A₀ *ᵥ u))) ?_
    rw [hdiff]
    conv_lhs => rw [hinvM, hinvA]
    ext k
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    ring
  · refine eq_smul_add_smul_of_isOrthonormalPair huv
      (a := c⁻¹ * (u ⬝ᵥ (M *ᵥ v) - u ⬝ᵥ (A₀ *ᵥ v)))
      (b := c⁻¹ * (v ⬝ᵥ (M *ᵥ v) - v ⬝ᵥ (A₀ *ᵥ v))) ?_
    rw [hdiff]
    conv_lhs => rw [hinvM', hinvA']
    ext k
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    ring

omit [DecidableEq ι] in
/-- Consequences of a vanishing off-diagonal entry `Pᵢⱼ = 0` at a maximizer: `Pᵢᵢ = Pⱼⱼ`, and
the rows `i` and `j` of `P` vanish off the diagonal. -/
theorem projPair_eq_zero_consequences (hS : IsSignMatrix S) (hpos : ∀ i, 0 < w i)
    (hmax : IsSignMaximizer S w) (huv : IsOrthonormalPair u v)
    (hval : fanValue (weightedMatrix S w) u v = π₂ (weightedMatrix S w)) {i j : ι}
    (hij : i ≠ j) (hp : u i * u j + v i * v j = 0) :
    u i * u i + v i * v i = u j * u j + v j * v j ∧
      ∀ l, l ≠ i → l ≠ j → u i * u l + v i * v l = 0 ∧ u j * u l + v j * v l = 0 := by
  classical
  obtain ⟨ha, hb⟩ := mulVec_symE_eq hS hpos hmax huv hval hij hp
  -- the symmetry `⟨v, E u⟩ = ⟨u, E v⟩`
  have hsym : v ⬝ᵥ (symE i j *ᵥ u) = u ⬝ᵥ (symE i j *ᵥ v) :=
    dotProduct_mulVec_comm (symE_symm i j) v u
  -- `aₖ uₗ + bₖ vₗ = aₗ uₖ + bₗ vₖ` for `a = E u` and `b = E v`
  have key : ∀ k l, (symE i j *ᵥ u) k * u l + (symE i j *ᵥ v) k * v l
      = (symE i j *ᵥ u) l * u k + (symE i j *ᵥ v) l * v k := by
    intro k l
    rw [ha, hb]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hsym]
    ring
  have hji : j ≠ i := Ne.symm hij
  refine ⟨?_, fun l hli hlj => ⟨?_, ?_⟩⟩
  · have := key i j
    simp [mulVec_symE, hij, hji] at this
    linarith
  · have := key j l
    simp [mulVec_symE, hji, hli, hlj] at this
    linarith
  · have := key i l
    simp [mulVec_symE, hij, hli, hlj] at this
    linarith

omit [DecidableEq ι] in
/-- `∑ₖₗ Pₖₗ² = 2` for `P = uuᵀ + vvᵀ` and an orthonormal pair `u, v`. -/
lemma sum_sq_projPair (huv : IsOrthonormalPair u v) :
    ∑ k, ∑ l, (u k * u l + v k * v l) ^ 2 = 2 := by
  have h1 : ∑ l, u l * u l = 1 := huv.norm_left
  have h2 : ∑ l, v l * v l = 1 := huv.norm_right
  have h3 : ∑ l, u l * v l = 0 := huv.orth
  have e : ∀ k, ∑ l, (u k * u l + v k * v l) ^ 2 = u k * u k + v k * v k := by
    intro k
    have : ∑ l, (u k * u l + v k * v l) ^ 2 = u k * u k * (∑ l, u l * u l)
        + 2 * (u k * v k) * (∑ l, u l * v l) + v k * v k * (∑ l, v l * v l) := by
      simp only [mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun l _ => by ring
    rw [this, h1, h2, h3]
    ring
  rw [sum_congr rfl fun k _ => e k, sum_add_distrib, h1, h2]
  norm_num

omit [DecidableEq ι] in
/-- **Lemma B(b)** ([AMOP, Lemma 3.2]). Let `|ι| > 2`, let `D` be positive definite and let `S`
maximize `S' ↦ π₂(√D S' √D)`. If `u, v` is an orthonormal pair with `uᵀMu + vᵀMv = π₂(M)` for
`M = √D S √D`, then `sᵢⱼ ⟨xᵢ, xⱼ⟩ > 0` for all `i, j`, where `xᵢ = (uᵢ, vᵢ)`. That is,
`sᵢⱼ = sgn⟨xᵢ, xⱼ⟩ ≠ 0`. -/
theorem mul_projPair_pos (hS : IsSignMatrix S) (hpos : ∀ i, 0 < w i)
    (h3 : 2 < Fintype.card ι) (hmax : IsSignMaximizer S w) (huv : IsOrthonormalPair u v)
    (hval : fanValue (weightedMatrix S w) u v = π₂ (weightedMatrix S w)) (i j : ι) :
    0 < S i j * (u i * u j + v i * v j) := by
  -- first: no off-diagonal entry of `P` vanishes
  have hoff : ∀ i j, i ≠ j → u i * u j + v i * v j ≠ 0 := by
    intro i₀ j₀ hij₀ hp₀
    obtain ⟨-, hrow⟩ := projPair_eq_zero_consequences hS hpos hmax huv hval hij₀ hp₀
    -- the row `i₀` vanishes off the diagonal
    have hrow0 : ∀ l, l ≠ i₀ → u i₀ * u l + v i₀ * v l = 0 := by
      intro l hl
      by_cases hlj : l = j₀
      · subst hlj; exact hp₀
      · exact (hrow l hl hlj).1
    -- hence `P = c 𝟙`
    set c := u i₀ * u i₀ + v i₀ * v i₀ with hc
    have hdiag : ∀ l, u l * u l + v l * v l = c := by
      intro l
      by_cases hl : l = i₀
      · subst hl; rfl
      · exact ((projPair_eq_zero_consequences hS hpos hmax huv hval (Ne.symm hl)
          (hrow0 l hl)).1).symm
    have hoffall : ∀ k l, k ≠ l → u k * u l + v k * v l = 0 := by
      intro k l hkl
      by_cases hk : k = i₀
      · subst hk; exact hrow0 l (Ne.symm hkl)
      · by_cases hl : l = i₀
        · subst hl
          have := hrow0 k hk
          linarith [mul_comm (u l) (u k), mul_comm (v l) (v k)]
        · exact ((projPair_eq_zero_consequences hS hpos hmax huv hval (Ne.symm hk)
            (hrow0 k hk)).2 l hl (Ne.symm hkl)).2
    -- the trace of `P` is `2` and so is `∑ₖₗ Pₖₗ²`
    have htr : ∑ k, (u k * u k + v k * v k) = 2 := by
      rw [sum_add_distrib]
      have h1 : ∑ k, u k * u k = 1 := huv.norm_left
      have h2 : ∑ k, v k * v k = 1 := huv.norm_right
      rw [h1, h2]
      norm_num
    have hfr := sum_sq_projPair huv
    have hfr' : ∑ k, ∑ l, (u k * u l + v k * v l) ^ 2 = ∑ _k : ι, c ^ 2 := by
      refine sum_congr rfl fun k _ => ?_
      rw [Fintype.sum_eq_single k]
      · rw [hdiag k]
      · intro l hl
        rw [hoffall k l (Ne.symm hl)]
        ring
    simp only [hdiag, sum_const, card_univ, nsmul_eq_mul] at htr hfr'
    rw [hfr'] at hfr
    have hc1 : c = 1 := by
      have hc0 : c ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at htr
        norm_num at htr
      have : (Fintype.card ι : ℝ) * c * (c - 1) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · have : (0 : ℝ) < Fintype.card ι := by exact_mod_cast (by omega : 0 < Fintype.card ι)
          linarith
        · exact absurd h' hc0
      · linarith
    rw [hc1, mul_one] at htr
    have : Fintype.card ι = 2 := by exact_mod_cast htr
    omega
  -- second: no diagonal entry of `P` vanishes
  have hdiag : ∀ i, u i * u i + v i * v i ≠ 0 := by
    intro i hi
    obtain ⟨l, hl⟩ : ∃ l, l ≠ i := by
      by_contra hcon
      push Not at hcon
      have : Fintype.card ι ≤ 1 :=
        Fintype.card_le_one_iff.mpr fun a b => (hcon a).trans (hcon b).symm
      omega
    apply hoff i l (Ne.symm hl)
    have hcs : (u i * u l + v i * v l) ^ 2 ≤
        (u i * u i + v i * v i) * (u l * u l + v l * v l) := by
      nlinarith [sq_nonneg (u i * v l - v i * u l)]
    rw [hi, zero_mul] at hcs
    exact pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm hcs (sq_nonneg _))
  by_cases hij : i = j
  · subst hij
    rw [hS.diag, one_mul]
    exact lt_of_le_of_ne (by nlinarith [mul_self_nonneg (u i), mul_self_nonneg (v i)])
      (Ne.symm (hdiag i))
  · have h0 := mul_projPair_nonneg hS hpos hmax huv hval hij
    have hne : S i j * (u i * u j + v i * v j) ≠ 0 := by
      intro h0
      apply hoff i j hij
      rcases hS.sign i j with h | h <;> rw [h] at h0 <;> linarith
    exact lt_of_le_of_ne h0 (Ne.symm hne)

omit [DecidableEq ι] in
/-- **Lemma B(b)** for maximizers of `Π(2, ι)`. -/
theorem IsMaximizer.mul_projPair_pos (hmax : IsMaximizer S w) (hpos : ∀ i, 0 < w i)
    (h3 : 2 < Fintype.card ι) (huv : IsOrthonormalPair u v)
    (hval : fanValue (weightedMatrix S w) u v = π₂ (weightedMatrix S w)) (i j : ι) :
    0 < S i j * (u i * u j + v i * v j) :=
  Grunbaum.mul_projPair_pos hmax.isSignMatrix hpos h3 hmax.isSignMaximizer huv hval i j

end SignPattern

omit [Fintype ι] in
/-- If `0 < sᵢⱼ Pᵢⱼ` then `sᵢⱼ Pᵢⱼ = |Pᵢⱼ|`. -/
lemma mul_eq_abs_of_pos {S : Matrix ι ι ℝ} (hS : IsSignMatrix S) {P : Matrix ι ι ℝ} {i j : ι}
    (h : 0 < S i j * P i j) : S i j * P i j = |P i j| := by
  rw [← abs_of_pos h, abs_mul, hS.abs_apply, one_mul]

/-! ### Switching -/

section Switch

variable {S : Matrix ι ι ℝ} {ε : ι → ℝ}

omit [Fintype ι] in
lemma weightedMatrix_switch (S : Matrix ι ι ℝ) (ε w : ι → ℝ) :
    weightedMatrix (switch S ε) w = switch (weightedMatrix S w) ε := by
  ext i j
  simp only [weightedMatrix, switch, of_apply]
  ring

/-- Switching `A` at the indices with `εᵢ = -1` corresponds to replacing `xᵢ` by `-xᵢ`. -/
lemma fanValue_switch (hε : IsSignVector ε) (A : Matrix ι ι ℝ) (x y : ι → ℝ) :
    fanValue (switch A ε) (ε * x) (ε * y) = fanValue A x y := by
  simp only [fanValue_eq_sum, switch, of_apply, Pi.mul_apply]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  linear_combination (A i j * (x i * x j + y i * y j) * (ε j * ε j)) * hε.mul_self i
    + A i j * (x i * x j + y i * y j) * hε.mul_self j

lemma IsOrthonormalPair.mul_left (hε : IsSignVector ε) {x y : ι → ℝ}
    (h : IsOrthonormalPair x y) : IsOrthonormalPair (ε * x) (ε * y) := by
  have e : ∀ a b : ι → ℝ, (ε * a) ⬝ᵥ (ε * b) = a ⬝ᵥ b := by
    intro a b
    simp only [dotProduct, Pi.mul_apply]
    exact sum_congr rfl fun i _ => by linear_combination (a i * b i) * hε.mul_self i
  exact ⟨by rw [e]; exact h.norm_left, by rw [e]; exact h.norm_right, by rw [e]; exact h.orth⟩

omit [Fintype ι] in
lemma mul_mul_cancel_left (hε : IsSignVector ε) (x : ι → ℝ) : ε * (ε * x) = x := by
  ext i
  simp only [Pi.mul_apply]
  linear_combination x i * hε.mul_self i

/-- Switching does not change `π₂`. -/
theorem sumTopTwo_switch (hε : IsSignVector ε) (A : Matrix ι ι ℝ) : π₂ (switch A ε) = π₂ A := by
  have hset : fanValues (switch A ε) = fanValues A := by
    ext t
    constructor
    · rintro ⟨x, y, h, rfl⟩
      refine ⟨ε * x, ε * y, h.mul_left hε, ?_⟩
      rw [← fanValue_switch hε A (ε * x) (ε * y), mul_mul_cancel_left hε,
        mul_mul_cancel_left hε]
    · rintro ⟨x, y, h, rfl⟩
      exact ⟨ε * x, ε * y, h.mul_left hε, fanValue_switch hε A x y⟩
  rw [sumTopTwo, sumTopTwo, hset]

/-- Switching a maximizer gives a maximizer. -/
theorem IsMaximizer.switch {w : ι → ℝ} (h : IsMaximizer S w) (hε : IsSignVector ε) :
    IsMaximizer (switch S ε) w := by
  refine isMaximizer_of_le (h.isSignMatrix.switch hε) h.isWeight ?_
  rw [weightedMatrix_switch, sumTopTwo_switch hε, h.sumTopTwo_eq]

end Switch

/-! ### Lemma B(c) -/

/-- **Lemma B(c)**: `π₂(M) = ∑ᵢⱼ √dᵢ √dⱼ |⟨xᵢ, xⱼ⟩|`. -/
theorem sumTopTwo_eq_sum_abs {S : Matrix ι ι ℝ} {w u v : ι → ℝ} (hS : IsSignMatrix S)
    (hval : fanValue (weightedMatrix S w) u v = π₂ (weightedMatrix S w))
    (hsign : ∀ i j, 0 < S i j * (u i * u j + v i * v j)) :
    π₂ (weightedMatrix S w) = ∑ i, ∑ j, √(w i) * √(w j) * |u i * u j + v i * v j| := by
  rw [← hval, fanValue_eq_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  have := mul_eq_abs_of_pos hS (P := projPair u v) (hsign i j)
  simp only [projPair_apply] at this
  rw [← this, weightedMatrix_apply]
  ring

/-! ### Lemma B(d) -/

/-- Four vectors in the plane cannot be pairwise obtuse. -/
lemma no_four_pairwise_obtuse (x0 y0 x1 y1 x2 y2 x3 y3 : ℝ) (h01 : x0 * x1 + y0 * y1 < 0)
    (h02 : x0 * x2 + y0 * y2 < 0) (h03 : x0 * x3 + y0 * y3 < 0) (h12 : x1 * x2 + y1 * y2 < 0)
    (h13 : x1 * x3 + y1 * y3 < 0) (h23 : x2 * x3 + y2 * y3 < 0) : False := by
  have hr : 0 < x0 ^ 2 + y0 ^ 2 := by
    by_contra hcon
    have hx : x0 = 0 := by nlinarith [sq_nonneg x0, sq_nonneg y0]
    have hy : y0 = 0 := by nlinarith [sq_nonneg x0, sq_nonneg y0]
    rw [hx, hy] at h01
    linarith
  -- `aₘ = ⟨xₘ, x₀⟩ < 0` and `bₘ = det(x₀, xₘ)`; then `|x₀|² ⟨xₘ, xₘ'⟩ = aₘ aₘ' + bₘ bₘ'`
  have key : ∀ xa ya xb yb : ℝ, xa * x0 + ya * y0 < 0 → xb * x0 + yb * y0 < 0 →
      xa * xb + ya * yb < 0 → (x0 * ya - y0 * xa) * (x0 * yb - y0 * xb) < 0 := by
    intro xa ya xb yb ha hb hab
    have lag : (xa * xb + ya * yb) * (x0 ^ 2 + y0 ^ 2) = (xa * x0 + ya * y0) * (xb * x0 + yb * y0)
        + (x0 * ya - y0 * xa) * (x0 * yb - y0 * xb) := by
      ring
    have h1 : (xa * xb + ya * yb) * (x0 ^ 2 + y0 ^ 2) < 0 := mul_neg_of_neg_of_pos hab hr
    have h2 : 0 < (xa * x0 + ya * y0) * (xb * x0 + yb * y0) := mul_pos_of_neg_of_neg ha hb
    linarith
  have e1 : x1 * x0 + y1 * y0 < 0 := by linarith
  have e2 : x2 * x0 + y2 * y0 < 0 := by linarith
  have e3 : x3 * x0 + y3 * y0 < 0 := by linarith
  have b12 := key x1 y1 x2 y2 e1 e2 h12
  have b13 := key x1 y1 x3 y3 e1 e3 h13
  have b23 := key x2 y2 x3 y3 e2 e3 h23
  nlinarith [mul_pos_of_neg_of_neg b12 b13, sq_nonneg (x0 * y1 - y0 * x1)]

omit [Fintype ι] in
/-- **Lemma B(d)** for `n = 2`: the sign pattern of vectors in the plane is `K₄`-free. A clique
of order `4` would give, after switching, four vectors in `ℝ²` with pairwise negative inner
products. -/
theorem k4Free_of_mul_projPair_pos {S : Matrix ι ι ℝ} (hS : IsSignMatrix S) {u v : ι → ℝ}
    (h : ∀ i j, 0 < S i j * (u i * u j + v i * v j)) : K4Free S := by
  rintro a b c d ⟨-, -, -, -, -, -, habc, habd, hacd, -⟩
  have hsq : ∀ i j, S i j * S i j = 1 := hS.mul_self_apply
  -- coherence of `{a, m, m'}` gives `sₐₘ sₐₘ' = - sₘₘ'`
  have ebc : S a b * S a c = -S b c := by
    unfold Coherent at habc
    linear_combination S b c * habc - S a b * S a c * hsq b c
  have ebd : S a b * S a d = -S b d := by
    unfold Coherent at habd
    linear_combination S b d * habd - S a b * S a d * hsq b d
  have ecd : S a c * S a d = -S c d := by
    unfold Coherent at hacd
    linear_combination S c d * hacd - S a c * S a d * hsq c d
  -- after switching, the vectors `xₐ, -sₐ_b x_b, -sₐ_c x_c, -sₐ_d x_d` are pairwise obtuse
  apply no_four_pairwise_obtuse (u a) (v a) (-S a b * u b) (-S a b * v b) (-S a c * u c)
    (-S a c * v c) (-S a d * u d) (-S a d * v d)
  · linarith [h a b]
  · linarith [h a c]
  · linarith [h a d]
  · have : (-S a b * u b) * (-S a c * u c) + (-S a b * v b) * (-S a c * v c)
        = -(S b c * (u b * u c + v b * v c)) := by
      linear_combination (u b * u c + v b * v c) * ebc
    rw [this]; linarith [h b c]
  · have : (-S a b * u b) * (-S a d * u d) + (-S a b * v b) * (-S a d * v d)
        = -(S b d * (u b * u d + v b * v d)) := by
      linear_combination (u b * u d + v b * v d) * ebd
    rw [this]; linarith [h b d]
  · have : (-S a c * u c) * (-S a d * u d) + (-S a c * v c) * (-S a d * v d)
        = -(S c d * (u c * u d + v c * v d)) := by
      linear_combination (u c * u d + v c * v d) * ecd
    rw [this]; linarith [h c d]

end Grunbaum
