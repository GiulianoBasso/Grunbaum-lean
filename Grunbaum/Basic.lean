/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Basic.Real.Star

/-!
# Basic notation: sign matrices, weights and `π₂`

We fix a finite index type `ι` (think of `ι = {1, …, d}`) and use the notation of the errata to
*Computation of maximal projection constants* (Section 3, *Basic notation and results*).

* `Grunbaum.IsSignMatrix S` : `S ∈ 𝒜`, a symmetric `(±1)`-matrix with ones on the diagonal,
  i.e. `S = 𝟙 + S(G)` for the Seidel adjacency matrix `S(G)` of a simple graph `G`;
* `Grunbaum.IsWeight w` : `D = Diag(w) ∈ 𝒟`, that is, `w ≥ 0` and `∑ wᵢ = 1`;
* `Grunbaum.weightedMatrix S w` : the symmetric matrix `√D S √D`;
* `Grunbaum.IsOrthonormalPair u v` : `u, v ∈ ℝ^ι` are orthonormal;
* `Grunbaum.fanValue A u v = uᵀAu + vᵀAv`, which is `Tr(AP)` for `P = uuᵀ + vvᵀ ∈ 𝒫₂`;
* `Grunbaum.sumTopTwo A` (notation `π₂ A`) : the supremum of `uᵀAu + vᵀAv` over orthonormal
  pairs. By Fan's maximum principle (`Grunbaum.sumTopTwo_eq_eigenvalues₀` in
  `Grunbaum.Fan`), this is the sum of the two largest eigenvalues of a symmetric matrix `A`.

We also collect elementary estimates: the Rayleigh bound `uᵀ(√D S √D)u ≤ |u|²`, Bessel's
inequality for an orthonormal pair, and two facts about the two largest values of a family.

## Implementation notes

The definition of `π₂` as a supremum over orthonormal pairs makes it a total function on all
square matrices. The paper writes `π₂(SD)` for the sum of the two largest eigenvalues of `SD`;
since `SD` and `√D S √D` have the same eigenvalues, we always work with `√D S √D`.

This file is adapted from `ProjectionConstants/Grunbaum/Basic.lean` of the library *Projection
constants in Lean*.
-/

open Finset Matrix

namespace Grunbaum

variable {ι : Type*}

/-! ### The sets `𝒜` and `𝒟` -/

/-- `S ∈ 𝒜`: `S` is a symmetric matrix with entries `±1` and ones on the diagonal. Equivalently,
`S = 𝟙 + S(G)`, where `S(G)` is the Seidel adjacency matrix of a simple graph `G`. -/
structure IsSignMatrix (S : Matrix ι ι ℝ) : Prop where
  symm : ∀ i j, S j i = S i j
  sign : ∀ i j, S i j = 1 ∨ S i j = -1
  diag : ∀ i, S i i = 1

/-- `Diag(w) ∈ 𝒟`: the weights `wᵢ` are nonnegative and sum to one. -/
structure IsWeight [Fintype ι] (w : ι → ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ w i
  sum_eq : ∑ i, w i = 1

/-- The matrix `√D S √D` for `D = Diag(w)`. -/
noncomputable def weightedMatrix (S : Matrix ι ι ℝ) (w : ι → ℝ) : Matrix ι ι ℝ :=
  of fun i j => √(w i) * S i j * √(w j)

lemma weightedMatrix_apply (S : Matrix ι ι ℝ) (w : ι → ℝ) (i j : ι) :
    weightedMatrix S w i j = √(w i) * S i j * √(w j) :=
  rfl

lemma weightedMatrix_eq_diagonal_mul [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) (w : ι → ℝ) :
    weightedMatrix S w = diagonal (fun i => √(w i)) * S * diagonal (fun i => √(w i)) := by
  ext i j
  simp [weightedMatrix, mul_diagonal, diagonal_mul]

namespace IsSignMatrix

variable {S : Matrix ι ι ℝ}

lemma abs_apply (hS : IsSignMatrix S) (i j : ι) : |S i j| = 1 := by
  rcases hS.sign i j with h | h <;> simp [h]

lemma mul_self_apply (hS : IsSignMatrix S) (i j : ι) : S i j * S i j = 1 := by
  rcases hS.sign i j with h | h <;> simp [h]

/-- The matrix `𝟙` of all ones (the sign matrix of the empty graph) lies in `𝒜`. -/
lemma ones : IsSignMatrix (of fun _ _ : ι => (1 : ℝ)) :=
  ⟨fun _ _ => rfl, fun _ _ => Or.inl rfl, fun _ => rfl⟩

end IsSignMatrix

lemma weightedMatrix_symm {S : Matrix ι ι ℝ} (hS : IsSignMatrix S) (w : ι → ℝ) (i j : ι) :
    weightedMatrix S w j i = weightedMatrix S w i j := by
  simp only [weightedMatrix, of_apply, hS.symm]
  ring

lemma isHermitian_weightedMatrix {S : Matrix ι ι ℝ} (hS : IsSignMatrix S) (w : ι → ℝ) :
    (weightedMatrix S w).IsHermitian :=
  IsHermitian.ext fun i j => by simp [weightedMatrix_symm hS w j i]

/-! ### Orthonormal pairs and `π₂` -/

variable [Fintype ι]

/-- The vectors `u, v ∈ ℝ^ι` are orthonormal. -/
structure IsOrthonormalPair (u v : ι → ℝ) : Prop where
  norm_left : u ⬝ᵥ u = 1
  norm_right : v ⬝ᵥ v = 1
  orth : u ⬝ᵥ v = 0

lemma IsOrthonormalPair.symm {u v : ι → ℝ} (h : IsOrthonormalPair u v) :
    IsOrthonormalPair v u :=
  ⟨h.norm_right, h.norm_left, by rw [dotProduct_comm]; exact h.orth⟩

/-- `uᵀAu + vᵀAv`. For an orthonormal pair this is `Tr(AP)`, where `P = uuᵀ + vvᵀ` is the
orthogonal projection onto the plane spanned by `u` and `v`. -/
def fanValue (A : Matrix ι ι ℝ) (u v : ι → ℝ) : ℝ := u ⬝ᵥ (A *ᵥ u) + v ⬝ᵥ (A *ᵥ v)

/-- The set of values `uᵀAu + vᵀAv` over all orthonormal pairs `u, v`. -/
def fanValues (A : Matrix ι ι ℝ) : Set ℝ :=
  {x | ∃ u v, IsOrthonormalPair u v ∧ fanValue A u v = x}

/-- `π₂(A) = sup { uᵀAu + vᵀAv : u, v orthonormal }`. By Fan's maximum principle
(`Grunbaum.sumTopTwo_eq_eigenvalues₀`), this is the sum of the two largest eigenvalues of a
symmetric matrix `A`. -/
noncomputable def sumTopTwo (A : Matrix ι ι ℝ) : ℝ := sSup (fanValues A)

@[inherit_doc] scoped notation "π₂" => sumTopTwo

/-! ### Elementary facts -/

lemma dotProduct_mulVec_eq_sum (A : Matrix ι ι ℝ) (u : ι → ℝ) :
    u ⬝ᵥ (A *ᵥ u) = ∑ i, ∑ j, A i j * u i * u j := by
  simp only [dotProduct, mulVec, mul_sum]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

lemma fanValue_symm (A : Matrix ι ι ℝ) (u v : ι → ℝ) : fanValue A u v = fanValue A v u := by
  simp only [fanValue, add_comm]

lemma fanValue_eq_sum (A : Matrix ι ι ℝ) (u v : ι → ℝ) :
    fanValue A u v = ∑ i, ∑ j, A i j * (u i * u j + v i * v j) := by
  simp only [fanValue, dotProduct_mulVec_eq_sum, ← sum_add_distrib]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

lemma dotProduct_self_nonneg' (u : ι → ℝ) : 0 ≤ u ⬝ᵥ u :=
  sum_nonneg fun i _ => mul_self_nonneg (u i)

/-- Coordinates of a unit vector are bounded by one. -/
lemma sq_le_one_of_dotProduct {u : ι → ℝ} (hu : u ⬝ᵥ u = 1) (i : ι) : u i ^ 2 ≤ 1 := by
  rw [← hu, dotProduct, sq]
  exact single_le_sum (f := fun k => u k * u k) (fun k _ => mul_self_nonneg (u k)) (mem_univ i)

lemma abs_le_one_of_dotProduct {u : ι → ℝ} (hu : u ⬝ᵥ u = 1) (i : ι) : |u i| ≤ 1 :=
  abs_le_of_sq_le_sq (by simpa using sq_le_one_of_dotProduct hu i) zero_le_one

/-- A crude bound: `uᵀAu + vᵀAv ≤ 2 ∑ |Aᵢⱼ|` for an orthonormal pair `u, v`. -/
lemma fanValue_le_sum_abs (A : Matrix ι ι ℝ) {u v : ι → ℝ} (h : IsOrthonormalPair u v) :
    fanValue A u v ≤ 2 * ∑ i, ∑ j, |A i j| := by
  rw [fanValue_eq_sum, mul_sum]
  refine sum_le_sum fun i _ => ?_
  rw [mul_sum]
  refine sum_le_sum fun j _ => ?_
  have hu := abs_le_one_of_dotProduct h.norm_left
  have hv := abs_le_one_of_dotProduct h.norm_right
  have h1 : |u i * u j + v i * v j| ≤ 2 := by
    calc |u i * u j + v i * v j| ≤ |u i| * |u j| + |v i| * |v j| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ 1 * 1 + 1 * 1 := by
          gcongr
          exacts [hu i, hu j, hv i, hv j]
      _ = 2 := by norm_num
  calc A i j * (u i * u j + v i * v j) ≤ |A i j * (u i * u j + v i * v j)| := le_abs_self _
    _ = |A i j| * |u i * u j + v i * v j| := abs_mul _ _
    _ ≤ |A i j| * 2 := by gcongr
    _ = 2 * |A i j| := by ring

lemma bddAbove_fanValues (A : Matrix ι ι ℝ) : BddAbove (fanValues A) :=
  ⟨2 * ∑ i, ∑ j, |A i j|, by rintro x ⟨u, v, h, rfl⟩; exact fanValue_le_sum_abs A h⟩

lemma fanValue_le_sumTopTwo (A : Matrix ι ι ℝ) {u v : ι → ℝ} (h : IsOrthonormalPair u v) :
    fanValue A u v ≤ π₂ A :=
  le_csSup (bddAbove_fanValues A) ⟨u, v, h, rfl⟩

lemma sumTopTwo_le {A : Matrix ι ι ℝ} {c : ℝ} (hne : (fanValues A).Nonempty)
    (h : ∀ u v, IsOrthonormalPair u v → fanValue A u v ≤ c) : π₂ A ≤ c :=
  csSup_le hne (by rintro x ⟨u, v, huv, rfl⟩; exact h u v huv)

/-- If there is no orthonormal pair, then `π₂ A = 0`. -/
lemma sumTopTwo_of_not_nonempty {A : Matrix ι ι ℝ} (h : ¬(fanValues A).Nonempty) :
    π₂ A = 0 := by
  rw [Set.not_nonempty_iff_eq_empty] at h
  simp [sumTopTwo, h]

/-- `π₂ A ≤ c` as soon as `uᵀAu + vᵀAv ≤ c` for all orthonormal pairs and `0 ≤ c`. -/
lemma sumTopTwo_le' {A : Matrix ι ι ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ u v, IsOrthonormalPair u v → fanValue A u v ≤ c) : π₂ A ≤ c := by
  by_cases hne : (fanValues A).Nonempty
  · exact sumTopTwo_le hne h
  · rw [sumTopTwo_of_not_nonempty hne]; exact hc

lemma fanValues_nonempty_iff (A B : Matrix ι ι ℝ) :
    (fanValues A).Nonempty ↔ (fanValues B).Nonempty := by
  constructor
  · rintro ⟨_, u, v, h, rfl⟩; exact ⟨_, u, v, h, rfl⟩
  · rintro ⟨_, u, v, h, rfl⟩; exact ⟨_, u, v, h, rfl⟩

/-! ### The Rayleigh bound `uᵀ(√D S √D)u ≤ |u|²` -/

lemma dotProduct_mulVec_weightedMatrix_le {S : Matrix ι ι ℝ} {w : ι → ℝ} (hS : IsSignMatrix S)
    (hw : IsWeight w) (u : ι → ℝ) : u ⬝ᵥ (weightedMatrix S w *ᵥ u) ≤ u ⬝ᵥ u := by
  have hsq : ∀ i, √(w i) ^ 2 = w i := fun i => Real.sq_sqrt (hw.nonneg i)
  calc u ⬝ᵥ (weightedMatrix S w *ᵥ u)
      = ∑ i, ∑ j, (√(w i) * S i j * √(w j)) * u i * u j := by
        simp [dotProduct_mulVec_eq_sum, weightedMatrix]
    _ ≤ ∑ i, ∑ j, (√(w i) * |u i|) * (√(w j) * |u j|) := by
        refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
        calc (√(w i) * S i j * √(w j)) * u i * u j
            ≤ |(√(w i) * S i j * √(w j)) * u i * u j| := le_abs_self _
          _ = (√(w i) * |u i|) * (√(w j) * |u j|) := by
              simp only [abs_mul, hS.abs_apply, abs_of_nonneg (Real.sqrt_nonneg _)]
              ring
    _ = (∑ i, √(w i) * |u i|) ^ 2 := by rw [sq, sum_mul_sum]
    _ ≤ (∑ i, √(w i) ^ 2) * ∑ i, |u i| ^ 2 := sum_mul_sq_le_sq_mul_sq _ _ _
    _ = u ⬝ᵥ u := by simp only [hsq, hw.sum_eq, one_mul, dotProduct, sq, abs_mul_abs_self]

lemma dotProduct_mulVec_weightedMatrix_le_one {S : Matrix ι ι ℝ} {w : ι → ℝ}
    (hS : IsSignMatrix S) (hw : IsWeight w) {u : ι → ℝ} (hu : u ⬝ᵥ u = 1) :
    u ⬝ᵥ (weightedMatrix S w *ᵥ u) ≤ 1 :=
  hu ▸ dotProduct_mulVec_weightedMatrix_le hS hw u

/-! ### Bessel's inequality for an orthonormal pair -/

lemma bessel {u v : ι → ℝ} (h : IsOrthonormalPair u v) (x : ι → ℝ) :
    (u ⬝ᵥ x) ^ 2 + (v ⬝ᵥ x) ^ 2 ≤ x ⬝ᵥ x := by
  set a := u ⬝ᵥ x
  set b := v ⬝ᵥ x
  have h0 : 0 ≤ ∑ i, (x i - a * u i - b * v i) ^ 2 := sum_nonneg fun i _ => sq_nonneg _
  have expand : ∑ i, (x i - a * u i - b * v i) ^ 2
      = x ⬝ᵥ x - 2 * a * (u ⬝ᵥ x) - 2 * b * (v ⬝ᵥ x) + a ^ 2 * (u ⬝ᵥ u)
        + 2 * a * b * (u ⬝ᵥ v) + b ^ 2 * (v ⬝ᵥ v) := by
    simp only [dotProduct, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [expand, h.norm_left, h.norm_right, h.orth] at h0
  nlinarith [h0]

/-! ### The two largest values of a family -/

/-- If `a` is a largest and `b` a second largest index of `l`, and `0 ≤ α ≤ 1` with
`∑ α = 2`, then `∑ lⱼ αⱼ ≤ l a + l b`. -/
lemma sum_mul_le_top_two (l α : ι → ℝ) (h0 : ∀ j, 0 ≤ α j)
    (h1 : ∀ j, α j ≤ 1) (hsum : ∑ j, α j = 2) {a b : ι} (ha : ∀ j, l j ≤ l a)
    (hb : ∀ j, j ≠ a → l j ≤ l b) : ∑ j, l j * α j ≤ l a + l b := by
  classical
  have key : ∑ j, l j * α j = ∑ j, (l j - l b) * α j + 2 * l b := by
    rw [← hsum, sum_mul, ← sum_add_distrib]
    exact sum_congr rfl fun j _ => by ring
  have hrest : ∑ j ∈ univ.erase a, (l j - l b) * α j ≤ 0 :=
    sum_nonpos fun j hj =>
      mul_nonpos_of_nonpos_of_nonneg (by linarith [hb j (ne_of_mem_erase hj)]) (h0 j)
  have htop : (l a - l b) * α a ≤ l a - l b := by
    have := ha b
    nlinarith [h1 a, h0 a]
  rw [key, ← add_sum_erase _ _ (mem_univ a)]
  linarith

/-- Every family indexed by a type with at least two elements has a largest and a second
largest index. -/
lemma exists_top_two (l : ι → ℝ) (h2 : 1 < Fintype.card ι) :
    ∃ a b, a ≠ b ∧ (∀ j, l j ≤ l a) ∧ ∀ j, j ≠ a → l j ≤ l b := by
  classical
  obtain ⟨a, -, ha⟩ := exists_max_image univ l
    (univ_nonempty_iff.2 (Fintype.card_pos_iff.mp (by omega)))
  have hne : (univ.erase a).Nonempty := by
    rw [← card_pos, card_erase_of_mem (mem_univ a), card_univ]
    omega
  obtain ⟨b, hb, hbmax⟩ := exists_max_image (univ.erase a) l hne
  exact ⟨a, b, (ne_of_mem_erase hb).symm, fun j => ha j (mem_univ j),
    fun j hj => hbmax j (mem_erase.2 ⟨hj, mem_univ j⟩)⟩

omit [Fintype ι] in
/-- For the top pair `(a, b)`, every sum `l i + l j` with `i ≠ j` is at most `l a + l b`. -/
lemma add_le_top_two (l : ι → ℝ) {a b : ι} (ha : ∀ j, l j ≤ l a)
    (hb : ∀ j, j ≠ a → l j ≤ l b) {i j : ι} (hij : i ≠ j) : l i + l j ≤ l a + l b := by
  by_cases hi : i = a
  · subst hi
    linarith [hb j (Ne.symm hij)]
  · by_cases hj : j = a
    · subst hj
      linarith [hb i hij]
    · linarith [ha i, hb j hj, ha j, hb i hi, ha b]

end Grunbaum
