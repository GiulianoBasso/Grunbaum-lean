/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import Grunbaum.Polygon

/-!
# Lemma D: `A₆` is not the sign pattern of six vectors in the plane

> **Lemma D.** `A₆` is not, up to switching and permutation, the sign pattern
> `(sgn⟨uᵢ, uⱼ⟩)ᵢⱼ` of six vectors `u₁, …, u₆ ∈ ℝ²` with pairwise non-zero inner products.

*Proof of the errata.* We may assume that the sign pattern equals `A₆ = 𝟙₆ + S(K₁ ∪ C₅)` and,
after a rotation, that `u₁ = (t, 0)` with `t > 0`. Since the vertex `1` is isolated, every `uⱼ`
has positive first coordinate, `uⱼ = rⱼ (cos θⱼ, sin θⱼ)` with `θⱼ ∈ (-π/2, π/2)`, and
`sᵢⱼ = +1` iff `|θᵢ - θⱼ| < π/2`. So on `{2, …, 6}` the graph `H` with these edges is the
complement of `C₅`, again a `5`-cycle. But `H` has no induced cycle of length at least `4`: in
such a cycle, the vertex `i` with the smallest `θᵢ` has two neighbours with `θ ∈ [θᵢ, θᵢ + π/2)`,
which are adjacent to each other.

In the formal proof we avoid angles: instead of `θⱼ` we use the slope `σⱼ = tan(θⱼ - θ₁)` of `uⱼ`
relative to `u₁`, i.e. `σⱼ = det(u₁, uⱼ) / ⟨u₁, uⱼ⟩`, and `sᵢⱼ = sgn(1 + σᵢ σⱼ)`. The key step is
`Grunbaum.acute_of_min`.

With the indices `0, …, 5` of `Grunbaum.A6`, the vertex `0` is isolated and `1 - 4 - 3 - 2 - 5 - 1`
is the `5`-cycle `C₅`.

This file is adapted from `ProjectionConstants/Grunbaum/{LemmaD,TwoGraph}.lean` of the library
*Projection constants in Lean*.
-/

open Finset Matrix

namespace Grunbaum

/-- The key inequality: if `a` is the smallest of three slopes `a, b, c` and the directions with
slopes `b` and `c` both make an acute angle with the direction of slope `a`, then they make an
acute angle with each other. -/
lemma acute_of_min {a b c : ℝ} (hb : a ≤ b) (hc : a ≤ c) (h1 : 0 < 1 + a * b)
    (h2 : 0 < 1 + a * c) : 0 < 1 + b * c := by
  rcases lt_or_ge 0 c with hc0 | hc0
  · nlinarith [mul_nonneg (sub_nonneg.2 hb) hc0.le]
  rcases lt_or_ge 0 b with hb0 | hb0
  · nlinarith [mul_nonneg (sub_nonneg.2 hc) hb0.le]
  · nlinarith [mul_nonneg_of_nonpos_of_nonpos hb0 hc0]

/-- **Lemma D.** `A₆` is not the sign pattern `(sgn⟨uᵢ, uⱼ⟩)ᵢⱼ` of six vectors
`uᵢ = (xᵢ, yᵢ) ∈ ℝ²` with pairwise non-zero inner products. -/
theorem not_signPattern_A6 (x y : Fin 6 → ℝ)
    (h : ∀ i j, 0 < A6 i j * (x i * x j + y i * y j)) : False := by
  -- coordinates relative to `u₀`: `aⱼ = ⟨uⱼ, u₀⟩`, `bⱼ = det(u₀, uⱼ)`, slope `σⱼ = bⱼ / aⱼ`
  set a : Fin 6 → ℝ := fun j => x j * x 0 + y j * y 0 with ha_def
  set b : Fin 6 → ℝ := fun j => x 0 * y j - y 0 * x j with hb_def
  set σ : Fin 6 → ℝ := fun j => b j / a j with hσ_def
  -- the vertex `0` is isolated: `⟨u₀, uⱼ⟩ > 0` for all `j`
  have hrow : ∀ j, A6 0 j = 1 := by intro j; fin_cases j <;> simp [A6]
  have ha : ∀ j, 0 < a j := by
    intro j
    have := h 0 j
    rw [hrow j, one_mul] at this
    simp only [ha_def]
    linarith
  have hr : 0 < x 0 ^ 2 + y 0 ^ 2 := by
    have := ha 0
    simp only [ha_def] at this
    nlinarith
  -- `⟨uᵢ, uⱼ⟩ |u₀|² = aᵢ aⱼ (1 + σᵢ σⱼ)`
  have hq : ∀ i j, (x i * x j + y i * y j) * (x 0 ^ 2 + y 0 ^ 2)
      = a i * a j * (1 + σ i * σ j) := by
    intro i j
    have hai := (ha i).ne'
    have haj := (ha j).ne'
    simp only [hσ_def]
    field_simp
    simp only [ha_def, hb_def]
    ring
  -- so the sign of `1 + σᵢ σⱼ` is the entry `A₆ i j`
  have key : ∀ i j, 0 < A6 i j * (1 + σ i * σ j) := by
    intro i j
    have h1 : 0 < A6 i j * (x i * x j + y i * y j) * (x 0 ^ 2 + y 0 ^ 2) := mul_pos (h i j) hr
    rw [mul_assoc, hq i j] at h1
    have h2 : 0 < A6 i j * (1 + σ i * σ j) * (a i * a j) := by linarith
    exact pos_of_mul_pos_left h2 (mul_pos (ha i) (ha j)).le
  -- the graph `{i, j : A₆ i j = 1}` on `{1, …, 5}` is the 5-cycle `1 - 2 - 4 - 5 - 3 - 1`
  have e12 : 0 < 1 + σ 1 * σ 2 := by simpa [A6] using key 1 2
  have e13 : 0 < 1 + σ 1 * σ 3 := by simpa [A6] using key 1 3
  have e24 : 0 < 1 + σ 2 * σ 4 := by simpa [A6] using key 2 4
  have e35 : 0 < 1 + σ 3 * σ 5 := by simpa [A6] using key 3 5
  have e45 : 0 < 1 + σ 4 * σ 5 := by simpa [A6] using key 4 5
  have n23 : 1 + σ 2 * σ 3 < 0 := by have := key 2 3; simp [A6] at this; linarith
  have n14 : 1 + σ 1 * σ 4 < 0 := by have := key 1 4; simp [A6] at this; linarith
  have n25 : 1 + σ 2 * σ 5 < 0 := by have := key 2 5; simp [A6] at this; linarith
  have n34 : 1 + σ 3 * σ 4 < 0 := by have := key 3 4; simp [A6] at this; linarith
  have n15 : 1 + σ 1 * σ 5 < 0 := by have := key 1 5; simp [A6] at this; linarith
  -- a vertex of the 5-cycle cannot have the smallest slope among itself and its two neighbours
  have v1 : σ 2 < σ 1 ∨ σ 3 < σ 1 := by
    by_contra hcon
    push Not at hcon
    have := acute_of_min hcon.1 hcon.2 e12 e13
    linarith
  have v2 : σ 1 < σ 2 ∨ σ 4 < σ 2 := by
    by_contra hcon
    push Not at hcon
    have := acute_of_min hcon.1 hcon.2 (by linarith [e12, mul_comm (σ 1) (σ 2)]) e24
    linarith
  have v4 : σ 2 < σ 4 ∨ σ 5 < σ 4 := by
    by_contra hcon
    push Not at hcon
    have := acute_of_min hcon.1 hcon.2 (by linarith [e24, mul_comm (σ 2) (σ 4)]) e45
    linarith
  have v5 : σ 4 < σ 5 ∨ σ 3 < σ 5 := by
    by_contra hcon
    push Not at hcon
    have := acute_of_min hcon.1 hcon.2 (by linarith [e45, mul_comm (σ 4) (σ 5)])
      (by linarith [e35, mul_comm (σ 3) (σ 5)])
    linarith [mul_comm (σ 3) (σ 4)]
  have v3 : σ 5 < σ 3 ∨ σ 1 < σ 3 := by
    by_contra hcon
    push Not at hcon
    have := acute_of_min hcon.1 hcon.2 e35 (by linarith [e13, mul_comm (σ 1) (σ 3)])
    linarith [mul_comm (σ 1) (σ 5)]
  -- the vertex with the smallest slope gives a contradiction
  rcases v1 with h1 | h1 <;> rcases v2 with h2 | h2 <;> rcases v3 with h3 | h3 <;>
    rcases v4 with h4 | h4 <;> rcases v5 with h5 | h5 <;> linarith

/-- **Lemma D**, up to switching and permutation: if `S` is the sign pattern of vectors
`xᵢ = (uᵢ, vᵢ)` in the plane, then no six indices of `S` carry a copy of `A₆` up to switching. -/
theorem not_signPattern_A6_of_switch {ι : Type*} {S : Matrix ι ι ℝ} {u v : ι → ℝ}
    (h : ∀ i j, 0 < S i j * (u i * u j + v i * v j)) (ψ : Fin 6 → ι) (δ : Fin 6 → ℝ)
    (hδ : ∀ a, δ a * δ a = 1) (hψ : ∀ a b, S (ψ a) (ψ b) = δ a * δ b * A6 a b) : False := by
  apply not_signPattern_A6 (fun a => δ a * u (ψ a)) (fun a => δ a * v (ψ a))
  intro a b
  have e : A6 a b = δ a * δ b * S (ψ a) (ψ b) := by
    rw [hψ]
    linear_combination (-(A6 a b) * δ b * δ b) * hδ a + (-(A6 a b)) * hδ b
  calc 0 < S (ψ a) (ψ b) * (u (ψ a) * u (ψ b) + v (ψ a) * v (ψ b)) := h (ψ a) (ψ b)
    _ = A6 a b * (δ a * u (ψ a) * (δ b * u (ψ b)) + δ a * v (ψ a) * (δ b * v (ψ b))) := by
        rw [e]
        linear_combination (-(S (ψ a) (ψ b) * (u (ψ a) * u (ψ b) + v (ψ a) * v (ψ b))) * δ b * δ b)
          * hδ a + (-(S (ψ a) (ψ b) * (u (ψ a) * u (ψ b) + v (ψ a) * v (ψ b)))) * hδ b

end Grunbaum
