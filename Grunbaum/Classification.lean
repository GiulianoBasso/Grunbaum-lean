/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import Grunbaum.CircleGraph
import FranklFuredi.Theorem1

/-!
# The classification (FF) of `K₄`-free two-graphs

The errata uses the theorem of Frankl and Füredi in the following form.

> **(FF)** Every `K₄`-free two-graph with at least one coherent triple is, up to switching and
> permutation, a blow-up of `R_{2N+1}` for some `N ≥ 1`, or of a principal submatrix of `A₆`.

We deduce it from Theorem 1 of Frankl and Füredi (`FranklFuredi.theorem1`): a 3-graph in which
any four points span `0` or `2` edges is a blow-up `H_S` of their 3-graph `S(6)` (Example 1), or a
circle 3-graph (Example 2). Since `S(6) = [A₆]` up to relabelling
(`Grunbaum.pullback_twoGraph_A6`), the first case gives a blow-up of a principal submatrix of
`A₆`. In the second case we first collapse the classes of twins
(`FranklFuredi.ThreeGraph.exists_twinFree_quotient`); a twin-free circle 3-graph is `[R_{2N+1}]`
(`Grunbaum.exists_equiv_polygon_of_twinFree`).

## Main results

* `Grunbaum.switchEquiv_of_twoGraph_eq` : sign matrices with the same two-graph are switching
  equivalent;
* `Grunbaum.classification` : **(FF)**;
* `Grunbaum.injective_of_switchEquiv_submatrix` : if `S` has no twins, then every blow-up map
  realizing `S` is injective ("the blow-up is trivial because `S₀` has no twins");
* `Grunbaum.hasCoherent_of_forall_not_isTwin` : a sign matrix without twins on at least two
  indices has a coherent triple;
* `Grunbaum.classification_of_forall_not_isTwin` : **(FF) without twins**: a `K₄`-free sign
  matrix without twins on at least two indices is, up to switching and permutation, `R_{2N+1}`
  for some `N ≥ 1`, or a principal submatrix of `A₆`.
-/

open Finset Matrix

namespace Grunbaum

open FranklFuredi

variable {ι κ : Type*}

/-- Sign matrices with the same two-graph are switching equivalent. -/
theorem switchEquiv_of_twoGraph_eq [Fintype ι] [DecidableEq ι] {S T : Matrix ι ι ℝ}
    (hS : IsSignMatrix S) (hT : IsSignMatrix T) (h : twoGraph S = twoGraph T) :
    SwitchEquiv S T := by
  refine switchEquiv_of_coherent_iff hS hT fun i j k hij hik hjk => ?_
  have e : (twoGraph S).IsEdge i j k ↔ (twoGraph T).IsEdge i j k := by rw [h]
  simpa [isEdge_twoGraph hS, isEdge_twoGraph hT, hij, hik, hjk] using e

/-- **(FF)** Every `K₄`-free two-graph with at least one coherent triple is, up to switching and
permutation, a blow-up of `R_{2N+1}` for some `N ≥ 1`, or of a principal submatrix of `A₆`.

A blow-up of `T` along a map `f` is the matrix `T(f, f) = (t_{f(i) f(j)})ᵢⱼ`; for a non-surjective
`f` this is a blow-up of the principal submatrix of `T` on the range of `f`. -/
theorem classification [Finite ι] {S : Matrix ι ι ℝ} (hS : IsSignMatrix S)
    (hK4 : K4Free S) (hcoh : HasCoherent S) :
    (∃ (N : ℕ) (f : ι → Fin (2 * N + 1)), 1 ≤ N ∧ Function.Surjective f ∧
        SwitchEquiv S ((polygonMatrix N).submatrix f f)) ∨
      ∃ f : ι → Fin 6, SwitchEquiv S (A6.submatrix f f) := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨Q, _, _, π, H', hπ, hgood', htf, hH⟩ :=
    ThreeGraph.exists_twinFree_quotient (good_twoGraph hS hK4)
  rcases theorem1 H' ((H'.fourPointProperty_iff).mpr hgood') with ⟨g, hg⟩ | ⟨p, hp, hpH⟩
  · -- a blow-up of `S(6) = [A₆]`
    right
    refine ⟨relabelS6 ∘ g ∘ π,
      switchEquiv_of_twoGraph_eq hS (isSignMatrix_A6.submatrix _) ?_⟩
    rw [twoGraph_submatrix isSignMatrix_A6, ← ThreeGraph.pullback_pullback, pullback_twoGraph_A6,
      ← ThreeGraph.pullback_pullback, hH, hg, HS]
  · -- a circle 3-graph: after collapsing twins, `[R_{2N+1}]`
    left
    obtain ⟨i₀, j₀, k₀, hijk⟩ := hcoh
    have : Nonempty Q := ⟨π i₀⟩
    have hp0 : ∀ v, p v ≠ 0 := fun v h => by
      have := hp.on_circle v
      rw [h] at this
      simp at this
    obtain ⟨N, e, he⟩ := exists_equiv_polygon_of_twinFree hp.genPos hp0 (hpH ▸ htf)
    have hsw : SwitchEquiv S ((polygonMatrix N).submatrix (e ∘ π) (e ∘ π)) := by
      refine switchEquiv_of_twoGraph_eq hS ((isSignMatrix_polygonMatrix N).submatrix _) ?_
      rw [twoGraph_submatrix (isSignMatrix_polygonMatrix N), ← ThreeGraph.pullback_pullback, ← he,
        ← hpH, ← hH]
    refine ⟨N, e ∘ π, ?_, e.surjective.comp hπ, hsw⟩
    -- `N ≥ 1`, since `R₁` has no coherent triple
    by_contra hN
    have h01 : ∀ a b : Fin (2 * N + 1), a = b := fun a b => by ext; omega
    have := hsw.coherent_iff.mp hijk
    unfold Coherent at this
    simp only [submatrix_apply, Function.comp_apply, h01 (e (π j₀)) (e (π i₀)),
      h01 (e (π k₀)) (e (π i₀)), (isSignMatrix_polygonMatrix N).diag] at this
    norm_num at this

/-- If `S` has no twins, then a map `f` with `S = T(f, f)` up to switching is injective: *the
blow-up is trivial because `S₀` has no twins*. -/
theorem injective_of_switchEquiv_submatrix {S : Matrix ι ι ℝ} {T : Matrix κ κ ℝ} {f : ι → κ}
    (h : SwitchEquiv S (T.submatrix f f)) (htw : ∀ i j, ¬IsTwin S i j) :
    Function.Injective f := by
  obtain ⟨ε, hε, h⟩ := h
  intro i j hij
  by_contra hne
  apply htw i j
  refine ⟨hne, ?_⟩
  have key : ∀ k, S j k = ε i * ε j * S i k := by
    intro k
    rw [h j k, h i k]
    simp only [submatrix_apply, hij]
    linear_combination (-(T (f j) (f k)) * ε j * ε k) * hε.mul_self i
  rcases hε i with h1 | h1 <;> rcases hε j with h2 | h2
  · exact Or.inl fun k => by rw [key k, h1, h2]; ring
  · exact Or.inr fun k => by rw [key k, h1, h2]; ring
  · exact Or.inr fun k => by rw [key k, h1, h2]; ring
  · exact Or.inl fun k => by rw [key k, h1, h2]; ring

/-- A sign matrix without twins on at least two indices has a coherent triple. (Otherwise it is
switching equivalent to `J`, and any two indices are twins.) -/
theorem hasCoherent_of_forall_not_isTwin [Fintype ι] {S : Matrix ι ι ℝ} (hS : IsSignMatrix S)
    (h2 : 2 ≤ Fintype.card ι) (htw : ∀ i j, ¬IsTwin S i j) : HasCoherent S := by
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card h2
  by_contra hcoh
  exact htw i j ((isTwin_iff hS).mpr ⟨hij, fun k hk => hcoh ⟨i, j, k, hk⟩⟩)

/-- **(FF) without twins.** A `K₄`-free sign matrix without twins, on at least two indices, is up
to switching and permutation `R_{2N+1}` for some `N ≥ 1`, or a principal submatrix of `A₆`. -/
theorem classification_of_forall_not_isTwin [Fintype ι] {S : Matrix ι ι ℝ}
    (hS : IsSignMatrix S) (hK4 : K4Free S) (h2 : 2 ≤ Fintype.card ι)
    (htw : ∀ i j, ¬IsTwin S i j) :
    (∃ (N : ℕ) (e : ι ≃ Fin (2 * N + 1)), 1 ≤ N ∧
        SwitchEquiv S ((polygonMatrix N).submatrix e e)) ∨
      ∃ f : ι → Fin 6, Function.Injective f ∧ SwitchEquiv S (A6.submatrix f f) := by
  rcases classification hS hK4 (hasCoherent_of_forall_not_isTwin hS h2 htw) with
    ⟨N, f, hN, hf, hsw⟩ | ⟨f, hsw⟩
  · left
    exact ⟨N, Equiv.ofBijective f ⟨injective_of_switchEquiv_submatrix hsw htw, hf⟩, hN, hsw⟩
  · right
    exact ⟨f, injective_of_switchEquiv_submatrix hsw htw, hsw⟩

end Grunbaum
