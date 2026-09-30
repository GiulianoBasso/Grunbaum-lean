/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import Grunbaum.TheoremA
import Grunbaum.PropositionF
import ProjectionConstants.Foundations.Reduction

/-!
# Corollary G: `Π₂ = 4/3`

> **Corollary G** (Chalmers–Lewicki). `Π₂ = 4/3`.
>
> *Proof.* Up to a permutation, `R₃` is the principal submatrix of `R₅` on `{1, 2, 4}`, and so
> `Π(2, R₃) ≤ Π(2, R₅)`. Hence, using Proposition F and Theorem A, we get
> `Π₂ = max {Π(2, R₃), Π(2, R₅)} = Π(2, R₅) = 4/3`.

This is Grünbaum's conjecture, first proved by Chalmers and Lewicki: the maximal absolute
projection constant of two-dimensional real normed spaces is `4/3`.

## Main results

* `Grunbaum.maxProjConst_two` : **Corollary G**, `Π₂ = λ_ℝ(2) = 4/3`;
* `Grunbaum.maxRelProjConst_two_le` : `Π(2, d) ≤ 4/3` for all `d`;
* `Grunbaum.absProjConst_le_four_thirds` : every two-dimensional real normed space `Y` has
  absolute projection constant `λ(Y) ≤ 4/3`;
* `Grunbaum.relProjConst_le_four_thirds` : every two-dimensional subspace `Y` of a real normed
  space `X` is the range of a projection `P : X → X` with `‖P‖ ≤ 4/3 + ε` for every `ε > 0`,
  i.e. `λ(Y, X) ≤ 4/3`.
-/

open ProjectionConstants

namespace Grunbaum

universe u

/-- **Corollary G** (Chalmers–Lewicki). `Π₂ = 4/3`: the maximal absolute projection constant of
two-dimensional real normed spaces is `4/3`. -/
theorem maxProjConst_two : maxProjConst ℝ 2 = 4 / 3 := by
  rw [maxProjConst_two_eq_max, max_eq_right supWeights_R3_le_R5, supWeights_R5]

/-- `Π(2, d) ≤ 4/3` for all `d`. -/
theorem maxRelProjConst_two_le (d : ℕ) : maxRelProjConst ℝ 2 d ≤ 4 / 3 := by
  rw [maxRelProjConst_two_eq_supConfigs]
  exact (supConfigs_le_max d).trans (by rw [max_eq_right supWeights_R3_le_R5, supWeights_R5])

/-- Every two-dimensional real normed space `Y` has absolute projection constant at most `4/3`. -/
theorem absProjConst_le_four_thirds (Y : Type u) [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y] (hY : Module.finrank ℝ Y = 2) : absProjConst ℝ Y ≤ 4 / 3 :=
  absProjConst_le_of_maxRelProjConst_le maxRelProjConst_two_le Y hY

/-- Every two-dimensional subspace `Y` of a real normed space `X` has relative projection constant
`λ(Y, X) ≤ 4/3`. -/
theorem relProjConst_le_four_thirds {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (Y : Submodule ℝ X) [FiniteDimensional ℝ Y] (hY : Module.finrank ℝ Y = 2) :
    relProjConst Y ≤ 4 / 3 :=
  relProjConst_le_of_maxRelProjConst_le maxRelProjConst_two_le Y hY

end Grunbaum
