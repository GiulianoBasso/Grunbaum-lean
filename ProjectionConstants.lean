/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Authors: Giuliano Basso, Claude
-/

-- Foundations
import ProjectionConstants.Foundations.Defs
import ProjectionConstants.Foundations.Linfty
import ProjectionConstants.Foundations.OrthProj
import ProjectionConstants.Foundations.Commute
import ProjectionConstants.Foundations.Reduction
-- Theorem 1.1 (Chalmers–Lewicki)
import ProjectionConstants.ChalmersLewicki.Defs
import ProjectionConstants.ChalmersLewicki.UpperBound
import ProjectionConstants.ChalmersLewicki.LowerBound
import ProjectionConstants.ChalmersLewicki.Formula
import ProjectionConstants.ChalmersLewicki.Absolute

/-!
# Projection constants in Lean (vendored subset)

This folder is an unchanged copy of the files `Foundations/` (without `RankTrace.lean`) and
`ChalmersLewicki/` of the library *Projection constants in Lean*. They provide

* `Foundations/` : relative, absolute and maximal projection constants `λ(Y, X)`, `λ(Y)`,
  `λ_𝕜(m)` of normed spaces; the reduction to subspaces of `ℓ∞^N`; orthogonal projection
  matrices; the commutation of maximizing projections (`commute_of_isMaxOn`);
* `ChalmersLewicki/` : **Theorem 1.1**, the formula of Chalmers and Lewicki
  `λ_𝕜(m, N) = max ∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ|`, and `λ_𝕜(m) = sup_N λ_𝕜(m, N)`.

Only this file was rewritten, so that it imports exactly the vendored files.
-/
