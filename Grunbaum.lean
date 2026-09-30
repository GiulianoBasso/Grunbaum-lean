/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
-- Notation, Fan's maximum principle and the formula of Chalmers and Lewicki
import Grunbaum.Basic
import Grunbaum.Fan
import Grunbaum.Transfer
import Grunbaum.Maximizer
import Grunbaum.ChalmersLewicki
-- Two-graphs and the classification (FF) of Frankl and Füredi
import Grunbaum.TwoGraph
import Grunbaum.ThreeGraph
import Grunbaum.Polygon
import Grunbaum.CircleGraph
import Grunbaum.Classification
-- The lemmas of the errata
import Grunbaum.LemmaB
import Grunbaum.KMMP
import Grunbaum.LemmaC
import Grunbaum.LemmaD
import Grunbaum.BlowUp
-- Theorem A, the computation of `Π(2, R₅)` and `Π₂ = 4/3`
import Grunbaum.TheoremA
import Grunbaum.PropositionF
import Grunbaum.CorollaryG
import Grunbaum.Main

/-!
# `Π₂ = 4/3`, following the errata

This library formalizes the self-contained proof of `Π₂ = 4/3` (Grünbaum's conjecture, first
proved by Chalmers and Lewicki) given in item 5) of Section 3 of the errata to

* G. Basso, *Computation of maximal projection constants*, J. Funct. Anal. 277 (2019).

The main result is `Grunbaum.maxProjConst_two : ProjectionConstants.maxProjConst ℝ 2 = 4 / 3`.
See `Grunbaum.Main` for the statements in the numbering of the errata, and `README.md` for an
overview.
-/
