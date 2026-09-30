#Proof of `Π₂ = 4/3` in Lean

![build](https://github.com/GiulianoBasso/Grunbaum-lean/actions/workflows/build.yml/badge.svg)





This repository is a self-contained Lean 4 / Mathlib formalization of the proof of

$$\Pi_2 = \tfrac43,$$

Grünbaum's conjecture on the maximal projection constant of two-dimensional real normed spaces
(first proved by Chalmers and Lewicki), **along the route of the new proof in the errata**:

* G. Basso, *Errata to the single-author papers of Giuliano Basso*, 
https://www.researchgate.net/publication/415013493_Errata_to_the_single-author_papers_of_Giuliano_Basso

The classification of `K₄`-free two-graphs is taken from a formalization of Frankl and Füredi,
*An exact result for 3-graphs* [FF], and the basic theory of projection constants and the formula
of Chalmers and Lewicki from the library *Projection constants in Lean* [PC]. The cloning lemma
used in Lemma C is formalized from Kumar, Mohar, Mojallal and Pragada [KMMP].

Everything is proved from the standard axioms (`propext`, `Classical.choice`, `Quot.sound`):
there is no `sorry`, no `native_decide` and no additional axiom.


## Authorship

The Lean code in this repository, including the vendored libraries, was written by Claude, an AI
model developed by Anthropic (model identifiers claude-opus-5-5 and claude-fable-5-1), in sessions
guided by Giuliano Basso. He chose the statements to formalize, built the project, ran the axiom
check in `scripts/CheckAxioms.lean` and compared the statements in `Grunbaum/Main.lean` with the
errata. 

A formal proof certifies exactly the Lean statement that was proved. Lean and Mathlib check the
proofs; what remains to be read by a human is the encoding of the definitions, described in the
sections *Errata → Lean* and *Where the formal proofs differ from the errata* below. 



## The main theorem

```lean
theorem Grunbaum.maxProjConst_two : ProjectionConstants.maxProjConst ℝ 2 = 4 / 3
```

Here `ProjectionConstants.maxProjConst ℝ 2` is the Banach-space quantity
`Π₂ = λ_ℝ(2) = sup { λ(Y) : dim Y = 2 }`, where `λ(Y) = sup_X λ(Y, X)` is the absolute projection
constant of a real normed space `Y` and `λ(Y, X) = inf { ‖P‖ : P projection of X onto Y }`
([PC], `ProjectionConstants/Foundations/Defs.lean`). Two consequences in plain words
(`Grunbaum/CorollaryG.lean`):

```lean
/-- Every two-dimensional real normed space has absolute projection constant at most `4/3`. -/
theorem Grunbaum.absProjConst_le_four_thirds (Y : Type u) [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] (hY : Module.finrank ℝ Y = 2) :
    absProjConst ℝ Y ≤ 4 / 3

/-- Every two-dimensional subspace of a real normed space has `λ(Y, X) ≤ 4/3`. -/
theorem Grunbaum.relProjConst_le_four_thirds {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (Y : Submodule ℝ X) [FiniteDimensional ℝ Y]
    (hY : Module.finrank ℝ Y = 2) : relProjConst Y ≤ 4 / 3
```

**Start reading at [`Grunbaum/Main.lean`](Grunbaum/Main.lean)**, which restates every result
of the errata in the order in which it appears there (namespace `Grunbaum.Errata`).

## The proof being formalized

For `S ∈ 𝒜_d` (symmetric `±1`-matrices with ones on the diagonal) and `D ∈ 𝒟_d` (non-negative
diagonal matrices of trace one) let `π₂(√D S √D)` be the sum of the two largest eigenvalues. By
the formula of Chalmers and Lewicki,

* `Π(2, d) = max { π₂(√D S √D) : S ∈ 𝒜_d, D ∈ 𝒟_d }` and `Π₂ = sup_d Π(2, d)`;
* `Π(2, S) := max_{D ∈ 𝒟_d} π₂(√D S √D)`.

**Theorem A** (Reduction). `Π₂ = max {Π(2, R₃), Π(2, R₅)}`.

Fix `d > 2`, take a maximizer of `Π(2, d)` of minimal support and restrict it to its support
`{1, …, m}`. It is a weighted configuration of vectors `u₁, …, u_m ∈ ℝ²` whose sign pattern is
`S₀` (Lemma B). Then:

1. **No clique of order 4** (Lemma B(d)): four vectors in the plane cannot be pairwise obtuse;
   also `m ≥ 3` and `Π(2, d) ≥ π₂(⅓R₃) = 4/3`.
2. **No twins**: twins could be merged by the blow-up lemma [JFA, Lemma 2.2], which removes one
   zero eigenvalue; since `λ₂(M) > 0` this does not change `π₂`.
3. **No coclique of order 4**: four rank-one matrices `uᵢuᵢᵀ` in the 3-dimensional space of
   symmetric `2 × 2` matrices are linearly dependent, and the cloning lemma (Lemma C, [KMMP,
   Claim 2.4]) shifts the weights until one vanishes.
4. **Classification**: by (FF) a `K₄`-free two-graph without twins is some `R_{2N+1}` or a
   principal submatrix of `A₆`; by (R1) and Step 3, `N ≤ 2`; `A₆` itself is excluded by
   Lemma D, and its `5 × 5` principal submatrices are `R₅` by (A1).

**Lemma E** computes `det(x𝟙₅ − √D R₅ √D) = x⁵ − x⁴ + 4τx² − 16δ`, and a Vieta argument gives
**Proposition F**: `Π(2, R₅) = 4/3`, attained only for singular `D`. Since `R₃` is a principal
submatrix of `R₅`, **Corollary G** follows: `Π₂ = Π(2, R₅) = 4/3`.

## Errata → Lean

All names are in the namespace `Grunbaum`; the column *Main* gives the restatement in
`Grunbaum/Main.lean` (namespace `Grunbaum.Errata`).

| Errata | Lean | Main | File |
|---|---|---|---|
| `𝒜_d`, `𝒟_d`, `√D S √D`, `π₂` | `IsSignMatrix`, `IsWeight`, `weightedMatrix`, `sumTopTwo` (notation `π₂`) | | `Basic` |
| Fan's maximum principle | `sumTopTwo_eq_top_two`, `sumTopTwo_eq_eigenvalues₀` | `fan` | `Fan` |
| `Π(2, S)`, `Π(2, d)`, maximizers | `supWeights`, `supConfigs`, `IsMaximizer`, `exists_isMaximizer` | | `Maximizer` |
| principal submatrices, switching, relabelling | `supWeights_le_of_transfer`, `supWeights_eq_of_equiv` | `supWeights_principal`, `supWeights_switch_relabel` | `Maximizer` |
| maximizer of minimal support | `exists_minimal_maximizer` | | `Maximizer` |
| Chalmers–Lewicki ([JFA, Thm 2.1]) | `maxRelProjConst_two_eq_supConfigs`, `maxProjConst_two_eq_iSup` | `chalmers_lewicki` | `ChalmersLewicki` |
| `[S]`, coherent, coclique, clique, twins | `twoGraph`, `Coherent`, `IsCoclique`, `K4Free`, `IsTwin` | `coclique_iff`, `clique_iff`, `twins_switch` | `TwoGraph` |
| `R_{2N+1}` of [JFA, §4.1] (item 8 corrected); "we may label the indices of `R_{2N+1}` by `p₀, …, p_{2N}` such that `[R_{2N+1}] = T_{2N+1}`" | `blockR`, `blockR_eq`, `twoGraph_blockR` | `twoGraph_R_JFA` | `Polygon` |
| `R_{2N+1}` with indices `p₀, …, p_{2N}`, `T_{2N+1}` | `polygonMatrix`, `twoGraph_polygonMatrix` | `twoGraph_R` | `Polygon` |
| **(R1)** | `isCoclique_polygonMatrix` | `fact_R1` | `Polygon` |
| **(R2)** | `polygonMatrix_two_eq`, `switchEquiv_polygonMatrix_two` | `fact_R2` | `Polygon` |
| **(A1)** | `A6_eq_certificate`, `certMap_injective` | `fact_A1` | `Polygon` |
| **(FF)** | `classification`, `classification_of_forall_not_isTwin` | `fact_FF` | `Classification` |
| twin-free circle 3-graphs are `T_{2N+1}` | `exists_equiv_polygon_of_twinFree` | | `CircleGraph` |
| **Theorem A** | `maxProjConst_two_eq_max`, `maxProjConst_two_eq_max_blockR` | `theorem_A`, `theorem_A'` | `TheoremA` |
| **Lemma B** (a)–(d), `n = 2` | `mul_projPair_comm`, `trace_mul_projPair`, `mul_projPair_pos`, `sumTopTwo_eq_sum_abs`, `k4Free_of_mul_projPair_pos` | `lemma_B` | `LemmaB` |
| **Lemma C**, `n = 2` | `IsMaximizer.clone` | `lemma_C` | `LemmaC` |
| [KMMP, Thm 2.1, Rem 2.2, Claims 2.1–2.4] | `KMMP.sigma_le`, `KMMP.one_le_maxRelProjConst`, `KMMP.IsMaximizingPair.absGram_mulVec`, `.mul_eq_mul`, `.dotProduct_mulVec_H`, `.clone` | `kmmp_cloning` | `KMMP` |
| **Lemma D** | `not_signPattern_A6`, `not_signPattern_A6_of_switch` | `lemma_D` | `LemmaD` |
| [JFA, Lemma 2.2] (blow-ups) | `charpoly_weightedMatrix_submatrix`, `charpoly_weightedMatrix_eq_X_mul`, `sumTopTwo_eq_of_charpoly_eq_X_mul` | `blow_up` | `BlowUp` |
| Step 1: `Π ≥ 4/3`, `m ≥ 3`; no clique of order 4 | `four_thirds_le_supConfigs`, `three_le_of_isMaximizer`; `k4Free_of_mul_projPair_pos` | `step_1`; `lemma_B` | `TheoremA`; `LemmaB` |
| Step 2: no twins | `not_isTwin_of_minimal` | `step_2` | `TheoremA` |
| Step 3: no coclique of order 4 | `card_le_three_of_isCoclique` | `step_3` | `TheoremA` |
| Step 4: classification | `supWeights_le_max_of_minimal` | `step_4` | `TheoremA` |
| **Lemma E** | `charpoly_weightedMatrix_R5` | `lemma_E` | `PropositionF` |
| **Proposition F** | `supWeights_R5`, `sumTopTwo_weightedMatrix_R5_lt` | `proposition_F` | `PropositionF` |
| **Corollary G** | `maxProjConst_two` | `corollary_G` | `CorollaryG` |

## Layout

```
Grunbaum.lean              root of the library
Grunbaum/
  Basic.lean               𝒜, 𝒟, √D S √D, orthonormal pairs, π₂ (variational definition)
  Fan.lean                 stationarity of maximizing pairs; Fan's maximum principle
  Transfer.lean            switching, relabelling, principal submatrices
  Maximizer.lean           Π(2, S), Π(2, ι), existence of maximizers, minimal support
  ChalmersLewicki.lean     Π(2, d) = λ_ℝ(2, d) and Π₂ = λ_ℝ(2), from [PC]
  TwoGraph.lean            two-graphs [S] as 3-graphs of [FF]; cocliques, cliques, twins
  ThreeGraph.lean          blow-ups of 3-graphs; the twin quotient
  Polygon.lean             R_{2N+1} of [JFA, §4.1], T_{2N+1}, R₅, A₆; (R1), (R2), (A1)
  CircleGraph.lean         twin-free circle 3-graphs are regular polygons
  Classification.lean      (FF), from Theorem 1 of Frankl and Füredi
  LemmaB.lean              Lemma B (structure of maximizers), n = 2
  KMMP.lean                Claims 2.1–2.4 of Kumar–Mohar–Mojallal–Pragada, any rank r
  LemmaC.lean              Lemma C (cloning), n = 2
  LemmaD.lean              Lemma D (A₆ is not a sign pattern of vectors in the plane)
  BlowUp.lean              [JFA, Lemma 2.2] for arbitrary blow-ups
  TheoremA.lean            R₃; Steps 1–4; Theorem A
  PropositionF.lean        Lemma E and Proposition F
  CorollaryG.lean          Corollary G: Π₂ = 4/3
  Main.lean                all statements, in the order of the errata
FranklFuredi/              vendored: formalization of [FF] (unchanged)
ProjectionConstants/       vendored: Foundations/ and ChalmersLewicki/ of [PC] (unchanged)
scripts/CheckAxioms.lean   #print axioms for the main results
```

The library `Grunbaum` has about 5 900 lines; the vendored libraries have about 3 550
(`FranklFuredi`) and 2 250 (`ProjectionConstants`) lines.

## Vendored libraries

To make the repository self-contained, two libraries are included as source code.

* **`FranklFuredi/`** is an unchanged copy of the formalization of [FF]. We use Theorem 1
  (`FranklFuredi.theorem1`): if any four points of a 3-graph span `0` or `2` edges, then it is a
  blow-up `H_S` of their 3-graph `S(6)` (Example 1), or a circle 3-graph (Example 2). We also
  use Proposition 6 (`FranklFuredi.prop6`) for the twin quotient.
* **`ProjectionConstants/`** contains the folders `Foundations/` (without `RankTrace.lean`) and
  `ChalmersLewicki/` of [PC], unchanged; only the root file `ProjectionConstants.lean` was
  rewritten to import exactly these files. We use the definitions of `λ(Y, X)`, `λ(Y)`,
  `λ_𝕜(m, N)` and `λ_𝕜(m)`, the formula of Chalmers and Lewicki
  (`ProjectionConstants.maxRelProjConst_eq_clConst`,
  `ProjectionConstants.maxProjConst_eq_iSup_maxRelProjConst`), orthogonal projection matrices,
  and the commutation of maximizing projections (`ProjectionConstants.commute_of_isMaxOn`).

Some files of `Grunbaum/` are adapted from the folder `Grunbaum/` of [PC], which contains an
earlier formalization of `Π₂ = 4/3` with a different Step 4 and a different cloning argument;
the files say so in their module documentation.

## Where the formal proofs differ from the errata

The statements follow the errata; the following proofs are organized differently.

1. **`π₂` and Fan's maximum principle.** `π₂(M)` is defined as the supremum of
   `uᵀMu + vᵀMv` over orthonormal pairs `u, v`, i.e. of `Tr(MP)` over `P ∈ 𝒫_{2,d}`. Fan's
   maximum principle, `π₂(M) = λ₁(M) + λ₂(M)`, is proved in `Fan.lean`. On an index set with
   fewer than two elements there is no orthonormal pair and `π₂ = 0`; this only concerns the
   degenerate values `Π(2, 0) = Π(2, 1) = 0`.
2. **Lemma B** is proved for `n = 2`, the case used in Theorem A, with `P = uuᵀ + vvᵀ` for any
   maximizing orthonormal pair (in particular for the spectral projection). Part (b) is
   [AMOP, Lemma 3.2]. Where the proofs in [JFA] and [AMOP] use the equality case of von
   Neumann's trace inequality (see Theobald [The75] and Carlsson [Car21]), we use the
   first-order condition that a maximizing orthonormal pair spans an invariant plane
   (`Grunbaum.mulVec_eq_of_isMax`), i.e. `PM = MP`.
3. **KMMP.** Claims 2.1–2.4 of [KMMP] are formalized for arbitrary rank `r ≥ 1` in their
   notation (`U ∈ ℝ^{n×r}` with `UᵀU = I_r`, rows `xᵢ`, `σ(U, w) = ∑ wᵢwⱼ|⟨xᵢ, xⱼ⟩|`). In
   Claim 2.1 the Perron–Frobenius theorem is replaced by the inequality `xᵀBx ≤ |x|ᵀB|x|`, and in
   Claim 2.2 the equality case of the Ky Fan principle by `commute_of_isMaxOn`. Lemma C follows
   from Claim 2.4 together with Lemma B(b), (c).
4. **Blow-ups.** [JFA, Lemma 2.2] is proved for arbitrary blow-ups `S = T(f, f)` in the form
   `X^{|κ|} χ(√D S √D) = X^{|ι|} χ(√D' T √D')`, a consequence of `X^n χ(AB) = X^m χ(BA)`
   for rectangular matrices (`Matrix.charpoly_mul_comm'`). Step 2 then argues as in the errata:
   `λ₂(M) > 0`, so deleting a zero eigenvalue does not change `π₂`.
5. **(FF).** From Theorem 1 of [FF] we first collapse the classes of twins (a twin-free
   quotient) and then show that a twin-free circle 3-graph is `T_{2N+1}` (Remark 1 of [FF] in
   the twin-free case): with representatives in a half-plane, the signs of the points alternate
   along the circular order, and the relabelling `j ↦ j(N + 1) mod (2N + 1)` identifies the
   3-graph with `T_{2N+1}`. The 3-graph `S(6)` is `[A₆]` up to relabelling.
6. **`R_{2N+1}` and certificates.** The block matrix `R_{2N+1}` of [JFA, Section 4.1]
   (`blockR`) is, after relabelling its indices by `p₀, …, p_{2N}` and switching the first
   index, the matrix `polygonMatrix N` with entries `sᵢⱼ = 1` iff `|i − j| ≤ N`
   (`blockR_eq`); the proofs work with `polygonMatrix N`. (R2), (A1) and `S(6) = [A₆]` are
   checked with explicit switchings and relabellings, by `fin_cases` and `decide`
   (no `native_decide`).
7. **Lemma D** uses slopes `σⱼ = det(u₁, uⱼ) / ⟨u₁, uⱼ⟩` relative to `u₁` instead of angles.
8. **Lemma E** is verified by expanding the determinant of the explicit `5 × 5` matrix rather
   than by summing principal minors. **Proposition F** reads off the elementary symmetric
   functions of the eigenvalues by evaluating the characteristic polynomial at `0, ±1, ±2`.

## Building

Toolchain: Lean `v4.34.1`, Mathlib `v4.34.1` (see `lean-toolchain` and `lakefile.toml`).

```bash
lake exe cache get                        # download the Mathlib build cache
lake build                                # about 4 minutes on two cores
lake env lean scripts/CheckAxioms.lean    # axioms of the main results
```

`lake build` builds the three libraries `FranklFuredi`, `ProjectionConstants` and `Grunbaum`.
The library `Grunbaum` is compiled with Mathlib's standard linter set
(`weak.linter.mathlibStandardSet`) and builds without warnings. The output of the axiom check is

```
'Grunbaum.maxProjConst_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'Grunbaum.absProjConst_le_four_thirds' depends on axioms: [propext, Classical.choice, Quot.sound]
'Grunbaum.Errata.chalmers_lewicki' depends on axioms: [propext, Classical.choice, Quot.sound]
...
'Grunbaum.Errata.grunbaum' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## References

* **[JFA]** G. Basso, *Computation of maximal projection constants*, J. Funct. Anal. 277
  (2019), no. 10, 3560–3585, arXiv:1901.07866.
* **[Cor]** G. Basso, *Corrigendum to "Computation of maximal projection constants"*,
  J. Funct. Anal. 287 (2024), no. 5, Paper No. 110491, arXiv:2402.06672.
* **[Err]** G. Basso, *Errata to the single-author papers of Giuliano Basso*, Section 3. 
https://www.researchgate.net/publication/415013493_Errata_to_the_single-author_papers_of_Giuliano_Basso
* **[AMOP]** G. Basso, *Almost minimal orthogonal projections*, Israel J. Math. 243 (2021),
  no. 1, 355–376, arXiv:2001.08698.
* **[CL]** B. L. Chalmers and G. Lewicki, *A proof of the Grünbaum conjecture*, Studia Math.
  200 (2010), no. 2, 103–129.
* **[FF]** P. Frankl and Z. Füredi, *An exact result for 3-graphs*, Discrete Math. 50 (1984),
  323–328.
* **[KMMP]** H. Kumar, B. Mohar, S. A. Mojallal and S. Pragada, *Stability of maximal relative
  projection constants*, preprint (2026), arXiv:2609.03200.
* **[The75]** C. M. Theobald, *An inequality for the trace of the product of two symmetric
  matrices*, Math. Proc. Cambridge Philos. Soc. 77 (1975), 265–267.
* **[Car21]** M. Carlsson, *von Neumann's trace inequality for Hilbert–Schmidt operators*,
  Expo. Math. 39 (2021), no. 1, 149–157.
* K. Fan, *On a theorem of Weyl concerning eigenvalues of linear transformations I*, Proc. Natl.
  Acad. Sci. USA 35 (1949), 652–655.
* **[PC]** *Projection constants in Lean* (G. Basso, Claude), Lean 4 / Mathlib library.

## License

Apache License 2.0, see [`LICENSE`](LICENSE).
