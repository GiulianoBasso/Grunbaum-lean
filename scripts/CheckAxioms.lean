-- Run with `lake env lean scripts/CheckAxioms.lean` after `lake build`.
-- Every result below depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`
-- (no `sorryAx`, no `Lean.ofReduceBool`).
import Grunbaum

open Grunbaum.Errata

#print axioms Grunbaum.maxProjConst_two
#print axioms Grunbaum.absProjConst_le_four_thirds
#print axioms chalmers_lewicki
#print axioms fan
#print axioms fact_R1
#print axioms fact_R2
#print axioms fact_A1
#print axioms fact_FF
#print axioms theorem_A
#print axioms theorem_A'
#print axioms twoGraph_R_JFA
#print axioms lemma_B
#print axioms lemma_C
#print axioms lemma_D
#print axioms step_1
#print axioms step_2
#print axioms step_3
#print axioms step_4
#print axioms blow_up
#print axioms kmmp_cloning
#print axioms lemma_E
#print axioms proposition_F
#print axioms corollary_G
#print axioms grunbaum
