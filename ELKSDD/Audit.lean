/-
  ELKSDD/Audit.lean
  -----------------
  Print the axiom dependencies of every key theorem in ELKSDD.
  Each `#print axioms` line lists the axioms the proof actually
  uses; if anything beyond `propext`, `Classical.choice`,
  `Quot.sound` (the standard Lean foundation) appears, we have a
  leak.

  Build with `lake build ELKSDD.Audit` and read the `info:` lines.
-/

import ELKSDD.Util
import ELKSDD.MiniEL
import ELKSDD.EL
import ELKSDD.ELpp
import ELKSDD.Normalize
import ELKSDD.Stratified
import ELKSDD.SDD

namespace ELKSDD

-- ============================================================
-- Util
-- ============================================================
#print axioms Util.length_flatMap_map_const
#print axioms Util.length_flatMap_const_length
#print axioms Util.triangle_double_eq
#print axioms Util.triangle_eq

-- ============================================================
-- MiniEL — atomic-subsumption fragment, fully zero-axiom proofs
-- ============================================================
-- Every theorem below should depend on NO axioms whatsoever.
#print axioms MiniEL.el0_sound
#print axioms MiniEL.el0_complete
#print axioms MiniEL.el0_correct
#print axioms MiniEL.example_sat
#print axioms MiniEL.example_entails

-- ============================================================
-- EL — conjunction + existential fragment with ELK soundness
--      and completeness end-to-end
-- ============================================================
#print axioms EL.sound
#print axioms EL.sound_atomSub
#print axioms EL.complete_atomSub
#print axioms EL.sound_disj
#print axioms EL.complete_disj
#print axioms EL.sound_unsat
#print axioms EL.complete_unsat
#print axioms EL.sound_link
#print axioms EL.complete_link
#print axioms EL.complete_via_canon
#print axioms EL.cyclicO_unbounded_sat
#print axioms EL.nestedExist_atom_inj
#print axioms EL.example_entails

-- ============================================================
-- ELpp — full EL_⊥^+ (= EL++ minus nominals/concrete domains):
--        EL with role inclusions R ⊑ S and role chains R₁ ∘ R₂ ⊑ S.
--        ELK 2014 calculus end-to-end (sound + complete via the
--        canonical-model construction of ELK 2014 §3.3).
-- Expected axiom surface: propext, Classical.choice, Quot.sound
-- (Lean foundation axioms only).
-- ============================================================
#print axioms ELpp.sound
#print axioms ELpp.canon_eval
#print axioms ELpp.canon_satisfies
#print axioms ELpp.complete_via_canon
#print axioms ELpp.sound_atomSub
#print axioms ELpp.complete_atomSub
#print axioms ELpp.correct_atomSub
#print axioms ELpp.exampleRH_sat
#print axioms ELpp.exampleRH_entails
#print axioms ELpp.exampleChain_sat
#print axioms ELpp.exampleChain_entails

-- ============================================================
-- Normalize — BBL 2005 normalization (Layer 2, COMPLETE for all
--             7 BBL rules in our EL_⊥^+ fragment):
--               NF1 — vacuous (binary chains by Axiom-type).
--               NF2 — C ⊓ Ĉ ⊑ E   ↦ {Ĉ ⊑ A, C ⊓ A ⊑ E}  fresh A
--               NF3 — ∃r.Ĉ ⊑ D    ↦ {Ĉ ⊑ A, ∃r.A ⊑ D}    fresh A
--               NF4 — ⊥ ⊑ D       ↦ ∅                    no fresh
--               NF5 — Ĉ ⊑ D̂      ↦ {Ĉ ⊑ A, A ⊑ D̂}      fresh A
--               NF6 — B ⊑ ∃r.Ĉ   ↦ {B ⊑ ∃r.A, A ⊑ Ĉ}   fresh A
--               NF7 — B ⊑ C ⊓ D  ↦ {B ⊑ C, B ⊑ D}      no fresh
--             Each fresh-name rule proved via the canonical model-
--             extension witness `extendInterp I A (I.eval Ĉ)`
--             of BBL 2005 §3.1.  The shared infrastructure:
--               extendInterp                 — interpretation extender
--               extendInterp_at_self         — A^I' = P x at self
--               eval_extendInterp_of_fresh   — eval invariant
--               satisfiesAxiom_extendInterp_of_fresh — axiom invariant
-- ============================================================
-- NF7 (no fresh names)
#print axioms Normalize.applyNF7_satisfies_orig
#print axioms Normalize.orig_satisfies_applyNF7
#print axioms Normalize.applyNF7_conservative
#print axioms Normalize.applyNF7_entails_iff

-- NF4 (drop tautology)
#print axioms Normalize.gci_bot_trivially_satisfied
#print axioms Normalize.applyNF4_satisfies_orig
#print axioms Normalize.orig_satisfies_applyNF4
#print axioms Normalize.applyNF4_conservative
#print axioms Normalize.applyNF4_entails_iff

-- Fresh-name infrastructure
#print axioms Normalize.freshAtomFor_fresh
#print axioms Normalize.freshAtomFor_not_in_ontologyAtoms
#print axioms Normalize.eval_extendInterp_of_fresh
#print axioms Normalize.extendInterp_at_self
#print axioms Normalize.satisfiesAxiom_extendInterp_of_fresh

-- NF5 (canonical fresh-name rule)
#print axioms Normalize.applyNF5OneFresh_implies_orig
#print axioms Normalize.orig_extends_to_applyNF5OneFresh
#print axioms Normalize.applyNF5OneFresh_consequence_via_extend
#print axioms Normalize.orig_consequence_via_applyNF5OneFresh

-- NF6 (existential RHS with fresh atom)
#print axioms Normalize.applyNF6OneFresh_implies_orig
#print axioms Normalize.orig_extends_to_applyNF6OneFresh

-- NF2 (conjunctive LHS with one complex side)
#print axioms Normalize.applyNF2OneFresh_implies_orig
#print axioms Normalize.orig_extends_to_applyNF2OneFresh

-- NF3 (existential LHS with complex inner)
#print axioms Normalize.applyNF3OneFresh_implies_orig
#print axioms Normalize.orig_extends_to_applyNF3OneFresh

-- NF1 (vacuous in our binary-chain Axiom representation)
#print axioms Normalize.rchain_already_in_nf1

-- ============================================================
-- Stratified — Layers 4-5: time-stamped Clark completion of the
--              EL_⊥^+ calculus.  `SatAt O k C D` makes the
--              derivation depth explicit; `Sat_iff_SatAt` shows
--              every closed atom has a finite derivation depth,
--              witnessing fixpoint convergence of the iterative
--              completion procedure.
-- ============================================================
#print axioms Stratified.SatAt_succ
#print axioms Stratified.SatAt_mono
#print axioms Stratified.Sat_to_SatAt
#print axioms Stratified.SatAt_to_Sat
#print axioms Stratified.Sat_iff_SatAt
#print axioms Stratified.Sat_iff_SatUpTo
#print axioms Stratified.IsFixpointDepth_imp_IsClosedDepth

-- ============================================================
-- SDD — BDD with linear-time WMC + Shannon-expansion compile
--       end-to-end correctness
-- ============================================================
#print axioms SDD.wmcCost_eq_size
#print axioms SDD.wmc_linear
#print axioms SDD.compileWithCtx_correct
#print axioms SDD.compile_correct

end ELKSDD
