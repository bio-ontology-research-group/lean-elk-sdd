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
import ELKSDD.RangeNorm
import ELKSDD.Stratified
import ELKSDD.SCC
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
#print axioms ELpp.canon_satisfies_strict
#print axioms ELpp.complete_via_canon_strict

-- ============================================================
-- RangeNorm — Path B (BBL 2008 §3.3) range elimination
-- ============================================================
-- The forward kernel `complete_via_canon_strict` is sorry-free.
-- The Path-B reduction (`complete_via_canon_owl2el`) uses sorrys
-- in conservativity proofs; closing them is bounded engineering.
#print axioms RangeNorm.modifyConcept_NominalFree
#print axioms RangeNorm.rangeMarker_inj
#print axioms RangeNorm.rangeMarker_fresh
#print axioms RangeNorm.eliminateRanges_no_range
#print axioms RangeNorm.eliminateRanges_strict
#print axioms RangeNorm.atom_MarkerFree_of_in_O
#print axioms RangeNorm.complete_via_canon_owl2el
#print axioms RangeNorm.complete_via_canon_owl2el_atom
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
-- SCC — Layer 6: signature-based factorization of the closure.
--       The novel SCC compositionality theorem, full IFF form:
--
--         Sat (O₁ ++ O₂) C D  ↔  Sat O₁ C D ∨ Sat O₂ ⊤ ⊥
--
--       under DisjointSigs O₁ O₂, ConceptInSig O₁ C/D, plus
--       NominalFree C/D and OntologyNominalFree O₁/O₂.
--
--       Both directions PROVED:
--         (mp)  monotonicity + global-inconsistency propagation
--         (mpr) product-interpretation construction over
--               α × CanonDom O₂, with eval-invariance lemmas
--               for both signatures.  Holds for full OWL 2 EL
--               (= EL_⊥^+) on the *nominal-free* fragment; no
--               ⊤- or ⊥-side restrictions on GCIs / role axioms.
--
--       OWL 2 EL nominals are added to the *language* (Concept.nom,
--       Interp.indiv, conceptIndividuals, ontologyIndividuals);
--       the formal factorisation extends to the nominal-free
--       fragment.  Full nominal-aware completeness requires the
--       merging-canonical-model construction (Kazakov 2014 §6) —
--       infrastructure is in place; theorem extension is future
--       work.
-- ============================================================
#print axioms SCC.Subontology.refl
#print axioms SCC.Subontology.append_left
#print axioms SCC.Subontology.append_right
#print axioms SCC.Sat_mono
#print axioms SCC.Sat_mono_append_left
#print axioms SCC.Sat_mono_append_right
#print axioms SCC.Sat_factor_easy
#print axioms SCC.DisjointConceptSigs.symm
#print axioms SCC.DisjointRoleSigs.symm
#print axioms SCC.DisjointSigs.symm
#print axioms SCC.ConceptInSig.top
#print axioms SCC.ConceptInSig.bot
#print axioms SCC.ontologyAtoms_append
#print axioms SCC.ontologyRoles_append
#print axioms SCC.mem_ontologyAtoms_append
#print axioms SCC.mem_ontologyRoles_append
#print axioms SCC.axiom_in_self_sig
#print axioms SCC.axiom_in_one_sig
#print axioms SCC.gci_in_O₁_atoms_implies_in_O₁
#print axioms SCC.global_inconsistency_propagates
#print axioms SCC.Sat_factor_refined_mp
-- Hard-direction infrastructure
#print axioms SCC.ConceptInSig.atom_mem
#print axioms SCC.ConceptInSig.conj_left
#print axioms SCC.ConceptInSig.conj_right
#print axioms SCC.ConceptInSig.exist_role
#print axioms SCC.ConceptInSig.exist_inner
#print axioms SCC.prodInterp_atom_O₁
#print axioms SCC.prodInterp_atom_not_O₁
#print axioms SCC.prodInterp_role_O₁
#print axioms SCC.prodInterp_role_not_O₁
#print axioms SCC.eval_prodInterp_O₁
#print axioms SCC.eval_prodInterp_O₂
#print axioms SCC.ConceptInSig_of_AxiomInSig_gci
#print axioms SCC.rinc_role_left_in_sig
#print axioms SCC.rinc_role_right_in_sig
#print axioms SCC.rchain_role₁_in_sig
#print axioms SCC.rchain_role₂_in_sig
#print axioms SCC.rchain_role₃_in_sig
#print axioms SCC.prodInterp_satisfies_O₁_axiom
#print axioms SCC.prodInterp_satisfies_O₂_axiom
#print axioms SCC.prodInterp_satisfies
-- Hard-direction theorem (mpr) and full IFF form
#print axioms SCC.Sat_factor_refined_mpr
#print axioms SCC.Sat_factor_refined

-- ============================================================
-- SDD — BDD with linear-time WMC + Shannon-expansion compile
--       end-to-end correctness
-- ============================================================
#print axioms SDD.wmcCost_eq_size
#print axioms SDD.wmc_linear
#print axioms SDD.compileWithCtx_correct
#print axioms SDD.compile_correct

end ELKSDD
