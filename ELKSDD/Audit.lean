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
import ELKSDD.Merging
import ELKSDD.OWL2EL
import ELKSDD.ELKBoundary
import ELKSDD.DISPONTE
import ELKSDD.Complexity
import ELKSDD.SatComplexity
import ELKSDD.Saturation
import ELKSDD.Compilation
import ELKSDD.Stratified
import ELKSDD.SCC
import ELKSDD.SDD
import ELKSDD.MOOSE
import ELKSDD.SatFactorGeneral
import ELKSDD.DISPONTERat

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
-- (Lean foundation axioms only) — sorry-free across this entire
-- module (range and chain are gated together via RangeChainSafe
-- on the completeness theorems; the strict variants exclude range
-- entirely and remain unconditionally sorry-free).
-- ============================================================
#print axioms ELpp.sound
#print axioms ELpp.canon_eval
#print axioms ELpp.canon_satisfies
#print axioms ELpp.complete_via_canon
#print axioms ELpp.canon_satisfies_strict
#print axioms ELpp.complete_via_canon_strict
-- LHS-nominal extension (ClassAssertion-style: gci (nom i) D allowed)
#print axioms ELpp.AxiomNominalFree_imp_NomLHS
#print axioms ELpp.OntologyNominalFree_imp_NomLHS
#print axioms ELpp.canon_indiv_eq
#print axioms ELpp.canon_satisfies_nomLHS
#print axioms ELpp.complete_via_canon_nomLHS
-- Shallow-exist-nominal RHS extension (ObjectPropertyAssertion-style:
-- gci C (∃R.(nom j)) allowed, range axioms forbidden in this fragment)
#print axioms ELpp.AxiomNomLR_no_range
#print axioms ELpp.canon_satisfies_nomLR
#print axioms ELpp.complete_via_canon_nomLR

-- ============================================================
-- RangeNorm — Path B (BBL 2008 §3.3) range elimination
-- ============================================================
-- All RangeNorm theorems are sorry-free.
--
-- The conservativity helpers (Sat_to_eliminated, Sat_from_eliminated,
-- Entails_to_eliminated) are closed for the NoRange degenerate case
-- (where eliminateRanges = id).  The full-range conservativity bodies
-- are no longer needed: Path-A `ELpp.complete_via_canon` is sorry-free
-- under `RangeChainSafe` and supersedes the syntactic-elimination
-- detour for ontologies that actually have range axioms.
--
-- The Path-B exports (complete_via_canon_owl2el, _atom) are now
-- direct wrappers around Path-A.
#print axioms RangeNorm.modifyConcept_NominalFree
#print axioms RangeNorm.rangeMarker_inj
#print axioms RangeNorm.rangeMarker_fresh
#print axioms RangeNorm.eliminateRanges_no_range
#print axioms RangeNorm.eliminateRanges_strict
#print axioms RangeNorm.atom_MarkerFree_of_in_O
#print axioms RangeNorm.hasRange_iff
#print axioms RangeNorm.Sat_modify_imp_orig
-- NoRange degenerate-case helpers (sorry-free, baseline for Path B narrative)
#print axioms RangeNorm.hasRange_false_under_no_range
#print axioms RangeNorm.modifyConcept_id_under_no_range
#print axioms RangeNorm.markerAxioms_nil_under_no_range
#print axioms RangeNorm.eliminateRanges_eq_under_no_range
#print axioms RangeNorm.Sat_to_eliminated
#print axioms RangeNorm.Sat_from_eliminated
#print axioms RangeNorm.Entails_to_eliminated
-- Path-B exports (now Path-A wrappers, sorry-free under RangeChainSafe)
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

-- ============================================================
-- Merging — Kazakov 2014 §6 merging quotient canonical model.
--           Adds shapes 1-4 (gci with nominals on either side or
--           inside ∃R.nom) and HasKey.  The quotient setoid uses
--           Sat.nom_symm + transitivity; HasKey uses Sat.hasKey_apply
--           (the new rule from ELpp).  Restricted to Shallow concepts
--           (no deep ∃-targets with non-nominal fillers).
-- ============================================================
#print axioms ELpp.nomCls_eq_iff
#print axioms ELpp.nomCls_sound
#print axioms ELpp.nomCls_exact
#print axioms ELpp.sat_nomLHS_respects
#print axioms ELpp.sat_nomRHS_respects
#print axioms ELpp.sat_existNomRHS_respects
#print axioms ELpp.sat_existNomBoth_respects
#print axioms ELpp.mergedCanon_indiv_eq
#print axioms ELpp.merged_canon_eval
#print axioms ELpp.mergedCanon_satisfies
#print axioms ELpp.complete_via_mergedCanon_regular
#print axioms ELpp.complete_via_mergedCanon_nom

-- ============================================================
-- OWL2EL — unified user-facing dispatch over the five fragment
--          completeness theorems (NF / nomLHS / nomLR / strict /
--          merge).  Soundness is uniform; completeness dispatches
--          on a fragment witness.
-- ============================================================
#print axioms ELpp.sound_owl2el
#print axioms ELpp.complete_owl2el
#print axioms ELpp.correct_owl2el

-- ============================================================
-- ELKBoundary — Sat ↔ ∀-quantified-over-models indicator semantics.
--               The boundary between calculus and model theory.
-- ============================================================
#print axioms ELpp.sat_imp_model
#print axioms ELpp.satIndicator_iff
#print axioms ELpp.satIndicator_isModel
#print axioms ELpp.boundary_theorem
#print axioms ELpp.sat_eq_minimal_model

-- ============================================================
-- DISPONTE — Riguzzi 2015 distribution-semantics correspondence.
--            DISPONTE WMC == SDD WMC over the per-axiom inclusion
--            world distribution (Nat-valued; Mathlib lift to ℝ is
--            mechanical follow-on).
-- ============================================================
#print axioms ELpp.selectedAxioms_subset
#print axioms ELpp.sat_world_mono
#print axioms ELpp.disponte_eq_wmc_of_correctness
#print axioms ELpp.worldWeight_uniform

-- ============================================================
-- Complexity — Shannon-tree SDD size bound.  WMC time = O(|tree|)
--              (linear in the SDD).
-- ============================================================
#print axioms SDD.compileWithCtx_size_bound
#print axioms SDD.compile_size_bound
#print axioms SDD.wmc_compile_time_bound

-- ============================================================
-- SatComplexity — polynomial closure-size bound on the new
--                 inductive Sat (shapes 1-4 + HasKey + range +
--                 reflexive + Self).  Per-shape exact lengths:
--                   atomEnum       n²
--                   linkEnum       n²·r
--                   rangeLinkEnum  n³·r
--                   reflEnum       n·r
--                   selfEnum       n·r
--                 Total: ≤ 5·n³·(r+1).
-- ============================================================
#print axioms ELpp.atomEnum_length
#print axioms ELpp.linkEnum_length
#print axioms ELpp.rangeLinkEnum_length
#print axioms ELpp.reflEnum_length
#print axioms ELpp.selfEnum_length
#print axioms ELpp.boundedAtomSet_length
#print axioms ELpp.boundedAtomSet_polynomial
#print axioms ELpp.sat_named_atom_in_bound
#print axioms ELpp.sat_named_atom_cardinality_bound
#print axioms ELpp.sat_closure_total_polynomial_bound

-- ============================================================
-- Saturation — saturation termination theorem: a polynomial-size
--              list contains exactly the Sat-derivable named atoms
--              over Sub(O).  Stratified-depth corollary via
--              Sat_iff_SatAt.  Cut elimination as the canonical
--              syntactic sharpening is documented as follow-on.
-- ============================================================
#print axioms ELpp.derivableClosure_length
#print axioms ELpp.derivableClosure_sound
#print axioms ELpp.derivableClosure_complete
#print axioms ELpp.saturation_terminates
#print axioms ELpp.sat_iff_in_derivableClosure
#print axioms ELpp.bounded_sat_depth
#print axioms ELpp.mem_derivableClosure_iff
#print axioms ELpp.sat_polynomial_decidable

-- ============================================================
-- Compilation — verified ELK→SDD compilation.  compileSat O C D
--               is a Shannon-expanded Tree (DispAtom O) such that
--               model t M ↔ Sat (selectedAxioms O M) C D for every
--               world M.  Closes the SDDEncodesQuery hypothesis;
--               the conditional DISPONTE correspondence reduces
--               disponte_eq_wmc_of_correctness to the standard
--               SDD WMC sum-form identity (h_wmc_form, follow-on).
-- ============================================================
#print axioms ELpp.compileSatAux_correct
#print axioms ELpp.compileSat_correct
#print axioms ELpp.exists_sdd_encoding
#print axioms ELpp.compileSatAux_size_bound
#print axioms ELpp.compileSat_size_bound
#print axioms ELpp.compileSat_models_iff_sat
#print axioms ELpp.compileSat_disponte_eq_of_wmc_form
#print axioms ELpp.disponte_eq_wmc_via_compileSat
-- A6: tighter SDD size bounds — exact size + essential-variable polynomial bound.
#print axioms ELpp.compileSatAux_size_eq
#print axioms ELpp.compileSat_size_eq
#print axioms ELpp.compileSat_wmcCost_eq
#print axioms ELpp.sat_invariant_multi
#print axioms ELpp.essential_compile_correct
#print axioms ELpp.essential_polynomial_bound

-- ============================================================
-- CompilationWMC — Shannon-recursive WMC + UNCONDITIONAL DISPONTE
--                  correspondence.  Bridges shannonSatSum to
--                  enumerateWorlds via Perm; closes the final
--                  unconditional theorem
--                  `wmc_compileSat_eq_disponteWMC`.
-- ============================================================
#print axioms ELpp.wmc_compileSatAux_eq
#print axioms ELpp.wmc_compileSat_eq_shannonSatSum
#print axioms ELpp.Perm_foldr_add_eq
#print axioms ELpp.Perm_foldr_add_eq_fn
#print axioms ELpp.shannonSatSum_eq_foldr_extensionList
#print axioms ELpp.weightAlong_finRange_eq_worldWeight
#print axioms ELpp.extensionList_length
#print axioms ELpp.enumerateWorlds_length
#print axioms ELpp.mem_extensionList_finRange
#print axioms ELpp.mem_enumerateWorlds
#print axioms ELpp.extensionList_Nodup
#print axioms ELpp.enumerateWorlds_Nodup
#print axioms ELpp.extensionList_finRange_perm_enumerateWorlds
#print axioms ELpp.wmc_compileSat_eq_disponteWMC
#print axioms ELpp.compileSat_disponte_correspondence
#print axioms ELpp.exists_disponte_correspondence

-- ============================================================
-- MOOSE — bow-tied paper-citation theorems for the inference
--         pipeline: end-to-end correctness, polynomial-time Sat
--         decision, and a combined factorisation of the entire
--         MOOSE algorithm.
-- ============================================================
#print axioms ELpp.moose_inference_correct
#print axioms ELpp.sat_decision_polynomial
#print axioms ELpp.moose_pipeline_complete
-- (3): SCC compositional theorems at the Sat level.
#print axioms ELpp.scc_sat_factor
#print axioms ELpp.scc_sat_factor_symm
#print axioms ELpp.moose_scc_summary
-- (B): multi-component (k-SCC) factorization.
#print axioms ELpp.joint_consistent_pair
#print axioms ELpp.scc_sat_factor_k
-- (E): rational-valued DISPONTE correspondence (Lean core only, no Mathlib).
#print axioms ELpp.wmc_compileSat_eq_disponteWMC_rat
#print axioms ELpp.compileSat_disponte_correspondence_rat
#print axioms ELpp.exists_disponte_correspondence_rat
-- (C): generalized Sat-factor — unblocks per-world Sat factor and WMC SCC.
#print axioms ELpp.prodInterp_satisfies_actual_O₁_axiom
#print axioms ELpp.prodInterp_satisfies_actual_O₂_axiom
#print axioms ELpp.prodInterp_satisfies_actual
#print axioms ELpp.Sat_factor_refined_general

end ELKSDD
