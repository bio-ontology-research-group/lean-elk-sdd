/-
  ELKSDD/SROIQAudit.lean
  -----------------------
  Axiom-budget audit for the SROIQ-direction Lean modules.  Every
  ``#print axioms`` line below must report at most
  ``propext, Classical.choice, Quot.sound`` (the standard Lean
  foundational axioms); anything more is a leak.

  Build with ``lake env lean ELKSDD/SROIQAudit.lean`` and read the
  ``info:`` lines.
-/

import ELKSDD.SROIQ
import ELKSDD.ALCHOQ
import ELKSDD.ALCHOQCompleteness
import ELKSDD.SROIQCompleteness
import ELKSDD.ALCHOIQContext
import ELKSDD.SROIQSkolem
import ELKSDD.SROIQCanonical
import ELKSDD.SROIQSkolemCanonical
import ELKSDD.SROIQContextBridge

namespace ELKSDD

-- ============================================================
-- ALCHOQ: full set-extension semantics + sound CB calculus, plus
-- the classical extension with full soundness.
-- ============================================================
#print axioms ALCHOQ.sat_sound
#print axioms ALCHOQ.satC_sound
#print axioms ALCHOQ.Interp.eval_nom_iff
#print axioms ALCHOQ.Interp.eval_atLeast_zero
#print axioms ALCHOQ.Interp.eval_atMost_zero
#print axioms ALCHOQ.Interp.eval_atLeast_one_iff_exist

-- ============================================================
-- SROIQ: RBox semantics + per-feature soundness lemmas.
-- ============================================================
#print axioms SROIQ.incl_sound
#print axioms SROIQ.trans_sound
#print axioms SROIQ.sym_sound
#print axioms SROIQ.asym_sound
#print axioms SROIQ.refl_sound
#print axioms SROIQ.irrefl_sound
#print axioms SROIQ.inv_sound
#print axioms SROIQ.disj_sound
#print axioms SROIQ.chain_two_sound
#print axioms SROIQ.trans_iff_chain
#print axioms SROIQ.sym_iff_self_inverse
#print axioms SROIQ.Interp.nom_singleton
#print axioms SROIQ.Interp.has_self_iff
#print axioms SROIQ.universal_implies_role_features

-- ============================================================
-- SROIQ classical extension: full soundness, completeness deferred.
-- ============================================================
#print axioms SROIQ.satC_sound
#print axioms SROIQ.satC_of_alchoq

-- ============================================================
-- Tena-Cucala ALCHOIQ+ context-structure calculus
-- (DPhil thesis, Oxford 2019, Chapters 5-6).
-- Headline soundness + completeness results.
-- ============================================================
#print axioms ALCHOIQContext.step_sound
#print axioms ALCHOIQContext.deriv_sound
#print axioms ALCHOIQContext.completeness_compat
#print axioms ALCHOIQContext.TenaCucalaCompleteness

-- ============================================================
-- SROIQ Skolem completeness: empty-RBox case (PROVED), and the
-- generalised theorem with canonical-RBox hypothesis (PROVED).
-- ============================================================
#print axioms SROIQ.sroiq_satC_complete_skolFragment_emptyRBox
#print axioms SROIQ.sroiq_satC_complete_skolFragment_canonical
#print axioms SROIQ.sroiq_canonical_satisfies_ontology
#print axioms SROIQ.sroiq_canonical_satisfies_emptyRBox

-- ============================================================
-- SROIQ canonical-model construction over SROIQ.SatC.
-- The carrier-type construction rebuilt so types are closed under
-- SROIQ-only rules (roleIncl_univ, roleChain_two, roleTrans_exist,
-- roleTrans_univ, roleIncl_hasSelf).
-- ============================================================
#print axioms SROIQ.consistent
#print axioms SROIQ.alchoq_consistent_of_sroiq
#print axioms SROIQ.bot_not_mem
#print axioms SROIQ.top_mem
#print axioms SROIQ.mem_xor_neg
#print axioms SROIQ.type_closure
#print axioms SROIQ.consistent_chain_union
#print axioms SROIQ.lindenbaum_max
#print axioms SROIQ.lindenbaum_max_closed
#print axioms SROIQ.lindenbaum
#print axioms SROIQ.c_negD_consistent
#print axioms SROIQ.type_nonempty_of_consistent

-- ============================================================
-- SROIQ Skolem canonical model (steps a-d from the rebuild plan).
-- ============================================================
#print axioms SROIQ.CanDom.succ_ne_parent
#print axioms SROIQ.satC_nom_to_conjList_of_noms
#print axioms SROIQ.nom_consistent_of_cons
#print axioms SROIQ.successor_consistent
#print axioms SROIQ.carrierType
#print axioms SROIQ.carrierSet
#print axioms SROIQ.succ_carrier_contains_C
#print axioms SROIQ.succ_carrier_propagates_univ
#print axioms SROIQ.nomElt_carrier_contains
#print axioms SROIQ.skolCanonical
#print axioms SROIQ.skolCanonical_ext_ind
#print axioms SROIQ.skolCanonical_satisfies_roleIncl
#print axioms SROIQ.skolCanonical_univ_trans

-- Truth lemma and headline SROIQ completeness theorems.
#print axioms SROIQ.conj_mem
#print axioms SROIQ.skol_succ_in_ext_role
#print axioms SROIQ.skol_eval_hasSelf_iff
#print axioms SROIQ.skol_eval_exist_iff
#print axioms SROIQ.skol_eval_univ_iff
#print axioms SROIQ.skol_canonical_eval_iff
#print axioms SROIQ.skol_canonical_satisfies
#print axioms SROIQ.sroiq_satC_complete_skolFragment
#print axioms SROIQ.sroiq_satC_complete_skolFragment_roleInclOnly
#print axioms SROIQ.skolCanonical_satisfies_refl
#print axioms SROIQ.sroiq_satC_complete_skolFragment_inclReflOnly
#print axioms SROIQ.skolCanonical_chain_two_univ
-- New role-axis canonical satisfaction (full irrefl, partial asym/disj
-- on self-loops, k-ary chain univ-propagation):
#print axioms SROIQ.skolCanonical_satisfies_irrefl
#print axioms SROIQ.skolCanonical_satisfies_asym_self
#print axioms SROIQ.skolCanonical_satisfies_disj_self
#print axioms SROIQ.skolCanonical_chain_n_univ
#print axioms SROIQ.univChain_propagates
#print axioms SROIQ.sroiq_satC_complete_skolFragment_inclReflIrreflOnly

-- ============================================================
-- Tena-Cucala context-structure bridge: full SROIQ completeness
-- conditional on the published thesis-2 (Tena-Cucala, 2021).
-- ============================================================
#print axioms ALCHOIQContext.TenaCucalaCompleteness
#print axioms ALCHOIQContext.CompositeRefutationLemma
#print axioms ALCHOIQContext.tc_from_refutation_lemma
#print axioms ALCHOIQContext.reducesToNominal
#print axioms ALCHOIQContext.HerbrandModel.refutesQuery
#print axioms ALCHOIQContext.coreClause
#print axioms ALCHOIQContext.StepCore
#print axioms ALCHOIQContext.step_core_sound
#print axioms ALCHOIQContext.StepIneq
#print axioms ALCHOIQContext.step_ineq_sound
#print axioms ALCHOIQContext.MonoExt
#print axioms ALCHOIQContext.mono_ext_sound
#print axioms ALCHOIQContext.MonoRestr
#print axioms ALCHOIQContext.mono_restr_sound
#print axioms ALCHOIQContext.subsumes
#print axioms ALCHOIQContext.StepElim
#print axioms ALCHOIQContext.step_elim_sound
#print axioms SROIQ.sroiq_complete_via_TC
#print axioms SROIQ.sroiq_iff_via_TC
#print axioms SROIQ.trivialContextStructure
#print axioms SROIQ.trivial_sound
#print axioms SROIQ.trivial_saturated
#print axioms SROIQ.trivialBridge
#print axioms SROIQ.sroiq_complete_via_CRL
#print axioms SROIQ.sroiq_iff_via_CRL
#print axioms SROIQ.sroiq_complete_via_canonical
#print axioms SROIQ.sroiq_complete_dispatch

end ELKSDD
