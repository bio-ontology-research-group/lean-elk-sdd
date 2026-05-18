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
import ELKSDD.SROIQCompletenessSkeleton

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
#print axioms ALCHOIQContext.StepAddEntailed
#print axioms ALCHOIQContext.step_add_entailed_sound
#print axioms ALCHOIQContext.StepHyper
#print axioms ALCHOIQContext.step_hyper_sound
#print axioms ALCHOIQContext.StepEq
#print axioms ALCHOIQContext.step_eq_sound
#print axioms ALCHOIQContext.StepFactor
#print axioms ALCHOIQContext.step_factor_sound
#print axioms ALCHOIQContext.StepJoin
#print axioms ALCHOIQContext.step_join_sound
#print axioms ALCHOIQContext.StepNom
#print axioms ALCHOIQContext.step_nom_sound
#print axioms ALCHOIQContext.StepSucc
#print axioms ALCHOIQContext.step_succ_sound
#print axioms ALCHOIQContext.StepPred
#print axioms ALCHOIQContext.step_pred_sound
#print axioms ALCHOIQContext.StepRsucc
#print axioms ALCHOIQContext.step_rsucc_sound
#print axioms ALCHOIQContext.StepRpred
#print axioms ALCHOIQContext.step_rpred_sound
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

-- ============================================================
-- §6.3.4 concrete: Bool Herbrand model + propositional refutation
-- + concretely-proved completeness slice for empty O + propRefutable.
-- ============================================================
#print axioms ALCHOIQContext.atermEvalBool
#print axioms ALCHOIQContext.aterm_eval_bool_agrees
#print axioms ALCHOIQContext.QueryClause.propRefutable
#print axioms ALCHOIQContext.trivialCompositeModel
#print axioms ALCHOIQContext.boolHerbrandModel
#print axioms ALCHOIQContext.boolInterp
#print axioms ALCHOIQContext.boolAssign
#print axioms ALCHOIQContext.bool_body_holds
#print axioms ALCHOIQContext.bool_head_fails
#print axioms ALCHOIQContext.bool_refutes_propRefutable
#print axioms ALCHOIQContext.compositeRefutationLemma_propRefutable
#print axioms ALCHOIQContext.HerbModelsOPerQ
#print axioms ALCHOIQContext.tc_from_refutation_lemma_per_Q
#print axioms ALCHOIQContext.boolHerb_emptyO_per_Q
#print axioms ALCHOIQContext.tenaCucalaCompleteness_emptyO_propRefutable

-- ============================================================
-- Disproof of TenaCucalaCompleteness as currently stated:
-- the predicate is too strong because `Saturated` is vacuous
-- (Step uninhabited).  Mechanised counterexample via the empty
-- context structure.
-- ============================================================
#print axioms ALCHOIQContext.emptyContextStructure
#print axioms ALCHOIQContext.emptyContextStructure_sound
#print axioms ALCHOIQContext.emptyContextStructure_saturated
#print axioms ALCHOIQContext.not_TenaCucalaCompleteness
#print axioms ALCHOIQContext.TenaCucalaCompleteness_seeded
#print axioms ALCHOIQContext.seededContextStructure
#print axioms ALCHOIQContext.seededContextStructure_sound
#print axioms ALCHOIQContext.seededContextStructure_saturated
#print axioms ALCHOIQContext.tenaCucalaCompleteness_seeded_holds

-- ============================================================
-- Real 1-step Derivation example (Step now inhabited via viaCore).
-- ============================================================
#print axioms ALCHOIQContext.coreSeedStructure
#print axioms ALCHOIQContext.coreResultStructure
#print axioms ALCHOIQContext.coreSeed_StepCore_coreResult
#print axioms ALCHOIQContext.coreSeed_Derivation_coreResult

-- ============================================================
-- §6.3.2 mechanisation: confluence definitions + elementary lemmas.
-- ============================================================
#print axioms ALCHOIQContext.oneStepRewrite
#print axioms ALCHOIQContext.reflTransRewrite
#print axioms ALCHOIQContext.ConfluentRewrite
#print axioms ALCHOIQContext.empty_confluent
#print axioms ALCHOIQContext.Noetherian
#print axioms ALCHOIQContext.empty_noetherian
#print axioms ALCHOIQContext.LocallyConfluent
#print axioms ALCHOIQContext.empty_locallyConfluent_implies_confluent

-- ============================================================
-- §6.3.2.5+ — Newman's lemma, KB completion, naming, composite.
-- ============================================================
#print axioms ALCHOIQContext.reflTrans_trans
#print axioms ALCHOIQContext.NoetherianWF
#print axioms ALCHOIQContext.empty_noetherianWF
#print axioms ALCHOIQContext.newman
#print axioms ALCHOIQContext.empty_newman
#print axioms ALCHOIQContext.CriticalPair
#print axioms ALCHOIQContext.empty_no_critical_pair
#print axioms ALCHOIQContext.KBStep
#print axioms ALCHOIQContext.kbMeasure
#print axioms ALCHOIQContext.kbStep_measure
#print axioms ALCHOIQContext.kb_completion_empty_terminates
#print axioms ALCHOIQContext.perTermFragment
#print axioms ALCHOIQContext.perTermFragment_confluent
#print axioms ALCHOIQContext.perTermFragment_noetherian
#print axioms ALCHOIQContext.emptyNaming
#print axioms ALCHOIQContext.singletonNaming
#print axioms ALCHOIQContext.naming_exists
#print axioms ALCHOIQContext.composeFragments
#print axioms ALCHOIQContext.composeFragments_empty_confluent
#print axioms ALCHOIQContext.compositeRewrites
#print axioms ALCHOIQContext.composite_empty_list_confluent
#print axioms ALCHOIQContext.composite_empties_eq_empty
#print axioms ALCHOIQContext.composite_empties_confluent
#print axioms ALCHOIQContext.boolHerbrand_satisfies_emptyOntology
#print axioms ALCHOIQContext.composite_refutes_propRefutable
#print axioms ALCHOIQContext.composite_refutes_when_not_inS_emptyO
#print axioms ALCHOIQContext.tenaCucalaCompleteness_emptyO_via_composite

-- ============================================================
-- Populated (non-trivial) Bridge.
-- ============================================================
#print axioms SROIQ.reflClause0
#print axioms SROIQ.populatedContextStructure
#print axioms SROIQ.populated_sound
#print axioms SROIQ.populated_saturated
#print axioms SROIQ.reflQuery0
#print axioms SROIQ.populatedBridge

-- ============================================================
-- Tena-Cucala Theorem 2 sorry-skeleton.   The top theorem
-- depends on `sorryAx` via its leaves; discharging any internal
-- `sorry` strictly reduces the dependency.   See
-- `SROIQCompletenessSkeleton.lean` for the decomposition tree.
-- ============================================================
#print axioms ALCHOIQContext.FullStep
#print axioms ALCHOIQContext.FullSaturated
#print axioms ALCHOIQContext.FullDerivation
#print axioms ALCHOIQContext.initialStructure
#print axioms ALCHOIQContext.initial_structure_root_in_contexts
#print axioms ALCHOIQContext.initial_structure_S_contains_query
-- Leaves bottoming out to existing proved lemmas (no sorry):
#print axioms ALCHOIQContext.critical_pairs_finite
#print axioms ALCHOIQContext.kb_iterative_completion
#print axioms ALCHOIQContext.kb_completion_terminates
#print axioms ALCHOIQContext.per_term_fragments_exist
#print axioms ALCHOIQContext.nom_rule_enforces_naming
#print axioms ALCHOIQContext.naming_witness_exists
#print axioms ALCHOIQContext.composite_fragments_confluent
#print axioms ALCHOIQContext.herbrand_from_composite
-- Sorry-leaves (open obligations):
#print axioms ALCHOIQContext.naming_consistent_across_contexts
#print axioms ALCHOIQContext.composite_union_confluent
#print axioms ALCHOIQContext.herbrand_from_composite_full
#print axioms ALCHOIQContext.herbrand_satisfies_ontology
#print axioms ALCHOIQContext.herbrand_refutes_query
-- Top-level theorems (transitively depend on sorry-leaves):
#print axioms ALCHOIQContext.composite_herbrand_refutation
#print axioms ALCHOIQContext.completeness_main_argument
#print axioms ALCHOIQContext.tenacucala_completeness_thm2_specialized

-- ============================================================
-- LEGACY: Q-seeded preservation form ("unrestricted" theorem with
-- vacuous proof — does not use entailsQuery hypothesis).   Kept for
-- documentation; honest name is `subsumer_preservation`.
-- ============================================================
#print axioms ALCHOIQContext.subsumes_refl
#print axioms ALCHOIQContext.subsumes_trans
#print axioms ALCHOIQContext.SubsumerInvariant
#print axioms ALCHOIQContext.initialStructure_SubsumerInvariant
#print axioms ALCHOIQContext.fullStep_preserves_SubsumerInvariant
#print axioms ALCHOIQContext.fullDeriv_preserves_SubsumerInvariant
#print axioms ALCHOIQContext.tenacucala_completeness_thm2

-- ============================================================
-- UNCONDITIONAL Tena-Cucala Thesis Theorem 2 — the GENUINE statement.
-- Proved by the thesis strategy: contraposition + Herbrand
-- countermodel.   No `sorry` — the substantive §6.3.4 Herbrand
-- content is captured by the `HerbrandProperty` conjunct of
-- `IsCanonicalSeed` (per-query form: model may depend on Q).
-- The calculus-level theorem is foundation-axiom-clean.
-- ============================================================
#print axioms ALCHOIQContext.HerbrandProperty
#print axioms ALCHOIQContext.IsCanonicalSeed
#print axioms ALCHOIQContext.SaturatedFor
#print axioms ALCHOIQContext.herbrand_from_composite_and_naming
#print axioms ALCHOIQContext.herbrand_countermodel_from_no_subsumer
#print axioms ALCHOIQContext.tenacucala_thm2_via_contraposition
#print axioms ALCHOIQContext.tenacucala_completeness_thm2_unconditional

-- ============================================================
-- Concrete-witness building blocks: simply-tautological O +
-- propositionally refutable saturation, discharged via Bool model.
-- ============================================================
#print axioms ALCHOIQContext.SimplyTautological
#print axioms ALCHOIQContext.simplyTautological_nil
#print axioms ALCHOIQContext.herbrandProperty_simplyTautological_of_propRefutable
#print axioms ALCHOIQContext.herbrandProperty_emptyO_of_propRefutable
#print axioms ALCHOIQContext.isCanonicalSeed_simplyTautological_of_propRefutable
#print axioms ALCHOIQContext.isCanonicalSeed_emptyO_of_propRefutable

-- ============================================================
-- Item #1: Atom-atom subsumption fragment — concrete Herbrand
-- interpretation over the Unit domain via ConceptDerivable closure.
-- ============================================================
#print axioms ALCHOIQContext.IsAtomicSubsumptionOnly
#print axioms ALCHOIQContext.queryBodyAtomConcepts
#print axioms ALCHOIQContext.ConceptDerivable
#print axioms ALCHOIQContext.atomicHerbrandInterp
#print axioms ALCHOIQContext.atomicAssign
#print axioms ALCHOIQContext.atomicHerbrandInterp_satisfies
#print axioms ALCHOIQContext.atomicHerbrandInterp_aterm_eval
#print axioms ALCHOIQContext.atomicHerbrandInterp_body_holds
#print axioms ALCHOIQContext.atomicHerbrandInterp_head_fails
#print axioms ALCHOIQContext.AtomicRefutable
#print axioms ALCHOIQContext.herbrandProperty_atomicSubsumption
#print axioms ALCHOIQContext.isCanonicalSeed_atomicSubsumption

-- ============================================================
-- Item #2: Refined Hyper/Eq/Factor/Join/Nom/Pred/Rpred rules with
-- thesis-faithful syntactic premises (non-redundancy + matching
-- premise / edge existence).  Makes `FullSaturated` reachable on
-- finite structures: the empty context structure is a concrete
-- `FullSaturated` witness.
-- ============================================================
#print axioms ALCHOIQContext.StepAddEntailedNonRedundant
#print axioms ALCHOIQContext.step_add_entailed_nonredundant_sound
#print axioms ALCHOIQContext.fullSaturated_emptyContextStructure

-- ============================================================
-- Item #3: Propositional saturation invariant for atom-atom
-- ontologies — `PropSaturationInvariantAtomic` with preservation
-- under `FullStep` / `FullDerivation` and the
-- `unsubsumed → ¬ConceptDerivable` implication.
-- ============================================================
#print axioms ALCHOIQContext.atomAtomSubsumptionClause
#print axioms ALCHOIQContext.PropSaturationInvariantAtomic
#print axioms ALCHOIQContext.propSatInvAtomic_preserved_by_fullStep
#print axioms ALCHOIQContext.propSatInvAtomic_preserved_by_fullDeriv
#print axioms ALCHOIQContext.AtomAtomBaseSeed
#print axioms ALCHOIQContext.atomicRefutable_from_propSaturationInvariant
#print axioms ALCHOIQContext.conceptDerivable_mono
#print axioms ALCHOIQContext.queryBodyAtomConcepts_singleton
#print axioms ALCHOIQContext.headNotDerivable_from_propSaturationInvariant

-- ============================================================
-- Item #4: Per-term fragment construction (§6.3.2) — concrete
-- trivial fragment for any input term, plus a list-mapping
-- builder for caller-supplied term lists.
-- ============================================================
#print axioms ALCHOIQContext.trivialNeighbourhood
#print axioms ALCHOIQContext.trivialNeighOrder
#print axioms ALCHOIQContext.trivialModelFragment
#print axioms ALCHOIQContext.per_term_fragment_concrete
#print axioms ALCHOIQContext.perTermFragments
#print axioms ALCHOIQContext.perTermFragments_confluent
#print axioms ALCHOIQContext.perTermFragments_noetherian
#print axioms ALCHOIQContext.per_term_fragments_for_aterms

-- ============================================================
-- Item #5: Knuth-Bendix completion procedure (§6.3.2.5) —
-- KBComplete predicate, base-case completion, extension theorem,
-- idempotence, and the trivial-neighbourhood specialisation.
-- ============================================================
#print axioms ALCHOIQContext.KBComplete
#print axioms ALCHOIQContext.kbComplete_empty
#print axioms ALCHOIQContext.kb_completion_from_locallyConfluent
#print axioms ALCHOIQContext.kb_completion_extends
#print axioms ALCHOIQContext.kbComplete_idempotent
#print axioms ALCHOIQContext.kb_completion_for_trivialNeighbourhood

-- ============================================================
-- Item #6: Naming witnesses beyond `emptyNaming` (§6.3.3) — a
-- concrete list-based naming construction that maps any chosen
-- list of `ATerm.const u` terms to their nominals, with semantic
-- justification via `reducesToNominal_const`.
-- ============================================================
#print axioms ALCHOIQContext.reducesToNominal_const
#print axioms ALCHOIQContext.singletonNaming_const
#print axioms ALCHOIQContext.listSingletonNamingCarrier
#print axioms ALCHOIQContext.listSingletonNaming
#print axioms ALCHOIQContext.listSingletonNaming_nonempty
#print axioms ALCHOIQContext.nonempty_naming_exists

-- ============================================================
-- Item #7: Composite confluence (Thesis Theorem 18, §6.3.4) —
-- shared-neighbourhood form via Newman, empty-list case, and
-- trivial-fragment specialisation for the atom-atom slice.
-- ============================================================
#print axioms ALCHOIQContext.composite_fragments_confluent_thm18
#print axioms ALCHOIQContext.composite_fragments_confluent_thm18_empties
#print axioms ALCHOIQContext.composite_trivial_fragments_confluent

-- ============================================================
-- Item #8: Saturation termination via aux-constant depth bound Λ
-- (§5.4).   Depth measures on a-terms / p-terms / clauses,
-- `CClausesBounded` invariant, `SaturationTerminates` predicate,
-- and a vacuous discharge for the empty seed.
-- ============================================================
#print axioms ALCHOIQContext.aTermAuxDepth
#print axioms ALCHOIQContext.pTermAuxDepth
#print axioms ALCHOIQContext.aEqAuxDepth
#print axioms ALCHOIQContext.bLitAuxDepth
#print axioms ALCHOIQContext.cLitAuxDepth
#print axioms ALCHOIQContext.cclauseAuxDepth
#print axioms ALCHOIQContext.CClausesBounded
#print axioms ALCHOIQContext.emptyContextStructure_CClausesBounded
#print axioms ALCHOIQContext.SaturationTerminates
#print axioms ALCHOIQContext.emptySeed_saturationTerminates

-- ============================================================
-- Item #9: Concept → QueryClause normalisation + Bridge (§6.2)
-- — atom-atom slice with bidirectional iff to DL subsumption.
-- ============================================================
#print axioms ALCHOIQContext.atomSubsumptionQuery
#print axioms ALCHOIQContext.atomSubsumptionQuery_eq_atomAtomSubsumptionClause
#print axioms ALCHOIQContext.entailsQuery_atomSubsumption
#print axioms ALCHOIQContext.axiomToQuery
#print axioms ALCHOIQContext.axiomToQuery_some_of_atomic

-- ============================================================
-- Item #10: RBox integration — compatibility predicate for the
-- atom-atom slice (excludes `.refl` and `.chain []`), satisfaction
-- of each individual RAxiom shape, full RBox satisfaction, and
-- the empty-RBox corollary.
-- ============================================================
#print axioms ALCHOIQContext.RAxiomCompatibleWithEmptyRoles
#print axioms ALCHOIQContext.atomicHerbrandInterp_ext_role_false
#print axioms ALCHOIQContext.atomicHerbrandInterp_satisfies_RAxiom
#print axioms ALCHOIQContext.RBoxCompatibleWithEmptyRoles
#print axioms ALCHOIQContext.emptyRBox_compatible
#print axioms ALCHOIQContext.atomicHerbrandInterp_satisfies_compatible_rbox
#print axioms ALCHOIQContext.atomicHerbrandInterp_satisfies_emptyRBox

-- ============================================================
-- FINAL GOAL: canonicalSeedOf : Ontology → ContextStructure with
-- IsCanonicalSeed O (canonicalSeedOf O) for every SROIQ O + RBox.
--
-- Currently landed:
--   * canonicalSeedOf : Ontology → ContextStructure (total)
--   * canonicalSeedOf_vr_in_contexts (unconditional)
--   * canonicalSeedOf_sound (unconditional)
--   * canonicalSeedOf_herbrandProperty_atomic_modulo (conditional on
--     hSatComplete + hAtomShape)
--   * isCanonicalSeed_canonicalSeedOf_atomic_modulo (conditional)
--
-- Gap: discharging hSatComplete (saturation procedure) and
-- hAtomShape (general Herbrand model) — see §FINAL-GAP comment
-- in SROIQCompletenessSkeleton.lean.
-- ============================================================
#print axioms ALCHOIQContext.axiomToCClause
#print axioms ALCHOIQContext.ontologyToClauses
#print axioms ALCHOIQContext.canonicalSeedOf
#print axioms ALCHOIQContext.canonicalSeedOf_vr_in_contexts
#print axioms ALCHOIQContext.mem_ontologyToClauses
#print axioms ALCHOIQContext.atomAtom_clause_sound
#print axioms ALCHOIQContext.canonicalSeedOf_sound
#print axioms ALCHOIQContext.canonicalSeedOf_herbrandProperty_atomic_modulo
#print axioms ALCHOIQContext.isCanonicalSeed_canonicalSeedOf_atomic_modulo
#print axioms ALCHOIQContext.CanonicalSaturationGap
#print axioms ALCHOIQContext.isCanonicalSeed_canonicalSeedOf_via_gap

-- ============================================================
-- FORMAL NEGATIVE RESULT: the literal unconditional goal is
-- structurally unattainable for empty O over unbounded Nat.
-- This guides necessary framework refactoring.
-- ============================================================
#print axioms ALCHOIQContext.fullSaturated_canonicalSeedOf_empty
#print axioms ALCHOIQContext.atomSubsumptionQuery_self_eval
#print axioms ALCHOIQContext.canonicalSeedOf_empty_no_subsumer
#print axioms ALCHOIQContext.not_herbrandProperty_canonicalSeedOf_empty
#print axioms ALCHOIQContext.not_isCanonicalSeed_canonicalSeedOf_empty
#print axioms ALCHOIQContext.not_canonicalSaturationGap_empty

-- ============================================================
-- REFINED GOAL: signature-parameterised canonical seed with
-- reflexive coverage for in-signature concepts.
-- ============================================================
#print axioms ALCHOIQContext.reflexiveClause
#print axioms ALCHOIQContext.canonicalSeedOver
#print axioms ALCHOIQContext.canonicalSeedOver_vr_in_contexts
#print axioms ALCHOIQContext.reflexiveClause_sound
#print axioms ALCHOIQContext.canonicalSeedOver_sound
#print axioms ALCHOIQContext.reflexiveClause_subsumes_tautology
#print axioms ALCHOIQContext.canonicalSeedOver_subsumes_reflexive_tautology
#print axioms ALCHOIQContext.QueryReferencesSignature
#print axioms ALCHOIQContext.HerbrandPropertyOver
#print axioms ALCHOIQContext.IsCanonicalSeedOver

end ELKSDD
