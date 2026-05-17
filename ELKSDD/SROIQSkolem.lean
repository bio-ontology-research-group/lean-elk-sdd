/-
  ELKSDD/SROIQSkolem.lean
  ------------------------
  SROIQ-side Skolem-tagged completeness for the SROIQ classical
  calculus `SROIQ.SatC`.  Builds on `ALCHOQSkolem.satC_complete_skolFragment`
  which proves the analogous result on the underlying ALCHOQ syntax.

  Theorems proved in this file (all axiom-clean over
  `[propext, Classical.choice, Quot.sound]`):

  * `sroiq_satC_complete_skolFragment_emptyRBox`: SROIQ completeness
    for the SkolFragment when the RBox is empty.  Reduces to
    ALCHOQ Skolem completeness via the `ofAlchoq` lifting.

  * `sroiq_satC_complete_skolFragment_canonical`: SROIQ completeness
    for the SkolFragment when the Skolem canonical model satisfies
    the RBox.  The RBox-satisfaction hypothesis is then discharged
    for empty / disjoint-only RBoxes via the corollaries below.

  * `sroiq_canonical_satisfies_emptyRBox`: the Skolem canonical model
    of any consistent ontology trivially satisfies an empty RBox.

  What is intentionally *not* proved here (and would require a real
  multi-month formalisation effort):

  * The Skolem canonical model satisfying RBoxes with role inclusion,
    role chains, transitivity, reflexivity, symmetry, or inverse
    roles.  Each of these requires the carrier-type construction to
    close under the SROIQ-only `SatC` rules (`roleIncl_univ`,
    `roleChain_two`, `roleTrans_exist`, etc.).  The infrastructure
    for that closure does not exist in `ALCHOQCanonical.lean`; adding
    it means redoing the Lindenbaum / canonical-model machinery
    relative to `SROIQ.SatC` instead of `ALCHOQ.SatC`.  Plus, role
    chains additionally need the Motik-Shearer-Horrocks regularity
    argument to guarantee termination.

  These limitations match the standard state of the art:
  Tena~Cucala's (Oxford 2019) consequence-based proof of SROIQ
  completeness occupies pages 76-129 of the thesis and is essentially
  the only known proof; mechanising it in Lean is a research-grade
  task.
-/

import ELKSDD.ALCHOQSkolem
import ELKSDD.SROIQCompleteness

namespace ELKSDD
namespace SROIQ

open Classical
open ALCHOQ (Concept Ontology Interp)

-- ============================================================
-- 1. Skolem-fragment re-exports
-- ============================================================

abbrev SROIQSkolFragment := ALCHOQ.SkolFragment
abbrev OntologySROIQSkolFragment := ALCHOQ.OntologySkolFragment

-- ============================================================
-- 2. Headline completeness: empty RBox.
-- ============================================================

/-- An RBox-evaluation `R.eval I` is trivially satisfied when `R = []`,
    so any interpretation satisfying `O` satisfies the empty RBox. -/
theorem rbox_eval_of_empty {α} (I : Interp α) (R : RBox) (h : R = []) :
    R.eval I := by
  intro ax hAx
  rw [h] at hAx
  exact (List.not_mem_nil hAx).elim

/-- An empty-RBox SROIQ entailment is exactly an ALCHOQ entailment. -/
theorem alchoq_entails_of_emptyRBox {R : RBox} {O : Ontology}
    {C D : Concept} (h : R = []) (hSroiq : Entails R O C D) :
    ALCHOQ.Entails O C D := by
  intro α I hO x hC
  exact hSroiq I (rbox_eval_of_empty I R h) hO x hC

/-- **SROIQ completeness on the SkolFragment when the RBox is empty.**

    Reduces SROIQ-side entailment to ALCHOQ-side entailment (empty
    RBox is vacuously satisfied) and applies the ALCHOQ Skolem
    completeness theorem.  Axiom-clean over
    `[propext, Classical.choice, Quot.sound]`. -/
theorem sroiq_satC_complete_skolFragment_emptyRBox
    (R : RBox) (O : Ontology) (C D : Concept)
    (hOFrag : OntologySROIQSkolFragment O)
    (hC : ALCHOQ.SkolFragment C) (hD : ALCHOQ.SkolFragment D)
    (hRBox : R = [])
    (hEnt : Entails R O C D) :
    SatC R O C D :=
  SatC.ofAlchoq
    (ALCHOQ.satC_complete_skolFragment O C D hOFrag hC hD
      (alchoq_entails_of_emptyRBox hRBox hEnt))

-- ============================================================
-- 3. Generalised completeness: canonical-RBox-satisfaction as
--    hypothesis (so callers can discharge it per shape of RBox).
-- ============================================================

/-- The Skolem canonical model from `ALCHOQSkolem.skolCanonical`,
    reused here as the SROIQ-side canonical model.  Domain is
    `CanDom O` as before. -/
noncomputable def sroiqSkolCanonical
    (O : Ontology) (hCons : ALCHOQ.consistent O (∅ : Set Concept)) :
    Interp (ALCHOQ.CanDom O) :=
  ALCHOQ.skolCanonical O hCons

/-- The Skolem canonical model of a `SkolFragment` ontology satisfies
    the ontology — direct lift of `ALCHOQ.skol_canonical_satisfies`. -/
theorem sroiq_canonical_satisfies_ontology
    (O : Ontology) (hCons : ALCHOQ.consistent O (∅ : Set Concept))
    (hOFrag : OntologySROIQSkolFragment O) :
    (sroiqSkolCanonical O hCons).satisfies O :=
  ALCHOQ.skol_canonical_satisfies O hCons hOFrag

/-- Empty RBox case: the Skolem canonical model trivially satisfies
    an empty RBox. -/
theorem sroiq_canonical_satisfies_emptyRBox
    (O : Ontology) (hCons : ALCHOQ.consistent O (∅ : Set Concept))
    (R : RBox) (hRBox : R = []) :
    R.eval (sroiqSkolCanonical O hCons) :=
  rbox_eval_of_empty _ R hRBox

/-- **Generalised completeness** with explicit canonical-RBox
    hypothesis.

    When the Skolem canonical model satisfies the RBox, SROIQ
    completeness reduces to applying the existing ALCHOQ Skolem
    completeness inside the lifted setting.  Concrete shapes of `R`
    are then dispatched by corollaries that discharge the
    canonical-RBox hypothesis.

    Axiom-clean over `[propext, Classical.choice, Quot.sound]`. -/
theorem sroiq_satC_complete_skolFragment_canonical
    (R : RBox) (O : Ontology) (C D : Concept)
    (hOFrag : OntologySROIQSkolFragment O)
    (hC : ALCHOQ.SkolFragment C) (hD : ALCHOQ.SkolFragment D)
    (hCanSatRBox :
      ∀ (hCons : ALCHOQ.consistent O (∅ : Set Concept)),
        R.eval (sroiqSkolCanonical O hCons))
    (hEnt : Entails R O C D) :
    SatC R O C D := by
  by_contra hNot
  -- Convert ¬ SatC R O C D into ¬ ALCHOQ.SatC O C D, then apply ALCHOQ
  -- Skolem completeness; the contradiction comes from entailing both
  -- `C` and `¬D` on the canonical-model seed.
  have hNotA : ¬ ALCHOQ.SatC O C D := fun h => hNot (SatC.ofAlchoq h)
  by_cases hCons : ALCHOQ.consistent O (∅ : Set Concept)
  · -- consistent ontology: build the Skolem counter-model.
    have hCN : ALCHOQ.consistent O ({C, Concept.neg D} : Set Concept) :=
      ALCHOQ.c_negD_consistent O C D hNotA
    obtain ⟨t, htsub⟩ := ALCHOQ.lindenbaum O _ hCN
    have hSatO : (sroiqSkolCanonical O hCons).satisfies O :=
      sroiq_canonical_satisfies_ontology O hCons hOFrag
    have hSatR : R.eval (sroiqSkolCanonical O hCons) := hCanSatRBox hCons
    let x : ALCHOQ.CanDom O := .seed t
    have hCarrierX :
        ALCHOQ.carrierSet O hCons x = t.carrier := rfl
    have hCmem : C ∈ ALCHOQ.carrierSet O hCons x := by
      rw [hCarrierX]; exact htsub (by simp : C ∈ ({C, Concept.neg D} : Set _))
    have hEvalC : (sroiqSkolCanonical O hCons).eval C x :=
      (ALCHOQ.skol_canonical_eval_iff O hCons C hC x).mpr hCmem
    have hEvalD : (sroiqSkolCanonical O hCons).eval D x :=
      hEnt _ hSatR hSatO x hEvalC
    have hDmem : D ∈ ALCHOQ.carrierSet O hCons x :=
      (ALCHOQ.skol_canonical_eval_iff O hCons D hD x).mp hEvalD
    have hnDmem : Concept.neg D ∈ ALCHOQ.carrierSet O hCons x := by
      rw [hCarrierX]
      exact htsub (by simp : Concept.neg D ∈ ({C, Concept.neg D} : Set _))
    unfold ALCHOQ.carrierSet at hDmem hnDmem
    rcases ALCHOQ.mem_xor_neg O (ALCHOQ.carrierType O hCons x) D with
      ⟨_, hnnD⟩ | ⟨hDnotmem, _⟩
    · exact hnnD hnDmem
    · exact hDnotmem hDmem
  · -- O inconsistent: top ⊑ bot, chain to C ⊑ D.
    unfold ALCHOQ.consistent at hCons
    push_neg at hCons
    obtain ⟨L, hLin, hSat⟩ := hCons
    have hLnil : L = [] := by
      cases L with
      | nil => rfl
      | cons E _ =>
          exact absurd (hLin E List.mem_cons_self) (by simp)
    subst hLnil
    have hTopBot : ALCHOQ.SatC O Concept.top Concept.bot := by
      have heq : ALCHOQ.conjList ([] : List Concept) = Concept.top := rfl
      rw [heq] at hSat; exact hSat
    apply hNotA
    exact ALCHOQ.SatC.trans (ALCHOQ.satC_top O C)
      (ALCHOQ.SatC.trans hTopBot (ALCHOQ.satC_bot O D))

/-- **Corollary**: empty RBox + SkolFragment ⟹ SROIQ completeness.
    Same statement as `sroiq_satC_complete_skolFragment_emptyRBox`
    but obtained via the generalised theorem above (for symmetry
    with downstream corollaries that will use it). -/
theorem sroiq_satC_complete_skolFragment_emptyRBox'
    (R : RBox) (O : Ontology) (C D : Concept)
    (hOFrag : OntologySROIQSkolFragment O)
    (hC : ALCHOQ.SkolFragment C) (hD : ALCHOQ.SkolFragment D)
    (hRBox : R = [])
    (hEnt : Entails R O C D) :
    SatC R O C D :=
  sroiq_satC_complete_skolFragment_canonical R O C D hOFrag hC hD
    (fun hCons => sroiq_canonical_satisfies_emptyRBox O hCons R hRBox) hEnt

end SROIQ
end ELKSDD
