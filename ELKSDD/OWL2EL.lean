/-
  ELKSDD/OWL2EL.lean
  ------------------
  *Unified user-facing interface* for OWL 2 EL soundness and completeness.

  This module wraps the per-fragment theorems from `ELpp` and `Merging`
  under a single `complete_owl2el` dispatch theorem.  It does NOT add
  new mathematical content — it merely consolidates the existing
  fragment theorems (each proved on its own preconditions) so a user
  can invoke "the OWL 2 EL completeness theorem" once and have the
  appropriate fragment selected by case-splitting on the precondition
  disjunction.

  Coverage (each entry is a fragment with its own canonical model):

    1. **NF fragment** — `OntologyNominalFree O ∧ RangeChainSafe O`
       Standard ELK, full deep existentials, range, rinc, rchain,
       reflexive, Self, but no nominals or HasKey.
       Theorem: `ELpp.complete_via_canon`.

    2. **LHS-nominal fragment (shape 1)** —
       `OntologyNomLHS O ∧ RangeChainSafe O ∧ AllNomInhabited O`
       Adds ClassAssertion-style axioms `gci {a} ⊑ D` (NF D).
       Theorem: `ELpp.complete_via_canon_nomLHS`.

    3. **NomLR fragment (shapes 1+3, no range)** —
       `OntologyNomLR O ∧ AllNomInhabited O`
       Adds ObjectPropertyAssertion-style `gci C ⊑ ∃R.{a}`.
       Theorem: `ELpp.complete_via_canon_nomLR`.

    4. **Strict (range-free) fragment** — `OntologyStrict O`
       NF concepts only, range axioms forbidden.
       Theorem: `ELpp.complete_via_canon_strict`.

    5. **Merge fragment (shapes 1-4 + HasKey, Shallow)** —
       `OntologyMerge O ∧ AllNomInhabited O`
       All four nominal shapes plus HasKey.  Restricted to *Shallow*
       concepts (no deep existentials with non-nominal targets).
       Theorem: `ELpp.complete_via_mergedCanon_regular`
              + `ELpp.complete_via_mergedCanon_nom`.

  *Soundness* is uniform: `ELpp.sound` covers every Sat constructor.

  Why a *dispatch* and not a single proof?  The five fragments use
  distinct canonical-model constructions and, crucially, the
  preconditions are not jointly compatible.  In particular, deep
  existentials with non-nominal targets and shape-2 (`gci C ⊑ {a}`)
  axioms cannot be simultaneously satisfied by a single canonical
  construction without resolving a long-standing semantic issue
  (an ontology may have both a model where C is empty and a model
  where C is forced into the {a}-class; the canonical model must
  pick one).  This is acknowledged in Kazakov 2014 §6 and resolved
  there only via additional preconditions that effectively disable
  one of the cases.  Our dispatch provides the union of supported
  fragments without the false promise of a unified construction.
-/

import ELKSDD.ELpp
import ELKSDD.Merging

namespace ELKSDD
namespace ELpp

-- ============================================================
-- 1. Unified well-formedness predicate
-- ============================================================

/-- Predicate "ontology + query are in a supported OWL 2 EL fragment".

    A user supplies *one* of the five branch-proofs to invoke
    `complete_owl2el`.  Each branch corresponds to a different
    canonical-model construction (see the file header). -/
inductive OWL2ELFragment (O : Ontology) (C D : Concept) : Prop where
  | nominalFree :
      OntologyNominalFree O → RangeChainSafe O →
      NominalFree C → NominalFree D →
      OWL2ELFragment O C D
  | nomLHS :
      OntologyNomLHS O → RangeChainSafe O → AllNomInhabited O →
      NominalFree C → NominalFree D →
      OWL2ELFragment O C D
  | nomLR :
      OntologyNomLR O → AllNomInhabited O →
      NominalFree C → NominalFree D →
      OWL2ELFragment O C D
  | strict :
      OntologyStrict O →
      NominalFree C → NominalFree D →
      OWL2ELFragment O C D
  | merge_regular :
      OntologyMerge O → AllNomInhabited O →
      Shallow C → Shallow D →
      Regular O C →
      OWL2ELFragment O C D
  | merge_nom :
      ∀ {i : Nat}, OntologyMerge O → AllNomInhabited O →
      Shallow D →
      C = .nom i →
      OWL2ELFragment O C D

-- ============================================================
-- 2. Unified soundness — already provided by ELpp.sound
-- ============================================================

/-- **Soundness on all of OWL 2 EL** (excluding datatypes).
    Every Sat-derivable subsumption is semantically entailed.
    No fragment-precondition is required for soundness. -/
theorem sound_owl2el (O : Ontology) (C D : Concept)
    (h : Sat O C D) : Entails O C D :=
  ELpp.sound O h

-- ============================================================
-- 3. Unified completeness — dispatch to fragment theorems
-- ============================================================

/-- **Unified completeness on OWL 2 EL** (excluding datatypes).

    Given the user-supplied fragment witness `hWF : OWL2ELFragment O C D`,
    Entails O C D implies Sat O C D.

    The proof case-splits on `hWF` and dispatches to the appropriate
    per-fragment completeness theorem.  No new mathematical content
    beyond the existing fragment theorems. -/
theorem complete_owl2el (O : Ontology) (C D : Concept)
    (hWF : OWL2ELFragment O C D)
    (h : Entails O C D) : Sat O C D := by
  cases hWF with
  | nominalFree hO hSafe hC hD =>
      exact complete_via_canon O C D hO hSafe hC hD h
  | nomLHS hO hSafe hInhab hC hD =>
      exact complete_via_canon_nomLHS O C D hO hSafe hInhab hC hD h
  | nomLR hO hInhab hC hD =>
      exact complete_via_canon_nomLR O C D hO hInhab hC hD h
  | strict hO hC hD =>
      exact complete_via_canon_strict O C D hO hC hD h
  | merge_regular hO hInhab hC hD hReg =>
      exact complete_via_mergedCanon_regular O C D hO hInhab hC hD hReg h
  | @merge_nom i hO hInhab hD hCi =>
      subst hCi
      exact complete_via_mergedCanon_nom O i D hO hInhab hD h

-- ============================================================
-- 4. Bidirectional characterisation — Sat ↔ Entails
-- ============================================================

/-- **Sat ↔ Entails** on the OWL 2 EL fragment.  Combines `sound_owl2el`
    (no precondition) with `complete_owl2el` (under `OWL2ELFragment`). -/
theorem correct_owl2el (O : Ontology) (C D : Concept)
    (hWF : OWL2ELFragment O C D) :
    Sat O C D ↔ Entails O C D :=
  ⟨sound_owl2el O C D, complete_owl2el O C D hWF⟩

-- ============================================================
-- 5. Audit
-- ============================================================

#print axioms sound_owl2el        -- (no axioms — pure induction)
#print axioms complete_owl2el     -- propext, Classical.choice, Quot.sound
#print axioms correct_owl2el      -- propext, Classical.choice, Quot.sound

end ELpp
end ELKSDD
