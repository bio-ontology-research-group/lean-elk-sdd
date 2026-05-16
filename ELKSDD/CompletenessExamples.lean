/-
  ELKSDD/CompletenessExamples.lean
  ----------------------------------
  Demonstration that the completeness theorem `satC_complete` is
  usable: from any semantic entailment we can extract a SatC
  derivation by `apply ALC.satC_complete; …` and discharge the
  semantic obligation with ordinary first-order reasoning.

  These examples are *worked* — fully checked, no `sorry` — and
  serve both as confidence checks on the formalisation and as a
  pattern for downstream users.

  Every theorem in this file depends only on the standard Lean
  foundational axioms (propext, Classical.choice, Quot.sound).
-/

import ELKSDD.Completeness

namespace ELKSDD
namespace ALC

/-- Toy ontology: { (atom 0, atom 1) } — a one-axiom TBox saying
    "A ⊑ B" with A = atom 0 and B = atom 1. -/
def toyOnt : Ontology := [(Concept.atom 0, Concept.atom 1)]

/-- Direct semantic check that `A ⊑ A ⊓ B` follows from `A ⊑ B`. -/
theorem toy_entails : Entails toyOnt (.atom 0) (.conj (.atom 0) (.atom 1)) := by
  intro α I hsat x hA
  refine ⟨hA, ?_⟩
  exact hsat (Concept.atom 0, Concept.atom 1) (by simp [toyOnt]) x hA

/-- Same fact extracted via the completeness theorem.  This shows
    `satC_complete` produces an explicit SatC derivation from
    semantic entailment. -/
theorem toy_satC : SatC toyOnt (.atom 0) (.conj (.atom 0) (.atom 1)) :=
  satC_complete _ _ _ toy_entails

/-- ``A ⊑ B ⊑ C ⊓ ⊤``  semantically. -/
theorem chain_entails :
    Entails [(Concept.atom 0, Concept.atom 1), (Concept.atom 1, Concept.atom 2)]
            (.atom 0)
            (.conj (.atom 2) .top) := by
  intro α I hsat x hA
  refine ⟨?_, trivial⟩
  have hB : I.eval (.atom 1) x :=
    hsat (Concept.atom 0, Concept.atom 1) (by simp) x hA
  exact hsat (Concept.atom 1, Concept.atom 2) (by simp) x hB

/-- And via completeness, the derivation exists. -/
theorem chain_satC :
    SatC [(Concept.atom 0, Concept.atom 1), (Concept.atom 1, Concept.atom 2)]
         (.atom 0)
         (.conj (.atom 2) .top) :=
  satC_complete _ _ _ chain_entails

/-- A classical move: ``A ⊔ ¬A ⊑ ⊤`` is semantically obvious; the
    completeness theorem hands us a syntactic derivation. -/
theorem em_entails (A : Concept) :
    Entails ([] : Ontology) (.disj A (.neg A)) .top := by
  intro α I _ x _
  trivial

theorem em_satC (A : Concept) :
    SatC ([] : Ontology) (.disj A (.neg A)) .top :=
  satC_complete _ _ _ (em_entails A)

/-- De~Morgan via completeness. -/
theorem demorgan_entails (A B : Concept) :
    Entails ([] : Ontology)
            (.neg (.disj A B))
            (.conj (.neg A) (.neg B)) := by
  intro α I _ x h
  refine ⟨?_, ?_⟩
  · intro hA; exact h (Or.inl hA)
  · intro hB; exact h (Or.inr hB)

theorem demorgan_satC (A B : Concept) :
    SatC ([] : Ontology)
         (.neg (.disj A B))
         (.conj (.neg A) (.neg B)) :=
  satC_complete _ _ _ (demorgan_entails A B)

/-- Role-axis entailment: ``∃R.(A ⊓ B) ⊑ ∃R.A``.  Derivable directly
    via `monoExist` + `andL`; here exposed through completeness. -/
theorem exist_entails (R : Nat) (A B : Concept) :
    Entails ([] : Ontology)
            (.exist R (.conj A B))
            (.exist R A) := by
  intro α I _ x h
  obtain ⟨y, hR, hAB⟩ := h
  exact ⟨y, hR, hAB.1⟩

theorem exist_satC (R : Nat) (A B : Concept) :
    SatC ([] : Ontology)
         (.exist R (.conj A B))
         (.exist R A) :=
  satC_complete _ _ _ (exist_entails R A B)

end ALC
end ELKSDD
