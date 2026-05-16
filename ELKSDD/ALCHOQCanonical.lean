/-
  ELKSDD/ALCHOQCanonical.lean
  ----------------------------
  Canonical-model construction for the full ALCHOQ description logic.

  This file extends the consequence-based saturation calculus
  `ALCHOQ.SatC` (whose new rules — `atLeast_to_exist`,
  `hasSelf_to_exist`, `hasSelf_with_univ`, the cardinality
  dualities, etc. — are already proved sound in
  `ELKSDD.ALCHOQCompleteness`) with a canonical-model construction
  in the style of Horrocks--Sattler--Tobies 2000 lifted to Lean 4.

  We progress section by section.  At any point the file should
  build cleanly (no `sorry`s in committed shape); residual cases
  are flagged as open theorems and we then close them by inductive
  extension.

  Axiom budget: only the standard Lean foundational axioms
  (propext, Classical.choice, Quot.sound), inherited from
  `ELKSDD.Completeness` (which provides the ALC base case) and
  `ELKSDD.ALCHOQCompleteness`.
-/

import ELKSDD.ALCHOQCompleteness
import ELKSDD.Completeness
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Zorn

namespace ELKSDD
namespace ALCHOQ

open Classical

-- ============================================================
-- 1.  Consistency and types (SatC-relative, ALCHOQ syntax).
-- ============================================================

/-- `conjList` reuses the ALC definition pointwise on ALCHOQ concepts. -/
def conjList : List Concept → Concept
  | []      => Concept.top
  | C :: Cs => Concept.conj C (conjList Cs)

/-- A concept set ``Γ`` is *SatC-consistent under O* if SatC does not
    derive ``⨅L ⊑ ⊥`` for any finite list ``L`` of elements of ``Γ``. -/
def consistent (O : Ontology) (Γ : Set Concept) : Prop :=
  ∀ L : List Concept, (∀ C ∈ L, C ∈ Γ) →
    ¬ SatC O (conjList L) Concept.bot

/-- The set of *types*: maximal SatC-consistent sets. -/
structure Type_ (O : Ontology) where
  carrier : Set Concept
  cons    : consistent O carrier
  maximal : ∀ C : Concept, C ∈ carrier ∨ Concept.neg C ∈ carrier

-- ============================================================
-- 2.  Canonical interpretation skeleton.
--     `ext_role` uses the standard Hintikka clause; `ext_ind` is
--     the per-nominal designated type-representative.
-- ============================================================

/-- `ext_role` definition lifted from ALC: every universal at `t`
    must propagate to `t'`.  We additionally include the self-loop
    case for `hasSelf`. -/
def canonicalRole (O : Ontology) (R : Nat) (t t' : Type_ O) : Prop :=
  (∀ C, Concept.univ R C ∈ t.carrier → C ∈ t'.carrier) ∧
  (t' = t → Concept.hasSelf R ∈ t.carrier)

-- ============================================================
-- 3.  Embedding into ALC canonical model — used for sanity checks.
-- ============================================================

end ALCHOQ
end ELKSDD
