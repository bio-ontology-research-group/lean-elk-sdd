/-
  ELKSDD/MiniEL.lean
  ------------------
  A self-contained, **fully proved (zero-axiom)** formalisation of
  the atomic-subsumption fragment of EL.

  Scope:
    * concept names ≔ Nat
    * EL axioms     ≔ A ⊑ B  (atomic on both sides)
    * ontology      ≔ list of axioms
    * interpretation: a Tarskian extension function over an
                      arbitrary domain α
    * semantic entailment, ELK saturation, soundness, completeness
      — all proved from first principles.

  No imports beyond Lean 4 core. No `Mathlib`. No `Classical.choice`.
  Verify with `#print axioms el0_sound` / `#print axioms el0_complete`.

  The MiniEL fragment corresponds to ELK Rules R₀ (reflexivity), the
  axiom-base, and R_⊑ (transitivity). For the full conjunction +
  existential fragment with all 10 ELK rules, see `EL.lean`.
-/

namespace ELKSDD
namespace MiniEL

-- ============================================================
-- 1. Syntax
-- ============================================================

/-- Atomic concept names. -/
abbrev Concept := Nat

/-- An EL axiom of the form `A ⊑ B`. -/
abbrev Axiom := Concept × Concept

/-- An EL ontology is a list of axioms. -/
abbrev Ontology := List Axiom

-- ============================================================
-- 2. Tarskian semantics
-- ============================================================

/-- A first-order interpretation over a domain `α` assigns each
    concept name a unary predicate (its extension). -/
def Interp (α : Type) := Concept → α → Prop

/-- An interpretation `I` satisfies the axiom `A ⊑ B` iff every
    element of `A`'s extension is in `B`'s extension. -/
def Interp.satisfiesAxiom {α : Type} (I : Interp α) (ax : Axiom) : Prop :=
  ∀ x, I ax.1 x → I ax.2 x

/-- An interpretation satisfies an ontology iff it satisfies every
    axiom. -/
def Interp.satisfies {α : Type} (I : Interp α) (O : Ontology) : Prop :=
  ∀ ax, ax ∈ O → I.satisfiesAxiom ax

/-- Semantic entailment: `O ⊨ A ⊑ B` iff every model of `O` (over
    every domain) satisfies `A ⊑ B`. -/
def Entails (O : Ontology) (A B : Concept) : Prop :=
  ∀ {α : Type} (I : Interp α), I.satisfies O →
    ∀ x, I A x → I B x

-- ============================================================
-- 3. ELK calculus for the atomic-subsumption fragment
-- ============================================================

/-- ELK saturation closure for the atomic-subsumption fragment.
    Three constructors:

      * `refl A`        — Rule R₀ (every concept subsumes itself);
      * `base A B h`    — every axiom in O is derivable;
      * `trans A B C …` — Rule R_⊑ (transitivity). -/
inductive Sat (O : Ontology) : Concept → Concept → Prop where
  | refl  : ∀ A, Sat O A A
  | base  : ∀ A B, (A, B) ∈ O → Sat O A B
  | trans : ∀ A B C, Sat O A B → Sat O B C → Sat O A C

-- ============================================================
-- 4. Soundness of ELK saturation
-- ============================================================

/-- **Soundness.** Every saturation atom is semantically entailed.
    Proof: induction on the saturation derivation. Reflexivity is
    immediate. The axiom-base case unpacks the ontology
    satisfaction. Transitivity composes the two inductive
    hypotheses. -/
theorem el0_sound (O : Ontology) (A B : Concept) (h : Sat O A B) :
    Entails O A B := by
  induction h with
  | refl A =>
      intro α I _ x hx
      exact hx
  | base A B hax =>
      intro α I hO x hx
      exact hO (A, B) hax x hx
  | trans A B C _ _ ihAB ihBC =>
      intro α I hO x hx
      exact ihBC I hO x (ihAB I hO x hx)

-- ============================================================
-- 5. The canonical (term) interpretation
-- ============================================================

/-- The canonical interpretation of `O`: domain ≔ Nat (concept
    names), and the extension of `A` consists of those `c` with
    `Sat O c A`. -/
def canon (O : Ontology) : Interp Nat :=
  fun A x => Sat O x A

/-- The canonical model satisfies its ontology. -/
theorem canon_satisfies (O : Ontology) :
    (canon O).satisfies O := by
  intro ax hax x hx
  exact Sat.trans _ _ _ hx (Sat.base _ _ (by
    cases ax
    exact hax))

-- ============================================================
-- 6. Completeness of ELK saturation
-- ============================================================

/-- **Completeness.** Every semantically-entailed atomic
    subsumption is in the saturation. Proved via the canonical-
    model construction. -/
theorem el0_complete (O : Ontology) (A B : Concept) :
    Entails O A B → Sat O A B := by
  intro h
  exact h (canon O) (canon_satisfies O) A (Sat.refl A)

-- ============================================================
-- 7. The biconditional ELK characterisation
-- ============================================================

/-- ELK is a sound-and-complete decision procedure for
    atomic-subsumption entailment. -/
theorem el0_correct (O : Ontology) (A B : Concept) :
    Sat O A B ↔ Entails O A B :=
  ⟨el0_sound O A B, el0_complete O A B⟩

-- ============================================================
-- 8. Useful structural lemmas
-- ============================================================

/-- Reflexivity-closure: every concept entails itself. -/
theorem el0_refl_entails (O : Ontology) (A : Concept) :
    Entails O A A := el0_sound O A A (Sat.refl A)

/-- Entailment is transitive. -/
theorem el0_entails_trans (O : Ontology) (A B C : Concept)
    (hAB : Entails O A B) (hBC : Entails O B C) :
    Entails O A C := by
  intro α I hO x hx
  exact hBC I hO x (hAB I hO x hx)

/-- Every axiom in O is entailed by O. -/
theorem el0_axiom_entails (O : Ontology) (A B : Concept)
    (h : (A, B) ∈ O) : Entails O A B :=
  el0_sound O A B (Sat.base A B h)

-- ============================================================
-- 9. Worked example: O = { 0 ⊑ 1, 1 ⊑ 2 } ⊨ 0 ⊑ 2
-- ============================================================

/-- Concrete ontology used in the worked example. -/
def exampleOntology : Ontology := [(0, 1), (1, 2)]

/-- 0 ⊑ 2 is in `Sat exampleOntology`. -/
theorem example_sat : Sat exampleOntology 0 2 :=
  Sat.trans 0 1 2
    (Sat.base 0 1 (by simp [exampleOntology]))
    (Sat.base 1 2 (by simp [exampleOntology]))

/-- 0 ⊑ 2 is entailed by `exampleOntology` — a fully mechanical
    fact; no admitted axioms anywhere in this chain. -/
theorem example_entails : Entails exampleOntology 0 2 :=
  el0_sound exampleOntology 0 2 example_sat

end MiniEL
end ELKSDD
