/-
  ELKSDD/ALC.lean
  ---------------
  Syntax and semantics of the description logic ALC, extending the EL
  fragment (`ELKSDD.EL`) with full Boolean negation, disjunction, and
  universal restrictions.

  This file is the entry point for the ALCHOQ direction of the moose
  project — see the project-level `SROIQ-PLAN.md` for the broader
  strategy. The first cut here gives the *syntax* and *semantics* (a
  Tarskian set-extension interpretation), plus the basic well-formed-
  ness lemmas: negation is involutive on truth, disjunction is dual to
  conjunction, the universal restriction is dual to the existential.

  Proof targets to add in subsequent commits (mirroring `EL.lean`):

  * `nnf`: a partial function pushing negation to atomic concepts, with
    `nnf_semantics_preserving`.
  * `Sat` inductive: a consequence-based saturation calculus (Tena
    Cucala, DPhil thesis, Sec. 3.2) — soundness via induction over
    derivations; completeness via canonical-model construction over
    the saturated clause set.
  * Bridge to `ELKSDD.SDD`: the saturated clause set, after grounding
    over a finite individual domain, is a CNF that compiles to an SDD
    via the existing `compile_correct` theorem.

  No imports beyond Lean 4 core. No Mathlib. Foundation-only axiom
  budget (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace ELKSDD
namespace ALC

-- ============================================================
-- 1. Concept syntax (atoms + Boolean connectives + ∃/∀ + ⊤/⊥)
-- ============================================================

/-- Concepts in ALC. Role names and concept names are indexed by
    natural numbers, matching the convention used by `EL.Concept`. -/
inductive Concept : Type where
  | atom  : Nat → Concept
  | top   : Concept
  | bot   : Concept
  | neg   : Concept → Concept                 -- ¬C
  | conj  : Concept → Concept → Concept       -- C ⊓ D
  | disj  : Concept → Concept → Concept       -- C ⊔ D
  | exist : Nat → Concept → Concept           -- ∃R.C
  | univ  : Nat → Concept → Concept           -- ∀R.C
  deriving DecidableEq

/-- An ALC general concept inclusion `C ⊑ D`. -/
abbrev Axiom := Concept × Concept

/-- An ALC ontology is a list of GCIs. -/
abbrev Ontology := List Axiom

-- ============================================================
-- 2. Tarskian semantics
-- ============================================================

/-- An interpretation over domain `α` assigns each atomic concept name
    a unary predicate, and each role name a binary relation. Identical
    in shape to `EL.Interp`; we re-declare for namespace clarity. -/
structure Interp (α : Type) where
  ext_concept : Nat → α → Prop
  ext_role    : Nat → α → α → Prop

/-- Recursive evaluation of an ALC concept. The negation, disjunction,
    and universal-restriction cases are the novel ones compared with
    `EL.Interp.eval`. -/
def Interp.eval {α : Type} (I : Interp α) : Concept → α → Prop
  | .atom n, x => I.ext_concept n x
  | .top, _ => True
  | .bot, _ => False
  | .neg C, x => ¬ I.eval C x
  | .conj A B, x => I.eval A x ∧ I.eval B x
  | .disj A B, x => I.eval A x ∨ I.eval B x
  | .exist R C, x => ∃ y, I.ext_role R x y ∧ I.eval C y
  | .univ  R C, x => ∀ y, I.ext_role R x y → I.eval C y

/-- An interpretation satisfies an axiom `C ⊑ D` iff every domain
    element in the extension of `C` is also in the extension of `D`. -/
def Interp.satisfiesAxiom {α : Type} (I : Interp α) (ax : Axiom) : Prop :=
  ∀ x, I.eval ax.1 x → I.eval ax.2 x

/-- An interpretation satisfies an ontology iff it satisfies every axiom. -/
def Interp.satisfies {α : Type} (I : Interp α) (O : Ontology) : Prop :=
  ∀ ax, ax ∈ O → I.satisfiesAxiom ax

/-- Semantic concept subsumption modulo an ontology. -/
def Entails (O : Ontology) (C D : Concept) : Prop :=
  ∀ {α : Type} (I : Interp α), I.satisfies O →
    ∀ x, I.eval C x → I.eval D x

-- ============================================================
-- 3. Basic semantic lemmas: dualities of the connectives
-- ============================================================

namespace Interp

variable {α : Type} (I : Interp α)

/-- Double negation collapses on truth values — uses classical logic
    via `Classical.byContradiction`. -/
theorem eval_neg_neg (C : Concept) (x : α) :
    I.eval (.neg (.neg C)) x ↔ I.eval C x := by
  show (¬ ¬ I.eval C x) ↔ I.eval C x
  exact ⟨fun h => Classical.byContradiction (fun nC => h nC),
         fun h nC => nC h⟩

/-- de Morgan: `¬(A ⊓ B) ↔ ¬A ⊔ ¬B`. Classical. -/
theorem eval_neg_conj (A B : Concept) (x : α) :
    I.eval (.neg (.conj A B)) x ↔ I.eval (.disj (.neg A) (.neg B)) x := by
  unfold eval
  constructor
  · intro h
    by_cases hA : I.eval A x
    · by_cases hB : I.eval B x
      · exact absurd ⟨hA, hB⟩ h
      · exact Or.inr hB
    · exact Or.inl hA
  · rintro (hA | hB) ⟨a, b⟩
    · exact hA a
    · exact hB b

/-- de Morgan: `¬(A ⊔ B) ↔ ¬A ⊓ ¬B`. -/
theorem eval_neg_disj (A B : Concept) (x : α) :
    I.eval (.neg (.disj A B)) x ↔ I.eval (.conj (.neg A) (.neg B)) x := by
  unfold eval
  constructor
  · intro h
    refine ⟨fun a => h (Or.inl a), fun b => h (Or.inr b)⟩
  · rintro ⟨hA, hB⟩ (a | b)
    · exact hA a
    · exact hB b

/-- Quantifier duality: `¬∃R.C ↔ ∀R.¬C`. -/
theorem eval_neg_exist (R : Nat) (C : Concept) (x : α) :
    I.eval (.neg (.exist R C)) x ↔ I.eval (.univ R (.neg C)) x := by
  unfold eval
  constructor
  · intro h y hR hC
    exact h ⟨y, hR, hC⟩
  · rintro h ⟨y, hR, hC⟩
    exact h y hR hC

/-- Quantifier duality: `¬∀R.C ↔ ∃R.¬C`. Classical (needs
    `byContradiction` to extract the witness). -/
theorem eval_neg_univ (R : Nat) (C : Concept) (x : α) :
    I.eval (.neg (.univ R C)) x ↔ I.eval (.exist R (.neg C)) x := by
  show (¬ ∀ y, I.ext_role R x y → I.eval C y)
       ↔ (∃ y, I.ext_role R x y ∧ ¬ I.eval C y)
  constructor
  · intro h
    apply Classical.byContradiction
    intro hne
    apply h
    intro y hR
    apply Classical.byContradiction
    intro hC
    exact hne ⟨y, hR, hC⟩
  · rintro ⟨y, hR, hC⟩ hall
    exact hC (hall y hR)

end Interp

end ALC
end ELKSDD
