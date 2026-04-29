/-
  ELKSDD/EL.lean
  --------------
  A self-contained, fully proved formalisation of the description
  logic EL with conjunction AND existential restrictions (the role
  fragment): atoms, ⊓, ⊤, ⊥, ∃R.C.

  The ELK calculus rules R₀, R_⊤, R_⊑, R⁻_⊓, R⁺_⊓, R_⊥, R⁺_∃,
  R_⊥-∃ (the existential-bot variant) are inductively encoded;
  soundness AND completeness are proved end-to-end via a canonical
  (term) model with a role-extension construction.

  References:
    [Kazakov 2014] Kazakov, Krötzsch, Simančík.
                   The Incredible ELK: From Polynomial Procedures
                   to Efficient Reasoning with EL Ontologies.
                   J. Automated Reasoning 53(1), 2014.

  No imports beyond Lean 4 core. No Mathlib. The use of classical
  `by_cases` in `complete_via_canon` introduces `Classical.choice`
  as a Lean foundation axiom (not an admitted prior-work axiom).

  Verify with `#print axioms EL.sound` (no axioms) /
  `#print axioms EL.complete_via_canon` (only Lean foundation:
  `propext`, `Classical.choice`, `Quot.sound`).
-/

namespace ELKSDD
namespace EL

-- ============================================================
-- 1. Concept syntax (atoms + ⊓ + ⊤ + ⊥ + ∃R.C)
-- ============================================================

inductive Concept : Type where
  | atom : Nat → Concept
  | conj : Concept → Concept → Concept
  | top  : Concept
  | bot  : Concept
  | exist : Nat → Concept → Concept   -- ∃R.C, role index R : Nat
  deriving DecidableEq

/-- An EL axiom of the form `C ⊑ D`. -/
abbrev Axiom := Concept × Concept

/-- An EL ontology is a list of GCIs. -/
abbrev Ontology := List Axiom

-- ============================================================
-- 2. Tarskian semantics
-- ============================================================

/-- An interpretation over domain `α` assigns each atom name a
    unary predicate (concept extension), and each role name a
    binary relation (role extension). -/
structure Interp (α : Type) where
  ext_concept : Nat → α → Prop
  ext_role    : Nat → α → α → Prop

/-- Recursive concept evaluation. -/
def Interp.eval {α : Type} (I : Interp α) : Concept → α → Prop
  | .atom n, x => I.ext_concept n x
  | .conj A B, x => I.eval A x ∧ I.eval B x
  | .top, _ => True
  | .bot, _ => False
  | .exist R C, x => ∃ y, I.ext_role R x y ∧ I.eval C y

/-- An interpretation satisfies an axiom `C ⊑ D` iff every domain
    element in the extension of `C` is also in the extension of `D`. -/
def Interp.satisfiesAxiom {α : Type} (I : Interp α) (ax : Axiom) : Prop :=
  ∀ x, I.eval ax.1 x → I.eval ax.2 x

/-- An interpretation satisfies an ontology iff it satisfies every
    axiom. -/
def Interp.satisfies {α : Type} (I : Interp α) (O : Ontology) : Prop :=
  ∀ ax, ax ∈ O → I.satisfiesAxiom ax

/-- Semantic concept entailment. -/
def Entails (O : Ontology) (C D : Concept) : Prop :=
  ∀ {α : Type} (I : Interp α), I.satisfies O →
    ∀ x, I.eval C x → I.eval D x

-- ============================================================
-- 3. ELK calculus for EL with conjunction and existentials
-- ============================================================

inductive Sat (O : Ontology) : Concept → Concept → Prop where
  | refl       : ∀ C, Sat O C C
  | top        : ∀ C, Sat O C .top
  | base       : ∀ {C D}, (C, D) ∈ O → Sat O C D
  | trans      : ∀ {C D E}, Sat O C D → Sat O D E → Sat O C E
  | conj_left  : ∀ {C D₁ D₂}, Sat O C (.conj D₁ D₂) → Sat O C D₁
  | conj_right : ∀ {C D₁ D₂}, Sat O C (.conj D₁ D₂) → Sat O C D₂
  | conj_intro : ∀ {C D₁ D₂}, Sat O C D₁ → Sat O C D₂ → Sat O C (.conj D₁ D₂)
  | bot_elim   : ∀ {C D}, Sat O C .bot → Sat O C D
  /-- R⁺_∃ : from `C ⊑ ∃R.D` and `D ⊑ E`, derive `C ⊑ ∃R.E`.
      (Side condition `∃R.E ∈ Sub(O)` dropped; sound regardless.) -/
  | exist_prop : ∀ {C R D E},
      Sat O C (.exist R D) → Sat O D E → Sat O C (.exist R E)
  /-- R_⊥-∃ : from `C ⊑ ∃R.D` and `D ⊑ ⊥`, derive `C ⊑ ⊥`. -/
  | exist_bot  : ∀ {C R D},
      Sat O C (.exist R D) → Sat O D .bot → Sat O C .bot

-- ============================================================
-- 4. Soundness of ELK
-- ============================================================

/-- **Soundness of ELK** for the role fragment of EL. Every
    saturation atom is semantically entailed. Induction on the
    derivation, one case per ELK rule. -/
theorem sound (O : Ontology) {C D : Concept} (h : Sat O C D) :
    Entails O C D := by
  induction h with
  | refl C =>
      intro α I _ x hx
      exact hx
  | top C =>
      intro α I _ x _
      trivial
  | base hax =>
      intro α I hO x hx
      exact hO _ hax x hx
  | trans _ _ ihCD ihDE =>
      intro α I hO x hx
      exact ihDE I hO x (ihCD I hO x hx)
  | conj_left _ ih =>
      intro α I hO x hx
      exact (ih I hO x hx).1
  | conj_right _ ih =>
      intro α I hO x hx
      exact (ih I hO x hx).2
  | conj_intro _ _ ih₁ ih₂ =>
      intro α I hO x hx
      exact ⟨ih₁ I hO x hx, ih₂ I hO x hx⟩
  | bot_elim _ ih =>
      intro α I hO x hx
      exact (ih I hO x hx).elim
  | exist_prop _ _ ihCRD ihDE =>
      intro α I hO x hx
      obtain ⟨y, hRxy, hDy⟩ := ihCRD I hO x hx
      exact ⟨y, hRxy, ihDE I hO y hDy⟩
  | exist_bot _ _ ihCRD ihDbot =>
      intro α I hO x hx
      obtain ⟨y, _, hDy⟩ := ihCRD I hO x hx
      exact (ihDbot I hO y hDy).elim

-- ============================================================
-- 5. Canonical (term) model with role extension
-- ============================================================

/-- Domain: concepts that are not derivably unsatisfiable. -/
def CanonDom (O : Ontology) : Type :=
  {C : Concept // ¬ Sat O C .bot}

/-- Canonical interpretation: atom extensions via `Sat`-membership;
    role extension `R(x, y)` iff `Sat O x.val (∃R.y.val)`. -/
def canon (O : Ontology) : Interp (CanonDom O) where
  ext_concept n x   := Sat O x.val (.atom n)
  ext_role    R x y := Sat O x.val (.exist R y.val)

-- ============================================================
-- 6. Eval ↔ Sat correspondence on the canonical model
-- ============================================================

/-- Universal correspondence: for *every* domain element `x`,
    `eval D x` matches `Sat O x.val D`. The `.exist` case uses the
    role-extension definition above plus `exist_prop` (forward)
    and the `exist_bot` rule together with `x.property` to handle
    the inconsistent-codomain case (backward). -/
theorem canon_eval (O : Ontology) :
    ∀ (D : Concept) (x : CanonDom O),
      (canon O).eval D x ↔ Sat O x.val D := by
  intro D
  induction D with
  | atom n =>
      intro _; exact Iff.rfl
  | conj A B ihA ihB =>
      intro x
      constructor
      · rintro ⟨hA, hB⟩
        exact Sat.conj_intro ((ihA x).mp hA) ((ihB x).mp hB)
      · intro hAB
        exact ⟨(ihA x).mpr (Sat.conj_left hAB),
               (ihB x).mpr (Sat.conj_right hAB)⟩
  | top =>
      intro _
      exact ⟨fun _ => Sat.top _, fun _ => trivial⟩
  | bot =>
      intro x
      exact ⟨fun h => h.elim, fun h => (x.property h).elim⟩
  | exist R E ihE =>
      intro x
      constructor
      · rintro ⟨y, hRxy, hEy⟩
        have hSatE : Sat O y.val E := (ihE y).mp hEy
        exact Sat.exist_prop hRxy hSatE
      · intro hSat
        by_cases hEbot : Sat O E .bot
        · exact (x.property (Sat.exist_bot hSat hEbot)).elim
        · let y : CanonDom O := ⟨E, hEbot⟩
          refine ⟨y, hSat, ?_⟩
          exact (ihE y).mpr (Sat.refl _)

-- ============================================================
-- 7. Canonical model satisfies the ontology
-- ============================================================

theorem canon_satisfies (O : Ontology) : (canon O).satisfies O := by
  intro ax hax x hx
  rw [canon_eval] at hx ⊢
  exact Sat.trans hx (Sat.base hax)

-- ============================================================
-- 8. Completeness theorems
-- ============================================================

/-- Helper: completeness via the canonical model, for any
    "endpoint" concept C and target D. Specialised below to the
    paper's atomic-shape conclusions. -/
theorem complete_via_canon (O : Ontology) (C D : Concept)
    (h : Entails O C D) :
    Sat O C D := by
  by_cases hCbot : Sat O C .bot
  · exact Sat.bot_elim hCbot
  · let x : CanonDom O := ⟨C, hCbot⟩
    have hcanon := canon_satisfies O
    have hxC : (canon O).eval C x := by
      rw [canon_eval]; exact Sat.refl _
    have hxD : (canon O).eval D x := h _ hcanon x hxC
    rw [canon_eval] at hxD
    exact hxD

/-- ELK soundness for atomic-atomic subsumption. -/
theorem sound_atomSub (O : Ontology) (A B : Nat)
    (h : Sat O (.atom A) (.atom B)) :
    Entails O (.atom A) (.atom B) := sound O h

/-- ELK completeness for atomic-atomic subsumption. -/
theorem complete_atomSub (O : Ontology) (A B : Nat)
    (h : Entails O (.atom A) (.atom B)) :
    Sat O (.atom A) (.atom B) :=
  complete_via_canon O _ _ h

-- ============================================================
-- 9. Disjointness (n-ary atomic) — soundness and completeness
-- ============================================================

/-- Right-folded conjunction. -/
def conjList : List Concept → Concept
  | [] => .top
  | [C] => C
  | C :: rest => .conj C (conjList rest)

theorem sound_disj (O : Ontology) (As : List Concept)
    (h : Sat O (conjList As) .bot) :
    Entails O (conjList As) .bot := sound O h

theorem complete_disj (O : Ontology) (As : List Concept)
    (h : Entails O (conjList As) .bot) :
    Sat O (conjList As) .bot := complete_via_canon O _ _ h

-- ============================================================
-- 10. Atomic unsatisfiability — soundness and completeness
-- ============================================================

theorem sound_unsat (O : Ontology) (A : Nat)
    (h : Sat O (.atom A) .bot) :
    Entails O (.atom A) .bot := sound O h

theorem complete_unsat (O : Ontology) (A : Nat)
    (h : Entails O (.atom A) .bot) :
    Sat O (.atom A) .bot := complete_via_canon O _ _ h

-- ============================================================
-- 11. Existential link — soundness and completeness
-- ============================================================

/-- ELK soundness for the link case `E ⊑ ∃R.C` (E, C atomic). -/
theorem sound_link (O : Ontology) (E : Nat) (R : Nat) (C : Nat)
    (h : Sat O (.atom E) (.exist R (.atom C))) :
    Entails O (.atom E) (.exist R (.atom C)) := sound O h

/-- ELK completeness for the link case. -/
theorem complete_link (O : Ontology) (E : Nat) (R : Nat) (C : Nat)
    (h : Entails O (.atom E) (.exist R (.atom C))) :
    Sat O (.atom E) (.exist R (.atom C)) := complete_via_canon O _ _ h

-- ============================================================
-- 12. Worked example: O = { 0 ⊑ ∃R.1, 1 ⊑ 2 } ⊨ 0 ⊑ ∃R.2
-- ============================================================

/-- Example ontology mixing atomic and existential axioms. -/
def exampleOntology : Ontology :=
  [(.atom 0, .exist 0 (.atom 1)),
   (.atom 1, .atom 2)]

/-- Sat-derivation: `0 ⊑ ∃R.2` (R = role index 0). -/
theorem example_sat : Sat exampleOntology (.atom 0) (.exist 0 (.atom 2)) := by
  have h1 : Sat exampleOntology (.atom 0) (.exist 0 (.atom 1)) :=
    Sat.base (by simp [exampleOntology])
  have h2 : Sat exampleOntology (.atom 1) (.atom 2) :=
    Sat.base (by simp [exampleOntology])
  exact Sat.exist_prop h1 h2

/-- Hence `0 ⊑ ∃R.2` is entailed (mechanical fact, no admits). -/
theorem example_entails :
    Entails exampleOntology (.atom 0) (.exist 0 (.atom 2)) :=
  sound_link exampleOntology 0 0 2 example_sat

-- ============================================================
-- 13. Cyclic-ontology counterexample (no side-condition saturation
--     produces unboundedly many distinct atoms)
-- ============================================================

/-- `nestedExist k C` = `∃R.∃R...∃R.C` with k nested existentials
    over role index 0. -/
def nestedExist : Nat → Concept → Concept
  | 0, C => C
  | n + 1, C => .exist 0 (nestedExist n C)

/-- The cyclic ontology used in the counterexample. -/
def cyclicO : Ontology := [(.atom 0, .exist 0 (.atom 0))]

/-- For every k, `Sat cyclicO (.atom 0) (nestedExist k (.atom 0))`. -/
theorem cyclicO_unbounded_sat (k : Nat) :
    Sat cyclicO (.atom 0) (nestedExist k (.atom 0)) := by
  induction k with
  | zero => exact Sat.refl _
  | succ n ih =>
      have hbase : Sat cyclicO (.atom 0) (.exist 0 (.atom 0)) :=
        Sat.base (by simp [cyclicO])
      exact Sat.exist_prop hbase ih

/-- For atomic seed concept `.atom 0`, `nestedExist` is injective on
    the depth parameter. The constructor mismatch between `.atom`
    and `.exist` rules out the off-diagonal cases. -/
theorem nestedExist_atom_inj :
    ∀ i j : Nat,
      nestedExist i (.atom 0) = nestedExist j (.atom 0) → i = j := by
  intro i
  induction i with
  | zero =>
      intro j hij
      cases j with
      | zero => rfl
      | succ m =>
          simp only [nestedExist] at hij
          exact Concept.noConfusion hij
  | succ n ih =>
      intro j hij
      cases j with
      | zero =>
          simp only [nestedExist] at hij
          exact Concept.noConfusion hij
      | succ m =>
          simp only [nestedExist, Concept.exist.injEq] at hij
          exact congrArg (· + 1) (ih m hij.2)

end EL
end ELKSDD
