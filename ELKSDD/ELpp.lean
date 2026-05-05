/-
  ELKSDD/ELpp.lean
  ----------------
  Full EL_⊥^+ (= EL++ minus nominals and concrete domains) following
  Kazakov, Krötzsch, Simančík 2014 "The Incredible ELK", §3.
  This extends `ELKSDD.EL` (concept-only fragment) with

    * role inclusion axioms      R ⊑ S
    * role composition axioms    R₁ ∘ R₂ ⊑ S

  Calculus (ELK 2014, Figure 1):
    R₀ refl, R⊤, R⊥-bot, R⊓⁻ left/right, R⊓⁺, R∃ (existential prop.),
    R⊑ (told subsumption / transitivity), R_H (role hierarchy),
    R∘ (role chain).

  Soundness AND completeness are proved end-to-end via the canonical
  (term) model construction of ELK 2014 §3.3 (Definition 2,
  Lemmas 1 and 2, Theorem 2). The role-axiom satisfaction in the
  canonical model is verified directly from the calculus rules
  R_H and R∘ (Theorem 2 cases α = R ⊑ S and α = R₁ ∘ R₂ ⊑ S).

  References:
    [Kazakov 2014]    Kazakov, Y., Krötzsch, M., Simančík, F.
                      The Incredible ELK: From Polynomial Procedures
                      to Efficient Reasoning with EL Ontologies.
                      J. Automated Reasoning 53(1):1-61, 2014.
                      Sections 3.1 (rules), 3.3 (canonical-model proof).
    [BBL 2005]        Baader, F., Brandt, S., Lutz, C.
                      Pushing the EL Envelope.
                      LTCS-Report 05-01 / IJCAI 2005.  Definition of
                      EL++ syntax/semantics (Table 1).

  Lean dependencies declared:
    * Concept syntax re-uses `ELKSDD.EL.Concept` (atoms, ⊤, ⊥, ⊓, ∃R.C).
    * No Mathlib.  No prior-work axioms (all results re-proved).
    * Classical reasoning: `Classical.byCases` in `complete_via_canon`
      introduces `Classical.choice` as a Lean foundation axiom.
-/

import ELKSDD.EL

namespace ELKSDD
namespace ELpp

/-- Concepts: re-exported from `ELKSDD.EL`.  Atoms, ⊤, ⊥,
    conjunction, existential restriction. -/
abbrev Concept := EL.Concept

/-- Role names: identified with `Nat`. -/
abbrev Role : Type := Nat

/-- EL_⊥^+ axioms.  Three kinds:

      gci    C D       — concept inclusion C ⊑ D
      rinc   R S       — role inclusion R ⊑ S
      rchain R₁ R₂ S   — role composition R₁ ∘ R₂ ⊑ S

    (Domain restrictions, range restrictions, nominals, concrete
    domains: not included in this layer; see Layer 2 for the
    BBL 2008 range-restriction elimination.) -/
inductive Axiom : Type where
  | gci    : Concept → Concept → Axiom
  | rinc   : Role → Role → Axiom
  | rchain : Role → Role → Role → Axiom
  deriving DecidableEq

/-- An EL_⊥^+ ontology is a list of axioms. -/
abbrev Ontology := List Axiom

-- ============================================================
-- 1. Tarskian semantics (ELK 2014 Table 1)
-- ============================================================

/-- An interpretation over domain `α`. -/
structure Interp (α : Type) where
  ext_concept : Nat → α → Prop
  ext_role    : Role → α → α → Prop

/-- Recursive concept evaluation. -/
def Interp.eval {α : Type} (I : Interp α) : Concept → α → Prop
  | .atom n, x       => I.ext_concept n x
  | .top, _          => True
  | .bot, _          => False
  | .conj A B, x     => I.eval A x ∧ I.eval B x
  | .exist R C, x    => ∃ y, I.ext_role R x y ∧ I.eval C y

/-- Axiom satisfaction. -/
def Interp.satisfiesAxiom {α : Type} (I : Interp α) : Axiom → Prop
  | .gci C D        => ∀ x, I.eval C x → I.eval D x
  | .rinc R S       => ∀ x y, I.ext_role R x y → I.ext_role S x y
  | .rchain R₁ R₂ S => ∀ x y z, I.ext_role R₁ x y → I.ext_role R₂ y z →
                                  I.ext_role S x z

/-- Ontology satisfaction. -/
def Interp.satisfies {α : Type} (I : Interp α) (O : Ontology) : Prop :=
  ∀ ax, ax ∈ O → I.satisfiesAxiom ax

/-- Semantic concept-subsumption entailment. -/
def Entails (O : Ontology) (C D : Concept) : Prop :=
  ∀ {α : Type} (I : Interp α), I.satisfies O →
    ∀ x, I.eval C x → I.eval D x

-- ============================================================
-- 2. Calculus (ELK 2014 Fig 1, extended)
-- ============================================================

/-- The closure relation.  Constructors mirror the ELK rules:

      refl          ↔  R₀
      top           ↔  R⊤
      base_gci      ↔  axiom-base for GCIs (used as one premise of R⊑)
      trans         ↔  composition of two derived subsumptions; subsumes
                       ELK's R⊑ which uses one told premise (`base_gci`).
                       Strictly more permissive than ELK's R⊑ but with
                       the same closure.
      conj_left     ↔  R⊓⁻ (first projection)
      conj_right    ↔  R⊓⁻ (second projection)
      conj_intro    ↔  R⊓⁺
      bot_elim      ↔  R⊥ (ex falso)
      exist_prop    ↔  R∃ (∃R.D ∧ D ⊑ E ⇒ ∃R.E)
      exist_bot     ↔  R⊥-∃ (existing in EL.lean; ∃R.D ∧ D ⊑ ⊥ ⇒ ⊥)
      rinc_apply    ↔  R_H (role hierarchy)
      rchain_apply  ↔  R∘ (role chain) -/
inductive Sat (O : Ontology) : Concept → Concept → Prop where
  | refl       : ∀ C, Sat O C C
  | top        : ∀ C, Sat O C .top
  | base_gci   : ∀ {C D}, Axiom.gci C D ∈ O → Sat O C D
  | trans      : ∀ {C D E}, Sat O C D → Sat O D E → Sat O C E
  | conj_left  : ∀ {C D₁ D₂}, Sat O C (.conj D₁ D₂) → Sat O C D₁
  | conj_right : ∀ {C D₁ D₂}, Sat O C (.conj D₁ D₂) → Sat O C D₂
  | conj_intro : ∀ {C D₁ D₂}, Sat O C D₁ → Sat O C D₂ →
                                Sat O C (.conj D₁ D₂)
  | bot_elim   : ∀ {C D}, Sat O C .bot → Sat O C D
  | exist_prop : ∀ {C R D E},
      Sat O C (.exist R D) → Sat O D E → Sat O C (.exist R E)
  | exist_bot  : ∀ {C R D},
      Sat O C (.exist R D) → Sat O D .bot → Sat O C .bot
  | rinc_apply : ∀ {C R S D},
      Sat O C (.exist R D) → Axiom.rinc R S ∈ O →
        Sat O C (.exist S D)
  | rchain_apply : ∀ {C R₁ R₂ S D E},
      Sat O C (.exist R₁ D) → Sat O D (.exist R₂ E) →
      Axiom.rchain R₁ R₂ S ∈ O → Sat O C (.exist S E)

-- ============================================================
-- 3. Soundness of the calculus
-- ============================================================

/-- **Soundness of the ELK calculus** for EL_⊥^+ (ELK 2014, Theorem
    of §3.1).  Every `Sat`-derivable subsumption is semantically
    entailed.  Proof: induction on the derivation, one case per rule. -/
theorem sound (O : Ontology) {C D : Concept} (h : Sat O C D) :
    Entails O C D := by
  induction h with
  | refl _ => intro α I _ x hx; exact hx
  | top _ => intro α I _ x _; trivial
  | base_gci hax =>
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
  | rinc_apply _ hax ih =>
      intro α I hO x hx
      obtain ⟨y, hRxy, hDy⟩ := ih I hO x hx
      have hRincSat : I.satisfiesAxiom (Axiom.rinc _ _) := hO _ hax
      exact ⟨y, hRincSat x y hRxy, hDy⟩
  | rchain_apply _ _ hax ihCR1D ihDR2E =>
      intro α I hO x hx
      obtain ⟨y, hR1xy, hDy⟩ := ihCR1D I hO x hx
      obtain ⟨z, hR2yz, hEz⟩ := ihDR2E I hO y hDy
      have hChainSat : I.satisfiesAxiom (Axiom.rchain _ _ _) := hO _ hax
      exact ⟨z, hChainSat x y z hR1xy hR2yz, hEz⟩

-- ============================================================
-- 4. Canonical (term) model — ELK 2014 Definition 2
-- ============================================================

/-- **Canonical domain** (ELK 2014, Definition 2):
        Δ^I  =  { x_C  |  C ⊑ ⊥ ∉ Closure }
    realised in Lean as the subtype of concepts not derivably
    unsatisfiable. -/
def CanonDom (O : Ontology) : Type :=
  {C : Concept // ¬ Sat O C .bot}

/-- **Canonical interpretation** (ELK 2014, Definition 2):

        A^I  =  { x_C  |  C ⊑ A ∈ Closure }
        R^I  =  { ⟨x_C, x_D⟩  |  C ⊑ ∃R.D ∈ Closure }

    Note: ELK uses the link relation `C →_R D` for the role
    extension; here `C →_R D ∈ Closure` is the same fact as
    `Sat O C (∃R.D)` because we have not separated the link type. -/
def canon (O : Ontology) : Interp (CanonDom O) where
  ext_concept n x   := Sat O x.val (.atom n)
  ext_role    R x y := Sat O x.val (.exist R y.val)

-- ============================================================
-- 5. Lemmas 1, 2 of ELK 2014 §3.3 — eval ↔ Sat correspondence
-- ============================================================

/-- **Lemma 1 + Lemma 2 of ELK 2014 §3.3 (combined).**
    For each `x_C ∈ Δ^I` and concept `D`,
        x_C ∈ D^I  ↔  Sat O C D.

    Proof: structural induction on `D`.  Cases:

      D = atom n   immediate from `canon.ext_concept = Sat O · (atom n)`.
      D = ⊤        forward: trivial; backward: `Sat.top _`.
      D = ⊥        forward: contradiction with `eval ⊥ x = False`;
                   backward: forces `Sat O C ⊥`, contradicting
                   `x.property : ¬ Sat O C ⊥`.
      D = D₁ ⊓ D₂  forward via `conj_intro`, backward via
                   `conj_left/conj_right`.
      D = ∃R.E     forward via `exist_prop`; backward by
                   case-split on `Sat O E ⊥`: if so, `exist_bot` to
                   contradict `x.property`; else use `y := ⟨E, _⟩`
                   and refl. -/
theorem canon_eval (O : Ontology) :
    ∀ (D : Concept) (x : CanonDom O),
      (canon O).eval D x ↔ Sat O x.val D := by
  intro D
  induction D with
  | atom n =>
      intro _; exact Iff.rfl
  | top =>
      intro _; exact ⟨fun _ => Sat.top _, fun _ => trivial⟩
  | bot =>
      intro x; exact ⟨fun h => h.elim, fun h => (x.property h).elim⟩
  | conj A B ihA ihB =>
      intro x
      constructor
      · rintro ⟨hA, hB⟩
        exact Sat.conj_intro ((ihA x).mp hA) ((ihB x).mp hB)
      · intro hAB
        exact ⟨(ihA x).mpr (Sat.conj_left hAB),
               (ihB x).mpr (Sat.conj_right hAB)⟩
  | exist R E ihE =>
      intro x
      constructor
      · rintro ⟨y, hRxy, hEy⟩
        have hSatE : Sat O y.val E := (ihE y).mp hEy
        -- canon's role extension says hRxy : Sat O x.val (∃R.y.val);
        -- by exist_prop with hSatE we get Sat O x.val (∃R.E).
        exact Sat.exist_prop hRxy hSatE
      · intro hSat
        by_cases hEbot : Sat O E .bot
        · exact (x.property (Sat.exist_bot hSat hEbot)).elim
        · let y : CanonDom O := ⟨E, hEbot⟩
          refine ⟨y, hSat, ?_⟩
          exact (ihE y).mpr (Sat.refl _)

-- ============================================================
-- 6. Theorem 2 of ELK 2014 §3.3 — canonical model satisfies O
-- ============================================================

/-- **Theorem 2 (ELK 2014 §3.3).**  The canonical interpretation
    satisfies the ontology.  Proof: case-analysis on the axiom kind.

      α = C ⊑ D:       Use `canon_eval` and `Sat.base_gci`/`trans`.
      α = R ⊑ S:       For ⟨x_C, x_D⟩ ∈ R^I we have
                         Sat O C (∃R.D); by `rinc_apply` with
                         `hax : Axiom.rinc R S ∈ O` we get
                         Sat O C (∃S.D), i.e. ⟨x_C, x_D⟩ ∈ S^I.
      α = R₁ ∘ R₂ ⊑ S: For ⟨x_C, x_D⟩ ∈ R₁^I and ⟨x_D, x_E⟩ ∈ R₂^I
                         we have Sat O C (∃R₁.D) and Sat O D (∃R₂.E);
                         by `rchain_apply` we get Sat O C (∃S.E),
                         i.e. ⟨x_C, x_E⟩ ∈ S^I. -/
theorem canon_satisfies (O : Ontology) : (canon O).satisfies O := by
  intro ax hax
  cases ax with
  | gci C D =>
      intro x hx
      rw [canon_eval] at hx
      have hSat : Sat O x.val D := Sat.trans hx (Sat.base_gci hax)
      exact (canon_eval O D x).mpr hSat
  | rinc R S =>
      intro x y hRxy
      -- hRxy : (canon O).ext_role R x y, i.e. Sat O x.val (∃R.y.val).
      -- Goal:  (canon O).ext_role S x y, i.e. Sat O x.val (∃S.y.val).
      exact Sat.rinc_apply hRxy hax
  | rchain R₁ R₂ S =>
      intro x y z hR1 hR2
      -- hR1 : Sat O x.val (∃R₁.y.val); hR2 : Sat O y.val (∃R₂.z.val).
      -- Goal: Sat O x.val (∃S.z.val).
      exact Sat.rchain_apply hR1 hR2 hax

-- ============================================================
-- 7. Completeness — ELK 2014 §3.3 (Theorem 1)
-- ============================================================

/-- **Completeness of the ELK calculus** for EL_⊥^+ (ELK 2014,
    Theorem 1).  If `O ⊨ C ⊑ D` then either `Sat O C D` or
    `Sat O C ⊥` (the latter giving `Sat O C D` via `bot_elim`).

    Proof: case-split on `Sat O C ⊥`.  If yes, `bot_elim`.
    Otherwise, instantiate the canonical model at `x := ⟨C, _⟩`,
    use `canon_eval` to convert `Sat O C C := Sat.refl C` into
    `(canon O).eval C x`, apply the entailment hypothesis to
    extract `(canon O).eval D x`, and convert back via
    `canon_eval`. -/
theorem complete_via_canon (O : Ontology) (C D : Concept)
    (h : Entails O C D) : Sat O C D := by
  by_cases hCbot : Sat O C .bot
  · exact Sat.bot_elim hCbot
  · let x : CanonDom O := ⟨C, hCbot⟩
    have hcanon := canon_satisfies O
    have hxC : (canon O).eval C x := by
      rw [canon_eval]; exact Sat.refl _
    have hxD : (canon O).eval D x := h _ hcanon x hxC
    rw [canon_eval] at hxD
    exact hxD

-- ============================================================
-- 8. Boilerplate corollaries — atom-shape sound/complete
-- ============================================================

theorem sound_atomSub (O : Ontology) (A B : Nat)
    (h : Sat O (.atom A) (.atom B)) :
    Entails O (.atom A) (.atom B) := sound O h

theorem complete_atomSub (O : Ontology) (A B : Nat)
    (h : Entails O (.atom A) (.atom B)) :
    Sat O (.atom A) (.atom B) :=
  complete_via_canon O _ _ h

/-- The biconditional ELK characterisation for atom-atom subsumption
    in EL_⊥^+. -/
theorem correct_atomSub (O : Ontology) (A B : Nat) :
    Sat O (.atom A) (.atom B) ↔ Entails O (.atom A) (.atom B) :=
  ⟨sound_atomSub O A B, complete_atomSub O A B⟩

-- ============================================================
-- 9. Worked example: role hierarchy
-- ============================================================
-- O = { 0 ⊑ ∃r₀.1, r₀ ⊑ r₁ } ⊨ 0 ⊑ ∃r₁.1
-- (concept names 0, 1, role names r₀ = 0, r₁ = 1)

def exampleRH : Ontology :=
  [Axiom.gci (.atom 0) (.exist 0 (.atom 1)),
   Axiom.rinc 0 1]

theorem exampleRH_sat : Sat exampleRH (.atom 0) (.exist 1 (.atom 1)) := by
  have h1 : Sat exampleRH (.atom 0) (.exist 0 (.atom 1)) :=
    Sat.base_gci (List.mem_cons_self)
  exact Sat.rinc_apply h1 (List.mem_cons.mpr (Or.inr List.mem_cons_self))

theorem exampleRH_entails :
    Entails exampleRH (.atom 0) (.exist 1 (.atom 1)) :=
  sound exampleRH exampleRH_sat

-- ============================================================
-- 10. Worked example: role chain
-- ============================================================
-- O = { 0 ⊑ ∃r₀.1, 1 ⊑ ∃r₁.2, r₀ ∘ r₁ ⊑ r₂ } ⊨ 0 ⊑ ∃r₂.2

def exampleChain : Ontology :=
  [Axiom.gci (.atom 0) (.exist 0 (.atom 1)),
   Axiom.gci (.atom 1) (.exist 1 (.atom 2)),
   Axiom.rchain 0 1 2]

theorem exampleChain_sat : Sat exampleChain (.atom 0) (.exist 2 (.atom 2)) := by
  have h1 : Sat exampleChain (.atom 0) (.exist 0 (.atom 1)) :=
    Sat.base_gci List.mem_cons_self
  have h2 : Sat exampleChain (.atom 1) (.exist 1 (.atom 2)) :=
    Sat.base_gci (List.mem_cons.mpr (Or.inr List.mem_cons_self))
  exact Sat.rchain_apply h1 h2
    (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr List.mem_cons_self))))

theorem exampleChain_entails :
    Entails exampleChain (.atom 0) (.exist 2 (.atom 2)) :=
  sound exampleChain exampleChain_sat

end ELpp
end ELKSDD
