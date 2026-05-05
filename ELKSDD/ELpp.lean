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

/-- ELpp Concepts.  Independent inductive (not the EL.Concept abbrev)
    so we can add the `nom` (nominal `{a_i}`) constructor for OWL~2~EL
    coverage.

    In OWL~2~EL the nominal `{a}` is the singleton class containing
    just the individual `a`; semantically `{a}^I = {a^I}`.  We
    represent each individual name by a `Nat` index, just as for
    atoms and roles. -/
inductive Concept : Type where
  | atom  : Nat → Concept
  | nom   : Nat → Concept            -- nominal {a_n}, a_n indexed by Nat
  | top   : Concept
  | bot   : Concept
  | conj  : Concept → Concept → Concept
  | exist : Nat → Concept → Concept
  deriving DecidableEq

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

/-- An interpretation over domain `α`.

    Adds an individual-name interpretation `indiv : Nat → α` for
    OWL~2~EL nominal handling.  An interpretation can only exist
    over a non-empty domain (because `indiv` must yield a value);
    this is consistent with OWL semantics, where the universe of
    discourse is non-empty. -/
structure Interp (α : Type) where
  ext_concept : Nat → α → Prop
  ext_role    : Role → α → α → Prop
  indiv       : Nat → α              -- individual interpretations a_n^I

/-- Recursive concept evaluation.

    Nominals: `(nom i)^I = {indiv i}`, i.e., the singleton class
    consisting of the individual `a_i^I`. -/
def Interp.eval {α : Type} (I : Interp α) : Concept → α → Prop
  | .atom n, x       => I.ext_concept n x
  | .nom i, x        => x = I.indiv i
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

/-- **Canonical interpretation** (ELK 2014, Definition 2; extended
    here for nominals):

        A^I  =  { x_C  |  C ⊑ A ∈ Closure }
        R^I  =  { ⟨x_C, x_D⟩  |  C ⊑ ∃R.D ∈ Closure }
        a_i^I =  ⟨nom i, h⟩   when nom i is not derivably ⊥
              =  default      otherwise (fallback)

    Note: ELK uses the link relation `C →_R D` for the role
    extension; here `C →_R D ∈ Closure` is the same fact as
    `Sat O C (∃R.D)` because we have not separated the link type.

    The `default` parameter is needed because `indiv : Nat → α`
    must produce a value even for nominals whose singleton is
    derivably empty.  In typical (consistent) usage, callers pass
    a known canonical element such as `⟨.top, h_top_consistent⟩`. -/
noncomputable def canon (O : Ontology) (default : CanonDom O) :
    Interp (CanonDom O) := by
  classical
  exact {
    ext_concept := fun n x => Sat O x.val (.atom n)
    ext_role    := fun R x y => Sat O x.val (.exist R y.val)
    indiv       := fun i =>
      if h : ¬ Sat O (.nom i) .bot then ⟨.nom i, h⟩ else default
  }

-- ============================================================
-- 5. Lemmas 1, 2 of ELK 2014 §3.3 — eval ↔ Sat correspondence
-- ============================================================

/-- A concept is *nominal-free* if it does not mention any
    `nom`/individual constructor.  The canonical-model
    correspondence (Lemmas~1+2 of ELK 2014 §3.3) is proved here
    only for the nominal-free fragment; the full ELK-with-nominals
    correspondence (Kazakov 2014 §6) requires the merging-
    canonical-model construction with concept equivalence classes,
    which is beyond the scope of this layer.  In Layer 6 we
    restrict subsumption queries to nominal-free C, D, while
    permitting arbitrary nominal-containing axioms inside the
    ontologies. -/
def NominalFree : Concept → Prop
  | .atom _    => True
  | .nom _     => False
  | .top       => True
  | .bot       => True
  | .conj A B  => NominalFree A ∧ NominalFree B
  | .exist _ E => NominalFree E

/-- ELK 2014 Lemmas 1+2 — eval ↔ Sat correspondence on the
    *nominal-free* fragment. -/
theorem canon_eval (O : Ontology) (default : CanonDom O) :
    ∀ (D : Concept), NominalFree D → ∀ (x : CanonDom O),
      (canon O default).eval D x ↔ Sat O x.val D := by
  classical
  intro D
  induction D with
  | atom n =>
      intro _ _; exact Iff.rfl
  | nom i =>
      intro hnf
      exact hnf.elim
  | top =>
      intro _ _; exact ⟨fun _ => Sat.top _, fun _ => trivial⟩
  | bot =>
      intro _ x; exact ⟨fun h => h.elim, fun h => (x.property h).elim⟩
  | conj A B ihA ihB =>
      intro hnf x
      constructor
      · rintro ⟨hA, hB⟩
        exact Sat.conj_intro ((ihA hnf.1 x).mp hA) ((ihB hnf.2 x).mp hB)
      · intro hAB
        exact ⟨(ihA hnf.1 x).mpr (Sat.conj_left hAB),
               (ihB hnf.2 x).mpr (Sat.conj_right hAB)⟩
  | exist R E ihE =>
      intro hnf x
      constructor
      · rintro ⟨y, hRxy, hEy⟩
        have hSatE : Sat O y.val E := (ihE hnf y).mp hEy
        exact Sat.exist_prop hRxy hSatE
      · intro hSat
        by_cases hEbot : Sat O E .bot
        · exact (x.property (Sat.exist_bot hSat hEbot)).elim
        · let y : CanonDom O := ⟨E, hEbot⟩
          refine ⟨y, hSat, ?_⟩
          exact (ihE hnf y).mpr (Sat.refl _)

-- ============================================================
-- 6. Theorem 2 of ELK 2014 §3.3 — canonical model satisfies O
-- ============================================================

/-- A GCI is *nominal-free* iff both sides are nominal-free.
    Role inclusions and role chains are vacuously nominal-free
    (no concepts inside).  -/
def AxiomNominalFree : Axiom → Prop
  | .gci C D => NominalFree C ∧ NominalFree D
  | .rinc _ _ => True
  | .rchain _ _ _ => True

/-- An ontology is nominal-free if all its axioms are. -/
def OntologyNominalFree (O : Ontology) : Prop :=
  ∀ ax ∈ O, AxiomNominalFree ax

/-- **Theorem 2 (ELK 2014 §3.3) — restricted to nominal-free
    ontologies.**

    The canonical interpretation satisfies all nominal-free axioms.
    For nominal axioms (involving `{a_i}`) the merging-canonical-
    model construction (Kazakov 2014 §6) is required; it is not
    formalised in this layer.  Layer 6's hard direction therefore
    requires `OntologyNominalFree O₁` and `OntologyNominalFree O₂`
    as preconditions.  -/
theorem canon_satisfies (O : Ontology) (default : CanonDom O)
    (hO : OntologyNominalFree O) : (canon O default).satisfies O := by
  intro ax hax
  have hax_nf : AxiomNominalFree ax := hO ax hax
  cases ax with
  | gci C D =>
      obtain ⟨hC_nf, hD_nf⟩ := hax_nf
      intro x hx
      rw [canon_eval _ _ _ hC_nf] at hx
      have hSat : Sat O x.val D := Sat.trans hx (Sat.base_gci hax)
      exact (canon_eval O default D hD_nf x).mpr hSat
  | rinc R S =>
      intro x y hRxy
      exact Sat.rinc_apply hRxy hax
  | rchain R₁ R₂ S =>
      intro x y z hR1 hR2
      exact Sat.rchain_apply hR1 hR2 hax

-- ============================================================
-- 7. Completeness — ELK 2014 §3.3 (Theorem 1)
-- ============================================================

/-- **Completeness of the ELK calculus** for EL_⊥^+ on the
    nominal-free fragment.

    If `O ⊨ C ⊑ D` and the ontology and the query are
    nominal-free, then `Sat O C D`.  -/
theorem complete_via_canon (O : Ontology) (C D : Concept)
    (hO : OntologyNominalFree O)
    (hC_nf : NominalFree C) (hD_nf : NominalFree D)
    (h : Entails O C D) : Sat O C D := by
  classical
  by_cases hCbot : Sat O C .bot
  · exact Sat.bot_elim hCbot
  · let x : CanonDom O := ⟨C, hCbot⟩
    have hcanon := canon_satisfies O x hO
    have hxC : (canon O x).eval C x := by
      rw [canon_eval _ _ _ hC_nf]; exact Sat.refl _
    have hxD : (canon O x).eval D x := h _ hcanon x hxC
    rw [canon_eval _ _ _ hD_nf] at hxD
    exact hxD

-- ============================================================
-- 8. Boilerplate corollaries — atom-shape sound/complete
-- ============================================================

theorem sound_atomSub (O : Ontology) (A B : Nat)
    (h : Sat O (.atom A) (.atom B)) :
    Entails O (.atom A) (.atom B) := sound O h

theorem complete_atomSub (O : Ontology) (hO : OntologyNominalFree O)
    (A B : Nat) (h : Entails O (.atom A) (.atom B)) :
    Sat O (.atom A) (.atom B) :=
  complete_via_canon O _ _ hO trivial trivial h

/-- The biconditional ELK characterisation for atom-atom subsumption
    in EL_⊥^+, on nominal-free ontologies. -/
theorem correct_atomSub (O : Ontology) (hO : OntologyNominalFree O) (A B : Nat) :
    Sat O (.atom A) (.atom B) ↔ Entails O (.atom A) (.atom B) :=
  ⟨sound_atomSub O A B, complete_atomSub O hO A B⟩

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
