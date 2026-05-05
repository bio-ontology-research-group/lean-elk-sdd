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
  | self  : Nat → Concept            -- ObjectHasSelf(R) — Self(R)
  | top   : Concept
  | bot   : Concept
  | conj  : Concept → Concept → Concept
  | exist : Nat → Concept → Concept
  deriving DecidableEq

/-- Role names: identified with `Nat`. -/
abbrev Role : Type := Nat

/-- EL_⊥^+ axioms (extended for full OWL 2 EL minus datatypes):

      gci       C D        — concept inclusion C ⊑ D
      rinc      R S        — role inclusion R ⊑ S
      rchain    R₁ R₂ S    — role composition R₁ ∘ R₂ ⊑ S
      range     R C        — ObjectPropertyRange(R, C):
                             ∀x y. R(x, y) → y ∈ C
      reflexive R          — ReflexiveObjectProperty(R):
                             ∀x. R(x, x)
      hasKey    C [R₁..Rₙ] — HasKey(C, R₁, …, Rₙ): named-individual
                             merge condition. -/
inductive Axiom : Type where
  | gci       : Concept → Concept → Axiom
  | rinc      : Role → Role → Axiom
  | rchain    : Role → Role → Role → Axiom
  | range     : Role → Concept → Axiom
  | reflexive : Role → Axiom
  | hasKey    : Concept → List Role → Axiom
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
    consisting of the individual `a_i^I`.

    Self-restrictions: `(self R)^I = {x : R(x, x)}`, the set of
    elements that are R-related to themselves. -/
def Interp.eval {α : Type} (I : Interp α) : Concept → α → Prop
  | .atom n, x       => I.ext_concept n x
  | .nom i, x        => x = I.indiv i
  | .self R, x       => I.ext_role R x x
  | .top, _          => True
  | .bot, _          => False
  | .conj A B, x     => I.eval A x ∧ I.eval B x
  | .exist R C, x    => ∃ y, I.ext_role R x y ∧ I.eval C y

/-- Axiom satisfaction.

    For HasKey: OWL 2 EL semantics restricts the constraint to
    *named individuals*; if a, b are named (i.e., interpreted via
    `I.indiv`) and both lie in the key class, and they share named
    R-targets for every key role, then they coincide.  -/
def Interp.satisfiesAxiom {α : Type} (I : Interp α) : Axiom → Prop
  | .gci C D        => ∀ x, I.eval C x → I.eval D x
  | .rinc R S       => ∀ x y, I.ext_role R x y → I.ext_role S x y
  | .rchain R₁ R₂ S => ∀ x y z, I.ext_role R₁ x y → I.ext_role R₂ y z →
                                  I.ext_role S x z
  | .range R C      => ∀ x y, I.ext_role R x y → I.eval C y
  | .reflexive R    => ∀ x, I.ext_role R x x
  | .hasKey C rs    => ∀ a b : Nat,
      I.eval C (I.indiv a) → I.eval C (I.indiv b) →
        (∀ R ∈ rs, ∃ c : Nat,
          I.ext_role R (I.indiv a) (I.indiv c) ∧
          I.ext_role R (I.indiv b) (I.indiv c)) →
        I.indiv a = I.indiv b

/-- Ontology satisfaction. -/
def Interp.satisfies {α : Type} (I : Interp α) (O : Ontology) : Prop :=
  ∀ ax, ax ∈ O → I.satisfiesAxiom ax

/-- Semantic concept-subsumption entailment. -/
def Entails (O : Ontology) (C D : Concept) : Prop :=
  ∀ {α : Type} (I : Interp α), I.satisfies O →
    ∀ x, I.eval C x → I.eval D x

-- ============================================================
-- 2a. Role-hierarchy ancestor (rinc-closure)
-- ============================================================

/-- **Reflexive-transitive closure of `rinc` axioms in `O`.**

    `RincAncestor O R S` holds iff `R ⊑* S` in `O`'s role hierarchy:
    either `R = S` (refl), or there's an intermediate `T` with
    `RincAncestor O R T` and `Axiom.rinc T S ∈ O` (step).

    Used in the new Sat rule `range_via_rincStar` to lift range axioms
    of any rinc-ancestor of `R` into refinements of R-existential
    witnesses, and in `canon`'s `ext_role` guard to ensure R-edge
    targets satisfy not only R-ranges but also S-ranges for every
    `S` with `R ⊑* S`. -/
inductive RincAncestor (O : Ontology) : Role → Role → Prop where
  | refl : ∀ R, RincAncestor O R R
  | step : ∀ {R S T}, RincAncestor O R S → Axiom.rinc S T ∈ O →
           RincAncestor O R T

/-- Transitivity of `RincAncestor`. -/
theorem RincAncestor.trans {O : Ontology} {R S T : Role}
    (h₁ : RincAncestor O R S) (h₂ : RincAncestor O S T) :
    RincAncestor O R T := by
  induction h₂ with
  | refl => exact h₁
  | step _ hStep ih => exact RincAncestor.step ih hStep

/-- **Edge-transport along rinc-ancestor**.  In any model satisfying
    `O`, an `R`-edge transfers to a `S`-edge for every `S` with
    `R ⊑* S` in `O`'s rinc-closure.  By induction on the ancestor chain,
    using each rinc axiom's satisfaction as a single-step transport. -/
theorem ext_role_rincStar {α : Type} {I : Interp α} {O : Ontology}
    (hO : I.satisfies O) :
    ∀ {R S : Role}, RincAncestor O R S → ∀ {x y : α},
    I.ext_role R x y → I.ext_role S x y := by
  intro R S hAnc x y hRxy
  induction hAnc with
  | refl => exact hRxy
  | step _ hStep ih =>
      have hRincSat : I.satisfiesAxiom (Axiom.rinc _ _) := hO _ hStep
      exact hRincSat x y ih

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
  /-- **Range refinement** (BBL 2008 §3.3).  From `C ⊑ ∃R.D` and
      `range R E ∈ O`, derive `C ⊑ ∃R.(D ⊓ E)`: the witness is in
      both the original filler and the range concept.  Sound; the
      analogous unconstrained `D ⊑ E` rule is **not** sound. -/
  | range_apply : ∀ {C R D E},
      Sat O C (.exist R D) → Axiom.range R E ∈ O →
        Sat O C (.exist R (.conj D E))
  /-- **Reflexive role**.  `reflexive R ∈ O` ⇒ for any concept `C`,
      `C ⊑ ∃R.C` (every member has an R-self-loop, which is itself
      an R-successor in `C`). -/
  | reflexive_apply : ∀ {C R},
      Axiom.reflexive R ∈ O → Sat O C (.exist R C)
  /-- **Self introduction**.  From `C ⊑ Self(R)`, derive `C ⊑ ∃R.C`:
      every member of `C` has R(c, c), so c is its own R-witness. -/
  | self_intro : ∀ {C R},
      Sat O C (.self R) → Sat O C (.exist R C)
  /-- **Reflexive ⇒ Self**.  If `R` is reflexive, every concept `C`
      is subsumed by `Self(R)`: every domain element has `R(x, x)`. -/
  | reflexive_self : ∀ {C R},
      Axiom.reflexive R ∈ O → Sat O C (.self R)
  /-- **Self ∩ Range**.  From `C ⊑ Self(R)` and `Range(R, E)`, derive
      `C ⊑ E`: every `c ∈ C` has `R(c, c)`, and every R-target lies
      in `E`, so `c ∈ E`. -/
  | self_range : ∀ {C R E},
      Sat O C (.self R) → Axiom.range R E ∈ O → Sat O C E
  /-- **Range via rinc-closure** (transitive role-hierarchy refinement).

      From `Sat O C (∃R.D)`, `RincAncestor O R S` (i.e., `R ⊑* S` via
      a chain of rinc axioms), and `Axiom.range S E ∈ O`, refine the
      R-witness to also lie in `E`.

      Soundness: in any model satisfying O, an R-target of a C-instance
      is also an S-target via the rinc-chain (each rinc axiom transfers
      edges).  By `Range S E`, S-targets are in E.  Hence the R-target
      is in `D ⊓ E`.

      This generalises the existing `range_apply` rule (which is the
      `RincAncestor.refl` case where `S = R`).  -/
  | range_via_rincStar : ∀ {C R S D E},
      Sat O C (.exist R D) → RincAncestor O R S →
      Axiom.range S E ∈ O →
      Sat O C (.exist R (.conj D E))
  /-- **Self transfer along rinc-closure**.  `C ⊑ Self(R)` and `R ⊑* S`
      jointly imply `C ⊑ Self(S)`.

      Soundness: in any model, every `c ∈ C` has `R(c, c)`.  By the
      rinc-chain, `S(c, c)`.  So `c ∈ Self(S)`. -/
  | rinc_self_star : ∀ {C R S},
      Sat O C (.self R) → RincAncestor O R S → Sat O C (.self S)
  /-- **Nominal symmetry**.  Subsumption between two nominals is
      symmetric: `Sat O (.nom i) (.nom j) → Sat O (.nom j) (.nom i)`.

      Soundness: `Entails O (.nom i) (.nom j)` says every model
      satisfies `(nom i)^I ⊆ (nom j)^I`, i.e., `{a_i^I} ⊆ {a_j^I}`,
      i.e., `a_i^I = a_j^I`.  Equality is symmetric, so
      `a_j^I = a_i^I` ⇒ `(nom j)^I ⊆ (nom i)^I` ⇒ `Entails O (.nom j) (.nom i)`.

      This rule is essential for the merging-quotient canonical model
      (Kazakov 2014 §6) used to handle nominal-RHS GCIs (shapes 2 and 4
      in `ELKSDD.Merging`).  Without it, the nominal-equivalence
      relation `Sat O (.nom i) (.nom j)` is not provably symmetric in
      the calculus, so it does not form a Setoid. -/
  | nom_symm : ∀ {i j},
      Sat O (.nom i) (.nom j) → Sat O (.nom j) (.nom i)
  /-- **HasKey-induced nominal merging**.  If two nominals `a_i, a_j`
      both lie in a key-class `C` and share named R-targets (provided
      via a Skolem witness function `cs : Role → Nat`) for every key
      role, then `a_i = a_j`.

      OWL 2 EL `HasKey(C, R₁, …, Rₙ)`: any two named individuals that
      are both in `C` and share `Rₖ`-fillers for every key role must
      coincide.  The semantic reading: this is a *named-individual*
      merge condition (it does not constrain anonymous successors).

      The witness function `cs : Role → Nat` provides, per role `R ∈ rs`,
      the shared individual index `cs R` for which both `a_i` and `a_j`
      have an R-edge to `cs R`.  This is a Skolemized form of the
      semantic ∃-witnesses; using a function avoids a nested `Exists`
      under the recursive `Sat`, which Lean's kernel rejects in
      strictly-positive inductive datatypes.

      Soundness: in any `M⊨O`, the premises give `a_i^M ∈ C^M`,
      `a_j^M ∈ C^M`, and shared `Rₖ`-targets at `(cs Rₖ)^M` for each k.
      The HasKey axiom satisfaction in M then forces `a_i^M = a_j^M`.
      Hence `Entails O (.nom i) (.nom j)`.

      This rule is essential for the merging quotient with HasKey
      (Kazakov 2014 §6, full version): without it, HasKey-induced
      mergers between nominal classes are not derivable in the
      calculus, so the canonical model cannot satisfy HasKey axioms. -/
  | hasKey_apply : ∀ {a b : Nat} {C : Concept} {rs : List Role}
      (cs : Role → Nat),
      Sat O (.nom a) C → Sat O (.nom b) C →
      Axiom.hasKey C rs ∈ O →
      (∀ R, R ∈ rs → Sat O (.nom a) (.exist R (.nom (cs R)))) →
      (∀ R, R ∈ rs → Sat O (.nom b) (.exist R (.nom (cs R)))) →
      Sat O (.nom a) (.nom b)

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
  | range_apply _ hax ih =>
      intro α I hO x hx
      obtain ⟨y, hRxy, hDy⟩ := ih I hO x hx
      have hRange : I.satisfiesAxiom (Axiom.range _ _) := hO _ hax
      -- Witness y satisfies D (from ih) AND E (from range axiom),
      -- hence the conjunction.
      exact ⟨y, hRxy, hDy, hRange x y hRxy⟩
  | reflexive_apply hax =>
      intro α I hO x hx
      have hRefl : I.satisfiesAxiom (Axiom.reflexive _) := hO _ hax
      -- x is its own R-witness, and it lies in C by hypothesis.
      exact ⟨x, hRefl x, hx⟩
  | self_intro _ ih =>
      intro α I hO x hx
      -- ih gives us I.eval (.self R) x, i.e., R(x, x).
      have hSelf : I.ext_role _ x x := ih I hO x hx
      exact ⟨x, hSelf, hx⟩
  | reflexive_self hax =>
      intro α I hO x _
      have hRefl : I.satisfiesAxiom (Axiom.reflexive _) := hO _ hax
      -- I.eval (.self R) x = I.ext_role R x x, given by reflexivity.
      exact hRefl x
  | self_range _ hax ih =>
      intro α I hO x hx
      -- ih gives us I.eval (.self R) x, i.e., R(x, x).
      have hSelf : I.ext_role _ x x := ih I hO x hx
      have hRange : I.satisfiesAxiom (Axiom.range _ _) := hO _ hax
      exact hRange x x hSelf
  | range_via_rincStar _ hAnc hRange ih =>
      intro α I hO x hx
      -- ih: I.eval (∃R.D) x, i.e., ∃ y. R(x, y) ∧ y ∈ D.
      obtain ⟨y, hRxy, hDy⟩ := ih I hO x hx
      -- Transport the R-edge to an S-edge along the rinc-ancestor chain.
      have hSxy := ext_role_rincStar hO hAnc hRxy
      -- y is an S-target, so by Range S E, y ∈ E.
      have hRangeSat : I.satisfiesAxiom (Axiom.range _ _) := hO _ hRange
      have hEy : I.eval _ y := hRangeSat x y hSxy
      exact ⟨y, hRxy, hDy, hEy⟩
  | rinc_self_star _ hAnc ih =>
      intro α I hO x hx
      -- ih : I.eval (.self R) x = I.ext_role R x x.
      have hRxx : I.ext_role _ x x := ih I hO x hx
      -- Transport the R-self-loop to an S-self-loop.
      exact ext_role_rincStar hO hAnc hRxx
  | @nom_symm i j _ ih =>
      intro α I hO x hx
      -- hx : I.eval (.nom j) x, i.e., x = I.indiv j.
      -- ih : ∀ y. I.eval (.nom i) y → I.eval (.nom j) y, i.e.,
      --        y = I.indiv i → y = I.indiv j.
      -- Apply ih on y = I.indiv i (using rfl) to get I.indiv i = I.indiv j.
      -- Goal: I.eval (.nom i) x, i.e., x = I.indiv i.
      have hii : I.eval (.nom i) (I.indiv i) := show I.indiv i = I.indiv i from rfl
      have hij : I.indiv i = I.indiv j := ih I hO _ hii
      show x = I.indiv i
      have hxj : x = I.indiv j := hx
      exact hxj.trans hij.symm
  | @hasKey_apply a b C rs cs _ _ h_ax _ _ ih_aC ih_bC ih_a_roles ih_b_roles =>
      intro α I hO x hx
      -- hx : I.eval (.nom a) x, i.e., x = I.indiv a.
      -- Goal: I.eval (.nom b) x, i.e., x = I.indiv b.
      show x = I.indiv b
      -- Establish premises of HasKey in I.
      have h_aC_M : I.eval C (I.indiv a) :=
        ih_aC I hO _ (rfl : I.indiv a = I.indiv a)
      have h_bC_M : I.eval C (I.indiv b) :=
        ih_bC I hO _ (rfl : I.indiv b = I.indiv b)
      have h_roles_M : ∀ R, R ∈ rs → ∃ c : Nat,
          I.ext_role R (I.indiv a) (I.indiv c) ∧
          I.ext_role R (I.indiv b) (I.indiv c) := by
        intro R hR
        -- Use the Skolem witness cs R; both a, b have R-edge to cs R.
        have h_a_M : I.eval (.exist R (.nom (cs R))) (I.indiv a) :=
          ih_a_roles R hR I hO _ (rfl : I.indiv a = I.indiv a)
        have h_b_M : I.eval (.exist R (.nom (cs R))) (I.indiv b) :=
          ih_b_roles R hR I hO _ (rfl : I.indiv b = I.indiv b)
        -- I.eval (.exist R (.nom c)) y = ∃ z, R(y, z) ∧ z = I.indiv c.
        obtain ⟨y_a, hRa, hya⟩ := h_a_M
        obtain ⟨y_b, hRb, hyb⟩ := h_b_M
        subst hya; subst hyb
        exact ⟨cs R, hRa, hRb⟩
      -- Apply HasKey axiom satisfaction in I.
      have hHK_axiom : I.satisfiesAxiom (.hasKey C rs) := hO _ h_ax
      have h_eq : I.indiv a = I.indiv b :=
        hHK_axiom a b h_aC_M h_bC_M h_roles_M
      have hxa : x = I.indiv a := hx
      exact hxa.trans h_eq

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
    here for nominals and OWL 2 EL range axioms):

        A^I  =  { x_C  |  C ⊑ A ∈ Closure }
        R^I  =  { ⟨x_C, x_D⟩  |  C ⊑ ∃R.D ∈ Closure  AND
                                  ∀E. Range(R, E) ∈ O ⇒ D ⊑ E ∈ Closure }
        a_i^I =  ⟨nom i, h⟩   when nom i is not derivably ⊥
              =  default      otherwise (fallback)

    The role extension carries an *additional range guard*: an R-
    edge from `x_C` to `x_D` requires that `D` is subsumed by every
    range concept of `R` (BBL 2008 §3.3 effective-subsumer dynamic).
    This guard is vacuously satisfied when `O` has no range axioms
    (so the original ELK 2014 model is recovered as a special case),
    and is essential to make canon ⊨ Range(R, E) axioms.

    The `default` parameter is needed because `indiv : Nat → α`
    must produce a value even for nominals whose singleton is
    derivably empty.  In typical (consistent) usage, callers pass
    a known canonical element such as `⟨.top, h_top_consistent⟩`. -/
noncomputable def canon (O : Ontology) (default : CanonDom O) :
    Interp (CanonDom O) := by
  classical
  exact {
    ext_concept := fun n x => Sat O x.val (.atom n)
    ext_role    := fun R x y =>
      Sat O x.val (.exist R y.val) ∧
      ∀ S E, RincAncestor O R S → Axiom.range S E ∈ O → Sat O y.val E
    indiv       := fun i =>
      if h : ¬ Sat O (.nom i) .bot then ⟨.nom i, h⟩ else default
  }

/-- **Range-witness helper** (BBL 2008 §3.3 effective-subsumer dynamic
    extended with role-hierarchy closure).

    Given `Sat O C (∃R.E)`, produce a refined witness `D'` that
    (i) is still an R-witness from `C`, (ii) subsumes the original
    `E` (so the IH on `eval E ·` applies), and (iii) lies in every
    range concept of `R` AND of every `S` with `RincAncestor O R S`.

    Construction: iterate over the axiom list of `O`.  For each
    `range S F ∈ O` whose role `S` is an rinc-ancestor of `R`,
    refine the witness via `Sat.range_via_rincStar` (the new sound
    rule that subsumes `range_apply`).  Direct R-ranges are handled
    as the `RincAncestor.refl` special case. -/
theorem range_witness (O : Ontology) (R : Role) {C E : Concept}
    (h : Sat O C (.exist R E)) :
    ∃ D', Sat O C (.exist R D') ∧ Sat O D' E ∧
          (∀ S F, RincAncestor O R S → Axiom.range S F ∈ O → Sat O D' F) := by
  classical
  suffices haux : ∀ axList : Ontology, (∀ ax ∈ axList, ax ∈ O) →
      ∃ D', Sat O C (.exist R D') ∧ Sat O D' E ∧
            (∀ S F, RincAncestor O R S → Axiom.range S F ∈ axList →
                    Sat O D' F) by
    exact haux O (fun _ h => h)
  intro axList
  induction axList with
  | nil =>
      intro _
      exact ⟨E, h, Sat.refl _, fun _ _ _ hMem => (List.not_mem_nil hMem).elim⟩
  | cons ax rest ih =>
      intro hSub
      have hAxIn : ax ∈ O := hSub ax List.mem_cons_self
      have hSubRest : ∀ a ∈ rest, a ∈ O :=
        fun a ha => hSub a (List.mem_cons.mpr (Or.inr ha))
      obtain ⟨D₁, hExist₁, hDE₁, hAll₁⟩ := ih hSubRest
      by_cases hMatch : ∃ S F, ax = Axiom.range S F
      · obtain ⟨S, F, hFE⟩ := hMatch
        subst hFE
        -- ax is `range S F`.  Decide whether `S` is a rinc-ancestor of `R`.
        by_cases hAnc : RincAncestor O R S
        · -- Refine via range_via_rincStar.
          refine ⟨.conj D₁ F, Sat.range_via_rincStar hExist₁ hAnc hAxIn,
                  Sat.trans (Sat.conj_left (Sat.refl _)) hDE₁, ?_⟩
          intro S' F' hAnc' hF'
          rcases List.mem_cons.mp hF' with hEq | hRest
          · injection hEq with hSEq hFEq
            subst hSEq hFEq
            exact Sat.conj_right (Sat.refl _)
          · exact Sat.trans (Sat.conj_left (Sat.refl _)) (hAll₁ S' F' hAnc' hRest)
        · -- `S` is NOT a rinc-ancestor of `R`.  Skip refinement.
          refine ⟨D₁, hExist₁, hDE₁, ?_⟩
          intro S' F' hAnc' hF'
          rcases List.mem_cons.mp hF' with hEq | hRest
          · injection hEq with hSEq hFEq
            subst hSEq hFEq
            -- hAnc' : RincAncestor O R S — but we negated.
            exact absurd hAnc' hAnc
          · exact hAll₁ S' F' hAnc' hRest
      · -- ax is not a range axiom at all.
        refine ⟨D₁, hExist₁, hDE₁, ?_⟩
        intro S' F' hAnc' hF'
        rcases List.mem_cons.mp hF' with hEq | hRest
        · exact absurd ⟨S', F', hEq.symm⟩ hMatch
        · exact hAll₁ S' F' hAnc' hRest

-- ============================================================
-- 5. Lemmas 1, 2 of ELK 2014 §3.3 — eval ↔ Sat correspondence
-- ============================================================

/-- Predicate selecting the *core nominal-free fragment* — concepts
    built from `atom`, `top`, `bot`, `conj`, `exist`.  This is the
    fragment for which the canonical-model correspondence is proved.
    Both `nom` (true nominals) and `self` (self-restrictions) require
    additional canonical-model machinery (Kazakov 2014 §6) and are
    excluded.  -/
def NominalFree : Concept → Prop
  | .atom _    => True
  | .nom _     => False
  | .self _    => False
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
  | self R =>
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
        -- new ext_role bundles a range guard; only first conjunct needed
        have hSatExist := hRxy.1
        have hSatE : Sat O y.val E := (ihE hnf y).mp hEy
        exact Sat.exist_prop hSatExist hSatE
      · intro hSat
        -- BBL 2008 §3.3 effective-subsumer trick (extended with rinc-closure):
        -- refine the witness to absorb ranges of every rinc-ancestor of R.
        obtain ⟨D', hExist', hDE', hAllRanges⟩ := range_witness O R hSat
        by_cases hDbot : Sat O D' .bot
        · exact (x.property (Sat.exist_bot hExist' hDbot)).elim
        · let y : CanonDom O := ⟨D', hDbot⟩
          refine ⟨y, ⟨hExist', hAllRanges⟩, ?_⟩
          exact (ihE hnf y).mpr hDE'

-- ============================================================
-- 6. Theorem 2 of ELK 2014 §3.3 — canonical model satisfies O
-- ============================================================

/-- A GCI is *nominal-free* iff both sides are nominal-free.
    Role inclusions and role chains are vacuously nominal-free
    (no concepts inside).

    With the BBL 2008 §3.3 effective-subsumer dynamic in `canon`'s
    `ext_role` (range-guard) plus `Sat.reflexive_self`/`self_range`
    rules, the canonical model satisfies `range R E` (when `E` is
    nominal-free) and `reflexive R` axioms.  HasKey remains gated
    pending the merging-canonical-model construction (Kazakov 2014
    §6) which requires a quotient-by-nominal-equivalence not yet
    formalised here.  -/
def AxiomNominalFree : Axiom → Prop
  | .gci C D => NominalFree C ∧ NominalFree D
  | .rinc _ _ => True
  | .rchain _ _ _ => True
  | .range _ E => NominalFree E
  | .reflexive _ => True
  -- HasKey remains gated.  The sound `Sat` extension is in place;
  -- canonical-model satisfaction needs Kazakov 2014 §6 merging.
  | .hasKey _ _ => False

/-- An ontology is nominal-free if all its axioms are. -/
def OntologyNominalFree (O : Ontology) : Prop :=
  ∀ ax ∈ O, AxiomNominalFree ax

/-- **Range-chain-safety**: chain targets have no range axiom in their
    rinc-hierarchy.

    `RangeChainSafe O` requires: for every chain `R₁ ∘ R₂ ⊑ S ∈ O` and every
    rinc-ancestor `T` of `S`, no range axiom `range T E ∈ O` exists.

    *Why is this needed?*  The canonical-model rchain case requires
    `Sat O z.val E` for the chain target `z` and any range concept `E` of
    an rinc-ancestor of `S`.  Semantically this is *not* derivable from
    the calculus alone: chain composition asserts that *some* element
    of `z.val^I` is reached via the chain (and is thus in `E`), but it
    does not constrain *every* element of `z.val` to be in `E`.  Closing
    the rchain case in `canon_satisfies` therefore requires either:
      (i) a richer canonical domain that tracks chain history (heavy
          machinery; future work), or
      (ii) a precondition like `RangeChainSafe O` that makes the
          range-guard transfer vacuous when chain composition occurs.

    This predicate is the option-(ii) gate.  It permits arbitrary use
    of `range R E` axioms on roles outside chain-target hierarchies,
    arbitrary chains on roles whose rinc-targets carry no ranges, and
    arbitrary role hierarchy + range interactions (those are handled
    by `RincAncestor` + `range_via_rincStar` directly).  -/
def RangeChainSafe (O : Ontology) : Prop :=
  ∀ R₁ R₂ S T E,
    Axiom.rchain R₁ R₂ S ∈ O →
    RincAncestor O S T →
    Axiom.range T E ∉ O

/-- **Theorem 2 (ELK 2014 §3.3) — restricted to nominal-free
    ontologies.**

    The canonical interpretation satisfies all nominal-free axioms.
    For nominal axioms (involving `{a_i}`) the merging-canonical-
    model construction (Kazakov 2014 §6) is required; it is not
    formalised in this layer.  Layer 6's hard direction therefore
    requires `OntologyNominalFree O₁` and `OntologyNominalFree O₂`
    as preconditions.  -/
theorem canon_satisfies (O : Ontology) (default : CanonDom O)
    (hO : OntologyNominalFree O) (hO_safe : RangeChainSafe O) :
    (canon O default).satisfies O := by
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
      obtain ⟨hRxySat, hRxyAncRanges⟩ := hRxy
      refine ⟨Sat.rinc_apply hRxySat hax, ?_⟩
      -- New ext_role guard: ∀ T E. RincAncestor O R T → Range T E ∈ O →
      -- Sat O y.val E.  Need the analogous guard for S: ∀ T E.
      -- RincAncestor O S T → Range T E ∈ O → Sat O y.val E.
      -- Argument: any S-ancestor T is also an R-ancestor (by transitivity
      -- through `rinc R S ∈ O`), so the guard transfers cleanly.
      intro T E hAncST hRange
      -- Build RincAncestor O R T from RincAncestor O R S (single step)
      -- + RincAncestor O S T (given).
      have hAncRS : RincAncestor O R S := RincAncestor.step (RincAncestor.refl R) hax
      have hAncRT : RincAncestor O R T := RincAncestor.trans hAncRS hAncST
      exact hRxyAncRanges T E hAncRT hRange
  | rchain R₁ R₂ S =>
      intro x y z hR1 hR2
      obtain ⟨hR1Sat, _⟩ := hR1
      obtain ⟨hR2Sat, _⟩ := hR2
      refine ⟨Sat.rchain_apply hR1Sat hR2Sat hax, ?_⟩
      -- Range-guard transfer under role chain.  Closed via the
      -- `RangeChainSafe O` precondition: any rinc-ancestor T of the
      -- chain target S has no range axiom, so the guard is vacuously
      -- discharged.
      intro T E hAnc hRange
      exact (hO_safe R₁ R₂ S T E hax hAnc hRange).elim
  | range R C =>
      -- AxiomNominalFree (.range R C) = NominalFree C.  The ext_role
      -- guard at S = R via `RincAncestor.refl` directly gives the
      -- range constraint.
      have hC_nf : NominalFree C := hax_nf
      intro x y hxy
      have hSatYC : Sat O y.val C :=
        hxy.2 R C (RincAncestor.refl R) hax
      exact (canon_eval O default C hC_nf y).mpr hSatYC
  | reflexive R =>
      -- New ext_role guard: ∀ T E. RincAncestor O R T → Range T E ∈ O →
      -- Sat O x.val E.  Combine `Sat.reflexive_self` (Self R) +
      -- `Sat.rinc_self_star` (lift Self R to Self T along the rinc
      -- chain) + `Sat.self_range` (Self T + Range T E ⇒ Sat E).
      intro x
      refine ⟨Sat.reflexive_apply hax, ?_⟩
      intro T E hAnc hE
      have hSelfR : Sat O x.val (.self R) := Sat.reflexive_self hax
      have hSelfT : Sat O x.val (.self T) := Sat.rinc_self_star hSelfR hAnc
      exact Sat.self_range hSelfT hE
  | hasKey C rs =>
      exact hax_nf.elim

-- ============================================================
-- 6c. LHS-nominal extension — ABox-style nominals
-- ============================================================
--
-- **Coverage**: GCIs of shape `gci (nom i) D` (with D nominal-free) —
-- i.e., `ClassAssertion(D, a_i)` in OWL terms.  This is a common
-- ABox pattern: asserting that individual `a_i` is a member of
-- class `D`.  Combined with `Sat.rinc_apply` etc., this also
-- handles role assertions like `gci (nom i) (∃R.C)` (under
-- the existing canon's exist_role construction).
--
-- **What is NOT covered**: GCIs with direct nominal RHS
-- (`gci C (nom i)`, `gci (nom i) (nom j)`).  These require
-- the merging canonical model (Kazakov 2014 §6) — distinct
-- canonical concepts that share a nominal must be identified
-- via a quotient construction — which remains future work.
--
-- **Soundness gate**: `AllNomInhabited O` — every nominal index
-- in O is consistent (no `Sat O (nom i) ⊥`).  This ensures
-- `canon.indiv i = ⟨nom i, _⟩` (no fallback to default), which
-- is what the proof relies on.  Globally consistent ontologies
-- automatically satisfy this.

/-- Loose axiom-level nominal-freeness: the LHS of a GCI may be
    a nominal `nom i` (instead of being nominal-free).  RHS, ranges,
    and other axiom positions remain nominal-free. -/
def AxiomNomLHS : Axiom → Prop
  | .gci C D       => (NominalFree C ∨ ∃ i, C = .nom i) ∧ NominalFree D
  | .rinc _ _      => True
  | .rchain _ _ _  => True
  | .range _ E     => NominalFree E
  | .reflexive _   => True
  | .hasKey _ _    => False

/-- An ontology has only LHS-nominal-permissive axioms. -/
def OntologyNomLHS (O : Ontology) : Prop :=
  ∀ ax ∈ O, AxiomNomLHS ax

/-- AxiomNominalFree implies AxiomNomLHS (strict ⇒ permissive). -/
theorem AxiomNominalFree_imp_NomLHS (ax : Axiom) :
    AxiomNominalFree ax → AxiomNomLHS ax := by
  cases ax with
  | gci C D       => intro h; exact ⟨Or.inl h.1, h.2⟩
  | rinc _ _      => intro _; trivial
  | rchain _ _ _  => intro _; trivial
  | range _ _     => intro h; exact h
  | reflexive _   => intro _; trivial
  | hasKey _ _    => intro h; exact h.elim

theorem OntologyNominalFree_imp_NomLHS {O : Ontology}
    (hO : OntologyNominalFree O) : OntologyNomLHS O :=
  fun ax hax => AxiomNominalFree_imp_NomLHS ax (hO ax hax)

/-- All nominal indices in `O` are *inhabited*: not derivably empty.
    Globally consistent ontologies satisfy this; in OWL semantics
    individuals always interpret to non-empty singletons, so any
    `Sat O (nom i) ⊥` would mean the ontology contradicts itself
    on `a_i`. -/
def AllNomInhabited (O : Ontology) : Prop :=
  ∀ i, ¬ Sat O (.nom i) .bot

/-- **canon.indiv reduction lemma**.  Under `AllNomInhabited`, every
    nominal index reduces to its specific canonical element. -/
theorem canon_indiv_eq (O : Ontology) (default : CanonDom O) (i : Nat)
    (h : ¬ Sat O (.nom i) .bot) :
    (canon O default).indiv i = ⟨.nom i, h⟩ := by
  unfold canon
  simp [dif_pos h]

/-- **Theorem 2 extended — LHS-nominal coverage.**

    Under `OntologyNomLHS O ∧ RangeChainSafe O ∧ AllNomInhabited O`,
    the canonical model satisfies all of `O` — including LHS-nominal
    GCIs (i.e., `ClassAssertion`-style axioms).

    Strategy: the gci case now has two sub-cases:
      * `C` nominal-free: identical to `canon_satisfies`'s gci proof.
      * `C = nom i`: specialise `x` to `canon.indiv i = ⟨nom i, _⟩`
        (forced by `eval (nom i) x = (x = indiv i)`); apply
        `canon_eval` on the nominal-free RHS plus `base_gci` to close.
    -/
theorem canon_satisfies_nomLHS (O : Ontology) (default : CanonDom O)
    (hO : OntologyNomLHS O) (hO_safe : RangeChainSafe O)
    (hO_inhab : AllNomInhabited O) : (canon O default).satisfies O := by
  intro ax hax
  have hax_nf : AxiomNomLHS ax := hO ax hax
  cases ax with
  | gci C D =>
      obtain ⟨hC_or, hD_nf⟩ := hax_nf
      rcases hC_or with hC_nf | ⟨i, hCi⟩
      · -- Standard nominal-free LHS — identical to canon_satisfies.
        intro x hx
        rw [canon_eval _ _ _ hC_nf] at hx
        have hSat : Sat O x.val D := Sat.trans hx (Sat.base_gci hax)
        exact (canon_eval O default D hD_nf x).mpr hSat
      · -- LHS is `.nom i`.
        subst hCi
        intro x hx
        -- hx : (canon O default).eval (.nom i) x.  By def of eval on nom,
        -- this is `x = (canon O default).indiv i`.
        have hxEq : x = (canon O default).indiv i := hx
        -- Reduce indiv via AllNomInhabited.
        have hi : ¬ Sat O (.nom i) .bot := hO_inhab i
        rw [canon_indiv_eq O default i hi] at hxEq
        -- Now hxEq : x = ⟨.nom i, hi⟩.  Specialise x.
        subst hxEq
        -- Goal: eval D ⟨.nom i, hi⟩ in canon.  Use canon_eval on D.
        rw [canon_eval _ _ _ hD_nf]
        -- Goal: Sat O (.nom i) D.  By base_gci on the axiom.
        exact Sat.base_gci hax
  | rinc R S =>
      intro x y hRxy
      obtain ⟨hRxySat, hRxyAncRanges⟩ := hRxy
      refine ⟨Sat.rinc_apply hRxySat hax, ?_⟩
      intro T E hAncST hRange
      have hAncRS : RincAncestor O R S := RincAncestor.step (RincAncestor.refl R) hax
      have hAncRT : RincAncestor O R T := RincAncestor.trans hAncRS hAncST
      exact hRxyAncRanges T E hAncRT hRange
  | rchain R₁ R₂ S =>
      intro x y z hR1 hR2
      obtain ⟨hR1Sat, _⟩ := hR1
      obtain ⟨hR2Sat, _⟩ := hR2
      refine ⟨Sat.rchain_apply hR1Sat hR2Sat hax, ?_⟩
      intro T E hAnc hRange
      exact (hO_safe R₁ R₂ S T E hax hAnc hRange).elim
  | range R C =>
      have hC_nf : NominalFree C := hax_nf
      intro x y hxy
      have hSatYC : Sat O y.val C :=
        hxy.2 R C (RincAncestor.refl R) hax
      exact (canon_eval O default C hC_nf y).mpr hSatYC
  | reflexive R =>
      intro x
      refine ⟨Sat.reflexive_apply hax, ?_⟩
      intro T E hAnc hE
      have hSelfR : Sat O x.val (.self R) := Sat.reflexive_self hax
      have hSelfT : Sat O x.val (.self T) := Sat.rinc_self_star hSelfR hAnc
      exact Sat.self_range hSelfT hE
  | hasKey C rs =>
      exact hax_nf.elim

/-- **Completeness with LHS-nominal axioms.**

    Combines `canon_satisfies_nomLHS` with the standard canonical-
    model recipe.  Queries are still nominal-free (the canonical
    model's `eval` for direct nominal RHS would require merging,
    which is future work). -/
theorem complete_via_canon_nomLHS (O : Ontology) (C D : Concept)
    (hO : OntologyNomLHS O) (hO_safe : RangeChainSafe O)
    (hO_inhab : AllNomInhabited O)
    (hC_nf : NominalFree C) (hD_nf : NominalFree D)
    (h : Entails O C D) : Sat O C D := by
  classical
  by_cases hCbot : Sat O C .bot
  · exact Sat.bot_elim hCbot
  · let x : CanonDom O := ⟨C, hCbot⟩
    have hcanon := canon_satisfies_nomLHS O x hO hO_safe hO_inhab
    have hxC : (canon O x).eval C x := by
      rw [canon_eval _ _ _ hC_nf]; exact Sat.refl _
    have hxD : (canon O x).eval D x := h _ hcanon x hxC
    rw [canon_eval _ _ _ hD_nf] at hxD
    exact hxD

-- ============================================================
-- 6d. Shallow-exist-nominal RHS — ObjectPropertyAssertion-style
-- ============================================================
--
-- **Coverage**: GCIs of shape `gci C (∃R.(nom i))` —
-- `ObjectPropertyAssertion`-style: every C-element has an R-edge
-- to individual a_i.  This complements LHS-nominal support to
-- cover the bulk of OWL 2 EL ABox patterns.
--
-- **Soundness gate**: this fragment forbids range axioms entirely.
-- The reason is the `ext_role` range-guard: an R-edge to `indiv i =
-- ⟨nom i, _⟩` would need `Sat O (nom i) E` for every range axiom
-- on R's rinc-hierarchy.  Without merging-aware Sat rules, this
-- isn't generally derivable.  Range support over nominal targets
-- requires the merging quotient (future work).

/-- Loose axiom-level predicate covering shape 1 (LHS nominal) AND
    shape 3 (RHS shallow-exist with nominal target):
      * `gci (NF or nom) (NF or ∃R.(nom j))`.

    Range axioms are forbidden in this fragment (the range guard
    on a nominal target requires nominal-merging machinery). -/
def AxiomNomLR : Axiom → Prop
  | .gci C D =>
      (NominalFree C ∨ ∃ i, C = .nom i) ∧
      (NominalFree D ∨ ∃ R i, D = .exist R (.nom i))
  | .rinc _ _ => True
  | .rchain _ _ _ => True
  | .range _ _ => False
  | .reflexive _ => True
  | .hasKey _ _ => False

def OntologyNomLR (O : Ontology) : Prop :=
  ∀ ax ∈ O, AxiomNomLR ax

/-- Under `OntologyNomLR`, no range axioms exist in `O`. -/
theorem AxiomNomLR_no_range {O : Ontology}
    (hO : OntologyNomLR O) : ∀ R E, Axiom.range R E ∉ O := by
  intro R E hax
  have := hO _ hax
  exact this  -- AxiomNomLR (range R E) = False

/-- **Theorem 2 — shallow-exist-nominal RHS coverage.**

    Under `OntologyNomLR ∧ AllNomInhabited`, the canonical model
    satisfies all ABox-flavoured axioms (shape 1 LHS-nominal, plus
    shape 3 RHS-shallow-exist-with-nominal).  The `range _ _` and
    `RangeChainSafe` cases are vacuous here (no range axioms by
    `AxiomNomLR.range = False`). -/
theorem canon_satisfies_nomLR (O : Ontology) (default : CanonDom O)
    (hO : OntologyNomLR O) (hO_inhab : AllNomInhabited O) :
    (canon O default).satisfies O := by
  intro ax hax
  have hax_nf : AxiomNomLR ax := hO ax hax
  cases ax with
  | gci C D =>
      obtain ⟨hC_or, hD_or⟩ := hax_nf
      rcases hC_or with hC_nf | ⟨i, hCi⟩
      · -- LHS nominal-free.
        rcases hD_or with hD_nf | ⟨R, j, hDj⟩
        · -- (NF, NF): standard canon_satisfies gci proof.
          intro x hx
          rw [canon_eval _ _ _ hC_nf] at hx
          have hSat : Sat O x.val D := Sat.trans hx (Sat.base_gci hax)
          exact (canon_eval O default D hD_nf x).mpr hSat
        · -- (NF, ∃R.(nom j)): shape 3.
          subst hDj
          intro x hx
          have hxC : Sat O x.val C := (canon_eval _ _ _ hC_nf x).mp hx
          have hxRj : Sat O x.val (.exist R (.nom j)) :=
            Sat.trans hxC (Sat.base_gci hax)
          have hj : ¬ Sat O (.nom j) .bot := hO_inhab j
          -- Witness: indiv j = ⟨nom j, hj⟩.  Show ext_role R x (indiv j).
          refine ⟨(canon O default).indiv j, ?_, ?_⟩
          · -- ext_role R x (indiv j)
            rw [canon_indiv_eq O default j hj]
            refine ⟨hxRj, ?_⟩
            -- Range guard: vacuous under no-range.
            intro T E _ hRange
            exact (AxiomNomLR_no_range hO T E hRange).elim
          · -- y = indiv j
            rfl
      · -- LHS = nom i.
        subst hCi
        rcases hD_or with hD_nf | ⟨R, j, hDj⟩
        · -- (nom i, NF): shape 1.
          intro x hx
          have hxEq : x = (canon O default).indiv i := hx
          have hi : ¬ Sat O (.nom i) .bot := hO_inhab i
          rw [canon_indiv_eq O default i hi] at hxEq
          subst hxEq
          rw [canon_eval _ _ _ hD_nf]
          exact Sat.base_gci hax
        · -- (nom i, ∃R.(nom j)): combined shapes 1+3.
          subst hDj
          intro x hx
          have hxEq : x = (canon O default).indiv i := hx
          have hi : ¬ Sat O (.nom i) .bot := hO_inhab i
          rw [canon_indiv_eq O default i hi] at hxEq
          subst hxEq
          -- Goal: eval (∃R.(nom j)) ⟨nom i, hi⟩.
          have hSat_iRj : Sat O (.nom i) (.exist R (.nom j)) := Sat.base_gci hax
          have hj : ¬ Sat O (.nom j) .bot := hO_inhab j
          refine ⟨(canon O default).indiv j, ?_, ?_⟩
          · rw [canon_indiv_eq O default j hj]
            refine ⟨hSat_iRj, ?_⟩
            intro T E _ hRange
            exact (AxiomNomLR_no_range hO T E hRange).elim
          · rfl
  | rinc R S =>
      intro x y hRxy
      obtain ⟨hRxySat, _⟩ := hRxy
      refine ⟨Sat.rinc_apply hRxySat hax, ?_⟩
      intro T E _ hRange
      exact (AxiomNomLR_no_range hO T E hRange).elim
  | rchain R₁ R₂ S =>
      intro x y z hR1 hR2
      obtain ⟨hR1Sat, _⟩ := hR1
      obtain ⟨hR2Sat, _⟩ := hR2
      refine ⟨Sat.rchain_apply hR1Sat hR2Sat hax, ?_⟩
      intro T E _ hRange
      exact (AxiomNomLR_no_range hO T E hRange).elim
  | range R C => exact hax_nf.elim
  | reflexive R =>
      intro x
      refine ⟨Sat.reflexive_apply hax, ?_⟩
      intro T E _ hRange
      exact (AxiomNomLR_no_range hO T E hRange).elim
  | hasKey _ _ => exact hax_nf.elim

/-- **Completeness with LHS-and-RHS-shallow nominal axioms**, on
    nominal-free queries.  Direct nominal queries (e.g.,
    `Entails O C (nom i)`) still require the merging canonical
    model and remain future work. -/
theorem complete_via_canon_nomLR (O : Ontology) (C D : Concept)
    (hO : OntologyNomLR O) (hO_inhab : AllNomInhabited O)
    (hC_nf : NominalFree C) (hD_nf : NominalFree D)
    (h : Entails O C D) : Sat O C D := by
  classical
  by_cases hCbot : Sat O C .bot
  · exact Sat.bot_elim hCbot
  · let x : CanonDom O := ⟨C, hCbot⟩
    have hcanon := canon_satisfies_nomLR O x hO hO_inhab
    have hxC : (canon O x).eval C x := by
      rw [canon_eval _ _ _ hC_nf]; exact Sat.refl _
    have hxD : (canon O x).eval D x := h _ hcanon x hxC
    rw [canon_eval _ _ _ hD_nf] at hxD
    exact hxD

-- ============================================================
-- 7. Completeness — ELK 2014 §3.3 (Theorem 1)
-- ============================================================

-- ============================================================
-- 6b. Strict variant — sorry-free range-free completeness
-- ============================================================

/-- A *strict* axiom predicate that **also gates range axioms** on top
    of the nominal/HasKey gating.  Used by `canon_satisfies_strict`
    and `complete_via_canon_strict` below to obtain a sorry-free
    completeness theorem on the range-free fragment.

    This is exactly the predicate that the BBL 2008 §3.3 `eliminateRanges`
    pass (in `RangeNorm.lean`) ensures on its output ontology, so the
    Path-B Lean reduction lands on this strict fragment. -/
def AxiomStrict : Axiom → Prop
  | .gci C D => NominalFree C ∧ NominalFree D
  | .rinc _ _ => True
  | .rchain _ _ _ => True
  | .range _ _ => False
  | .reflexive _ => True
  | .hasKey _ _ => False

/-- An ontology is *strict* if every axiom satisfies `AxiomStrict`. -/
def OntologyStrict (O : Ontology) : Prop :=
  ∀ ax ∈ O, AxiomStrict ax

/-- Strict implies the broader nominal-free predicate.  -/
theorem AxiomStrict_imp_NominalFree (ax : Axiom) :
    AxiomStrict ax → AxiomNominalFree ax := by
  cases ax with
  | gci C D => intro h; exact h
  | rinc _ _ => intro _; trivial
  | rchain _ _ _ => intro _; trivial
  | range _ _ => intro h; exact h.elim
  | reflexive _ => intro _; trivial
  | hasKey _ _ => intro h; exact h.elim

theorem OntologyStrict_imp_NominalFree {O : Ontology}
    (hO : OntologyStrict O) : OntologyNominalFree O :=
  fun ax hax => AxiomStrict_imp_NominalFree ax (hO ax hax)

/-- **Sorry-free `canon_satisfies` on the strict (range-free) fragment.**

    Under `OntologyStrict O` (no range, no hasKey), the canonical
    interpretation satisfies all axioms.  The rinc/rchain cases are
    discharged via the strict gating: the `Range S E ∈ O` premise of
    the range guard is impossible because `AxiomStrict` rules out
    range axioms entirely. -/
theorem canon_satisfies_strict (O : Ontology) (default : CanonDom O)
    (hO : OntologyStrict O) : (canon O default).satisfies O := by
  intro ax hax
  have hax_s : AxiomStrict ax := hO ax hax
  cases ax with
  | gci C D =>
      obtain ⟨hC_nf, hD_nf⟩ := hax_s
      intro x hx
      rw [canon_eval _ _ _ hC_nf] at hx
      have hSat : Sat O x.val D := Sat.trans hx (Sat.base_gci hax)
      exact (canon_eval O default D hD_nf x).mpr hSat
  | rinc R S =>
      intro x y hRxy
      obtain ⟨hRxySat, _⟩ := hRxy
      refine ⟨Sat.rinc_apply hRxySat hax, ?_⟩
      intro T E _ hE
      -- O is range-free under OntologyStrict: hE contradicts AxiomStrict.
      exact (hO _ hE).elim
  | rchain R₁ R₂ S =>
      intro x y z hR1 hR2
      obtain ⟨hR1Sat, _⟩ := hR1
      obtain ⟨hR2Sat, _⟩ := hR2
      refine ⟨Sat.rchain_apply hR1Sat hR2Sat hax, ?_⟩
      intro T E _ hE
      exact (hO _ hE).elim
  | range _ _ => exact hax_s.elim
  | reflexive R =>
      intro x
      refine ⟨Sat.reflexive_apply hax, ?_⟩
      intro T E _ hE
      exact (hO _ hE).elim
  | hasKey _ _ => exact hax_s.elim

/-- **Sorry-free completeness** on the strict (range-free) fragment.
    Used as the kernel of Path-B (BBL 2008 §3.3) reduction in
    `RangeNorm.lean`. -/
theorem complete_via_canon_strict (O : Ontology) (C D : Concept)
    (hO : OntologyStrict O)
    (hC_nf : NominalFree C) (hD_nf : NominalFree D)
    (h : Entails O C D) : Sat O C D := by
  classical
  by_cases hCbot : Sat O C .bot
  · exact Sat.bot_elim hCbot
  · let x : CanonDom O := ⟨C, hCbot⟩
    have hcanon := canon_satisfies_strict O x hO
    have hxC : (canon O x).eval C x := by
      rw [canon_eval _ _ _ hC_nf]; exact Sat.refl _
    have hxD : (canon O x).eval D x := h _ hcanon x hxC
    rw [canon_eval _ _ _ hD_nf] at hxD
    exact hxD

-- ============================================================
-- 7. Completeness — ELK 2014 §3.3 (Theorem 1)
-- ============================================================

/-- **Completeness of the ELK calculus** for OWL 2 EL on the
    nominal-free and HasKey-free fragment.

    If `O ⊨ C ⊑ D` and the ontology and the query satisfy
    `OntologyNominalFree` and `NominalFree` (i.e., contain no
    `Concept.nom`, no `Concept.self`, and no `Axiom.hasKey`), then
    `Sat O C D`.

    Coverage relative to OWL 2 EL (modulo datatypes):

      * `gci`, `rinc`, `rchain`                — fully closed (ELK 2014).
      * `range R E` (when E is nominal-free)   — closed via the
              BBL 2008 §3.3 effective-subsumer dynamic baked into
              `canon`'s `ext_role` and the `range_witness` helper.
      * `reflexive R`                          — closed via
              `Sat.reflexive_apply` + `Sat.reflexive_self` and
              `Sat.self_range`.

    Closure invariant: closed via the `RangeChainSafe O` precondition,
    which gates the rchain case of `canon_satisfies` (the only remaining
    issue with the canonical-model construction in the presence of range
    axioms).  Ontologies that don't combine `rchain` with `range`
    axioms in the chain-target's rinc-hierarchy automatically satisfy
    `RangeChainSafe`. -/
theorem complete_via_canon (O : Ontology) (C D : Concept)
    (hO : OntologyNominalFree O) (hO_safe : RangeChainSafe O)
    (hC_nf : NominalFree C) (hD_nf : NominalFree D)
    (h : Entails O C D) : Sat O C D := by
  classical
  by_cases hCbot : Sat O C .bot
  · exact Sat.bot_elim hCbot
  · let x : CanonDom O := ⟨C, hCbot⟩
    have hcanon := canon_satisfies O x hO hO_safe
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
    (hO_safe : RangeChainSafe O)
    (A B : Nat) (h : Entails O (.atom A) (.atom B)) :
    Sat O (.atom A) (.atom B) :=
  complete_via_canon O _ _ hO hO_safe trivial trivial h

/-- The biconditional ELK characterisation for atom-atom subsumption
    in EL_⊥^+, on nominal-free ontologies. -/
theorem correct_atomSub (O : Ontology) (hO : OntologyNominalFree O)
    (hO_safe : RangeChainSafe O) (A B : Nat) :
    Sat O (.atom A) (.atom B) ↔ Entails O (.atom A) (.atom B) :=
  ⟨sound_atomSub O A B, complete_atomSub O hO hO_safe A B⟩

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
