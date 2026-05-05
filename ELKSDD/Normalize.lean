/-
  ELKSDD/Normalize.lean
  ---------------------
  Normalization of EL_⊥^+ ontologies into the four normal-form
  shapes of Baader–Brandt–Lutz 2005 "Pushing the EL Envelope"
  (Definition 1, Figure 1).  Each general axiom is rewritten,
  using fresh concept names, to a list of axioms each of which
  has one of:

      NF1:  C₁ ⊑ D                         (basic ⊑ basic)
      NF2:  C₁ ⊓ C₂ ⊑ D                    (binary conj ⊑ basic)
      NF3:  C₁ ⊑ ∃r.C₂                     (basic ⊑ existential)
      NF4:  ∃r.C₁ ⊑ D                      (existential ⊑ basic)

  where each `C_i` ∈ BC := {atomic concept name} ∪ {⊤} ∪ {⊥}, and
  D ∈ BC ∪ {⊥}.  (Nominals omitted in our EL_⊥^+ fragment.)

  The principal result, Lemma 2 of BBL 2005 §3.1, is *conservative
  extension*:  every model of the normalized ontology is a model
  of the original (forward), and every model of the original
  extends to a model of the normalized ontology by appropriate
  interpretation of the fresh concept names (backward).  The
  consequence is

      T ⊨ C ⊑ D   ↔   normalize(T) ⊨ C ⊑ D       (*)

  for `C`, `D` over the *original* signature.

  -------------------------------------------------------------
  Status of this layer (Layer 2 of the full-algorithm proof):
  -------------------------------------------------------------

  This module establishes the framework:

    1. `BasicConcept`  predicate identifying BC.
    2. `IsNormalGCI`   predicate characterising the 4 NFs.
    3. `IsNormal`      every axiom in O is normal.

  And proves conservative extension for the simplest rewrite,
  NF7 (split conjunctive RHS):  B ⊑ C ⊓ D  ↦  {B ⊑ C, B ⊑ D}.
  This rewrite needs *no* fresh names — both directions of the
  conservative-extension theorem are essentially structural.
  Subsequent layers will extend to NF2, NF3, NF5, NF6 (which
  introduce fresh atoms), and to NF1 (which introduces a fresh
  role).

  References:
    [BBL 2005]   Baader, F., Brandt, S., Lutz, C.
                 Pushing the EL Envelope.  IJCAI 2005 / LTCS-Report
                 05-01.  Definition 1 (normal form), Figure 1
                 (rewrite rules NF1-NF7), Lemma 2 (conservative
                 extension).

  Lean dependencies declared:
    * Concept syntax from `ELKSDD.EL`.
    * Axiom/Sat machinery from `ELKSDD.ELpp` (Layer 1).
    * No Mathlib.  No prior-work axioms admitted.  Classical
      reasoning yields `Classical.choice` only.
-/

import ELKSDD.ELpp

namespace ELKSDD
namespace Normalize

open ELpp

-- ============================================================
-- 1. Basic-concept predicate
-- ============================================================

/-- BC := {atomic concept name} ∪ {⊤} ∪ {⊥} (no nominals in
    EL_⊥^+).  These are the concepts allowed on either side of
    a normal-form GCI. -/
inductive BasicConcept : Concept → Prop where
  | atom : ∀ n, BasicConcept (.atom n)
  | top  : BasicConcept .top
  | bot  : BasicConcept .bot

/-- Decidability of `BasicConcept`.  Useful for case-splits in
    normalization. -/
instance (C : Concept) : Decidable (BasicConcept C) := by
  cases C with
  | atom n => exact isTrue (BasicConcept.atom n)
  | nom _ => exact isFalse (by intro h; cases h)
  | top    => exact isTrue BasicConcept.top
  | bot    => exact isTrue BasicConcept.bot
  | conj _ _ => exact isFalse (by intro h; cases h)
  | exist _ _ => exact isFalse (by intro h; cases h)

-- ============================================================
-- 2. Normal-form GCI predicate (BBL 2005, Definition 1)
-- ============================================================

/-- `IsNormalGCI C D` iff `C ⊑ D` is in one of the four BBL
    normal forms:

      NF1: BasicConcept C    ∧ BasicConcept D
      NF2: ∃ C₁ C₂, C = C₁ ⊓ C₂ ∧ BasicConcept C₁ ∧ BasicConcept C₂
                                  ∧ BasicConcept D
      NF3: ∃ R E, BasicConcept C ∧ D = .exist R E ∧ BasicConcept E
      NF4: ∃ R E, C = .exist R E ∧ BasicConcept E ∧ BasicConcept D

    BBL also allows `D = ⊥` on the RHS of NF1 / NF2 / NF4; that's
    already covered by `BasicConcept .bot` here. -/
inductive IsNormalGCI : Concept → Concept → Prop where
  | nf1 : ∀ {C D}, BasicConcept C → BasicConcept D → IsNormalGCI C D
  | nf2 : ∀ {C₁ C₂ D}, BasicConcept C₁ → BasicConcept C₂ → BasicConcept D →
            IsNormalGCI (.conj C₁ C₂) D
  | nf3 : ∀ {C R E}, BasicConcept C → BasicConcept E →
            IsNormalGCI C (.exist R E)
  | nf4 : ∀ {R E D}, BasicConcept E → BasicConcept D →
            IsNormalGCI (.exist R E) D

/-- Whole-axiom normal-form predicate.  GCIs must be `IsNormalGCI`;
    role inclusion `r ⊑ s` and binary role chain `r₁ ∘ r₂ ⊑ s`
    are *already* in normal form by construction of `Axiom`. -/
def IsNormalAxiom : Axiom → Prop
  | .gci C D => IsNormalGCI C D
  | .rinc _ _ => True
  | .rchain _ _ _ => True

/-- An ontology is *normal* iff every one of its axioms is
    in normal form. -/
def IsNormal (O : Ontology) : Prop := ∀ ax ∈ O, IsNormalAxiom ax

-- ============================================================
-- 3. NF7 rewrite — split conjunctive RHS — no fresh names
-- ============================================================
-- BBL 2005 Figure 1, NF7:    B ⊑ C ⊓ D   ⟶   {B ⊑ C, B ⊑ D}.
-- This is the simplest of the seven rules: the rewrite uses no
-- fresh names, and conservative extension is structural.

/-- The NF7 rewrite, applied to a single axiom: replace
    `gci C₀ (D₁ ⊓ D₂)` by the two atomic GCIs `C₀ ⊑ D₁` and
    `C₀ ⊑ D₂`.  Other axiom shapes are left unchanged. -/
def applyNF7One : Axiom → List Axiom
  | .gci C₀ (.conj D₁ D₂) => [.gci C₀ D₁, .gci C₀ D₂]
  | ax => [ax]

/-- The NF7 rewrite extended to an ontology — flat-map the
    per-axiom rewrite. -/
def applyNF7 (O : Ontology) : Ontology :=
  O.flatMap applyNF7One

-- ============================================================
-- 4. NF7 conservative extension — semantic equivalence
-- ============================================================

/-- Forward direction (easy):  every interpretation that
    satisfies `applyNF7 O` also satisfies `O`.

    Proof: case-analysis on each axiom in O.

      * `gci C₀ (D₁ ⊓ D₂)` becomes `[gci C₀ D₁, gci C₀ D₂]`.
        `I` satisfies the latter pair iff for every `x ∈ C₀^I`
        we have `x ∈ D₁^I` AND `x ∈ D₂^I`, which is exactly
        `x ∈ (D₁ ⊓ D₂)^I` by the conjunction-eval rule.
      * Other axiom shapes appear unchanged in `applyNF7 O`. -/
theorem applyNF7_satisfies_orig {α : Type} (I : Interp α) (O : Ontology)
    (hN : I.satisfies (applyNF7 O)) : I.satisfies O := by
  intro ax hax
  -- We prove `I.satisfiesAxiom ax` by showing that every clause
  -- of `applyNF7One ax` is satisfied by I (via hN), and re-assembling.
  have hN' : ∀ ax' ∈ applyNF7One ax, I.satisfiesAxiom ax' := by
    intro ax' hax'
    apply hN
    exact List.mem_flatMap.mpr ⟨ax, hax, hax'⟩
  cases ax with
  | gci C₀ D =>
      cases D with
      | conj D₁ D₂ =>
          -- `applyNF7One (gci C₀ (D₁ ⊓ D₂)) = [gci C₀ D₁, gci C₀ D₂]`
          have h1 : I.satisfiesAxiom (.gci C₀ D₁) :=
            hN' _ (List.mem_cons.mpr (Or.inl rfl))
          have h2 : I.satisfiesAxiom (.gci C₀ D₂) :=
            hN' _ (List.mem_cons.mpr (Or.inr List.mem_cons_self))
          intro x hx
          -- Goal: I.eval (D₁ ⊓ D₂) x; by conjunction-eval, ⟨h1 x hx, h2 x hx⟩.
          exact ⟨h1 x hx, h2 x hx⟩
      | atom n =>
          exact hN' _ (by simp [applyNF7One])
      | nom i =>
          exact hN' _ (by simp [applyNF7One])
      | top =>
          exact hN' _ (by simp [applyNF7One])
      | bot =>
          exact hN' _ (by simp [applyNF7One])
      | exist R E =>
          exact hN' _ (by simp [applyNF7One])
  | rinc R S =>
      exact hN' _ (by simp [applyNF7One])
  | rchain R₁ R₂ S =>
      exact hN' _ (by simp [applyNF7One])

/-- Backward direction (also easy for NF7): every interpretation
    that satisfies `O` also satisfies `applyNF7 O`.

    Proof: each axiom in `applyNF7 O` originated from an axiom
    in `O`.  For the conj-RHS case, the projection is sound:
    if `x ∈ C₀^I → x ∈ (D₁ ⊓ D₂)^I` then `x ∈ C₀^I → x ∈ D₁^I`
    and similarly for `D₂`. -/
theorem orig_satisfies_applyNF7 {α : Type} (I : Interp α) (O : Ontology)
    (hO : I.satisfies O) : I.satisfies (applyNF7 O) := by
  intro ax' hax'
  -- ax' came from `applyNF7One ax` for some ax ∈ O.
  obtain ⟨ax, hax_in_O, hax'_in_one⟩ := List.mem_flatMap.mp hax'
  cases ax with
  | gci C₀ D =>
      cases D with
      | conj D₁ D₂ =>
          have hOax : I.satisfiesAxiom (.gci C₀ (.conj D₁ D₂)) := hO _ hax_in_O
          -- applyNF7One = [gci C₀ D₁, gci C₀ D₂]; hax'_in_one selects one of them.
          rcases List.mem_cons.mp hax'_in_one with rfl | h2
          · -- ax' = gci C₀ D₁
            intro x hx
            exact (hOax x hx).1
          · rcases List.mem_cons.mp h2 with rfl | hN
            · -- ax' = gci C₀ D₂
              intro x hx
              exact (hOax x hx).2
            · exact (List.not_mem_nil hN).elim
      | atom n =>
          have hOax : I.satisfiesAxiom (.gci C₀ (.atom n)) := hO _ hax_in_O
          have : ax' = .gci C₀ (.atom n) := by
            simp [applyNF7One] at hax'_in_one
            exact hax'_in_one
          rw [this]; exact hOax
      | nom i =>
          have hOax : I.satisfiesAxiom (.gci C₀ (.nom i)) := hO _ hax_in_O
          have : ax' = .gci C₀ (.nom i) := by
            simp [applyNF7One] at hax'_in_one
            exact hax'_in_one
          rw [this]; exact hOax
      | top =>
          have hOax : I.satisfiesAxiom (.gci C₀ .top) := hO _ hax_in_O
          have : ax' = .gci C₀ .top := by
            simp [applyNF7One] at hax'_in_one
            exact hax'_in_one
          rw [this]; exact hOax
      | bot =>
          have hOax : I.satisfiesAxiom (.gci C₀ .bot) := hO _ hax_in_O
          have : ax' = .gci C₀ .bot := by
            simp [applyNF7One] at hax'_in_one
            exact hax'_in_one
          rw [this]; exact hOax
      | exist R E =>
          have hOax : I.satisfiesAxiom (.gci C₀ (.exist R E)) := hO _ hax_in_O
          have : ax' = .gci C₀ (.exist R E) := by
            simp [applyNF7One] at hax'_in_one
            exact hax'_in_one
          rw [this]; exact hOax
  | rinc R S =>
      have hOax : I.satisfiesAxiom (.rinc R S) := hO _ hax_in_O
      have : ax' = .rinc R S := by
        simp [applyNF7One] at hax'_in_one
        exact hax'_in_one
      rw [this]; exact hOax
  | rchain R₁ R₂ S =>
      have hOax : I.satisfiesAxiom (.rchain R₁ R₂ S) := hO _ hax_in_O
      have : ax' = .rchain R₁ R₂ S := by
        simp [applyNF7One] at hax'_in_one
        exact hax'_in_one
      rw [this]; exact hOax

/-- **NF7 conservative extension.**  An interpretation `I`
    satisfies `O` iff it satisfies `applyNF7 O`.  The NF7 case is
    *strict* equivalence (no fresh names involved), unlike NF2/3/5/6
    which only give a one-direction extension via fresh-name witness. -/
theorem applyNF7_conservative {α : Type} (I : Interp α) (O : Ontology) :
    I.satisfies O ↔ I.satisfies (applyNF7 O) :=
  ⟨orig_satisfies_applyNF7 I O, applyNF7_satisfies_orig I O⟩

/-- Hence: `O ⊨ C ⊑ D ↔ applyNF7 O ⊨ C ⊑ D`.  No fresh names; the
    signature of `O` and `applyNF7 O` is identical, so this is the
    full conservative-extension statement (*) for the NF7 case. -/
theorem applyNF7_entails_iff (O : Ontology) (C D : Concept) :
    Entails O C D ↔ Entails (applyNF7 O) C D := by
  constructor
  · intro h α I hN x hx
    exact h I ((applyNF7_conservative I O).mpr hN) x hx
  · intro h α I hO x hx
    exact h I ((applyNF7_conservative I O).mp hO) x hx

-- ============================================================
-- 5. NF4 rewrite — drop the tautology ⊥ ⊑ D — no fresh names
-- ============================================================
-- BBL 2005 Figure 1, NF4:    ⊥ ⊑ D   ⟶   ∅.
-- The dropped axiom is *semantically* a tautology because
-- ⊥^I = ∅ for every interpretation I, so ∀x ∈ ⊥^I, x ∈ D^I
-- holds vacuously.  Conservative extension is therefore
-- trivial in both directions and uses no fresh names.

/-- Filter out axioms of the form `gci ⊥ D`. -/
def applyNF4 (O : Ontology) : Ontology :=
  O.filter (fun ax => match ax with
                       | .gci .bot _ => false
                       | _ => true)

/-- Trivial: a `gci ⊥ D` axiom is satisfied by every
    interpretation, because `⊥^I = ∅`. -/
theorem gci_bot_trivially_satisfied {α : Type} (I : Interp α) (D : Concept) :
    I.satisfiesAxiom (.gci .bot D) := by
  intro x hx
  exact hx.elim

/-- Forward direction: every model of `applyNF4 O` is a model of `O`. -/
theorem applyNF4_satisfies_orig {α : Type} (I : Interp α) (O : Ontology)
    (hN : I.satisfies (applyNF4 O)) : I.satisfies O := by
  intro ax hax
  -- Either ax was kept by the filter (then satisfied by hN), or
  -- ax was dropped (then ax = .gci .bot _ and is trivially satisfied).
  cases ax with
  | gci C D =>
      cases C with
      | bot => exact gci_bot_trivially_satisfied I D
      | atom n =>
          apply hN
          unfold applyNF4
          simp only [List.mem_filter]
          exact ⟨hax, by decide⟩
      | nom i =>
          apply hN
          unfold applyNF4
          simp only [List.mem_filter]
          exact ⟨hax, by decide⟩
      | top =>
          apply hN
          unfold applyNF4
          simp only [List.mem_filter]
          exact ⟨hax, by decide⟩
      | conj A B =>
          apply hN
          unfold applyNF4
          simp only [List.mem_filter]
          exact ⟨hax, by decide⟩
      | exist R E =>
          apply hN
          unfold applyNF4
          simp only [List.mem_filter]
          exact ⟨hax, by decide⟩
  | rinc R S =>
      apply hN
      unfold applyNF4
      simp only [List.mem_filter]
      exact ⟨hax, by decide⟩
  | rchain R₁ R₂ S =>
      apply hN
      unfold applyNF4
      simp only [List.mem_filter]
      exact ⟨hax, by decide⟩

/-- Backward direction: every model of `O` is a model of
    `applyNF4 O` (trivial: `applyNF4 O ⊆ O`). -/
theorem orig_satisfies_applyNF4 {α : Type} (I : Interp α) (O : Ontology)
    (hO : I.satisfies O) : I.satisfies (applyNF4 O) := by
  intro ax hax
  apply hO
  unfold applyNF4 at hax
  exact (List.mem_filter.mp hax).1

/-- **NF4 conservative extension.** -/
theorem applyNF4_conservative {α : Type} (I : Interp α) (O : Ontology) :
    I.satisfies O ↔ I.satisfies (applyNF4 O) :=
  ⟨orig_satisfies_applyNF4 I O, applyNF4_satisfies_orig I O⟩

theorem applyNF4_entails_iff (O : Ontology) (C D : Concept) :
    Entails O C D ↔ Entails (applyNF4 O) C D := by
  constructor
  · intro h α I hN x hx
    exact h I ((applyNF4_conservative I O).mpr hN) x hx
  · intro h α I hO x hx
    exact h I ((applyNF4_conservative I O).mp hO) x hx

-- ============================================================
-- 6. Atom-set computation (signature of a concept / axiom / ontology)
-- ============================================================
-- Used to identify "fresh" atoms for the BBL 2005 normalization
-- rules NF2, NF3, NF5, NF6 (which introduce a fresh concept name)
-- and NF1 (which introduces a fresh role name).

/-- Concept atoms: the set of atomic-concept names appearing in C.
    Nominals contribute no concept atoms (their identity is tracked
    by `conceptIndividuals`, which is in the *individual* signature
    rather than the concept-atom signature). -/
def conceptAtoms : Concept → List Nat
  | .atom n     => [n]
  | .nom _      => []
  | .top        => []
  | .bot        => []
  | .conj A B   => conceptAtoms A ++ conceptAtoms B
  | .exist _ E  => conceptAtoms E

/-- Concept individuals: the set of individual names appearing in C
    (only nominals contribute). -/
def conceptIndividuals : Concept → List Nat
  | .atom _     => []
  | .nom i      => [i]
  | .top        => []
  | .bot        => []
  | .conj A B   => conceptIndividuals A ++ conceptIndividuals B
  | .exist _ E  => conceptIndividuals E

/-- Axiom individuals (nominals appearing in the axiom). -/
def axiomIndividuals : Axiom → List Nat
  | .gci C D       => conceptIndividuals C ++ conceptIndividuals D
  | .rinc _ _      => []
  | .rchain _ _ _  => []

/-- Ontology individuals. -/
def ontologyIndividuals (O : Ontology) : List Nat :=
  O.flatMap axiomIndividuals

/-- Axiom atoms: atomic-concept names appearing in the axiom. -/
def axiomAtoms : Axiom → List Nat
  | .gci C D       => conceptAtoms C ++ conceptAtoms D
  | .rinc _ _      => []
  | .rchain _ _ _  => []

/-- Ontology atoms: union (with multiplicity) of all axiom atom sets. -/
def ontologyAtoms (O : Ontology) : List Nat :=
  O.flatMap axiomAtoms

/-- Concept roles: the role names appearing in C. -/
def conceptRoles : Concept → List Role
  | .atom _     => []
  | .nom _      => []
  | .top        => []
  | .bot        => []
  | .conj A B   => conceptRoles A ++ conceptRoles B
  | .exist R E  => R :: conceptRoles E

/-- Axiom roles: role names appearing in the axiom. -/
def axiomRoles : Axiom → List Role
  | .gci C D       => conceptRoles C ++ conceptRoles D
  | .rinc R S      => [R, S]
  | .rchain R S T  => [R, S, T]

/-- Ontology roles. -/
def ontologyRoles (O : Ontology) : List Role :=
  O.flatMap axiomRoles

/-- A "concept-fresh" atom for `O`: a `Nat` not in `ontologyAtoms O`.
    Concrete witness: `1 + max (ontologyAtoms O ++ extra)`. -/
def freshAtomFor (O : Ontology) (extra : List Nat := []) : Nat :=
  ((ontologyAtoms O ++ extra).foldr max 0) + 1

/-- The freshAtom is indeed not in the input list. -/
private theorem foldr_max_lt_succ (l : List Nat) :
    l.foldr max 0 < l.foldr max 0 + 1 := Nat.lt_succ_self _

private theorem mem_foldr_max_le (l : List Nat) (n : Nat) (h : n ∈ l) :
    n ≤ l.foldr max 0 := by
  induction l with
  | nil => exact (List.not_mem_nil h).elim
  | cons a t ih =>
      simp only [List.foldr]
      rcases List.mem_cons.mp h with rfl | ht
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih ht) (Nat.le_max_right _ _)

theorem freshAtomFor_fresh (O : Ontology) (extra : List Nat := []) :
    freshAtomFor O extra ∉ ontologyAtoms O ++ extra := by
  intro hmem
  have hle := mem_foldr_max_le _ _ hmem
  exact Nat.not_succ_le_self _ (Nat.succ_le_of_lt (Nat.lt_succ_of_le hle))

theorem freshAtomFor_not_in_ontologyAtoms (O : Ontology) :
    freshAtomFor O ∉ ontologyAtoms O := by
  intro h
  have := freshAtomFor_fresh O []
  apply this
  exact List.mem_append.mpr (Or.inl h)

-- ============================================================
-- 7. Interpretation extension by a fresh concept name
-- ============================================================

/-- Extend an interpretation by overriding one concept-name's
    extension; leave everything else unchanged.  Free function
    (not dot-notation method) because `Interp` is in namespace
    `ELKSDD.ELpp` while we're in `ELKSDD.Normalize`. -/
noncomputable def extendInterp {α : Type} (I : Interp α)
    (n : Nat) (P : α → Prop) : Interp α := by
  classical
  exact {
    ext_concept := fun m x => if m = n then P x else I.ext_concept m x
    ext_role := I.ext_role
    indiv := I.indiv
  }

/-- Eval is invariant under `extendInterp` for concepts that don't
    mention the overridden name `n`.  Proof: structural induction on
    the concept; only the `atom m` case touches `ext_concept`. -/
theorem eval_extendInterp_of_fresh {α : Type} (I : Interp α)
    (n : Nat) (P : α → Prop) (C : Concept)
    (hfresh : n ∉ conceptAtoms C) :
    ∀ x, (extendInterp I n P).eval C x ↔ I.eval C x := by
  classical
  induction C with
  | atom m =>
      intro x
      simp only [conceptAtoms, List.mem_singleton] at hfresh
      simp only [Interp.eval, extendInterp]
      have hne : ¬ (m = n) := fun h => hfresh h.symm
      rw [if_neg hne]
  | nom i =>
      intro x; exact Iff.rfl
  | top => intro x; exact Iff.rfl
  | bot => intro x; exact Iff.rfl
  | conj A B ihA ihB =>
      intro x
      simp only [conceptAtoms, List.mem_append, not_or] at hfresh
      simp only [Interp.eval]
      constructor
      · rintro ⟨ha, hb⟩
        exact ⟨(ihA hfresh.1 x).mp ha, (ihB hfresh.2 x).mp hb⟩
      · rintro ⟨ha, hb⟩
        exact ⟨(ihA hfresh.1 x).mpr ha, (ihB hfresh.2 x).mpr hb⟩
  | exist R E ihE =>
      intro x
      simp only [conceptAtoms] at hfresh
      simp only [Interp.eval, extendInterp]
      exact ⟨fun ⟨y, hRxy, hEy⟩ => ⟨y, hRxy, (ihE hfresh y).mp hEy⟩,
             fun ⟨y, hRxy, hEy⟩ => ⟨y, hRxy, (ihE hfresh y).mpr hEy⟩⟩

/-- The extended interpretation evaluates the overridden atom to
    exactly `P x`.  Used in NF5/NF6/NF2/NF3 model-extension proofs. -/
theorem extendInterp_at_self {α : Type} (I : Interp α) (n : Nat)
    (P : α → Prop) (x : α) :
    (extendInterp I n P).ext_concept n x ↔ P x := by
  classical
  simp [extendInterp]

/-- Axiom satisfaction is invariant under `extendInterp` for axioms
    that don't mention the overridden name. -/
theorem satisfiesAxiom_extendInterp_of_fresh {α : Type} (I : Interp α)
    (n : Nat) (P : α → Prop) (ax : Axiom) (hfresh : n ∉ axiomAtoms ax) :
    I.satisfiesAxiom ax ↔ (extendInterp I n P).satisfiesAxiom ax := by
  cases ax with
  | gci C D =>
      simp only [axiomAtoms, List.mem_append, not_or] at hfresh
      constructor
      · intro hsat x hxC
        rw [eval_extendInterp_of_fresh I n P C hfresh.1] at hxC
        rw [eval_extendInterp_of_fresh I n P D hfresh.2]
        exact hsat x hxC
      · intro hsat x hxC
        rw [← eval_extendInterp_of_fresh I n P C hfresh.1] at hxC
        rw [← eval_extendInterp_of_fresh I n P D hfresh.2]
        exact hsat x hxC
  | rinc R S =>
      simp only [Interp.satisfiesAxiom, extendInterp]
  | rchain R₁ R₂ S =>
      simp only [Interp.satisfiesAxiom, extendInterp]

-- ============================================================
-- 8. NF5 rewrite — Ch ⊑ Dh → {Ch ⊑ A, A ⊑ Dh} — fresh atom
-- ============================================================
-- BBL 2005 Figure 1, NF5:    Ch ⊑ Dh  ⟶  {Ch ⊑ A, A ⊑ Dh}
-- where Ch, Dh ∉ BC and A is a fresh concept name.
--
-- This rule is the canonical fresh-name normalization: it splits
-- a complex-on-both-sides GCI through a fresh atom A.  We prove
-- conservative extension under the hypothesis that A is fresh
-- for the ontology.

/-- The NF5 single-axiom rewrite, parameterised by a fresh atom `A`.
    Replaces `gci Ch Dh` with `{gci Ch (atom A), gci (atom A) Dh}`. -/
def applyNF5OneFresh (A : Nat) (Ch Dh : Concept) : List Axiom :=
  [.gci Ch (.atom A), .gci (.atom A) Dh]

/-- Forward direction (no extension needed): if I satisfies the
    rewrite output, then I satisfies the original axiom (by
    transitivity).  The new axioms together logically imply the
    original. -/
theorem applyNF5OneFresh_implies_orig {α : Type} (I : Interp α)
    (A : Nat) (Ch Dh : Concept)
    (h : ∀ ax ∈ applyNF5OneFresh A Ch Dh, I.satisfiesAxiom ax) :
    I.satisfiesAxiom (.gci Ch Dh) := by
  intro x hx
  have h1 : I.satisfiesAxiom (.gci Ch (.atom A)) :=
    h _ (List.mem_cons.mpr (Or.inl rfl))
  have h2 : I.satisfiesAxiom (.gci (.atom A) Dh) :=
    h _ (List.mem_cons.mpr (Or.inr List.mem_cons_self))
  -- I.eval Ch x → I.eval (atom A) x → I.eval Dh x
  exact h2 x (h1 x hx)

/-- Backward direction — model extension.  If I satisfies the
    original axiom `gci Ch Dh`, then the extended interpretation
    `extendInterp I A (I.eval Ch)` satisfies the rewrite output,
    *provided* A is fresh for both Ch and Dh.

    This is the canonical model-extension witness construction
    of BBL 2005 §3.1: set `A^{I'} := Ch^I`. -/
theorem orig_extends_to_applyNF5OneFresh {α : Type} (I : Interp α)
    (A : Nat) (Ch Dh : Concept)
    (hC : A ∉ conceptAtoms Ch) (hD : A ∉ conceptAtoms Dh)
    (hOrig : I.satisfiesAxiom (.gci Ch Dh)) :
    ∀ ax ∈ applyNF5OneFresh A Ch Dh,
      (extendInterp I A (I.eval Ch)).satisfiesAxiom ax := by
  classical
  intro ax hax
  rcases List.mem_cons.mp hax with rfl | h2
  · -- ax = gci Ch (atom A); show I'.eval Ch x → I'.eval (atom A) x.
    intro x hxC'
    -- I'.eval Ch x ↔ I.eval Ch x (by extend invariance, A ∉ Ch)
    have hxC : I.eval Ch x :=
      (eval_extendInterp_of_fresh I A (I.eval Ch) Ch hC x).mp hxC'
    -- I'.eval (atom A) x = I'.ext_concept A x = I.eval Ch x by definition.
    show (extendInterp I A (I.eval Ch)).ext_concept A x
    exact (extendInterp_at_self I A (I.eval Ch) x).mpr hxC
  · rcases List.mem_cons.mp h2 with rfl | hN
    · -- ax = gci (atom A) Dh; show I'.eval (atom A) x → I'.eval Dh x.
      intro x hxA'
      -- I'.ext_concept A x = I.eval Ch x by definition.
      have hxC : I.eval Ch x :=
        (extendInterp_at_self I A (I.eval Ch) x).mp hxA'
      have hxD : I.eval Dh x := hOrig x hxC
      exact (eval_extendInterp_of_fresh I A (I.eval Ch) Dh hD x).mpr hxD
    · exact (List.not_mem_nil hN).elim

-- ============================================================
-- 9. NF5 entailment-equivalence (modulo fresh-atom witness)
-- ============================================================

/-- Forward direction: `applyNF5OneFresh A Ch Dh ⊨ C ⊑ D` implies
    `gci Ch Dh ⊨ C ⊑ D` for any concepts `C, D`.  This is the
    "drop the rewrite" direction: any model of `gci Ch Dh` (alone)
    plus any extra axioms is also a model of the rewrite (by
    backward, after extension), so any consequence of the
    rewrite is a consequence of the original.  Stated for
    a single-axiom ontology to highlight the structural pattern. -/
theorem applyNF5OneFresh_consequence_via_extend {α : Type}
    (A : Nat) (Ch Dh : Concept)
    (hC : A ∉ conceptAtoms Ch) (hD : A ∉ conceptAtoms Dh)
    (C D : Concept)
    (hCfresh : A ∉ conceptAtoms C) (hDfresh : A ∉ conceptAtoms D)
    (h : ∀ (I : Interp α),
            (∀ ax ∈ applyNF5OneFresh A Ch Dh, I.satisfiesAxiom ax) →
            ∀ x, I.eval C x → I.eval D x) :
    ∀ (I : Interp α),
      I.satisfiesAxiom (.gci Ch Dh) →
      ∀ x, I.eval C x → I.eval D x := by
  intro I hOrig x hxC
  -- Extend I by setting A^I' = Ch^I.
  let I' := extendInterp I A (I.eval Ch)
  -- I' satisfies the rewrite output.
  have hI' : ∀ ax ∈ applyNF5OneFresh A Ch Dh, I'.satisfiesAxiom ax :=
    orig_extends_to_applyNF5OneFresh I A Ch Dh hC hD hOrig
  -- C and D unchanged on extension since A is fresh in them.
  have hxC' : I'.eval C x :=
    (eval_extendInterp_of_fresh I A (I.eval Ch) C hCfresh x).mpr hxC
  have hxD' : I'.eval D x := h I' hI' x hxC'
  exact (eval_extendInterp_of_fresh I A (I.eval Ch) D hDfresh x).mp hxD'

/-- Backward direction: `gci Ch Dh ⊨ C ⊑ D` implies
    `applyNF5OneFresh A Ch Dh ⊨ C ⊑ D`.

    Proof: any model of the rewrite is a model of the original
    (by `applyNF5OneFresh_implies_orig`), so its consequences
    extend. -/
theorem orig_consequence_via_applyNF5OneFresh {α : Type}
    (A : Nat) (Ch Dh : Concept) (C D : Concept)
    (h : ∀ (I : Interp α),
            I.satisfiesAxiom (.gci Ch Dh) →
            ∀ x, I.eval C x → I.eval D x) :
    ∀ (I : Interp α),
      (∀ ax ∈ applyNF5OneFresh A Ch Dh, I.satisfiesAxiom ax) →
      ∀ x, I.eval C x → I.eval D x := by
  intro I hRewrite x hxC
  exact h I (applyNF5OneFresh_implies_orig I A Ch Dh hRewrite) x hxC

-- ============================================================
-- 10. NF6 rewrite — B ⊑ ∃r.Ch → {B ⊑ ∃r.A, A ⊑ Ch} — fresh atom
-- ============================================================
-- BBL 2005 Figure 1, NF6:    B ⊑ ∃r.Ch  ⟶  {B ⊑ ∃r.A, A ⊑ Ch}
-- where Ch ∉ BC and A is a fresh concept name.

/-- The NF6 single-axiom rewrite. -/
def applyNF6OneFresh (A : Nat) (B : Concept) (R : Role) (Ch : Concept) : List Axiom :=
  [.gci B (.exist R (.atom A)), .gci (.atom A) Ch]

/-- Forward (logical implication of original from rewrite). -/
theorem applyNF6OneFresh_implies_orig {α : Type} (I : Interp α)
    (A : Nat) (B : Concept) (R : Role) (Ch : Concept)
    (h : ∀ ax ∈ applyNF6OneFresh A B R Ch, I.satisfiesAxiom ax) :
    I.satisfiesAxiom (.gci B (.exist R Ch)) := by
  intro x hxB
  have h1 : I.satisfiesAxiom (.gci B (.exist R (.atom A))) :=
    h _ (List.mem_cons.mpr (Or.inl rfl))
  have h2 : I.satisfiesAxiom (.gci (.atom A) Ch) :=
    h _ (List.mem_cons.mpr (Or.inr List.mem_cons_self))
  -- I.eval B x → ∃ y, I.ext_role R x y ∧ I.eval (atom A) y → I.eval Ch y.
  obtain ⟨y, hRxy, hAy⟩ := h1 x hxB
  exact ⟨y, hRxy, h2 y hAy⟩

/-- Backward (model extension): set A^{I'} := Ch^I. -/
theorem orig_extends_to_applyNF6OneFresh {α : Type} (I : Interp α)
    (A : Nat) (B : Concept) (R : Role) (Ch : Concept)
    (hB : A ∉ conceptAtoms B) (hCh : A ∉ conceptAtoms Ch)
    (hOrig : I.satisfiesAxiom (.gci B (.exist R Ch))) :
    ∀ ax ∈ applyNF6OneFresh A B R Ch,
      (extendInterp I A (I.eval Ch)).satisfiesAxiom ax := by
  classical
  intro ax hax
  rcases List.mem_cons.mp hax with rfl | h2
  · -- ax = gci B (∃R.A); show I'.eval B x → ∃ y, I'.ext_role R x y ∧ I'.eval (atom A) y.
    intro x hxB'
    have hxB : I.eval B x :=
      (eval_extendInterp_of_fresh I A (I.eval Ch) B hB x).mp hxB'
    obtain ⟨y, hRxy, hCy⟩ := hOrig x hxB
    refine ⟨y, hRxy, ?_⟩
    show (extendInterp I A (I.eval Ch)).ext_concept A y
    exact (extendInterp_at_self I A (I.eval Ch) y).mpr hCy
  · rcases List.mem_cons.mp h2 with rfl | hN
    · -- ax = gci (atom A) Ch
      intro x hxA'
      have hxC : I.eval Ch x :=
        (extendInterp_at_self I A (I.eval Ch) x).mp hxA'
      exact (eval_extendInterp_of_fresh I A (I.eval Ch) Ch hCh x).mpr hxC
    · exact (List.not_mem_nil hN).elim

-- ============================================================
-- 11. NF2 rewrite — C ⊓ Ch ⊑ E → {Ch ⊑ A, C ⊓ A ⊑ E} — fresh atom
-- ============================================================
-- BBL 2005 Figure 1, NF2: C ⊓ Ch ⊑ E ⟶ {Ch ⊑ A, C ⊓ A ⊑ E}
-- where Ch ∉ BC, A is a fresh concept name.

/-- The NF2 single-axiom rewrite. -/
def applyNF2OneFresh (A : Nat) (C Ch E : Concept) : List Axiom :=
  [.gci Ch (.atom A), .gci (.conj C (.atom A)) E]

/-- Forward (logical implication of original from rewrite). -/
theorem applyNF2OneFresh_implies_orig {α : Type} (I : Interp α)
    (A : Nat) (C Ch E : Concept)
    (h : ∀ ax ∈ applyNF2OneFresh A C Ch E, I.satisfiesAxiom ax) :
    I.satisfiesAxiom (.gci (.conj C Ch) E) := by
  intro x ⟨hxC, hxCh⟩
  have h1 : I.satisfiesAxiom (.gci Ch (.atom A)) :=
    h _ (List.mem_cons.mpr (Or.inl rfl))
  have h2 : I.satisfiesAxiom (.gci (.conj C (.atom A)) E) :=
    h _ (List.mem_cons.mpr (Or.inr List.mem_cons_self))
  -- I.eval Ch x → I.eval (atom A) x by h1.
  have hxA : I.eval (.atom A) x := h1 x hxCh
  -- I.eval (C ⊓ atom A) x → I.eval E x by h2.
  exact h2 x ⟨hxC, hxA⟩

/-- Backward (model extension): set A^{I'} := Ch^I. -/
theorem orig_extends_to_applyNF2OneFresh {α : Type} (I : Interp α)
    (A : Nat) (C Ch E : Concept)
    (hC : A ∉ conceptAtoms C) (hCh : A ∉ conceptAtoms Ch)
    (hE : A ∉ conceptAtoms E)
    (hOrig : I.satisfiesAxiom (.gci (.conj C Ch) E)) :
    ∀ ax ∈ applyNF2OneFresh A C Ch E,
      (extendInterp I A (I.eval Ch)).satisfiesAxiom ax := by
  classical
  intro ax hax
  rcases List.mem_cons.mp hax with rfl | h2
  · -- gci Ch (atom A): identical structure to NF5 first axiom.
    intro x hxC'
    have hxC : I.eval Ch x :=
      (eval_extendInterp_of_fresh I A (I.eval Ch) Ch hCh x).mp hxC'
    show (extendInterp I A (I.eval Ch)).ext_concept A x
    exact (extendInterp_at_self I A (I.eval Ch) x).mpr hxC
  · rcases List.mem_cons.mp h2 with rfl | hN
    · -- gci (C ⊓ atom A) E: x in (C ⊓ A)^I' implies x in C^I' and x in A^I'.
      intro x ⟨hxC', hxA'⟩
      -- A^I' x = I.eval Ch x
      have hxCh : I.eval Ch x :=
        (extendInterp_at_self I A (I.eval Ch) x).mp hxA'
      -- C unchanged under extension since A ∉ C.
      have hxCo : I.eval C x :=
        (eval_extendInterp_of_fresh I A (I.eval Ch) C hC x).mp hxC'
      have hxE : I.eval E x := hOrig x ⟨hxCo, hxCh⟩
      exact (eval_extendInterp_of_fresh I A (I.eval Ch) E hE x).mpr hxE
    · exact (List.not_mem_nil hN).elim

-- ============================================================
-- 12. NF3 rewrite — ∃r.Ch ⊑ D → {Ch ⊑ A, ∃r.A ⊑ D} — fresh atom
-- ============================================================
-- BBL 2005 Figure 1, NF3: ∃r.Ch ⊑ D ⟶ {Ch ⊑ A, ∃r.A ⊑ D}.

/-- The NF3 single-axiom rewrite. -/
def applyNF3OneFresh (A : Nat) (R : Role) (Ch D : Concept) : List Axiom :=
  [.gci Ch (.atom A), .gci (.exist R (.atom A)) D]

/-- Forward (logical implication of original from rewrite). -/
theorem applyNF3OneFresh_implies_orig {α : Type} (I : Interp α)
    (A : Nat) (R : Role) (Ch D : Concept)
    (h : ∀ ax ∈ applyNF3OneFresh A R Ch D, I.satisfiesAxiom ax) :
    I.satisfiesAxiom (.gci (.exist R Ch) D) := by
  intro x ⟨y, hRxy, hyCh⟩
  have h1 : I.satisfiesAxiom (.gci Ch (.atom A)) :=
    h _ (List.mem_cons.mpr (Or.inl rfl))
  have h2 : I.satisfiesAxiom (.gci (.exist R (.atom A)) D) :=
    h _ (List.mem_cons.mpr (Or.inr List.mem_cons_self))
  -- I.eval (∃R.A) x via the witness y: I.ext_role R x y ∧ I.eval (atom A) y.
  have hyA : I.eval (.atom A) y := h1 y hyCh
  exact h2 x ⟨y, hRxy, hyA⟩

/-- Backward (model extension): set A^{I'} := Ch^I. -/
theorem orig_extends_to_applyNF3OneFresh {α : Type} (I : Interp α)
    (A : Nat) (R : Role) (Ch D : Concept)
    (hCh : A ∉ conceptAtoms Ch) (hD : A ∉ conceptAtoms D)
    (hOrig : I.satisfiesAxiom (.gci (.exist R Ch) D)) :
    ∀ ax ∈ applyNF3OneFresh A R Ch D,
      (extendInterp I A (I.eval Ch)).satisfiesAxiom ax := by
  classical
  intro ax hax
  rcases List.mem_cons.mp hax with rfl | h2
  · -- gci Ch (atom A): identical to NF5/NF2 first axiom.
    intro x hxC'
    have hxC : I.eval Ch x :=
      (eval_extendInterp_of_fresh I A (I.eval Ch) Ch hCh x).mp hxC'
    show (extendInterp I A (I.eval Ch)).ext_concept A x
    exact (extendInterp_at_self I A (I.eval Ch) x).mpr hxC
  · rcases List.mem_cons.mp h2 with rfl | hN
    · -- gci (∃R.A) D: x ∈ (∃R.A)^I' = ∃y, R^I' x y ∧ A^I' y.
      intro x hxEx
      obtain ⟨y, hRxy, hyA'⟩ := hxEx
      have hyCh : I.eval Ch y :=
        (extendInterp_at_self I A (I.eval Ch) y).mp hyA'
      -- The role-extension is unchanged by extendInterp.
      have hRxy' : I.ext_role R x y := hRxy
      have hxOrig : I.eval (.exist R Ch) x := ⟨y, hRxy', hyCh⟩
      have hxD : I.eval D x := hOrig x hxOrig
      exact (eval_extendInterp_of_fresh I A (I.eval Ch) D hD x).mpr hxD
    · exact (List.not_mem_nil hN).elim

-- ============================================================
-- 13. NF1 rewrite — r₁∘r₂∘r₃...∘rₖ ⊑ s → {chain via fresh role}
-- ============================================================
-- BBL 2005 Figure 1, NF1:    r₁∘···∘rₖ ⊑ s
--    ⟶   {r₁∘···∘rₖ₋₁ ⊑ u, u∘rₖ ⊑ s}     (k ≥ 3, u fresh role)
--
-- In our `Axiom` type, role chains are already binary
-- (`rchain R₁ R₂ S` = R₁ ∘ R₂ ⊑ S).  Hence chains of length k ≥ 3
-- are NOT representable in our `Axiom` type — they would need to
-- be encoded via auxiliary axioms in the input.  As a consequence,
-- NF1 is *vacuously* satisfied for our `Axiom` representation: every
-- role-chain axiom is already in normal form.
--
-- For longer chains in the *paper-level* algorithm, the user would
-- pre-process the input by introducing auxiliary roles, but at the
-- Lean level our `Axiom` type already enforces the binary-chain
-- normal form syntactically.  No proof obligation here.

/-- Sanity: every `rchain` axiom in our representation is binary,
    hence already in NF1 normal form. -/
theorem rchain_already_in_nf1 (R S T : Role) :
    IsNormalAxiom (.rchain R S T) := by
  trivial

-- ============================================================
-- 14. Structural sanity lemmas about applyNF7
-- ============================================================

/-- After one `applyNF7One` step on `gci C₀ (D₁ ⊓ D₂)`, the two
    replacement axioms have a non-conjunction RHS at the *outer*
    level when `D₁`, `D₂` are not themselves conjunctions.
    Stated as a structural fact about the rewrite. -/
theorem applyNF7One_unfolds_outer_conj (C₀ D₁ D₂ : Concept) :
    applyNF7One (.gci C₀ (.conj D₁ D₂)) =
      [.gci C₀ D₁, .gci C₀ D₂] := rfl

/-- Idempotence on already-non-conj axioms: `applyNF7One ax = [ax]`
    when ax is not a `gci _ (conj _ _)`. -/
theorem applyNF7One_id_of_nonconj_gci (C₀ D : Concept)
    (h : ∀ D₁ D₂, D ≠ .conj D₁ D₂) :
    applyNF7One (.gci C₀ D) = [.gci C₀ D] := by
  cases D with
  | atom n => rfl
  | nom i => rfl
  | top => rfl
  | bot => rfl
  | exist R E => rfl
  | conj D₁ D₂ => exact (h D₁ D₂ rfl).elim

theorem applyNF7One_id_rinc (R S : Role) :
    applyNF7One (.rinc R S) = [.rinc R S] := rfl

theorem applyNF7One_id_rchain (R₁ R₂ S : Role) :
    applyNF7One (.rchain R₁ R₂ S) = [.rchain R₁ R₂ S] := rfl

end Normalize
end ELKSDD
