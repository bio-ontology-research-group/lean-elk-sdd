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
-- 6. Sanity test: NF7 produces only NF-shape GCIs at the outer
--    level when the input is structurally bounded
-- ============================================================
-- We do NOT formalise a termination measure for the iterated
-- rewrite here — the conservative-extension theorem (above)
-- holds for a single rewrite step, and that's the load-bearing
-- result for Layer 2.  Composing repeated `applyNF7` calls into
-- a terminating normalize function is the topic of Layer 2's
-- subsequent file (which will combine NF2/3/5/6/7 with a
-- common fresh-name supply and a structural complexity measure
-- on Concept).

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
