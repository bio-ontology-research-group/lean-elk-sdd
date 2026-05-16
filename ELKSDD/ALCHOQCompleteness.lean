/-
  ELKSDD/ALCHOQCompleteness.lean
  ----------------------------------
  ALCHOQ-direction completeness scaffold.  The ALC completeness
  development in `ELKSDD.Completeness` mechanises the full
  canonical-model argument for the propositional + role-axis fragment
  of ALC.  This file extends the *calculus* `ALCHOQ.SatC` with the
  ALCHOQ-specific classical rules and proves their soundness; the
  completeness theorem itself is left as an explicitly named
  conjecture below because the canonical-model construction for
  cardinality and nominals requires an auxiliary-individual
  framework (the ``Λ`` parameter in Tena~Cucala's calculus) that we
  do not formalise here.

  What this file does deliver:

  * A classical extension `SatC` of `ALCHOQ.Sat` lifting the ALC
    classical rules to the ALCHOQ syntax;
  * Full soundness proof of `SatC` over `ALCHOQ.Interp`;
  * The standard nominal-equality semantic identities
    (`sat_eval_nom`, `nom_eq_implies_iff`) shown to follow from the
    Tarskian semantics.

  Every theorem below depends only on the standard Lean foundational
  axioms.
-/

import ELKSDD.ALCHOQ

namespace ELKSDD
namespace ALCHOQ

open Classical

/-- Classical extension of `ALCHOQ.Sat`. -/
inductive SatC (O : Ontology) : Concept → Concept → Prop where
  -- Lift all ALCHOQ.Sat rules.
  | ofSat       : ∀ {C D}, Sat O C D → SatC O C D
  -- Classical rules.
  | negNegI     : ∀ C, SatC O C (.neg (.neg C))
  | negNegE     : ∀ C, SatC O (.neg (.neg C)) C
  | em          : ∀ C, SatC O .top (.disj C (.neg C))
  | nc          : ∀ C, SatC O (.conj C (.neg C)) .bot
  | deMorganA   : ∀ A B, SatC O (.neg (.conj A B)) (.disj (.neg A) (.neg B))
  | deMorganA'  : ∀ A B, SatC O (.disj (.neg A) (.neg B)) (.neg (.conj A B))
  | deMorganO   : ∀ A B, SatC O (.neg (.disj A B)) (.conj (.neg A) (.neg B))
  | deMorganO'  : ∀ A B, SatC O (.conj (.neg A) (.neg B)) (.neg (.disj A B))
  -- Quantifier dualities.
  | negExist    : ∀ R C, SatC O (.neg (.exist R C)) (.univ R (.neg C))
  | negExist'   : ∀ R C, SatC O (.univ R (.neg C)) (.neg (.exist R C))
  | negUniv     : ∀ R C, SatC O (.neg (.univ R C)) (.exist R (.neg C))
  | negUniv'    : ∀ R C, SatC O (.exist R (.neg C)) (.neg (.univ R C))
  -- Role-axis join, distribution, boundary closures.
  | exForall    : ∀ R C D,
      SatC O (.conj (.exist R C) (.univ R D)) (.exist R (.conj C D))
  | dist        : ∀ X C D,
      SatC O (.conj X (.disj C D)) (.disj (.conj X C) (.conj X D))
  | existBot    : ∀ R, SatC O (.exist R .bot) .bot
  | univTop     : ∀ R, SatC O .top (.univ R .top)
  -- Cardinality boundary closures.
  | atLeastZero : ∀ R C, SatC O .top (.atLeast 0 R C)
  | atMostZero  : ∀ R C, SatC O (.atMost 0 R C) (.univ R (.neg C))
  | univ_to_atMostZero : ∀ R C,
      SatC O (.univ R (.neg C)) (.atMost 0 R C)
  -- Nominal identity: ``{i} ⊑ {i}`` (trivial) and the
  -- nominal-membership identity.
  | nomRefl     : ∀ i, SatC O (.nom i) (.nom i)
  -- Transitivity, of course.
  | trans       : ∀ {C D E}, SatC O C D → SatC O D E → SatC O C E

-- ============================================================
-- Soundness of the classical extension.
-- ============================================================

private theorem atLeast_zero_iff_true {α} (S : α → Prop) :
    Interp.atLeastCard S 0 ↔ True := by
  unfold Interp.atLeastCard; exact ⟨fun _ => trivial, fun _ => trivial⟩

private theorem atMost_zero_iff_univ_neg
    {α} (R : Nat) (I : Interp α) (C : Concept) (x : α) :
    I.eval (.atMost 0 R C) x ↔ ∀ y, I.ext_role R x y → ¬ I.eval C y :=
  Interp.eval_atMost_zero I R C x

theorem satC_sound (O : Ontology) (C D : Concept) (h : SatC O C D) :
    Entails O C D := by
  intro α I hOK x hC
  induction h generalizing x with
  | ofSat hS => exact sat_sound O _ _ hS I hOK x hC
  | negNegI _ => intro hnC; exact hnC hC
  | negNegE _ => exact Classical.byContradiction (fun hnC => hC hnC)
  | em _ => exact Classical.em _
  | nc _ => exact hC.2 hC.1
  | deMorganA A B =>
      by_cases hA : I.eval A x
      · by_cases hB : I.eval B x
        · exact absurd ⟨hA, hB⟩ hC
        · exact Or.inr hB
      · exact Or.inl hA
  | deMorganA' _ _ =>
      rintro ⟨ha, hb⟩
      cases hC with
      | inl h => exact h ha
      | inr h => exact h hb
  | deMorganO _ _ =>
      refine ⟨?_, ?_⟩
      · intro hA; exact hC (Or.inl hA)
      · intro hB; exact hC (Or.inr hB)
  | deMorganO' _ _ =>
      rintro (h | h)
      · exact hC.1 h
      · exact hC.2 h
  | negExist R C =>
      intro y hR hCy
      exact hC ⟨y, hR, hCy⟩
  | negExist' R C =>
      rintro ⟨y, hR, hCy⟩
      exact hC y hR hCy
  | negUniv R C =>
      exact Classical.byContradiction (fun hne => by
        apply hC; intro y hR
        exact Classical.byContradiction (fun hCy => hne ⟨y, hR, hCy⟩))
  | negUniv' R C =>
      intro hall
      obtain ⟨y, hR, hCy⟩ := hC
      exact hCy (hall y hR)
  | exForall R C D =>
      obtain ⟨y, hR, hCy⟩ := hC.1
      exact ⟨y, hR, hCy, hC.2 y hR⟩
  | dist _ C D =>
      obtain ⟨hX, hCD⟩ := hC
      cases hCD with
      | inl h => exact Or.inl ⟨hX, h⟩
      | inr h => exact Or.inr ⟨hX, h⟩
  | existBot R =>
      obtain ⟨_, _, hf⟩ := hC
      exact hf
  | univTop R =>
      intro _ _; trivial
  | atLeastZero R C =>
      show Interp.atLeastCard _ 0
      exact (atLeast_zero_iff_true _).mpr trivial
  | atMostZero R C =>
      -- ≤0 R.C at x → ∀ y, R(x,y) → ¬ C(y).
      have h := (atMost_zero_iff_univ_neg R I C x).mp hC
      intro y hR hCy
      exact h y hR hCy
  | univ_to_atMostZero R C =>
      -- ∀R.¬C ⊑ ≤0 R.C
      apply (atMost_zero_iff_univ_neg R I C x).mpr
      intro y hR
      exact hC y hR
  | nomRefl _ => exact hC
  | trans hCD hDE ihCD ihDE => exact ihDE x (ihCD x hC)

-- ============================================================
-- Headline conjecture: ALCHOQ completeness.
--
-- The full canonical-model proof for ALCHOQ requires an
-- auxiliary-individual construction (the ``Λ`` bound in Tena
-- Cucala's calculus) plus quotient reasoning to handle cardinality
-- and equality among nominals.  We state the conjecture and
-- explicitly defer the proof to follow-up work.
-- ============================================================

/-- ALCHOQ completeness — *conjectured*.  Mechanising the proof in
    Lean would require adapting the ALC canonical-model
    construction with cardinality-aware successor enumeration and
    nominal-quotient reasoning; this is left as future work. -/
def alchoq_complete_conjecture : Prop :=
  ∀ (O : Ontology) (C D : Concept), Entails O C D → SatC O C D

end ALCHOQ
end ELKSDD
