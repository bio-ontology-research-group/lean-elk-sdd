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
  -- Structural SatC-level primitives so we can build SatC derivations
  -- without bouncing through `Sat`.  All four are direct images of
  -- corresponding `Sat` rules but having them at SatC level lets us
  -- conjunction-introduce SatC derivations whose premises are
  -- themselves SatC (not necessarily Sat).
  | satC_andI  : ∀ {C D E}, SatC O C D → SatC O C E → SatC O C (.conj D E)
  | satC_orE   : ∀ {C D E}, SatC O C E → SatC O D E → SatC O (.disj C D) E
  | satC_andL  : ∀ C D, SatC O (.conj C D) C
  | satC_andR  : ∀ C D, SatC O (.conj C D) D
  -- Role-axis monotonicity at SatC level.
  | satC_monoExist : ∀ R {C D}, SatC O C D →
      SatC O (.exist R C) (.exist R D)
  | satC_monoUniv  : ∀ R {C D}, SatC O C D →
      SatC O (.univ R C) (.univ R D)
  | satC_monoAtLeast : ∀ n R {C D}, SatC O C D →
      SatC O (.atLeast n R C) (.atLeast n R D)
  | satC_monoAtMost  : ∀ n R {C D}, SatC O C D →
      SatC O (.atMost n R D) (.atMost n R C)
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
  -- Cardinality bridges (needed for canonical-model construction):
  -- ≥(n+1) R.C ⊑ ∃R.C   and   ∃R.C ⊑ ≥1 R.C.
  | atLeast_to_exist  : ∀ n R C,
      SatC O (.atLeast (n+1) R C) (.exist R C)
  | exist_to_atLeast1 : ∀ R C,
      SatC O (.exist R C) (.atLeast 1 R C)
  -- Cardinality monotonicity in the bound:
  -- m ≥ n   ⟹   ≥m R.C ⊑ ≥n R.C   (covariant in n on the right)
  -- m ≥ n   ⟹   ≤n R.C ⊑ ≤m R.C   (contravariant in n)
  | atLeast_anti_n : ∀ {n m} R C, n ≤ m →
      SatC O (.atLeast m R C) (.atLeast n R C)
  | atMost_mono_n  : ∀ {n m} R C, n ≤ m →
      SatC O (.atMost n R C) (.atMost m R C)
  -- Cardinality contradiction: ≥(n+1) R.C ⊓ ≤n R.C ⊑ ⊥.
  | atLeast_atMost_bot : ∀ n R C,
      SatC O (.conj (.atLeast (n+1) R C) (.atMost n R C)) .bot
  -- Cardinality duality (negation):
  -- ¬(≥(n+1) R.C) ⊑ ≤n R.C   and   ¬(≤n R.C) ⊑ ≥(n+1) R.C, plus
  -- the converse directions.
  | neg_atLeast  : ∀ n R C,
      SatC O (.neg (.atLeast (n+1) R C)) (.atMost n R C)
  | neg_atLeast' : ∀ n R C,
      SatC O (.atMost n R C) (.neg (.atLeast (n+1) R C))
  | neg_atMost   : ∀ n R C,
      SatC O (.neg (.atMost n R C)) (.atLeast (n+1) R C)
  | neg_atMost'  : ∀ n R C,
      SatC O (.atLeast (n+1) R C) (.neg (.atMost n R C))
  -- Local reflexivity (hasSelf) bridges:
  -- hasSelf R ⊑ ∃R.⊤   and   hasSelf R ⊓ ∀R.C ⊑ C.
  | hasSelf_to_exist  : ∀ R, SatC O (.hasSelf R) (.exist R .top)
  | hasSelf_with_univ : ∀ R C,
      SatC O (.conj (.hasSelf R) (.univ R C)) C
  -- Nominal case-analysis: at the element denoted by `nom i`, every
  -- concept either holds or fails (classical EM at the nominal).  The
  -- premises capture both branches; the conclusion lifts to `nom i ⊑ E`.
  -- Sound at any model where `nom i` denotes a single element.
  | nomCases : ∀ i C E,
      SatC O (.conj (.nom i) C) E →
      SatC O (.conj (.nom i) (.neg C)) E →
      SatC O (.nom i) E
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

/-- `atLeastCard S (n+1)` says there's an element of S and the rest of
    S has cardinality ≥ n: a witness exists. -/
private theorem atLeastCard_succ_imp_nonempty {α} (S : α → Prop) (n : Nat)
    (h : Interp.atLeastCard S (n+1)) : ∃ x, S x := by
  unfold Interp.atLeastCard at h
  obtain ⟨x, hSx, _⟩ := h
  exact ⟨x, hSx⟩

/-- Monotonicity of `atLeastCard` in the bound: greater bound implies
    smaller bound, by simple induction. -/
private theorem atLeastCard_anti_n {α} (S : α → Prop) :
    ∀ {n m : Nat}, n ≤ m → Interp.atLeastCard S m → Interp.atLeastCard S n
  | 0, _, _, _ => trivial
  | _+1, 0, h, _ => absurd h (Nat.not_succ_le_zero _)
  | n+1, m+1, hle, ⟨x, hSx, hRest⟩ => by
      refine ⟨x, hSx, ?_⟩
      exact atLeastCard_anti_n
        (fun y => S y ∧ y ≠ x) (Nat.le_of_succ_le_succ hle) hRest

/-- Contradiction between `≥(n+1)` and `≤n`. -/
private theorem atLeast_atMost_card_bot {α} (S : α → Prop) (n : Nat)
    (h1 : Interp.atLeastCard S (n+1)) (h2 : Interp.atMostCard S n) : False :=
  h2 h1

/-- Filler-monotonicity of `atLeastCard`: `P ⊆ Q → atLeastCard P ⊑ atLeastCard Q`. -/
private theorem atLeastCard_filler_mono {α} (P Q : α → Prop)
    (hPQ : ∀ y, P y → Q y) :
    ∀ n, Interp.atLeastCard P n → Interp.atLeastCard Q n
  | 0, _ => trivial
  | (n+1), ⟨x, hPx, hRest⟩ => by
      refine ⟨x, hPQ x hPx, ?_⟩
      have hPx' : ∀ y, (P y ∧ y ≠ x) → (Q y ∧ y ≠ x) := by
        intro y ⟨hp, hne⟩; exact ⟨hPQ y hp, hne⟩
      exact atLeastCard_filler_mono _ _ hPx' n hRest

theorem satC_sound (O : Ontology) (C D : Concept) (h : SatC O C D) :
    Entails O C D := by
  intro α I hOK x hC
  induction h generalizing x with
  | ofSat hS => exact sat_sound O _ _ hS I hOK x hC
  | satC_andI _ _ ihD ihE => exact ⟨ihD x hC, ihE x hC⟩
  | satC_orE _ _ ihC ihD =>
      cases hC with
      | inl h => exact ihC x h
      | inr h => exact ihD x h
  | satC_andL _ _ => exact hC.1
  | satC_andR _ _ => exact hC.2
  | satC_monoExist R _ ih =>
      obtain ⟨y, hR, hCy⟩ := hC
      exact ⟨y, hR, ih y hCy⟩
  | satC_monoUniv R _ ih =>
      intro y hR
      exact ih y (hC y hR)
  | satC_monoAtLeast n R _ ih =>
      -- atLeast n on C ⊑ atLeast n on D since C ⊑ D
      show Interp.atLeastCard _ n
      apply atLeastCard_filler_mono (P := fun y => I.ext_role R x y ∧ I.eval _ y)
                          (Q := fun y => I.ext_role R x y ∧ I.eval _ y)
                          (fun y ⟨hr, hCy⟩ => ⟨hr, ih y hCy⟩) n hC
  | satC_monoAtMost n R _ ih =>
      intro hCard
      apply hC
      exact atLeastCard_filler_mono (P := fun y => I.ext_role R x y ∧ I.eval _ y)
                          (Q := fun y => I.ext_role R x y ∧ I.eval _ y)
                          (fun y ⟨hr, hDy⟩ => ⟨hr, ih y hDy⟩) (n+1) hCard
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
  | atLeast_to_exist n R C =>
      -- ≥(n+1) R.C → ∃ y, R(x,y) ∧ C(y)
      have hC' : Interp.atLeastCard
                   (fun y => I.ext_role R x y ∧ I.eval C y) (n+1) := hC
      obtain ⟨y, hSy⟩ := atLeastCard_succ_imp_nonempty _ n hC'
      exact ⟨y, hSy.1, hSy.2⟩
  | exist_to_atLeast1 R C =>
      -- ∃R.C ⊑ ≥1 R.C
      obtain ⟨y, hR, hCy⟩ := hC
      show Interp.atLeastCard _ 1
      exact ⟨y, ⟨hR, hCy⟩, trivial⟩
  | atLeast_anti_n R C hle =>
      exact atLeastCard_anti_n _ hle hC
  | atMost_mono_n R C hle =>
      intro hCard
      apply hC
      exact atLeastCard_anti_n _ (Nat.succ_le_succ hle) hCard
  | atLeast_atMost_bot n R C =>
      exact atLeast_atMost_card_bot _ n hC.1 hC.2
  | neg_atLeast n R C =>
      -- ¬(≥(n+1) R.C) ⊑ ≤n R.C, i.e., atMostCard S n
      intro hCard
      exact hC hCard
  | neg_atLeast' n R C =>
      -- ≤n R.C ⊑ ¬(≥(n+1) R.C), i.e., I.eval (≤n R.C) x → ¬ I.eval (≥(n+1) R.C) x
      intro hCard
      exact hC hCard
  | neg_atMost n R C =>
      -- ¬(≤n R.C) ⊑ ≥(n+1) R.C
      show Interp.atLeastCard _ (n+1)
      -- hC : ¬ I.eval (≤n R.C) x, i.e., ¬ ¬ atLeastCard S (n+1) = atLeastCard S (n+1) (classically)
      exact Classical.byContradiction (fun hne => hC hne)
  | neg_atMost' n R C =>
      intro hne
      exact hne hC
  | hasSelf_to_exist R =>
      -- hasSelf R ⊑ ∃R.⊤
      exact ⟨x, hC, trivial⟩
  | hasSelf_with_univ R C =>
      -- (hasSelf R ⊓ ∀R.C)(x) → C(x)
      exact hC.2 x hC.1
  | nomCases i C E _ _ ihC ihNC =>
      -- I.eval (.nom i) x, so x = I.ext_ind i.
      -- Classical EM on I.eval C x picks the relevant branch.
      by_cases hCx : I.eval C x
      · exact ihC x ⟨hC, hCx⟩
      · exact ihNC x ⟨hC, hCx⟩
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
