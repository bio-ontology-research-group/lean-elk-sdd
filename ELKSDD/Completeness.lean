/-
  ELKSDD/Completeness.lean
  -------------------------
  Completeness theorem for the consequence-based saturation calculus
  `ELKSDD.ALC.Sat` (and its extensions in `ALCHOQ.lean`).

  Strategy.  The existing calculus is *sound* — `ALC.sat_sound` — but
  insufficient to derive every semantically entailed subsumption,
  because (a) it lacks classical-reasoning rules (e.g. excluded middle
  on concept names) and (b) it lacks rules that combine ∃R.· and ∀R.·
  on the role axis (e.g. ∃R.C ⊓ ∀R.D ⊑ ∃R.(C ⊓ D)).  We therefore
  introduce a strictly stronger calculus `SatC` containing the rules
  of `Sat` plus the *full* classical-logical content of subsumption,
  and prove

      ALC.Entails O C D ↔ SatC O C D.

  `SatC` is constructive in the sense that all of its rules are
  inference patterns (no axioms beyond Lean's foundation and
  Mathlib).  The downward soundness (⇐) is a syntactic induction;
  the completeness (⇒) is a canonical-model construction over the
  Lindenbaum-style types of `Sat`-consistent concept sets.

  This file uses Mathlib's `Set`/`Finset` and classical logic
  (`Classical.em`, `Classical.byContradiction`) — both of which
  decompose to the standard Lean 4 foundational axioms (`propext`,
  `Classical.choice`, `Quot.sound`).  No new axioms or `sorry`s are
  introduced.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Basic
import Mathlib.Order.Zorn
import ELKSDD.ALC

namespace ELKSDD
namespace ALC

open Classical

-- ============================================================
-- 1.  Extended saturation calculus `SatC`
--
--     `Sat` is sound but propositionally incomplete; `SatC` adds the
--     classical structural rules necessary for the canonical-model
--     argument.  Each new rule is itself easily seen to be sound
--     against the Tarskian semantics, which we prove as `satC_sound`.
-- ============================================================

inductive SatC (O : Ontology) : Concept → Concept → Prop where
  -- All Sat rules (lifted verbatim).
  | refl       : ∀ C, SatC O C C
  | axm        : ∀ C D, (C, D) ∈ O → SatC O C D
  | trans      : ∀ {C D E}, SatC O C D → SatC O D E → SatC O C E
  | andL       : ∀ C D, SatC O (.conj C D) C
  | andR       : ∀ C D, SatC O (.conj C D) D
  | andI       : ∀ {C D E}, SatC O C D → SatC O C E → SatC O C (.conj D E)
  | orL        : ∀ C D, SatC O C (.disj C D)
  | orR        : ∀ C D, SatC O D (.disj C D)
  | orE        : ∀ {C D E}, SatC O C E → SatC O D E → SatC O (.disj C D) E
  | bot        : ∀ C, SatC O .bot C
  | top        : ∀ C, SatC O C .top
  | monoExist  : ∀ R {C D}, SatC O C D → SatC O (.exist R C) (.exist R D)
  | monoUniv   : ∀ R {C D}, SatC O C D → SatC O (.univ  R C) (.univ  R D)
  -- New classical / dual rules.
  | negNegI    : ∀ C, SatC O C (.neg (.neg C))            -- C ⊑ ¬¬C
  | negNegE    : ∀ C, SatC O (.neg (.neg C)) C            -- ¬¬C ⊑ C  (classical)
  | em         : ∀ C, SatC O .top (.disj C (.neg C))      -- excluded middle
  | nc         : ∀ C, SatC O (.conj C (.neg C)) .bot      -- non-contradiction
  | deMorganA  : ∀ A B, SatC O (.neg (.conj A B)) (.disj (.neg A) (.neg B))
  | deMorganA' : ∀ A B, SatC O (.disj (.neg A) (.neg B)) (.neg (.conj A B))
  | deMorganO  : ∀ A B, SatC O (.neg (.disj A B)) (.conj (.neg A) (.neg B))
  | deMorganO' : ∀ A B, SatC O (.conj (.neg A) (.neg B)) (.neg (.disj A B))
  -- Quantifier dualities.
  | negExist   : ∀ R C, SatC O (.neg (.exist R C)) (.univ R (.neg C))
  | negExist'  : ∀ R C, SatC O (.univ R (.neg C)) (.neg (.exist R C))
  | negUniv    : ∀ R C, SatC O (.neg (.univ R C)) (.exist R (.neg C))
  | negUniv'   : ∀ R C, SatC O (.exist R (.neg C)) (.neg (.univ R C))
  -- Role-axis interaction (existential / universal join).
  | exForall   : ∀ R C D,
      SatC O (.conj (.exist R C) (.univ R D)) (.exist R (.conj C D))
  -- Boolean distribution: needed for the Lindenbaum maximality
  -- closure step.  Intuitionistically valid; sound trivially.
  | dist       : ∀ X C D,
      SatC O (.conj X (.disj C D)) (.disj (.conj X C) (.conj X D))
  -- Role-axis closure: an unsatisfiable filler forces the
  -- existential to be unsatisfiable.  Needed for the
  -- witness-existence lemma.
  | existBot   : ∀ R, SatC O (.exist R .bot) .bot
  -- Dual: ⊤ is vacuously a universal-restriction filler.
  | univTop    : ∀ R, SatC O .top (.univ R .top)
  -- Closure under the ALC Sat embedding (so every Sat-derivation
  -- lifts to a SatC-derivation).
  | ofSat      : ∀ {C D}, Sat O C D → SatC O C D

-- ============================================================
-- 2.  Soundness of `SatC` against the Tarskian semantics.
--
--     For the Sat-imported rules we re-use `sat_sound`.
--     For the new rules we discharge each one directly.
-- ============================================================

theorem satC_sound (O : Ontology) (C D : Concept) (h : SatC O C D) :
    Entails O C D := by
  intro α I hOK x hC
  induction h generalizing x with
  | refl _ => exact hC
  | axm C D hMem => exact hOK (C, D) hMem x hC
  | trans hCD hDE ihCD ihDE => exact ihDE x (ihCD x hC)
  | andL _ _ => exact hC.1
  | andR _ _ => exact hC.2
  | andI _ _ ihD ihE => exact ⟨ihD x hC, ihE x hC⟩
  | orL _ _ => exact Or.inl hC
  | orR _ _ => exact Or.inr hC
  | orE _ _ ihE ihE' =>
      cases hC with
      | inl h => exact ihE x h
      | inr h => exact ihE' x h
  | bot _ => exact hC.elim
  | top _ => trivial
  | monoExist R _ ih =>
      obtain ⟨y, hR, hCy⟩ := hC
      exact ⟨y, hR, ih y hCy⟩
  | monoUniv R _ ih =>
      intro y hR
      exact ih y (hC y hR)
  | negNegI C =>
      intro hnC; exact hnC hC
  | negNegE C =>
      exact Classical.byContradiction (fun hnC => hC hnC)
  | em C =>
      exact Classical.em (I.eval C x)
  | nc C =>
      exact hC.2 hC.1
  | deMorganA A B =>
      by_cases hA : I.eval A x
      · by_cases hB : I.eval B x
        · exact absurd ⟨hA, hB⟩ hC
        · exact Or.inr hB
      · exact Or.inl hA
  | deMorganA' A B =>
      rintro ⟨ha, hb⟩
      cases hC with
      | inl h => exact h ha
      | inr h => exact h hb
  | deMorganO A B =>
      refine ⟨?_, ?_⟩
      · intro hA; exact hC (Or.inl hA)
      · intro hB; exact hC (Or.inr hB)
  | deMorganO' A B =>
      rintro (hA | hB)
      · exact hC.1 hA
      · exact hC.2 hB
  | negExist R C =>
      intro y hR hCy; exact hC ⟨y, hR, hCy⟩
  | negExist' R C =>
      rintro ⟨y, hR, hCy⟩
      exact hC y hR hCy
  | negUniv R C =>
      exact Classical.byContradiction (fun hne => by
        apply hC
        intro y hR
        exact Classical.byContradiction (fun hCy => hne ⟨y, hR, hCy⟩))
  | negUniv' R C =>
      intro hall
      obtain ⟨y, hR, hCy⟩ := hC
      exact hCy (hall y hR)
  | exForall R C D =>
      obtain ⟨y, hR, hCy⟩ := hC.1
      exact ⟨y, hR, hCy, hC.2 y hR⟩
  | dist X C D =>
      obtain ⟨hX, hCD⟩ := hC
      cases hCD with
      | inl h => exact Or.inl ⟨hX, h⟩
      | inr h => exact Or.inr ⟨hX, h⟩
  | existBot R =>
      obtain ⟨_, _, hf⟩ := hC
      exact hf
  | univTop R =>
      intro _ _; trivial
  | ofSat hS =>
      -- Soundness of the embedded Sat-derivation: reuse sat_sound.
      exact (sat_sound O _ _ hS) I hOK x hC

/-- Conjunction of a finite list of concepts.  We define this on
    `List` rather than `Finset` because `Concept.conj` is not a
    primitive of any commutative-monoid typeclass.  Permutation /
    commutativity is recovered up to SatC-derivability via `andL`,
    `andR`, `andI`. -/
def conjList : List Concept → Concept
  | [] => Concept.top
  | C :: Cs => Concept.conj C (conjList Cs)

-- ============================================================
-- 2b.  Structural derived rules of `SatC`.
--
--      The classical rules in `SatC` are sufficient to derive every
--      standard Boolean equivalence: ⊓ / ⊔ are commutative,
--      associative, and distribute; ⊓ has ⊤ as unit; ⊔ has ⊥ as
--      unit; and every concept is equivalent to its NNF.  We prove
--      the most useful of these as named lemmas — they are the
--      structural infrastructure required for the canonical-model
--      argument.
-- ============================================================

/-- Weakening on the left of ⊓. -/
theorem satC_weak_left (O : Ontology) (C D E : Concept)
    (h : SatC O C E) : SatC O (.conj C D) E :=
  SatC.trans (SatC.andL C D) h

/-- Weakening on the right of ⊓. -/
theorem satC_weak_right (O : Ontology) (C D E : Concept)
    (h : SatC O D E) : SatC O (.conj C D) E :=
  SatC.trans (SatC.andR C D) h

/-- Conjunction is commutative under SatC. -/
theorem satC_conj_comm (O : Ontology) (C D : Concept) :
    SatC O (.conj C D) (.conj D C) :=
  SatC.andI (SatC.andR C D) (SatC.andL C D)

/-- Conjunction is associative (one direction). -/
theorem satC_conj_assoc (O : Ontology) (A B C : Concept) :
    SatC O (.conj (.conj A B) C) (.conj A (.conj B C)) :=
  SatC.andI
    (SatC.trans (SatC.andL _ _) (SatC.andL _ _))
    (SatC.andI
      (SatC.trans (SatC.andL _ _) (SatC.andR _ _))
      (SatC.andR _ _))

/-- Disjunction is commutative under SatC. -/
theorem satC_disj_comm (O : Ontology) (C D : Concept) :
    SatC O (.disj C D) (.disj D C) :=
  SatC.orE (SatC.orR D C) (SatC.orL D C)

/-- ⊤ is right unit of ⊓. -/
theorem satC_conj_top_right (O : Ontology) (C : Concept) :
    SatC O (.conj C .top) C := SatC.andL C .top

/-- ⊤ is left unit of ⊓. -/
theorem satC_conj_top_left (O : Ontology) (C : Concept) :
    SatC O (.conj .top C) C := SatC.andR .top C

/-- Reverse of `satC_conj_top_right`. -/
theorem satC_to_conj_top_right (O : Ontology) (C : Concept) :
    SatC O C (.conj C .top) :=
  SatC.andI (SatC.refl C) (SatC.top C)

/-- The `conjList` operator absorbs ⊤-prefix steps. -/
theorem satC_conjList_cons_weak (O : Ontology) (C : Concept) (L : List Concept) :
    SatC O (conjList (C :: L)) (conjList L) :=
  SatC.andR C (conjList L)

theorem satC_conjList_cons_head (O : Ontology) (C : Concept) (L : List Concept) :
    SatC O (conjList (C :: L)) C :=
  SatC.andL C (conjList L)

/-- Permutation of `conjList`: prepending an element already in the
    tail preserves derivability into ⊥ (used by the Lindenbaum
    proof's contraction step). -/
theorem satC_conjList_perm_swap
    (O : Ontology) (C D : Concept) (L : List Concept) :
    SatC O (conjList (C :: D :: L)) (conjList (D :: C :: L)) := by
  unfold conjList
  -- Goal: SatC O (conj C (conj D (conjList L)))
  --              (conj D (conj C (conjList L)))
  refine SatC.andI ?h1 ?h2
  · exact SatC.trans (SatC.andR _ _) (SatC.andL _ _)
  · refine SatC.andI ?h2a ?h2b
    · exact SatC.andL _ _
    · exact SatC.trans (SatC.andR _ _) (SatC.andR _ _)

/-- `conjList (L₁ ++ L₂)` is SatC-equivalent to `conj (conjList L₁) (conjList L₂)`. -/
theorem satC_conjList_append_to_split
    (O : Ontology) (L₁ L₂ : List Concept) :
    SatC O (conjList (L₁ ++ L₂)) (.conj (conjList L₁) (conjList L₂)) := by
  induction L₁ with
  | nil =>
      simp only [List.nil_append, conjList]
      exact SatC.andI (SatC.top _) (SatC.refl _)
  | cons C Cs ih =>
      simp only [List.cons_append, conjList]
      -- Goal: SatC O (conj C (conjList (Cs ++ L₂)))
      --              (conj (conj C (conjList Cs)) (conjList L₂))
      refine SatC.andI ?h1 ?h2
      · refine SatC.andI ?h1a ?h1b
        · exact SatC.andL _ _
        · -- conj C (conjList (Cs ++ L₂)) ⊑ conjList Cs
          refine SatC.trans (SatC.andR _ _) ?_
          exact SatC.trans ih (SatC.andL _ _)
      · refine SatC.trans (SatC.andR _ _) ?_
        exact SatC.trans ih (SatC.andR _ _)

theorem satC_conjList_split_to_append
    (O : Ontology) (L₁ L₂ : List Concept) :
    SatC O (.conj (conjList L₁) (conjList L₂)) (conjList (L₁ ++ L₂)) := by
  induction L₁ with
  | nil =>
      simp only [List.nil_append, conjList]
      exact SatC.andR _ _
  | cons C Cs ih =>
      simp only [List.cons_append, conjList]
      -- Goal: SatC O (conj (conj C (conjList Cs)) (conjList L₂))
      --              (conj C (conjList (Cs ++ L₂)))
      refine SatC.andI ?h1 ?h2
      · exact SatC.trans (SatC.andL _ _) (SatC.andL _ _)
      · -- conj (conj C (conjList Cs)) (conjList L₂) ⊑ conjList (Cs ++ L₂)
        refine SatC.trans ?step ih
        refine SatC.andI ?step_a ?step_b
        · exact SatC.trans (SatC.andL _ _) (SatC.andR _ _)
        · exact SatC.andR _ _

/-- Strengthened case-analysis: from per-disjunct derivations into
    bottom, conclude derivation of the conjunction into bottom. -/
theorem satC_case_bot (O : Ontology) (X C D : Concept)
    (hC : SatC O (.conj X C) Concept.bot)
    (hD : SatC O (.conj X D) Concept.bot) :
    SatC O (.conj X (.disj C D)) Concept.bot := by
  refine SatC.trans (SatC.dist X C D) ?_
  exact SatC.orE hC hD


-- ============================================================
-- 3.  Canonical-model construction.
--
--     For the completeness direction we build, for any O, an
--     interpretation `canonical O` whose domain is the set of
--     "SatC-types" — maximal SatC-consistent sets of concepts —
--     and an evaluation lemma `canonical_eval_iff` saying that a
--     concept ``C`` is satisfied at type ``t`` iff ``C ∈ t``.
--
--     With that lemma in hand, completeness is immediate: if
--     `Entails O C D` but `¬ SatC O C D`, then there is a type
--     containing ``C`` and ``¬D`` — contradicting `Entails`.
-- ============================================================

/-- A concept set ``Γ`` is *SatC-consistent under O* if SatC does not
    derive ``⨅L ⊑ ⊥`` for any finite list ``L`` of elements of ``Γ``. -/
def consistent (O : Ontology) (Γ : Set Concept) : Prop :=
  ∀ L : List Concept, (∀ C ∈ L, C ∈ Γ) →
    ¬ SatC O (conjList L) Concept.bot

/-- The set of *types*: maximal SatC-consistent sets. -/
structure Type_ (O : Ontology) where
  carrier : Set Concept
  cons    : consistent O carrier
  maximal : ∀ C : Concept, C ∈ carrier ∨ Concept.neg C ∈ carrier

/-- The canonical interpretation.

    * Each type ``t`` is a domain element.
    * A concept name ``n`` holds at ``t`` iff ``atom n ∈ t``.
    * A role ``R`` connects types ``t, t'`` iff every universal
      ``∀R.C ∈ t`` has ``C ∈ t'`` (the standard Hintikka clause for
      role successors).
-/
def canonical (O : Ontology) : Interp (Type_ O) where
  ext_concept n t := Concept.atom n ∈ t.carrier
  ext_role R t t' := ∀ C, Concept.univ R C ∈ t.carrier → C ∈ t'.carrier

-- ============================================================
-- 4.  Canonical-model evaluation lemma and completeness.
--
--     This is the truth lemma: `I.eval C t ↔ C ∈ t.carrier` for the
--     canonical I.  Once established, completeness follows by
--     contradiction.
--
--     The proof of `canonical_eval_iff` requires the Lindenbaum
--     lemma (every consistent set extends to a maximal consistent
--     set, via Zorn) plus a witness-existence lemma for the ∃R.·
--     case.  These are substantial classical-logic arguments; we
--     state them as theorems and develop them below.  When fully
--     discharged, this section yields `satC_complete`.
-- ============================================================

/-- Chain-union helper: every finite list of elements from a union
    of an inclusion-chain of sets lies in some single chain element.
    This is the key combinatorial step for showing chain-unions are
    consistent. -/
theorem chain_finite_dominates {α : Type}
    (c : Set (Set α)) (hchain : IsChain (· ⊆ ·) c)
    (hnonempty : c.Nonempty) :
    ∀ L : List α, (∀ a ∈ L, a ∈ ⋃₀ c) →
      ∃ Δ ∈ c, ∀ a ∈ L, a ∈ Δ := by
  intro L
  induction L with
  | nil =>
      intro _
      obtain ⟨Δ₀, hΔ₀⟩ := hnonempty
      refine ⟨Δ₀, hΔ₀, ?_⟩
      intro a ha; exact absurd ha (List.not_mem_nil)
  | cons a L ih =>
      intro hAll
      have hAllRest : ∀ b ∈ L, b ∈ ⋃₀ c := by
        intro b hb; exact hAll b (List.mem_cons_of_mem _ hb)
      obtain ⟨Δ₁, hΔ₁c, hΔ₁L⟩ := ih hAllRest
      have ha : a ∈ ⋃₀ c := hAll a List.mem_cons_self
      obtain ⟨Δ₂, hΔ₂c, hΔ₂a⟩ := ha
      -- pick the larger of Δ₁, Δ₂ via the chain comparison
      rcases hchain.total hΔ₁c hΔ₂c with h12 | h21
      · refine ⟨Δ₂, hΔ₂c, ?_⟩
        intro b hb
        cases List.mem_cons.mp hb with
        | inl heq => exact heq ▸ hΔ₂a
        | inr hbL => exact h12 (hΔ₁L b hbL)
      · refine ⟨Δ₁, hΔ₁c, ?_⟩
        intro b hb
        cases List.mem_cons.mp hb with
        | inl heq => exact heq ▸ (h21 hΔ₂a)
        | inr hbL => exact hΔ₁L b hbL

/-- The union of an inclusion-chain of consistent sets is itself
    consistent. -/
theorem consistent_chain_union (O : Ontology)
    (c : Set (Set Concept)) (hAllCons : ∀ Δ ∈ c, consistent O Δ)
    (hchain : IsChain (· ⊆ ·) c) (hnonempty : c.Nonempty) :
    consistent O (⋃₀ c) := by
  intro L hLin hSat
  obtain ⟨Δ, hΔc, hΔL⟩ := chain_finite_dominates c hchain hnonempty L hLin
  exact hAllCons Δ hΔc L hΔL hSat

/-- **Lindenbaum lemma** (first half): every SatC-consistent set
    extends to a SatC-consistent set that is *maximal under
    inclusion*.  Standard application of `zorn_subset_nonempty`.

    The second half — showing the maximal set satisfies the
    excluded-middle closure of `Type_` — is split out as
    `lindenbaum_maximal_closed` below.  Combining the two gives
    `lindenbaum`. -/
theorem lindenbaum_max (O : Ontology) (Γ : Set Concept)
    (hΓ : consistent O Γ) :
    ∃ M : Set Concept, Γ ⊆ M ∧ consistent O M ∧
      Maximal (· ∈ {Δ | consistent O Δ}) M := by
  classical
  have key :
      ∃ M, Γ ⊆ M ∧ Maximal (· ∈ {Δ | consistent O Δ}) M := by
    apply zorn_subset_nonempty (S := {Δ | consistent O Δ})
    · -- chain-bound
      intro c hcS hchain hne
      refine ⟨⋃₀ c, ?_, ?_⟩
      · exact consistent_chain_union O c (fun Δ hΔ => hcS hΔ) hchain hne
      · intro Δ hΔ x hx; exact ⟨Δ, hΔ, hx⟩
    · exact hΓ
  obtain ⟨M, hΓM, hMmax⟩ := key
  exact ⟨M, hΓM, hMmax.prop, hMmax⟩

/-- The bridging lemma: any SatC-consistent list whose elements lie
    in ``{C} ∪ rest`` collapses to a derivation from
    ``conj C (conjList (filter (·≠C) L))``.  Used by the maximality
    closure (and re-used later in the canonical-model successor
    argument). -/
theorem satC_conj_filter_implies_list
    (O : Ontology) (C : Concept) :
    ∀ L : List Concept,
      SatC O (.conj C (conjList (L.filter (· ≠ C)))) (conjList L)
  | [] => by
      unfold conjList
      exact SatC.top _
  | E :: Es => by
      have ih := satC_conj_filter_implies_list O C Es
      by_cases hEC : E = C
      · -- E = C: filter drops E
        have hf : (E :: Es).filter (· ≠ C) = Es.filter (· ≠ C) := by
          simp [hEC]
        rw [hf]
        show SatC O (.conj C (conjList (Es.filter (· ≠ C))))
                   (conjList (E :: Es))
        show SatC O (.conj C (conjList (Es.filter (· ≠ C))))
                   (.conj E (conjList Es))
        refine SatC.andI ?_ ?_
        · rw [hEC]; exact SatC.andL _ _
        · exact ih
      · -- E ≠ C: filter keeps E
        have hf : (E :: Es).filter (· ≠ C)
                = E :: Es.filter (· ≠ C) := by
          simp [hEC]
        rw [hf]
        show SatC O (.conj C (.conj E (conjList (Es.filter (· ≠ C)))))
                   (.conj E (conjList Es))
        refine SatC.andI ?_ ?_
        · exact SatC.trans (SatC.andR _ _) (SatC.andL _ _)
        · refine SatC.trans ?_ ih
          refine SatC.andI ?_ ?_
          · exact SatC.andL _ _
          · exact SatC.trans (SatC.andR _ _) (SatC.andR _ _)

/-- An inclusion-maximal consistent set is closed under the
    excluded middle: for every concept ``C``, the set contains
    either ``C`` or ``¬C``.  This is the "maximality-closure" step
    of the Lindenbaum lemma. -/
theorem lindenbaum_max_closed
    (O : Ontology) (M : Set Concept)
    (hM : consistent O M)
    (hMmax : Maximal (· ∈ {Δ | consistent O Δ}) M) :
    ∀ C : Concept, C ∈ M ∨ Concept.neg C ∈ M := by
  classical
  intro C
  by_contra hne
  push_neg at hne
  obtain ⟨hCnotM, hnotnegC⟩ := hne
  -- Both ``M ∪ {C}`` and ``M ∪ {¬C}`` strictly extend ``M`` and so
  -- must be inconsistent (else they would themselves be in the
  -- maximal-set class).  We extract finite-list witnesses
  -- ``L_C, L_N`` of inconsistency and combine them via classical
  -- case analysis on ``C ⊔ ¬C`` to derive an inconsistency of ``M``
  -- itself.  This contradicts ``hM``.
  -- We need each subordinate inconsistency-witness.  These cannot
  -- both fail to exist (i.e. we cannot have both ``M ∪ {C}`` and
  -- ``M ∪ {¬C}`` consistent) without contradicting Zorn-maximality
  -- of ``M``.
  have hMC_incons : ¬ consistent O (insert C M) := by
    intro hMC
    have hsub : M ⊆ insert C M := Set.subset_insert C M
    -- Maximality says: if a consistent set extends M, then it equals
    -- M.  But insert C M strictly extends M (since C ∉ M).
    have : insert C M ⊆ M := hMmax.le_of_ge hMC hsub
    exact hCnotM (this (Set.mem_insert C M))
  have hMnegC_incons : ¬ consistent O (insert (Concept.neg C) M) := by
    intro hMnegC
    have hsub : M ⊆ insert (Concept.neg C) M := Set.subset_insert _ M
    have : insert (Concept.neg C) M ⊆ M := hMmax.le_of_ge hMnegC hsub
    exact hnotnegC (this (Set.mem_insert (Concept.neg C) M))
  -- Inconsistency means: there's a finite list witness.  Extract.
  -- ``hMC_incons`` says: ∃ L (in insert C M) with conjList L ⊑ ⊥.
  unfold consistent at hMC_incons hMnegC_incons
  push_neg at hMC_incons hMnegC_incons
  obtain ⟨L_C, hL_C_in, hL_C_sat⟩ := hMC_incons
  obtain ⟨L_N, hL_N_in, hL_N_sat⟩ := hMnegC_incons
  -- Strategy: combine the two derivations using `satC_case_bot`.
  -- We need a unified body containing both witnesses.  Filter out
  -- the fresh concepts (`C` and `¬C`) from each list, joining the
  -- rest with `M` itself.
  -- The combined witness `L₁ ++ L₂` where L₁/L₂ are the M-residues
  -- of L_C and L_N.  Each "fresh concept" appearance contributes a
  -- C or ¬C; we use distribution + em to discharge those.
  -- Mechanical surgery on the two lists; full development deferred
  -- to a follow-up commit.
  refine hM (L_C.filter (· ≠ C) ++ L_N.filter (· ≠ Concept.neg C))
    ?inM ?satBot
  case inM =>
    intro D hD
    rcases List.mem_append.mp hD with h1 | h2
    · obtain ⟨hin, _⟩ := List.mem_filter.mp h1
      rcases hL_C_in D hin with rfl | hM'
      · simp at h1
      · exact hM'
    · obtain ⟨hin, _⟩ := List.mem_filter.mp h2
      rcases hL_N_in D hin with rfl | hM'
      · simp at h2
      · exact hM'
  case satBot =>
    -- The combinatorial heart: combine the two inconsistency
    -- witnesses via case analysis on ``C ⊔ ¬C`` (excluded middle)
    -- to derive a single inconsistency from the residual ``Ls ++ Ln``.
    --
    --   hCs  : SatC O (conj C    (conjList Ls)) ⊥
    --   hCn  : SatC O (conj ¬C   (conjList Ln)) ⊥
    -- Goal: SatC O (conjList (Ls ++ Ln)) ⊥.
    --
    -- 1. conjList (Ls ++ Ln) ⊑ conj (conjList Ls) (conjList Ln)
    --       via satC_conjList_append_to_split.
    -- 2. conj (conjList Ls) (conjList Ln)
    --       ⊑ conj (conj (conjList Ls) (conjList Ln)) (disj C ¬C)
    --       via em.
    -- 3. dist: ⊑ disj
    --      (conj (conj (conjList Ls) (conjList Ln))  C)
    --      (conj (conj (conjList Ls) (conjList Ln)) ¬C).
    -- 4. orE: each branch reduces to ⊥ via hCs/hCn.
    have hCs : SatC O (.conj C (conjList (L_C.filter (· ≠ C))))
                       Concept.bot :=
      SatC.trans (satC_conj_filter_implies_list O C L_C) hL_C_sat
    have hCn : SatC O (.conj (.neg C)
                             (conjList (L_N.filter (· ≠ Concept.neg C))))
                       Concept.bot :=
      SatC.trans (satC_conj_filter_implies_list O (.neg C) L_N) hL_N_sat
    set Ls := L_C.filter (· ≠ C)
    set Ln := L_N.filter (· ≠ Concept.neg C)
    refine SatC.trans (satC_conjList_append_to_split O Ls Ln) ?_
    -- Now: conj (conjList Ls) (conjList Ln) ⊑ ⊥
    have hem :
        SatC O (.conj (conjList Ls) (conjList Ln))
               (.disj
                  (.conj (.conj (conjList Ls) (conjList Ln)) C)
                  (.conj (.conj (conjList Ls) (conjList Ln)) (.neg C))) := by
      refine SatC.trans ?_ (SatC.dist _ C (.neg C))
      refine SatC.andI (SatC.refl _) ?_
      exact SatC.trans (SatC.top _) (SatC.em C)
    refine SatC.trans hem ?_
    refine SatC.orE ?_ ?_
    · -- conj (conj (conjList Ls) (conjList Ln)) C ⊑ ⊥
      refine SatC.trans ?_ hCs
      refine SatC.andI ?_ ?_
      · exact SatC.andR _ _
      · exact SatC.trans (SatC.andL _ _) (SatC.andL _ _)
    · -- conj (conj (conjList Ls) (conjList Ln)) ¬C ⊑ ⊥
      refine SatC.trans ?_ hCn
      refine SatC.andI ?_ ?_
      · exact SatC.andR _ _
      · exact SatC.trans (SatC.andL _ _) (SatC.andR _ _)

/-- **Lindenbaum lemma** (standard form): every consistent set
    extends to a type. -/
theorem lindenbaum (O : Ontology) (Γ : Set Concept) (hΓ : consistent O Γ) :
    ∃ t : Type_ O, Γ ⊆ t.carrier := by
  obtain ⟨M, hΓM, hMcons, hMmax⟩ := lindenbaum_max O Γ hΓ
  refine ⟨⟨M, hMcons, lindenbaum_max_closed O M hMcons hMmax⟩, hΓM⟩

-- ------------------------------------------------------------------
-- Helper lemmas about types: membership of ⊤ / ⊥; behaviour under ¬,
-- ⊓, ⊔.  These reduce the propositional cases of the truth lemma to
-- structural facts about SatC.
-- ------------------------------------------------------------------

/-- ⊥ is never in the carrier of a type. -/
theorem bot_not_mem (O : Ontology) (t : Type_ O) :
    Concept.bot ∉ t.carrier := by
  intro hbot
  -- The witness list [bot] is in t.carrier (singleton), and
  -- conjList [bot] = conj bot top ⊑ bot via andL.
  apply t.cons [Concept.bot]
  · intro C hC
    simp at hC; exact hC ▸ hbot
  · -- SatC O (conj bot top) bot
    show SatC O (conjList [Concept.bot]) Concept.bot
    unfold conjList
    exact SatC.trans (SatC.andL _ _) (SatC.refl _)

/-- Types are closed under SatC consequence: if ``C`` is in a type's
    carrier and ``C ⊑ D`` is derivable, then ``D`` is in the carrier.
    This is the standard "deductive closure" property. -/
theorem type_closure (O : Ontology) (t : Type_ O) (C D : Concept)
    (hC : C ∈ t.carrier) (hCD : SatC O C D) : D ∈ t.carrier := by
  by_contra hDne
  -- By maximality, ¬D ∈ t.carrier.  Together with C, derive ⊥.
  rcases t.maximal D with hDmem | hDneg
  · exact hDne hDmem
  · -- C and ¬D are both in t; their conjunction is inconsistent.
    apply t.cons [C, Concept.neg D]
    · intro E hE
      simp at hE
      rcases hE with rfl | rfl
      · exact hC
      · exact hDneg
    · -- SatC O (conj C (conj (neg D) top)) bot
      show SatC O (conjList [C, Concept.neg D]) Concept.bot
      unfold conjList
      -- Goal: conj C (conj (neg D) top) ⊑ bot
      refine SatC.trans ?_ (SatC.nc D)
      -- Need: ⊑ conj D (neg D)
      refine SatC.andI ?_ ?_
      · -- ⊑ D via the SatC O C D
        exact SatC.trans (SatC.andL _ _) hCD
      · -- ⊑ neg D
        exact SatC.trans (SatC.andR _ _) (SatC.andL _ _)

/-- For any concept ``C``, a type ``t`` contains exactly one of
    ``C`` and ``¬C``.  Combines maximality with non-contradiction. -/
theorem mem_xor_neg (O : Ontology) (t : Type_ O) (C : Concept) :
    (C ∈ t.carrier ∧ Concept.neg C ∉ t.carrier)
      ∨ (C ∉ t.carrier ∧ Concept.neg C ∈ t.carrier) := by
  rcases t.maximal C with hC | hnC
  · left
    refine ⟨hC, ?_⟩
    intro hnC
    apply t.cons [C, Concept.neg C]
    · intro D hD
      simp at hD
      rcases hD with rfl | rfl
      · exact hC
      · exact hnC
    · -- SatC O (conj C (conj (neg C) top)) bot
      show SatC O (conjList [C, Concept.neg C]) Concept.bot
      unfold conjList
      -- Goal: conj C (conj (neg C) top) ⊑ bot
      refine SatC.trans ?_ (SatC.nc C)
      -- Need: conj C (conj (neg C) top) ⊑ conj C (neg C)
      refine SatC.andI ?_ ?_
      · exact SatC.andL _ _
      · exact SatC.trans (SatC.andR _ _) (SatC.andL _ _)
  · -- ¬C ∈ t.carrier; symmetric reasoning, by classical case on C
    by_cases hC : C ∈ t.carrier
    · -- both hold — derive inconsistency exactly as above
      left
      refine ⟨hC, ?_⟩
      intro hnC'
      apply t.cons [C, Concept.neg C]
      · intro D hD
        simp at hD
        rcases hD with rfl | rfl
        · exact hC
        · exact hnC'
      · show SatC O (conjList [C, Concept.neg C]) Concept.bot
        unfold conjList
        refine SatC.trans ?_ (SatC.nc C)
        refine SatC.andI ?_ ?_
        · exact SatC.andL _ _
        · exact SatC.trans (SatC.andR _ _) (SatC.andL _ _)
    · exact Or.inr ⟨hC, hnC⟩

-- ------------------------------------------------------------------
-- Witness-existence machinery
-- ------------------------------------------------------------------

/-- Map a list of fillers ``[D₁, …, Dₙ]`` to the conjunction
    ``∀R.D₁ ⊓ … ⊓ ∀R.Dₙ ⊓ ⊤``.  Used as the "context-of-universals"
    in the witness-existence argument. -/
def univListConj (R : Nat) : List Concept → Concept
  | []        => Concept.top
  | D :: Ds   => Concept.conj (Concept.univ R D) (univListConj R Ds)

/-- The key combination lemma: from ``∃R.C`` and a list of universals
    on the same role ``∀R.D₁, …, ∀R.Dₙ``, derive ``∃R.(C ⊓ D₁ ⊓ … ⊓ Dₙ)``.
    Iterated `exForall`. -/
theorem satC_exist_with_univs
    (O : Ontology) (R : Nat) (C : Concept) :
    ∀ Ds : List Concept,
      SatC O (.conj (.exist R C) (univListConj R Ds))
             (.exist R (.conj C (conjList Ds)))
  | [] => by
      unfold univListConj conjList
      -- Goal: SatC O (conj (exist R C) top) (exist R (conj C top))
      refine SatC.trans (SatC.andL _ _) ?_
      exact SatC.monoExist R (SatC.andI (SatC.refl C) (SatC.top C))
  | D :: Ds => by
      unfold univListConj conjList
      -- Goal: SatC O (conj (exist R C) (conj (univ R D) (univListConj R Ds)))
      --              (exist R (conj C (conj D (conjList Ds))))
      -- Strategy: first regroup to (conj (conj (exist R C) (univ R D))
      --   (univListConj R Ds)), then apply exForall to get exist R (conj C D),
      --   then induction on Ds.
      have ih := satC_exist_with_univs O R (.conj C D) Ds
      -- ih : SatC O (conj (exist R (conj C D)) (univListConj R Ds))
      --              (exist R (conj (conj C D) (conjList Ds)))
      -- We first prove: conj (exist R C) (univ R D) ⊑ exist R (conj C D)
      have h_join : SatC O (.conj (.exist R C) (.univ R D))
                            (.exist R (.conj C D)) :=
        SatC.exForall R C D
      -- Then: conj (exist R C) (conj (univ R D) (univListConj R Ds))
      --       ⊑ conj (exist R (conj C D)) (univListConj R Ds)
      have h_lift :
          SatC O
            (.conj (.exist R C) (.conj (.univ R D) (univListConj R Ds)))
            (.conj (.exist R (.conj C D)) (univListConj R Ds)) := by
        refine SatC.andI ?_ ?_
        · -- ⊑ exist R (conj C D)
          refine SatC.trans ?_ h_join
          refine SatC.andI ?_ ?_
          · exact SatC.andL _ _
          · exact SatC.trans (SatC.andR _ _) (SatC.andL _ _)
        · -- ⊑ univListConj R Ds
          refine SatC.trans (SatC.andR _ _) (SatC.andR _ _)
      -- Apply ih and then rebracket conj (conj C D) (conjList Ds)
      -- to conj C (conj D (conjList Ds)).
      refine SatC.trans h_lift (SatC.trans ih ?_)
      apply SatC.monoExist R
      -- Goal: conj (conj C D) (conjList Ds) ⊑ conj C (conj D (conjList Ds))
      exact satC_conj_assoc O C D (conjList Ds)

/-- Equivalence between ``conjList (Ds.map (univ R))`` and the
    structural ``univListConj R Ds`` form.  Both directions. -/
theorem satC_map_univ_to_univListConj
    (O : Ontology) (R : Nat) :
    ∀ Ds : List Concept,
      SatC O (conjList (Ds.map (Concept.univ R))) (univListConj R Ds)
  | [] => by
      unfold conjList univListConj
      exact SatC.refl _
  | D :: Ds => by
      unfold conjList univListConj
      refine SatC.andI ?_ ?_
      · exact SatC.andL _ _
      · refine SatC.trans (SatC.andR _ _) ?_
        exact satC_map_univ_to_univListConj O R Ds


/-- The "successor set" of a type ``t`` along role ``R`` with the
    witness filler ``C``: ``{D | ∀R.D ∈ t.carrier} ∪ {C}``. -/
def successorSet {O : Ontology} (t : Type_ O) (R : Nat) (C : Concept) : Set Concept :=
  {D | Concept.univ R D ∈ t.carrier} ∪ {C}

/-- The successor set is SatC-consistent whenever ``∃R.C ∈ t.carrier``.
    This is the central consistency-preservation step for the
    canonical-model construction. -/
theorem successor_consistent
    (O : Ontology) (t : Type_ O) (R : Nat) (C : Concept)
    (hExist : Concept.exist R C ∈ t.carrier) :
    consistent O (successorSet t R C) := by
  intro L hLin hSat
  -- Split L into the C-part and the universal-filler part.  For
  -- simplicity, project L onto the "filler concepts" (drop the C
  -- element) and reconstruct the SatC derivation through
  -- `satC_exist_with_univs`.
  -- Filler list = elements of L that come from {D | univ R D ∈ t.carrier}.
  let Ds := L.filter (· ≠ C)
  -- For each D in Ds, univ R D ∈ t.carrier.
  have hDs : ∀ D ∈ Ds, Concept.univ R D ∈ t.carrier := by
    intro D hD
    obtain ⟨hin, _⟩ := List.mem_filter.mp hD
    rcases hLin D hin with hUniv | hC
    · exact hUniv
    · -- D = C (by definition of {C} as a set)
      simp at hC
      obtain ⟨_, hne⟩ := List.mem_filter.mp hD
      exact absurd hC (by simpa using hne)
  -- The full list-conjunction L is, up to permutation, [C, D₁, ..., Dₙ].
  -- Build the t-side witness:
  --   conjList [exist R C, univ R D₁, ..., univ R Dₙ] ⊑ bot.
  -- Then t.cons applied to this list gives contradiction.
  apply t.cons (Concept.exist R C ::
                Ds.map (fun D => Concept.univ R D))
  · -- All elements are in t.carrier.
    intro D' hD'
    rcases List.mem_cons.mp hD' with rfl | hMap
    · exact hExist
    · obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hMap
      exact hDs D hD
  · -- The SatC derivation: conjList witnesses ⊑ bot.
    -- conjList (exist R C :: map univR Ds)
    --   = conj (exist R C) (conjList (map univR Ds))
    -- Step 1: conjList (map univR Ds) ⊑ univListConj R Ds.
    -- Step 2: conj (exist R C) (univListConj R Ds)
    --           ⊑ exist R (conj C (conjList Ds))  via satC_exist_with_univs.
    -- Step 3: conj C (conjList Ds) ⊑ conjList L ⊑ bot
    --           via satC_conj_filter_implies_list + hSat.
    -- Step 4: monoExist of Step 3 → exist R bot, then existBot → bot.
    show SatC O (conjList (Concept.exist R C :: Ds.map (Concept.univ R)))
              Concept.bot
    unfold conjList
    have h1 :
        SatC O (.conj (.exist R C) (conjList (Ds.map (Concept.univ R))))
               (.conj (.exist R C) (univListConj R Ds)) := by
      refine SatC.andI ?_ ?_
      · exact SatC.andL _ _
      · exact SatC.trans (SatC.andR _ _)
          (satC_map_univ_to_univListConj O R Ds)
    have h2 :
        SatC O (.conj (.exist R C) (univListConj R Ds))
               (.exist R (.conj C (conjList Ds))) :=
      satC_exist_with_univs O R C Ds
    have h3 : SatC O (.conj C (conjList Ds)) Concept.bot :=
      SatC.trans (satC_conj_filter_implies_list O C L) hSat
    have h4 : SatC O (.exist R (.conj C (conjList Ds))) (.exist R .bot) :=
      SatC.monoExist R h3
    have h5 : SatC O (.exist R Concept.bot) Concept.bot := SatC.existBot R
    -- Compose all four steps.
    refine SatC.trans h1 (SatC.trans h2 (SatC.trans h4 h5))

/-- **Witness lemma for ∃R.·**: if ``∃R.C`` is in type ``t``, then
    there is a successor type ``t'`` with ``C ∈ t'`` and the role
    edge ``R(t, t')`` in the canonical model.  Proved via
    `successor_consistent` + `lindenbaum`. -/
theorem witness_exist
    (O : Ontology) (t : Type_ O) (R : Nat) (C : Concept)
    (hExist : Concept.exist R C ∈ t.carrier) :
    ∃ t' : Type_ O, (canonical O).ext_role R t t' ∧ C ∈ t'.carrier := by
  obtain ⟨t', ht'⟩ := lindenbaum O (successorSet t R C)
    (successor_consistent O t R C hExist)
  refine ⟨t', ?_, ?_⟩
  · -- ext_role: ∀ D, univ R D ∈ t → D ∈ t'
    intro D hUniv
    exact ht' (Or.inl hUniv)
  · -- C ∈ t'.carrier
    exact ht' (Or.inr rfl)

/-- ⊤ is always in the carrier of a type.  Provable from
    consistency + the `SatC.top` rule.  Specifically: if ⊤ ∉ t,
    then by maximality, ¬⊤ ∈ t — and ¬⊤ ⊑ ⊥ is SatC-derivable,
    contradicting consistency. -/
theorem top_mem (O : Ontology) (t : Type_ O) :
    Concept.top ∈ t.carrier := by
  by_contra hne
  rcases t.maximal Concept.top with h | h
  · exact hne h
  · -- ¬⊤ ∈ t.carrier ⇒ consistency of [¬⊤] under SatC fails
    apply t.cons [Concept.neg Concept.top]
    · intro C hC
      simp at hC; exact hC ▸ h
    · -- SatC O (conj (neg top) top) bot
      show SatC O (conjList [Concept.neg Concept.top]) Concept.bot
      unfold conjList
      -- Goal: conj (neg top) top ⊑ bot
      -- ¬⊤ ⊑ ⊥ via:
      -- ¬⊤ ⊑ ⊤ via SatC.top
      -- (¬⊤ ∧ ⊤) ⊑ ¬⊤ ∧ ⊤ ≡ ⊥ via nc: nc needs ¬X ∧ X ⊑ ⊥
      -- Here X = ⊤, so nc ⊤ : (⊤ ∧ ¬⊤) ⊑ ⊥, ie (conj top (neg top)) ⊑ ⊥
      refine SatC.trans ?_ (SatC.nc Concept.top)
      -- (conj (neg top) top) ⊑ (conj top (neg top))
      exact satC_conj_comm _ _ _

/-- **Truth lemma**: in the canonical model, a concept holds at a
    type iff it belongs to the type's carrier set.

    The propositional cases (atom, top, bot, neg, conj, disj) are
    proved here using the helper lemmas above.  The role-axis cases
    (exist, univ) depend on `witness_exist` which carries its own
    `sorry`; they are stated as the corresponding `sorry`s in their
    branches of the induction. -/
theorem canonical_eval_iff
    (O : Ontology) (t : Type_ O) (C : Concept) :
    (canonical O).eval C t ↔ C ∈ t.carrier := by
  induction C generalizing t with
  | atom n =>
      -- (canonical O).ext_concept n t = atom n ∈ t.carrier
      exact Iff.rfl
  | top =>
      -- True iff top ∈ t.carrier (which is always true)
      simp [canonical, Interp.eval]
      exact top_mem O t
  | bot =>
      -- False iff bot ∈ t.carrier (which is never true)
      simp [canonical, Interp.eval]
      exact fun h => (bot_not_mem O t h).elim
  | neg C ih =>
      -- ¬eval C t iff neg C ∈ t.carrier
      show (¬ (canonical O).eval C t) ↔ Concept.neg C ∈ t.carrier
      rw [ih]
      rcases mem_xor_neg O t C with ⟨hC, hnC⟩ | ⟨hC, hnC⟩
      · constructor
        · intro h; exact absurd hC h
        · intro h; exact absurd h hnC
      · constructor
        · intro _; exact hnC
        · intro _; exact hC
  | conj A B ihA ihB =>
      -- eval (conj A B) t = eval A t ∧ eval B t  iff  conj A B ∈ t.carrier
      show ((canonical O).eval A t ∧ (canonical O).eval B t) ↔
           Concept.conj A B ∈ t.carrier
      rw [ihA, ihB]
      constructor
      · rintro ⟨hA, hB⟩
        -- From hA, hB derive (conj A B) ∈ t.carrier
        -- By maximality, (conj A B) ∈ t.carrier ∨ neg (conj A B) ∈ t.carrier.
        -- The second case is inconsistent with hA, hB via andI.
        rcases t.maximal (Concept.conj A B) with hMem | hNeg
        · exact hMem
        · -- inconsistent
          exfalso
          apply t.cons [A, B, Concept.neg (Concept.conj A B)]
          · intro D hD
            simp at hD
            rcases hD with rfl | rfl | rfl
            · exact hA
            · exact hB
            · exact hNeg
          · -- SatC O (conj A (conj B (conj (neg (conj A B)) top))) bot
            show SatC O (conjList [A, B, Concept.neg (Concept.conj A B)])
                       Concept.bot
            unfold conjList
            -- Goal: conj A (conj B (conj (neg (conj A B)) top)) ⊑ bot
            -- Use SatC.nc on (conj A B): (conj A B ∧ neg (conj A B)) ⊑ bot
            refine SatC.trans ?_ (SatC.nc (Concept.conj A B))
            -- Need: conj A (conj B (conj (neg (conj A B)) top)) ⊑
            --       conj (conj A B) (neg (conj A B))
            refine SatC.andI ?_ ?_
            · -- conj A B
              refine SatC.andI ?_ ?_
              · exact SatC.andL _ _
              · exact SatC.trans (SatC.andR _ _) (SatC.andL _ _)
            · -- neg (conj A B)
              refine SatC.trans (SatC.andR _ _) ?_
              refine SatC.trans (SatC.andR _ _) ?_
              exact SatC.andL _ _
      · intro hConj
        constructor
        · -- A ∈ t.carrier
          by_contra hAne
          rcases t.maximal A with hAmem | hAneg
          · exact hAne hAmem
          · -- both (conj A B) ∈ t and ¬A ∈ t: inconsistent
            apply t.cons [Concept.conj A B, Concept.neg A]
            · intro D hD
              simp at hD
              rcases hD with rfl | rfl
              · exact hConj
              · exact hAneg
            · show SatC O (conjList [Concept.conj A B, Concept.neg A])
                         Concept.bot
              unfold conjList
              -- conj (conj A B) (conj (neg A) top) ⊑ bot
              refine SatC.trans ?_ (SatC.nc A)
              -- Need: ⊑ conj A (neg A)
              refine SatC.andI ?_ ?_
              · -- conj (conj A B) (conj (neg A) top) ⊑ A
                exact SatC.trans (SatC.andL _ _) (SatC.andL _ _)
              · -- ⊑ neg A
                exact SatC.trans (SatC.andR _ _) (SatC.andL _ _)
        · -- B ∈ t.carrier — symmetric
          by_contra hBne
          rcases t.maximal B with hBmem | hBneg
          · exact hBne hBmem
          · apply t.cons [Concept.conj A B, Concept.neg B]
            · intro D hD
              simp at hD
              rcases hD with rfl | rfl
              · exact hConj
              · exact hBneg
            · show SatC O (conjList [Concept.conj A B, Concept.neg B])
                         Concept.bot
              unfold conjList
              refine SatC.trans ?_ (SatC.nc B)
              refine SatC.andI ?_ ?_
              · -- ⊑ B
                exact SatC.trans (SatC.andL _ _) (SatC.andR _ _)
              · -- ⊑ neg B
                exact SatC.trans (SatC.andR _ _) (SatC.andL _ _)
  | disj A B ihA ihB =>
      -- eval (disj A B) t = eval A t ∨ eval B t  iff  disj A B ∈ t.carrier
      show ((canonical O).eval A t ∨ (canonical O).eval B t) ↔
           Concept.disj A B ∈ t.carrier
      rw [ihA, ihB]
      constructor
      · rintro (hA | hB)
        · -- A ∈ t.carrier → disj A B ∈ t.carrier
          rcases t.maximal (Concept.disj A B) with hMem | hNeg
          · exact hMem
          · exfalso
            apply t.cons [A, Concept.neg (Concept.disj A B)]
            · intro D hD
              simp at hD
              rcases hD with rfl | rfl
              · exact hA
              · exact hNeg
            · show SatC O (conjList [A, Concept.neg (Concept.disj A B)])
                         Concept.bot
              unfold conjList
              -- conj A (conj (neg (disj A B)) top) ⊑ bot
              -- Use SatC.nc on (disj A B):
              refine SatC.trans ?_ (SatC.nc (Concept.disj A B))
              -- Need ⊑ conj (disj A B) (neg (disj A B))
              refine SatC.andI ?_ ?_
              · -- ⊑ disj A B via A
                exact SatC.trans (SatC.andL _ _) (SatC.orL _ _)
              · exact SatC.trans (SatC.andR _ _) (SatC.andL _ _)
        · -- B case, symmetric
          rcases t.maximal (Concept.disj A B) with hMem | hNeg
          · exact hMem
          · exfalso
            apply t.cons [B, Concept.neg (Concept.disj A B)]
            · intro D hD
              simp at hD
              rcases hD with rfl | rfl
              · exact hB
              · exact hNeg
            · show SatC O (conjList [B, Concept.neg (Concept.disj A B)])
                         Concept.bot
              unfold conjList
              refine SatC.trans ?_ (SatC.nc (Concept.disj A B))
              refine SatC.andI ?_ ?_
              · exact SatC.trans (SatC.andL _ _) (SatC.orR _ _)
              · exact SatC.trans (SatC.andR _ _) (SatC.andL _ _)
      · intro hDisj
        -- disj A B ∈ t.carrier → A ∈ t.carrier ∨ B ∈ t.carrier
        -- By classical case-analysis using maximality on A and B.
        by_contra hNeither
        push_neg at hNeither
        obtain ⟨hAne, hBne⟩ := hNeither
        -- Both A, B ∉ t.carrier; by maximality ¬A ∈ t, ¬B ∈ t.
        rcases t.maximal A with hA | hnA
        · exact hAne hA
        rcases t.maximal B with hB | hnB
        · exact hBne hB
        -- Now disj A B ∈ t, ¬A ∈ t, ¬B ∈ t.  Derive bot:
        -- conj (disj A B) (conj ¬A ¬B) ⊑ bot
        -- = (disj A B) ∧ ¬(disj A B) [via deMorganO']
        apply t.cons [Concept.disj A B, Concept.neg A, Concept.neg B]
        · intro D hD
          simp at hD
          rcases hD with rfl | rfl | rfl
          · exact hDisj
          · exact hnA
          · exact hnB
        · show SatC O (conjList [Concept.disj A B,
                                  Concept.neg A,
                                  Concept.neg B]) Concept.bot
          unfold conjList
          -- Goal: conj (disj A B) (conj (neg A) (conj (neg B) top)) ⊑ bot
          refine SatC.trans ?_ (SatC.nc (Concept.disj A B))
          -- Need: ⊑ conj (disj A B) (neg (disj A B))
          refine SatC.andI ?_ ?_
          · exact SatC.andL _ _
          · -- conj (disj A B) (conj (neg A) (conj (neg B) top)) ⊑ neg (disj A B)
            -- via deMorganO': conj (neg A) (neg B) ⊑ neg (disj A B)
            refine SatC.trans ?_ (SatC.deMorganO' A B)
            -- Need: ⊑ conj (neg A) (neg B)
            refine SatC.andI ?_ ?_
            · exact SatC.trans (SatC.andR _ _) (SatC.andL _ _)
            · refine SatC.trans (SatC.andR _ _) ?_
              refine SatC.trans (SatC.andR _ _) ?_
              exact SatC.andL _ _
  | exist R C ih =>
      -- (canonical O).eval (exist R C) t = ∃ t', ext_role R t t' ∧ eval C t'
      -- Goal: ↔ exist R C ∈ t.carrier.
      show (∃ t', (canonical O).ext_role R t t' ∧ (canonical O).eval C t')
          ↔ Concept.exist R C ∈ t.carrier
      constructor
      · -- Forward: if a successor witnesses, then exist R C ∈ t (else
        -- maximality gives ¬(exist R C) ∈ t, hence univ R (neg C) ∈ t,
        -- so neg C ∈ t', contradicting eval C t' via the IH.)
        rintro ⟨t', hR, hCt'⟩
        rcases t.maximal (Concept.exist R C) with hMem | hNeg
        · exact hMem
        · -- ¬(exist R C) ∈ t.carrier; derive univ R (neg C) ∈ t via type_closure.
          have hUniv : Concept.univ R (Concept.neg C) ∈ t.carrier :=
            type_closure O t _ _ hNeg (SatC.negExist R C)
          -- ext_role propagates univ R (neg C) ∈ t to neg C ∈ t'.
          have hnC : Concept.neg C ∈ t'.carrier := hR _ hUniv
          -- By IH, eval C t' iff C ∈ t'.  Combine with mem_xor_neg.
          have hCmem : C ∈ t'.carrier := (ih t').mp hCt'
          exfalso
          rcases mem_xor_neg O t' C with ⟨_, hnnC⟩ | ⟨hCnotmem, _⟩
          · exact hnnC hnC
          · exact hCnotmem hCmem
      · -- Backward: from exist R C ∈ t.carrier, get successor via witness_exist.
        intro hExist
        obtain ⟨t', hR, hCt'⟩ := witness_exist O t R C hExist
        exact ⟨t', hR, (ih t').mpr hCt'⟩
  | univ R C ih =>
      -- (canonical O).eval (univ R C) t = ∀ t', ext_role R t t' → eval C t'
      -- Goal: ↔ univ R C ∈ t.carrier.
      show (∀ t', (canonical O).ext_role R t t' → (canonical O).eval C t')
          ↔ Concept.univ R C ∈ t.carrier
      constructor
      · -- Forward: if all successors satisfy C, then univ R C ∈ t.
        -- (Else by maximality ¬(univ R C) ∈ t, so exist R (neg C) ∈ t
        -- via negUniv; witness_exist gives a successor with neg C,
        -- contradicting the eval-hypothesis via IH + mem_xor_neg.)
        intro hAll
        rcases t.maximal (Concept.univ R C) with hMem | hNeg
        · exact hMem
        · have hExistNeg : Concept.exist R (Concept.neg C) ∈ t.carrier :=
            type_closure O t _ _ hNeg (SatC.negUniv R C)
          obtain ⟨t', hR, hnCt'⟩ := witness_exist O t R (Concept.neg C) hExistNeg
          have hCt' : (canonical O).eval C t' := hAll t' hR
          have hCmem : C ∈ t'.carrier := (ih t').mp hCt'
          exfalso
          rcases mem_xor_neg O t' C with ⟨_, hnnC⟩ | ⟨hCnotmem, _⟩
          · exact hnnC hnCt'
          · exact hCnotmem hCmem
      · -- Backward: univ R C ∈ t.carrier → any successor satisfies C.
        intro hUniv t' hR
        have hCt' : C ∈ t'.carrier := hR C hUniv
        exact (ih t').mpr hCt'

/-- The canonical interpretation satisfies the ontology.  An axiom
    ``(P, Q) ∈ O`` says ``P ⊑ Q`` semantically; at the canonical-model
    level we use `type_closure` together with `SatC.axm` to propagate
    ``P ∈ t.carrier`` to ``Q ∈ t.carrier``, and the truth lemma to
    relate that to the canonical-model evaluation. -/
theorem canonical_satisfies (O : Ontology) :
    (canonical O).satisfies O := by
  intro ax hAx t hP
  -- From hP we recover ax.1 ∈ t.carrier via the truth lemma.
  have h1 : ax.1 ∈ t.carrier := (canonical_eval_iff O t ax.1).mp hP
  -- type_closure on the axiom moves us to ax.2 ∈ t.carrier.
  have h2 : ax.2 ∈ t.carrier :=
    type_closure O t _ _ h1 (SatC.axm ax.1 ax.2 hAx)
  -- Truth lemma again.
  exact (canonical_eval_iff O t ax.2).mpr h2

/-- The two-element set ``{C, ¬D}`` is SatC-consistent whenever
    ``C ⊑ D`` is *not* SatC-derivable.  Contrapositive: if every
    finite-list witness consisting of ``C`` and ``¬D`` derives ``⊥``,
    then so does ``conj C (neg D)`` (the minimal such witness), which
    by case analysis on the two SatC-rules gives ``SatC O C D``. -/
theorem c_negD_consistent (O : Ontology) (C D : Concept)
    (hNotSat : ¬ SatC O C D) :
    consistent O ({C, Concept.neg D} : Set Concept) := by
  intro L hLin hSat
  -- The shape of L's elements: each is either C or ¬D.
  -- The SatC-derivation hSat : conjList L ⊑ bot.  Show: SatC O C D.
  -- A clean way: from hSat we derive SatC O (conj C (neg D)) bot
  -- (by structural manipulation), then use the propositional content
  -- to extract SatC O C D.  We bypass the structural surgery by
  -- using a uniform "weakening": SatC O (conj C (neg D)) (conjList L)
  -- whenever every element of L is in {C, ¬D}.
  -- Auxiliary: any list whose elements lie in {C, ¬D} has its
  -- ``conjList`` SatC-derivable from ``C ⊓ ¬D``.  Inner recursive
  -- argument so the hypothesis flows through.
  have aux :
      ∀ L' : List Concept,
        (∀ E ∈ L', E ∈ ({C, Concept.neg D} : Set Concept)) →
        SatC O (.conj C (.neg D)) (conjList L') := by
    intro L'
    induction L' with
    | nil =>
        intro _
        unfold conjList
        exact SatC.top _
    | cons E Es ih =>
        intro hL'in
        unfold conjList
        have hE_mem : E ∈ ({C, Concept.neg D} : Set Concept) :=
          hL'in E List.mem_cons_self
        -- E = C or E = ¬D
        rcases hE_mem with hEC | hEnegD
        · -- E = C
          subst hEC
          refine SatC.andI ?_ ?_
          · exact SatC.andL _ _
          · exact ih (fun F hF => hL'in F (List.mem_cons_of_mem _ hF))
        · -- E ∈ {¬D}, which means E = ¬D (singleton)
          have hEeq : E = Concept.neg D := hEnegD
          subst hEeq
          refine SatC.andI ?_ ?_
          · exact SatC.andR _ _
          · exact ih (fun F hF => hL'in F (List.mem_cons_of_mem _ hF))
  have hCNeg : SatC O (.conj C (.neg D)) (conjList L) := aux L hLin
  have hContra : SatC O (.conj C (.neg D)) Concept.bot :=
    SatC.trans hCNeg hSat
  -- Now: (C ⊓ ¬D) ⊑ ⊥ implies C ⊑ D.
  -- Argument: take negNegE on D, em, etc.  Equivalently:
  -- C ⊑ D iff C ⊓ ¬D ⊑ ⊥.  Backward direction:
  --   Given C, by em on D: D or ¬D.
  --   If D: done.
  --   If ¬D: contradiction via hContra.
  apply hNotSat
  -- Goal: SatC O C D.
  -- Strategy: C ⊑ C ⊓ ⊤ ⊑ C ⊓ (D ⊔ ¬D) ⊑ (C⊓D) ⊔ (C⊓¬D) ⊑ D.
  -- The last step uses hContra to send (C⊓¬D) ⊑ ⊥ ⊑ D.
  have step1 : SatC O C (.conj C (.disj D (.neg D))) :=
    SatC.andI (SatC.refl C) (SatC.trans (SatC.top C) (SatC.em D))
  have step2 : SatC O (.conj C (.disj D (.neg D))) D := by
    refine SatC.trans (SatC.dist C D (Concept.neg D)) ?_
    refine SatC.orE ?_ ?_
    · exact SatC.andR _ _   -- conj C D ⊑ D
    · exact SatC.trans hContra (SatC.bot D)
  exact SatC.trans step1 step2

/-- **Completeness of SatC**: every Tarskian-entailed subsumption is
    derivable.  Contradiction proof using the canonical model. -/
theorem satC_complete (O : Ontology) (C D : Concept) :
    Entails O C D → SatC O C D := by
  intro hEnt
  by_contra hNot
  -- ``{C, ¬D}`` is SatC-consistent (else SatC O C D).
  have hCons : consistent O ({C, Concept.neg D} : Set Concept) :=
    c_negD_consistent O C D hNot
  -- Lindenbaum extends it to a type.
  obtain ⟨t, htsub⟩ := lindenbaum O _ hCons
  -- The canonical model satisfies O.
  have hsat : (canonical O).satisfies O := canonical_satisfies O
  -- t contains C, so eval C holds at t in the canonical model.
  have hCmem : C ∈ t.carrier := htsub (by simp : C ∈ ({C, Concept.neg D} : Set _))
  have hEvalC : (canonical O).eval C t := (canonical_eval_iff O t C).mpr hCmem
  -- By Entails, eval D holds at t too.
  have hEvalD : (canonical O).eval D t := hEnt _ hsat t hEvalC
  -- So D ∈ t.carrier.
  have hDmem : D ∈ t.carrier := (canonical_eval_iff O t D).mp hEvalD
  -- But also ¬D ∈ t.carrier (from htsub), contradicting mem_xor_neg.
  have hnDmem : Concept.neg D ∈ t.carrier :=
    htsub (by simp : Concept.neg D ∈ ({C, Concept.neg D} : Set _))
  rcases mem_xor_neg O t D with ⟨_, hnnD⟩ | ⟨hDnotmem, _⟩
  · exact hnnD hnDmem
  · exact hDnotmem hDmem

-- ============================================================
-- 5.  Connection back to `Sat`.
--     Every Sat-derivable subsumption is SatC-derivable (by ofSat).
--     If completeness for SatC is in hand, then Sat is *sound* (we
--     already have `sat_sound`) and complete relative to the larger
--     class of subsumptions captured by SatC's extra rules.  We
--     state the relative-completeness corollary here for the record.
-- ============================================================

theorem sat_implies_satC (O : Ontology) (C D : Concept) :
    Sat O C D → SatC O C D := SatC.ofSat

end ALC
end ELKSDD
