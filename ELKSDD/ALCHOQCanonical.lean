/-
  ELKSDD/ALCHOQCanonical.lean
  ----------------------------
  Canonical-model construction for the full ALCHOQ description logic.

  Built section by section.  At any committed state the file builds
  cleanly with no `sorry`s; in-progress sections are excluded from
  the export until they are closed.  Axiom budget: only the standard
  Lean foundational axioms.
-/

import ELKSDD.ALCHOQCompleteness
import ELKSDD.Completeness
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Zorn

namespace ELKSDD
namespace ALCHOQ

open Classical

-- ============================================================
-- 1.  Helpers and structural SatC lemmas.
-- ============================================================

/-- ALCHOQ-side `conjList`: ⋀L collapsed to nested `conj`s. -/
def conjList : List Concept → Concept
  | []      => Concept.top
  | C :: Cs => Concept.conj C (conjList Cs)

theorem satC_refl (O : Ontology) (C : Concept) : SatC O C C :=
  SatC.ofSat (Sat.refl C)

theorem satC_top (O : Ontology) (C : Concept) : SatC O C Concept.top :=
  SatC.ofSat (Sat.top C)

theorem satC_bot (O : Ontology) (C : Concept) : SatC O Concept.bot C :=
  SatC.ofSat (Sat.bot C)

theorem satC_orL (O : Ontology) (C D : Concept) :
    SatC O C (.disj C D) := SatC.ofSat (Sat.orL C D)

theorem satC_orR (O : Ontology) (C D : Concept) :
    SatC O D (.disj C D) := SatC.ofSat (Sat.orR C D)

/-- Strengthen the left side: `SatC O C E → SatC O (C ⊓ D) E`. -/
theorem satC_weak_left (O : Ontology) {C D E : Concept}
    (h : SatC O C E) : SatC O (.conj C D) E :=
  SatC.trans (SatC.satC_andL C D) h

/-- Strengthen the right side: `SatC O D E → SatC O (C ⊓ D) E`. -/
theorem satC_weak_right (O : Ontology) {C D E : Concept}
    (h : SatC O D E) : SatC O (.conj C D) E :=
  SatC.trans (SatC.satC_andR C D) h

theorem satC_conj_comm (O : Ontology) (C D : Concept) :
    SatC O (.conj C D) (.conj D C) :=
  SatC.satC_andI (SatC.satC_andR C D) (SatC.satC_andL C D)

/-- Conjunction is associative (one direction). -/
theorem satC_conj_assoc (O : Ontology) (A B C : Concept) :
    SatC O (.conj A (.conj B C)) (.conj (.conj A B) C) :=
  SatC.satC_andI
    (SatC.satC_andI (SatC.satC_andL A _)
                    (SatC.trans (SatC.satC_andR A _) (SatC.satC_andL B C)))
    (SatC.trans (SatC.satC_andR A _) (SatC.satC_andR B C))

/-- ⊤ is right-unit of ⊓ under SatC. -/
theorem satC_conj_top_right (O : Ontology) (C : Concept) :
    SatC O (.conj C .top) C := SatC.satC_andL _ _

theorem satC_to_conj_top_right (O : Ontology) (C : Concept) :
    SatC O C (.conj C .top) := SatC.satC_andI (satC_refl O C) (satC_top O C)

/-- `conjList (L₁ ++ L₂)` ⊑ `conj (conjList L₁) (conjList L₂)`. -/
theorem satC_conjList_append_to_split
    (O : Ontology) :
    ∀ L₁ L₂ : List Concept,
      SatC O (conjList (L₁ ++ L₂)) (.conj (conjList L₁) (conjList L₂))
  | [], L₂ => by
      unfold conjList
      -- Goal: conjList L₂ ⊑ conj top (conjList L₂)
      exact SatC.satC_andI (satC_top O _) (satC_refl O _)
  | C :: Cs, L₂ => by
      have ih := satC_conjList_append_to_split O Cs L₂
      show SatC O (conjList (C :: (Cs ++ L₂)))
                 (.conj (conjList (C :: Cs)) (conjList L₂))
      show SatC O (.conj C (conjList (Cs ++ L₂)))
                 (.conj (.conj C (conjList Cs)) (conjList L₂))
      refine SatC.satC_andI ?_ ?_
      · refine SatC.satC_andI ?_ ?_
        · exact SatC.satC_andL _ _
        · exact SatC.trans (SatC.satC_andR _ _)
                  (SatC.trans ih (SatC.satC_andL _ _))
      · exact SatC.trans (SatC.satC_andR _ _)
                (SatC.trans ih (SatC.satC_andR _ _))

-- ============================================================
-- 2.  Consistency and types.
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

-- ============================================================
-- 3.  Canonical interpretation skeleton.
-- ============================================================

/-- Canonical successor relation: every universal at `t` propagates,
    *and* self-loops correspond to `hasSelf` membership.  The
    self-loop clause is essential for the hasSelf-truth-lemma. -/
def canonicalRole (O : Ontology) (R : Nat) (t t' : Type_ O) : Prop :=
  (∀ C, Concept.univ R C ∈ t.carrier → C ∈ t'.carrier) ∧
  (t' = t → Concept.hasSelf R ∈ t.carrier)

-- ============================================================
-- 4.  Chain-bound + Lindenbaum machinery.
-- ============================================================

theorem chain_finite_dominates_ALCHOQ {α : Type}
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

/-- Chain-union of consistent sets is consistent. -/
theorem consistent_chain_union (O : Ontology)
    (c : Set (Set Concept)) (hAllCons : ∀ Δ ∈ c, consistent O Δ)
    (hchain : IsChain (· ⊆ ·) c) (hnonempty : c.Nonempty) :
    consistent O (⋃₀ c) := by
  intro L hLin hSat
  obtain ⟨Δ, hΔc, hΔL⟩ :=
    chain_finite_dominates_ALCHOQ c hchain hnonempty L hLin
  exact hAllCons Δ hΔc L hΔL hSat

/-- Lindenbaum part 1: every consistent set extends to a
    maximal-consistent set (Zorn). -/
theorem lindenbaum_max (O : Ontology) (Γ : Set Concept)
    (hΓ : consistent O Γ) :
    ∃ M : Set Concept, Γ ⊆ M ∧ consistent O M ∧
      Maximal (· ∈ {Δ | consistent O Δ}) M := by
  classical
  have key :
      ∃ M, Γ ⊆ M ∧ Maximal (· ∈ {Δ | consistent O Δ}) M := by
    apply zorn_subset_nonempty (S := {Δ | consistent O Δ})
    · intro c hcS hchain hne
      refine ⟨⋃₀ c, ?_, ?_⟩
      · exact consistent_chain_union O c (fun Δ hΔ => hcS hΔ) hchain hne
      · intro Δ hΔ x hx; exact ⟨Δ, hΔ, hx⟩
    · exact hΓ
  obtain ⟨M, hΓM, hMmax⟩ := key
  exact ⟨M, hΓM, hMmax.prop, hMmax⟩

/-- Bridge: SatC-derive `conjList L` from `C ⊓ conjList (L.filter (·≠C))`. -/
theorem satC_conj_filter_implies_list
    (O : Ontology) (C : Concept) :
    ∀ L : List Concept,
      SatC O (.conj C (conjList (L.filter (· ≠ C)))) (conjList L)
  | [] => by
      unfold conjList
      exact satC_top O _
  | E :: Es => by
      have ih := satC_conj_filter_implies_list O C Es
      by_cases hEC : E = C
      · have hf : (E :: Es).filter (· ≠ C) = Es.filter (· ≠ C) := by
          simp [hEC]
        rw [hf]
        show SatC O (.conj C (conjList (Es.filter (· ≠ C))))
                   (.conj E (conjList Es))
        refine SatC.satC_andI ?_ ?_
        · rw [hEC]; exact SatC.satC_andL _ _
        · exact ih
      · have hf : (E :: Es).filter (· ≠ C)
                = E :: Es.filter (· ≠ C) := by
          simp [hEC]
        rw [hf]
        show SatC O (.conj C (.conj E (conjList (Es.filter (· ≠ C)))))
                   (.conj E (conjList Es))
        refine SatC.satC_andI ?_ ?_
        · exact SatC.trans (SatC.satC_andR _ _) (SatC.satC_andL _ _)
        · refine SatC.trans ?_ ih
          refine SatC.satC_andI ?_ ?_
          · exact SatC.satC_andL _ _
          · exact SatC.trans (SatC.satC_andR _ _) (SatC.satC_andR _ _)

/-- Lindenbaum part 2: a maximal-consistent set contains either ``C``
    or ``¬C`` for every concept. -/
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
  have hMC_incons : ¬ consistent O (insert C M) := by
    intro hMC
    have hsub : M ⊆ insert C M := Set.subset_insert C M
    have : insert C M ⊆ M := hMmax.le_of_ge hMC hsub
    exact hCnotM (this (Set.mem_insert C M))
  have hMnegC_incons : ¬ consistent O (insert (Concept.neg C) M) := by
    intro hMnegC
    have hsub : M ⊆ insert (Concept.neg C) M := Set.subset_insert _ M
    have : insert (Concept.neg C) M ⊆ M := hMmax.le_of_ge hMnegC hsub
    exact hnotnegC (this (Set.mem_insert (Concept.neg C) M))
  unfold consistent at hMC_incons hMnegC_incons
  push_neg at hMC_incons hMnegC_incons
  obtain ⟨L_C, hL_C_in, hL_C_sat⟩ := hMC_incons
  obtain ⟨L_N, hL_N_in, hL_N_sat⟩ := hMnegC_incons
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
    have hem :
        SatC O (.conj (conjList Ls) (conjList Ln))
               (.disj
                  (.conj (.conj (conjList Ls) (conjList Ln)) C)
                  (.conj (.conj (conjList Ls) (conjList Ln)) (.neg C))) := by
      refine SatC.trans ?_ (SatC.dist _ C (.neg C))
      refine SatC.satC_andI (satC_refl O _) ?_
      exact SatC.trans (satC_top O _) (SatC.em C)
    refine SatC.trans hem ?_
    refine SatC.satC_orE ?_ ?_
    · refine SatC.trans ?_ hCs
      refine SatC.satC_andI ?_ ?_
      · exact SatC.satC_andR _ _
      · exact SatC.trans (SatC.satC_andL _ _) (SatC.satC_andL _ _)
    · refine SatC.trans ?_ hCn
      refine SatC.satC_andI ?_ ?_
      · exact SatC.satC_andR _ _
      · exact SatC.trans (SatC.satC_andL _ _) (SatC.satC_andR _ _)

/-- **Lindenbaum lemma** (standard form): every consistent set extends
    to a type. -/
theorem lindenbaum (O : Ontology) (Γ : Set Concept) (hΓ : consistent O Γ) :
    ∃ t : Type_ O, Γ ⊆ t.carrier := by
  obtain ⟨M, hΓM, hMcons, hMmax⟩ := lindenbaum_max O Γ hΓ
  refine ⟨⟨M, hMcons, lindenbaum_max_closed O M hMcons hMmax⟩, hΓM⟩

-- ============================================================
-- 5.  Type helpers (top_mem, bot_not_mem, type_closure, mem_xor_neg).
-- ============================================================

/-- ⊥ is never in the carrier of a type. -/
theorem bot_not_mem (O : Ontology) (t : Type_ O) :
    Concept.bot ∉ t.carrier := by
  intro hbot
  apply t.cons [Concept.bot]
  · intro C hC; simp at hC; exact hC ▸ hbot
  · show SatC O (conjList [Concept.bot]) Concept.bot
    unfold conjList
    exact SatC.trans (SatC.satC_andL _ _) (satC_refl O _)

/-- Types are closed under SatC consequence. -/
theorem type_closure (O : Ontology) (t : Type_ O) (C D : Concept)
    (hC : C ∈ t.carrier) (hSat : SatC O C D) : D ∈ t.carrier := by
  rcases t.maximal D with hD | hnegD
  · exact hD
  · -- D not in t but ¬D is.  Combined with C ∈ t, conjList [C, ¬D] is
    -- inconsistent via hSat (since C ⊑ D and ¬D ∈ t gives contradiction).
    exfalso
    apply t.cons [C, Concept.neg D]
    · intro E hE
      simp at hE
      rcases hE with rfl | rfl
      · exact hC
      · exact hnegD
    · -- SatC O (conjList [C, ¬D]) ⊥
      show SatC O (conjList [C, Concept.neg D]) Concept.bot
      unfold conjList
      -- conj C (conj ¬D ⊤) ⊑ ⊥
      -- Use SatC.nc on D: (conj D ¬D) ⊑ ⊥
      refine SatC.trans ?_ (SatC.nc D)
      refine SatC.satC_andI ?_ ?_
      · -- conj C (conj ¬D ⊤) ⊑ D, via C ⊑ D
        exact SatC.trans (SatC.satC_andL _ _) hSat
      · -- conj C (conj ¬D ⊤) ⊑ ¬D
        exact SatC.trans (SatC.satC_andR _ _) (SatC.satC_andL _ _)

/-- ⊤ is always in the carrier of a type. -/
theorem top_mem (O : Ontology) (t : Type_ O) :
    Concept.top ∈ t.carrier := by
  -- By maximality: top ∈ t.carrier ∨ neg top ∈ t.carrier.
  rcases t.maximal Concept.top with h | h
  · exact h
  · -- If ¬⊤ ∈ t.carrier, then by closure under SatC (¬⊤ ⊑ ⊥ classically),
    -- ⊥ ∈ t.carrier, contradicting bot_not_mem.
    exfalso
    have hbot : Concept.bot ∈ t.carrier := by
      apply type_closure O t (.neg .top) Concept.bot h
      -- SatC O (neg top) bot
      -- (neg top ⊑ ⊥) via classical: any contradiction with ⊤.
      -- Specifically: neg top ⊓ top ⊑ ⊥ via nc top.
      -- But neg top alone? neg top is "x | I.eval top x is False",
      -- but I.eval top is always True, so neg top is contradictory.
      -- Syntactically: neg top ⊑ neg top ⊓ top (since top is reflexive)
      -- ⊑ bot via nc.
      refine SatC.trans ?_ (SatC.nc Concept.top)
      refine SatC.satC_andI ?_ ?_
      · exact satC_top O _
      · exact satC_refl O _
    exact bot_not_mem O t hbot

/-- A concept is *structural* iff it avoids nominals, hasSelf, and
    positive cardinality bounds.  The canonical model is faithful
    on this fragment.  Lifting hasSelf, nominals, and positive
    cardinality is the planned follow-on. -/
def Structural : Concept → Prop
  | .atom _        => True
  | .top           => True
  | .bot           => True
  | .nom _         => False
  | .neg C         => Structural C
  | .conj A B      => Structural A ∧ Structural B
  | .disj A B      => Structural A ∧ Structural B
  | .exist _ C     => Structural C
  | .univ _ C      => Structural C
  | .atLeast 0 _ C => Structural C
  | .atLeast _ _ _ => False
  | .atMost 0 _ C  => Structural C
  | .atMost _ _ _  => False
  | .hasSelf _     => False

/-- An ontology is *structural* iff every axiom involves only
    structural concepts on both sides. -/
def OntologyStructural (O : Ontology) : Prop :=
  ∀ ax ∈ O, Structural ax.1 ∧ Structural ax.2

/-- Exactly one of `C, ¬C` is in a type's carrier.  Returns the
    disjoint partition. -/
theorem mem_xor_neg (O : Ontology) (t : Type_ O) (C : Concept) :
    (C ∈ t.carrier ∧ Concept.neg C ∉ t.carrier) ∨
    (C ∉ t.carrier ∧ Concept.neg C ∈ t.carrier) := by
  rcases t.maximal C with hC | hnC
  · -- C ∈ t.  We need ¬C ∉ t.  If ¬C ∈ t too, list witness [C, ¬C]
    -- collapses to ⊥, contradicting consistency.
    left
    refine ⟨hC, ?_⟩
    intro hnC
    apply t.cons [C, Concept.neg C]
    · intro E hE
      simp at hE
      rcases hE with rfl | rfl
      · exact hC
      · exact hnC
    · show SatC O (conjList [C, Concept.neg C]) Concept.bot
      unfold conjList
      refine SatC.trans ?_ (SatC.nc C)
      refine SatC.satC_andI ?_ ?_
      · exact SatC.satC_andL _ _
      · exact SatC.trans (SatC.satC_andR _ _) (SatC.satC_andL _ _)
  · -- ¬C ∈ t.  Symmetric: by_cases on C ∈ t.
    by_cases hC : C ∈ t.carrier
    · -- Both C and ¬C in t.  Contradiction.
      left
      refine ⟨hC, ?_⟩
      intro hnC'
      -- inline contradiction
      apply t.cons [C, Concept.neg C]
      · intro E hE
        simp at hE
        rcases hE with rfl | rfl
        · exact hC
        · exact hnC'
      · show SatC O (conjList [C, Concept.neg C]) Concept.bot
        unfold conjList
        refine SatC.trans ?_ (SatC.nc C)
        refine SatC.satC_andI ?_ ?_
        · exact SatC.satC_andL _ _
        · exact SatC.trans (SatC.satC_andR _ _) (SatC.satC_andL _ _)
    · right
      exact ⟨hC, hnC⟩

-- ============================================================
-- 6.  Canonical interpretation.
-- ============================================================

/-- A "default" type in `Type_ O` if one exists (otherwise we can't
    define ext_ind cleanly).  For the structural fragment (no
    nominals), `ext_ind` is unused so we use the empty default. -/
noncomputable def Interp.defaultType (O : Ontology)
    (h : ∃ t : Type_ O, True) : Type_ O :=
  h.choose

/-- The canonical interpretation, parameterised on a non-emptiness
    witness for `Type_ O`.  The `ext_role` definition is the standard
    ALC Hintikka clause; the truth lemma is proved for the
    structural fragment (no hasSelf, no nominals, no positive
    cardinality).  Extending the role with a self-loop case for
    hasSelf, and the domain with nominal-quotient and
    Skolem-cardinality-tagging, is the planned follow-on. -/
noncomputable def canonical (O : Ontology)
    (hNE : ∃ t : Type_ O, True) :
    Interp (Type_ O) where
  ext_concept n t := Concept.atom n ∈ t.carrier
  ext_role R t t' :=
    ∀ C, Concept.univ R C ∈ t.carrier → C ∈ t'.carrier
  ext_ind _ := Interp.defaultType O hNE

-- ============================================================
-- 7.  Witness-existence for the existential truth-lemma case.
-- ============================================================

/-- The *successor seed* for a type `t` with `∃R.C ∈ t.carrier`: the
    set containing `C` together with every `D` forced by a universal
    `∀R.D ∈ t.carrier`.  We will Lindenbaum-extend this to a type. -/
def successorSet (O : Ontology) (t : Type_ O) (R : Nat) (C : Concept) :
    Set Concept :=
  {C} ∪ {D | Concept.univ R D ∈ t.carrier}

theorem mem_successorSet_iff (O : Ontology) (t : Type_ O) (R : Nat)
    (C D : Concept) :
    D ∈ successorSet O t R C ↔
      D = C ∨ Concept.univ R D ∈ t.carrier := by
  unfold successorSet
  constructor
  · rintro (rfl | h)
    · left; rfl
    · right; exact h
  · rintro (rfl | h)
    · left; rfl
    · right; exact h

/-- Universal-conjunction helper: maps a list of fillers to the
    conjunction ∀R.D₁ ⊓ … ⊓ ∀R.Dₙ ⊓ ⊤. -/
def univListConj (R : Nat) : List Concept → Concept
  | []        => Concept.top
  | D :: Ds   => Concept.conj (Concept.univ R D) (univListConj R Ds)

/-- The role-axis join lemma (iterated `exForall`): from ∃R.C ⊓
    (∀R.D₁ ⊓ … ⊓ ∀R.Dₙ) derive ∃R.(C ⊓ D₁ ⊓ … ⊓ Dₙ). -/
theorem satC_exist_with_univs
    (O : Ontology) (R : Nat) (C : Concept) :
    ∀ Ds : List Concept,
      SatC O (.conj (.exist R C) (univListConj R Ds))
             (.exist R (.conj C (conjList Ds)))
  | [] => by
      unfold univListConj conjList
      refine SatC.trans (SatC.satC_andL _ _) ?_
      exact SatC.ofSat (Sat.monoExist R
        (Sat.andI (Sat.refl C) (Sat.top C)))
  | D :: Ds => by
      unfold univListConj conjList
      have ih := satC_exist_with_univs O R (.conj C D) Ds
      have h_join : SatC O (.conj (.exist R C) (.univ R D))
                            (.exist R (.conj C D)) :=
        SatC.exForall R C D
      have h_lift :
          SatC O
            (.conj (.exist R C) (.conj (.univ R D) (univListConj R Ds)))
            (.conj (.exist R (.conj C D)) (univListConj R Ds)) := by
        refine SatC.satC_andI ?_ ?_
        · refine SatC.trans ?_ h_join
          refine SatC.satC_andI ?_ ?_
          · exact SatC.satC_andL _ _
          · exact SatC.trans (SatC.satC_andR _ _) (SatC.satC_andL _ _)
        · refine SatC.trans (SatC.satC_andR _ _) (SatC.satC_andR _ _)
      refine SatC.trans h_lift (SatC.trans ih ?_)
      apply SatC.ofSat (Sat.monoExist R ?_)
      -- Need: Sat O (conj (conj C D) (conjList Ds))
      --                (conj C (conj D (conjList Ds)))
      -- This is associativity rebracketing, provable in Sat.
      exact (Sat.andI
                (Sat.trans (Sat.andL _ _) (Sat.andL _ _))
                (Sat.andI
                    (Sat.trans (Sat.andL _ _) (Sat.andR _ _))
                    (Sat.andR _ _)))

theorem satC_map_univ_to_univListConj
    (O : Ontology) (R : Nat) :
    ∀ Ds : List Concept,
      SatC O (conjList (Ds.map (Concept.univ R))) (univListConj R Ds)
  | [] => by
      unfold conjList univListConj
      exact satC_refl O _
  | D :: Ds => by
      unfold conjList univListConj
      refine SatC.satC_andI ?_ ?_
      · exact SatC.satC_andL _ _
      · refine SatC.trans (SatC.satC_andR _ _) ?_
        exact satC_map_univ_to_univListConj O R Ds

/-- The successor seed is consistent whenever `∃R.C` is in `t`. -/
theorem successor_consistent
    (O : Ontology) (t : Type_ O) (R : Nat) (C : Concept)
    (hExist : Concept.exist R C ∈ t.carrier) :
    consistent O (successorSet O t R C) := by
  intro L hLin hSat
  let Ds := L.filter (· ≠ C)
  have hDs : ∀ D ∈ Ds, Concept.univ R D ∈ t.carrier := by
    intro D hD
    obtain ⟨hin, hne⟩ := List.mem_filter.mp hD
    rcases (mem_successorSet_iff O t R C D).mp (hLin D hin) with hC | hUniv
    · exact absurd hC (by simpa using hne)
    · exact hUniv
  apply t.cons (Concept.exist R C :: Ds.map (Concept.univ R))
  · intro D' hD'
    rcases List.mem_cons.mp hD' with rfl | hMap
    · exact hExist
    · obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hMap
      exact hDs D hD
  · show SatC O (conjList (Concept.exist R C :: Ds.map (Concept.univ R)))
              Concept.bot
    unfold conjList
    have h1 :
        SatC O (.conj (.exist R C) (conjList (Ds.map (Concept.univ R))))
               (.conj (.exist R C) (univListConj R Ds)) := by
      refine SatC.satC_andI ?_ ?_
      · exact SatC.satC_andL _ _
      · exact SatC.trans (SatC.satC_andR _ _)
          (satC_map_univ_to_univListConj O R Ds)
    have h2 :
        SatC O (.conj (.exist R C) (univListConj R Ds))
               (.exist R (.conj C (conjList Ds))) :=
      satC_exist_with_univs O R C Ds
    have h3 : SatC O (.conj C (conjList Ds)) Concept.bot :=
      SatC.trans (satC_conj_filter_implies_list O C L) hSat
    have h4 : SatC O (.exist R (.conj C (conjList Ds))) (.exist R .bot) :=
      SatC.satC_monoExist R h3
    have h5 : SatC O (.exist R Concept.bot) Concept.bot := SatC.existBot R
    refine SatC.trans h1 (SatC.trans h2 (SatC.trans h4 h5))

/-- **Witness lemma for ∃R.·**: if `∃R.C ∈ t.carrier`, then in the
    canonical model there is a successor type `t'` containing `C` and
    bearing the R-edge from `t`. -/
theorem witness_exist
    (O : Ontology) (hNE : ∃ t : Type_ O, True)
    (t : Type_ O) (R : Nat) (C : Concept)
    (hExist : Concept.exist R C ∈ t.carrier) :
    ∃ t' : Type_ O, (canonical O hNE).ext_role R t t' ∧ C ∈ t'.carrier := by
  obtain ⟨t', ht'⟩ := lindenbaum O (successorSet O t R C)
    (successor_consistent O t R C hExist)
  refine ⟨t', ?_, ?_⟩
  · -- ext_role: ∀ D, univ R D ∈ t → D ∈ t'
    intro D hUniv
    exact ht' ((mem_successorSet_iff O t R C D).mpr (Or.inr hUniv))
  · -- C ∈ t'.carrier
    exact ht' ((mem_successorSet_iff O t R C C).mpr (Or.inl rfl))

end ALCHOQ
end ELKSDD
