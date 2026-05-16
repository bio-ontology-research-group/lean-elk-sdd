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

-- ============================================================
-- 8.  Truth lemma (canonical_eval_iff) for the structural fragment.
-- ============================================================

/-- The truth lemma for the structural ALCHOQ fragment.  Non-
    structural cases (`nom`, `hasSelf`, `atLeast (n+1)`,
    `atMost (n+1)`) are dispatched via the `Structural` hypothesis. -/
theorem canonical_eval_iff
    (O : Ontology) (hNE : ∃ t : Type_ O, True)
    (C : Concept) :
    Structural C →
    ∀ t : Type_ O, ((canonical O hNE).eval C t ↔ C ∈ t.carrier) := by
  induction C with
  | atom n =>
      intro _ t
      exact Iff.rfl
  | top =>
      intro _ t
      show True ↔ _
      exact ⟨fun _ => top_mem O t, fun _ => trivial⟩
  | bot =>
      intro _ t
      show False ↔ _
      exact ⟨fun h => h.elim, fun h => (bot_not_mem O t h).elim⟩
  | nom _ =>
      intro hC _
      exact hC.elim
  | neg C ih =>
      intro hC t
      show (¬ (canonical O hNE).eval C t) ↔ Concept.neg C ∈ t.carrier
      rw [ih hC t]
      rcases mem_xor_neg O t C with ⟨hCmem, hnCnotmem⟩ | ⟨hCnotmem, hnCmem⟩
      · constructor
        · intro h; exact absurd hCmem h
        · intro h; exact absurd h hnCnotmem
      · constructor
        · intro _; exact hnCmem
        · intro _; exact hCnotmem
  | conj A B ihA ihB =>
      intro hC t
      obtain ⟨hA, hB⟩ := hC
      show ((canonical O hNE).eval A t ∧ (canonical O hNE).eval B t) ↔
            Concept.conj A B ∈ t.carrier
      rw [ihA hA t, ihB hB t]
      constructor
      · rintro ⟨hAmem, hBmem⟩
        rcases t.maximal (Concept.conj A B) with hMem | hNeg
        · exact hMem
        · exfalso
          apply t.cons [A, B, Concept.neg (Concept.conj A B)]
          · intro D hD
            simp at hD
            rcases hD with rfl | rfl | rfl
            · exact hAmem
            · exact hBmem
            · exact hNeg
          · show SatC O (conjList [A, B, Concept.neg (Concept.conj A B)])
                       Concept.bot
            unfold conjList
            refine SatC.trans ?_ (SatC.nc (Concept.conj A B))
            refine SatC.satC_andI ?_ ?_
            · refine SatC.satC_andI ?_ ?_
              · exact SatC.satC_andL _ _
              · exact SatC.trans (SatC.satC_andR _ _) (SatC.satC_andL _ _)
            · refine SatC.trans (SatC.satC_andR _ _) ?_
              refine SatC.trans (SatC.satC_andR _ _) ?_
              exact SatC.satC_andL _ _
      · intro hConj
        refine ⟨?_, ?_⟩
        · by_contra hAne
          rcases t.maximal A with hAmem | hAneg
          · exact hAne hAmem
          · apply t.cons [Concept.conj A B, Concept.neg A]
            · intro D hD
              simp at hD
              rcases hD with rfl | rfl
              · exact hConj
              · exact hAneg
            · show SatC O (conjList [Concept.conj A B, Concept.neg A])
                         Concept.bot
              unfold conjList
              refine SatC.trans ?_ (SatC.nc A)
              refine SatC.satC_andI ?_ ?_
              · exact SatC.trans (SatC.satC_andL _ _) (SatC.satC_andL _ _)
              · exact SatC.trans (SatC.satC_andR _ _) (SatC.satC_andL _ _)
        · by_contra hBne
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
              refine SatC.satC_andI ?_ ?_
              · exact SatC.trans (SatC.satC_andL _ _) (SatC.satC_andR _ _)
              · exact SatC.trans (SatC.satC_andR _ _) (SatC.satC_andL _ _)
  | disj A B ihA ihB =>
      intro hC t
      obtain ⟨hA, hB⟩ := hC
      show ((canonical O hNE).eval A t ∨ (canonical O hNE).eval B t) ↔
            Concept.disj A B ∈ t.carrier
      rw [ihA hA t, ihB hB t]
      constructor
      · rintro (hAmem | hBmem)
        · rcases t.maximal (Concept.disj A B) with hMem | hNeg
          · exact hMem
          · exfalso
            apply t.cons [A, Concept.neg (Concept.disj A B)]
            · intro D hD
              simp at hD
              rcases hD with rfl | rfl
              · exact hAmem
              · exact hNeg
            · show SatC O (conjList [A, Concept.neg (Concept.disj A B)])
                         Concept.bot
              unfold conjList
              refine SatC.trans ?_ (SatC.nc (Concept.disj A B))
              refine SatC.satC_andI ?_ ?_
              · exact SatC.trans (SatC.satC_andL _ _) (satC_orL O _ _)
              · exact SatC.trans (SatC.satC_andR _ _) (SatC.satC_andL _ _)
        · rcases t.maximal (Concept.disj A B) with hMem | hNeg
          · exact hMem
          · exfalso
            apply t.cons [B, Concept.neg (Concept.disj A B)]
            · intro D hD
              simp at hD
              rcases hD with rfl | rfl
              · exact hBmem
              · exact hNeg
            · show SatC O (conjList [B, Concept.neg (Concept.disj A B)])
                         Concept.bot
              unfold conjList
              refine SatC.trans ?_ (SatC.nc (Concept.disj A B))
              refine SatC.satC_andI ?_ ?_
              · exact SatC.trans (SatC.satC_andL _ _) (satC_orR O _ _)
              · exact SatC.trans (SatC.satC_andR _ _) (SatC.satC_andL _ _)
      · intro hDisj
        by_contra hNeither
        push_neg at hNeither
        obtain ⟨hAne, hBne⟩ := hNeither
        rcases t.maximal A with hAmem | hnA
        · exact hAne hAmem
        rcases t.maximal B with hBmem | hnB
        · exact hBne hBmem
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
          refine SatC.trans ?_ (SatC.nc (Concept.disj A B))
          refine SatC.satC_andI ?_ ?_
          · exact SatC.satC_andL _ _
          · refine SatC.trans ?_ (SatC.deMorganO' A B)
            refine SatC.satC_andI ?_ ?_
            · exact SatC.trans (SatC.satC_andR _ _) (SatC.satC_andL _ _)
            · refine SatC.trans (SatC.satC_andR _ _) ?_
              refine SatC.trans (SatC.satC_andR _ _) ?_
              exact SatC.satC_andL _ _
  | exist R C ih =>
      intro hC t
      show (∃ t', (canonical O hNE).ext_role R t t' ∧
                   (canonical O hNE).eval C t') ↔
            Concept.exist R C ∈ t.carrier
      constructor
      · rintro ⟨t', hR, hCt'⟩
        rcases t.maximal (Concept.exist R C) with hMem | hNeg
        · exact hMem
        · have hUniv : Concept.univ R (Concept.neg C) ∈ t.carrier :=
            type_closure O t _ _ hNeg (SatC.negExist R C)
          have hnC : Concept.neg C ∈ t'.carrier := hR _ hUniv
          have hCmem : C ∈ t'.carrier := (ih hC t').mp hCt'
          exfalso
          rcases mem_xor_neg O t' C with ⟨_, hnnC⟩ | ⟨hCnotmem, _⟩
          · exact hnnC hnC
          · exact hCnotmem hCmem
      · intro hExist
        obtain ⟨t', hR, hCt'⟩ := witness_exist O hNE t R C hExist
        exact ⟨t', hR, (ih hC t').mpr hCt'⟩
  | univ R C ih =>
      intro hC t
      show (∀ t', (canonical O hNE).ext_role R t t' →
                   (canonical O hNE).eval C t') ↔
            Concept.univ R C ∈ t.carrier
      constructor
      · intro hAll
        rcases t.maximal (Concept.univ R C) with hMem | hNeg
        · exact hMem
        · have hExistNeg : Concept.exist R (Concept.neg C) ∈ t.carrier :=
            type_closure O t _ _ hNeg (SatC.negUniv R C)
          obtain ⟨t', hR, hnCt'⟩ :=
            witness_exist O hNE t R (Concept.neg C) hExistNeg
          have hCt' : (canonical O hNE).eval C t' := hAll t' hR
          have hCmem : C ∈ t'.carrier := (ih hC t').mp hCt'
          exfalso
          rcases mem_xor_neg O t' C with ⟨_, hnnC⟩ | ⟨hCnotmem, _⟩
          · exact hnnC hnCt'
          · exact hCnotmem hCmem
      · intro hUniv t' hR
        have hCt' : C ∈ t'.carrier := hR C hUniv
        exact (ih hC t').mpr hCt'
  | atLeast n R C ih =>
      intro hC t
      cases n with
      | zero =>
          have hC' : Structural C := hC
          constructor
          · intro _
            exact type_closure O t _ _ (top_mem O t)
              (SatC.atLeastZero R C)
          · intro _
            show Interp.atLeastCard _ 0
            exact trivial
      | succ _ => exact hC.elim
  | atMost n R C ih =>
      intro hC t
      cases n with
      | zero =>
          have hC' : Structural C := hC
          have hSem : (canonical O hNE).eval (.atMost 0 R C) t ↔
                      ∀ t', (canonical O hNE).ext_role R t t' →
                            ¬ (canonical O hNE).eval C t' :=
            Interp.eval_atMost_zero (canonical O hNE) R C t
          rw [hSem]
          constructor
          · intro hAll
            have hUnivNeg : Concept.univ R (Concept.neg C) ∈ t.carrier := by
              rcases t.maximal (Concept.univ R (Concept.neg C)) with h | h
              · exact h
              · have hExC : Concept.exist R C ∈ t.carrier := by
                  have h1 : Concept.exist R (.neg (.neg C)) ∈ t.carrier :=
                    type_closure O t _ _ h (SatC.negUniv R (.neg C))
                  exact type_closure O t _ _ h1
                    (SatC.satC_monoExist R (SatC.negNegE C))
                obtain ⟨t', hR, hCt'⟩ := witness_exist O hNE t R C hExC
                have hCsem : (canonical O hNE).eval C t' :=
                  (ih hC' t').mpr hCt'
                exact absurd hCsem (hAll t' hR)
            exact type_closure O t _ _ hUnivNeg
              (SatC.univ_to_atMostZero R C)
          · intro hAtMost t' hR
            have hUnivNeg : Concept.univ R (Concept.neg C) ∈ t.carrier :=
              type_closure O t _ _ hAtMost (SatC.atMostZero R C)
            have hNegC_mem : Concept.neg C ∈ t'.carrier := hR _ hUnivNeg
            intro hCeval
            have hCmem : C ∈ t'.carrier := (ih hC' t').mp hCeval
            rcases mem_xor_neg O t' C with ⟨_, hnnC⟩ | ⟨hCnotmem, _⟩
            · exact hnnC hNegC_mem
            · exact hCnotmem hCmem
      | succ _ => exact hC.elim
  | hasSelf _ =>
      intro hC _
      exact hC.elim

-- ============================================================
-- 9.  Canonical satisfies the structural ontology.
-- ============================================================

theorem canonical_satisfies
    (O : Ontology) (hNE : ∃ t : Type_ O, True)
    (hOStruct : OntologyStructural O) :
    (canonical O hNE).satisfies O := by
  intro ax hAx t hP
  obtain ⟨h1Struct, h2Struct⟩ := hOStruct ax hAx
  have h1 : ax.1 ∈ t.carrier :=
    (canonical_eval_iff O hNE ax.1 h1Struct t).mp hP
  have h2 : ax.2 ∈ t.carrier :=
    type_closure O t _ _ h1
      (SatC.ofSat (Sat.axm ax.1 ax.2 hAx))
  exact (canonical_eval_iff O hNE ax.2 h2Struct t).mpr h2

-- ============================================================
-- 10.  The two-element set ``{C, ¬D}`` is consistent if C ⊑ D is not
--      SatC-derivable.  Used in the contradiction proof of
--      completeness.
-- ============================================================

theorem c_negD_consistent (O : Ontology) (C D : Concept)
    (hNotSat : ¬ SatC O C D) :
    consistent O ({C, Concept.neg D} : Set Concept) := by
  intro L hLin hSat
  have aux :
      ∀ L' : List Concept,
        (∀ E ∈ L', E ∈ ({C, Concept.neg D} : Set Concept)) →
        SatC O (.conj C (.neg D)) (conjList L') := by
    intro L'
    induction L' with
    | nil =>
        intro _
        unfold conjList
        exact satC_top O _
    | cons E Es ih =>
        intro hL'in
        unfold conjList
        have hE_mem : E ∈ ({C, Concept.neg D} : Set Concept) :=
          hL'in E List.mem_cons_self
        rcases hE_mem with hEC | hEnegD
        · subst hEC
          refine SatC.satC_andI ?_ ?_
          · exact SatC.satC_andL _ _
          · exact ih (fun F hF => hL'in F (List.mem_cons_of_mem _ hF))
        · have hEeq : E = Concept.neg D := hEnegD
          subst hEeq
          refine SatC.satC_andI ?_ ?_
          · exact SatC.satC_andR _ _
          · exact ih (fun F hF => hL'in F (List.mem_cons_of_mem _ hF))
  have hCNeg : SatC O (.conj C (.neg D)) (conjList L) := aux L hLin
  have hContra : SatC O (.conj C (.neg D)) Concept.bot :=
    SatC.trans hCNeg hSat
  apply hNotSat
  -- C ⊑ C ⊓ (D ⊔ ¬D) ⊑ (C⊓D) ⊔ (C⊓¬D) ⊑ D.
  have step1 : SatC O C (.conj C (.disj D (.neg D))) :=
    SatC.satC_andI (satC_refl O C)
                   (SatC.trans (satC_top O C) (SatC.em D))
  have step2 : SatC O (.conj C (.disj D (.neg D))) D := by
    refine SatC.trans (SatC.dist C D (Concept.neg D)) ?_
    refine SatC.satC_orE ?_ ?_
    · exact SatC.satC_andR _ _
    · exact SatC.trans hContra (satC_bot O D)
  exact SatC.trans step1 step2

-- ============================================================
-- 11.  Completeness theorem for the structural fragment.
-- ============================================================

/-- Non-emptiness of `Type_ O`: provable from consistency of the
    empty set (which is equivalent to O being SatC-satisfiable). -/
theorem type_nonempty_of_consistent (O : Ontology)
    (hC : consistent O (∅ : Set Concept)) :
    ∃ t : Type_ O, True := by
  obtain ⟨t, _⟩ := lindenbaum O ∅ hC
  exact ⟨t, trivial⟩

/-- **Completeness theorem for the structural ALCHOQ fragment**.

    For ALCHOQ concepts in the no-nom / no-hasSelf / cardinality-
    trivial sub-fragment, every Tarskian entailment under O is
    derivable in `SatC`.

    Non-structural cases (nominals, hasSelf, positive cardinality)
    require either a quotient construction or auxiliary-individual
    Skolemization (Tena~Cucala 2021 thesis); planned as follow-on.
-/
theorem satC_complete_structural
    (O : Ontology) (C D : Concept)
    (hOStruct : OntologyStructural O)
    (hC : Structural C) (hD : Structural D)
    (hEnt : Entails O C D) : SatC O C D := by
  by_contra hNot
  -- We want a contradiction.  Distinguish on whether ∅ is
  -- SatC-consistent under O.  If ¬consistent O ∅, then top ⊑ bot is
  -- derivable, so SatC O C D follows trivially — contradiction with
  -- hNot.
  by_cases hCons : consistent O (∅ : Set Concept)
  · -- O is consistent.  Build a counter-model and contradict hEnt.
    have hCN : consistent O ({C, Concept.neg D} : Set Concept) :=
      c_negD_consistent O C D hNot
    obtain ⟨t, htsub⟩ := lindenbaum O _ hCN
    have hNE : ∃ t : Type_ O, True := type_nonempty_of_consistent O hCons
    have hsat : (canonical O hNE).satisfies O :=
      canonical_satisfies O hNE hOStruct
    have hCmem : C ∈ t.carrier :=
      htsub (by simp : C ∈ ({C, Concept.neg D} : Set _))
    have hEvalC : (canonical O hNE).eval C t :=
      (canonical_eval_iff O hNE C hC t).mpr hCmem
    have hEvalD : (canonical O hNE).eval D t := hEnt _ hsat t hEvalC
    have hDmem : D ∈ t.carrier :=
      (canonical_eval_iff O hNE D hD t).mp hEvalD
    have hnDmem : Concept.neg D ∈ t.carrier :=
      htsub (by simp : Concept.neg D ∈ ({C, Concept.neg D} : Set _))
    rcases mem_xor_neg O t D with ⟨_, hnnD⟩ | ⟨hDnotmem, _⟩
    · exact hnnD hnDmem
    · exact hDnotmem hDmem
  · -- O is inconsistent.  Then top ⊑ bot is derivable; chain to SatC O C D.
    unfold consistent at hCons
    push_neg at hCons
    obtain ⟨L, hLin, hSat⟩ := hCons
    -- All elements of L are in ∅, so L = []; conjList [] = top.
    have hLnil : L = [] := by
      cases L with
      | nil => rfl
      | cons E Es => exact absurd (hLin E List.mem_cons_self) (by simp)
    subst hLnil
    -- hSat : SatC O (conjList []) bot = SatC O top bot
    have hTopBot : SatC O Concept.top Concept.bot := by
      have : conjList ([] : List Concept) = Concept.top := rfl
      rw [this] at hSat
      exact hSat
    -- Now SatC O C D via C ⊑ top ⊑ bot ⊑ D.
    apply hNot
    exact SatC.trans (satC_top O C)
            (SatC.trans hTopBot (satC_bot O D))

end ALCHOQ
end ELKSDD
