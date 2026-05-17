/-
  ELKSDD/SROIQCanonical.lean
  ---------------------------
  Canonical-model construction over `SROIQ.SatC` (rather than
  `ALCHOQ.SatC`).  This is the SROIQ-specific Lindenbaum / type
  machinery needed so that maximal-consistent types are closed under
  the SROIQ-only rules (`roleIncl_univ`, `roleChain_two`,
  `roleTrans_exist`, `roleRefl_exist`, `roleIncl_hasSelf`,
  `roleTrans_univ`).

  Strategy
  --------
  `SROIQ.SatC R O` *extends* `ALCHOQ.SatC O` via `ofAlchoq`.
  Consequently every SROIQ-consistent set is also ALCHOQ-consistent,
  and every maximal SROIQ-consistent set whose carrier sees every
  `C ∨ ¬C` is automatically an `ALCHOQ.Type_` — so the entire ALCHOQ
  truth-lemma infrastructure lifts via the coercion `Type_.toAlchoq`.

  The new contribution of this file is:

  * `consistent` / `Type_` defined over `SROIQ.SatC`;
  * `type_closure` under `SROIQ.SatC` (not just ALCHOQ);
  * `lindenbaum` for the SROIQ-consistent predicate (full Zorn
    proof for the SROIQ-consistency predicate).

  Axiom-clean over `[propext, Classical.choice, Quot.sound]`.
-/

import ELKSDD.ALCHOQCanonical
import ELKSDD.SROIQCompleteness
import Mathlib.Order.Zorn

namespace ELKSDD
namespace SROIQ

open Classical
open ALCHOQ (Concept Ontology Interp)

-- ============================================================
-- 1.  conjList and structural SatC lemmas at SROIQ level.
-- ============================================================

abbrev conjList := ALCHOQ.conjList

theorem satC_refl (R : RBox) (O : Ontology) (C : Concept) :
    SatC R O C C := SatC.ofAlchoq (ALCHOQ.satC_refl O C)

theorem satC_top (R : RBox) (O : Ontology) (C : Concept) :
    SatC R O C Concept.top := SatC.ofAlchoq (ALCHOQ.satC_top O C)

theorem satC_bot (R : RBox) (O : Ontology) (C : Concept) :
    SatC R O Concept.bot C := SatC.ofAlchoq (ALCHOQ.satC_bot O C)

theorem satC_andL (R : RBox) (O : Ontology) (C D : Concept) :
    SatC R O (.conj C D) C := SatC.ofAlchoq (ALCHOQ.SatC.satC_andL C D)

theorem satC_andR (R : RBox) (O : Ontology) (C D : Concept) :
    SatC R O (.conj C D) D := SatC.ofAlchoq (ALCHOQ.SatC.satC_andR C D)

theorem satC_nc (R : RBox) (O : Ontology) (C : Concept) :
    SatC R O (.conj C (.neg C)) .bot := SatC.ofAlchoq (ALCHOQ.SatC.nc C)

theorem satC_weak_left (R : RBox) (O : Ontology) {C D E : Concept}
    (h : SatC R O C E) : SatC R O (.conj C D) E :=
  SatC.trans (satC_andL R O C D) h

theorem satC_weak_right (R : RBox) (O : Ontology) {C D E : Concept}
    (h : SatC R O D E) : SatC R O (.conj C D) E :=
  SatC.trans (satC_andR R O C D) h

-- ============================================================
-- 2.  Consistency and types.
-- ============================================================

/-- A concept set ``Γ`` is *SROIQ-SatC-consistent* under `R, O` if
    `SROIQ.SatC` does not derive ``⨅L ⊑ ⊥`` for any finite list `L`
    of elements of `Γ`. -/
def consistent (R : RBox) (O : Ontology) (Γ : Set Concept) : Prop :=
  ∀ L : List Concept, (∀ C ∈ L, C ∈ Γ) →
    ¬ SatC R O (conjList L) Concept.bot

/-- SROIQ-consistent implies ALCHOQ-consistent (contrapositive of the
    fact that ALCHOQ inconsistencies lift to SROIQ via `ofAlchoq`). -/
theorem alchoq_consistent_of_sroiq (R : RBox) (O : Ontology) (Γ : Set Concept)
    (h : consistent R O Γ) : ALCHOQ.consistent O Γ := by
  intro L hLin hSatA
  exact h L hLin (SatC.ofAlchoq hSatA)

/-- The set of *SROIQ-types*: maximal SROIQ-consistent sets. -/
structure Type_ (R : RBox) (O : Ontology) where
  carrier : Set Concept
  cons    : consistent R O carrier
  maximal : ∀ C : Concept, C ∈ carrier ∨ Concept.neg C ∈ carrier

/-- Every SROIQ-type wraps as an ALCHOQ-type — same carrier, same
    maximality, ALCHOQ-consistency inherited via the SROIQ ⊇ ALCHOQ
    direction. -/
def Type_.toAlchoq {R : RBox} {O : Ontology} (t : Type_ R O) :
    ALCHOQ.Type_ O where
  carrier := t.carrier
  cons    := alchoq_consistent_of_sroiq R O t.carrier t.cons
  maximal := t.maximal

-- ============================================================
-- 3.  Bot/top/xor-neg lemmas inherited via coercion.
-- ============================================================

theorem bot_not_mem (R : RBox) (O : Ontology) (t : Type_ R O) :
    Concept.bot ∉ t.carrier :=
  ALCHOQ.bot_not_mem O t.toAlchoq

theorem top_mem (R : RBox) (O : Ontology) (t : Type_ R O) :
    Concept.top ∈ t.carrier :=
  ALCHOQ.top_mem O t.toAlchoq

theorem mem_xor_neg (R : RBox) (O : Ontology) (t : Type_ R O) (C : Concept) :
    (C ∈ t.carrier ∧ Concept.neg C ∉ t.carrier) ∨
    (C ∉ t.carrier ∧ Concept.neg C ∈ t.carrier) :=
  ALCHOQ.mem_xor_neg O t.toAlchoq C

-- ============================================================
-- 4.  type_closure under SROIQ.SatC (THE KEY NEW LEMMA).
-- ============================================================

/-- SROIQ-types are closed under SROIQ-SatC consequence: this is what
    makes the canonical model satisfy role-inclusion / transitivity /
    chain RBox axioms because `SROIQ.SatC` includes `roleIncl_univ`,
    `roleChain_two`, `roleTrans_exist`, `roleTrans_univ`, etc. -/
theorem type_closure (R : RBox) (O : Ontology) (t : Type_ R O) (C D : Concept)
    (hC : C ∈ t.carrier) (hSat : SatC R O C D) : D ∈ t.carrier := by
  rcases t.maximal D with hD | hnegD
  · exact hD
  · exfalso
    apply t.cons [C, Concept.neg D]
    · intro E hE
      simp at hE
      rcases hE with rfl | rfl
      · exact hC
      · exact hnegD
    · show SatC R O (conjList [C, Concept.neg D]) Concept.bot
      unfold conjList ALCHOQ.conjList
      -- Goal: conj C (conj ¬D ⊤) ⊑ ⊥, deriving via:
      --   conj C (conj ¬D ⊤) ⊑ conj D ¬D ⊑ ⊥
      refine SatC.trans ?_ (satC_nc R O D)
      -- Goal: conj C (conj ¬D ⊤) ⊑ conj D ¬D
      apply SatC.satC_andI
      · -- conj C (conj ¬D ⊤) ⊑ D
        exact SatC.trans (satC_andL R O _ _) hSat
      · -- conj C (conj ¬D ⊤) ⊑ ¬D
        exact SatC.trans
          (satC_andR R O _ _)
          (satC_andL R O _ _)

-- ============================================================
-- 5.  Lindenbaum lemma for SROIQ-consistency.
-- ============================================================

/-- Chain-union of SROIQ-consistent sets is SROIQ-consistent. -/
theorem consistent_chain_union (R : RBox) (O : Ontology)
    (c : Set (Set Concept)) (hAllCons : ∀ Δ ∈ c, consistent R O Δ)
    (hchain : IsChain (· ⊆ ·) c) (hnonempty : c.Nonempty) :
    consistent R O (⋃₀ c) := by
  intro L hLin hSat
  obtain ⟨Δ, hΔc, hΔL⟩ :=
    ALCHOQ.chain_finite_dominates_ALCHOQ c hchain hnonempty L hLin
  exact hAllCons Δ hΔc L hΔL hSat

/-- Lindenbaum part 1 (Zorn): every SROIQ-consistent set extends to a
    maximal SROIQ-consistent set. -/
theorem lindenbaum_max (R : RBox) (O : Ontology) (Γ : Set Concept)
    (hΓ : consistent R O Γ) :
    ∃ M : Set Concept, Γ ⊆ M ∧ consistent R O M ∧
      Maximal (· ∈ {Δ | consistent R O Δ}) M := by
  classical
  have key : ∃ M, Γ ⊆ M ∧ Maximal (· ∈ {Δ | consistent R O Δ}) M := by
    apply zorn_subset_nonempty (S := {Δ | consistent R O Δ})
    · intro c hcS hchain hne
      refine ⟨⋃₀ c, ?_, ?_⟩
      · exact consistent_chain_union R O c (fun Δ hΔ => hcS hΔ) hchain hne
      · intro Δ hΔ x hx; exact ⟨Δ, hΔ, hx⟩
    · exact hΓ
  obtain ⟨M, hΓM, hMmax⟩ := key
  exact ⟨M, hΓM, hMmax.prop, hMmax⟩

/-- A maximal SROIQ-consistent set is *closed* under classical case
    analysis: every `C` is either in `M` or `¬C` is.

    Same Zorn-maximality argument as in `ALCHOQ.lindenbaum_max_closed`
    but with the consistent predicate replaced; we reuse the ALCHOQ
    closure via the consistency-coercion. -/
theorem lindenbaum_max_closed
    (R : RBox) (O : Ontology) (M : Set Concept)
    (hCons : consistent R O M)
    (hMax : Maximal (· ∈ {Δ | consistent R O Δ}) M) :
    ∀ C : Concept, C ∈ M ∨ Concept.neg C ∈ M := by
  intro C
  -- If neither is in M, both M ∪ {C} and M ∪ {¬C} extend M strictly,
  -- so by maximality both must be inconsistent.  From two
  -- inconsistencies we derive ⊥ ∈ M-derivation, contradicting hCons.
  classical
  by_contra hN
  push_neg at hN
  obtain ⟨hCnot, hnCnot⟩ := hN
  -- M ∪ {C} is inconsistent.
  have hC_incon : ¬ consistent R O (insert C M) := by
    intro hCons'
    have hExt : M ⊆ insert C M := fun x hx => Set.mem_insert_of_mem _ hx
    have hThis : (insert C M) ∈ {Δ | consistent R O Δ} := hCons'
    have hM_eq : insert C M = M := hMax.eq_of_ge hThis hExt
    apply hCnot
    rw [← hM_eq]; exact Set.mem_insert _ _
  -- M ∪ {¬C} is inconsistent.
  have hnC_incon : ¬ consistent R O (insert (Concept.neg C) M) := by
    intro hCons'
    have hExt : M ⊆ insert (Concept.neg C) M :=
      fun x hx => Set.mem_insert_of_mem _ hx
    have hThis : (insert (Concept.neg C) M) ∈ {Δ | consistent R O Δ} := hCons'
    have hM_eq : insert (Concept.neg C) M = M := hMax.eq_of_ge hThis hExt
    apply hnCnot
    rw [← hM_eq]; exact Set.mem_insert _ _
  -- Both inconsistencies in hand.  Extract finite witnesses.
  unfold consistent at hC_incon
  push_neg at hC_incon
  obtain ⟨L_C, hLC_in, hLC_sat⟩ := hC_incon
  unfold consistent at hnC_incon
  push_neg at hnC_incon
  obtain ⟨L_nC, hLnC_in, hLnC_sat⟩ := hnC_incon
  -- From hLC_sat (∃ L_C in M ∪ {C}, conjList L_C ⊑ ⊥):
  -- derive  conjList (L_C ∖ {C}) ⊑ ¬C  by case-split on C ∈ L_C.
  -- Symmetric on hLnC_sat for ¬C.
  -- Then conjList ((L_C ∖ {C}) ++ (L_nC ∖ {¬C})) ⊑ conj (¬C) C ⊑ ⊥,
  -- contradicting hCons on the combined finite-list-in-M witness.
  --
  -- Mathematically standard; the ALCHOQ-side proof spans ~50 lines.
  -- We import the ALCHOQ result by coercing through `t.toAlchoq`:
  -- because M is SROIQ-consistent, it's ALCHOQ-consistent; the same
  -- Lindenbaum-maximality construction inside ALCHOQ yields the
  -- closure result for the ALCHOQ-side derivation.  But SROIQ-side
  -- maximality might be strictly stronger than ALCHOQ-side, so the
  -- coercion isn't immediate.  We perform the proof directly.
  have hSplit_C :
      SatC R O (conjList (L_C.filter (· ≠ C))) (.neg C) := by
    -- conjList L_C ⊑ ⊥ → conj C (conjList (L_C.filter (·≠C))) ⊑ ⊥
    --                 → conjList (L_C.filter (·≠C)) ⊑ ¬C
    have hSplitConj :
        SatC R O (.conj C (conjList (L_C.filter (· ≠ C)))) Concept.bot := by
      exact SatC.trans
        (SatC.ofAlchoq (ALCHOQ.satC_conj_filter_implies_list O C L_C))
        hLC_sat
    -- Apply: A ⊓ B ⊑ ⊥ ⇒ B ⊑ ¬A   (classical contrapositive).
    -- Proof:  B ⊑ B ⊓ (C ⊔ ¬C) (EM)
    --       = (B ⊓ C) ⊔ (B ⊓ ¬C) (dist)
    --       ⊑ ⊥ ⊔ ¬C            (by hSplitConj on left disjunct;
    --                            comm to get C ⊓ B form, etc.)
    --       ⊑ ¬C.
    -- Implement via SatC tactics.
    have hEM : SatC R O (conjList (L_C.filter (· ≠ C))) (.disj C (.neg C)) :=
      SatC.trans (satC_top R O _) (SatC.ofAlchoq (ALCHOQ.SatC.em C))
    have hConj :
        SatC R O (conjList (L_C.filter (· ≠ C)))
          (.conj (conjList (L_C.filter (· ≠ C))) (.disj C (.neg C))) :=
      SatC.satC_andI (satC_refl R O _) hEM
    have hDist :
        SatC R O
          (.conj (conjList (L_C.filter (· ≠ C))) (.disj C (.neg C)))
          (.disj (.conj (conjList (L_C.filter (· ≠ C))) C)
                 (.conj (conjList (L_C.filter (· ≠ C))) (.neg C))) :=
      SatC.ofAlchoq (ALCHOQ.SatC.dist _ C (.neg C))
    have hLeft :
        SatC R O (.conj (conjList (L_C.filter (· ≠ C))) C) (.neg C) := by
      -- conj X C ⊑ conj C X (comm) ⊑ ⊥ (hSplitConj) ⊑ ¬C (bot)
      refine SatC.trans
        (SatC.ofAlchoq (ALCHOQ.satC_conj_comm O _ C))
        (SatC.trans hSplitConj (satC_bot R O _))
    have hRight :
        SatC R O (.conj (conjList (L_C.filter (· ≠ C))) (.neg C)) (.neg C) :=
      satC_andR R O _ _
    exact SatC.trans hConj
      (SatC.trans hDist (SatC.satC_orE hLeft hRight))
  have hSplit_nC :
      SatC R O (conjList (L_nC.filter (· ≠ Concept.neg C))) C := by
    have hSplitConj :
        SatC R O
          (.conj (Concept.neg C) (conjList (L_nC.filter (· ≠ Concept.neg C))))
          Concept.bot :=
      SatC.trans
        (SatC.ofAlchoq (ALCHOQ.satC_conj_filter_implies_list O _ L_nC))
        hLnC_sat
    -- Symmetric reasoning: conj (¬C) X ⊑ ⊥ ⇒ X ⊑ ¬¬C ⊑ C.
    have hEM : SatC R O (conjList (L_nC.filter (· ≠ Concept.neg C)))
        (.disj C (.neg C)) :=
      SatC.trans (satC_top R O _) (SatC.ofAlchoq (ALCHOQ.SatC.em C))
    have hConj :
        SatC R O (conjList (L_nC.filter (· ≠ Concept.neg C)))
          (.conj (conjList (L_nC.filter (· ≠ Concept.neg C)))
                 (.disj C (.neg C))) :=
      SatC.satC_andI (satC_refl R O _) hEM
    have hDist :
        SatC R O
          (.conj (conjList (L_nC.filter (· ≠ Concept.neg C)))
                 (.disj C (.neg C)))
          (.disj (.conj (conjList (L_nC.filter (· ≠ Concept.neg C))) C)
                 (.conj (conjList (L_nC.filter (· ≠ Concept.neg C)))
                        (.neg C))) :=
      SatC.ofAlchoq (ALCHOQ.SatC.dist _ C (.neg C))
    have hLeft :
        SatC R O (.conj (conjList (L_nC.filter (· ≠ Concept.neg C))) C) C :=
      satC_andR R O _ _
    have hRight :
        SatC R O
          (.conj (conjList (L_nC.filter (· ≠ Concept.neg C))) (.neg C)) C := by
      refine SatC.trans
        (SatC.ofAlchoq (ALCHOQ.satC_conj_comm O _ (.neg C)))
        (SatC.trans hSplitConj (satC_bot R O _))
    exact SatC.trans hConj
      (SatC.trans hDist (SatC.satC_orE hLeft hRight))
  -- Combine to an inconsistency in M.
  let L := L_C.filter (· ≠ C) ++ L_nC.filter (· ≠ Concept.neg C)
  apply hCons L
  · intro E hE
    rcases List.mem_append.mp hE with hE1 | hE2
    · have hfilt := List.mem_filter.mp hE1
      rcases hLC_in E hfilt.1 with hEC | hEM
      · exact absurd hEC (by simpa using hfilt.2)
      · exact hEM
    · have hfilt := List.mem_filter.mp hE2
      rcases hLnC_in E hfilt.1 with hEnC | hEM
      · exact absurd hEnC (by simpa using hfilt.2)
      · exact hEM
  · -- conjList L ⊑ ⊥ via splits.
    show SatC R O (conjList L) Concept.bot
    have hSplit :
        SatC R O (conjList L)
          (.conj (conjList (L_C.filter (· ≠ C)))
                 (conjList (L_nC.filter (· ≠ Concept.neg C)))) :=
      SatC.ofAlchoq
        (ALCHOQ.satC_conjList_append_to_split O _ _)
    refine SatC.trans hSplit ?_
    refine SatC.trans ?_ (satC_nc R O C)
    apply SatC.satC_andI
    · exact SatC.trans (satC_andR R O _ _) hSplit_nC
    · exact SatC.trans (satC_andL R O _ _) hSplit_C

/-- **Lindenbaum lemma** (SROIQ): every SROIQ-consistent set extends
    to a SROIQ-type. -/
theorem lindenbaum (R : RBox) (O : Ontology) (Γ : Set Concept)
    (hΓ : consistent R O Γ) :
    ∃ t : Type_ R O, Γ ⊆ t.carrier := by
  obtain ⟨M, hΓM, hMcons, hMmax⟩ := lindenbaum_max R O Γ hΓ
  refine ⟨⟨M, hMcons, lindenbaum_max_closed R O M hMcons hMmax⟩, hΓM⟩

-- ============================================================
-- 6.  Counter-witness consistency: ¬ SatC R O C D → consistent R O {C, ¬D}.
-- ============================================================

/-- If `R, O ⊬ C ⊑ D`, then the set `{C, ¬D}` is SROIQ-consistent.

    Faithful transcription of `ALCHOQ.c_negD_consistent` to the
    SROIQ-side `SatC R O`, using the SROIQ-level `satC_andI` and
    `satC_orE` constructors plus lifted ALCHOQ rules. -/
theorem c_negD_consistent (R : RBox) (O : Ontology) (C D : Concept)
    (hNotSat : ¬ SatC R O C D) :
    consistent R O ({C, Concept.neg D} : Set Concept) := by
  intro L hLin hSat
  have aux :
      ∀ L' : List Concept,
        (∀ E ∈ L', E ∈ ({C, Concept.neg D} : Set Concept)) →
        SatC R O (.conj C (.neg D)) (conjList L') := by
    intro L'
    induction L' with
    | nil =>
        intro _
        unfold conjList ALCHOQ.conjList
        exact satC_top R O _
    | cons E Es ih =>
        intro hL'in
        unfold conjList ALCHOQ.conjList
        have hE_mem : E ∈ ({C, Concept.neg D} : Set Concept) :=
          hL'in E List.mem_cons_self
        rcases hE_mem with hEC | hEnegD
        · subst hEC
          refine SatC.satC_andI ?_ ?_
          · exact satC_andL R O _ _
          · exact ih (fun F hF => hL'in F (List.mem_cons_of_mem _ hF))
        · have hEeq : E = Concept.neg D := hEnegD
          subst hEeq
          refine SatC.satC_andI ?_ ?_
          · exact satC_andR R O _ _
          · exact ih (fun F hF => hL'in F (List.mem_cons_of_mem _ hF))
  have hCNeg : SatC R O (.conj C (.neg D)) (conjList L) := aux L hLin
  have hContra : SatC R O (.conj C (.neg D)) Concept.bot :=
    SatC.trans hCNeg hSat
  apply hNotSat
  -- C ⊑ C ⊓ (D ⊔ ¬D) ⊑ (C⊓D) ⊔ (C⊓¬D) ⊑ D.
  have step1 : SatC R O C (.conj C (.disj D (.neg D))) :=
    SatC.satC_andI (satC_refl R O C)
                   (SatC.trans (satC_top R O C)
                     (SatC.ofAlchoq (ALCHOQ.SatC.em D)))
  have step2 : SatC R O (.conj C (.disj D (.neg D))) D := by
    refine SatC.trans (SatC.ofAlchoq (ALCHOQ.SatC.dist C D (Concept.neg D))) ?_
    refine SatC.satC_orE ?_ ?_
    · exact satC_andR R O _ _
    · exact SatC.trans hContra (satC_bot R O D)
  exact SatC.trans step1 step2

-- ============================================================
-- 7.  Type non-emptiness.
-- ============================================================

/-- Non-emptiness of `Type_ R O`: provable from SROIQ-consistency of
    the empty set. -/
theorem type_nonempty_of_consistent (R : RBox) (O : Ontology)
    (hC : consistent R O (∅ : Set Concept)) :
    ∃ t : Type_ R O, True := by
  obtain ⟨t, _⟩ := lindenbaum R O ∅ hC
  exact ⟨t, trivial⟩

end SROIQ
end ELKSDD
