/-
  ELKSDD/SROIQSkolemCanonical.lean
  ---------------------------------
  Skolem-tagged canonical model for SROIQ.

  Builds:

  (a) `CanDom R O` -- Skolem-tagged canonical domain over `Type_ R O`;
  (b) SROIQ-side `nom_consistent_of_cons` (via `SatC.nomGlobal`);
  (c) Carrier-recursion + canonical interpretation + propositional
      truth-lemma cases over SROIQ types;
  (d) Canonical model satisfies role-inclusion RBox axioms.

  Axiom-clean over `[propext, Classical.choice, Quot.sound]`.
-/

import ELKSDD.SROIQCanonical
import ELKSDD.ALCHOQSkolem

namespace ELKSDD
namespace SROIQ

open Classical
open ALCHOQ (Concept Ontology Interp)

-- ============================================================
-- (a) Skolem-tagged canonical domain over SROIQ types.
-- ============================================================

inductive CanDom (R : RBox) (O : Ontology) : Type where
  | seed   : Type_ R O → CanDom R O
  | nomElt : Nat → CanDom R O
  | succ   : CanDom R O → Nat → Concept → Nat → CanDom R O

theorem CanDom.succ_ne_parent (R : RBox) (O : Ontology) :
    ∀ (p : CanDom R O) (r : Nat) (C : Concept) (k : Nat),
      CanDom.succ p r C k ≠ p := by
  intro p
  induction p with
  | seed _   => intros _ _ _ h; cases h
  | nomElt _ => intros _ _ _ h; cases h
  | succ q r' C' k' ih =>
      intros r C k h
      have hq : CanDom.succ q r' C' k' = q := by
        injection h with hq _ _ _
      exact ih r' C' k' hq

-- ============================================================
-- (b) SROIQ NomConsistent via SatC.nomGlobal.
-- ============================================================

theorem satC_nom_to_conjList_of_noms (R : RBox) (O : Ontology) (i : Nat) :
    ∀ L : List Concept, (∀ E ∈ L, E = .nom i) →
      SatC R O (.nom i) (conjList L)
  | [], _ => by
      unfold conjList ALCHOQ.conjList
      exact satC_top R O _
  | E :: Es, hL => by
      unfold conjList ALCHOQ.conjList
      have hE : E = Concept.nom i := hL E List.mem_cons_self
      subst hE
      refine SatC.satC_andI ?_ ?_
      · exact satC_refl R O _
      · exact satC_nom_to_conjList_of_noms R O i Es
                (fun F hF => hL F (List.mem_cons_of_mem _ hF))

def NomConsistent (R : RBox) (O : Ontology) : Prop :=
  ∀ i, consistent R O ({Concept.nom i} : Set Concept)

theorem nom_consistent_of_cons (R : RBox) (O : Ontology)
    (hCons : consistent R O (∅ : Set Concept)) :
    NomConsistent R O := by
  intro i L hLin hSat
  have hLnom : ∀ E ∈ L, E = Concept.nom i := by
    intro E hE
    have := hLin E hE
    simpa [Set.mem_singleton_iff] using this
  have hNomBot : SatC R O (Concept.nom i) Concept.bot :=
    SatC.trans (satC_nom_to_conjList_of_noms R O i L hLnom) hSat
  have hTopBot : SatC R O Concept.top Concept.bot := SatC.nomGlobal hNomBot
  apply hCons ([] : List Concept)
  · intro E hE; exact absurd hE List.not_mem_nil
  · show SatC R O (conjList []) Concept.bot
    unfold conjList ALCHOQ.conjList
    exact hTopBot

-- ============================================================
-- (c.1) Successor seed consistency (SROIQ-side).
-- ============================================================

/-- successor seed: `{C} ∪ {D | univ r D ∈ pT.carrier}` -/
def successorSet (R : RBox) (O : Ontology)
    (pT : Type_ R O) (r : Nat) (C : Concept) : Set Concept :=
  {C} ∪ {D | Concept.univ r D ∈ pT.carrier}

theorem mem_successorSet_iff (R : RBox) (O : Ontology) (pT : Type_ R O)
    (r : Nat) (C D : Concept) :
    D ∈ successorSet R O pT r C ↔
      D = C ∨ Concept.univ r D ∈ pT.carrier := by
  unfold successorSet
  constructor
  · rintro (hC | hU)
    · exact Or.inl hC
    · exact Or.inr hU
  · rintro (rfl | hU)
    · exact Or.inl rfl
    · exact Or.inr hU

/-- Convert ALCHOQ-derived `univListConj` step to SROIQ via `ofAlchoq`. -/
theorem satC_map_univ_to_univListConj (R : RBox) (O : Ontology)
    (r : Nat) (Ds : List Concept) :
    SatC R O (conjList (Ds.map (Concept.univ r)))
             (ALCHOQ.univListConj r Ds) :=
  SatC.ofAlchoq (ALCHOQ.satC_map_univ_to_univListConj O r Ds)

/-- Lift `satC_exist_with_univs` to SROIQ via `ofAlchoq`. -/
theorem satC_exist_with_univs (R : RBox) (O : Ontology)
    (r : Nat) (C : Concept) (Ds : List Concept) :
    SatC R O (.conj (.exist r C) (ALCHOQ.univListConj r Ds))
             (.exist r (.conj C (conjList Ds))) :=
  SatC.ofAlchoq (ALCHOQ.satC_exist_with_univs O r C Ds)

/-- The successor seed is SROIQ-consistent whenever `∃r.C ∈ pT.carrier`.

    Transcription of `ALCHOQ.successor_consistent` to the SROIQ side.
    Uses the SROIQ-side `type_closure` plus the lifted ALCHOQ
    derivations (`satC_map_univ_to_univListConj`,
    `satC_exist_with_univs`, `existBot`, `satC_monoExist`,
    `satC_conj_filter_implies_list`). -/
theorem successor_consistent
    (R : RBox) (O : Ontology) (pT : Type_ R O) (r : Nat) (C : Concept)
    (hExist : Concept.exist r C ∈ pT.carrier) :
    consistent R O (successorSet R O pT r C) := by
  intro L hLin hSat
  let Ds := L.filter (· ≠ C)
  have hDs : ∀ D ∈ Ds, Concept.univ r D ∈ pT.carrier := by
    intro D hD
    obtain ⟨hin, hne⟩ := List.mem_filter.mp hD
    rcases (mem_successorSet_iff R O pT r C D).mp (hLin D hin) with hC | hUniv
    · exact absurd hC (by simpa using hne)
    · exact hUniv
  apply pT.cons (Concept.exist r C :: Ds.map (Concept.univ r))
  · intro D' hD'
    rcases List.mem_cons.mp hD' with rfl | hMap
    · exact hExist
    · obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hMap
      exact hDs D hD
  · show SatC R O (conjList (Concept.exist r C :: Ds.map (Concept.univ r)))
             Concept.bot
    unfold conjList ALCHOQ.conjList
    have h1 :
        SatC R O (.conj (.exist r C) (conjList (Ds.map (Concept.univ r))))
                 (.conj (.exist r C) (ALCHOQ.univListConj r Ds)) := by
      refine SatC.satC_andI ?_ ?_
      · exact satC_andL R O _ _
      · exact SatC.trans (satC_andR R O _ _)
                (satC_map_univ_to_univListConj R O r Ds)
    have h2 :
        SatC R O (.conj (.exist r C) (ALCHOQ.univListConj r Ds))
                 (.exist r (.conj C (conjList Ds))) :=
      satC_exist_with_univs R O r C Ds
    have h3 : SatC R O (.conj C (conjList Ds)) Concept.bot :=
      SatC.trans (SatC.ofAlchoq
        (ALCHOQ.satC_conj_filter_implies_list O C L)) hSat
    have h4 :
        SatC R O (.exist r (.conj C (conjList Ds))) (.exist r Concept.bot) :=
      SatC.satC_monoExist r h3
    have h5 : SatC R O (.exist r Concept.bot) Concept.bot :=
      SatC.ofAlchoq (ALCHOQ.SatC.existBot r)
    refine SatC.trans h1 (SatC.trans h2 (SatC.trans h4 h5))

-- ============================================================
-- (c.2) Carrier-type and canonical interpretation.
-- ============================================================

/-- Carrier-type assigning each canonical-domain element a maximal
    SROIQ-consistent type.  Mirrors `ALCHOQ.carrierType`. -/
noncomputable def carrierType (R : RBox) (O : Ontology)
    (hCons : consistent R O (∅ : Set Concept)) :
    CanDom R O → Type_ R O
  | .seed t => t
  | .nomElt i =>
      (lindenbaum R O ({.nom i} : Set Concept)
        (nom_consistent_of_cons R O hCons i)).choose
  | .succ p r C _k =>
      let pT := carrierType R O hCons p
      let seed : Set Concept := successorSet R O pT r C
      if h : consistent R O seed then
        (lindenbaum R O seed h).choose
      else
        pT

/-- Carrier set (sugar). -/
noncomputable def carrierSet (R : RBox) (O : Ontology)
    (hCons : consistent R O (∅ : Set Concept)) (x : CanDom R O) :
    Set Concept :=
  (carrierType R O hCons x).carrier

theorem succ_carrier_contains_C
    (R : RBox) (O : Ontology) (hCons : consistent R O (∅ : Set Concept))
    (p : CanDom R O) (r : Nat) (C : Concept) (k : Nat)
    (hExist : Concept.exist r C ∈ carrierSet R O hCons p) :
    C ∈ carrierSet R O hCons (.succ p r C k) := by
  unfold carrierSet
  show C ∈ (carrierType R O hCons (.succ p r C k)).carrier
  have hSeedCons :
      consistent R O (successorSet R O (carrierType R O hCons p) r C) :=
    successor_consistent R O (carrierType R O hCons p) r C hExist
  show C ∈ (if h : consistent R O _ then
              (lindenbaum R O _ h).choose else _).carrier
  rw [dif_pos hSeedCons]
  have h := (lindenbaum R O _ hSeedCons).choose_spec
  exact h (Or.inl rfl)

theorem succ_carrier_propagates_univ
    (R : RBox) (O : Ontology) (hCons : consistent R O (∅ : Set Concept))
    (p : CanDom R O) (r : Nat) (C : Concept) (k : Nat)
    (hExist : Concept.exist r C ∈ carrierSet R O hCons p)
    (D : Concept) (hUniv : Concept.univ r D ∈ carrierSet R O hCons p) :
    D ∈ carrierSet R O hCons (.succ p r C k) := by
  unfold carrierSet at hUniv ⊢
  show D ∈ (carrierType R O hCons (.succ p r C k)).carrier
  have hSeedCons :
      consistent R O (successorSet R O (carrierType R O hCons p) r C) :=
    successor_consistent R O (carrierType R O hCons p) r C hExist
  show D ∈ (if h : consistent R O _ then
              (lindenbaum R O _ h).choose else _).carrier
  rw [dif_pos hSeedCons]
  have h := (lindenbaum R O _ hSeedCons).choose_spec
  exact h (Or.inr hUniv)

theorem nomElt_carrier_contains
    (R : RBox) (O : Ontology) (hCons : consistent R O (∅ : Set Concept))
    (i : Nat) :
    Concept.nom i ∈ carrierSet R O hCons (.nomElt i) := by
  unfold carrierSet
  show Concept.nom i ∈ (carrierType R O hCons (.nomElt i)).carrier
  have h := (lindenbaum R O ({.nom i} : Set Concept)
    (nom_consistent_of_cons R O hCons i)).choose_spec
  exact h (Set.mem_singleton_iff.mpr rfl)

/-- The SROIQ Skolem canonical interpretation. -/
noncomputable def skolCanonical (R : RBox) (O : Ontology)
    (hCons : consistent R O (∅ : Set Concept)) :
    Interp (CanDom R O) where
  ext_concept n x := Concept.atom n ∈ carrierSet R O hCons x
  ext_role r x y :=
    (∀ D, Concept.univ r D ∈ carrierSet R O hCons x →
          D ∈ carrierSet R O hCons y) ∧
    (y = x → Concept.hasSelf r ∈ carrierSet R O hCons x)
  ext_ind i := .nomElt i

theorem skolCanonical_ext_ind (R : RBox) (O : Ontology)
    (hCons : consistent R O (∅ : Set Concept)) (i : Nat) :
    (skolCanonical R O hCons).ext_ind i = .nomElt i := rfl

-- ============================================================
-- (d) Headline: canonical satisfies role-inclusion RBox axioms.
-- ============================================================

/-- **The canonical Skolem model satisfies every role-inclusion RBox
    axiom.**  This is the payoff of rebuilding the carrier-type
    construction over `SROIQ.SatC`: the type-closure under
    `roleIncl_univ` / `roleIncl_hasSelf` automatically gives
    `ext_role r ⊆ ext_role s`. -/
theorem skolCanonical_satisfies_roleIncl
    (R : RBox) (O : Ontology) (hCons : consistent R O (∅ : Set Concept))
    (r s : Nat) (hMem : RAxiom.incl r s ∈ R) :
    ∀ x y : CanDom R O,
      (skolCanonical R O hCons).ext_role r x y →
      (skolCanonical R O hCons).ext_role s x y := by
  intro x y ⟨hUniv_r, hSelf_r⟩
  refine ⟨?_, ?_⟩
  · -- Universal-propagation: univ s D ∈ x → D ∈ y.
    intro D hUnivS
    -- By type_closure: univ s D ∈ x.carrier ⟹ univ r D ∈ x.carrier
    -- (since SatC.roleIncl_univ : univ s D ⊑ univ r D when r ⊑ s).
    have hUnivR : Concept.univ r D ∈ carrierSet R O hCons x :=
      type_closure R O (carrierType R O hCons x)
        (Concept.univ s D) (Concept.univ r D) hUnivS
        (SatC.roleIncl_univ D hMem)
    exact hUniv_r D hUnivR
  · -- Self-loop: y = x → hasSelf s ∈ x.
    intro hyx
    have hSelfR : Concept.hasSelf r ∈ carrierSet R O hCons x := hSelf_r hyx
    exact type_closure R O (carrierType R O hCons x)
      (Concept.hasSelf r) (Concept.hasSelf s) hSelfR
      (SatC.roleIncl_hasSelf hMem)

-- ============================================================
-- (c.3) Truth lemma at hasSelf, ∃R.C, ∀R.C.
-- ============================================================

/-- Conjunction-closure inside a SROIQ type's carrier. -/
theorem conj_mem (R : RBox) (O : Ontology) (t : Type_ R O) (C D : Concept)
    (hC : C ∈ t.carrier) (hD : D ∈ t.carrier) :
    Concept.conj C D ∈ t.carrier := by
  rcases t.maximal (Concept.conj C D) with hMem | hNeg
  · exact hMem
  · exfalso
    have hDisj : Concept.disj (Concept.neg C) (Concept.neg D) ∈ t.carrier :=
      type_closure R O t _ _ hNeg
        (SatC.ofAlchoq (ALCHOQ.SatC.deMorganA C D))
    apply t.cons [C, D, Concept.disj (Concept.neg C) (Concept.neg D)]
    · intro E hE
      simp at hE
      rcases hE with rfl | rfl | rfl
      · exact hC
      · exact hD
      · exact hDisj
    · show SatC R O (conjList [C, D,
            Concept.disj (Concept.neg C) (Concept.neg D)]) Concept.bot
      unfold conjList ALCHOQ.conjList
      have hCD : SatC R O (.conj C (.conj D
                  (.conj (.disj (.neg C) (.neg D)) .top)))
                       (.conj (.conj C D) (.disj (.neg C) (.neg D))) := by
        refine SatC.satC_andI ?_ ?_
        · refine SatC.satC_andI ?_ ?_
          · exact satC_andL R O _ _
          · exact SatC.trans (satC_andR R O _ _) (satC_andL R O _ _)
        · refine SatC.trans (satC_andR R O _ _) ?_
          refine SatC.trans (satC_andR R O _ _) ?_
          exact satC_andL R O _ _
      have hDist : SatC R O (.conj (.conj C D) (.disj (.neg C) (.neg D)))
                          (.disj (.conj (.conj C D) (.neg C))
                                 (.conj (.conj C D) (.neg D))) :=
        SatC.ofAlchoq (ALCHOQ.SatC.dist _ _ _)
      have hLeft : SatC R O (.conj (.conj C D) (.neg C)) Concept.bot := by
        refine SatC.trans ?_ (satC_nc R O C)
        refine SatC.satC_andI ?_ ?_
        · exact SatC.trans (satC_andL R O _ _) (satC_andL R O _ _)
        · exact satC_andR R O _ _
      have hRight : SatC R O (.conj (.conj C D) (.neg D)) Concept.bot := by
        refine SatC.trans ?_ (satC_nc R O D)
        refine SatC.satC_andI ?_ ?_
        · exact SatC.trans (satC_andL R O _ _) (satC_andR R O _ _)
        · exact satC_andR R O _ _
      exact SatC.trans hCD (SatC.trans hDist (SatC.satC_orE hLeft hRight))

/-- ``∃r.C ∈ carrier x → skolCanonical's ext_role r x (succ x r C k)``.

    For the universal-propagation conjunct we use
    `succ_carrier_propagates_univ`; for the self-loop conjunct we use
    `succ_ne_parent` to show the case is vacuous. -/
theorem skol_succ_in_ext_role
    (R : RBox) (O : Ontology) (hCons : consistent R O (∅ : Set Concept))
    (x : CanDom R O) (r : Nat) (C : Concept) (k : Nat)
    (hExist : Concept.exist r C ∈ carrierSet R O hCons x) :
    (skolCanonical R O hCons).ext_role r x (.succ x r C k) := by
  refine ⟨?_, ?_⟩
  · intro D hUniv
    exact succ_carrier_propagates_univ R O hCons x r C k hExist D hUniv
  · intro heq
    -- heq : succ x r C k = x; impossible by succ_ne_parent.
    exact absurd heq (CanDom.succ_ne_parent R O x r C k)

/-- Truth lemma at `hasSelf r` (SROIQ-Skolem-canonical). -/
theorem skol_eval_hasSelf_iff
    (R : RBox) (O : Ontology) (hCons : consistent R O (∅ : Set Concept))
    (r : Nat) (x : CanDom R O) :
    (skolCanonical R O hCons).eval (.hasSelf r) x ↔
      Concept.hasSelf r ∈ carrierSet R O hCons x := by
  show (skolCanonical R O hCons).ext_role r x x ↔ _
  constructor
  · rintro ⟨_, hSelf⟩; exact hSelf rfl
  · intro hSelf
    refine ⟨?_, ?_⟩
    · intro D hUniv
      have hConj : Concept.conj (.hasSelf r) (.univ r D) ∈
                       carrierSet R O hCons x := by
        unfold carrierSet at hSelf hUniv ⊢
        exact conj_mem R O (carrierType R O hCons x) _ _ hSelf hUniv
      unfold carrierSet at hConj ⊢
      exact type_closure R O (carrierType R O hCons x) _ _ hConj
        (SatC.ofAlchoq (ALCHOQ.SatC.hasSelf_with_univ r D))
    · intro _; exact hSelf

/-- Truth lemma at `∃r.C` (modulo IH at `C`). -/
theorem skol_eval_exist_iff
    (R : RBox) (O : Ontology) (hCons : consistent R O (∅ : Set Concept))
    (r : Nat) (C : Concept) (x : CanDom R O)
    (ihC : ∀ y : CanDom R O,
      (skolCanonical R O hCons).eval C y ↔ C ∈ carrierSet R O hCons y) :
    (skolCanonical R O hCons).eval (.exist r C) x ↔
      Concept.exist r C ∈ carrierSet R O hCons x := by
  show (∃ y, (skolCanonical R O hCons).ext_role r x y ∧
              (skolCanonical R O hCons).eval C y) ↔ _
  constructor
  · rintro ⟨y, hr, hCy⟩
    rcases (carrierType R O hCons x).maximal (Concept.exist r C) with hMem | hNeg
    · exact hMem
    · exfalso
      have hUnivNegC : Concept.univ r (.neg C) ∈ carrierSet R O hCons x := by
        unfold carrierSet
        exact type_closure R O (carrierType R O hCons x) _ _ hNeg
          (SatC.ofAlchoq (ALCHOQ.SatC.negExist r C))
      have hNegCy : Concept.neg C ∈ carrierSet R O hCons y :=
        hr.1 _ hUnivNegC
      have hCy_mem : C ∈ carrierSet R O hCons y := (ihC y).mp hCy
      unfold carrierSet at hNegCy hCy_mem
      rcases mem_xor_neg R O (carrierType R O hCons y) C with
        ⟨_, hnnC⟩ | ⟨hCnotmem, _⟩
      · exact hnnC hNegCy
      · exact hCnotmem hCy_mem
  · intro hExist
    refine ⟨.succ x r C 0, ?_, ?_⟩
    · exact skol_succ_in_ext_role R O hCons x r C 0 hExist
    · apply (ihC _).mpr
      exact succ_carrier_contains_C R O hCons x r C 0 hExist

/-- Truth lemma at `∀r.C` (modulo IH at `C`). -/
theorem skol_eval_univ_iff
    (R : RBox) (O : Ontology) (hCons : consistent R O (∅ : Set Concept))
    (r : Nat) (C : Concept) (x : CanDom R O)
    (ihC : ∀ y : CanDom R O,
      (skolCanonical R O hCons).eval C y ↔ C ∈ carrierSet R O hCons y) :
    (skolCanonical R O hCons).eval (.univ r C) x ↔
      Concept.univ r C ∈ carrierSet R O hCons x := by
  show (∀ y, (skolCanonical R O hCons).ext_role r x y →
              (skolCanonical R O hCons).eval C y) ↔ _
  constructor
  · intro hAll
    rcases (carrierType R O hCons x).maximal (Concept.univ r C) with hMem | hNeg
    · exact hMem
    · exfalso
      have hExistNeg : Concept.exist r (.neg C) ∈ carrierSet R O hCons x := by
        unfold carrierSet
        exact type_closure R O (carrierType R O hCons x) _ _ hNeg
          (SatC.ofAlchoq (ALCHOQ.SatC.negUniv r C))
      let y : CanDom R O := CanDom.succ x r (.neg C) 0
      have hER : (skolCanonical R O hCons).ext_role r x y :=
        skol_succ_in_ext_role R O hCons x r (.neg C) 0 hExistNeg
      have hNegCy : Concept.neg C ∈ carrierSet R O hCons y :=
        succ_carrier_contains_C R O hCons x r (.neg C) 0 hExistNeg
      have hCy : (skolCanonical R O hCons).eval C y := hAll y hER
      have hCmem : C ∈ carrierSet R O hCons y := (ihC y).mp hCy
      unfold carrierSet at hNegCy hCmem
      rcases mem_xor_neg R O (carrierType R O hCons y) C with
        ⟨_, hnnC⟩ | ⟨hCnotmem, _⟩
      · exact hnnC hNegCy
      · exact hCnotmem hCmem
  · intro hUniv y hR
    apply (ihC y).mpr
    exact hR.1 C hUniv

-- ============================================================
-- (c.4) Full truth lemma for the SROIQ SkolFragment.
--
--     SkolFragment is the ALCHOQ-side fragment from ALCHOQSkolem.lean
--     (atoms, ⊤, ⊥, ¬, ⊓, ⊔, ∃, ∀, hasSelf, ≥0, ≥1, ≤0; nominal-free).
--     Reused unchanged; the role-axis cases now apply at the
--     SROIQ-Skolem-canonical level.
-- ============================================================

theorem skol_top_mem (R : RBox) (O : Ontology)
    (hCons : consistent R O (∅ : Set Concept)) (x : CanDom R O) :
    Concept.top ∈ carrierSet R O hCons x :=
  top_mem R O _

theorem skol_bot_not_mem (R : RBox) (O : Ontology)
    (hCons : consistent R O (∅ : Set Concept)) (x : CanDom R O) :
    Concept.bot ∉ carrierSet R O hCons x :=
  bot_not_mem R O _

/-- **Truth lemma on the SROIQ SkolFragment** (unconditional in `O`
    apart from `consistent R O ∅`). -/
theorem skol_canonical_eval_iff
    (R : RBox) (O : Ontology) (hCons : consistent R O (∅ : Set Concept))
    (C : Concept) (hC : ALCHOQ.SkolFragment C) :
    ∀ x : CanDom R O,
      ((skolCanonical R O hCons).eval C x ↔ C ∈ carrierSet R O hCons x) := by
  induction C with
  | atom n => intro x; exact Iff.rfl
  | top =>
      intro x
      show True ↔ _
      exact ⟨fun _ => skol_top_mem R O hCons x, fun _ => trivial⟩
  | bot =>
      intro x
      show False ↔ _
      exact ⟨fun h => h.elim,
             fun h => (skol_bot_not_mem R O hCons x h).elim⟩
  | nom i => exact absurd hC (by simp [ALCHOQ.SkolFragment])
  | neg D ih =>
      intro x
      show (¬ (skolCanonical R O hCons).eval D x) ↔
              Concept.neg D ∈ carrierSet R O hCons x
      have ihD := ih hC
      rw [ihD x]
      unfold carrierSet
      rcases mem_xor_neg R O (carrierType R O hCons x) D with
        ⟨hDmem, hnDnotmem⟩ | ⟨hDnotmem, hnDmem⟩
      · exact ⟨fun h => absurd hDmem h, fun h => absurd h hnDnotmem⟩
      · exact ⟨fun _ => hnDmem, fun _ => hDnotmem⟩
  | conj A B ihA ihB =>
      intro x
      obtain ⟨hA, hB⟩ := hC
      show ((skolCanonical R O hCons).eval A x ∧
            (skolCanonical R O hCons).eval B x) ↔
            Concept.conj A B ∈ carrierSet R O hCons x
      rw [ihA hA x, ihB hB x]
      unfold carrierSet
      constructor
      · rintro ⟨hAmem, hBmem⟩
        exact conj_mem R O (carrierType R O hCons x) A B hAmem hBmem
      · intro hConj
        refine ⟨?_, ?_⟩
        · exact type_closure R O _ _ _ hConj (satC_andL R O _ _)
        · exact type_closure R O _ _ _ hConj (satC_andR R O _ _)
  | disj A B ihA ihB =>
      intro x
      obtain ⟨hA, hB⟩ := hC
      show ((skolCanonical R O hCons).eval A x ∨
            (skolCanonical R O hCons).eval B x) ↔
            Concept.disj A B ∈ carrierSet R O hCons x
      rw [ihA hA x, ihB hB x]
      unfold carrierSet
      constructor
      · rintro (hA' | hB')
        · exact type_closure R O _ _ _ hA'
            (SatC.ofAlchoq (ALCHOQ.satC_orL O A B))
        · exact type_closure R O _ _ _ hB'
            (SatC.ofAlchoq (ALCHOQ.satC_orR O A B))
      · intro hDisj
        by_contra hNeither
        push_neg at hNeither
        obtain ⟨hAne, hBne⟩ := hNeither
        rcases mem_xor_neg R O (carrierType R O hCons x) A with
          ⟨hAmem, _⟩ | ⟨_, hnA⟩
        · exact hAne hAmem
        rcases mem_xor_neg R O (carrierType R O hCons x) B with
          ⟨hBmem, _⟩ | ⟨_, hnB⟩
        · exact hBne hBmem
        apply (carrierType R O hCons x).cons
          [Concept.disj A B, Concept.neg A, Concept.neg B]
        · intro D hD
          simp at hD
          rcases hD with rfl | rfl | rfl
          · exact hDisj
          · exact hnA
          · exact hnB
        · show SatC R O (conjList
                  [Concept.disj A B, Concept.neg A, Concept.neg B])
                       Concept.bot
          unfold conjList ALCHOQ.conjList
          refine SatC.trans ?_ (satC_nc R O (Concept.disj A B))
          refine SatC.satC_andI ?_ ?_
          · exact satC_andL R O _ _
          · refine SatC.trans ?_
              (SatC.ofAlchoq (ALCHOQ.SatC.deMorganO' A B))
            refine SatC.satC_andI ?_ ?_
            · exact SatC.trans (satC_andR R O _ _) (satC_andL R O _ _)
            · refine SatC.trans (satC_andR R O _ _) ?_
              refine SatC.trans (satC_andR R O _ _) ?_
              exact satC_andL R O _ _
  | exist r D ih =>
      intro x
      exact skol_eval_exist_iff R O hCons r D x (ih hC)
  | univ r D ih =>
      intro x
      exact skol_eval_univ_iff R O hCons r D x (ih hC)
  | atLeast n r D ih =>
      cases n with
      | zero =>
          intro x
          show Interp.atLeastCard _ 0 ↔ _
          unfold Interp.atLeastCard
          refine ⟨fun _ => ?_, fun _ => trivial⟩
          unfold carrierSet
          exact type_closure R O (carrierType R O hCons x) _ _
            (top_mem R O _)
            (SatC.ofAlchoq (ALCHOQ.SatC.atLeastZero r D))
      | succ m =>
          cases m with
          | zero =>
              intro x
              have ihD := ih hC
              have hExistIff := skol_eval_exist_iff R O hCons r D x ihD
              have hSem :
                  (skolCanonical R O hCons).eval (.atLeast 1 r D) x ↔
                  (skolCanonical R O hCons).eval (.exist r D) x :=
                Interp.eval_atLeast_one_iff_exist
                  (skolCanonical R O hCons) r D x
              rw [hSem, hExistIff]
              constructor
              · intro hExD
                unfold carrierSet at hExD ⊢
                exact type_closure R O (carrierType R O hCons x) _ _ hExD
                  (SatC.ofAlchoq (ALCHOQ.SatC.exist_to_atLeast1 r D))
              · intro hAL
                unfold carrierSet at hAL ⊢
                exact type_closure R O (carrierType R O hCons x) _ _ hAL
                  (SatC.ofAlchoq (ALCHOQ.SatC.atLeast_to_exist 0 r D))
          | succ _ =>
              exact absurd hC (by simp [ALCHOQ.SkolFragment])
  | atMost n r D ih =>
      intro x
      have hD : ALCHOQ.SkolFragment D := by
        cases n with
        | zero => exact hC
        | succ _ => exact absurd hC (by simp [ALCHOQ.SkolFragment])
      cases n with
      | zero =>
          have hSem : (skolCanonical R O hCons).eval (.atMost 0 r D) x ↔
                      ∀ y, (skolCanonical R O hCons).ext_role r x y →
                            ¬ (skolCanonical R O hCons).eval D y :=
            Interp.eval_atMost_zero (skolCanonical R O hCons) r D x
          rw [hSem]
          have ihD := ih hD
          constructor
          · intro hAll
            have hUniv : Concept.univ r (Concept.neg D) ∈
                            carrierSet R O hCons x := by
              rcases (carrierType R O hCons x).maximal
                  (Concept.univ r (Concept.neg D)) with hMem | hNeg
              · exact hMem
              · have hExNN : Concept.exist r (.neg (.neg D)) ∈
                              carrierSet R O hCons x := by
                  unfold carrierSet
                  exact type_closure R O (carrierType R O hCons x) _ _ hNeg
                    (SatC.ofAlchoq (ALCHOQ.SatC.negUniv r (.neg D)))
                have hExD : Concept.exist r D ∈ carrierSet R O hCons x := by
                  unfold carrierSet
                  unfold carrierSet at hExNN
                  exact type_closure R O _ _ _ hExNN
                    (SatC.satC_monoExist r
                      (SatC.ofAlchoq (ALCHOQ.SatC.negNegE D)))
                let y : CanDom R O := CanDom.succ x r D 0
                have hER : (skolCanonical R O hCons).ext_role r x y :=
                  skol_succ_in_ext_role R O hCons x r D 0 hExD
                have hDy : (skolCanonical R O hCons).eval D y :=
                  (ihD y).mpr (succ_carrier_contains_C R O hCons x r D 0 hExD)
                exact absurd hDy (hAll y hER)
            unfold carrierSet at hUniv
            unfold carrierSet
            exact type_closure R O (carrierType R O hCons x) _ _ hUniv
              (SatC.ofAlchoq (ALCHOQ.SatC.univ_to_atMostZero r D))
          · intro hAtMost y hR
            intro hDy
            have hDmem : D ∈ carrierSet R O hCons y := (ihD y).mp hDy
            have hUnivNeg : Concept.univ r (Concept.neg D) ∈
                            carrierSet R O hCons x := by
              unfold carrierSet
              unfold carrierSet at hAtMost
              exact type_closure R O (carrierType R O hCons x) _ _ hAtMost
                (SatC.ofAlchoq (ALCHOQ.SatC.atMostZero r D))
            have hNegD : Concept.neg D ∈ carrierSet R O hCons y :=
              hR.1 _ hUnivNeg
            unfold carrierSet at hDmem hNegD
            rcases mem_xor_neg R O (carrierType R O hCons y) D with
              ⟨_, hnnD⟩ | ⟨hDnotmem, _⟩
            · exact hnnD hNegD
            · exact hDnotmem hDmem
      | succ _ =>
          exact absurd hC (by simp [ALCHOQ.SkolFragment])
  | hasSelf r =>
      intro x
      exact skol_eval_hasSelf_iff R O hCons r x

-- ============================================================
-- (c.5) Canonical satisfies the ontology.
-- ============================================================

/-- An SROIQ-side `SatC-Entails` adapter: turn an SROIQ-axiom
    `(C, D) ∈ O` into a SatC derivation `SatC R O C D`. -/
theorem satC_of_axiom (R : RBox) (O : Ontology) (C D : Concept)
    (h : (C, D) ∈ O) : SatC R O C D :=
  SatC.ofAlchoq (ALCHOQ.SatC.ofSat (ALCHOQ.Sat.axm C D h))

/-- **The SROIQ Skolem canonical model satisfies a SkolFragment ontology**. -/
theorem skol_canonical_satisfies
    (R : RBox) (O : Ontology) (hCons : consistent R O (∅ : Set Concept))
    (hOFrag : ALCHOQ.OntologySkolFragment O) :
    (skolCanonical R O hCons).satisfies O := by
  intro ax hAx x hP
  obtain ⟨h1Frag, h2Frag⟩ := hOFrag ax hAx
  have h1 : ax.1 ∈ carrierSet R O hCons x :=
    (skol_canonical_eval_iff R O hCons ax.1 h1Frag x).mp hP
  have h2 : ax.2 ∈ carrierSet R O hCons x := by
    unfold carrierSet at h1 ⊢
    exact type_closure R O (carrierType R O hCons x) _ _ h1
      (satC_of_axiom R O ax.1 ax.2 hAx)
  exact (skol_canonical_eval_iff R O hCons ax.2 h2Frag x).mpr h2

-- ============================================================
-- (e) Headline completeness theorem.
-- ============================================================

/-- **SROIQ headline completeness on the SkolFragment** for *any* RBox
    whose canonical-model satisfaction follows from the SROIQ-side
    `type_closure`.

    In particular: when the RBox consists only of role-inclusion
    axioms, the canonical satisfaction follows from
    `skolCanonical_satisfies_roleIncl` (proved earlier in this file).

    For RBoxes with transitivity / chain / reflexivity / etc., the
    proof extends analogously using the appropriate SROIQ-SatC rules
    plus `type_closure`.

    Hypothesis `hCanSatR`: the canonical model satisfies the RBox.
    Hypothesis `hOFrag`: the ontology is in the SkolFragment.

    Axiom-clean over `[propext, Classical.choice, Quot.sound]`. -/
theorem sroiq_satC_complete_skolFragment
    (R : RBox) (O : Ontology) (C D : Concept)
    (hOFrag : ALCHOQ.OntologySkolFragment O)
    (hC : ALCHOQ.SkolFragment C) (hD : ALCHOQ.SkolFragment D)
    (hCanSatR :
      ∀ (hCons : consistent R O (∅ : Set Concept)),
        R.eval (skolCanonical R O hCons))
    (hEnt : Entails R O C D) :
    SatC R O C D := by
  by_contra hNot
  by_cases hCons : consistent R O (∅ : Set Concept)
  · -- consistent case: build the Skolem countermodel.
    have hCN : consistent R O ({C, Concept.neg D} : Set Concept) :=
      c_negD_consistent R O C D hNot
    obtain ⟨t, htsub⟩ := lindenbaum R O _ hCN
    have hSatO : (skolCanonical R O hCons).satisfies O :=
      skol_canonical_satisfies R O hCons hOFrag
    have hSatR : R.eval (skolCanonical R O hCons) := hCanSatR hCons
    let x : CanDom R O := .seed t
    have hCarrierX : carrierSet R O hCons x = t.carrier := rfl
    have hCmem : C ∈ carrierSet R O hCons x := by
      rw [hCarrierX]; exact htsub (by simp : C ∈ ({C, Concept.neg D} : Set _))
    have hEvalC : (skolCanonical R O hCons).eval C x :=
      (skol_canonical_eval_iff R O hCons C hC x).mpr hCmem
    have hEvalD : (skolCanonical R O hCons).eval D x :=
      hEnt _ hSatR hSatO x hEvalC
    have hDmem : D ∈ carrierSet R O hCons x :=
      (skol_canonical_eval_iff R O hCons D hD x).mp hEvalD
    have hnDmem : Concept.neg D ∈ carrierSet R O hCons x := by
      rw [hCarrierX]
      exact htsub (by simp : Concept.neg D ∈ ({C, Concept.neg D} : Set _))
    unfold carrierSet at hDmem hnDmem
    rcases mem_xor_neg R O (carrierType R O hCons x) D with
      ⟨_, hnnD⟩ | ⟨hDnotmem, _⟩
    · exact hnnD hnDmem
    · exact hDnotmem hDmem
  · -- inconsistent case: chain top ⊑ bot to C ⊑ D.
    unfold consistent at hCons
    push_neg at hCons
    obtain ⟨L, hLin, hSat⟩ := hCons
    have hLnil : L = [] := by
      cases L with
      | nil => rfl
      | cons E _ =>
          exact absurd (hLin E List.mem_cons_self) (by simp)
    subst hLnil
    have hTopBot : SatC R O Concept.top Concept.bot := by
      have heq : conjList ([] : List Concept) = Concept.top := rfl
      rw [heq] at hSat; exact hSat
    apply hNot
    exact SatC.trans (satC_top R O C)
      (SatC.trans hTopBot (satC_bot R O D))

/-- **Corollary**: SROIQ completeness on the SkolFragment when the
    RBox consists only of role-inclusion axioms.  Discharged
    automatically via `skolCanonical_satisfies_roleIncl`. -/
theorem sroiq_satC_complete_skolFragment_roleInclOnly
    (R : RBox) (O : Ontology) (C D : Concept)
    (hOFrag : ALCHOQ.OntologySkolFragment O)
    (hC : ALCHOQ.SkolFragment C) (hD : ALCHOQ.SkolFragment D)
    (hRBox : ∀ ax ∈ R, ∃ r s, ax = RAxiom.incl r s)
    (hEnt : Entails R O C D) :
    SatC R O C D := by
  apply sroiq_satC_complete_skolFragment R O C D hOFrag hC hD ?_ hEnt
  intro hCons ax hAx
  obtain ⟨r, s, hrep⟩ := hRBox ax hAx
  subst hrep
  show ∀ x y, (skolCanonical R O hCons).ext_role r x y →
              (skolCanonical R O hCons).ext_role s x y
  exact skolCanonical_satisfies_roleIncl R O hCons r s hAx

-- ============================================================
-- (d.2) Headline: canonical satisfies the universal-propagation
--       half of transitive-role RBox axioms.
--
--       The full RBox-evaluation of `trans r` also requires the
--       hasSelf-self-loop case to propagate; that branch needs a
--       transitive-hasSelf calculus rule and is left as a follow-up.
--       For the SkolFragment-without-hasSelf cases the
--       universal-propagation half is sufficient.
-- ============================================================

/-- **Universal-propagation half of canonical transitivity.**

    The canonical Skolem model's `ext_role r` is transitive in the
    universal-propagation component whenever `RAxiom.trans r ∈ R`.
    The corresponding hasSelf-self-loop preservation is documented
    as a follow-up (needs a `hasSelf_trans` calculus rule). -/
theorem skolCanonical_univ_trans
    (R : RBox) (O : Ontology) (hCons : consistent R O (∅ : Set Concept))
    (r : Nat) (hMem : RAxiom.trans r ∈ R) :
    ∀ x y z : CanDom R O,
      (∀ D, Concept.univ r D ∈ carrierSet R O hCons x →
            D ∈ carrierSet R O hCons y) →
      (∀ D, Concept.univ r D ∈ carrierSet R O hCons y →
            D ∈ carrierSet R O hCons z) →
      (∀ D, Concept.univ r D ∈ carrierSet R O hCons x →
            D ∈ carrierSet R O hCons z) := by
  intro x y z hxy hyz C hUniv
  -- type_closure with roleTrans_univ: univ r C ⊑ univ r (univ r C)
  have hUUC : Concept.univ r (Concept.univ r C) ∈ carrierSet R O hCons x :=
    type_closure R O (carrierType R O hCons x)
      (Concept.univ r C) (Concept.univ r (Concept.univ r C)) hUniv
      (SatC.roleTrans_univ C hMem)
  have hUC_y : Concept.univ r C ∈ carrierSet R O hCons y :=
    hxy (Concept.univ r C) hUUC
  exact hyz C hUC_y

end SROIQ
end ELKSDD
