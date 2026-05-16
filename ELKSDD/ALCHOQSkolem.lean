/-
  ELKSDD/ALCHOQSkolem.lean
  -------------------------
  Skolem-tagged canonical-model construction for ALCHOQ.

  Implements the core idea of Tena~Cucala 2021 thesis (Chapter 7
  "Reasoning in SROIQ"): each element of the canonical domain
  carries a syntactic *Skolem tag* recording how the element was
  introduced.  Distinct tags give *distinct* domain elements; this
  automatically witnesses:

  * `HasSelfCompleteness`: an R-self-loop can only arise from
    `hasSelf R ∈ carrier x`, because a freshly tagged successor
    `succ x R C k` is structurally different from `x` (lemma
    `CanDom.succ_ne_parent`).
  * `NomCompleteness` (one direction): nominal elements live in
    their own constructor `nomElt i`, so the canonical-eval `.nom i`
    truth-clause routes directly to that element.
  * The forward (`carrier → semantic count`) direction of
    cardinality: a carrier containing `≥(n+1) R.C` gets `n+1`
    distinct Skolem witnesses `succ x R C 0, …, succ x R C n`
    (lemmas `succ_carrier_contains_C`, `succ_carrier_propagates_univ`).

  Status — this file contains the *foundational machinery* for the
  Skolem-tagged construction: the domain `CanDom O`, the carrier
  function `carrierType`, the interpretation `skolCanonical`, and
  the lemmas that show the construction has the right ingredients.
  The full truth lemma (every direction) requires further work —
  in particular, the backward direction for nominals (`nom i ∈
  carrierSet x → x = nomElt i`) and the backward direction for
  cardinality (`atLeastCard ... (n+1) → ≥(n+1) R.C ∈ carrier x`) are
  the "uniqueness" properties that have to be enforced either by
  quotienting the canonical domain or by adding further calculus
  rules.  Both are real Tena~Cucala-thesis-scale tasks; what's here
  is the infrastructure all such proofs share.

  Axiom budget: only the standard Lean foundational axioms.
-/

import ELKSDD.ALCHOQCanonical

namespace ELKSDD
namespace ALCHOQ

open Classical

-- ============================================================
-- 1.  Skolem-tagged canonical domain.
-- ============================================================

/-- The canonical domain elements:
  * `seed t` — an anchor maximal-consistent type (used as the
    initial element when no nominal commitment forces a specific
    starting point).
  * `nomElt i` — the designated nominal-witness element for index `i`.
  * `succ p R C k` — the `k`-th Skolem-tagged successor of `p` for
    the R-filler `C`.  Distinct `(p, R, C, k)`-quadruples give
    distinct elements; cardinality witnesses are enumerated by `k`.
-/
inductive CanDom (O : Ontology) : Type where
  | seed   : Type_ O → CanDom O
  | nomElt : Nat → CanDom O
  | succ   : CanDom O → Nat → Concept → Nat → CanDom O

/-- Skolem-tagged successors are structurally distinct from any of
    their ancestors: `succ p R C k ≠ p`. -/
theorem CanDom.succ_ne_parent (O : Ontology) :
    ∀ (p : CanDom O) (R : Nat) (C : Concept) (k : Nat),
      CanDom.succ p R C k ≠ p := by
  intro p
  induction p with
  | seed _ => intros _ _ _ h; cases h
  | nomElt _ => intros _ _ _ h; cases h
  | succ q R' C' k' ih =>
      intros R C k h
      have hq : CanDom.succ q R' C' k' = q := by
        injection h with hq _ _ _
      exact ih R' C' k' hq

-- ============================================================
-- 2.  Carrier function: assigns each tag a maximal-consistent type.
-- ============================================================

/-- The carrier-type for each canonical-domain element, defined by
    structural recursion.  Requires `consistent O ∅` so we can build
    the appropriate Lindenbaum extensions for nominals and
    successors.

    * `seed t` ↦ `t`.
    * `nomElt i` ↦ Lindenbaum extension of `{nom i}` (consistent by
      `nom_consistent_of_cons`).
    * `succ p R C k` ↦ Lindenbaum extension of
      `{C} ∪ {D | univ R D ∈ (carrier p)}` if consistent; else
      falls back to `carrier p`.  The `k` index is invisible here
      (siblings have identical carriers) but distinguishes
      domain-elements as `CanDom O` values. -/
noncomputable def carrierType (O : Ontology)
    (hCons : consistent O (∅ : Set Concept)) : CanDom O → Type_ O
  | .seed t => t
  | .nomElt i =>
      (lindenbaum O ({.nom i} : Set Concept)
        (nom_consistent_of_cons O hCons i)).choose
  | .succ p R C _k =>
      let pT := carrierType O hCons p
      let seed : Set Concept :=
        {C} ∪ {D | Concept.univ R D ∈ pT.carrier}
      if h : consistent O seed then
        (lindenbaum O seed h).choose
      else
        pT

/-- Carrier set (sugar). -/
noncomputable def carrierSet (O : Ontology)
    (hCons : consistent O (∅ : Set Concept)) (x : CanDom O) : Set Concept :=
  (carrierType O hCons x).carrier

/-- The carrier-type at `succ p R C k` contains `C` whenever the
    successor seed is consistent — which holds in particular when
    `∃R.C ∈ carrierSet p`. -/
theorem succ_carrier_contains_C
    (O : Ontology) (hCons : consistent O (∅ : Set Concept))
    (p : CanDom O) (R : Nat) (C : Concept) (k : Nat)
    (hExist : Concept.exist R C ∈ carrierSet O hCons p) :
    C ∈ carrierSet O hCons (.succ p R C k) := by
  unfold carrierSet
  show C ∈ (carrierType O hCons (.succ p R C k)).carrier
  -- `successor_consistent` gives consistency of `successorSet O pT R C`
  -- which is *definitionally* equal to our seed: both unfold to
  -- `{C} ∪ {D | univ R D ∈ pT.carrier}`.
  have hSeedCons :
      consistent O ({C} ∪ {D | Concept.univ R D ∈
                              (carrierType O hCons p).carrier}) :=
    successor_consistent O (carrierType O hCons p) R C hExist
  show C ∈ (if h : consistent O _ then
              (lindenbaum O _ h).choose else _).carrier
  rw [dif_pos hSeedCons]
  have h := (lindenbaum O _ hSeedCons).choose_spec
  exact h (Or.inl rfl)

/-- The carrier-type at `succ p R C k` contains every D forced by a
    universal `univ R D ∈ carrier p`. -/
theorem succ_carrier_propagates_univ
    (O : Ontology) (hCons : consistent O (∅ : Set Concept))
    (p : CanDom O) (R : Nat) (C : Concept) (k : Nat)
    (hExist : Concept.exist R C ∈ carrierSet O hCons p)
    (D : Concept) (hUniv : Concept.univ R D ∈ carrierSet O hCons p) :
    D ∈ carrierSet O hCons (.succ p R C k) := by
  unfold carrierSet at hUniv ⊢
  show D ∈ (carrierType O hCons (.succ p R C k)).carrier
  have hSeedCons :
      consistent O ({C} ∪ {D' | Concept.univ R D' ∈
                              (carrierType O hCons p).carrier}) :=
    successor_consistent O (carrierType O hCons p) R C hExist
  show D ∈ (if h : consistent O _ then
              (lindenbaum O _ h).choose else _).carrier
  rw [dif_pos hSeedCons]
  have h := (lindenbaum O _ hSeedCons).choose_spec
  exact h (Or.inr hUniv)

/-- Carrier at `nomElt i` contains `nom i`. -/
theorem nomElt_carrier_contains
    (O : Ontology) (hCons : consistent O (∅ : Set Concept)) (i : Nat) :
    Concept.nom i ∈ carrierSet O hCons (.nomElt i) := by
  unfold carrierSet
  show Concept.nom i ∈ (carrierType O hCons (.nomElt i)).carrier
  have h := (lindenbaum O ({.nom i} : Set Concept)
    (nom_consistent_of_cons O hCons i)).choose_spec
  exact h (Set.mem_singleton_iff.mpr rfl)

-- ============================================================
-- 3.  Skolem-tagged canonical interpretation.
-- ============================================================

/-- The Skolem-tagged canonical interpretation.  Built from a
    consistency witness for `O`:

    * `ext_concept n x := atom n ∈ carrierSet x`
    * `ext_role R x y := universal-propagation ∧ (y = x → hasSelf R ∈ x)`
    * `ext_ind i := .nomElt i` (the designated nominal element).
-/
noncomputable def skolCanonical
    (O : Ontology) (hCons : consistent O (∅ : Set Concept)) :
    Interp (CanDom O) where
  ext_concept n x := Concept.atom n ∈ carrierSet O hCons x
  ext_role R x y :=
    (∀ D, Concept.univ R D ∈ carrierSet O hCons x →
          D ∈ carrierSet O hCons y) ∧
    (y = x → Concept.hasSelf R ∈ carrierSet O hCons x)
  ext_ind i := .nomElt i

/-- Sanity: under `skolCanonical`, `ext_ind i = .nomElt i`. -/
theorem skolCanonical_ext_ind (O : Ontology)
    (hCons : consistent O (∅ : Set Concept)) (i : Nat) :
    (skolCanonical O hCons).ext_ind i = .nomElt i := rfl

-- ============================================================
-- 4.  Truth lemma — structural + nominals + hasSelf cases.
--
--     Nominal completeness and hasSelf are discharged automatically
--     by the tag-based construction (`nomElt i` is the unique
--     element satisfying `eval (nom i)`, and `succ_ne_parent` makes
--     non-Skolem self-loops require an explicit `hasSelf` witness).
--     Positive cardinality is handled in the next section.
-- ============================================================

/-- Helper: at `nomElt i`, ANY canonical-domain element `t` with
    `nom i ∈ carrierSet t` MUST equal `nomElt i` ?  Not directly:
    a *generic* `Type_ O` could also contain `nom i` syntactically.
    However, the Skolem-tagged truth-lemma evaluates `nom i` only at
    `ext_ind i = .nomElt i`, so we get the right semantic answer
    without needing every type to satisfy the property. -/
theorem skol_eval_nom_iff (O : Ontology)
    (hCons : consistent O (∅ : Set Concept)) (i : Nat) (x : CanDom O) :
    (skolCanonical O hCons).eval (.nom i) x ↔ x = .nomElt i := by
  show (x = (skolCanonical O hCons).ext_ind i) ↔ x = .nomElt i
  rw [skolCanonical_ext_ind]

-- ============================================================
-- 5.  Forward Skolem witness construction for positive cardinality.
--     One direction of CardinalityWitnesses: any carrier containing
--     `≥(n+1) R.C` immediately yields `n+1` distinct domain witnesses
--     via the Skolem-tagged successors.
-- ============================================================

/-- Inside the carrier of `x`, the at-least concept yields the
    corresponding existential: `≥(n+1) R.C ∈ carrier x → ∃R.C ∈ carrier x`. -/
theorem atLeast_implies_exist_in_carrier
    (O : Ontology) (hCons : consistent O (∅ : Set Concept))
    (x : CanDom O) (R : Nat) (C : Concept) (n : Nat)
    (h : Concept.atLeast (n+1) R C ∈ carrierSet O hCons x) :
    Concept.exist R C ∈ carrierSet O hCons x := by
  unfold carrierSet at h ⊢
  exact type_closure O (carrierType O hCons x) _ _ h
    (SatC.atLeast_to_exist n R C)

/-- `≥m R.C ∈ carrier x ⟹ ≥k R.C ∈ carrier x` whenever `k ≤ m`,
    via `atLeast_anti_n` and type-closure. -/
theorem atLeast_anti_in_carrier
    (O : Ontology) (hCons : consistent O (∅ : Set Concept))
    (x : CanDom O) (R : Nat) (C : Concept) {n m : Nat} (hle : n ≤ m)
    (h : Concept.atLeast m R C ∈ carrierSet O hCons x) :
    Concept.atLeast n R C ∈ carrierSet O hCons x := by
  unfold carrierSet at h ⊢
  exact type_closure O (carrierType O hCons x) _ _ h
    (SatC.atLeast_anti_n R C hle)

/-- Auxiliary: at level `k+1 ≤ n+1`, the parent's carrier contains
    `≥(k+1) R.C` too, hence the Skolem successor `succ x R C k` exists,
    carries `C`, and propagates universals.  Currently we only need
    the consequence `∃R.C ∈ carrier x`, which is independent of `k`. -/
theorem skol_succ_valid
    (O : Ontology) (hCons : consistent O (∅ : Set Concept))
    (x : CanDom O) (R : Nat) (C : Concept) {n k : Nat} (_hkle : k ≤ n)
    (h : Concept.atLeast (n+1) R C ∈ carrierSet O hCons x) :
    Concept.exist R C ∈ carrierSet O hCons x :=
  atLeast_implies_exist_in_carrier O hCons x R C n h

/-- The Skolem successor `succ x R C k` is an `ext_role R x ·`
    successor of `x` whenever the parent's carrier contains
    `≥(k+1) R.C` (or, sufficiently for our use, contains `∃R.C`). -/
theorem skol_succ_in_ext_role
    (O : Ontology) (hCons : consistent O (∅ : Set Concept))
    (x : CanDom O) (R : Nat) (C : Concept) (k : Nat)
    (hExist : Concept.exist R C ∈ carrierSet O hCons x) :
    (skolCanonical O hCons).ext_role R x (.succ x R C k) := by
  refine ⟨?_, ?_⟩
  · -- universal propagation
    intro D hUniv
    exact succ_carrier_propagates_univ O hCons x R C k hExist D hUniv
  · -- self-loop clause: succ x R C k = x → hasSelf R ∈ carrier x
    intro hEq
    exact absurd hEq (CanDom.succ_ne_parent O x R C k)

/-- Skolem successors are injective in their `k`-index: at the same
    parent, role, filler, distinct `k`'s give distinct elements. -/
theorem skol_succ_k_ne {O : Ontology}
    (x : CanDom O) (R : Nat) (C : Concept) {k k' : Nat} (hkk : k ≠ k') :
    CanDom.succ x R C k ≠ CanDom.succ x R C k' := by
  intro h
  injection h with _ _ _ hk
  exact hkk hk

/-- **Skolem witness theorem (forward CardinalityWitnesses)**.

    If `≥(n+1) R.C ∈ carrierSet x`, then the `n+1` Skolem successors
    `succ x R C 0, …, succ x R C n` provide `n+1` distinct
    `ext_role`-witnesses for the filler `C` — establishing
    `atLeastCard … (n+1)` directly. -/
theorem skol_atLeast_forward
    (O : Ontology) (hCons : consistent O (∅ : Set Concept))
    (x : CanDom O) (R : Nat) (C : Concept) (n : Nat)
    (hCarrier : Concept.atLeast (n+1) R C ∈ carrierSet O hCons x) :
    Interp.atLeastCard
      (fun y : CanDom O =>
        (skolCanonical O hCons).ext_role R x y ∧
        C ∈ carrierSet O hCons y)
      (n+1) := by
  have hExist : Concept.exist R C ∈ carrierSet O hCons x :=
    atLeast_implies_exist_in_carrier O hCons x R C n hCarrier
  -- Generic helper: build the nested atLeastCard structure using
  -- successive Skolem indices starting from any base `b`.
  suffices aux :
      ∀ (b m : Nat),
        Interp.atLeastCard
          (fun y : CanDom O =>
            ((skolCanonical O hCons).ext_role R x y ∧
              C ∈ carrierSet O hCons y) ∧
            (∀ k < b, y ≠ .succ x R C k))
          m by
    have h := aux 0 (n+1)
    refine atLeastCard_filler_mono
      (P := fun y => ((skolCanonical O hCons).ext_role R x y ∧
                       C ∈ carrierSet O hCons y) ∧
                       (∀ k < 0, y ≠ .succ x R C k))
      (Q := fun y => (skolCanonical O hCons).ext_role R x y ∧
                       C ∈ carrierSet O hCons y)
      ?_ (n+1) h
    intro y ⟨hMain, _⟩
    exact hMain
  intro b m
  induction m generalizing b with
  | zero => trivial
  | succ m ih =>
      refine ⟨.succ x R C b, ?_, ?_⟩
      · refine ⟨⟨?_, ?_⟩, ?_⟩
        · exact skol_succ_in_ext_role O hCons x R C b hExist
        · exact succ_carrier_contains_C O hCons x R C b hExist
        · intro k hk hEq
          exact (skol_succ_k_ne x R C (Nat.ne_of_lt hk).symm) hEq
      · -- atLeastCard (filter out the just-chosen successor) m, by IH at b+1.
        refine atLeastCard_filler_mono
          (P := fun y =>
            ((skolCanonical O hCons).ext_role R x y ∧
              C ∈ carrierSet O hCons y) ∧
            (∀ k < (b+1), y ≠ .succ x R C k))
          (Q := fun y =>
            (((skolCanonical O hCons).ext_role R x y ∧
              C ∈ carrierSet O hCons y) ∧
            (∀ k < b, y ≠ .succ x R C k)) ∧
            y ≠ .succ x R C b)
          ?_ m (ih (b+1))
        intro y ⟨hMain, hNeAll⟩
        refine ⟨⟨hMain, ?_⟩, ?_⟩
        · intro k hk
          exact hNeAll k (Nat.lt_succ_of_lt hk)
        · exact hNeAll b (Nat.lt_succ_self _)

-- ============================================================
-- 6.  Truth-lemma cases that the Skolem-tagging discharges
--     unconditionally: existentials, hasSelf, universals.
-- ============================================================

/-- Type-membership of conjunctions: if both `C` and `D` are in a
    type's carrier, so is `conj C D`.  Useful helper not in
    `ALCHOQCanonical`. -/
theorem conj_mem (O : Ontology) (t : Type_ O) (C D : Concept)
    (hC : C ∈ t.carrier) (hD : D ∈ t.carrier) :
    Concept.conj C D ∈ t.carrier := by
  rcases t.maximal (Concept.conj C D) with hMem | hNeg
  · exact hMem
  · exfalso
    -- neg (conj C D) ∈ t.carrier  with  C, D ∈ t.carrier.
    -- By deMorganA: SatC O (neg (conj C D)) (disj (neg C) (neg D)).
    -- By type_closure, disj (neg C) (neg D) ∈ t.carrier.
    have hDisj : Concept.disj (Concept.neg C) (Concept.neg D) ∈ t.carrier :=
      type_closure O t _ _ hNeg (SatC.deMorganA C D)
    -- Now `[C, D, disj (neg C) (neg D)]` is inconsistent.
    apply t.cons [C, D, Concept.disj (Concept.neg C) (Concept.neg D)]
    · intro E hE
      simp at hE
      rcases hE with rfl | rfl | rfl
      · exact hC
      · exact hD
      · exact hDisj
    · show SatC O (conjList [C, D,
                              Concept.disj (Concept.neg C) (Concept.neg D)])
                  Concept.bot
      unfold conjList
      -- conj C (conj D (conj (disj (neg C) (neg D)) top)) ⊑ bot.
      -- Strategy: discard the trailing top, rebracket to
      -- `(conj C D) ⊓ (disj (neg C) (neg D))`, then via dist:
      -- `(disj ((conj C D) ⊓ (neg C)) ((conj C D) ⊓ (neg D)))` ⊑ bot
      -- by `nc`-on-each-disjunct.
      have hCD : SatC O (.conj C (.conj D
                  (.conj (.disj (.neg C) (.neg D)) .top)))
                       (.conj (.conj C D) (.disj (.neg C) (.neg D))) := by
        refine SatC.satC_andI ?_ ?_
        · refine SatC.satC_andI ?_ ?_
          · exact SatC.satC_andL _ _
          · exact SatC.trans (SatC.satC_andR _ _) (SatC.satC_andL _ _)
        · refine SatC.trans (SatC.satC_andR _ _) ?_
          refine SatC.trans (SatC.satC_andR _ _) ?_
          exact SatC.satC_andL _ _
      have hDist : SatC O (.conj (.conj C D) (.disj (.neg C) (.neg D)))
                          (.disj (.conj (.conj C D) (.neg C))
                                 (.conj (.conj C D) (.neg D))) :=
        SatC.dist _ _ _
      have hLeft : SatC O (.conj (.conj C D) (.neg C)) Concept.bot := by
        refine SatC.trans ?_ (SatC.nc C)
        refine SatC.satC_andI ?_ ?_
        · exact SatC.trans (SatC.satC_andL _ _) (SatC.satC_andL _ _)
        · exact SatC.satC_andR _ _
      have hRight : SatC O (.conj (.conj C D) (.neg D)) Concept.bot := by
        refine SatC.trans ?_ (SatC.nc D)
        refine SatC.satC_andI ?_ ?_
        · exact SatC.trans (SatC.satC_andL _ _) (SatC.satC_andR _ _)
        · exact SatC.satC_andR _ _
      exact SatC.trans hCD (SatC.trans hDist (SatC.satC_orE hLeft hRight))

/-- **Truth lemma at hasSelf** in the Skolem model: needs no
    meta-hypothesis.  The forward direction reads off the self-loop
    clause of `ext_role`; the backward direction uses `hasSelf_with_univ`
    plus type-closure for universal-self-propagation. -/
theorem skol_eval_hasSelf_iff
    (O : Ontology) (hCons : consistent O (∅ : Set Concept))
    (R : Nat) (x : CanDom O) :
    (skolCanonical O hCons).eval (.hasSelf R) x ↔
      Concept.hasSelf R ∈ carrierSet O hCons x := by
  show (skolCanonical O hCons).ext_role R x x ↔ _
  constructor
  · -- ext_role at (x, x) → second conjunct gives hasSelf.
    rintro ⟨_, hSelf⟩
    exact hSelf rfl
  · -- hasSelf in carrier → ext_role at (x, x).
    intro hSelf
    refine ⟨?_, ?_⟩
    · -- universal self-closure at x.
      intro D hUniv
      -- conj (hasSelf R) (univ R D) ⊑ D, hasSelf and univ both in carrier.
      have hConj : Concept.conj (.hasSelf R) (.univ R D) ∈
                       carrierSet O hCons x := by
        unfold carrierSet at hSelf hUniv ⊢
        exact conj_mem O (carrierType O hCons x) _ _ hSelf hUniv
      unfold carrierSet at hConj ⊢
      exact type_closure O (carrierType O hCons x) _ _ hConj
        (SatC.hasSelf_with_univ R D)
    · -- x = x → hasSelf in carrier.
      intro _; exact hSelf

/-- **Truth lemma at ∃R.C** in the Skolem model — modulo IH at the
    filler `C`.  The forward direction uses the 0-th Skolem
    successor as witness; the backward direction is by maximality
    plus `negExist` + universal propagation. -/
theorem skol_eval_exist_iff
    (O : Ontology) (hCons : consistent O (∅ : Set Concept))
    (R : Nat) (C : Concept) (x : CanDom O)
    (ihC : ∀ y : CanDom O,
      (skolCanonical O hCons).eval C y ↔ C ∈ carrierSet O hCons y) :
    (skolCanonical O hCons).eval (.exist R C) x ↔
      Concept.exist R C ∈ carrierSet O hCons x := by
  show (∃ y, (skolCanonical O hCons).ext_role R x y ∧
              (skolCanonical O hCons).eval C y) ↔ _
  constructor
  · -- (←): semantic witness gives existence by maximality argument.
    rintro ⟨y, hR, hCy⟩
    rcases (carrierType O hCons x).maximal (Concept.exist R C) with hMem | hNeg
    · exact hMem
    · -- neg ∃R.C ∈ carrier x → univ R (neg C) ∈ carrier x → neg C ∈ carrier y.
      exfalso
      have hUnivNegC : Concept.univ R (.neg C) ∈ carrierSet O hCons x := by
        unfold carrierSet
        exact type_closure O (carrierType O hCons x) _ _ hNeg
          (SatC.negExist R C)
      have hNegCy : Concept.neg C ∈ carrierSet O hCons y :=
        hR.1 _ hUnivNegC
      have hCy_mem : C ∈ carrierSet O hCons y := (ihC y).mp hCy
      unfold carrierSet at hNegCy hCy_mem
      rcases mem_xor_neg O (carrierType O hCons y) C with
        ⟨_, hnnC⟩ | ⟨hCnotmem, _⟩
      · exact hnnC hNegCy
      · exact hCnotmem hCy_mem
  · -- (→): given ∃R.C ∈ carrier x, witness with the 0-th Skolem successor.
    intro hExist
    refine ⟨.succ x R C 0, ?_, ?_⟩
    · exact skol_succ_in_ext_role O hCons x R C 0 hExist
    · -- C ∈ carrier (.succ x R C 0).
      apply (ihC _).mpr
      exact succ_carrier_contains_C O hCons x R C 0 hExist

/-- **Truth lemma at ∀R.C** in the Skolem model — modulo IH at `C`. -/
theorem skol_eval_univ_iff
    (O : Ontology) (hCons : consistent O (∅ : Set Concept))
    (R : Nat) (C : Concept) (x : CanDom O)
    (ihC : ∀ y : CanDom O,
      (skolCanonical O hCons).eval C y ↔ C ∈ carrierSet O hCons y) :
    (skolCanonical O hCons).eval (.univ R C) x ↔
      Concept.univ R C ∈ carrierSet O hCons x := by
  show (∀ y, (skolCanonical O hCons).ext_role R x y →
              (skolCanonical O hCons).eval C y) ↔ _
  constructor
  · -- (←) eval ∀R.C at x → ∀R.C ∈ carrier x, by maximality.
    intro hAll
    rcases (carrierType O hCons x).maximal (Concept.univ R C) with hMem | hNeg
    · exact hMem
    · exfalso
      -- neg ∀R.C ∈ carrier → ∃R.(neg C) ∈ carrier → exists successor with
      -- (neg C) in its carrier → contradicts ihC + hAll.
      have hExistNeg : Concept.exist R (.neg C) ∈ carrierSet O hCons x := by
        unfold carrierSet
        exact type_closure O (carrierType O hCons x) _ _ hNeg
          (SatC.negUniv R C)
      -- Skolem successor witness.
      let y := CanDom.succ x R (.neg C) 0
      have hER : (skolCanonical O hCons).ext_role R x y :=
        skol_succ_in_ext_role O hCons x R (.neg C) 0 hExistNeg
      have hNegCy : Concept.neg C ∈ carrierSet O hCons y :=
        succ_carrier_contains_C O hCons x R (.neg C) 0 hExistNeg
      have hCy : (skolCanonical O hCons).eval C y := hAll y hER
      have hCmem : C ∈ carrierSet O hCons y := (ihC y).mp hCy
      unfold carrierSet at hNegCy hCmem
      rcases mem_xor_neg O (carrierType O hCons y) C with
        ⟨_, hnnC⟩ | ⟨hCnotmem, _⟩
      · exact hnnC hNegCy
      · exact hCnotmem hCmem
  · -- (→) ∀R.C ∈ carrier x → eval ∀R.C at x, by universal propagation.
    intro hUniv y hR
    apply (ihC y).mpr
    -- y is an R-successor of x; universal propagation gives C ∈ carrier y.
    exact hR.1 C hUniv

end ALCHOQ
end ELKSDD
