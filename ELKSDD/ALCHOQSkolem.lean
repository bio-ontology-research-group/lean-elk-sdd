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

-- ============================================================
-- 7.  Structural fragment with NO meta-hypotheses.
--
--     We isolate the sub-syntax of ALCHOQ where every case of the
--     truth lemma can be discharged purely by the Skolem-tagged
--     construction — *no* NomCompleteness, *no* HasSelfCompleteness,
--     *no* CardinalityWitnesses.
--
--     `SkolFragment` admits: atoms, ⊤, ⊥, negation, conjunction,
--     disjunction, ∃R.C, ∀R.C, ≥0 / ≤0 cardinality (which collapse
--     to ⊤ / ∀R.¬C), and `hasSelf R`.  Excluded: nominals and
--     positive `≥(n+1)` / `≤(n+1)` cardinality (these are the
--     genuinely non-Tena-Cucala-handled cases).
-- ============================================================

/-- The unconditionally-discharged sub-syntax of ALCHOQ. -/
def SkolFragment : Concept → Prop
  | .atom _        => True
  | .top           => True
  | .bot           => True
  | .nom _         => False
  | .neg C         => SkolFragment C
  | .conj A B      => SkolFragment A ∧ SkolFragment B
  | .disj A B      => SkolFragment A ∧ SkolFragment B
  | .exist _ C     => SkolFragment C
  | .univ _ C      => SkolFragment C
  | .atLeast 0 _ C => SkolFragment C
  | .atLeast (_+1) _ _ => False
  | .atMost 0 _ C  => SkolFragment C
  | .atMost (_+1) _ _ => False
  | .hasSelf _     => True

/-- An ontology is in the SkolFragment iff every axiom uses only
    SkolFragment concepts. -/
def OntologySkolFragment (O : Ontology) : Prop :=
  ∀ ax ∈ O, SkolFragment ax.1 ∧ SkolFragment ax.2

/-- ⊤ is always in a carrier (via top_mem applied to the underlying
    Type_ O). -/
theorem skol_top_mem (O : Ontology) (hCons : consistent O (∅ : Set Concept))
    (x : CanDom O) :
    Concept.top ∈ carrierSet O hCons x := top_mem O _

/-- ⊥ is never in a carrier. -/
theorem skol_bot_not_mem (O : Ontology)
    (hCons : consistent O (∅ : Set Concept)) (x : CanDom O) :
    Concept.bot ∉ carrierSet O hCons x := bot_not_mem O _

/-- **Truth lemma on the SkolFragment** — unconditional in `O`,
    needing only `consistent O ∅`.  Proven by structural induction
    on the concept. -/
theorem skol_canonical_eval_iff
    (O : Ontology) (hCons : consistent O (∅ : Set Concept))
    (C : Concept) (hC : SkolFragment C) :
    ∀ x : CanDom O,
      ((skolCanonical O hCons).eval C x ↔ C ∈ carrierSet O hCons x) := by
  induction C with
  | atom n => intro x; exact Iff.rfl
  | top =>
      intro x
      show True ↔ _
      exact ⟨fun _ => skol_top_mem O hCons x,
             fun _ => trivial⟩
  | bot =>
      intro x
      show False ↔ _
      exact ⟨fun h => h.elim,
             fun h => (skol_bot_not_mem O hCons x h).elim⟩
  | nom i => exact absurd hC (by simp [SkolFragment])
  | neg D ih =>
      intro x
      show (¬ (skolCanonical O hCons).eval D x) ↔
              Concept.neg D ∈ carrierSet O hCons x
      have ihD := ih hC
      rw [ihD x]
      unfold carrierSet
      rcases mem_xor_neg O (carrierType O hCons x) D with
        ⟨hDmem, hnDnotmem⟩ | ⟨hDnotmem, hnDmem⟩
      · exact ⟨fun h => absurd hDmem h, fun h => absurd h hnDnotmem⟩
      · exact ⟨fun _ => hnDmem, fun _ => hDnotmem⟩
  | conj A B ihA ihB =>
      intro x
      obtain ⟨hA, hB⟩ := hC
      show ((skolCanonical O hCons).eval A x ∧ (skolCanonical O hCons).eval B x) ↔
            Concept.conj A B ∈ carrierSet O hCons x
      rw [ihA hA x, ihB hB x]
      unfold carrierSet
      constructor
      · rintro ⟨hAmem, hBmem⟩
        exact conj_mem O (carrierType O hCons x) A B hAmem hBmem
      · intro hConj
        refine ⟨?_, ?_⟩
        · exact type_closure O _ _ _ hConj (SatC.satC_andL _ _)
        · exact type_closure O _ _ _ hConj (SatC.satC_andR _ _)
  | disj A B ihA ihB =>
      intro x
      obtain ⟨hA, hB⟩ := hC
      show ((skolCanonical O hCons).eval A x ∨ (skolCanonical O hCons).eval B x) ↔
            Concept.disj A B ∈ carrierSet O hCons x
      rw [ihA hA x, ihB hB x]
      unfold carrierSet
      constructor
      · rintro (hA' | hB')
        · exact type_closure O _ _ _ hA' (SatC.ofSat (Sat.orL A B))
        · exact type_closure O _ _ _ hB' (SatC.ofSat (Sat.orR A B))
      · intro hDisj
        -- Suppose neither A nor B is in carrier x; deduce contradiction.
        by_contra hNeither
        push_neg at hNeither
        obtain ⟨hAne, hBne⟩ := hNeither
        rcases mem_xor_neg O (carrierType O hCons x) A with
          ⟨hAmem, _⟩ | ⟨_, hnA⟩
        · exact hAne hAmem
        rcases mem_xor_neg O (carrierType O hCons x) B with
          ⟨hBmem, _⟩ | ⟨_, hnB⟩
        · exact hBne hBmem
        -- Both `neg A, neg B` in carrier with `disj A B` ∈ carrier → contradiction.
        apply (carrierType O hCons x).cons
          [Concept.disj A B, Concept.neg A, Concept.neg B]
        · intro D hD
          simp at hD
          rcases hD with rfl | rfl | rfl
          · exact hDisj
          · exact hnA
          · exact hnB
        · show SatC O (conjList [Concept.disj A B, Concept.neg A, Concept.neg B])
                     Concept.bot
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
  | exist R D ih =>
      intro x
      exact skol_eval_exist_iff O hCons R D x (ih hC)
  | univ R D ih =>
      intro x
      exact skol_eval_univ_iff O hCons R D x (ih hC)
  | atLeast n R D ih =>
      cases n with
      | zero =>
          intro x
          show Interp.atLeastCard _ 0 ↔ _
          unfold Interp.atLeastCard
          refine ⟨fun _ => ?_, fun _ => trivial⟩
          unfold carrierSet
          exact type_closure O (carrierType O hCons x) _ _
            (top_mem O _) (SatC.atLeastZero R D)
      | succ m =>
          exact absurd hC (by simp [SkolFragment])
  | atMost n R D ih =>
      intro x
      have hD : SkolFragment D := by
        cases n with
        | zero => exact hC
        | succ _ => exact absurd hC (by simp [SkolFragment])
      cases n with
      | zero =>
          have hSem : (skolCanonical O hCons).eval (.atMost 0 R D) x ↔
                      ∀ y, (skolCanonical O hCons).ext_role R x y →
                            ¬ (skolCanonical O hCons).eval D y :=
            Interp.eval_atMost_zero (skolCanonical O hCons) R D x
          rw [hSem]
          have ihD := ih hD
          constructor
          · intro hAll
            -- Show univ R (neg D) ∈ carrier x first.
            have hUniv : Concept.univ R (Concept.neg D) ∈
                            carrierSet O hCons x := by
              -- By maximality on univ R (neg D); contradiction if neg.
              rcases (carrierType O hCons x).maximal
                  (Concept.univ R (Concept.neg D)) with hMem | hNeg
              · exact hMem
              · -- neg univ R (neg D) → exist R (neg (neg D)) → exist R D.
                have hExNN : Concept.exist R (.neg (.neg D)) ∈
                              carrierSet O hCons x := by
                  unfold carrierSet
                  exact type_closure O (carrierType O hCons x) _ _ hNeg
                    (SatC.negUniv R (.neg D))
                have hExD : Concept.exist R D ∈ carrierSet O hCons x := by
                  unfold carrierSet
                  unfold carrierSet at hExNN
                  exact type_closure O _ _ _ hExNN
                    (SatC.satC_monoExist R (SatC.negNegE D))
                -- Witness with .succ x R D 0; evaluate D there;
                -- contradiction with hAll.
                let y := CanDom.succ x R D 0
                have hER : (skolCanonical O hCons).ext_role R x y :=
                  skol_succ_in_ext_role O hCons x R D 0 hExD
                have hDy : (skolCanonical O hCons).eval D y :=
                  (ihD y).mpr (succ_carrier_contains_C O hCons x R D 0 hExD)
                exact absurd hDy (hAll y hER)
            unfold carrierSet at hUniv
            unfold carrierSet
            exact type_closure O (carrierType O hCons x) _ _ hUniv
              (SatC.univ_to_atMostZero R D)
          · intro hAtMost y hR
            intro hDy
            have hDmem : D ∈ carrierSet O hCons y := (ihD y).mp hDy
            have hUnivNeg : Concept.univ R (Concept.neg D) ∈
                            carrierSet O hCons x := by
              unfold carrierSet
              unfold carrierSet at hAtMost
              exact type_closure O (carrierType O hCons x) _ _ hAtMost
                (SatC.atMostZero R D)
            have hNegD : Concept.neg D ∈ carrierSet O hCons y :=
              hR.1 _ hUnivNeg
            unfold carrierSet at hDmem hNegD
            rcases mem_xor_neg O (carrierType O hCons y) D with
              ⟨_, hnnD⟩ | ⟨hDnotmem, _⟩
            · exact hnnD hNegD
            · exact hDnotmem hDmem
      | succ m =>
          exact absurd hC (by simp [SkolFragment])
  | hasSelf R => intro x; exact skol_eval_hasSelf_iff O hCons R x

/-- **Skolem canonical satisfies a SkolFragment ontology**. -/
theorem skol_canonical_satisfies
    (O : Ontology) (hCons : consistent O (∅ : Set Concept))
    (hOFrag : OntologySkolFragment O) :
    (skolCanonical O hCons).satisfies O := by
  intro ax hAx x hP
  obtain ⟨h1Frag, h2Frag⟩ := hOFrag ax hAx
  have h1 : ax.1 ∈ carrierSet O hCons x :=
    (skol_canonical_eval_iff O hCons ax.1 h1Frag x).mp hP
  have h2 : ax.2 ∈ carrierSet O hCons x := by
    unfold carrierSet at h1 ⊢
    exact type_closure O (carrierType O hCons x) _ _ h1
      (SatC.ofSat (Sat.axm ax.1 ax.2 hAx))
  exact (skol_canonical_eval_iff O hCons ax.2 h2Frag x).mpr h2

-- The SkolFragment excludes nominals from queries, so we can use the
-- standard `c_negD_consistent` directly — no need for a nominal-purity
-- side condition on the Lindenbaum extension.

/-- **Headline completeness for the SkolFragment** — unconditional in
    `O` (no NomCompleteness, HasSelfCompleteness, or
    CardinalityWitnesses). -/
theorem satC_complete_skolFragment
    (O : Ontology) (C D : Concept)
    (hOFrag : OntologySkolFragment O)
    (hC : SkolFragment C) (hD : SkolFragment D)
    (hEnt : Entails O C D) : SatC O C D := by
  by_contra hNot
  by_cases hCons : consistent O (∅ : Set Concept)
  · -- consistent ontology; build counter-model.
    have hCN : consistent O ({C, Concept.neg D} : Set Concept) :=
      c_negD_consistent O C D hNot
    obtain ⟨t, htsub⟩ := lindenbaum O _ hCN
    have hsat : (skolCanonical O hCons).satisfies O :=
      skol_canonical_satisfies O hCons hOFrag
    -- Anchor at `.seed t` in the Skolem domain.
    let x : CanDom O := .seed t
    have hCarrierX : carrierSet O hCons x = t.carrier := rfl
    have hCmem : C ∈ carrierSet O hCons x := by
      rw [hCarrierX]
      exact htsub (by simp : C ∈ ({C, Concept.neg D} : Set _))
    have hEvalC : (skolCanonical O hCons).eval C x :=
      (skol_canonical_eval_iff O hCons C hC x).mpr hCmem
    have hEvalD : (skolCanonical O hCons).eval D x := hEnt _ hsat x hEvalC
    have hDmem : D ∈ carrierSet O hCons x :=
      (skol_canonical_eval_iff O hCons D hD x).mp hEvalD
    have hnDmem : Concept.neg D ∈ carrierSet O hCons x := by
      rw [hCarrierX]
      exact htsub (by simp : Concept.neg D ∈ ({C, Concept.neg D} : Set _))
    unfold carrierSet at hDmem hnDmem
    rcases mem_xor_neg O (carrierType O hCons x) D with
      ⟨_, hnnD⟩ | ⟨hDnotmem, _⟩
    · exact hnnD hnDmem
    · exact hDnotmem hDmem
  · -- O inconsistent; chain top ⊑ bot.
    unfold consistent at hCons
    push_neg at hCons
    obtain ⟨L, hLin, hSat⟩ := hCons
    have hLnil : L = [] := by
      cases L with
      | nil => rfl
      | cons E _ => exact absurd (hLin E List.mem_cons_self) (by simp)
    subst hLnil
    have hTopBot : SatC O Concept.top Concept.bot := by
      have : conjList ([] : List Concept) = Concept.top := rfl
      rw [this] at hSat; exact hSat
    apply hNot
    exact SatC.trans (satC_top O C) (SatC.trans hTopBot (satC_bot O D))

end ALCHOQ
end ELKSDD
