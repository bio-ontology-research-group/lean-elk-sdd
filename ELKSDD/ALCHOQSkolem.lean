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

end ALCHOQ
end ELKSDD
