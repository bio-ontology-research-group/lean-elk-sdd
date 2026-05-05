/-
  ELKSDD/Merging.lean
  -------------------
  Merging canonical model (Kazakov 2014 §6) for OWL 2 EL nominal axioms
  of the *RHS* shapes:

      shape 2:  gci C ⊑ {a_i}            -- "C is a singleton class"
      shape 4:  gci {a_i} ⊑ {a_j}        -- SameIndividual(a_i, a_j)

  These shapes force domain elements to be merged: shape 2 collapses
  every C-instance with `indiv i`, and shape 4 collapses `indiv i` with
  `indiv j`.  The plain canonical model of `ELpp.canon` cannot satisfy
  them because its `indiv i` is `⟨nom i, _⟩` and distinct concepts
  produce distinct domain elements by constructor disjointness.

  Construction sketch.

    1. Treat the relation `Sat O (.nom i) (.nom j)` as a Setoid on `Nat`
       (reflexive by `Sat.refl`, transitive by `Sat.trans`, symmetric by
       the new `Sat.nom_symm` calculus rule added in `ELpp`).
    2. Domain = `MergedDom O`, a sum of two cases:
        * `nominal q` for `q : NomClass O`, the equivalence class of a
          nominal index — one element per equivalence class.
        * `regular C h hnot` for a *non-nominal* concept `C` with
          `¬ Sat O C .bot` and `∀ i. ¬ Sat O C (.nom i)` (i.e., `C` is
          not forced into any nominal class).
    3. `eval`, `ext_role`, and `indiv` are defined on this domain via
       `Quotient.lift` for nominal cases and by direct `Sat`-lookup for
       regular cases.  Range guards mirror the original `canon`.

  Coverage in this layer.

    * `gci`s of all four nominal shapes (LHS NF/nom × RHS NF/nom/∃R.nom).
    * `rinc` (role hierarchy).
    * `reflexive`.

  Excluded (still future work).

    * `rchain` — would require the merged-domain analogue of
      `RangeChainSafe`, plus the `range`+chain interaction.
    * `range` — needs `Sat O (.nom i) E` to be derivable for every
      range axiom on a nominal target's rinc-hierarchy; this requires
      a *merging-aware* `Sat` rule (not added here).
    * `hasKey` — gated `False` (Kazakov 2014 §6, separate construction).

  References.
    [Kazakov 2014]    The Incredible ELK, §6 — merging canonical model
                      for nominals.
    [BBL 2008]        Pushing the EL Envelope Further — original
                      treatment of nominal merging in EL++.
-/

import ELKSDD.ELpp

namespace ELKSDD
namespace ELpp

-- ============================================================
-- 1. Nominal-equivalence setoid on Nat
-- ============================================================

/-- The relation `Sat O (.nom i) (.nom j)` is a Setoid on `Nat`.

    *Reflexivity*  : `Sat.refl (.nom i)`.
    *Transitivity* : `Sat.trans`.
    *Symmetry*     : `Sat.nom_symm` (new rule).

    The equivalence class `⟦i⟧` represents *all* nominals provably
    forced equal to `a_i` in the calculus. -/
def nomEqvSetoid (O : Ontology) : Setoid Nat where
  r := fun i j => Sat O (.nom i) (.nom j)
  iseqv := {
    refl := fun _ => Sat.refl _
    symm := Sat.nom_symm
    trans := Sat.trans
  }

/-- Equivalence classes of nominal indices (Kazakov 2014 §6).
    A `NomClass O` is one merged "individual" in the canonical model. -/
def NomClass (O : Ontology) : Type := Quotient (nomEqvSetoid O)

/-- Helper: lift a nominal index to its equivalence class. -/
def nomCls (O : Ontology) (i : Nat) : NomClass O :=
  Quotient.mk (nomEqvSetoid O) i

/-- Two nominals share an equivalence class iff they are mutually
    Sat-derivable (the underlying setoid relation). -/
theorem nomCls_eq_iff {O : Ontology} {i j : Nat} :
    nomCls O i = nomCls O j ↔ Sat O (.nom i) (.nom j) :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- Forward direction of `nomCls_eq_iff` — the Sat relation
    derives the class equality. -/
theorem nomCls_sound {O : Ontology} {i j : Nat}
    (h : Sat O (.nom i) (.nom j)) : nomCls O i = nomCls O j :=
  Quotient.sound h

/-- Backward direction — class equality implies the Sat relation
    (in either direction; we pick i ⊑ j here). -/
theorem nomCls_exact {O : Ontology} {i j : Nat}
    (h : nomCls O i = nomCls O j) : Sat O (.nom i) (.nom j) :=
  Quotient.exact h

-- ============================================================
-- 2. Merged canonical domain
-- ============================================================

/-- *Pre-quotient* concepts that should NOT be merged with any nominal
    class.  A concept `C` is "regular" if it is consistent (`¬ Sat O C .bot`)
    and is not provably forced into any nominal singleton
    (`∀ i, ¬ Sat O C (.nom i)`).

    Concepts that ARE forced into a nominal class will be represented
    by `MergedDom.nominal q` for the appropriate equivalence class `q`,
    not by a regular element. -/
def Regular (O : Ontology) (C : Concept) : Prop :=
  ¬ Sat O C .bot ∧ ∀ i, ¬ Sat O C (.nom i)

/-- **Merged canonical domain** (Kazakov 2014 §6).

    A merged element is either:

      * `nominal q`  — the merged equivalence class of nominal indices
        `q : NomClass O`.  All nominals related under `Sat O (.nom ·) (.nom ·)`
        collapse to the same domain element.

      * `regular C h` — a non-nominal concept with `Regular O C`
        (consistent and not forced-nominal).  These represent ordinary
        canonical witnesses unaffected by merging. -/
inductive MergedDom (O : Ontology) : Type where
  | nominal : NomClass O → MergedDom O
  | regular : (C : Concept) → Regular O C → MergedDom O

-- ============================================================
-- 3. Helper: Quotient.lift respect proofs for Sat-on-nominals
-- ============================================================

/-- *Sat from a nominal LHS* respects nominal equivalence.

    If `Sat O (.nom i) (.nom j)` (the setoid relation) and
    `Sat O (.nom i) D`, then `Sat O (.nom j) D` (and conversely).
    Proof: `Sat.nom_symm` + `Sat.trans`. -/
theorem sat_nomLHS_respects (O : Ontology) (D : Concept) :
    ∀ i j, Sat O (.nom i) (.nom j) →
      Sat O (.nom i) D = Sat O (.nom j) D := by
  intro i j hij
  apply propext
  constructor
  · intro hi
    -- From hij : Sat O (.nom i) (.nom j), get Sat O (.nom j) (.nom i) by symm.
    have hji : Sat O (.nom j) (.nom i) := Sat.nom_symm hij
    -- Then Sat O (.nom j) D by trans.
    exact Sat.trans hji hi
  · intro hj
    exact Sat.trans hij hj

/-- *Sat to a nominal RHS* respects nominal equivalence on the RHS.

    If `Sat O (.nom i) (.nom j)` and `Sat O C (.nom i)`, then
    `Sat O C (.nom j)` (and conversely). -/
theorem sat_nomRHS_respects (O : Ontology) (C : Concept) :
    ∀ i j, Sat O (.nom i) (.nom j) →
      Sat O C (.nom i) = Sat O C (.nom j) := by
  intro i j hij
  apply propext
  constructor
  · intro hCi
    exact Sat.trans hCi hij
  · intro hCj
    have hji : Sat O (.nom j) (.nom i) := Sat.nom_symm hij
    exact Sat.trans hCj hji

/-- *Sat to ∃R.(nom)* respects nominal equivalence on the RHS witness.

    If `Sat O (.nom j) (.nom k)` and `Sat O C (.exist R (.nom j))`,
    then `Sat O C (.exist R (.nom k))`.  Uses `Sat.exist_prop`. -/
theorem sat_existNomRHS_respects (O : Ontology) (C : Concept) (R : Role) :
    ∀ j k, Sat O (.nom j) (.nom k) →
      Sat O C (.exist R (.nom j)) = Sat O C (.exist R (.nom k)) := by
  intro j k hjk
  apply propext
  constructor
  · intro hCRj
    exact Sat.exist_prop hCRj hjk
  · intro hCRk
    have hkj : Sat O (.nom k) (.nom j) := Sat.nom_symm hjk
    exact Sat.exist_prop hCRk hkj

/-- *Sat from ∃R.(nom)* — lifting both sides — respects nominal
    equivalence on both arguments. -/
theorem sat_existNomBoth_respects (O : Ontology) (R : Role) :
    ∀ i₁ j₁ i₂ j₂,
      Sat O (.nom i₁) (.nom i₂) →
      Sat O (.nom j₁) (.nom j₂) →
      Sat O (.nom i₁) (.exist R (.nom j₁)) =
      Sat O (.nom i₂) (.exist R (.nom j₂)) := by
  intro i₁ j₁ i₂ j₂ hi hj
  rw [sat_nomLHS_respects O _ _ _ hi]
  exact sat_existNomRHS_respects O _ R _ _ hj

-- ============================================================
-- 4. Merged canonical interpretation
-- ============================================================

/-- Concept-extension on the merged canonical model.

    `mc_ext_concept O n x` decides whether `x ∈ (atom n)^I`:

      * If `x = nominal q`, lift `Sat O (.nom i) (.atom n)` over `q`.
      * If `x = regular C _`, take `Sat O C (.atom n)`. -/
def mc_ext_concept (O : Ontology) (n : Nat) : MergedDom O → Prop
  | .nominal q     => Quotient.lift (fun i => Sat O (.nom i) (.atom n))
                        (sat_nomLHS_respects O (.atom n)) q
  | .regular C _   => Sat O C (.atom n)

/-- Role-extension on the merged canonical model.

    `mc_ext_role O R x y` decides whether `(x, y) ∈ R^I`:

      * `nominal qi, nominal qj`: lift `Sat O (.nom i) (.exist R (.nom j))`.
      * `nominal qi, regular D _`: lift `Sat O (.nom i) (.exist R D)`.
      * `regular C _, nominal qj`: lift `Sat O C (.exist R (.nom j))`.
      * `regular C _, regular D _`: `Sat O C (.exist R D)`.

    *Note*: this fragment forbids range axioms entirely (see
    `AxiomMerge`), so no range-guard is required. -/
def mc_ext_role (O : Ontology) (R : Role) : MergedDom O → MergedDom O → Prop
  | .nominal qi, .nominal qj =>
      Quotient.lift₂ (fun i j => Sat O (.nom i) (.exist R (.nom j)))
        (sat_existNomBoth_respects O R) qi qj
  | .nominal qi, .regular D _ =>
      Quotient.lift (fun i => Sat O (.nom i) (.exist R D))
        (sat_nomLHS_respects O (.exist R D)) qi
  | .regular C _, .nominal qj =>
      Quotient.lift (fun j => Sat O C (.exist R (.nom j)))
        (sat_existNomRHS_respects O C R) qj
  | .regular C _, .regular D _ => Sat O C (.exist R D)

/-- Individual-name interpretation on the merged canonical model.

    `mc_indiv O default i` returns:
      * `nominal (nomCls O i)` if `nom i` is consistent (`¬ Sat O (.nom i) .bot`).
      * `default` otherwise (fallback for inconsistent ontologies). -/
noncomputable def mc_indiv (O : Ontology) (default : MergedDom O) (i : Nat) :
    MergedDom O := by
  classical
  exact if _ : ¬ Sat O (.nom i) .bot then .nominal (nomCls O i) else default

/-- **Merged canonical interpretation** (Kazakov 2014 §6).

    Domain is `MergedDom O`; concept- and role-extensions and
    individual-name interpretation are as above.  All nominal
    equivalences forced by the calculus (i.e., `Sat O (.nom i) (.nom j)`)
    are merged via the `nominal q` constructor sharing class `q`. -/
noncomputable def mergedCanon (O : Ontology) (default : MergedDom O) :
    Interp (MergedDom O) :=
  { ext_concept := mc_ext_concept O
    ext_role    := mc_ext_role O
    indiv       := mc_indiv O default }

-- ============================================================
-- 5. "Shallow" concept fragment
-- ============================================================

/-- *Shallow* concepts — the fragment for which the merged-canonical-
    model correspondence (`merged_canon_eval`) is established.

    This fragment includes:
      * atomic concepts, top, bot, conjunctions thereof
      * direct nominals `.nom i`
      * one level of existential restriction with a nominal target,
        i.e., `.exist R (.nom j)` (shape 3).

    It excludes deeper existentials (`.exist R E` with `E` non-nominal),
    because the merging-aware existential-witness selection at nominal
    classes requires Sat-rules that are not semantically sound in
    classical OWL semantics (a forced-nominal concept is not
    necessarily inhabited by its target individual in every model).

    For the *typical OWL 2 EL TBox fragment with deep existentials*
    (e.g., `Mother ⊑ ∃hasChild.Person`) but no nominal-RHS axioms
    (no shapes 2/4), use the standard `canon` from `ELKSDD.ELpp`
    instead — it handles deep existentials cleanly. -/
inductive Shallow : Concept → Prop where
  | atom      : ∀ n, Shallow (.atom n)
  | top       : Shallow .top
  | bot       : Shallow .bot
  | conj      : ∀ {A B}, Shallow A → Shallow B → Shallow (.conj A B)
  | nom       : ∀ i, Shallow (.nom i)
  | exist_nom : ∀ R i, Shallow (.exist R (.nom i))

-- ============================================================
-- 6. Sat-side image — merged-Sat
-- ============================================================

/-- The "merged Sat" — Sat-style relation `Sat O · D` extended to
    the merged domain.  At a `nominal q` element, it is the lifted
    `Sat O (.nom k) D` over the equivalence class.  At a `regular C h`
    element, it is `Sat O C D`. -/
def MergedSat (O : Ontology) (D : Concept) : MergedDom O → Prop
  | .nominal q   => Quotient.lift (fun k => Sat O (.nom k) D)
                      (sat_nomLHS_respects O D) q
  | .regular C _ => Sat O C D

/-- Reduction: `MergedSat` at a fully-applied nominal class
    representative is the underlying Sat. -/
theorem mergedSat_nominal_rep (O : Ontology) (D : Concept) (k : Nat) :
    MergedSat O D (.nominal (nomCls O k)) ↔ Sat O (.nom k) D := by
  unfold MergedSat nomCls
  rfl

theorem mergedSat_regular (O : Ontology) (D : Concept) (C : Concept)
    (h : Regular O C) : MergedSat O D (.regular C h) ↔ Sat O C D := by
  unfold MergedSat
  rfl

-- ============================================================
-- 7. `merged_canon_eval` — correspondence eval ↔ MergedSat
-- ============================================================

/-- Helper: `(mergedCanon O default).indiv j = .nominal (nomCls O j)`
    when `nom j` is consistent (`AllNomInhabited` blanket). -/
theorem mergedCanon_indiv_eq (O : Ontology) (default : MergedDom O) (j : Nat)
    (h : ¬ Sat O (.nom j) .bot) :
    (mergedCanon O default).indiv j = .nominal (nomCls O j) := by
  unfold mergedCanon mc_indiv
  simp [dif_pos h]

/-- **Merged canonical eval ↔ MergedSat correspondence** (analog of
    `canon_eval` from `ELpp` for the merged model).

    For any `Shallow` concept `D`, the `mergedCanon` interpretation
    evaluates `D` at any merged element `x` exactly when `MergedSat O D x`
    holds (i.e., the Sat-image of `x.label` derives `D`).

    Proof: structural induction on the `Shallow D` derivation.
    The key cases are:

      * `nom j`     — direct via `mergedCanon_indiv_eq` and quotient equality.
      * `exist_nom` — direct via the `mc_ext_role` definition and
        constructor disjointness.

    Atom/top/bot/conj are routine. -/
theorem merged_canon_eval (O : Ontology) (default : MergedDom O)
    (hO_inhab : AllNomInhabited O) :
    ∀ (D : Concept), Shallow D → ∀ (x : MergedDom O),
      (mergedCanon O default).eval D x ↔ MergedSat O D x := by
  classical
  intro D hD
  induction hD with
  | atom n =>
      intro x
      cases x with
      | nominal q =>
          unfold MergedSat
          show mc_ext_concept O n (.nominal q) ↔
            Quotient.lift (fun k => Sat O (.nom k) (.atom n))
              (sat_nomLHS_respects O (.atom n)) q
          unfold mc_ext_concept
          rfl
      | regular C h =>
          unfold MergedSat
          show mc_ext_concept O n (.regular C h) ↔ Sat O C (.atom n)
          unfold mc_ext_concept
          rfl
  | top =>
      intro x
      cases x with
      | nominal q =>
          refine ⟨fun _ => ?_, fun _ => trivial⟩
          -- MergedSat O .top (nominal q) lifts Sat O (.nom k) .top.
          -- Sat.top gives this for any rep.
          induction q using Quotient.ind
          unfold MergedSat
          show Sat O (.nom _) .top
          exact Sat.top _
      | regular C h =>
          refine ⟨fun _ => ?_, fun _ => trivial⟩
          show Sat O C .top
          exact Sat.top _
  | bot =>
      intro x
      cases x with
      | nominal q =>
          refine ⟨fun h => h.elim, fun h => ?_⟩
          -- h : MergedSat O .bot (nominal q) = Sat O (.nom k_rep) .bot.
          -- But under AllNomInhabited, ¬ Sat O (.nom k_rep) .bot.  Contra.
          induction q using Quotient.ind with
          | _ k =>
              unfold MergedSat at h
              show False
              exact (hO_inhab k h).elim
      | regular C hReg =>
          refine ⟨fun h => h.elim, fun h => ?_⟩
          show False
          exact (hReg.1 h).elim
  | @conj A B _ _ ihA ihB =>
      intro x
      cases x with
      | nominal q =>
          induction q using Quotient.ind with
          | _ k =>
              constructor
              · rintro ⟨hA, hB⟩
                -- ihA, ihB give eval iff MergedSat at this nominal.
                have hAk : Sat O (.nom k) A := (ihA _).mp hA
                have hBk : Sat O (.nom k) B := (ihB _).mp hB
                show Sat O (.nom k) (.conj A B)
                exact Sat.conj_intro hAk hBk
              · intro hAB
                show (mergedCanon O default).eval A (.nominal _) ∧
                     (mergedCanon O default).eval B (.nominal _)
                have hABk : Sat O (.nom k) (.conj A B) := hAB
                refine ⟨(ihA _).mpr ?_, (ihB _).mpr ?_⟩
                · show Sat O (.nom k) A; exact Sat.conj_left hABk
                · show Sat O (.nom k) B; exact Sat.conj_right hABk
      | regular C hReg =>
          constructor
          · rintro ⟨hA, hB⟩
            have hCA : Sat O C A := (ihA _).mp hA
            have hCB : Sat O C B := (ihB _).mp hB
            show Sat O C (.conj A B)
            exact Sat.conj_intro hCA hCB
          · intro hAB
            have hABc : Sat O C (.conj A B) := hAB
            refine ⟨(ihA _).mpr ?_, (ihB _).mpr ?_⟩
            · show Sat O C A; exact Sat.conj_left hABc
            · show Sat O C B; exact Sat.conj_right hABc
  | nom j =>
      intro x
      cases x with
      | nominal q =>
          induction q using Quotient.ind with
          | _ k =>
              show (.nominal (nomCls O k) = (mergedCanon O default).indiv j) ↔
                Sat O (.nom k) (.nom j)
              rw [mergedCanon_indiv_eq O default j (hO_inhab j)]
              constructor
              · intro hEq
                have h_qkj : nomCls O k = nomCls O j := by
                  injection hEq
                exact nomCls_exact h_qkj
              · intro hSat
                have h_qkj : nomCls O k = nomCls O j := nomCls_sound hSat
                rw [h_qkj]
      | regular C hReg =>
          constructor
          · intro hEq
            -- hEq : (regular C hReg) = mergedCanon.indiv j.  After indiv-reduction,
            -- this is regular = nominal — constructor disjoint.
            have hEq' : MergedDom.regular C hReg = (mergedCanon O default).indiv j := hEq
            rw [mergedCanon_indiv_eq O default j (hO_inhab j)] at hEq'
            cases hEq'
          · intro hSat
            -- hSat : Sat O C (.nom j).  Contradicts hReg.2.
            exact (hReg.2 j hSat).elim
  | exist_nom R j =>
      intro x
      -- eval (.exist R (.nom j)) x = ∃ y, ext_role R x y ∧ eval (.nom j) y.
      -- eval (.nom j) y = (y = mergedCanon.indiv j) = (y = nominal (nomCls O j)).
      -- So the existential reduces to mc_ext_role R x (nominal (nomCls O j)).
      have hindiv : (mergedCanon O default).indiv j = .nominal (nomCls O j) :=
        mergedCanon_indiv_eq O default j (hO_inhab j)
      cases x with
      | nominal qi =>
          induction qi using Quotient.ind with
          | _ i =>
              show (∃ y, (mergedCanon O default).ext_role R (.nominal (nomCls O i)) y ∧
                          (mergedCanon O default).eval (.nom j) y) ↔
                   Sat O (.nom i) (.exist R (.nom j))
              constructor
              · rintro ⟨y, hRxy, hyj⟩
                -- hyj : y = mergedCanon.indiv j.  So y = nominal (nomCls O j).
                have hy : y = .nominal (nomCls O j) := by
                  rw [show (mergedCanon O default).eval (.nom j) y = (y = (mergedCanon O default).indiv j) from rfl] at hyj
                  rw [hyj, hindiv]
                subst hy
                show Sat O (.nom i) (.exist R (.nom j))
                -- hRxy : mc_ext_role R (nominal ⟦i⟧) (nominal ⟦j⟧)
                --       = Sat O (.nom i) (.exist R (.nom j))
                exact hRxy
              · intro hSat
                refine ⟨.nominal (nomCls O j), ?_, ?_⟩
                · show (mergedCanon O default).ext_role R
                       (.nominal (nomCls O i)) (.nominal (nomCls O j))
                  exact hSat
                · show (mergedCanon O default).eval (.nom j) (.nominal (nomCls O j))
                  show .nominal (nomCls O j) = (mergedCanon O default).indiv j
                  exact hindiv.symm
      | regular C hReg =>
          show (∃ y, (mergedCanon O default).ext_role R (.regular C hReg) y ∧
                      (mergedCanon O default).eval (.nom j) y) ↔
               Sat O C (.exist R (.nom j))
          constructor
          · rintro ⟨y, hRxy, hyj⟩
            have hy : y = .nominal (nomCls O j) := by
              rw [show (mergedCanon O default).eval (.nom j) y = (y = (mergedCanon O default).indiv j) from rfl] at hyj
              rw [hyj, hindiv]
            subst hy
            show Sat O C (.exist R (.nom j))
            exact hRxy
          · intro hSat
            refine ⟨.nominal (nomCls O j), ?_, ?_⟩
            · show (mergedCanon O default).ext_role R
                   (.regular C hReg) (.nominal (nomCls O j))
              exact hSat
            · show .nominal (nomCls O j) = (mergedCanon O default).indiv j
              exact hindiv.symm

-- ============================================================
-- 8. AxiomMerge predicate — supported axiom shapes
-- ============================================================

/-- *Axiom shape* supported by the merged canonical model.

      * `gci C D`     — both `C` and `D` are `Shallow` (atom/top/bot/conj
                         + nominal LHS shape 1 + nominal RHS shape 2 +
                         shape-3 `∃R.{a}` + shape-4 `{a} ⊑ {b}`).
      * `rinc R S`    — supported.
      * `reflexive R` — supported.
      * `hasKey C rs` — supported when `C` is `Shallow` (HasKey-induced
                         merging is captured via `Sat.hasKey_apply`).
      * `rchain`, `range` — gated `False` (require additional
        machinery: `RangeChainSafe` analogue, range-on-nominal Sat rules). -/
def AxiomMerge : Axiom → Prop
  | .gci C D       => Shallow C ∧ Shallow D
  | .rinc _ _      => True
  | .rchain _ _ _  => False
  | .range _ _     => False
  | .reflexive _   => True
  | .hasKey C _    => Shallow C

/-- An ontology supports the merged canonical model if all its axioms
    fall in `AxiomMerge`. -/
def OntologyMerge (O : Ontology) : Prop :=
  ∀ ax ∈ O, AxiomMerge ax

-- ============================================================
-- 9. mergedCanon satisfies axioms (Theorem 2 — merging case)
-- ============================================================

/-- **mergedCanon satisfies all `AxiomMerge`-shape axioms.**

    Under `OntologyMerge O ∧ AllNomInhabited O`, the merged canonical
    interpretation satisfies all of `O` — including shape-2 and
    shape-4 nominal-RHS GCIs.

    Proof outline:

      * `gci C D` (Shallow C, Shallow D): use `merged_canon_eval` to
        reduce `eval C x → eval D x` to `MergedSat O C x → MergedSat O D x`,
        then close by `Sat.base_gci` and `Sat.trans`.
      * `rinc R S`: case-split on the (regular/nominal) end-points
        of the `R`-edge; close each by `Sat.rinc_apply`.
      * `reflexive R`: case-split on the element; close each by
        `Sat.reflexive_apply`. -/
theorem mergedCanon_satisfies (O : Ontology) (default : MergedDom O)
    (hO : OntologyMerge O) (hO_inhab : AllNomInhabited O) :
    (mergedCanon O default).satisfies O := by
  classical
  intro ax hax
  have hax_m : AxiomMerge ax := hO ax hax
  cases ax with
  | gci C D =>
      obtain ⟨hC_sh, hD_sh⟩ := hax_m
      intro x hx
      -- Forward: eval C x → MergedSat O C x.
      have hMSC : MergedSat O C x :=
        (merged_canon_eval O default hO_inhab C hC_sh x).mp hx
      -- Use the gci axiom: Sat O C D.
      have hCD : Sat O C D := Sat.base_gci hax
      -- Lift through MergedSat: MergedSat O C x → MergedSat O D x.
      have hMSD : MergedSat O D x := by
        cases x with
        | nominal q =>
            induction q using Quotient.ind with
            | _ k =>
                have hkC : Sat O (.nom k) C := hMSC
                show Sat O (.nom k) D
                exact Sat.trans hkC hCD
        | regular C' hReg =>
            have hC'C : Sat O C' C := hMSC
            show Sat O C' D
            exact Sat.trans hC'C hCD
      -- Backward: MergedSat O D x → eval D x.
      exact (merged_canon_eval O default hO_inhab D hD_sh x).mpr hMSD
  | rinc R S =>
      intro x y hRxy
      -- Need: ext_role S x y.  Case-split on (x, y) constructors.
      cases x with
      | nominal qi =>
          induction qi using Quotient.ind with
          | _ i =>
              cases y with
              | nominal qj =>
                  induction qj using Quotient.ind with
                  | _ j =>
                      have h_iRj : Sat O (.nom i) (.exist R (.nom j)) := hRxy
                      show Sat O (.nom i) (.exist S (.nom j))
                      exact Sat.rinc_apply h_iRj hax
              | regular D hReg =>
                  have h_iRD : Sat O (.nom i) (.exist R D) := hRxy
                  show Sat O (.nom i) (.exist S D)
                  exact Sat.rinc_apply h_iRD hax
      | regular C hReg =>
          cases y with
          | nominal qj =>
              induction qj using Quotient.ind with
              | _ j =>
                  have h_CRj : Sat O C (.exist R (.nom j)) := hRxy
                  show Sat O C (.exist S (.nom j))
                  exact Sat.rinc_apply h_CRj hax
          | regular D hRegD =>
              have h_CRD : Sat O C (.exist R D) := hRxy
              show Sat O C (.exist S D)
              exact Sat.rinc_apply h_CRD hax
  | rchain R₁ R₂ S => exact hax_m.elim
  | range R C => exact hax_m.elim
  | reflexive R =>
      intro x
      cases x with
      | nominal q =>
          induction q using Quotient.ind with
          | _ k =>
              show Sat O (.nom k) (.exist R (.nom k))
              exact Sat.reflexive_apply hax
      | regular C hReg =>
          show Sat O C (.exist R C)
          exact Sat.reflexive_apply hax
  | hasKey C rs =>
      -- AxiomMerge (.hasKey C rs) = Shallow C.
      have hC_sh : Shallow C := hax_m
      -- HasKey semantics: ∀ a b. eval C (indiv a) → eval C (indiv b) →
      --   (∀ R ∈ rs, ∃ c, ext_role R (indiv a) (indiv c) ∧
      --                    ext_role R (indiv b) (indiv c)) →
      --   indiv a = indiv b.
      intro a b h_aC h_bC h_roles
      -- Reduce indiv a and indiv b under AllNomInhabited.
      have ha_indiv : (mergedCanon O default).indiv a =
          .nominal (nomCls O a) :=
        mergedCanon_indiv_eq O default a (hO_inhab a)
      have hb_indiv : (mergedCanon O default).indiv b =
          .nominal (nomCls O b) :=
        mergedCanon_indiv_eq O default b (hO_inhab b)
      -- Translate role witnesses to Sat-typed facts.
      have h_aC_sat : Sat O (.nom a) C := by
        rw [ha_indiv] at h_aC
        have h_msC : MergedSat O C (.nominal (nomCls O a)) :=
          (merged_canon_eval O default hO_inhab C hC_sh _).mp h_aC
        exact h_msC
      have h_bC_sat : Sat O (.nom b) C := by
        rw [hb_indiv] at h_bC
        have h_msC : MergedSat O C (.nominal (nomCls O b)) :=
          (merged_canon_eval O default hO_inhab C hC_sh _).mp h_bC
        exact h_msC
      -- For each R ∈ rs, classical-choose the witness c (Nat).
      -- Build a Skolem witness function cs : Role → Nat.
      have h_pair : ∀ R, R ∈ rs → ∃ c : Nat,
          Sat O (.nom a) (.exist R (.nom c)) ∧
          Sat O (.nom b) (.exist R (.nom c)) := by
        intro R hR
        obtain ⟨c, hRa, hRb⟩ := h_roles R hR
        -- hRa : ext_role R (indiv a) (indiv c).
        -- mc_indiv c is either nominal (nomCls c) (consistent) or default.
        -- Under AllNomInhabited, c is consistent.
        have hc_indiv : (mergedCanon O default).indiv c =
            .nominal (nomCls O c) :=
          mergedCanon_indiv_eq O default c (hO_inhab c)
        rw [ha_indiv, hc_indiv] at hRa
        rw [hb_indiv, hc_indiv] at hRb
        -- mc_ext_role R (nominal ⟦a⟧) (nominal ⟦c⟧) =
        --   Sat O (.nom a) (.exist R (.nom c)).
        exact ⟨c, hRa, hRb⟩
      classical
      let cs : Role → Nat := fun R =>
        if hR : R ∈ rs then Classical.choose (h_pair R hR) else 0
      have h_aR : ∀ R, R ∈ rs →
          Sat O (.nom a) (.exist R (.nom (cs R))) := by
        intro R hR
        show Sat O (.nom a) (.exist R (.nom
          (if hR' : R ∈ rs then Classical.choose (h_pair R hR') else 0)))
        rw [dif_pos hR]
        exact (Classical.choose_spec (h_pair R hR)).1
      have h_bR : ∀ R, R ∈ rs →
          Sat O (.nom b) (.exist R (.nom (cs R))) := by
        intro R hR
        show Sat O (.nom b) (.exist R (.nom
          (if hR' : R ∈ rs then Classical.choose (h_pair R hR') else 0)))
        rw [dif_pos hR]
        exact (Classical.choose_spec (h_pair R hR)).2
      -- Apply the new Sat.hasKey_apply rule.
      have h_eq_sat : Sat O (.nom a) (.nom b) :=
        Sat.hasKey_apply cs h_aC_sat h_bC_sat hax h_aR h_bR
      -- Hence the nominal classes match.
      have h_cls_eq : nomCls O a = nomCls O b := nomCls_sound h_eq_sat
      -- Conclude the indiv equality.
      rw [ha_indiv, hb_indiv, h_cls_eq]

-- ============================================================
-- 10. Completeness via the merged canonical model
-- ============================================================

/-- **Completeness via the merged canonical model.**

    Suppose `O` is `OntologyMerge` (axioms in supported fragment) and
    `AllNomInhabited`.  Suppose `C` and `D` are `Shallow` and `C` is
    `Embeddable`.  Then `Entails O C D → Sat O C D`.

    Proof: build `mergedCanon O default`; pick the embedding `x` of `C`
    (regular or nominal); use `merged_canon_eval` to extract `MergedSat`. -/
theorem complete_via_mergedCanon_regular (O : Ontology) (C D : Concept)
    (hO : OntologyMerge O) (hO_inhab : AllNomInhabited O)
    (hC_sh : Shallow C) (hD_sh : Shallow D)
    (hC_reg : Regular O C)
    (h : Entails O C D) : Sat O C D := by
  classical
  let x : MergedDom O := .regular C hC_reg
  let dflt : MergedDom O := x
  have hcanon : (mergedCanon O dflt).satisfies O :=
    mergedCanon_satisfies O dflt hO hO_inhab
  have hxC : (mergedCanon O dflt).eval C x := by
    rw [merged_canon_eval O dflt hO_inhab C hC_sh x]
    show Sat O C C
    exact Sat.refl _
  have hxD : (mergedCanon O dflt).eval D x := h _ hcanon x hxC
  rw [merged_canon_eval O dflt hO_inhab D hD_sh x] at hxD
  exact hxD

/-- **Completeness for nominal queries** via the merged canonical model.

    For a query `nom i ⊑ D` on a `Shallow` D, with consistent `i`,
    `Entails → Sat`. -/
theorem complete_via_mergedCanon_nom (O : Ontology) (i : Nat) (D : Concept)
    (hO : OntologyMerge O) (hO_inhab : AllNomInhabited O)
    (hD_sh : Shallow D)
    (h : Entails O (.nom i) D) : Sat O (.nom i) D := by
  classical
  let x : MergedDom O := .nominal (nomCls O i)
  let dflt : MergedDom O := x
  have hcanon : (mergedCanon O dflt).satisfies O :=
    mergedCanon_satisfies O dflt hO hO_inhab
  have hxC : (mergedCanon O dflt).eval (.nom i) x := by
    show .nominal (nomCls O i) = (mergedCanon O dflt).indiv i
    exact (mergedCanon_indiv_eq O dflt i (hO_inhab i)).symm
  have hxD : (mergedCanon O dflt).eval D x := h _ hcanon x hxC
  rw [merged_canon_eval O dflt hO_inhab D hD_sh x] at hxD
  -- hxD : MergedSat O D (nominal ⟦i⟧) = Sat O (.nom i) D.
  exact hxD

-- ============================================================
-- 11. Worked examples — shapes 2 and 4
-- ============================================================
--
-- Concrete, end-to-end examples demonstrating the merged canonical
-- model handles the new nominal shapes.

namespace Examples

/-- *Shape 2 worked example* — `Pope ⊑ {pope_individual}`.

    A class is asserted to be the singleton containing one individual.
    After this axiom, every instance of `Pope` collapses with
    `pope_individual`.  Concept names: `Pope = atom 0`.  Individual
    name: `pope_individual = nom 0`. -/
def shape2_O : Ontology := [Axiom.gci (.atom 0) (.nom 0)]

/-- The shape-2 axiom is supported. -/
theorem shape2_axiom_merge : OntologyMerge shape2_O := by
  intro ax hax
  simp [shape2_O] at hax
  subst hax
  exact ⟨Shallow.atom 0, Shallow.nom 0⟩

/-- The Sat-derivation of the singleton-class assertion. -/
theorem shape2_sat : Sat shape2_O (.atom 0) (.nom 0) :=
  Sat.base_gci List.mem_cons_self

/-- *Shape 4 worked example* — `SameAs(a, b)` via `gci {a} ⊑ {b}`.

    Asserts that two named individuals are equal.  By `Sat.nom_symm`,
    we also derive the converse direction. -/
def shape4_O : Ontology := [Axiom.gci (.nom 0) (.nom 1)]

theorem shape4_axiom_merge : OntologyMerge shape4_O := by
  intro ax hax
  simp [shape4_O] at hax
  subst hax
  exact ⟨Shallow.nom 0, Shallow.nom 1⟩

/-- Forward direction: `{0} ⊑ {1}` from the axiom. -/
theorem shape4_sat_forward : Sat shape4_O (.nom 0) (.nom 1) :=
  Sat.base_gci List.mem_cons_self

/-- Reverse direction: `{1} ⊑ {0}` via `Sat.nom_symm`.  This is
    new in this layer — the standard ELK calculus could not derive
    it without the merging-symm rule. -/
theorem shape4_sat_reverse : Sat shape4_O (.nom 1) (.nom 0) :=
  Sat.nom_symm shape4_sat_forward

/-- *Shape 2 + 4 combined* — class to individual and equating
    individuals.  Demonstrates the full merging quotient: `Pope`-
    instances are forced to equal `a_0`, and `a_0 = a_1`, so
    `Pope`-instances are forced to equal `a_1`. -/
def shape24_O : Ontology :=
  [Axiom.gci (.atom 0) (.nom 0),
   Axiom.gci (.nom 0) (.nom 1)]

theorem shape24_axiom_merge : OntologyMerge shape24_O := by
  intro ax hax
  simp [shape24_O] at hax
  rcases hax with h | h
  all_goals (subst h; first | exact ⟨Shallow.atom 0, Shallow.nom 0⟩
                            | exact ⟨Shallow.nom 0, Shallow.nom 1⟩)

/-- The chained derivation: `Pope ⊑ {a_1}` via the shape-2 axiom
    composed with the shape-4 axiom. -/
theorem shape24_chain : Sat shape24_O (.atom 0) (.nom 1) := by
  have h1 : Sat shape24_O (.atom 0) (.nom 0) :=
    Sat.base_gci List.mem_cons_self
  have h2 : Sat shape24_O (.nom 0) (.nom 1) :=
    Sat.base_gci (List.mem_cons.mpr (Or.inr List.mem_cons_self))
  exact Sat.trans h1 h2

/-- *HasKey worked example* — a primary key on `Email` for `User`.

    `O = { hasKey User [hasEmail], gci {alice} User, gci {bob} User,
           gci {alice} (∃hasEmail.{e}), gci {bob} (∃hasEmail.{e}) }`

    Reading: alice and bob are both Users, and both have email `e`.
    HasKey(User, [hasEmail]) says email is a key for User, so
    alice = bob.  Concept names: `User = atom 0`, `hasEmail = role 0`.
    Individuals: `alice = nom 0`, `bob = nom 1`, `e = nom 2`. -/
def hasKey_O : Ontology :=
  [ Axiom.hasKey (.atom 0) [0],
    Axiom.gci (.nom 0) (.atom 0),
    Axiom.gci (.nom 1) (.atom 0),
    Axiom.gci (.nom 0) (.exist 0 (.nom 2)),
    Axiom.gci (.nom 1) (.exist 0 (.nom 2)) ]

theorem hasKey_axiom_merge : OntologyMerge hasKey_O := by
  intro ax hax
  simp [hasKey_O] at hax
  rcases hax with h | h | h | h | h
  · subst h; exact Shallow.atom 0
  · subst h; exact ⟨Shallow.nom 0, Shallow.atom 0⟩
  · subst h; exact ⟨Shallow.nom 1, Shallow.atom 0⟩
  · subst h; exact ⟨Shallow.nom 0, Shallow.exist_nom 0 2⟩
  · subst h; exact ⟨Shallow.nom 1, Shallow.exist_nom 0 2⟩

/-- HasKey forces `alice = bob` — Sat O {alice} ⊑ {bob}.

    Combines the four GCIs with `Sat.hasKey_apply`: alice and bob
    are both in `User`, and both have email `e`, so the HasKey axiom
    fires and merges them. -/
theorem hasKey_merges : Sat hasKey_O (.nom 0) (.nom 1) := by
  -- Class memberships.
  have h_aliceUser : Sat hasKey_O (.nom 0) (.atom 0) :=
    Sat.base_gci (by simp [hasKey_O])
  have h_bobUser : Sat hasKey_O (.nom 1) (.atom 0) :=
    Sat.base_gci (by simp [hasKey_O])
  -- Email-edges.
  have h_aliceEmail : Sat hasKey_O (.nom 0) (.exist 0 (.nom 2)) :=
    Sat.base_gci (by simp [hasKey_O])
  have h_bobEmail : Sat hasKey_O (.nom 1) (.exist 0 (.nom 2)) :=
    Sat.base_gci (by simp [hasKey_O])
  -- HasKey axiom membership.
  have h_hk : Axiom.hasKey (.atom 0) [0] ∈ hasKey_O := by simp [hasKey_O]
  -- Skolem witness function: every role maps to email-target = 2.
  let cs : Role → Nat := fun _ => 2
  -- Apply Sat.hasKey_apply.
  exact Sat.hasKey_apply (rs := [0]) cs h_aliceUser h_bobUser h_hk
    (fun R hR => by
      simp at hR
      subst hR; exact h_aliceEmail)
    (fun R hR => by
      simp at hR
      subst hR; exact h_bobEmail)

/-- By `Sat.nom_symm`, `bob = alice` is also derivable. -/
theorem hasKey_symm : Sat hasKey_O (.nom 1) (.nom 0) :=
  Sat.nom_symm hasKey_merges

end Examples

-- ============================================================
-- 12. Axiom audit
-- ============================================================
--
-- All theorems in this layer use only Lean's foundational axioms:
-- `propext`, `Classical.choice`, `Quot.sound`.  No `sorry`s, no
-- additional Mathlib or third-party axioms.

#print axioms Sat.nom_symm                            -- Sat constructor (no axioms)
#print axioms nomCls_eq_iff                           -- propext, Quot.sound
#print axioms merged_canon_eval                       -- propext, Quot.sound, Classical.choice
#print axioms mergedCanon_satisfies                   -- propext, Quot.sound, Classical.choice
#print axioms complete_via_mergedCanon_regular        -- propext, Quot.sound, Classical.choice
#print axioms complete_via_mergedCanon_nom            -- propext, Quot.sound, Classical.choice
#print axioms Examples.shape2_sat                     -- (no axioms)
#print axioms Examples.shape4_sat_reverse             -- (no axioms — uses nom_symm)
#print axioms Examples.shape24_chain                  -- (no axioms)
#print axioms Examples.hasKey_merges                  -- (no axioms — uses hasKey_apply)
#print axioms Examples.hasKey_symm                    -- (no axioms — adds nom_symm)

end ELpp
end ELKSDD
