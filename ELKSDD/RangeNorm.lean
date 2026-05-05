/-
  ELKSDD/RangeNorm.lean
  ---------------------
  Path B of OWL 2 EL Range completeness in Lean: BBL 2008 §3.3
  fresh-atom range-restriction elimination as a syntactic
  pre-processing pass, followed by sorry-free
  `complete_via_canon_strict` on the eliminated ontology.

  References:
    [BBL 2008]  Baader, F., Brandt, S., Lutz, C.
                Pushing the EL Envelope Further.
                Proceedings of OWLED 2008 DC, §3.3.

  Encoding (BBL 2008 §3.3):
    * For each role `R` with `Range R E ∈ O`, allocate a fresh atom
      `A_R := rangeMarker O R`.
    * Replace every existential `∃R.E` on the *right-hand side* of
      a GCI with `∃R.(E ⊓ A_R)` (i.e., target witness must be in A_R).
    * Add `A_R ⊑ E` GCIs for every original `Range R E` axiom.
    * Drop the original `Range R E` axioms.

  After this transformation, the resulting ontology
  `eliminateRanges O` has no range axioms.  Combined with
  `OntologyNominalFree O` on the input, the output is `OntologyStrict`,
  so the sorry-free `complete_via_canon_strict` (in `ELpp.lean`)
  applies.

  Conservativity (proved with sorrys for the inductive bodies; the
  shape of the argument is well-known and is sketched in the
  comments):
    * `Sat_to_eliminated`     — Sat O X Y ⇒ Sat O' X' Y' (X', Y' are
                                marker-decorated translations of X, Y).
    * `Sat_from_eliminated`   — Sat O' X Y ⇒ Sat O X Y for marker-free
                                X, Y in O's signature.
    * `Entails_to_eliminated` — semantic forward.
    * `complete_via_canon_owl2el` — full OWL 2 EL completeness via
                                Path B reduction (modulo HasKey + nominals,
                                which still need Kazakov 2014 §6 merging).
-/

import ELKSDD.ELpp
import ELKSDD.Normalize

namespace ELKSDD
namespace RangeNorm

open ELpp

-- ============================================================
-- 1. Fresh-atom assignment
-- ============================================================

/-- The fresh marker atom for role `R` w.r.t. ontology `O`.

    Using `Normalize.freshAtomFor O + R + 1` ensures:
    (i) the marker is strictly greater than any atom in `O`
        (since `freshAtomFor O = 1 + max(ontologyAtoms O)`); and
    (ii) markers for distinct roles are distinct
        (since `R + 1` is injective in `R`). -/
def rangeMarker (O : Ontology) (R : Role) : Nat :=
  Normalize.freshAtomFor O + R + 1

/-- Marker is fresh w.r.t. the original ontology's atoms.

    Argument: every `n ∈ ontologyAtoms O` has `n < freshAtomFor O`
    (by `Normalize.mem_ontologyAtoms_lt_freshAtomFor`).
    `rangeMarker O R = freshAtomFor O + R + 1 > freshAtomFor O > n`. -/
theorem rangeMarker_fresh (O : Ontology) (R : Role) :
    rangeMarker O R ∉ Normalize.ontologyAtoms O := by
  intro h
  have hbound := Normalize.mem_ontologyAtoms_lt_freshAtomFor O _ h
  unfold rangeMarker at hbound
  omega

/-- Different roles yield different markers. -/
theorem rangeMarker_inj (O : Ontology) {R S : Role} :
    rangeMarker O R = rangeMarker O S → R = S := by
  intro h
  unfold rangeMarker at h
  -- h : freshAtomFor O + R + 1 = freshAtomFor O + S + 1
  have h1 : Normalize.freshAtomFor O + R = Normalize.freshAtomFor O + S :=
    Nat.add_right_cancel h
  exact Nat.add_left_cancel h1

-- ============================================================
-- 2. Range-axiom predicate (decidable)
-- ============================================================

/-- Does role `R` have at least one range axiom in `O`? -/
def hasRange : Ontology → Role → Bool
  | [], _ => false
  | (.range R' _) :: rest, R =>
      decide (R = R') || hasRange rest R
  | _ :: rest, R => hasRange rest R

theorem hasRange_iff (O : Ontology) (R : Role) :
    hasRange O R = true ↔ ∃ E, Axiom.range R E ∈ O := by
  induction O with
  | nil =>
      constructor
      · intro h; cases h
      · intro ⟨_, hE⟩; exact (List.not_mem_nil hE).elim
  | cons ax rest ih =>
      cases ax with
      | range R' E' =>
          constructor
          · intro h
            -- h : (decide (R = R') || hasRange rest R) = true
            simp only [hasRange, Bool.or_eq_true, decide_eq_true_eq] at h
            rcases h with hRR' | hRest
            · subst hRR'
              exact ⟨E', List.mem_cons_self⟩
            · obtain ⟨E, hE⟩ := ih.mp hRest
              exact ⟨E, List.mem_cons.mpr (Or.inr hE)⟩
          · intro ⟨E, hE⟩
            simp only [hasRange, Bool.or_eq_true, decide_eq_true_eq]
            rcases List.mem_cons.mp hE with hEq | hRest
            · injection hEq with hRR' _
              subst hRR'
              exact Or.inl rfl
            · exact Or.inr (ih.mpr ⟨E, hRest⟩)
      | gci _ _ =>
          constructor
          · intro h
            simp only [hasRange] at h
            obtain ⟨E, hE⟩ := ih.mp h
            exact ⟨E, List.mem_cons.mpr (Or.inr hE)⟩
          · intro ⟨E, hE⟩
            simp only [hasRange]
            rcases List.mem_cons.mp hE with hEq | hRest
            · cases hEq
            · exact ih.mpr ⟨E, hRest⟩
      | rinc _ _ =>
          constructor
          · intro h
            simp only [hasRange] at h
            obtain ⟨E, hE⟩ := ih.mp h
            exact ⟨E, List.mem_cons.mpr (Or.inr hE)⟩
          · intro ⟨E, hE⟩
            simp only [hasRange]
            rcases List.mem_cons.mp hE with hEq | hRest
            · cases hEq
            · exact ih.mpr ⟨E, hRest⟩
      | rchain _ _ _ =>
          constructor
          · intro h
            simp only [hasRange] at h
            obtain ⟨E, hE⟩ := ih.mp h
            exact ⟨E, List.mem_cons.mpr (Or.inr hE)⟩
          · intro ⟨E, hE⟩
            simp only [hasRange]
            rcases List.mem_cons.mp hE with hEq | hRest
            · cases hEq
            · exact ih.mpr ⟨E, hRest⟩
      | reflexive _ =>
          constructor
          · intro h
            simp only [hasRange] at h
            obtain ⟨E, hE⟩ := ih.mp h
            exact ⟨E, List.mem_cons.mpr (Or.inr hE)⟩
          · intro ⟨E, hE⟩
            simp only [hasRange]
            rcases List.mem_cons.mp hE with hEq | hRest
            · cases hEq
            · exact ih.mpr ⟨E, hRest⟩
      | hasKey _ _ =>
          constructor
          · intro h
            simp only [hasRange] at h
            obtain ⟨E, hE⟩ := ih.mp h
            exact ⟨E, List.mem_cons.mpr (Or.inr hE)⟩
          · intro ⟨E, hE⟩
            simp only [hasRange]
            rcases List.mem_cons.mp hE with hEq | hRest
            · cases hEq
            · exact ih.mpr ⟨E, hRest⟩

-- ============================================================
-- 3. Concept and axiom modification
-- ============================================================

/-- Modify a concept syntactically: add the range marker `A_R` to
    every existential `∃R.E` whose role has range axioms in `O`.

    Only RHS-style existentials (in axiom right-hand sides) need
    modification; we apply this recursively wherever it descends.
    For atomic queries `X ⊑ Y` (the typical use case), modification
    is identity since X, Y are atoms. -/
def modifyConcept (O : Ontology) : Concept → Concept
  | .atom n => .atom n
  | .nom i => .nom i
  | .self R => .self R
  | .top => .top
  | .bot => .bot
  | .conj A B => .conj (modifyConcept O A) (modifyConcept O B)
  | .exist R E =>
      let E' := modifyConcept O E
      if hasRange O R = true then
        .exist R (.conj E' (.atom (rangeMarker O R)))
      else
        .exist R E'

/-- Modify an axiom: drop range axioms; modify the right-hand side of
    GCIs; leave others alone (HasKey is not handled here — it stays
    in the ontology and remains gated separately). -/
def modifyAxiom (O : Ontology) : Axiom → Option Axiom
  | .gci C D       => some (.gci C (modifyConcept O D))
  | .rinc R S      => some (.rinc R S)
  | .rchain R₁ R₂ S => some (.rchain R₁ R₂ S)
  | .range _ _     => none
  | .reflexive R   => some (.reflexive R)
  | .hasKey C rs   => some (.hasKey C rs)

/-- Generated marker-axioms: `A_R ⊑ E` for each `Range R E ∈ O`.
    Markers are computed w.r.t. the full original O (filterMap closes
    over O) so they are consistent across the whole transformation. -/
def markerAxioms (O : Ontology) : Ontology :=
  O.filterMap (fun ax => match ax with
    | .range R E => some (.gci (.atom (rangeMarker O R)) E)
    | _ => none)

/-- The full BBL 2008 §3.3 normalization. -/
def eliminateRanges (O : Ontology) : Ontology :=
  O.filterMap (modifyAxiom O) ++ markerAxioms O

-- ============================================================
-- 4. Structural properties of `eliminateRanges`
-- ============================================================

/-- `modifyConcept` preserves `NominalFree`: the only addition is
    the atom `A_R`, which is itself nominal-free. -/
theorem modifyConcept_NominalFree (O : Ontology) (C : Concept)
    (h : NominalFree C) : NominalFree (modifyConcept O C) := by
  induction C with
  | atom _ => exact h
  | nom _ => exact h.elim
  | self _ => exact h.elim
  | top => exact h
  | bot => exact h
  | conj A B ihA ihB =>
      obtain ⟨hA, hB⟩ := h
      exact ⟨ihA hA, ihB hB⟩
  | exist R E ihE =>
      simp only [modifyConcept]
      by_cases hR : hasRange O R = true
      · simp [hR]
        exact ⟨ihE h, trivial⟩
      · simp [hR]
        exact ihE h

/-- Helper: `markerAxioms` produces only GCI axioms (never range). -/
theorem markerAxioms_no_range (O : Ontology) :
    ∀ R E, Axiom.range R E ∉ markerAxioms O := by
  intro R E hMem
  unfold markerAxioms at hMem
  rw [List.mem_filterMap] at hMem
  obtain ⟨origAx, _, hOpt⟩ := hMem
  cases origAx with
  | range _ _ => simp at hOpt
  | gci _ _ => simp at hOpt
  | rinc _ _ => simp at hOpt
  | rchain _ _ _ => simp at hOpt
  | reflexive _ => simp at hOpt
  | hasKey _ _ => simp at hOpt

/-- Helper: `modifyAxiom` never produces a range axiom (it drops
    `range` and produces non-range axiom kinds for others). -/
theorem modifyAxiom_no_range (O : Ontology) (ax : Axiom) :
    ∀ R E, modifyAxiom O ax ≠ some (Axiom.range R E) := by
  intro R E
  cases ax with
  | gci _ _      => intro h; cases h
  | rinc _ _     => intro h; cases h
  | rchain _ _ _ => intro h; cases h
  | range _ _    => intro h; cases h
  | reflexive _  => intro h; cases h
  | hasKey _ _   => intro h; cases h

/-- `eliminateRanges` produces no range axioms. -/
theorem eliminateRanges_no_range (O : Ontology) :
    ∀ R E, Axiom.range R E ∉ eliminateRanges O := by
  intro R E hMem
  unfold eliminateRanges at hMem
  rcases List.mem_append.mp hMem with hLeft | hRight
  · rw [List.mem_filterMap] at hLeft
    obtain ⟨origAx, _, hMod⟩ := hLeft
    exact modifyAxiom_no_range O origAx R E hMod
  · exact markerAxioms_no_range O R E hRight

/-- Under `OntologyNominalFree`, `eliminateRanges` produces an
    `OntologyStrict` ontology (no range, no hasKey, GCIs nominal-free).

    HasKey: if O contains a hasKey axiom, `OntologyNominalFree O` is
    False (because `AxiomNominalFree (.hasKey _ _) = False`); so this
    precondition rules HasKey out of consideration here.  -/
theorem eliminateRanges_strict (O : Ontology)
    (hO : OntologyNominalFree O) : OntologyStrict (eliminateRanges O) := by
  intro ax hax
  unfold eliminateRanges at hax
  rcases List.mem_append.mp hax with hLeft | hRight
  · -- ax came from filterMap (modifyAxiom O)
    rw [List.mem_filterMap] at hLeft
    obtain ⟨origAx, hOrigIn, hMod⟩ := hLeft
    have hOrigNF : AxiomNominalFree origAx := hO origAx hOrigIn
    cases origAx with
    | gci C D =>
        simp [modifyAxiom] at hMod
        subst hMod
        obtain ⟨hC_nf, hD_nf⟩ := hOrigNF
        exact ⟨hC_nf, modifyConcept_NominalFree O D hD_nf⟩
    | rinc R S =>
        simp [modifyAxiom] at hMod
        subst hMod
        trivial
    | rchain R₁ R₂ S =>
        simp [modifyAxiom] at hMod
        subst hMod
        trivial
    | range _ _ =>
        -- modifyAxiom returns none for range; hMod : none = some _.
        simp [modifyAxiom] at hMod
    | reflexive R =>
        simp [modifyAxiom] at hMod
        subst hMod
        trivial
    | hasKey _ _ =>
        -- AxiomNominalFree (.hasKey _ _) = False
        exact hOrigNF.elim
  · -- ax came from markerAxioms O: it's a gci of the form `gci (atom (rangeMarker O R)) E` for Range R E ∈ O.
    unfold markerAxioms at hRight
    rw [List.mem_filterMap] at hRight
    obtain ⟨origAx, hOrigIn, hOpt⟩ := hRight
    have hOrigNF : AxiomNominalFree origAx := hO origAx hOrigIn
    cases origAx with
    | gci _ _ => simp at hOpt
    | rinc _ _ => simp at hOpt
    | rchain _ _ _ => simp at hOpt
    | range R' E' =>
        simp at hOpt
        subst hOpt
        -- ax = gci (atom (rangeMarker O R')) E'.  AxiomStrict needs
        -- NominalFree (atom _) ∧ NominalFree E'.  First is trivial.
        -- Second: from AxiomNominalFree (.range R' E') = NominalFree E'.
        exact ⟨trivial, hOrigNF⟩
    | reflexive _ => simp at hOpt
    | hasKey _ _ => simp at hOpt

-- ============================================================
-- 5. Sat conservativity (forward / soundness of encoding)
-- ============================================================

/-- **Forward conservativity** (Sat O ⇒ Sat O').

    Every `Sat O X Y` derivation in the original ontology has a
    corresponding `Sat O' (modifyConcept O X) (modifyConcept O Y)`
    derivation in the eliminated ontology.  In particular, the
    `range_apply` rule's effect is recovered via `Sat.exist_prop`
    + `Sat.conj_left`/`Sat.conj_right` chains through the modified
    existentials' marker conjunct and the marker subsumption
    `A_R ⊑ E`.

    The proof is by induction on the `Sat O` derivation, with one
    case per constructor.  The non-trivial case is `range_apply`,
    which uses the marker GCI `A_R ⊑ E ∈ markerAxioms O` to refine
    the modified existential's witness.

    *Future Lean work:* the case-by-case Sat translation
    (~150 lines).  -/
theorem Sat_to_eliminated {O : Ontology} {X Y : Concept}
    (h : Sat O X Y) :
    Sat (eliminateRanges O) (modifyConcept O X) (modifyConcept O Y) := by
  sorry

/-- **Helper for `Sat_to_eliminated` (sorry-free).**

    `modifyConcept` only ADDS markers (as right conjuncts of existential
    fillers).  Therefore the modified concept is always subsumed by
    the original, in O' (not O — markers don't exist in O):

        Sat (eliminateRanges O) (modifyConcept O C) C

    Proof by structural induction on `C`.  The interesting case is
    `exist R E`: when `hasRange O R = true`, the modified concept is
    `exist R (conj (modifyConcept E) (atom (rangeMarker O R)))`, and
    we project away the marker via `Sat.conj_left` and recurse on `E`.
    When `hasRange O R = false`, the modification is just on the
    inner `E`, handled by induction.

    This helper is used in the future Lean proof of `Sat_to_eliminated`
    to bridge the LHS of `base_gci` (modified-axiom application gives
    `Sat O' C (modifyConcept D)` but we need `Sat O' (modifyConcept C)
    (modifyConcept D)`; bridge via `Sat_modify_imp_orig` + `Sat.trans`). -/
theorem Sat_modify_imp_orig (O : Ontology) (C : Concept) :
    Sat (eliminateRanges O) (modifyConcept O C) C := by
  induction C with
  | atom n => exact Sat.refl _
  | nom i => exact Sat.refl _
  | self R => exact Sat.refl _
  | top => exact Sat.refl _
  | bot => exact Sat.refl _
  | conj A B ihA ihB =>
      -- modifyConcept (conj A B) = conj (modifyConcept A) (modifyConcept B)
      -- want Sat O' (conj _ _) (conj A B), via conj_intro of ihA composed and ihB composed
      apply Sat.conj_intro
      · exact Sat.trans (Sat.conj_left (Sat.refl _)) ihA
      · exact Sat.trans (Sat.conj_right (Sat.refl _)) ihB
  | exist R E ihE =>
      simp only [modifyConcept]
      by_cases hR : hasRange O R = true
      · simp [hR]
        -- Goal: Sat O' (.exist R (.conj (modifyConcept E) (atom marker))) (.exist R E)
        -- Sat.exist_prop: from refl + (conj_left ; ihE)
        refine Sat.exist_prop (Sat.refl _) ?_
        exact Sat.trans (Sat.conj_left (Sat.refl _)) ihE
      · simp [hR]
        -- Goal: Sat O' (.exist R (modifyConcept E)) (.exist R E)
        exact Sat.exist_prop (Sat.refl _) ihE

-- ============================================================
-- 6. Sat conservativity (backward — projection)
-- ============================================================

/-- A concept *uses no marker*: contains no atom of the form
    `rangeMarker O _`.  Concepts in O's original signature satisfy
    this; in particular, atomic queries `X = atom A` for `A ∈ ontologyAtoms O`
    do not collide with markers (since markers are `> max(ontologyAtoms O)`). -/
def MarkerFree (O : Ontology) : Concept → Prop
  | .atom n => ∀ R, n ≠ rangeMarker O R
  | .nom _ => True
  | .self _ => True
  | .top => True
  | .bot => True
  | .conj A B => MarkerFree O A ∧ MarkerFree O B
  | .exist _ E => MarkerFree O E

/-- For marker-free `X`, `modifyConcept O X = X` is *not* an identity
    (existentials get markers if their role has ranges).  Instead:
    `modifyConcept` only adds markers, doesn't remove or rename.
    So `modifyConcept O X` always uses markers; the converse direction
    of conservativity therefore needs a substitution `unMarker`.

    *Stub:* the full implementation requires `findMarkerRole : Nat →
    Option Role` to invert `rangeMarker O`, then substitute
    `atom (rangeMarker O R) ↦ ⊓ {E : Range R E ∈ O}`.  Future work. -/
def unMarker (_O : Ontology) : Concept → Concept
  | C => C

/-- **Backward conservativity** (Sat O' ⇒ Sat O for marker-free queries).

    Given `Sat (eliminateRanges O) X Y` for `X`, `Y` *marker-free*,
    we recover `Sat O X Y` by translating the derivation: marker
    atoms `A_R` become `⊓ E_i` (conjunction of R's range concepts),
    and modified existentials project via `Sat.conj_left`.

    *Future Lean work:* full Sat-translation by case on the
    derivation (~200 lines).  -/
theorem Sat_from_eliminated {O : Ontology} {X Y : Concept}
    (hX_mf : MarkerFree O X) (hY_mf : MarkerFree O Y)
    (h : Sat (eliminateRanges O) X Y) : Sat O X Y := by
  sorry

-- ============================================================
-- 7. Semantic conservativity (Entails preserved)
-- ============================================================

/-- **Semantic forward** (Entails O ⇒ Entails O').

    Every model of O extends to a model of `eliminateRanges O` by
    interpreting `A_R` as `⋂ {E : Range R E ∈ O}` (the conjunction
    of R's range concepts).  Then the modified existentials are
    satisfied because R-targets in the original model are in `A_R`
    by the Range axioms.

    *Future Lean work:* model-extension construction (~100 lines). -/
theorem Entails_to_eliminated {O : Ontology} {X Y : Concept}
    (h : Entails O X Y) :
    Entails (eliminateRanges O) (modifyConcept O X) (modifyConcept O Y) := by
  sorry

-- ============================================================
-- 8. Path-B completeness theorem
-- ============================================================

/-- **OWL 2 EL completeness via Path B (BBL 2008 §3.3 reduction).**

    Strategy:
      1. By `Entails_to_eliminated`, `O ⊨ X ⊑ Y` lifts to
         `O' ⊨ X' ⊑ Y'` where `O' = eliminateRanges O`,
         `X' = modifyConcept O X`, `Y' = modifyConcept O Y`.
      2. By `eliminateRanges_strict`, `O'` satisfies `OntologyStrict`.
      3. By `complete_via_canon_strict` (sorry-free!), `Sat O' X' Y'`.
      4. By `Sat_from_eliminated` (marker-free X, Y), `Sat O X Y`.

    Coverage: the `OntologyNominalFree` precondition rules out
    `hasKey` and nominal axioms, but allows full Range and
    Reflexive coverage with arbitrary role hierarchy and chains.

    The remaining four sorrys (`rangeMarker_fresh` arithmetic,
    `eliminateRanges_no_range`, `eliminateRanges_strict`,
    `Sat_to_eliminated`, `Sat_from_eliminated`, `Entails_to_eliminated`)
    are clearly-scoped routine inductions/case-splits.  Each is
    documented above with its argument shape; closing them is a
    bounded engineering task.

    HasKey + nominals + Self-as-query-target remain genuinely deferred
    to the merging canonical model of Kazakov 2014 §6. -/
theorem complete_via_canon_owl2el (O : Ontology) (X Y : Concept)
    (hO_nf : OntologyNominalFree O)
    (hX_nf : NominalFree X) (hY_nf : NominalFree Y)
    (hX_mf : MarkerFree O X) (hY_mf : MarkerFree O Y)
    (h : Entails O X Y) : Sat O X Y := by
  -- Step 1: lift to eliminated ontology semantically.
  have h' : Entails (eliminateRanges O) (modifyConcept O X) (modifyConcept O Y) :=
    Entails_to_eliminated h
  -- Step 2: eliminated ontology is strict.
  have hO'_strict : OntologyStrict (eliminateRanges O) :=
    eliminateRanges_strict O hO_nf
  -- Step 3: modified concepts are nominal-free.
  have hX'_nf : NominalFree (modifyConcept O X) := modifyConcept_NominalFree O X hX_nf
  have hY'_nf : NominalFree (modifyConcept O Y) := modifyConcept_NominalFree O Y hY_nf
  -- Step 4: apply sorry-free strict completeness.
  have hSat' : Sat (eliminateRanges O) (modifyConcept O X) (modifyConcept O Y) :=
    complete_via_canon_strict (eliminateRanges O) _ _ hO'_strict hX'_nf hY'_nf h'
  -- Step 5: translate back to Sat O via Sat_from_eliminated.
  -- Sat_from_eliminated needs marker-free X, Y; we have those.
  -- But it's stated on Sat O' X Y, with X = modifyConcept O X here.
  -- For atomic X (the typical case), modifyConcept O X = X, so this works.
  -- For non-atomic X with existentials, we'd need a slightly stronger lemma
  -- relating Sat O' (modifyConcept O X) Y' to Sat O X Y.  For atomic X, Y
  -- (the most common application — atom-atom subsumption queries),
  -- modifyConcept is identity so we apply Sat_from_eliminated directly.
  sorry  -- Future work: full lifting for non-atomic X, Y.

-- ============================================================
-- 9. Atomic-query specialisation (typical use)
-- ============================================================

/-- For atomic-atomic queries, `modifyConcept` is identity, so the
    Path-B reduction simplifies. -/
theorem modifyConcept_atom (O : Ontology) (n : Nat) :
    modifyConcept O (.atom n) = .atom n := rfl

/-- **Atomic-query specialisation of Path B.**

    The most common subsumption query: `O ⊨ atom A ⊑ atom B`.
    Here `modifyConcept` is identity on both sides, so the
    Path-B reduction is fully structural:

      `complete_via_canon_owl2el_atom` =
        `Sat_from_eliminated` ∘ `complete_via_canon_strict` ∘
        `eliminateRanges_strict` ∘ `Entails_to_eliminated`.

    All but the conservativity-direction sorrys (`Sat_from_eliminated`,
    `Entails_to_eliminated`) are sorry-free here.  -/
theorem complete_via_canon_owl2el_atom (O : Ontology) (A B : Nat)
    (hO_nf : OntologyNominalFree O)
    (hA_mf : MarkerFree O (.atom A)) (hB_mf : MarkerFree O (.atom B))
    (h : Entails O (.atom A) (.atom B)) : Sat O (.atom A) (.atom B) := by
  -- Step 1: semantic lift.  modifyConcept on atoms is definitionally
  -- the identity, so the lifted Entails has the same atomic shape.
  have h' : Entails (eliminateRanges O) (.atom A) (.atom B) :=
    Entails_to_eliminated h
  -- Step 2: strict.
  have hStrict : OntologyStrict (eliminateRanges O) :=
    eliminateRanges_strict O hO_nf
  -- Step 3: sorry-free completeness on the strict (range-free)
  -- eliminated ontology.
  have hSat' : Sat (eliminateRanges O) (.atom A) (.atom B) :=
    complete_via_canon_strict (eliminateRanges O) _ _ hStrict trivial trivial h'
  -- Step 4: project back via Sat_from_eliminated (marker-free atoms).
  exact Sat_from_eliminated hA_mf hB_mf hSat'

/-- Atomic queries trivially have `MarkerFree`: an `atom n` is a
    marker iff `n = rangeMarker O R` for some `R`, which we exclude
    by hypothesis on the query atoms (typically: `n ∈ ontologyAtoms O`,
    so `n` is bounded below the marker offset). -/
theorem atom_MarkerFree_of_in_O {O : Ontology} {n : Nat}
    (h : n ∈ Normalize.ontologyAtoms O) : MarkerFree O (.atom n) := by
  intro R hEq
  -- hEq : n = rangeMarker O R = freshAtomFor O + R + 1.
  -- But h says n is in ontologyAtoms O, hence n < freshAtomFor O.
  have hbound := Normalize.mem_ontologyAtoms_lt_freshAtomFor O n h
  unfold rangeMarker at hEq
  omega

end RangeNorm
end ELKSDD
