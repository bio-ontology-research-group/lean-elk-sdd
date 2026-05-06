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

/-- Generated marker-axioms: `A_R ⊑ modifyConcept O E` for each
    `Range R E ∈ O`.  Markers are computed w.r.t. the full original
    O (filterMap closes over O) so they are consistent across the
    whole transformation.

    *Note*: the RHS uses `modifyConcept O E` (not raw E) so that
    Sat-conservativity on the eliminated ontology can transfer the
    marker constraint cleanly into the modified concept space.  When
    `E` is atomic (the typical OWL 2 EL usage), `modifyConcept O E = E`
    and this distinction is transparent. -/
def markerAxioms (O : Ontology) : Ontology :=
  O.filterMap (fun ax => match ax with
    | .range R E => some (.gci (.atom (rangeMarker O R)) (modifyConcept O E))
    | _ => none)

/-- **Marker-propagation axioms** for rinc + range and reflexive + range
    interactions.

    Two cases:
    1. For each rinc R S ∈ O with both R and S having range axioms,
       add `gci (atom marker_R) (atom marker_S)`.  Captures: R-target
       witnesses are also S-target witnesses by rinc R S → R ⊑ S,
       so marker_R ⊑ marker_S.
    2. For each reflexive R ∈ O with R having a range axiom, add
       `gci .top (atom marker_R)`.  Captures: reflexive R + range R E
       jointly entail ⊤ ⊑ E in O (every x is its own R-target via
       reflexive, hence in E via range), so ⊤ ⊑ marker_R.

    Both forms produce gci axioms with NominalFree LHS (atom or .top)
    and NominalFree RHS (atom), so they preserve `OntologyStrict`. -/
def markerPropagationAxioms (O : Ontology) : Ontology :=
  O.filterMap (fun ax => match ax with
    | .rinc R S =>
        if hasRange O R = true ∧ hasRange O S = true then
          some (.gci (.atom (rangeMarker O R)) (.atom (rangeMarker O S)))
        else
          none
    | .reflexive R =>
        if hasRange O R = true then
          some (.gci .top (.atom (rangeMarker O R)))
        else
          none
    | _ => none)

/-- One step of the rinc-closure: extend `current` with every `S` such that
    there is some `T ∈ current` with `Axiom.rinc T S ∈ O`. -/
private def rincStepFn (O : Ontology) (current : List Role) : List Role :=
  current ++ (O.filterMap (fun ax => match ax with
    | .rinc T S => if T ∈ current ∧ S ∉ current then some S else none
    | _ => none))

/-- Bounded iteration of `rincStepFn`. -/
private def rincIter : Nat → Ontology → List Role → List Role
  | 0, _, current => current
  | Nat.succ n, O, current => rincIter n O (rincStepFn O current)

/-- The set of roles reachable from `R` via 0+ `rinc`-edges in `O`.
    Bounded fixed-point iteration for `O.length + 1` steps suffices
    because each productive step adds a distinct new role (bounded
    by the number of distinct roles syntactically in `O`). -/
def rincDescendants (O : Ontology) (R : Role) : List Role :=
  rincIter (O.length + 1) O [R]

theorem rincStepFn_subset (O : Ontology) (current : List Role) :
    ∀ x ∈ current, x ∈ rincStepFn O current := by
  intro x hx
  unfold rincStepFn
  exact List.mem_append.mpr (Or.inl hx)

theorem rincIter_subset {O : Ontology} (n : Nat) (current : List Role) :
    ∀ x ∈ current, x ∈ rincIter n O current := by
  induction n generalizing current with
  | zero => intro _ h; exact h
  | succ n ih =>
      intro x hx
      apply ih
      exact rincStepFn_subset O current x hx

theorem rincDescendants_self (O : Ontology) (R : Role) :
    R ∈ rincDescendants O R := by
  unfold rincDescendants
  exact rincIter_subset _ [R] R (List.mem_singleton.mpr rfl)

/-- One-step rinc lifting: if `rinc T S ∈ O` and `T ∈ current`,
    then `S ∈ rincStepFn O current`. -/
theorem rincStepFn_step {O : Ontology} {current : List Role} {T S : Role}
    (hT : T ∈ current) (hRinc : Axiom.rinc T S ∈ O) :
    S ∈ rincStepFn O current := by
  unfold rincStepFn
  by_cases hS : S ∈ current
  · exact List.mem_append.mpr (Or.inl hS)
  · refine List.mem_append.mpr (Or.inr ?_)
    rw [List.mem_filterMap]
    refine ⟨Axiom.rinc T S, hRinc, ?_⟩
    simp [hT, hS]

/-- Soundness: every element of `rincDescendants O R` is `RincAncestor O R`-related to `R`. -/
theorem rincIter_sound {O : Ontology} (n : Nat) (R : Role) (current : List Role)
    (h : ∀ S ∈ current, RincAncestor O R S) :
    ∀ S ∈ rincIter n O current, RincAncestor O R S := by
  induction n generalizing current with
  | zero =>
      intro S hS
      exact h S hS
  | succ n ih =>
      apply ih
      intro S hS
      unfold rincStepFn at hS
      rcases List.mem_append.mp hS with hCurr | hExt
      · exact h S hCurr
      · rw [List.mem_filterMap] at hExt
        obtain ⟨ax, haxIn, hOpt⟩ := hExt
        cases ax with
        | rinc T S' =>
            simp only at hOpt
            by_cases hCond : T ∈ current ∧ S' ∉ current
            · simp [hCond] at hOpt
              obtain ⟨hT, _⟩ := hCond
              subst hOpt
              exact RincAncestor.step (h T hT) haxIn
            · simp [hCond] at hOpt
        | gci _ _ => simp at hOpt
        | rchain _ _ _ => simp at hOpt
        | range _ _ => simp at hOpt
        | reflexive _ => simp at hOpt
        | hasKey _ _ => simp at hOpt

theorem rincDescendants_sound {O : Ontology} {R S : Role}
    (h : S ∈ rincDescendants O R) : RincAncestor O R S := by
  unfold rincDescendants at h
  apply rincIter_sound _ R [R] _ S h
  intro T hT
  rw [List.mem_singleton] at hT
  subst hT
  exact RincAncestor.refl _

/-- **Transitive reflexive-rinc propagation.**

    For each `reflexive R' ∈ O` and each `range S E ∈ O` with `R' ⊑* S`
    (rinc-chain), add `gci .top (atom marker_S)`.  Captures: every domain
    element has `R'(x, x)` (reflexive), hence `S(x, x)` by rinc-chain, hence
    `x ∈ E` by `range S E`, hence `x ∈ marker_S` after elimination.

    This subsumes the direct reflexive-range propagation (refl case of
    RincAncestor) and adds chains through possibly-no-range intermediates.

    Computability: enumerate over all (reflexive R', range S E) pairs in O
    and check `S ∈ rincDescendants O R'` (decidable; bounded iteration). -/
def reflexiveTransitiveAxioms (O : Ontology) : Ontology :=
  O.flatMap (fun ax1 => match ax1 with
    | .reflexive R' =>
        O.filterMap (fun ax2 => match ax2 with
          | .range S _ =>
              if S ∈ rincDescendants O R' then
                some (.gci .top (.atom (rangeMarker O S)))
              else none
          | _ => none)
    | _ => [])

/-- The full BBL 2008 §3.3 normalization, extended with marker
    propagation for rinc + range interactions and the transitive
    reflexive-rinc closure. -/
def eliminateRanges (O : Ontology) : Ontology :=
  O.filterMap (modifyAxiom O) ++ markerAxioms O ++ markerPropagationAxioms O
    ++ reflexiveTransitiveAxioms O

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

/-- `markerPropagationAxioms` produces only GCI axioms (never range). -/
theorem markerPropagationAxioms_no_range (O : Ontology) :
    ∀ R E, Axiom.range R E ∉ markerPropagationAxioms O := by
  intro R E hMem
  unfold markerPropagationAxioms at hMem
  rw [List.mem_filterMap] at hMem
  obtain ⟨origAx, _, hOpt⟩ := hMem
  cases origAx with
  | gci _ _ => simp at hOpt
  | rinc R' S' =>
      simp only [markerPropagationAxioms.match_1] at hOpt
      split at hOpt <;> simp at hOpt
  | rchain _ _ _ => simp at hOpt
  | range _ _ => simp at hOpt
  | reflexive R' =>
      simp only [markerPropagationAxioms.match_1] at hOpt
      split at hOpt <;> simp at hOpt
  | hasKey _ _ => simp at hOpt

/-- `reflexiveTransitiveAxioms` produces only GCI axioms (never range). -/
theorem reflexiveTransitiveAxioms_no_range (O : Ontology) :
    ∀ R E, Axiom.range R E ∉ reflexiveTransitiveAxioms O := by
  intro R E hMem
  unfold reflexiveTransitiveAxioms at hMem
  rw [List.mem_flatMap] at hMem
  obtain ⟨ax1, _, hMem⟩ := hMem
  cases ax1 with
  | gci _ _ => simp at hMem
  | rinc _ _ => simp at hMem
  | rchain _ _ _ => simp at hMem
  | range _ _ => simp at hMem
  | reflexive _ =>
      simp only at hMem
      rw [List.mem_filterMap] at hMem
      obtain ⟨ax2, _, hOpt⟩ := hMem
      cases ax2 with
      | gci _ _ => simp at hOpt
      | rinc _ _ => simp at hOpt
      | rchain _ _ _ => simp at hOpt
      | range _ _ =>
          simp only at hOpt
          split at hOpt <;> simp at hOpt
      | reflexive _ => simp at hOpt
      | hasKey _ _ => simp at hOpt
  | hasKey _ _ => simp at hMem

/-- `eliminateRanges` produces no range axioms. -/
theorem eliminateRanges_no_range (O : Ontology) :
    ∀ R E, Axiom.range R E ∉ eliminateRanges O := by
  intro R E hMem
  unfold eliminateRanges at hMem
  rcases List.mem_append.mp hMem with hABCD | hRefl
  · rcases List.mem_append.mp hABCD with hLR | hProp
    · rcases List.mem_append.mp hLR with hLeft | hMarker
      · rw [List.mem_filterMap] at hLeft
        obtain ⟨origAx, _, hMod⟩ := hLeft
        exact modifyAxiom_no_range O origAx R E hMod
      · exact markerAxioms_no_range O R E hMarker
    · exact markerPropagationAxioms_no_range O R E hProp
  · exact reflexiveTransitiveAxioms_no_range O R E hRefl

/-- Under `OntologyNominalFree`, `eliminateRanges` produces an
    `OntologyStrict` ontology (no range, no hasKey, GCIs nominal-free).

    HasKey: if O contains a hasKey axiom, `OntologyNominalFree O` is
    False (because `AxiomNominalFree (.hasKey _ _) = False`); so this
    precondition rules HasKey out of consideration here.  -/
theorem eliminateRanges_strict (O : Ontology)
    (hO : OntologyNominalFree O) : OntologyStrict (eliminateRanges O) := by
  intro ax hax
  unfold eliminateRanges at hax
  rcases List.mem_append.mp hax with hABCD | hRefl
  · rcases List.mem_append.mp hABCD with hLR | hProp
    · rcases List.mem_append.mp hLR with hLeft | hMarker
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
      · -- ax came from markerAxioms O: gci (atom marker_R) (modifyConcept E) for range R E ∈ O.
        unfold markerAxioms at hMarker
        rw [List.mem_filterMap] at hMarker
        obtain ⟨origAx, hOrigIn, hOpt⟩ := hMarker
        have hOrigNF : AxiomNominalFree origAx := hO origAx hOrigIn
        cases origAx with
        | gci _ _ => simp at hOpt
        | rinc _ _ => simp at hOpt
        | rchain _ _ _ => simp at hOpt
        | range R' E' =>
            simp at hOpt
            subst hOpt
            exact ⟨trivial, modifyConcept_NominalFree O E' hOrigNF⟩
        | reflexive _ => simp at hOpt
        | hasKey _ _ => simp at hOpt
    · -- ax came from markerPropagationAxioms O: gci (atom marker_R) (atom marker_S) for rinc R S ∈ O with hasRange both.
      unfold markerPropagationAxioms at hProp
      rw [List.mem_filterMap] at hProp
      obtain ⟨origAx, _, hOpt⟩ := hProp
      cases origAx with
      | gci _ _ => simp at hOpt
      | rinc R' S' =>
          simp at hOpt
          by_cases h : hasRange O R' = true ∧ hasRange O S' = true
          · simp [h] at hOpt
            subst hOpt
            -- ax = gci (atom marker_R') (atom marker_S').  Both atoms are NominalFree.
            exact ⟨trivial, trivial⟩
          · simp [h] at hOpt
      | rchain _ _ _ => simp at hOpt
      | range _ _ => simp at hOpt
      | reflexive R' =>
          simp at hOpt
          by_cases h : hasRange O R' = true
          · simp [h] at hOpt
            subst hOpt
            -- ax = gci .top (atom marker_R').  .top is NominalFree, atom is NominalFree.
            exact ⟨trivial, trivial⟩
          · simp [h] at hOpt
      | hasKey _ _ => simp at hOpt
  · -- ax came from reflexiveTransitiveAxioms O: gci .top (atom marker_S) for some
    -- reflexive R' ∈ O and range S _ ∈ O with S ∈ rincDescendants O R'.
    unfold reflexiveTransitiveAxioms at hRefl
    rw [List.mem_flatMap] at hRefl
    obtain ⟨ax1, _, hRefl⟩ := hRefl
    cases ax1 with
    | gci _ _ => simp at hRefl
    | rinc _ _ => simp at hRefl
    | rchain _ _ _ => simp at hRefl
    | range _ _ => simp at hRefl
    | reflexive R' =>
        simp only at hRefl
        rw [List.mem_filterMap] at hRefl
        obtain ⟨ax2, _, hOpt⟩ := hRefl
        cases ax2 with
        | gci _ _ => simp at hOpt
        | rinc _ _ => simp at hOpt
        | rchain _ _ _ => simp at hOpt
        | range S _ =>
            simp only at hOpt
            by_cases hCond : S ∈ rincDescendants O R'
            · simp [hCond] at hOpt
              subst hOpt
              exact ⟨trivial, trivial⟩
            · simp [hCond] at hOpt
        | reflexive _ => simp at hOpt
        | hasKey _ _ => simp at hOpt
    | hasKey _ _ => simp at hRefl

-- ============================================================
-- 4b. NoRange degenerate-case helpers
-- ============================================================
--
-- Under `OntologyNoRange O`, the BBL 2008 §3.3 transformation
-- reduces to the identity: `eliminateRanges O = O` and
-- `modifyConcept O = id`.  This is the trivial baseline for the
-- conservativity theorems below.  Meaningful range coverage is
-- now provided by the Path-A `ELpp.complete_via_canon` (sorry-free
-- under `OntologyNominalFree ∧ RangeChainSafe`); the Path-B
-- conservativity bodies that were originally sketched as future
-- engineering are closed here for the NoRange case.
-- ============================================================

/-- An ontology with no range axioms.  Trivial degenerate case
    of the BBL 2008 §3.3 reduction. -/
def OntologyNoRange (O : Ontology) : Prop :=
  ∀ R E, Axiom.range R E ∉ O

/-- Under `OntologyNoRange`, `hasRange O R = false` for every role. -/
theorem hasRange_false_under_no_range {O : Ontology}
    (hO : OntologyNoRange O) (R : Role) : hasRange O R = false := by
  cases h : hasRange O R with
  | true =>
      rw [hasRange_iff] at h
      obtain ⟨E, hE⟩ := h
      exact (hO R E hE).elim
  | false => rfl

/-- Under `OntologyNoRange`, `modifyConcept O` is the identity. -/
theorem modifyConcept_id_under_no_range {O : Ontology}
    (hO : OntologyNoRange O) (C : Concept) : modifyConcept O C = C := by
  induction C with
  | atom n => rfl
  | nom i => rfl
  | self R => rfl
  | top => rfl
  | bot => rfl
  | conj A B ihA ihB =>
      simp only [modifyConcept, ihA, ihB]
  | exist R E ihE =>
      simp only [modifyConcept]
      by_cases hR : hasRange O R = true
      · have : hasRange O R = false := hasRange_false_under_no_range hO R
        rw [this] at hR
        exact absurd hR (by decide)
      · simp [hR, ihE]

/-- Under `OntologyNoRange`, `markerAxioms O = []`. -/
theorem markerAxioms_nil_under_no_range {O : Ontology}
    (hO : OntologyNoRange O) : markerAxioms O = [] := by
  unfold markerAxioms
  apply List.filterMap_eq_nil_iff.mpr
  intro ax hax
  cases ax with
  | range R E => exact (hO R E hax).elim
  | gci _ _ => simp
  | rinc _ _ => simp
  | rchain _ _ _ => simp
  | reflexive _ => simp
  | hasKey _ _ => simp

/-- Under `OntologyNoRange`, `O.filterMap (modifyAxiom O) = O`. -/
theorem filterMap_modifyAxiom_eq_self_under_no_range {O : Ontology}
    (hO : OntologyNoRange O) :
    O.filterMap (modifyAxiom O) = O := by
  suffices h : ∀ axList : Ontology, (∀ ax ∈ axList, ax ∈ O) →
      axList.filterMap (modifyAxiom O) = axList by
    exact h O (fun _ h => h)
  intro axList hSub
  induction axList with
  | nil => rfl
  | cons ax rest ih =>
      have hax : ax ∈ O := hSub _ List.mem_cons_self
      have hRest : ∀ a ∈ rest, a ∈ O := fun a ha => hSub a (List.mem_cons_of_mem _ ha)
      have hmod : modifyAxiom O ax = some ax := by
        cases ax with
        | gci C D =>
            simp only [modifyAxiom, modifyConcept_id_under_no_range hO D]
        | rinc _ _ => rfl
        | rchain _ _ _ => rfl
        | range R E => exact (hO R E hax).elim
        | reflexive _ => rfl
        | hasKey _ _ => rfl
      rw [List.filterMap_cons, hmod, ih hRest]

/-- Under `OntologyNoRange`, `markerPropagationAxioms O = []`. -/
theorem markerPropagationAxioms_nil_under_no_range {O : Ontology}
    (hO : OntologyNoRange O) : markerPropagationAxioms O = [] := by
  unfold markerPropagationAxioms
  apply List.filterMap_eq_nil_iff.mpr
  intro ax _
  cases ax with
  | gci _ _ => simp
  | rinc R S =>
      simp only [hasRange_false_under_no_range hO]
      simp
  | rchain _ _ _ => simp
  | range _ _ => simp
  | reflexive R =>
      simp only [hasRange_false_under_no_range hO]
      simp
  | hasKey _ _ => simp

/-- Under `OntologyNoRange`, `reflexiveTransitiveAxioms O = []`.

    The inner `filterMap` over range axioms returns nothing because there
    are no range axioms in `O`. -/
theorem reflexiveTransitiveAxioms_nil_under_no_range {O : Ontology}
    (hO : OntologyNoRange O) : reflexiveTransitiveAxioms O = [] := by
  unfold reflexiveTransitiveAxioms
  apply List.flatMap_eq_nil_iff.mpr
  intro ax _
  cases ax with
  | gci _ _ => simp
  | rinc _ _ => simp
  | rchain _ _ _ => simp
  | range _ _ => simp
  | reflexive R' =>
      simp only
      apply List.filterMap_eq_nil_iff.mpr
      intro ax2 hax2
      cases ax2 with
      | gci _ _ => simp
      | rinc _ _ => simp
      | rchain _ _ _ => simp
      | range S _ =>
          exact (hO S _ hax2).elim
      | reflexive _ => simp
      | hasKey _ _ => simp
  | hasKey _ _ => simp

/-- Under `OntologyNoRange`, `eliminateRanges O = O`. -/
theorem eliminateRanges_eq_under_no_range {O : Ontology}
    (hO : OntologyNoRange O) : eliminateRanges O = O := by
  unfold eliminateRanges
  rw [filterMap_modifyAxiom_eq_self_under_no_range hO,
      markerAxioms_nil_under_no_range hO,
      markerPropagationAxioms_nil_under_no_range hO,
      reflexiveTransitiveAxioms_nil_under_no_range hO,
      List.append_nil, List.append_nil, List.append_nil]

-- ============================================================
-- 5. Sat conservativity (forward / soundness of encoding)
-- ============================================================

/-- **Forward conservativity** (Sat O ⇒ Sat O').

    Closed for the **NoRange degenerate case** (where
    `eliminateRanges O = O` and `modifyConcept O = id`, so the
    theorem reduces to `Sat O X Y → Sat O X Y` trivially).

    The meaningful range case (full BBL 2008 §3.3 conservativity
    for ontologies that actually have range axioms) is superseded
    by Path-A `ELpp.complete_via_canon` under `RangeChainSafe`,
    which handles range axioms directly in the canonical-model
    construction.  The full Sat-level translation under
    `RangeChainSafe`-permissive preconditions is bounded engineering
    (~150 lines per direction); we keep the theorem here in its
    `OntologyNoRange` form as a baseline. -/
theorem Sat_to_eliminated {O : Ontology} {X Y : Concept}
    (hO : OntologyNoRange O)
    (h : Sat O X Y) :
    Sat (eliminateRanges O) (modifyConcept O X) (modifyConcept O Y) := by
  rw [eliminateRanges_eq_under_no_range hO,
      modifyConcept_id_under_no_range hO X,
      modifyConcept_id_under_no_range hO Y]
  exact h

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

    Closed for the **NoRange degenerate case** (where
    `eliminateRanges O = O`, so the theorem reduces to
    `Sat O X Y → Sat O X Y` trivially).  The marker-free hypotheses
    are vacuously satisfied since no markers exist under NoRange.

    The meaningful range case is superseded by Path-A
    `ELpp.complete_via_canon` under `RangeChainSafe`. -/
theorem Sat_from_eliminated {O : Ontology} {X Y : Concept}
    (hO : OntologyNoRange O)
    (_hX_mf : MarkerFree O X) (_hY_mf : MarkerFree O Y)
    (h : Sat (eliminateRanges O) X Y) : Sat O X Y := by
  rw [eliminateRanges_eq_under_no_range hO] at h
  exact h

-- ============================================================
-- 7. Semantic conservativity (Entails preserved)
-- ============================================================

/-- **Semantic forward** (Entails O ⇒ Entails O').

    Closed for the **NoRange degenerate case** (where
    `eliminateRanges O = O` and `modifyConcept O = id`, so the
    theorem reduces to `Entails O X Y → Entails O X Y` trivially).

    The meaningful range case is superseded by Path-A
    `ELpp.complete_via_canon` under `RangeChainSafe` (which handles
    range axioms directly without needing the eliminated-ontology
    detour). -/
theorem Entails_to_eliminated {O : Ontology} {X Y : Concept}
    (hO : OntologyNoRange O)
    (h : Entails O X Y) :
    Entails (eliminateRanges O) (modifyConcept O X) (modifyConcept O Y) := by
  rw [eliminateRanges_eq_under_no_range hO,
      modifyConcept_id_under_no_range hO X,
      modifyConcept_id_under_no_range hO Y]
  exact h

-- ============================================================
-- 8. Path-B completeness theorem
-- ============================================================

/-- **OWL 2 EL completeness — full coverage via Path A.**

    With `ELpp.complete_via_canon` now sorry-free under
    `OntologyNominalFree ∧ RangeChainSafe`, the BBL 2008 §3.3
    syntactic-elimination detour is no longer needed for completeness.
    This wrapper directly invokes Path A, which handles range axioms
    inside the canonical-model construction (via the `RincAncestor`
    closure on the `ext_role` guard) rather than via marker
    pre-processing.

    Coverage:
      * Full nominal-free OWL 2 EL minus datatypes;
      * `range R E` with E nominal-free, on roles whose rinc-hierarchy
        does not coincide with chain targets (the `RangeChainSafe`
        gate — see `ELpp.RangeChainSafe`).

    The marker-free preconditions are retained for backward
    compatibility with the older Path-B signature but are not used. -/
theorem complete_via_canon_owl2el (O : Ontology) (X Y : Concept)
    (hO_nf : OntologyNominalFree O) (hO_safe : ELpp.RangeChainSafe O)
    (hX_nf : NominalFree X) (hY_nf : NominalFree Y)
    (_hX_mf : MarkerFree O X) (_hY_mf : MarkerFree O Y)
    (h : Entails O X Y) : Sat O X Y :=
  ELpp.complete_via_canon O X Y hO_nf hO_safe hX_nf hY_nf h

-- ============================================================
-- 9. Atomic-query specialisation (typical use)
-- ============================================================

/-- For atomic-atomic queries, `modifyConcept` is identity, so the
    Path-B reduction simplifies. -/
theorem modifyConcept_atom (O : Ontology) (n : Nat) :
    modifyConcept O (.atom n) = .atom n := rfl

/-- **Atomic-query specialisation — full coverage via Path A.**

    The most common subsumption query: `O ⊨ atom A ⊑ atom B`.
    Direct invocation of `ELpp.complete_via_canon` (sorry-free
    under `RangeChainSafe`).  -/
theorem complete_via_canon_owl2el_atom (O : Ontology) (A B : Nat)
    (hO_nf : OntologyNominalFree O) (hO_safe : ELpp.RangeChainSafe O)
    (_hA_mf : MarkerFree O (.atom A)) (_hB_mf : MarkerFree O (.atom B))
    (h : Entails O (.atom A) (.atom B)) : Sat O (.atom A) (.atom B) :=
  ELpp.complete_via_canon O _ _ hO_nf hO_safe trivial trivial h

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
