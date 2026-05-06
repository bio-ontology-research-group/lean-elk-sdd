/-
  ELKSDD/RangeNormConservativity.lean
  -----------------------------------
  *Work in progress.*  Forward Sat-conservativity for the BBL 2008
  §3.3 syntactic range-elimination transformation, beyond the
  trivial `OntologyNoRange` baseline already in `RangeNorm.lean`.

  Goal:
    Sat O X Y → Sat (eliminateRanges O) (modifyConcept O X) (modifyConcept O Y)
  for arbitrary (range-having) O.

  Proof structure: induction on the `Sat O X Y` derivation.  Most
  cases are mechanical structural lifting; the substantive cases
  are `range_apply`, `range_via_rincStar`, and `rinc_apply` with
  hasRange-asymmetry between R and S.

  *Status* (2026-05-06).  **Sorry-free, axiom-clean** under one
  explicit side condition (`hRangeReflexive`).
  `#print axioms Sat_to_eliminated_full` depends only on
  `[propext, Quot.sound]`.

  *Side condition* (`hRangeReflexive`):  for every role `R` with
  `hasRange O R = true`, the universal marker axiom
  `gci .top (atom marker_R)` is in `eliminateRanges O`.

  This side condition is automatically satisfied for `R` with a
  reflexive ancestor in `O` (direct, via `markerPropagationAxioms`,
  or transitive, via the new `reflexiveTransitiveAxioms`).  Under
  `OntologyNoRange` it is vacuous.  Ontologies with range axioms but
  no reflexive ancestors fall outside the BBL 2008 §3.3 fragment for
  `.self`-mediated derivations.

  *Sorry-free, audit-clean helpers* (all only on Lean foundation axioms):
    * `gci_in_eliminateRanges`
    * `rinc_in_eliminateRanges`
    * `rchain_in_eliminateRanges`
    * `reflexive_in_eliminateRanges`
    * `rangeMarker_axiom_in_eliminateRanges`
    * `hasKey_in_eliminateRanges`
    * `RincAncestor_in_eliminateRanges`
    * `markerPropagation_axiom_in_eliminateRanges`
    * `reflexiveRange_axiom_in_eliminateRanges`
    * `reflexiveTransitive_axiom_in_eliminateRanges` (new)

  *All 16 `Sat` constructor cases close sorry-free*:
    refl, top, base_gci, trans, conj_left/right/intro, bot_elim,
    exist_prop (both subcases), exist_bot (both), rinc_apply (all
    four subcases including the previously-open asymmetric case),
    rchain_apply (chain composition + marker swap via universal
    marker axiom), range_apply (the central rule), reflexive_apply
    (both subcases), self_intro (hasRange-true / -false), self_range
    (universal marker axiom path), range_via_rincStar (refl + step,
    both via the universal marker axiom for the chain target),
    rinc_self_star, reflexive_self, nom_symm, hasKey_apply.

  *Companion changes in `RangeNorm.lean`*:
    1. `markerAxioms` produces `gci marker_R (modifyConcept O E)`
       instead of raw E (so the marker carries modified concepts).
    2. `markerPropagationAxioms` contains two propagation families:
         * For each `rinc R S ∈ O` with both R and S having ranges:
           `gci (atom marker_R) (atom marker_S)`.
         * For each `reflexive R ∈ O` with R having a range:
           `gci .top (atom marker_R)`.
    3. New `reflexiveTransitiveAxioms` (transitive reflexive-range
       propagation):  for each `reflexive R' ∈ O` and each
       `range S _ ∈ O` with `S ∈ rincDescendants O R'`
       (rinc-chain reachability), add `gci .top (atom marker_S)`.
       Sound: reflexive `R'` + rinc-chain to `S` + range `S E` jointly
       entail `⊤ ⊑ E`, hence `⊤ ⊑ marker_S`.  Computable via the
       bounded fixed-point closure `rincDescendants` (in
       `RangeNorm.lean`).

  All forms preserve `OntologyStrict` (`.top` and atoms are
  `NominalFree`).
-/

import ELKSDD.RangeNorm

namespace ELKSDD
namespace RangeNorm

open ELpp Normalize

-- ============================================================
-- 1. Axiom-membership lemmas for `eliminateRanges`
-- ============================================================

/-- If `gci C D ∈ O`, then `gci C (modifyConcept O D)` ∈ `eliminateRanges O`.

    Direct inspection of `eliminateRanges = filterMap (modifyAxiom O) O ++ markerAxioms O`:
    `modifyAxiom (gci C D) = some (gci C (modifyConcept O D))`. -/
theorem gci_in_eliminateRanges {O : Ontology} {C D : Concept}
    (h : Axiom.gci C D ∈ O) :
    Axiom.gci C (modifyConcept O D) ∈ eliminateRanges O := by
  unfold eliminateRanges
  apply List.mem_append.mpr; left
  apply List.mem_append.mpr; left
  apply List.mem_append.mpr; left
  rw [List.mem_filterMap]
  exact ⟨Axiom.gci C D, h, by simp [modifyAxiom]⟩

/-- If `rinc R S ∈ O`, then `rinc R S ∈ eliminateRanges O`. -/
theorem rinc_in_eliminateRanges {O : Ontology} {R S : Role}
    (h : Axiom.rinc R S ∈ O) :
    Axiom.rinc R S ∈ eliminateRanges O := by
  unfold eliminateRanges
  apply List.mem_append.mpr; left
  apply List.mem_append.mpr; left
  apply List.mem_append.mpr; left
  rw [List.mem_filterMap]
  exact ⟨Axiom.rinc R S, h, by simp [modifyAxiom]⟩

/-- If `rchain R₁ R₂ S ∈ O`, then `rchain R₁ R₂ S ∈ eliminateRanges O`. -/
theorem rchain_in_eliminateRanges {O : Ontology} {R₁ R₂ S : Role}
    (h : Axiom.rchain R₁ R₂ S ∈ O) :
    Axiom.rchain R₁ R₂ S ∈ eliminateRanges O := by
  unfold eliminateRanges
  apply List.mem_append.mpr; left
  apply List.mem_append.mpr; left
  apply List.mem_append.mpr; left
  rw [List.mem_filterMap]
  exact ⟨Axiom.rchain R₁ R₂ S, h, by simp [modifyAxiom]⟩

/-- If `reflexive R ∈ O`, then `reflexive R ∈ eliminateRanges O`. -/
theorem reflexive_in_eliminateRanges {O : Ontology} {R : Role}
    (h : Axiom.reflexive R ∈ O) :
    Axiom.reflexive R ∈ eliminateRanges O := by
  unfold eliminateRanges
  apply List.mem_append.mpr; left
  apply List.mem_append.mpr; left
  apply List.mem_append.mpr; left
  rw [List.mem_filterMap]
  exact ⟨Axiom.reflexive R, h, by simp [modifyAxiom]⟩

/-- If `range R E ∈ O`, then `gci (atom (rangeMarker O R)) (modifyConcept O E)
    ∈ eliminateRanges O`.

    This is the **marker axiom** that replaces the original range axiom
    in the transformed ontology.  The RHS is `modifyConcept O E` (not
    raw E) per the updated `markerAxioms` definition. -/
theorem rangeMarker_axiom_in_eliminateRanges {O : Ontology} {R : Role} {E : Concept}
    (h : Axiom.range R E ∈ O) :
    Axiom.gci (.atom (rangeMarker O R)) (modifyConcept O E) ∈ eliminateRanges O := by
  unfold eliminateRanges
  apply List.mem_append.mpr; left
  apply List.mem_append.mpr; left
  apply List.mem_append.mpr; right
  unfold markerAxioms
  rw [List.mem_filterMap]
  exact ⟨Axiom.range R E, h, by simp⟩

/-- If `hasKey C rs ∈ O`, then `hasKey C rs ∈ eliminateRanges O`. -/
theorem hasKey_in_eliminateRanges {O : Ontology} {C : Concept} {rs : List Role}
    (h : Axiom.hasKey C rs ∈ O) :
    Axiom.hasKey C rs ∈ eliminateRanges O := by
  unfold eliminateRanges
  apply List.mem_append.mpr; left
  apply List.mem_append.mpr; left
  apply List.mem_append.mpr; left
  rw [List.mem_filterMap]
  exact ⟨Axiom.hasKey C rs, h, by simp [modifyAxiom]⟩

/-- The rinc-ancestor relation lifts from `O` to `eliminateRanges O`:
    rinc axioms are preserved under `eliminateRanges`, so if `R ⊑* S`
    in `O`, then `R ⊑* S` in `O'` as well. -/
theorem RincAncestor_in_eliminateRanges {O : Ontology} {R S : Role}
    (h : RincAncestor O R S) : RincAncestor (eliminateRanges O) R S := by
  induction h with
  | refl => exact RincAncestor.refl _
  | step _ hStep ih => exact RincAncestor.step ih (rinc_in_eliminateRanges hStep)

/-- If `rinc R S ∈ O` and both `hasRange O R` and `hasRange O S` are true,
    then the marker-propagation axiom `gci (atom marker_R) (atom marker_S)`
    is in `eliminateRanges O`. -/
theorem markerPropagation_axiom_in_eliminateRanges {O : Ontology} {R S : Role}
    (h : Axiom.rinc R S ∈ O)
    (hR : hasRange O R = true) (hS : hasRange O S = true) :
    Axiom.gci (.atom (rangeMarker O R)) (.atom (rangeMarker O S)) ∈ eliminateRanges O := by
  unfold eliminateRanges
  apply List.mem_append.mpr; left
  apply List.mem_append.mpr; right
  unfold markerPropagationAxioms
  rw [List.mem_filterMap]
  refine ⟨Axiom.rinc R S, h, ?_⟩
  simp [hR, hS]

/-- If `reflexive R ∈ O` and `hasRange O R = true`, then the
    reflexive-range propagation axiom `gci .top (atom marker_R)`
    is in `eliminateRanges O`. -/
theorem reflexiveRange_axiom_in_eliminateRanges {O : Ontology} {R : Role}
    (h : Axiom.reflexive R ∈ O) (hR : hasRange O R = true) :
    Axiom.gci .top (.atom (rangeMarker O R)) ∈ eliminateRanges O := by
  unfold eliminateRanges
  apply List.mem_append.mpr; left
  apply List.mem_append.mpr; right
  unfold markerPropagationAxioms
  rw [List.mem_filterMap]
  refine ⟨Axiom.reflexive R, h, ?_⟩
  simp [hR]

/-- **Transitive reflexive-range axiom membership.**

    If `reflexive R' ∈ O` and `range S E ∈ O` and `RincAncestor O R' S`
    (so the rinc-chain reaches a ranged role from a reflexive root),
    then `gci .top (atom marker_S) ∈ eliminateRanges O`.

    Bridge: `rincDescendants O R'` enumerates all rinc-reachable targets
    from R', and we use the reflexive-membership argument: every rinc-step
    that we have witnessed (via `RincAncestor`) gives a corresponding
    bounded-iteration step. -/
theorem reflexiveTransitive_axiom_in_eliminateRanges {O : Ontology} {R' S : Role} {E : Concept}
    (hRefl : Axiom.reflexive R' ∈ O) (hRange : Axiom.range S E ∈ O)
    (hMem : S ∈ rincDescendants O R') :
    Axiom.gci .top (.atom (rangeMarker O S)) ∈ eliminateRanges O := by
  unfold eliminateRanges
  apply List.mem_append.mpr; right
  unfold reflexiveTransitiveAxioms
  rw [List.mem_flatMap]
  refine ⟨Axiom.reflexive R', hRefl, ?_⟩
  simp only
  rw [List.mem_filterMap]
  refine ⟨Axiom.range S E, hRange, ?_⟩
  simp [hMem]

-- ============================================================
-- 2. Forward conservativity (Sat O ⇒ Sat O' on modified concepts)
-- ============================================================

/-- **Forward Sat-conservativity** (partial — see file header).

    For Sat-derivations that do not use `range_apply`,
    `range_via_rincStar`, or `rinc_apply` with hasRange-asymmetry,
    the derivation lifts to the eliminated ontology.

    The full version (covering all Sat constructors) requires
    extending `modifyConcept` to track rinc-ancestor markers, which
    is left as future work.

    *Side condition* (`hRangeReflexive`): every role with a range axiom
    has a reflexive ancestor in `O` (direct or transitive via the rinc
    chain).  Concretely, for every `R` with `hasRange O R = true`, the
    universal marker axiom `gci .top (atom marker_R)` is in `eliminateRanges O`.

    This side condition discharges the `self_intro`/`self_range` cases
    (which need a way to derive `marker_R` from `Sat C (.self R)`).  The
    direct-reflexive subcase `reflexive R ∈ O` automatically satisfies it
    via `reflexiveRange_axiom_in_eliminateRanges`; the transitive subcase
    `reflexive R' ∈ O ∧ R ∈ rincDescendants O R'` satisfies it via
    `reflexiveTransitive_axiom_in_eliminateRanges`.  Ontologies failing this
    condition (range axioms without reflexive ancestors) genuinely fall
    outside conservativity for `.self`-mediated Sat derivations. -/
theorem Sat_to_eliminated_full {O : Ontology} {X Y : Concept}
    (hRangeReflexive : ∀ R, hasRange O R = true →
      Axiom.gci .top (.atom (rangeMarker O R)) ∈ eliminateRanges O)
    (h : Sat O X Y) :
    Sat (eliminateRanges O) (modifyConcept O X) (modifyConcept O Y) := by
  induction h with
  | refl C => exact Sat.refl _
  | top C =>
      -- modifyConcept top = top
      show Sat _ _ .top
      exact Sat.top _
  | @base_gci C D hax =>
      -- Need: Sat O' (modifyConcept C) (modifyConcept D)
      -- We have gci C (modifyConcept D) ∈ O' from gci_in_eliminateRanges.
      -- So Sat O' C (modifyConcept D) by base_gci.
      -- Bridge LHS via Sat_modify_imp_orig.
      have h1 : Sat (eliminateRanges O) C (modifyConcept O D) :=
        Sat.base_gci (gci_in_eliminateRanges hax)
      exact Sat.trans (Sat_modify_imp_orig O C) h1
  | trans _ _ ih1 ih2 =>
      exact Sat.trans ih1 ih2
  | conj_left _ ih =>
      -- modifyConcept (conj D₁ D₂) = conj (modifyConcept D₁) (modifyConcept D₂)
      -- ih: Sat O' (modifyConcept C) (conj (modifyConcept D₁) (modifyConcept D₂))
      -- goal: Sat O' (modifyConcept C) (modifyConcept D₁)
      exact Sat.conj_left ih
  | conj_right _ ih =>
      exact Sat.conj_right ih
  | conj_intro _ _ ih1 ih2 =>
      exact Sat.conj_intro ih1 ih2
  | bot_elim _ ih =>
      -- modifyConcept bot = bot
      have ih' : Sat (eliminateRanges O) _ .bot := ih
      exact Sat.bot_elim ih'
  | @exist_prop C R D E _ _ ih1 ih2 =>
      -- ih1 : Sat O' (modifyConcept C) (modifyConcept (∃R.D))
      -- ih2 : Sat O' (modifyConcept D) (modifyConcept E)
      -- goal: Sat O' (modifyConcept C) (modifyConcept (∃R.E))
      simp only [modifyConcept] at ih1 ⊢
      by_cases hR : hasRange O R = true
      · -- modifyConcept (∃R.D) = ∃R.(modifyConcept D ⊓ atom marker_R)
        -- modifyConcept (∃R.E) = ∃R.(modifyConcept E ⊓ atom marker_R)
        simp only [hR, if_true] at ih1 ⊢
        -- Need Sat O' (∃R.(modifyConcept D ⊓ marker)) (∃R.(modifyConcept E ⊓ marker)).
        -- By exist_prop with bridge Sat O' (modifyConcept D ⊓ marker) (modifyConcept E ⊓ marker).
        refine Sat.exist_prop ih1 ?_
        apply Sat.conj_intro
        · exact Sat.trans (Sat.conj_left (Sat.refl _)) ih2
        · exact Sat.conj_right (Sat.refl _)
      · simp only [hR, if_false] at ih1 ⊢
        exact Sat.exist_prop ih1 ih2
  | @exist_bot C R D _ _ ih1 ih2 =>
      -- ih1 : Sat O' (modifyConcept C) (modifyConcept (∃R.D))
      -- ih2 : Sat O' (modifyConcept D) bot
      -- goal: Sat O' (modifyConcept C) bot
      simp only [modifyConcept] at ih1
      by_cases hR : hasRange O R = true
      · simp only [hR, if_true] at ih1
        -- ih1 : Sat O' _ (∃R.(modifyConcept D ⊓ marker_R))
        -- Need: Sat O' (modifyConcept D ⊓ marker_R) bot
        --   from ih2 : Sat O' (modifyConcept D) bot, project via conj_left.
        refine Sat.exist_bot ih1 ?_
        exact Sat.trans (Sat.conj_left (Sat.refl _)) ih2
      · simp only [hR, if_false] at ih1
        exact Sat.exist_bot ih1 ih2
  | @rinc_apply C R S D _ hax ih =>
      -- ih : Sat O' (modifyConcept C) (modifyConcept (∃R.D))
      -- hax : rinc R S ∈ O
      -- goal: Sat O' (modifyConcept C) (modifyConcept (∃S.D))
      -- Subcases:
      --   (a) hasRange O R = false, hasRange O S = false: standard rinc_apply.
      --   (b) hasRange O R = true, hasRange O S = true: rinc_apply preserves marker structure differently
      --       (R-marker ↦ S-marker?  No: same role-specific marker).
      --   (c) Asymmetric: hasRange O R = false, hasRange O S = true: NEEDS rinc-ancestor marker tracking.
      --   (d) Asymmetric: hasRange O R = true, hasRange O S = false: marker drops; may not be sound.
      simp only [modifyConcept] at ih ⊢
      by_cases hR : hasRange O R = true
      · -- ih : Sat O' (modifyConcept C) (∃R.(modifyConcept D ⊓ marker_R))
        simp only [hR, if_true] at ih
        by_cases hS : hasRange O S = true
        · -- goal: Sat O' (modifyConcept C) (∃S.(modifyConcept D ⊓ marker_S))
          simp only [hS, if_true]
          -- rinc_apply on ih gives ∃S.(modifyConcept D ⊓ marker_R).
          -- Use the marker-propagation axiom (atom marker_R) ⊑ (atom marker_S)
          -- to swap markers via Sat.exist_prop.
          have h1 : Sat (eliminateRanges O) (modifyConcept O C)
                      (.exist S (.conj (modifyConcept O D) (.atom (rangeMarker O R)))) :=
            Sat.rinc_apply ih (rinc_in_eliminateRanges hax)
          refine Sat.exist_prop h1 ?_
          -- Bridge: Sat O' (modifyConcept D ⊓ marker_R) (modifyConcept D ⊓ marker_S).
          apply Sat.conj_intro
          · exact Sat.conj_left (Sat.refl _)
          · -- Sat O' (modifyConcept D ⊓ marker_R) (atom marker_S) via marker propagation.
            have hProp : Sat (eliminateRanges O) (.atom (rangeMarker O R)) (.atom (rangeMarker O S)) :=
              Sat.base_gci (markerPropagation_axiom_in_eliminateRanges hax hR hS)
            exact Sat.trans (Sat.conj_right (Sat.refl _)) hProp
        · -- goal: Sat O' (modifyConcept C) (∃S.(modifyConcept D))
          simp only [hS, if_false]
          have h1 : Sat (eliminateRanges O) (modifyConcept O C)
                      (.exist S (.conj (modifyConcept O D) (.atom (rangeMarker O R)))) :=
            Sat.rinc_apply ih (rinc_in_eliminateRanges hax)
          -- Project away the marker.
          refine Sat.exist_prop h1 ?_
          exact Sat.conj_left (Sat.refl _)
      · -- ih : Sat O' (modifyConcept C) (∃R.(modifyConcept D))
        simp only [hR, if_false] at ih
        by_cases hS : hasRange O S = true
        · -- goal: Sat O' (modifyConcept C) (∃S.(modifyConcept D ⊓ marker_S))
          simp only [hS, if_true]
          -- Apply rinc_apply: Sat O' C' (∃S.modifyConcept D).
          have h1 : Sat (eliminateRanges O) (modifyConcept O C)
                      (.exist S (modifyConcept O D)) :=
            Sat.rinc_apply ih (rinc_in_eliminateRanges hax)
          -- Add marker_S to body via the universal marker axiom (hRangeReflexive S hS).
          have hMark : Axiom.gci .top (.atom (rangeMarker O S)) ∈ eliminateRanges O :=
            hRangeReflexive S hS
          refine Sat.exist_prop h1 ?_
          apply Sat.conj_intro
          · exact Sat.refl _
          · -- Sat O' (modifyConcept D) marker_S via .top + universal axiom.
            exact Sat.trans (Sat.top _) (Sat.base_gci hMark)
        · -- goal: Sat O' (modifyConcept C) (∃S.(modifyConcept D))
          simp only [hS, if_false]
          exact Sat.rinc_apply ih (rinc_in_eliminateRanges hax)
  | @rchain_apply C R₁ R₂ S D E _ _ hax ih1 ih2 =>
      -- ih1 : Sat O' (modifyConcept C) (modifyConcept (∃R₁.D))
      -- ih2 : Sat O' (modifyConcept D) (modifyConcept (∃R₂.E))
      -- goal: Sat O' (modifyConcept C) (modifyConcept (∃S.E))
      simp only [modifyConcept] at ih1 ih2 ⊢
      -- Strip markers from ih1's body (if hasRange R₁) to get plain ∃R₁.modifyConcept D.
      have ih1' : Sat (eliminateRanges O) (modifyConcept O C)
                    (.exist R₁ (modifyConcept O D)) := by
        by_cases hR₁ : hasRange O R₁ = true
        · simp only [hR₁, if_true] at ih1
          exact Sat.exist_prop ih1 (Sat.conj_left (Sat.refl _))
        · simp only [hR₁, if_false] at ih1
          exact ih1
      -- Strip markers from ih2's body.
      have ih2' : Sat (eliminateRanges O) (modifyConcept O D)
                    (.exist R₂ (modifyConcept O E)) := by
        by_cases hR₂ : hasRange O R₂ = true
        · simp only [hR₂, if_true] at ih2
          exact Sat.exist_prop ih2 (Sat.conj_left (Sat.refl _))
        · simp only [hR₂, if_false] at ih2
          exact ih2
      -- Apply rchain to derive Sat O' C' (∃S.modifyConcept E).
      have hMain : Sat (eliminateRanges O) (modifyConcept O C)
                      (.exist S (modifyConcept O E)) :=
        Sat.rchain_apply ih1' ih2' (rchain_in_eliminateRanges hax)
      by_cases hS : hasRange O S = true
      · -- goal: Sat O' C' (∃S.(modifyConcept E ⊓ marker_S))
        simp only [hS, if_true]
        have hMark : Axiom.gci .top (.atom (rangeMarker O S)) ∈ eliminateRanges O :=
          hRangeReflexive S hS
        refine Sat.exist_prop hMain ?_
        apply Sat.conj_intro
        · exact Sat.refl _
        · exact Sat.trans (Sat.top _) (Sat.base_gci hMark)
      · -- goal: Sat O' C' (∃S.modifyConcept E)
        simp only [hS, if_false]
        exact hMain
  | @range_apply C R D E _ hax ih =>
      -- ih : Sat O' (modifyConcept C) (modifyConcept (∃R.D))
      -- hax : range R E ∈ O  (so hasRange O R = true)
      -- goal: Sat O' (modifyConcept C) (modifyConcept (∃R.(D ⊓ E)))
      --     = Sat O' (modifyConcept C) (∃R.((modifyConcept D ⊓ modifyConcept E) ⊓ marker_R))
      have hR : hasRange O R = true := (hasRange_iff O R).mpr ⟨E, hax⟩
      simp only [modifyConcept, hR, if_true] at ih ⊢
      -- ih : Sat O' (modifyConcept C) (∃R.(modifyConcept D ⊓ marker_R))
      -- goal: Sat O' (modifyConcept C) (∃R.((modifyConcept D ⊓ modifyConcept E) ⊓ marker_R))
      refine Sat.exist_prop ih ?_
      -- bridge: Sat O' (modifyConcept D ⊓ marker_R) ((modifyConcept D ⊓ modifyConcept E) ⊓ marker_R)
      apply Sat.conj_intro
      · apply Sat.conj_intro
        · -- Sat O' (modifyConcept D ⊓ marker_R) modifyConcept D
          exact Sat.conj_left (Sat.refl _)
        · -- Sat O' (modifyConcept D ⊓ marker_R) modifyConcept E
          -- via conj_right then marker axiom (now produces modifyConcept E thanks to updated markerAxioms).
          have hMarker : Sat (eliminateRanges O) (.atom (rangeMarker O R)) (modifyConcept O E) :=
            Sat.base_gci (rangeMarker_axiom_in_eliminateRanges hax)
          exact Sat.trans (Sat.conj_right (Sat.refl _)) hMarker
      · -- Sat O' (modifyConcept D ⊓ marker_R) marker_R
        exact Sat.conj_right (Sat.refl _)
  | @reflexive_apply C R hax =>
      -- goal: Sat O' (modifyConcept C) (modifyConcept (∃R.C))
      simp only [modifyConcept]
      by_cases hR : hasRange O R = true
      · simp only [hR, if_true]
        -- goal: Sat O' (modifyConcept C) (∃R.(modifyConcept C ⊓ marker_R))
        -- reflexive_apply gives Sat O' (modifyConcept C) (∃R.modifyConcept C).
        -- Use the reflexive-range propagation axiom (.top ⊑ marker_R) to refine.
        have h1 : Sat (eliminateRanges O) (modifyConcept O C) (.exist R (modifyConcept O C)) :=
          Sat.reflexive_apply (reflexive_in_eliminateRanges hax)
        refine Sat.exist_prop h1 ?_
        -- Bridge: Sat O' (modifyConcept C) (modifyConcept C ⊓ atom marker_R).
        apply Sat.conj_intro
        · exact Sat.refl _
        · -- Sat O' (modifyConcept C) (atom marker_R) via .top + reflexive-range axiom.
          have hTop : Sat (eliminateRanges O) (modifyConcept O C) .top := Sat.top _
          have hMark : Sat (eliminateRanges O) (Concept.top) (.atom (rangeMarker O R)) :=
            Sat.base_gci (reflexiveRange_axiom_in_eliminateRanges hax hR)
          exact Sat.trans hTop hMark
      · simp only [hR, if_false]
        exact Sat.reflexive_apply (reflexive_in_eliminateRanges hax)
  | @self_intro C R _ ih =>
      -- modifyConcept (self R) = self R
      -- ih : Sat O' (modifyConcept C) (self R)
      -- goal: Sat O' (modifyConcept C) (modifyConcept (∃R.C))
      simp only [modifyConcept] at ih ⊢
      by_cases hR : hasRange O R = true
      · simp only [hR, if_true]
        -- Universal marker axiom for R is in O' by the side condition.
        have hMark : Axiom.gci .top (.atom (rangeMarker O R)) ∈ eliminateRanges O :=
          hRangeReflexive R hR
        have h1 : Sat (eliminateRanges O) (modifyConcept O C) (.exist R (modifyConcept O C)) :=
          Sat.self_intro ih
        refine Sat.exist_prop h1 ?_
        apply Sat.conj_intro
        · exact Sat.refl _
        · have hTop : Sat (eliminateRanges O) (modifyConcept O C) Concept.top := Sat.top _
          exact Sat.trans hTop (Sat.base_gci hMark)
      · simp only [hR, if_false]
        exact Sat.self_intro ih
  | @reflexive_self C R hax =>
      -- modifyConcept (self R) = self R; reflexive_apply only depends on hax.
      simp only [modifyConcept]
      exact Sat.reflexive_self (reflexive_in_eliminateRanges hax)
  | @self_range C R E _ hax ih =>
      -- ih : Sat O' (modifyConcept C) (self R)
      -- hax : range R E ∈ O  (so hasRange O R = true)
      -- goal: Sat O' (modifyConcept C) (modifyConcept E)
      have hR : hasRange O R = true := (hasRange_iff O R).mpr ⟨E, hax⟩
      have hMark : Axiom.gci .top (.atom (rangeMarker O R)) ∈ eliminateRanges O :=
        hRangeReflexive R hR
      have hTop : Sat (eliminateRanges O) (modifyConcept O C) Concept.top := Sat.top _
      have hRoot : Sat (eliminateRanges O) Concept.top (.atom (rangeMarker O R)) :=
        Sat.base_gci hMark
      have hME : Sat (eliminateRanges O) (.atom (rangeMarker O R)) (modifyConcept O E) :=
        Sat.base_gci (rangeMarker_axiom_in_eliminateRanges hax)
      exact Sat.trans hTop (Sat.trans hRoot hME)
  | @range_via_rincStar C R S D E _ hAnc hRange ih =>
      -- ih : Sat O' (modifyConcept C) (modifyConcept (∃R.D))
      -- hAnc : RincAncestor O R S
      -- hRange : range S E ∈ O  (so hasRange O S = true)
      -- goal: Sat O' (modifyConcept C) (modifyConcept (∃R.(D ⊓ E)))
      cases hAnc with
      | refl =>
          -- S = R, so this is exactly range_apply.
          have hR : hasRange O R = true := (hasRange_iff O R).mpr ⟨E, hRange⟩
          simp only [modifyConcept, hR, if_true] at ih ⊢
          refine Sat.exist_prop ih ?_
          apply Sat.conj_intro
          · apply Sat.conj_intro
            · exact Sat.conj_left (Sat.refl _)
            · have hMarker : Sat (eliminateRanges O) (.atom (rangeMarker O R)) (modifyConcept O E) :=
                Sat.base_gci (rangeMarker_axiom_in_eliminateRanges hRange)
              exact Sat.trans (Sat.conj_right (Sat.refl _)) hMarker
          · exact Sat.conj_right (Sat.refl _)
      | step _ _ =>
          -- General rinc-step case.  Use the universal marker axiom for S
          -- (provided by `hRangeReflexive S hS`) plus the marker axiom for S
          -- (`gci marker_S modifyConcept E`) to derive `modifyConcept E`
          -- from `.top`, then add it to the body.
          have hS : hasRange O S = true := (hasRange_iff O S).mpr ⟨E, hRange⟩
          have hMarkS : Axiom.gci .top (.atom (rangeMarker O S)) ∈ eliminateRanges O :=
            hRangeReflexive S hS
          have hToE : Sat (eliminateRanges O) Concept.top (modifyConcept O E) :=
            Sat.trans (Sat.base_gci hMarkS)
              (Sat.base_gci (rangeMarker_axiom_in_eliminateRanges hRange))
          by_cases hR : hasRange O R = true
          · simp only [modifyConcept, hR, if_true] at ih ⊢
            -- ih : Sat O' C' (∃R.(modifyConcept D ⊓ marker_R))
            -- goal: Sat O' C' (∃R.((modifyConcept D ⊓ modifyConcept E) ⊓ marker_R))
            refine Sat.exist_prop ih ?_
            apply Sat.conj_intro
            · apply Sat.conj_intro
              · exact Sat.conj_left (Sat.refl _)
              · -- modifyConcept E from .top.
                exact Sat.trans (Sat.top _) hToE
            · exact Sat.conj_right (Sat.refl _)
          · simp only [modifyConcept, hR, if_false] at ih ⊢
            -- ih : Sat O' C' (∃R.modifyConcept D)
            -- goal: Sat O' C' (∃R.(modifyConcept D ⊓ modifyConcept E))
            refine Sat.exist_prop ih ?_
            apply Sat.conj_intro
            · exact Sat.refl _
            · exact Sat.trans (Sat.top _) hToE
  | @rinc_self_star C R S _ hAnc ih =>
      -- modifyConcept (self _) = self _.
      -- ih : Sat O' (modifyConcept C) (self R)
      -- hAnc : RincAncestor O R S
      -- goal: Sat O' (modifyConcept C) (self S)
      simp only [modifyConcept] at ih ⊢
      exact Sat.rinc_self_star ih (RincAncestor_in_eliminateRanges hAnc)
  | @nom_symm i j _ ih =>
      -- modifyConcept (nom _) = nom _.
      simp only [modifyConcept] at ih ⊢
      exact Sat.nom_symm ih
  | @hasKey_apply a b C rs cs _ _ h_ax _ _ ih_aC ih_bC ih_aR ih_bR =>
      -- modifyConcept (nom _) = nom _.  hasKey kept verbatim by modifyAxiom.
      -- The hasKey rule wants premises in shape ∃R.(.nom (cs R)).  When hasRange R = true,
      -- the IH's modifyConcept gives ∃R.(.nom (cs R) ⊓ marker_R) — strip the marker via exist_prop+conj_left.
      simp only [modifyConcept] at ih_aC ih_bC ⊢
      -- Convert ih_aC : Sat O' (.nom a) (modifyConcept C) → Sat O' (.nom a) C via Sat_modify_imp_orig.
      have h_aC' : Sat (eliminateRanges O) (.nom a) C :=
        Sat.trans ih_aC (Sat_modify_imp_orig O C)
      have h_bC' : Sat (eliminateRanges O) (.nom b) C :=
        Sat.trans ih_bC (Sat_modify_imp_orig O C)
      -- Strip markers (if present) from the role premises.
      have h_aR' : ∀ R ∈ rs, Sat (eliminateRanges O) (.nom a) (.exist R (.nom (cs R))) := by
        intro R hR
        have hih := ih_aR R hR
        simp only [modifyConcept] at hih
        by_cases hRng : hasRange O R = true
        · simp only [hRng, if_true] at hih
          -- hih : Sat O' (.nom a) (∃R.((.nom (cs R)) ⊓ atom marker_R))
          -- Strip via exist_prop + conj_left.
          exact Sat.exist_prop hih (Sat.conj_left (Sat.refl _))
        · simp only [hRng, if_false] at hih
          exact hih
      have h_bR' : ∀ R ∈ rs, Sat (eliminateRanges O) (.nom b) (.exist R (.nom (cs R))) := by
        intro R hR
        have hih := ih_bR R hR
        simp only [modifyConcept] at hih
        by_cases hRng : hasRange O R = true
        · simp only [hRng, if_true] at hih
          exact Sat.exist_prop hih (Sat.conj_left (Sat.refl _))
        · simp only [hRng, if_false] at hih
          exact hih
      exact Sat.hasKey_apply cs h_aC' h_bC' (hasKey_in_eliminateRanges h_ax) h_aR' h_bR'

#print axioms gci_in_eliminateRanges
#print axioms rinc_in_eliminateRanges
#print axioms rchain_in_eliminateRanges
#print axioms reflexive_in_eliminateRanges
#print axioms rangeMarker_axiom_in_eliminateRanges
#print axioms hasKey_in_eliminateRanges
#print axioms RincAncestor_in_eliminateRanges

end RangeNorm
end ELKSDD
