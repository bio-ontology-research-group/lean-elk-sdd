/-
  ELKSDD/Stratified.lean
  ----------------------
  Layers 4–5 of the full-algorithm proof: time-stamped Clark
  completion of the EL_⊥^+ calculus.

  This module exposes the *algorithmic content* of the inductive
  closure relation `Sat O` from `ELKSDD.ELpp`:

    1.  `SatAt O k C D` — a *time-stamped* (depth-bounded) Sat
        predicate: `C ⊑ D` is derivable using a derivation tree of
        depth ≤ k.

    2.  `Sat O C D ↔ ∃ k, SatAt O k C D` — every closed atom has a
        finite derivation depth, witnessing finite stratification of
        the inductive closure.

    3.  Monotonicity in depth and rule structure: `SatAt O k C D →
        SatAt O (k+1) C D`, plus admissibility of all calculus rules
        at the time-stamped level.

  -------------------------------------------------------------
  Algorithmic interpretation (Clark completion)
  -------------------------------------------------------------

  Reading `Sat O` as a positive datalog program (one Horn clause
  per constructor of `Sat`), the *Clark completion* of the program
  is the if-and-only-if encoding of each predicate.  The least
  Herbrand model of the Clark completion is the union over k of
  the "stage k" interpretations:

        T^0(P) := ∅
        T^{k+1}(P) := { atoms derivable from T^k(P) using one rule
                        of P }
        lfp T(P)  := ⋃_k T^k(P).

  In Lean 4, this iteration is realised by the inductive `Sat`
  itself — the least Prop-valued relation closed under the
  constructors.  The `SatAt` family in this module makes the
  staging *explicit* — `SatAt O k C D` is exactly the predicate
  "C ⊑ D ∈ T^k({Sat-rules})".  The equivalence theorem then
  expresses that the algorithmic fixpoint converges (depth-
  collapse) to the calculus closure.

  -------------------------------------------------------------
  Termination
  -------------------------------------------------------------

  Combined with the closure-size bound (paper Theorem T1, Lean
  `elk_closure_size_bound` in `Moose/Prior.lean`) on the *enumerated*
  closure list `Sat O = atomEnum O ++ linkEnum O ++ reflEnum O`, the
  time-stamped fixpoint terminates after at most `|Sat O|` iterations
  — each iteration adds at least one new atom, and the closure is
  bounded by the enumeration cardinality.  We do *not* re-prove that
  bound here (it is on a different `Sat`-as-enumeration object than
  this module's `Sat`-as-Prop); the depth-existence theorem
  `Sat_iff_SatAt` is the load-bearing finiteness witness for Layer 5.

  -------------------------------------------------------------
  Lean dependencies
  -------------------------------------------------------------

  Imports `ELKSDD.ELpp` only (Layer 1+3).  No Mathlib.  No prior-
  work axioms admitted.  Foundation axioms only (propext / Quot.sound).

  References:
    [Clark 1978]      K.L. Clark.  Negation as Failure.  In
                      Logic and Data Bases, Plenum Press, 1978.
    [Apt-Blair-Walker 1988]  Towards a Theory of Declarative
                      Knowledge.  In Foundations of Deductive
                      Databases and Logic Programming, 1988.
                      (Stratified-program semantics.)
-/

import ELKSDD.ELpp

namespace ELKSDD
namespace Stratified

open ELpp

-- ============================================================
-- 0. Helpers — foldr-max bound
-- ============================================================

/-- For any `f : α → Nat` and any list `xs : List α`, the
    foldr-max `xs.foldr (fun x acc => max (f x) acc) 0` upper-bounds
    `f x` for every `x ∈ xs`. -/
theorem foldr_max_ge {α : Type} (f : α → Nat) :
    ∀ (xs : List α) (x : α), x ∈ xs →
      f x ≤ xs.foldr (fun y acc => Nat.max (f y) acc) 0 := by
  intro xs
  induction xs with
  | nil => intro x hx; exact (List.not_mem_nil hx).elim
  | cons y ys ih =>
      intro x hx
      rcases List.mem_cons.mp hx with hEq | hMem
      · subst hEq
        simp only [List.foldr_cons]
        exact Nat.le_max_left _ _
      · simp only [List.foldr_cons]
        exact Nat.le_trans (ih x hMem) (Nat.le_max_right _ _)

-- ============================================================
-- 1. Time-stamped saturation predicate
-- ============================================================

/-- `SatAt O k C D` — `C ⊑ D` is derivable in EL_⊥^+ at depth ≤ k.

    Each constructor mirrors the corresponding constructor of
    `Sat O`, but premises must be at depth `k` and the conclusion is
    at depth `k+1`.  The reflexivity-and-top axioms are admitted at
    every depth (they are derivation-axiomatic).

    The `weaken` constructor witnesses depth-monotonicity directly.
-/
inductive SatAt (O : Ontology) : Nat → Concept → Concept → Prop where
  | refl       : ∀ k C, SatAt O k C C
  | top        : ∀ k C, SatAt O k C .top
  | weaken     : ∀ {k C D}, SatAt O k C D → SatAt O (k+1) C D
  | base_gci   : ∀ {k C D}, Axiom.gci C D ∈ O → SatAt O (k+1) C D
  | trans      : ∀ {k C D E},
      SatAt O k C D → SatAt O k D E → SatAt O (k+1) C E
  | conj_left  : ∀ {k C D₁ D₂},
      SatAt O k C (.conj D₁ D₂) → SatAt O (k+1) C D₁
  | conj_right : ∀ {k C D₁ D₂},
      SatAt O k C (.conj D₁ D₂) → SatAt O (k+1) C D₂
  | conj_intro : ∀ {k C D₁ D₂},
      SatAt O k C D₁ → SatAt O k C D₂ → SatAt O (k+1) C (.conj D₁ D₂)
  | bot_elim   : ∀ {k C D},
      SatAt O k C .bot → SatAt O (k+1) C D
  | exist_prop : ∀ {k C R D E},
      SatAt O k C (.exist R D) → SatAt O k D E → SatAt O (k+1) C (.exist R E)
  | exist_bot  : ∀ {k C R D},
      SatAt O k C (.exist R D) → SatAt O k D .bot → SatAt O (k+1) C .bot
  | rinc_apply : ∀ {k C R S D},
      SatAt O k C (.exist R D) → Axiom.rinc R S ∈ O →
        SatAt O (k+1) C (.exist S D)
  | rchain_apply : ∀ {k C R₁ R₂ S D E},
      SatAt O k C (.exist R₁ D) → SatAt O k D (.exist R₂ E) →
      Axiom.rchain R₁ R₂ S ∈ O → SatAt O (k+1) C (.exist S E)
  | range_apply : ∀ {k C R D E},
      SatAt O k C (.exist R D) → Axiom.range R E ∈ O →
        SatAt O (k+1) C (.exist R (.conj D E))
  | reflexive_apply : ∀ {k C R},
      Axiom.reflexive R ∈ O → SatAt O (k+1) C (.exist R C)
  | self_intro : ∀ {k C R},
      SatAt O k C (.self R) → SatAt O (k+1) C (.exist R C)
  | reflexive_self : ∀ {k C R},
      Axiom.reflexive R ∈ O → SatAt O (k+1) C (.self R)
  | self_range : ∀ {k C R E},
      SatAt O k C (.self R) → Axiom.range R E ∈ O → SatAt O (k+1) C E
  | range_via_rincStar : ∀ {k C R S D E},
      SatAt O k C (.exist R D) → RincAncestor O R S →
      Axiom.range S E ∈ O →
      SatAt O (k+1) C (.exist R (.conj D E))
  | rinc_self_star : ∀ {k C R S},
      SatAt O k C (.self R) → RincAncestor O R S →
      SatAt O (k+1) C (.self S)
  | nom_symm : ∀ {k i j},
      SatAt O k (.nom i) (.nom j) → SatAt O (k+1) (.nom j) (.nom i)
  | hasKey_apply : ∀ {k a b C rs} (cs : Role → Nat),
      SatAt O k (.nom a) C → SatAt O k (.nom b) C →
      Axiom.hasKey C rs ∈ O →
      (∀ R, R ∈ rs → SatAt O k (.nom a) (.exist R (.nom (cs R)))) →
      (∀ R, R ∈ rs → SatAt O k (.nom b) (.exist R (.nom (cs R)))) →
      SatAt O (k+1) (.nom a) (.nom b)

-- ============================================================
-- 2. Depth monotonicity
-- ============================================================

/-- `SatAt` is monotone in the depth: if `SatAt O k C D` then
    `SatAt O (k+1) C D`.  Direct from the `weaken` constructor. -/
theorem SatAt_succ {O : Ontology} {k : Nat} {C D : Concept}
    (h : SatAt O k C D) : SatAt O (k+1) C D :=
  SatAt.weaken h

/-- General monotonicity: `SatAt O k C D → SatAt O k' C D` for `k ≤ k'`.
    Proof: induction on `k' - k` via repeated `weaken`. -/
theorem SatAt_mono {O : Ontology} {k k' : Nat} {C D : Concept}
    (h : SatAt O k C D) (hle : k ≤ k') : SatAt O k' C D := by
  induction hle with
  | refl => exact h
  | step _ ih => exact SatAt.weaken ih

-- ============================================================
-- 3. Forward: Sat ⊆ ∃k, SatAt
-- ============================================================

/-- Every `Sat`-derivable atom has a finite derivation depth.
    Proof: induction on the `Sat` derivation, taking the max of
    the IH depths and adding 1.  Each constructor of `Sat`
    corresponds to a constructor of `SatAt` after adjusting depths
    via `SatAt_mono`. -/
theorem Sat_to_SatAt {O : Ontology} {C D : Concept}
    (h : Sat O C D) : ∃ k, SatAt O k C D := by
  induction h with
  | refl _ =>
      exact ⟨0, SatAt.refl 0 _⟩
  | top _ =>
      exact ⟨0, SatAt.top 0 _⟩
  | base_gci hax =>
      exact ⟨1, SatAt.base_gci hax⟩
  | trans _ _ ihCD ihDE =>
      obtain ⟨k₁, hCD⟩ := ihCD
      obtain ⟨k₂, hDE⟩ := ihDE
      exact ⟨max k₁ k₂ + 1,
             SatAt.trans
               (SatAt_mono hCD (Nat.le_max_left _ _))
               (SatAt_mono hDE (Nat.le_max_right _ _))⟩
  | conj_left _ ih =>
      obtain ⟨k, h⟩ := ih
      exact ⟨k+1, SatAt.conj_left h⟩
  | conj_right _ ih =>
      obtain ⟨k, h⟩ := ih
      exact ⟨k+1, SatAt.conj_right h⟩
  | conj_intro _ _ ih₁ ih₂ =>
      obtain ⟨k₁, h₁⟩ := ih₁
      obtain ⟨k₂, h₂⟩ := ih₂
      exact ⟨max k₁ k₂ + 1,
             SatAt.conj_intro
               (SatAt_mono h₁ (Nat.le_max_left _ _))
               (SatAt_mono h₂ (Nat.le_max_right _ _))⟩
  | bot_elim _ ih =>
      obtain ⟨k, h⟩ := ih
      exact ⟨k+1, SatAt.bot_elim h⟩
  | exist_prop _ _ ihCRD ihDE =>
      obtain ⟨k₁, hCRD⟩ := ihCRD
      obtain ⟨k₂, hDE⟩ := ihDE
      exact ⟨max k₁ k₂ + 1,
             SatAt.exist_prop
               (SatAt_mono hCRD (Nat.le_max_left _ _))
               (SatAt_mono hDE (Nat.le_max_right _ _))⟩
  | exist_bot _ _ ihCRD ihDbot =>
      obtain ⟨k₁, hCRD⟩ := ihCRD
      obtain ⟨k₂, hDbot⟩ := ihDbot
      exact ⟨max k₁ k₂ + 1,
             SatAt.exist_bot
               (SatAt_mono hCRD (Nat.le_max_left _ _))
               (SatAt_mono hDbot (Nat.le_max_right _ _))⟩
  | rinc_apply _ hax ih =>
      obtain ⟨k, h⟩ := ih
      exact ⟨k+1, SatAt.rinc_apply h hax⟩
  | rchain_apply _ _ hax ihCR1 ihDR2 =>
      obtain ⟨k₁, hCR1⟩ := ihCR1
      obtain ⟨k₂, hDR2⟩ := ihDR2
      exact ⟨max k₁ k₂ + 1,
             SatAt.rchain_apply
               (SatAt_mono hCR1 (Nat.le_max_left _ _))
               (SatAt_mono hDR2 (Nat.le_max_right _ _))
               hax⟩
  | range_apply _ hax ih =>
      obtain ⟨k, h⟩ := ih
      exact ⟨k+1, SatAt.range_apply h hax⟩
  | reflexive_apply hax =>
      exact ⟨1, SatAt.reflexive_apply hax⟩
  | self_intro _ ih =>
      obtain ⟨k, h⟩ := ih
      exact ⟨k+1, SatAt.self_intro h⟩
  | reflexive_self hax =>
      exact ⟨1, SatAt.reflexive_self hax⟩
  | self_range _ hax ih =>
      obtain ⟨k, h⟩ := ih
      exact ⟨k+1, SatAt.self_range h hax⟩
  | range_via_rincStar _ hAnc hRange ih =>
      obtain ⟨k, h⟩ := ih
      exact ⟨k+1, SatAt.range_via_rincStar h hAnc hRange⟩
  | rinc_self_star _ hAnc ih =>
      obtain ⟨k, h⟩ := ih
      exact ⟨k+1, SatAt.rinc_self_star h hAnc⟩
  | nom_symm _ ih =>
      obtain ⟨k, h⟩ := ih
      exact ⟨k+1, SatAt.nom_symm h⟩
  | @hasKey_apply a b C rs cs _ _ h_ax _ _ ih_aC ih_bC ih_aR ih_bR =>
      classical
      obtain ⟨k₁, h_aC_k⟩ := ih_aC
      obtain ⟨k₂, h_bC_k⟩ := ih_bC
      -- For each R in rs, classical-choose a uniform pair-depth.
      have h_pair : ∀ R, R ∈ rs → ∃ k,
          SatAt O k (.nom a) (.exist R (.nom (cs R))) ∧
          SatAt O k (.nom b) (.exist R (.nom (cs R))) := by
        intro R hR
        obtain ⟨ka, ha⟩ := ih_aR R hR
        obtain ⟨kb, hb⟩ := ih_bR R hR
        exact ⟨Nat.max ka kb,
               SatAt_mono ha (Nat.le_max_left _ _),
               SatAt_mono hb (Nat.le_max_right _ _)⟩
      -- Build a per-role depth function and its list-max bound.
      let kR : Role → Nat := fun R =>
        if h : R ∈ rs then Classical.choose (h_pair R h) else 0
      let kFold : Nat := rs.foldr (fun R acc => Nat.max (kR R) acc) 0
      -- Foldr-max lemma: every kR R for R ∈ rs is bounded by kFold.
      have kR_le_fold : ∀ R, R ∈ rs → kR R ≤ kFold := fun R hR =>
        foldr_max_ge kR rs R hR
      let kAll : Nat := Nat.max (Nat.max k₁ k₂) kFold
      refine ⟨kAll + 1, SatAt.hasKey_apply cs ?_ ?_ h_ax ?_ ?_⟩
      · exact SatAt_mono h_aC_k
          (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
      · exact SatAt_mono h_bC_k
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
      · intro R hR
        have hkR_def : kR R = Classical.choose (h_pair R hR) := by
          show (if h : R ∈ rs then Classical.choose (h_pair R h) else 0) = _
          rw [dif_pos hR]
        have h_at_kR : SatAt O (kR R) (.nom a) (.exist R (.nom (cs R))) := by
          rw [hkR_def]
          exact (Classical.choose_spec (h_pair R hR)).1
        exact SatAt_mono h_at_kR
          (Nat.le_trans (kR_le_fold R hR) (Nat.le_max_right _ _))
      · intro R hR
        have hkR_def : kR R = Classical.choose (h_pair R hR) := by
          show (if h : R ∈ rs then Classical.choose (h_pair R h) else 0) = _
          rw [dif_pos hR]
        have h_at_kR : SatAt O (kR R) (.nom b) (.exist R (.nom (cs R))) := by
          rw [hkR_def]
          exact (Classical.choose_spec (h_pair R hR)).2
        exact SatAt_mono h_at_kR
          (Nat.le_trans (kR_le_fold R hR) (Nat.le_max_right _ _))

-- ============================================================
-- 4. Backward: SatAt ⊆ Sat
-- ============================================================

/-- Every depth-bounded derivation is a `Sat` derivation.
    Proof: induction on the `SatAt` derivation; depth annotations
    are erased and each constructor maps to its `Sat` analogue. -/
theorem SatAt_to_Sat {O : Ontology} : ∀ {k C D},
    SatAt O k C D → Sat O C D := by
  intro k C D h
  induction h with
  | refl _ _ => exact Sat.refl _
  | top _ _ => exact Sat.top _
  | weaken _ ih => exact ih
  | base_gci hax => exact Sat.base_gci hax
  | trans _ _ ihCD ihDE => exact Sat.trans ihCD ihDE
  | conj_left _ ih => exact Sat.conj_left ih
  | conj_right _ ih => exact Sat.conj_right ih
  | conj_intro _ _ ih₁ ih₂ => exact Sat.conj_intro ih₁ ih₂
  | bot_elim _ ih => exact Sat.bot_elim ih
  | exist_prop _ _ ihCRD ihDE => exact Sat.exist_prop ihCRD ihDE
  | exist_bot _ _ ihCRD ihDbot => exact Sat.exist_bot ihCRD ihDbot
  | rinc_apply _ hax ih => exact Sat.rinc_apply ih hax
  | rchain_apply _ _ hax ihCR1 ihDR2 => exact Sat.rchain_apply ihCR1 ihDR2 hax
  | range_apply _ hax ih => exact Sat.range_apply ih hax
  | reflexive_apply hax => exact Sat.reflexive_apply hax
  | self_intro _ ih => exact Sat.self_intro ih
  | reflexive_self hax => exact Sat.reflexive_self hax
  | self_range _ hax ih => exact Sat.self_range ih hax
  | range_via_rincStar _ hAnc hRange ih => exact Sat.range_via_rincStar ih hAnc hRange
  | rinc_self_star _ hAnc ih => exact Sat.rinc_self_star ih hAnc
  | nom_symm _ ih => exact Sat.nom_symm ih
  | @hasKey_apply k a b C rs cs _ _ h_ax _ _ ih_aC ih_bC ih_aR ih_bR =>
      exact Sat.hasKey_apply cs ih_aC ih_bC h_ax ih_aR ih_bR

-- ============================================================
-- 5. The equivalence — Layer 5 main theorem
-- ============================================================

/-- **Time-stamped Clark equivalence (Layer 5 main result).**
    The inductive closure equals the union over all finite depths
    of the time-stamped fixpoint:

        Sat O C D  ↔  ∃ k : Nat,  SatAt O k C D.

    This is the algorithmic content of the calculus: every derivable
    atom has a finite derivation depth, so the iterative fixpoint
    procedure converges in finite time on any concrete (finite)
    ontology. -/
theorem Sat_iff_SatAt {O : Ontology} {C D : Concept} :
    Sat O C D ↔ ∃ k, SatAt O k C D :=
  ⟨Sat_to_SatAt, fun ⟨_, h⟩ => SatAt_to_Sat h⟩

-- ============================================================
-- 6. Cumulative fixpoint: SatUpTo k = ⋃ k' ≤ k SatAt O k'
-- ============================================================

/-- For convenience and to mirror the algorithmic intuition,
    `SatUpTo O k C D` packages "derivable at *some* depth ≤ k".
    Definitionally equal to `SatAt O k C D` thanks to `weaken`,
    but we expose the abbreviation to highlight the cumulative
    reading. -/
def SatUpTo (O : Ontology) (k : Nat) (C D : Concept) : Prop :=
  SatAt O k C D

theorem SatUpTo_mono {O : Ontology} {k k' : Nat} {C D : Concept}
    (h : SatUpTo O k C D) (hle : k ≤ k') : SatUpTo O k' C D :=
  SatAt_mono h hle

theorem Sat_iff_SatUpTo {O : Ontology} {C D : Concept} :
    Sat O C D ↔ ∃ k, SatUpTo O k C D :=
  Sat_iff_SatAt

-- ============================================================
-- 7. Fixpoint convergence statement
-- ============================================================

/-- A *fixpoint depth* is a `K` such that `SatAt O K` already
    contains every `Sat`-derivable atom.  The existence of a
    fixpoint depth witnesses termination of the iterative procedure. -/
def IsFixpointDepth (O : Ontology) (K : Nat) : Prop :=
  ∀ C D, Sat O C D → SatAt O K C D

/-- Equivalent fixpoint-depth characterisation: depths `K` such that
    `SatAt O (K+1)` adds nothing beyond `SatAt O K`. -/
def IsClosedDepth (O : Ontology) (K : Nat) : Prop :=
  ∀ C D, SatAt O (K+1) C D → SatAt O K C D

/-- A fixpoint depth is also closed (the converse holds under finite
    closure size, but isn't needed for our purposes). -/
theorem IsFixpointDepth_imp_IsClosedDepth {O : Ontology} {K : Nat}
    (h : IsFixpointDepth O K) : IsClosedDepth O K := by
  intro C D hK1
  apply h C D
  exact SatAt_to_Sat hK1

end Stratified
end ELKSDD
