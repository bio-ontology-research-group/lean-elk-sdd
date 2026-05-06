/-
  ELKSDD/DISPONTERat.lean
  -----------------------
  *Real-valued (rational) DISPONTE correspondence.*

  This module ports the unconditional DISPONTE correspondence
  (`wmc_compileSat_eq_disponteWMC` in `CompilationWMC.lean`) from
  `Nat`-valued weights to `Rat`-valued weights — the rational form of
  proper probability semantics.

  *Why `Rat`, not `ℝ`?*

    Lean 4 core ships `Rat` (rational numbers) but not `ℝ` (real
    numbers); `ℝ` is in Mathlib.  For DISPONTE-style probabilistic
    reasoning over OWL 2 EL ontologies, rational weights suffice:
      * Per-axiom probabilities `p_i ∈ Q ∩ [0,1]` are the standard
        case in practice (database-style probabilistic ontologies
        with finite-precision elicited probabilities).
      * The marginal `disponteWMC O C D w ∈ Q ∩ [0,1]` is the
        rational form of the query probability.
    Real-valued weights via Mathlib are a mechanical generalisation
    once the algebraic typeclass instances are available, but the
    `Rat` version captures the substantive content without the
    Mathlib dependency.

  *Headline theorem.*

    `wmc_compileSat_eq_disponteWMC_rat` —
        for every ontology `O`, query `(C, D)`, and rational weight
        function `w`, the rational WMC of the verified compiled SDD
        equals the rational DISPONTE marginal:
            `wmcRat (compileSat O C D) w = disponteWMCRat O C D w`.

  *Strategy.*

    The proof structure mirrors `wmc_compileSat_eq_disponteWMC` (the
    `Nat` version), with `Rat` algebra lemmas replacing `Nat` ones.
    The structural bridge `extensionList ~ enumerateWorlds` (proved
    once in `CompilationWMC.lean`) is reused; only the algebraic
    foldr-add and foldr-mul manipulations are re-done over `Rat`.

  All theorems audit-clean — only Lean foundation axioms (`propext`,
  `Classical.choice`, `Quot.sound`).  No Mathlib.
-/

import ELKSDD.MOOSE

namespace ELKSDD
namespace ELpp

open SDD

-- ============================================================
-- 1. Rat-valued analogs of the Nat-valued DISPONTE pipeline
-- ============================================================

/-- Rat-valued world weight: product of `w p (M p)` over all axiom
    positions. -/
def worldWeightRat (O : Ontology) (M : World O) (w : DispAtom O → Bool → Rat) :
    Rat :=
  (List.finRange O.length).foldr (fun i acc => w i (M i) * acc) 1

/-- Rat-valued DISPONTE marginal — the rational query probability. -/
noncomputable def disponteWMCRat (O : Ontology) (C D : Concept)
    (w : DispAtom O → Bool → Rat) : Rat := by
  classical
  exact (enumerateWorlds O.length).foldr
    (fun M acc =>
      (if Sat (selectedAxioms O M) C D then worldWeightRat O M w else 0) + acc) 0

/-- Rat-valued WMC over an SDD tree.  Standard recursive bottom-up
    Shannon-decomposition formula. -/
def wmcRat {α : Type _} : SDD.Tree α → (α → Bool → Rat) → Rat
  | .leaf b, _ => if b then 1 else 0
  | .branch p hi lo, w => w p true * wmcRat hi w + w p false * wmcRat lo w

/-- Rat-valued Shannon-recursive sum.  Mirrors `shannonSatSum` from
    `CompilationWMC.lean` but over `Rat`. -/
noncomputable def shannonSatSumRat (O : Ontology) (C D : Concept) :
    List (DispAtom O) → Assignment (DispAtom O) →
    (DispAtom O → Bool → Rat) → Rat
  | [], ctx, _ =>
      have : Decidable (Sat (selectedAxioms O ctx) C D) :=
        Classical.propDecidable _
      if Sat (selectedAxioms O ctx) C D then 1 else 0
  | p :: rest, ctx, w =>
      w p true * shannonSatSumRat O C D rest (setAt ctx p true) w +
      w p false * shannonSatSumRat O C D rest (setAt ctx p false) w

/-- Rat-valued path weight. -/
noncomputable def weightAlongRat {O : Ontology} (vs : List (DispAtom O))
    (M : Assignment (DispAtom O)) (w : DispAtom O → Bool → Rat) : Rat :=
  vs.foldr (fun p acc => w p (M p) * acc) 1

theorem weightAlongRat_cons {O : Ontology} (p : DispAtom O) (rest : List (DispAtom O))
    (M : Assignment (DispAtom O)) (w : DispAtom O → Bool → Rat) :
    weightAlongRat (p :: rest) M w = w p (M p) * weightAlongRat rest M w := rfl

-- ============================================================
-- 2. Rat foldr-add helpers
-- ============================================================

theorem foldr_add_append_rat {α : Type _} (l1 l2 : List α) (f : α → Rat) :
    (l1 ++ l2).foldr (fun a acc => f a + acc) 0 =
    l1.foldr (fun a acc => f a + acc) 0 +
    l2.foldr (fun a acc => f a + acc) 0 := by
  induction l1 with
  | nil =>
      show l2.foldr _ 0 = 0 + l2.foldr _ 0
      rw [Rat.zero_add]
  | cons x rest ih =>
      simp only [List.cons_append, List.foldr_cons]
      rw [ih, Rat.add_assoc]

theorem foldr_add_const_mul_rat {α : Type _} (l : List α) (k : Rat) (h : α → Rat) :
    l.foldr (fun a acc => k * h a + acc) 0 =
    k * l.foldr (fun a acc => h a + acc) 0 := by
  induction l with
  | nil => simp [Rat.mul_zero]
  | cons x rest ih =>
      simp only [List.foldr_cons]
      rw [ih, Rat.mul_add]

theorem foldr_add_eq_of_eqOn_rat {α : Type _} (l : List α) (f g : α → Rat)
    (h : ∀ x ∈ l, f x = g x) :
    l.foldr (fun a acc => f a + acc) 0 = l.foldr (fun a acc => g a + acc) 0 := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
      simp only [List.foldr_cons]
      have hx : f x = g x := h x List.mem_cons_self
      have hRest : ∀ y ∈ rest, f y = g y :=
        fun y hy => h y (List.mem_cons_of_mem _ hy)
      rw [hx, ih hRest]

theorem if_then_mul_zero_rat {P : Prop} [Decidable P] (k x : Rat) :
    (if P then k * x else 0) = k * (if P then x else 0) := by
  by_cases h : P
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, Rat.mul_zero]

-- ============================================================
-- 3. Perm-foldr-add (Rat)
-- ============================================================

/-- Rat-foldr-sum is permutation-invariant. -/
theorem Perm_foldr_add_eq_fn_rat {α : Type _} (f : α → Rat) (l₁ l₂ : List α)
    (h : l₁.Perm l₂) :
    l₁.foldr (fun a acc => f a + acc) 0 =
    l₂.foldr (fun a acc => f a + acc) 0 := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [List.foldr_cons]; exact congrArg _ ih
  | swap x y l =>
      show List.foldr (fun a acc => f a + acc) 0 (y :: x :: l) =
           List.foldr (fun a acc => f a + acc) 0 (x :: y :: l)
      simp only [List.foldr_cons]
      rw [← Rat.add_assoc, ← Rat.add_assoc, Rat.add_comm (f y) (f x)]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

-- ============================================================
-- 4. WMC = shannonSatSum (Rat)
-- ============================================================

theorem wmc_compileSatAux_eq_rat (O : Ontology) (C D : Concept)
    (vs : List (DispAtom O)) (ctx : Assignment (DispAtom O))
    (w : DispAtom O → Bool → Rat) :
    wmcRat (compileSatAux O C D vs ctx) w =
    shannonSatSumRat O C D vs ctx w := by
  classical
  induction vs generalizing ctx with
  | nil =>
      unfold compileSatAux shannonSatSumRat
      by_cases h : Sat (selectedAxioms O ctx) C D
      · rw [if_pos h, if_pos h]; rfl
      · rw [if_neg h, if_neg h]; rfl
  | cons p rest ih =>
      unfold compileSatAux shannonSatSumRat
      rw [wmcRat, ih, ih]

theorem wmc_compileSat_eq_shannonSatSum_rat (O : Ontology) (C D : Concept)
    (w : DispAtom O → Bool → Rat) :
    wmcRat (compileSat O C D) w =
    shannonSatSumRat O C D (List.finRange O.length) (fun _ => false) w := by
  unfold compileSat
  exact wmc_compileSatAux_eq_rat O C D _ _ w

-- ============================================================
-- 5. shannonSatSumRat = foldr over extensionList (Rat)
-- ============================================================

theorem shannonSatSumRat_eq_foldr_extensionList (O : Ontology) (C D : Concept)
    (vs : List (DispAtom O)) (ctx : Assignment (DispAtom O))
    (w : DispAtom O → Bool → Rat) (hNodup : vs.Nodup) :
    letI : ∀ M : Assignment (DispAtom O), Decidable (Sat (selectedAxioms O M) C D) :=
      fun _ => Classical.propDecidable _
    shannonSatSumRat O C D vs ctx w =
    (extensionList vs ctx).foldr
      (fun M acc =>
        (if Sat (selectedAxioms O M) C D then weightAlongRat vs M w else 0) + acc) 0 := by
  classical
  induction vs generalizing ctx with
  | nil =>
      simp only [shannonSatSumRat, extensionList, List.foldr_cons, List.foldr_nil]
      by_cases h : Sat (selectedAxioms O ctx) C D
      · rw [if_pos h, if_pos h]
        show (1 : Rat) = weightAlongRat [] _ w + 0
        rw [Rat.add_zero]
        rfl
      · rw [if_neg h, if_neg h]; rw [Rat.add_zero]
  | cons p rest ih =>
      have hpNotInRest : p ∉ rest := by
        rw [List.nodup_cons] at hNodup; exact hNodup.1
      have hRestNodup : rest.Nodup := by
        rw [List.nodup_cons] at hNodup; exact hNodup.2
      simp only [shannonSatSumRat, extensionList]
      rw [ih (setAt ctx p true) hRestNodup, ih (setAt ctx p false) hRestNodup]
      rw [foldr_add_append_rat]
      have key : ∀ b : Bool,
          w p b *
            (extensionList rest (setAt ctx p b)).foldr
              (fun M acc =>
                (if Sat (selectedAxioms O M) C D then weightAlongRat rest M w else 0) + acc) 0 =
          (extensionList rest (setAt ctx p b)).foldr
            (fun M acc =>
              (if Sat (selectedAxioms O M) C D then weightAlongRat (p :: rest) M w else 0) + acc) 0 := by
        intro b
        have hVal : ∀ M ∈ extensionList rest (setAt ctx p b),
            (if Sat (selectedAxioms O M) C D then weightAlongRat (p :: rest) M w else 0) =
            (if Sat (selectedAxioms O M) C D then w p b * weightAlongRat rest M w else 0) := by
          intro M hM
          have hMp : M p = b := mem_extensionList_value rest ctx p b hpNotInRest M hM
          show (if _ then weightAlongRat (p :: rest) M w else 0) = _
          unfold weightAlongRat
          simp only [List.foldr_cons]
          rw [hMp]
        rw [foldr_add_eq_of_eqOn_rat _ _ _ hVal]
        have hFactor : ∀ M ∈ extensionList rest (setAt ctx p b),
            (if Sat (selectedAxioms O M) C D then w p b * weightAlongRat rest M w else 0) =
            w p b * (if Sat (selectedAxioms O M) C D then weightAlongRat rest M w else 0) := by
          intro M _
          exact if_then_mul_zero_rat (w p b) (weightAlongRat rest M w)
        rw [foldr_add_eq_of_eqOn_rat _ _ _ hFactor]
        rw [foldr_add_const_mul_rat]
      rw [← key true, ← key false]

theorem weightAlongRat_finRange_eq_worldWeightRat (O : Ontology)
    (M : Assignment (DispAtom O)) (w : DispAtom O → Bool → Rat) :
    weightAlongRat (List.finRange O.length) M w = worldWeightRat O M w := by
  unfold weightAlongRat worldWeightRat
  rfl

-- ============================================================
-- 6. THE UNCONDITIONAL RAT-VALUED DISPONTE CORRESPONDENCE
-- ============================================================

/-- **The unconditional rational DISPONTE correspondence theorem.**
    For every ontology `O`, query `(C, D)`, and rational weight
    function `w`, the rational WMC of the verified compiled SDD
    equals the rational DISPONTE distribution-semantics marginal.
    *No free hypothesis* — all premises are discharged.

    This is the rational form of proper probability semantics: when
    weights `w(p, b) ∈ Q ∩ [0,1]` model per-axiom inclusion
    probabilities, `disponteWMCRat O C D w` is the rational marginal
    probability `P(O ⊨ q)` where the quantifier ranges over the
    DISPONTE world distribution. -/
theorem wmc_compileSat_eq_disponteWMC_rat (O : Ontology) (C D : Concept)
    (w : DispAtom O → Bool → Rat) :
    wmcRat (compileSat O C D) w = disponteWMCRat O C D w := by
  classical
  rw [wmc_compileSat_eq_shannonSatSum_rat]
  rw [shannonSatSumRat_eq_foldr_extensionList O C D
        (List.finRange O.length) (fun _ => false) w (finRange_Nodup _)]
  have hSummand :
      ∀ M ∈ extensionList (List.finRange O.length) (fun _ => false : Assignment (DispAtom O)),
        (if Sat (selectedAxioms O M) C D then weightAlongRat (List.finRange O.length) M w else 0) =
        (if Sat (selectedAxioms O M) C D then worldWeightRat O M w else 0) := by
    intro M _
    rw [weightAlongRat_finRange_eq_worldWeightRat]
  rw [foldr_add_eq_of_eqOn_rat _ _ _ hSummand]
  have hPerm := extensionList_finRange_perm_enumerateWorlds (O := O) (fun _ => false)
  rw [Perm_foldr_add_eq_fn_rat _ _ _ hPerm]
  rfl

/-- **Clean restatement.**  The MOOSE inference pipeline computes the
    rational DISPONTE marginal for every weight function. -/
theorem compileSat_disponte_correspondence_rat (O : Ontology) (C D : Concept) :
    ∀ w : DispAtom O → Bool → Rat,
      wmcRat (compileSat O C D) w = disponteWMCRat O C D w :=
  fun w => wmc_compileSat_eq_disponteWMC_rat O C D w

/-- **Existence form.**  There exists a verified SDD tree such that
    its rational WMC equals the rational DISPONTE marginal for every
    weight function.  Witness: `compileSat O C D`. -/
theorem exists_disponte_correspondence_rat (O : Ontology) (C D : Concept) :
    ∃ tree : Tree (DispAtom O),
      SDDEncodesQuery O C D tree ∧
      ∀ w : DispAtom O → Bool → Rat, wmcRat tree w = disponteWMCRat O C D w :=
  ⟨compileSat O C D,
   compileSat_correct O C D,
   compileSat_disponte_correspondence_rat O C D⟩

-- ============================================================
-- 7. Audit
-- ============================================================

#print axioms wmc_compileSat_eq_disponteWMC_rat
#print axioms compileSat_disponte_correspondence_rat
#print axioms exists_disponte_correspondence_rat

end ELpp
end ELKSDD
