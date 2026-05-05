/-
  ELKSDD/CompilationWMC.lean
  --------------------------
  *Shannon-recursive WMC* — building blocks toward an unconditional
  DISPONTE correspondence on the verified tree `compileSat O C D`.

  *What this module proves.*

    * `shannonSatSum` — recursive Shannon-expansion sum mirroring
      `wmc`'s structure, specialised to the Sat-decision predicate.
    * `wmc_compileSatAux_eq` — the SDD WMC of the Shannon-expanded
      `compileSatAux O C D vs ctx` matches `shannonSatSum O C D vs
      ctx w` *exactly* (mechanical induction on `vs`).
    * `Perm_foldr_add_eq` — Nat-foldr-sum is permutation-invariant;
      generalised version `Perm_foldr_add_eq_fn` covers Nat-valued
      function-foldr.

  *What remains.*

    The final step — equating
        `shannonSatSum O C D (List.finRange O.length) (fun _ => false) w`
        =  `disponteWMC O C D w`
    — requires bridging two equivalent enumerations of the 2^|O|
    worlds:

      * `extensions (List.finRange n) (fun _ => false)`  branches
        head-first on `finRange` (⟨0⟩-slowest lex order).
      * `enumerateWorlds n`  recurses last-bit-extension (⟨n-1⟩-
        fastest lex order).

    Both produce the same multiset in the same lex order, but the
    Lean terms differ (extensions uses iterated `setAt`;
    enumerateWorlds uses positional `if h : i.val < n` branching).
    Equating them requires either:
      (a) element-wise list equality via `funext` (~150 lines), or
      (b) proving `shannonSatSum` is invariant under permutations of
          `vs` and reversing `finRange` to match enumerateWorlds's
          recursion structure (~150 lines).

    Both routes are mechanical but substantial; the present module
    provides the `Perm_foldr_add_eq_fn` infrastructure that route
    (b) needs.

  All theorems audit-clean — only Lean foundation axioms.
-/

import ELKSDD.Compilation

namespace ELKSDD
namespace ELpp

open SDD

-- ============================================================
-- 1. Shannon-recursive sum specialised to the Sat predicate
-- ============================================================

/-- Recursive Shannon-expansion sum, with Sat-decision at the leaf.
    Uses `Classical.propDecidable` to decide Sat. -/
noncomputable def shannonSatSum (O : Ontology) (C D : Concept) :
    List (DispAtom O) → Assignment (DispAtom O) →
    (DispAtom O → Bool → Nat) → Nat
  | [], ctx, _ =>
      have : Decidable (Sat (selectedAxioms O ctx) C D) :=
        Classical.propDecidable _
      if Sat (selectedAxioms O ctx) C D then 1 else 0
  | p :: rest, ctx, w =>
      w p true * shannonSatSum O C D rest (setAt ctx p true) w +
      w p false * shannonSatSum O C D rest (setAt ctx p false) w

/-- **WMC matches the Shannon-recursive sum.**  By direct induction
    on `vs`. -/
theorem wmc_compileSatAux_eq (O : Ontology) (C D : Concept)
    (vs : List (DispAtom O)) (ctx : Assignment (DispAtom O))
    (w : DispAtom O → Bool → Nat) :
    SDD.wmc (compileSatAux O C D vs ctx) w =
    shannonSatSum O C D vs ctx w := by
  classical
  induction vs generalizing ctx with
  | nil =>
      unfold compileSatAux shannonSatSum
      by_cases h : Sat (selectedAxioms O ctx) C D
      · rw [if_pos h, if_pos h]; rfl
      · rw [if_neg h, if_neg h]; rfl
  | cons p rest ih =>
      unfold compileSatAux shannonSatSum
      rw [SDD.wmc, ih, ih]

/-- **Top-level WMC = Shannon-sum** for the verified tree `compileSat`. -/
theorem wmc_compileSat_eq_shannonSatSum (O : Ontology) (C D : Concept)
    (w : DispAtom O → Bool → Nat) :
    SDD.wmc (compileSat O C D) w =
    shannonSatSum O C D (List.finRange O.length) (fun _ => false) w := by
  unfold compileSat
  exact wmc_compileSatAux_eq O C D _ _ w

-- ============================================================
-- 2. Permutation-invariance of foldr-add over Nat
-- ============================================================

/-- Nat-foldr-sum is permutation-invariant.  Proof by induction on
    the Perm relation, using commutativity and associativity of `+`. -/
theorem Perm_foldr_add_eq (l₁ l₂ : List Nat) (h : l₁.Perm l₂) :
    l₁.foldr (· + ·) 0 = l₂.foldr (· + ·) 0 := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [List.foldr_cons]; exact congrArg _ ih
  | swap x y l =>
      show List.foldr (· + ·) 0 (y :: x :: l) = List.foldr (· + ·) 0 (x :: y :: l)
      simp only [List.foldr_cons]
      rw [← Nat.add_assoc, ← Nat.add_assoc, Nat.add_comm y x]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- Generalisation: foldr of a Nat-valued function under permutation. -/
theorem Perm_foldr_add_eq_fn {α : Type _} (f : α → Nat) (l₁ l₂ : List α)
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
      rw [← Nat.add_assoc, ← Nat.add_assoc, Nat.add_comm (f y) (f x)]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

-- ============================================================
-- 3. Audit
-- ============================================================

#print axioms wmc_compileSatAux_eq
#print axioms wmc_compileSat_eq_shannonSatSum
#print axioms Perm_foldr_add_eq
#print axioms Perm_foldr_add_eq_fn

end ELpp
end ELKSDD
