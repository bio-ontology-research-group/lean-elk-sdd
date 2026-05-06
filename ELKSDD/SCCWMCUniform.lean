/-
  ELKSDD/SCCWMCUniform.lean
  -------------------------
  *World-restriction summation identity* for WMC-level SCC
  factorization under uniform weights.

  This module proves the key combinatorial identity needed to lift
  the per-world Sat factor (`per_world_sat_factor_consistent` in
  `SCCWorld.lean`) to a closed-form WMC factorization:

    ∀ n m : Nat, ∀ f : (Fin n → Bool) → Rat,
      Σ_{M ∈ enumerateWorlds (n+m)} f (restrictFirst n m M)
      = (Σ_{M' ∈ enumerateWorlds n} f M') · 2^m.

  *Proof strategy.*

    Induction on `m`.  The base case (`m = 0`) is direct.  The
    inductive step uses `enumerateWorlds (n+k+1) = (enumerateWorlds
    (n+k)).flatMap [extLast true, extLast false]`, foldr-flatMap
    expansion, and the observation that `restrictFirst n (k+1)
    (extLast M' b) = restrictFirst n k M'` (since `extLast` only
    adds at the last position, beyond the first `n` bits).

    The key Rat-arithmetic identity `a + (a + (b + b)) = (a + b) +
    (a + b)` is proved manually via `Rat.add_assoc` and
    `Rat.add_comm` (since `ring` is not in Lean core).

  *Application.*

    Combined with `per_world_sat_factor_consistent`, this yields the
    closed-form WMC-level SCC factorization under uniform weights:
       disponteWMCRat (O₁ ++ O₂) C D uniform = disponteWMCRat O₁ C D
       uniform · 2^|O₂|
    The length-cast bridge `(O₁ ++ O₂).length = O₁.length + O₂.length`
    via `List.length_append` is handled by
    `sum_enumerateWorlds_factor_general`, which uses `subst` to lift
    the canonical identity to any propositionally-equivalent length.

  All theorems audit-clean — only Lean foundation axioms.  No
  Mathlib.
-/

import ELKSDD.SCCWorld
import ELKSDD.DISPONTERat

namespace ELKSDD
namespace ELpp

open SDD SCC Normalize

-- ============================================================
-- Helper: restrict a Fin (n+m) → Bool function to its first n bits.
-- ============================================================

noncomputable def restrictFirst (n m : Nat) (M : Fin (n + m) → Bool) : Fin n → Bool :=
  fun i => M ⟨i.val, by omega⟩

theorem restrictFirst_extLast (n k : Nat) (M : Fin (n + k) → Bool) (b : Bool) :
    restrictFirst n (k + 1)
      (fun i : Fin (n + k + 1) => if h : i.val < n + k then M ⟨i.val, h⟩ else b)
    = restrictFirst n k M := by
  funext i
  unfold restrictFirst
  have hi : i.val < n + k := by omega
  show (if h : (⟨i.val, by omega⟩ : Fin (n + k + 1)).val < n + k then M ⟨_, h⟩ else b) =
       M ⟨i.val, by omega⟩
  rw [dif_pos hi]

-- ============================================================
-- Rat arithmetic helper
-- ============================================================

private theorem rat_quad_rearrange (a b : Rat) :
    a + (a + (b + b)) = (a + b) + (a + b) := by
  rw [← Rat.add_assoc a a (b + b),
      ← Rat.add_assoc (a + b) a b,
      Rat.add_assoc a b a,
      Rat.add_comm b a,
      ← Rat.add_assoc a a b,
      Rat.add_assoc (a + a) b b]

-- ============================================================
-- THE WORLD-SUMMATION FACTORIZATION IDENTITY
-- ============================================================

/-- **World-summation factorization.**

    For any function `f : (Fin n → Bool) → Rat`, the sum of
    `f (restrictFirst n m M)` over all `M ∈ enumerateWorlds (n+m)`
    factors as `(Σ over enumerateWorlds n of f) · 2^m`.

    This is the combinatorial heart of the WMC-level SCC
    factorization: when the summand depends only on the first `n`
    bits of a `(n+m)`-bit world, the sum factors with the trailing
    `2^m` worlds contributing equally.

    Proof: induction on `m`.  The inductive step uses
    `enumerateWorlds`'s flatMap structure and `restrictFirst_extLast`. -/
theorem sum_enumerateWorlds_factor (n m : Nat) (f : (Fin n → Bool) → Rat) :
    (enumerateWorlds (n + m)).foldr
      (fun M acc => f (restrictFirst n m M) + acc) 0 =
    ((enumerateWorlds n).foldr (fun M' acc => f M' + acc) 0) * (2 ^ m : Nat) := by
  induction m with
  | zero =>
      show (enumerateWorlds (n + 0)).foldr (fun M acc => f (restrictFirst n 0 M) + acc) 0 =
           ((enumerateWorlds n).foldr (fun M' acc => f M' + acc) 0) * (2 ^ 0 : Nat)
      have h_pow : ((2 ^ 0 : Nat) : Rat) = 1 := by norm_cast
      rw [h_pow, Rat.mul_one]
      apply foldr_add_eq_of_eqOn_rat
      intro M _
      rfl
  | succ k ih =>
      show (enumerateWorlds (n + (k + 1))).foldr
              (fun M acc => f (restrictFirst n (k + 1) M) + acc) 0 =
           ((enumerateWorlds n).foldr (fun M' acc => f M' + acc) 0) * (2 ^ (k + 1) : Nat)
      simp only [enumerateWorlds]
      rw [List.foldr_flatMap]
      change List.foldr
          (fun x acc =>
            f (restrictFirst n (k + 1)
                (fun i : Fin (n + k + 1) =>
                  if h : i.val < n + k then x ⟨i.val, h⟩ else true)) +
            (f (restrictFirst n (k + 1)
                (fun i : Fin (n + k + 1) =>
                  if h : i.val < n + k then x ⟨i.val, h⟩ else false)) + acc))
          0 (enumerateWorlds (n + k)) = _
      have h_addsplit : (enumerateWorlds (n + k)).foldr
          (fun a acc =>
            f (restrictFirst n (k + 1)
                (fun i : Fin (n + k + 1) =>
                  if h : i.val < n + k then a ⟨i.val, h⟩ else true)) +
            (f (restrictFirst n (k + 1)
                (fun i : Fin (n + k + 1) =>
                  if h : i.val < n + k then a ⟨i.val, h⟩ else false)) + acc)) 0 =
          (enumerateWorlds (n + k)).foldr
            (fun M' acc => f (restrictFirst n k M') + acc) 0 +
          (enumerateWorlds (n + k)).foldr
            (fun M' acc => f (restrictFirst n k M') + acc) 0 := by
        induction enumerateWorlds (n + k) with
        | nil =>
            show (0 : Rat) = 0 + 0
            rw [Rat.add_zero]
        | cons M' rest ihL =>
            simp only [List.foldr_cons]
            rw [ihL, restrictFirst_extLast n k M' true, restrictFirst_extLast n k M' false]
            exact rat_quad_rearrange _ _
      rw [h_addsplit, ih]
      have h_pow_succ : ((2 ^ (k + 1) : Nat) : Rat) =
                        ((2 ^ k : Nat) : Rat) + ((2 ^ k : Nat) : Rat) := by
        have hnat : (2 ^ (k + 1) : Nat) = 2 ^ k + 2 ^ k := by
          rw [Nat.pow_succ]; omega
        rw [hnat]
        push_cast; rfl
      rw [h_pow_succ, Rat.mul_add]

-- ============================================================
-- Uniform weight definition and basic theorem
-- ============================================================

/-- **Generalized world-summation factorization** with arbitrary
    length `N = n + m`.  Bridges from the canonical `enumerateWorlds
    (n + m)` form (in `sum_enumerateWorlds_factor`) to any length
    propositionally equal to `n + m` (e.g., `(O₁ ++ O₂).length` via
    `List.length_append`).

    Proof: `subst` reduces the parametrised length to `n + m`; the
    `by omega` bound uses `hEq` automatically, and after substitution
    the body matches `restrictFirst` up to proof irrelevance. -/
theorem sum_enumerateWorlds_factor_general
    {N n m : Nat} (hEq : N = n + m) (f : (Fin n → Bool) → Rat) :
    (enumerateWorlds N).foldr
      (fun M acc => f (fun i : Fin n => M ⟨i.val, by omega⟩) + acc) 0 =
    ((enumerateWorlds n).foldr (fun M' acc => f M' + acc) 0) * (2 ^ m : Nat) := by
  subst hEq
  exact sum_enumerateWorlds_factor n m f

-- ============================================================
-- Uniform weight definition and basic theorem
-- ============================================================

/-- *Uniform Rat weight*: every per-axiom value is 1.  Models the
    "uniform prior" case where every axiom is equally likely. -/
def uniformRat {O : Ontology} : DispAtom O → Bool → Rat := fun _ _ => 1

/-- Under uniform weights, every world has weight 1. -/
theorem worldWeightRat_uniform (O : Ontology) (M : World O) :
    worldWeightRat O M (@uniformRat O) = 1 := by
  unfold worldWeightRat uniformRat
  induction List.finRange O.length with
  | nil => rfl
  | cons _ rest ih =>
      simp only [List.foldr_cons]
      rw [ih, Rat.one_mul]

-- ============================================================
-- WMC-level SCC factorization for uniform weights — closed form
-- ============================================================

/-- **WMC-level SCC factorization (uniform weights).**

    Under SCC conditions (disjoint signatures, consistent O₂, query
    inside O₁'s signature, both ontologies nominal-free and
    range-chain-safe), the rational DISPONTE marginal under uniform
    weights factorizes:

      `disponteWMCRat (O₁ ++ O₂) C D uniformRat = disponteWMCRat O₁ C D uniformRat · 2^|O₂|`.

    Proof: combine `per_world_sat_factor_consistent` (Sat-level
    factorization), `worldWeightRat_uniform` (uniform weight
    reduction), and `sum_enumerateWorlds_factor_general` (the
    combinatorial summation identity, length-cast version). -/
theorem disponteWMCRat_uniform_scc_factor
    {O₁ O₂ : Ontology}
    (hO₁_nf : OntologyNominalFree O₁) (hO₂_nf : OntologyNominalFree O₂)
    (hO₁_safe : RangeChainSafe O₁) (hO₂_safe : RangeChainSafe O₂)
    (hO₂_cons : ¬ Sat O₂ .top .bot)
    (hdisj : DisjointSigs O₁ O₂)
    {C D : Concept} (hC_nf : NominalFree C) (hD_nf : NominalFree D)
    (hC : ConceptInSig O₁ C) (hD : ConceptInSig O₁ D) :
    disponteWMCRat (O₁ ++ O₂) C D uniformRat =
    disponteWMCRat O₁ C D uniformRat * ((2 ^ O₂.length : Nat) : Rat) := by
  classical
  unfold disponteWMCRat
  -- Step 1: rewrite LHS summand using `worldWeightRat_uniform` + `per_world_sat_factor_consistent`.
  have h_lhs : ∀ M ∈ enumerateWorlds (O₁ ++ O₂).length,
      (if Sat (selectedAxioms (O₁ ++ O₂) M) C D
        then worldWeightRat (O₁ ++ O₂) M uniformRat else 0) =
      (if Sat (selectedAxioms O₁ (restrictWorld₁ M)) C D then 1 else 0) := by
    intro M _
    rw [worldWeightRat_uniform]
    rw [per_world_sat_factor_consistent hO₁_nf hO₂_nf hO₁_safe hO₂_safe
          hO₂_cons hdisj hC_nf hD_nf hC hD M]
    -- selectedFromO₁ O₁ O₂ M = selectedAxioms O₁ (restrictWorld₁ M) by definition.
    rfl
  rw [foldr_add_eq_of_eqOn_rat _ _ _ h_lhs]
  -- Step 2: rewrite RHS summand using `worldWeightRat_uniform`.
  have h_rhs : ∀ M' ∈ enumerateWorlds O₁.length,
      (if Sat (selectedAxioms O₁ M') C D then worldWeightRat O₁ M' uniformRat else 0) =
      (if Sat (selectedAxioms O₁ M') C D then 1 else 0) := by
    intro M' _
    rw [worldWeightRat_uniform]
  rw [foldr_add_eq_of_eqOn_rat _ _ _ h_rhs]
  -- Step 3: apply the general factor with length cast `(O₁++O₂).length = O₁.length + O₂.length`.
  -- Proof irrelevance reconciles `restrictWorld₁ M` with the abstract `fun i => M ⟨i.val, _⟩` form.
  exact sum_enumerateWorlds_factor_general
    (List.length_append : (O₁ ++ O₂).length = O₁.length + O₂.length)
    (fun M' => if Sat (selectedAxioms O₁ M') C D then 1 else 0)

-- ============================================================
-- Audit
-- ============================================================

#print axioms restrictFirst_extLast
#print axioms sum_enumerateWorlds_factor
#print axioms sum_enumerateWorlds_factor_general
#print axioms worldWeightRat_uniform
#print axioms disponteWMCRat_uniform_scc_factor

end ELpp
end ELKSDD
