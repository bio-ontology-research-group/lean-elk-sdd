/-
  ELKSDD/ModularBEARSMultilinear.lean
  -----------------------------------
  Formalises the multilinearity equivalence at the heart of
  module-level BEARS (the proposition labelled
  "Modular BEARS multilinearity" in the paper).

  Abstract setup.
    * `B` is a finite atom set (the global boundary).
    * For each of `K` modules and each of `M` ensemble heads we
      have a *boundary marginal tensor* `T m k : (B → Bool) → ℝ`.
      Per the paper, this is the per-module WMC at a boundary
      assignment, computed under head `k`'s atom probabilities.
    * `w a v` is the per-boundary-atom weight at value
      `v ∈ Bool` (typically `(1 - p, p)`, ensemble-independent).
    * The contraction is
          contract T = ∑_{x : B → Bool}
                         (∏_m T m x) * ∏_a w a (x a)
      for a fixed assignment of tensors `T : Fin K → (B → Bool) → ℝ`.

  Theorem `modular_bears_multilinear`:

      contract (fun m => fun x => (1/M) * ∑_k T m k x)
        =
      (1/M^K) * ∑_{j : Fin K → Fin M} contract (fun m => T m (j m))

  This is the modular-BEARS forward pass on the LHS and the full
  `M^K` deep-ensemble joint on the RHS. The proof is
  multilinearity of `contract` in each module's tensor, realised
  via `Finset.prod_sum` (product of sums = sum of products) and
  algebraic manipulation.

  Axiom-clean — depends only on the standard Lean foundation
  axioms (`propext`, `Classical.choice`, `Quot.sound`). Audited
  at the bottom of this file.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ELKSDD
namespace ModularBEARS

universe u

/-- A boundary tensor over a finite atom set `B`: a real-valued
function on the `2^|B|`-element cube of Boolean assignments. -/
abbrev BoundaryTensor (B : Type u) [Fintype B] : Type u := (B → Bool) → ℝ

variable {K M : ℕ} {B : Type u} [Fintype B] [DecidableEq B]

/-- Contraction of `K` per-module boundary tensors, with a
per-boundary-atom weight `w`. All modules share the same boundary
`B`; a module that doesn't touch some atom `a ∈ B` simply has a
tensor constant in `a`. This WLOG reformulation keeps the proof
clean and is equivalent to the restriction-based version in the
paper. -/
def contract
    (T : Fin K → BoundaryTensor B)
    (w : B → Bool → ℝ) : ℝ :=
  ∑ x : B → Bool,
    (∏ m : Fin K, T m x) * ∏ a : B, w a (x a)

/-- **The modular-BEARS multilinearity equivalence.**

Averaging the `M` per-module ensemble tensors then contracting
equals averaging the `M^K` per-head deep-ensemble contractions.

Symbolically:
    contract (fun m => fun x => (1/M) * ∑_k T m k x) w
    = (1/M^K) * ∑_j contract (fun m => T m (j m)) w
-/
theorem modular_bears_multilinear
    (T : Fin K → Fin M → BoundaryTensor B)
    (w : B → Bool → ℝ) :
    contract (fun m => fun x => (1 / (M : ℝ)) * ∑ k : Fin M, T m k x) w
    = (1 / ((M : ℝ) ^ K)) *
      ∑ (j : Fin K → Fin M),
        contract (fun m => T m (j m)) w := by
  classical
  -- Unfold contract on both sides.
  unfold contract
  -- Step 1: re-shape the RHS. Push the leading 1/M^K all the way
  -- in (past both sums), then swap the outer ∑_j with the inner
  -- ∑_x, so the RHS becomes ∑_x (∑_j ...).
  rw [show
        ((1 / ((M : ℝ) ^ K)) *
          ∑ (j : Fin K → Fin M),
            ∑ x, (∏ m : Fin K, T m (j m) x) * ∏ a : B, w a (x a))
        = ∑ x,
            ∑ (j : Fin K → Fin M),
              (1 / ((M : ℝ) ^ K)) *
                ((∏ m : Fin K, T m (j m) x) * ∏ a : B, w a (x a))
        from by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]]
  -- Step 2. Both sides are now ∑_x (stuff). Match per-x summands.
  apply Finset.sum_congr rfl
  intro x _
  -- Step 3. The LHS at this `x` is
  --   (∏_m ((1/M) * ∑_k T m k x)) * (∏_a w a (x a)).
  -- Factor (1/M)^K out of the per-module product, rewrite as 1/M^K.
  rw [show
        (∏ m : Fin K, (1 / (M : ℝ)) * ∑ k : Fin M, T m k x)
        = (1 / ((M : ℝ) ^ K)) * ∏ m, ∑ k : Fin M, T m k x
        from by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
              Fintype.card_fin, div_pow, one_pow]]
  -- Step 4. The headline identity: ∏_m (∑_k f m k) = ∑_j ∏_m f m (j m).
  rw [Finset.prod_univ_sum]
  -- Step 5. Distribute the 1/M^K over the resulting ∑_j on the LHS,
  -- and pull the boundary-weight product inside the sum, then match
  -- per-summand by `ring`.
  rw [Finset.mul_sum, Finset.sum_mul]
  -- Normalise the LHS Pi-Finset to Finset.univ to match the RHS sum.
  simp only [Fintype.piFinset_univ]
  apply Finset.sum_congr rfl
  intro j _
  ring

-- Audit: the multilinearity theorem depends only on the standard
-- Lean foundation axioms (`propext`, `Classical.choice`,
-- `Quot.sound`). Reported on every build.
#print axioms modular_bears_multilinear

end ModularBEARS
end ELKSDD
