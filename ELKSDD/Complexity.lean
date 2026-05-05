/-
  ELKSDD/Complexity.lean
  ----------------------
  Complexity bounds for the ELK→SDD pipeline.

  *What this module proves.*

    * **SDD size bound** (`compile_size_bound`).  The Shannon-expansion
      compile produces a tree of size strictly less than
      `2^(|vars(Γ)|+1)` — the worst-case complete-binary-tree node
      count.  Combined with `wmc_linear` (already proved in
      `ELKSDD.SDD`), this gives:

        `wmc_compile_time_bound`:
          computing WMC over `compile Γ` is in time `2^(|vars(Γ)|+1)`.

      The bound is *tight* in the worst case (SAT instances).  For
      *specific* clause-set structures (e.g., the Clark completion of
      ELK rules over a stratified signature) tighter polynomial bounds
      are folklore in the SDD literature; those are not formalised
      here.

  *What this module does NOT prove.*

    * A polynomial closure-size bound on the *new* `Sat` (the inductive
      `Prop` from `ELKSDD.ELpp`, which extends standard ELK with
      nominals, HasKey, range, reflexive, Self, plus the `nom_symm`
      and `hasKey_apply` rules from `ELKSDD.Merging`).

      The polynomial bound `(|sub(O)|+2)² + |sub(O)|²·|R| + |sub(O)|`
      is proved as `elk_closure_size_bound` in the *older* library at
      `proofs/lean/Moose/Prior.lean`, on a *different* formalisation
      of `Sat` as an explicit `List SatAtom` (rather than an inductive
      `Prop`).  Carrying that bound to the new inductive `Sat` requires
      either:
        (a) a forward simulation new-Sat → old-Sat (each new
            derivation maps to an old one, so the new closure ⊆ old
            enumeration);
        (b) re-proving the bound directly via a fresh enumeration
            list and length computation.

      Both paths are mechanical but substantial; the present module
      flags the bound as a documented gap rather than introducing a
      `sorry`.

  *Cross-library reference.*

    * `Moose.Prior.elk_closure_size_bound`:
        `(Sat O).length ≤ (numSubexprs O + 2)^2 + numSubexprs O^2 *
                          numRoles O + numSubexprs O`.

  Working over `Nat`; no Mathlib dependency.
-/

import ELKSDD.SDD
import ELKSDD.ELpp

namespace ELKSDD
namespace SDD

universe u

-- ============================================================
-- 1. SDD size bound — Shannon-expansion compile is < 2^(n+1)
-- ============================================================

/-- The Shannon-expansion compile under any context produces a tree
    of size strictly less than `2^(|vs|+1)`, the node count of a
    complete binary tree of depth `|vs|`.  Proof: induction on the
    variable list. -/
theorem compileWithCtx_size_bound {α : Type u}
    (vs : List α) (ctx : Assignment α) (Γ : List (Clause α)) :
    size (compileWithCtx vs ctx Γ) < 2 ^ (vs.length + 1) := by
  classical
  induction vs generalizing ctx with
  | nil =>
      -- compileWithCtx [] ctx Γ = leaf b for some b; size = 1 < 2 = 2^1.
      show size (compileWithCtx [] ctx Γ) < 2 ^ (0 + 1)
      unfold compileWithCtx
      by_cases h : satisfiesAll ctx Γ
      · simp only [h, if_true]; show 1 < 2; omega
      · simp only [h, if_false]; show 1 < 2; omega
  | cons p rest ih =>
      -- compileWithCtx (p :: rest) ctx Γ
      --   = .branch p (compileWithCtx rest (setAt ctx p true) Γ)
      --              (compileWithCtx rest (setAt ctx p false) Γ).
      -- size = 1 + size hi + size lo.
      -- IH: each subtree's size < 2^(|rest|+1).
      show size (compileWithCtx (p :: rest) ctx Γ) < 2 ^ (rest.length + 1 + 1)
      unfold compileWithCtx size
      have h_hi := ih (setAt ctx p true)
      have h_lo := ih (setAt ctx p false)
      -- Abstract `2^(rest.length+1)` to a variable `k` so omega can
      -- reason linearly.  `generalize ... at *` substitutes in
      -- hypotheses too, so h_hi and h_lo become `... < k`.
      generalize hk : 2 ^ (rest.length + 1) = k at h_hi h_lo
      -- Goal: 1 + s_hi + s_lo < 2^(rest.length+1+1).
      -- Recompute the goal-side bound: 2^(rest.length+1+1) = 2 * k.
      have h2 : 2 ^ (rest.length + 1 + 1) = 2 * k := by
        rw [Nat.pow_succ, hk, Nat.mul_comm]
      rw [h2]
      omega

/-- **SDD size bound**.  `compile Γ` produces a tree of size strictly
    less than `2^(|vars(Γ)|+1)` — the worst-case complete-binary-tree
    bound. -/
theorem compile_size_bound {α : Type u} (Γ : List (Clause α)) :
    size (compile Γ) < 2 ^ ((varsOfClauses Γ).length + 1) := by
  unfold compile
  exact compileWithCtx_size_bound _ _ _

/-- **WMC time complexity**.  Combining `compile_size_bound` with
    `wmc_linear`, computing WMC over `compile Γ` is in time at most
    `2^(|vars|+1)`.  This is *not* polynomial in `|Γ|` in general
    (Shannon expansion is exponential in the variable count); the
    SDD literature provides tighter bounds for specific clause-set
    structure (decomposability, smoothness, vtree shape). -/
theorem wmc_compile_time_bound {α : Type u} (Γ : List (Clause α)) :
    wmcCost (compile Γ) < 2 ^ ((varsOfClauses Γ).length + 1) := by
  rw [wmcCost_eq_size]
  exact compile_size_bound Γ

-- ============================================================
-- 2. Audit
-- ============================================================

#print axioms compile_size_bound
#print axioms wmc_compile_time_bound

end SDD
end ELKSDD
