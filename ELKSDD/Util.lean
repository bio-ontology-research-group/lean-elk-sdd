/-
  ELKSDD/Util.lean
  ----------------
  Reusable utility lemmas:

  * `length_flatMap_map_const`     — length of `l.flatMap (fun a =>
                                     l'.map (f a))` is `l.length *
                                     l'.length`.
  * `length_flatMap_const_length`  — length of `l.flatMap f` when
                                     every inner list has the same
                                     length k.
  * `triangle`                     — triangular number recursion.
  * `triangle_double_eq`           — `2 · triangle K = K · (K - 1)`.
  * `triangle_eq`                  — `triangle K = K · (K - 1) / 2`.

  No imports beyond Lean 4 core. No Mathlib.
-/

namespace ELKSDD
namespace Util

-- ============================================================
-- 1. List length lemmas for nested flatMap/map patterns
-- ============================================================

/-- Length of `l.flatMap (fun a => l'.map (f a))` is
    `l.length * l'.length`. Useful for bounding the size of
    Cartesian-product enumerations. -/
theorem length_flatMap_map_const {α β γ : Type _}
    (l : List α) (l' : List β) (f : α → β → γ) :
    (l.flatMap (fun a => l'.map (f a))).length = l.length * l'.length := by
  induction l with
  | nil => simp [List.flatMap]
  | cons a t ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map, ih,
                 List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- Length of `l.flatMap f` when every inner list has the same
    length `k`. -/
theorem length_flatMap_const_length {α β : Type _}
    (l : List α) (f : α → List β) (k : Nat)
    (hk : ∀ a ∈ l, (f a).length = k) :
    (l.flatMap f).length = l.length * k := by
  induction l with
  | nil => simp [List.flatMap]
  | cons a t ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [hk a List.mem_cons_self,
          ih (fun b hb => hk b (List.mem_cons_of_mem a hb))]
      simp only [Nat.add_mul, Nat.one_mul]
      omega

-- ============================================================
-- 2. Triangular numbers
-- ============================================================

/-- Triangular number `0 + 1 + ... + (n - 1)`. -/
def triangle : Nat → Nat
  | 0 => 0
  | n + 1 => n + triangle n

/-- `2 · triangle K = K · (K - 1)`. Provable by induction on K
    without going through Nat division. -/
theorem triangle_double_eq (K : Nat) :
    2 * triangle K = K * (K - 1) := by
  induction K with
  | zero => rfl
  | succ n ih =>
      simp only [triangle, Nat.mul_add]
      rw [ih, Nat.add_sub_cancel]
      cases n with
      | zero => rfl
      | succ m =>
          simp only [Nat.succ_sub_one, Nat.add_mul, Nat.mul_add,
                     Nat.one_mul, Nat.mul_one]
          omega

/-- `triangle K = K · (K - 1) / 2`. Follows from `triangle_double_eq`
    by canceling the factor of 2. -/
theorem triangle_eq (K : Nat) : triangle K = K * (K - 1) / 2 := by
  have h := triangle_double_eq K
  have h2 : 2 * triangle K / 2 = triangle K :=
    Nat.mul_div_cancel_left _ (by decide : (0 : Nat) < 2)
  rw [h] at h2
  exact h2.symm

end Util
end ELKSDD
