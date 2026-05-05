/-
  ELKSDD/CompilationWMC.lean
  --------------------------
  *Shannon-recursive WMC + UNCONDITIONAL DISPONTE correspondence* on the
  verified tree `compileSat O C D`.

  *What this module proves.*

    * `shannonSatSum` — recursive Shannon-expansion sum mirroring
      `wmc`'s structure, specialised to the Sat-decision predicate.
    * `wmc_compileSatAux_eq` — the SDD WMC of the Shannon-expanded
      `compileSatAux O C D vs ctx` matches `shannonSatSum O C D vs
      ctx w` *exactly* (mechanical induction on `vs`).
    * `Perm_foldr_add_eq`, `Perm_foldr_add_eq_fn` — Nat-foldr-sum is
      permutation-invariant.
    * `extensionList` — explicit enumeration of the 2^|vs| extensions
      of a partial assignment along `vs`.
    * `shannonSatSum_eq_foldr_extensionList` — shannonSatSum equals a
      foldr over the extension list with weight = path-product times
      `[Sat]`-indicator.  Requires `vs.Nodup`.
    * `extensionList_finRange_perm_enumerateWorlds` — the two
      enumerations of `Fin n → Bool` are permutations of each other.
      Proof goes via mutual containment + length match + `Nodup` + a
      custom `nodup_perm_of_subset_subset` lemma (no DecidableEq).
    * **`wmc_compileSat_eq_disponteWMC`** — *the unconditional
      DISPONTE correspondence theorem* on the verified `compileSat`:
      `SDD.wmc (compileSat O C D) w = disponteWMC O C D w` for every
      weight function `w`, *with no free hypothesis*.
    * `compileSat_disponte_correspondence` — clean restatement of the
      unconditional theorem.
    * `exists_disponte_correspondence` — existence form.

  All theorems audit-clean — only Lean foundation axioms (`propext`,
  `Classical.choice`, `Quot.sound`).
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

/-- Nat-foldr-sum is permutation-invariant. -/
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
-- 3. Extension list and weightAlong
-- ============================================================

/-- *Extension list* — all 2^|vs| extensions of `ctx` by setting each
    variable in `vs` to true or false in turn.  Branches on the head:
    first emit all extensions with the head set to `true`, then all
    extensions with the head set to `false`. -/
noncomputable def extensionList {O : Ontology} :
    List (DispAtom O) → Assignment (DispAtom O) → List (Assignment (DispAtom O))
  | [], ctx => [ctx]
  | p :: rest, ctx =>
      extensionList rest (setAt ctx p true) ++
      extensionList rest (setAt ctx p false)

/-- *Path weight* — product of `w p (M p)` along `vs`. -/
noncomputable def weightAlong {O : Ontology} (vs : List (DispAtom O))
    (M : Assignment (DispAtom O)) (w : DispAtom O → Bool → Nat) : Nat :=
  vs.foldr (fun p acc => w p (M p) * acc) 1

@[simp] theorem weightAlong_nil {O : Ontology} (M : Assignment (DispAtom O))
    (w : DispAtom O → Bool → Nat) : weightAlong [] M w = 1 := rfl

theorem weightAlong_cons {O : Ontology} (p : DispAtom O) (rest : List (DispAtom O))
    (M : Assignment (DispAtom O)) (w : DispAtom O → Bool → Nat) :
    weightAlong (p :: rest) M w = w p (M p) * weightAlong rest M w := rfl

-- ============================================================
-- 4. Foldr-add helpers
-- ============================================================

theorem foldr_add_append {α : Type _} (l1 l2 : List α) (f : α → Nat) :
    (l1 ++ l2).foldr (fun a acc => f a + acc) 0 =
    l1.foldr (fun a acc => f a + acc) 0 +
    l2.foldr (fun a acc => f a + acc) 0 := by
  induction l1 with
  | nil => simp
  | cons x rest ih =>
      simp only [List.cons_append, List.foldr_cons]
      rw [ih]; omega

theorem foldr_add_const_mul {α : Type _} (l : List α) (k : Nat) (h : α → Nat) :
    l.foldr (fun a acc => k * h a + acc) 0 =
    k * l.foldr (fun a acc => h a + acc) 0 := by
  induction l with
  | nil => simp
  | cons x rest ih =>
      simp only [List.foldr_cons]
      rw [ih, Nat.mul_add]

theorem foldr_add_eq_of_eqOn {α : Type _} (l : List α) (f g : α → Nat)
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

theorem if_then_mul_zero {P : Prop} [Decidable P] (k x : Nat) :
    (if P then k * x else 0) = k * (if P then x else 0) := by
  by_cases h : P
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, Nat.mul_zero]

-- ============================================================
-- 5. setAt commutativity & extension-list value lemma
-- ============================================================

/-- `setAt` at distinct keys commutes. -/
theorem setAt_comm {α : Type _} (ctx : Assignment α) (p q : α) (hpq : p ≠ q)
    (a b : Bool) :
    setAt (setAt ctx p a) q b = setAt (setAt ctx q b) p a := by
  classical
  funext r
  unfold setAt
  by_cases h1 : r = q
  · subst h1
    have hrp : r ≠ p := fun h => hpq h.symm
    simp [hrp]
  · by_cases h2 : r = p
    · subst h2
      simp [h1]
    · simp [h1, h2]

/-- For `M ∈ extensionList rest (setAt ctx p b)` with `p ∉ rest`, we
    have `M p = b`. -/
theorem mem_extensionList_value {O : Ontology} (vs : List (DispAtom O))
    (ctx : Assignment (DispAtom O)) (p : DispAtom O) (b : Bool)
    (hp : p ∉ vs) (M : Assignment (DispAtom O))
    (hM : M ∈ extensionList vs (setAt ctx p b)) :
    M p = b := by
  classical
  induction vs generalizing ctx with
  | nil =>
      simp only [extensionList, List.mem_singleton] at hM
      subst hM
      simp [setAt]
  | cons q rest ih =>
      have hpne_q : p ≠ q := fun h => hp (h ▸ List.mem_cons_self)
      have hp_rest : p ∉ rest :=
        fun h => hp (List.mem_cons_of_mem _ h)
      simp only [extensionList, List.mem_append] at hM
      cases hM with
      | inl hT =>
          rw [setAt_comm ctx p q hpne_q b true] at hT
          exact ih (setAt ctx q true) hp_rest hT
      | inr hF =>
          rw [setAt_comm ctx p q hpne_q b false] at hF
          exact ih (setAt ctx q false) hp_rest hF

-- ============================================================
-- 6. shannonSatSum = foldr over extensionList
-- ============================================================

/-- **Key lemma**: `shannonSatSum` equals a foldr over the extension
    list, weighting each extension by its path-product times the
    `[Sat]`-indicator.  Proof by induction on `vs`.

    `vs.Nodup` is required so that the path-product is well-defined
    (no double-counted weights). -/
theorem shannonSatSum_eq_foldr_extensionList (O : Ontology) (C D : Concept)
    (vs : List (DispAtom O)) (ctx : Assignment (DispAtom O))
    (w : DispAtom O → Bool → Nat) (hNodup : vs.Nodup) :
    letI : ∀ M : Assignment (DispAtom O), Decidable (Sat (selectedAxioms O M) C D) :=
      fun _ => Classical.propDecidable _
    shannonSatSum O C D vs ctx w =
    (extensionList vs ctx).foldr
      (fun M acc =>
        (if Sat (selectedAxioms O M) C D then weightAlong vs M w else 0) + acc) 0 := by
  classical
  induction vs generalizing ctx with
  | nil =>
      simp only [shannonSatSum, extensionList, List.foldr_cons, List.foldr_nil]
      by_cases h : Sat (selectedAxioms O ctx) C D
      · rw [if_pos h, if_pos h]; simp [weightAlong]
      · rw [if_neg h, if_neg h]
  | cons p rest ih =>
      have hpNotInRest : p ∉ rest := by
        rw [List.nodup_cons] at hNodup; exact hNodup.1
      have hRestNodup : rest.Nodup := by
        rw [List.nodup_cons] at hNodup; exact hNodup.2
      simp only [shannonSatSum, extensionList]
      rw [ih (setAt ctx p true) hRestNodup, ih (setAt ctx p false) hRestNodup]
      rw [foldr_add_append]
      have key : ∀ b : Bool,
          w p b *
            (extensionList rest (setAt ctx p b)).foldr
              (fun M acc =>
                (if Sat (selectedAxioms O M) C D then weightAlong rest M w else 0) + acc) 0 =
          (extensionList rest (setAt ctx p b)).foldr
            (fun M acc =>
              (if Sat (selectedAxioms O M) C D then weightAlong (p :: rest) M w else 0) + acc) 0 := by
        intro b
        have hVal : ∀ M ∈ extensionList rest (setAt ctx p b),
            (if Sat (selectedAxioms O M) C D then weightAlong (p :: rest) M w else 0) =
            (if Sat (selectedAxioms O M) C D then w p b * weightAlong rest M w else 0) := by
          intro M hM
          have hMp : M p = b := mem_extensionList_value rest ctx p b hpNotInRest M hM
          show (if _ then weightAlong (p :: rest) M w else 0) = _
          unfold weightAlong
          simp only [List.foldr_cons]
          rw [hMp]
        rw [foldr_add_eq_of_eqOn _ _ _ hVal]
        have hFactor : ∀ M ∈ extensionList rest (setAt ctx p b),
            (if Sat (selectedAxioms O M) C D then w p b * weightAlong rest M w else 0) =
            w p b * (if Sat (selectedAxioms O M) C D then weightAlong rest M w else 0) := by
          intro M _
          exact if_then_mul_zero (w p b) (weightAlong rest M w)
        rw [foldr_add_eq_of_eqOn _ _ _ hFactor]
        rw [foldr_add_const_mul]
      rw [← key true, ← key false]

-- ============================================================
-- 7. weightAlong on finRange = worldWeight (definitional)
-- ============================================================

theorem weightAlong_finRange_eq_worldWeight (O : Ontology)
    (M : Assignment (DispAtom O)) (w : DispAtom O → Bool → Nat) :
    weightAlong (List.finRange O.length) M w = worldWeight O M w := by
  unfold weightAlong worldWeight
  rfl

-- ============================================================
-- 8. Length lemmas
-- ============================================================

theorem extensionList_length {O : Ontology} (vs : List (DispAtom O))
    (ctx : Assignment (DispAtom O)) :
    (extensionList vs ctx).length = 2 ^ vs.length := by
  classical
  induction vs generalizing ctx with
  | nil => simp [extensionList]
  | cons p rest ih =>
      simp only [extensionList, List.length_append, List.length_cons]
      rw [ih, ih, Nat.pow_succ]
      omega

theorem enumerateWorlds_length (n : Nat) :
    (enumerateWorlds n).length = 2 ^ n := by
  induction n with
  | zero => simp [enumerateWorlds]
  | succ k ih =>
      simp only [enumerateWorlds]
      rw [List.length_flatMap]
      have hSum : ∀ (l : List (Fin k → Bool)),
          (List.map (fun M : Fin k → Bool =>
              List.length [(fun i : Fin (k+1) =>
                if h : i.val < k then M ⟨i.val, h⟩ else true),
              (fun i : Fin (k+1) =>
                if h : i.val < k then M ⟨i.val, h⟩ else false)]) l).sum =
          l.length * 2 := by
        intro l
        induction l with
        | nil => simp
        | cons _ rest ihL =>
            show 2 + (List.map _ rest).sum = (rest.length + 1) * 2
            rw [ihL]; omega
      rw [hSum, ih, Nat.pow_succ]

-- ============================================================
-- 9. Membership: every M is in both lists
-- ============================================================

theorem mem_extensionList_of_agrees {O : Ontology} (vs : List (DispAtom O))
    (ctx : Assignment (DispAtom O)) (M : Assignment (DispAtom O))
    (hAgree : ∀ q, q ∉ vs → M q = ctx q) :
    M ∈ extensionList vs ctx := by
  classical
  induction vs generalizing ctx with
  | nil =>
      simp only [extensionList, List.mem_singleton]
      funext q
      exact hAgree q (List.not_mem_nil)
  | cons p rest ih =>
      simp only [extensionList, List.mem_append]
      by_cases hMp : M p = true
      · left
        apply ih (setAt ctx p true)
        intro q hq_not
        by_cases hqp : q = p
        · subst hqp; simp only [setAt, if_pos rfl]; exact hMp
        · have hq_not_cons : q ∉ p :: rest := by
            intro h
            cases List.mem_cons.mp h with
            | inl h1 => exact hqp h1
            | inr h2 => exact hq_not h2
          rw [hAgree q hq_not_cons]
          simp [setAt, hqp]
      · right
        have hMp' : M p = false := by
          cases h : M p with
          | true => exact absurd h hMp
          | false => rfl
        apply ih (setAt ctx p false)
        intro q hq_not
        by_cases hqp : q = p
        · subst hqp; simp only [setAt, if_pos rfl]; exact hMp'
        · have hq_not_cons : q ∉ p :: rest := by
            intro h
            cases List.mem_cons.mp h with
            | inl h1 => exact hqp h1
            | inr h2 => exact hq_not h2
          rw [hAgree q hq_not_cons]
          simp [setAt, hqp]

theorem mem_extensionList_finRange {O : Ontology} (M : Assignment (DispAtom O))
    (ctx : Assignment (DispAtom O)) :
    M ∈ extensionList (List.finRange O.length) ctx := by
  apply mem_extensionList_of_agrees
  intro q hq
  exact absurd (List.mem_finRange q) hq

theorem mem_enumerateWorlds (n : Nat) (M : Fin n → Bool) :
    M ∈ enumerateWorlds n := by
  induction n with
  | zero =>
      simp only [enumerateWorlds, List.mem_singleton]
      funext q
      exact q.elim0
  | succ k ih =>
      simp only [enumerateWorlds, List.mem_flatMap]
      let M' : Fin k → Bool := fun i => M ⟨i.val, by omega⟩
      refine ⟨M', ih M', ?_⟩
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
      by_cases hLast : M ⟨k, by omega⟩ = true
      · left
        funext i
        by_cases hi : i.val < k
        · simp only [hi, dif_pos]
          show M ⟨i.val, by omega⟩ = M i
          congr 1
        · have hieq : i.val = k := by have := i.isLt; omega
          have hi_eq_k : i = ⟨k, by omega⟩ := Fin.ext hieq
          rw [hi_eq_k]
          rw [dif_neg (by omega : ¬ k < k)]
          exact hLast
      · right
        have hLast' : M ⟨k, by omega⟩ = false := by
          cases h : M ⟨k, by omega⟩ with
          | true => exact absurd h hLast
          | false => rfl
        funext i
        by_cases hi : i.val < k
        · simp only [hi, dif_pos]
          show M ⟨i.val, by omega⟩ = M i
          congr 1
        · have hieq : i.val = k := by have := i.isLt; omega
          have hi_eq_k : i = ⟨k, by omega⟩ := Fin.ext hieq
          rw [hi_eq_k]
          rw [dif_neg (by omega : ¬ k < k)]
          exact hLast'

-- ============================================================
-- 10. Nodup of extensionList
-- ============================================================

theorem extensionList_Nodup {O : Ontology} (vs : List (DispAtom O))
    (ctx : Assignment (DispAtom O)) (hNodup : vs.Nodup) :
    (extensionList vs ctx).Nodup := by
  classical
  induction vs generalizing ctx with
  | nil => simp [extensionList]
  | cons p rest ih =>
      have hpNotInRest : p ∉ rest := by
        rw [List.nodup_cons] at hNodup; exact hNodup.1
      have hRestNodup : rest.Nodup := by
        rw [List.nodup_cons] at hNodup; exact hNodup.2
      simp only [extensionList]
      rw [List.nodup_append]
      refine ⟨ih (setAt ctx p true) hRestNodup,
              ih (setAt ctx p false) hRestNodup, ?_⟩
      intro M1 hM1 M2 hM2 hEq
      have h1 : M1 p = true :=
        mem_extensionList_value rest ctx p true hpNotInRest M1 hM1
      have h2 : M2 p = false :=
        mem_extensionList_value rest ctx p false hpNotInRest M2 hM2
      rw [hEq, h2] at h1
      exact (Bool.noConfusion h1)

/-- ext-style lift is injective in M for any tail bit b. -/
theorem ext_lift_inj {k : Nat} (b : Bool) (M M' : Fin k → Bool)
    (hEq : (fun i : Fin (k+1) => if h : i.val < k then M ⟨i.val, h⟩ else b) =
           (fun i : Fin (k+1) => if h : i.val < k then M' ⟨i.val, h⟩ else b)) :
    M = M' := by
  funext i
  have hVal :
      (fun j : Fin (k+1) => if h : j.val < k then M ⟨j.val, h⟩ else b) ⟨i.val, by omega⟩ =
      (fun j : Fin (k+1) => if h : j.val < k then M' ⟨j.val, h⟩ else b) ⟨i.val, by omega⟩ :=
    congrFun hEq _
  simp only [dif_pos i.isLt] at hVal
  show M i = M' i
  have h1 : M i = M ⟨i.val, i.isLt⟩ := by congr 1
  have h2 : M' i = M' ⟨i.val, i.isLt⟩ := by congr 1
  rw [h1, h2, hVal]

/-- ext T and ext F differ at position ⟨k⟩. -/
theorem ext_T_ne_ext_F {k : Nat} (M M' : Fin k → Bool) :
    (fun i : Fin (k+1) => if h : i.val < k then M ⟨i.val, h⟩ else true) ≠
    (fun i : Fin (k+1) => if h : i.val < k then M' ⟨i.val, h⟩ else false) := by
  intro hEq
  have h := congrFun hEq ⟨k, by omega⟩
  simp at h

/-- Nodup is preserved under injective map. -/
theorem nodup_map_injective {α β : Type _} (f : α → β) (hf : ∀ a b, f a = f b → a = b)
    (l : List α) (h : l.Nodup) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons x rest ih =>
      rw [List.map_cons, List.nodup_cons]
      rw [List.nodup_cons] at h
      refine ⟨?_, ih h.2⟩
      intro hMem
      rw [List.mem_map] at hMem
      obtain ⟨y, hyRest, hyEq⟩ := hMem
      have : x = y := hf _ _ hyEq.symm
      subst this
      exact h.1 hyRest

/-- finRange is Nodup. -/
theorem finRange_Nodup (n : Nat) : (List.finRange n).Nodup := by
  induction n with
  | zero => simp [List.finRange]
  | succ k ih =>
      rw [List.finRange_succ, List.nodup_cons]
      refine ⟨?_, ?_⟩
      · intro hMem
        rw [List.mem_map] at hMem
        obtain ⟨x, _, hx⟩ := hMem
        exact Fin.succ_ne_zero _ hx
      · exact nodup_map_injective Fin.succ (fun _ _ h => Fin.succ_inj.mp h)
                _ ih

-- ============================================================
-- 11. Nodup of enumerateWorlds
-- ============================================================

theorem enumerateWorlds_Nodup (n : Nat) : (enumerateWorlds n).Nodup := by
  induction n with
  | zero => simp [enumerateWorlds]
  | succ k ih =>
      simp only [enumerateWorlds]
      generalize hL : enumerateWorlds k = L at ih
      clear hL
      induction L with
      | nil => simp
      | cons M rest ihL =>
          rw [List.flatMap_cons, List.nodup_append]
          rw [List.nodup_cons] at ih
          have ihL' := ihL ih.2
          refine ⟨?_, ihL', ?_⟩
          · -- inner pair Nodup
            simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
                       List.nodup_nil, and_true, or_false, not_false_eq_true]
            exact ext_T_ne_ext_F M M
          · -- between-pair disjointness
            intro x hxAB y hyRest hxy
            simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hxAB
            rw [List.mem_flatMap] at hyRest
            obtain ⟨M', hM'Rest, hyMM'⟩ := hyRest
            simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hyMM'
            apply ih.1
            cases hxAB with
            | inl hxT =>
                cases hyMM' with
                | inl hyT =>
                    have hMM' : M = M' := ext_lift_inj true M M' (hxT.symm.trans (hxy.trans hyT))
                    rw [hMM']; exact hM'Rest
                | inr hyF =>
                    exfalso
                    exact ext_T_ne_ext_F M M' (hxT.symm.trans (hxy.trans hyF))
            | inr hxF =>
                cases hyMM' with
                | inl hyT =>
                    exfalso
                    exact ext_T_ne_ext_F M' M (hyT.symm.trans (hxy.symm.trans hxF))
                | inr hyF =>
                    have hMM' : M = M' := ext_lift_inj false M M' (hxF.symm.trans (hxy.trans hyF))
                    rw [hMM']; exact hM'Rest

-- ============================================================
-- 12. Custom Nodup-perm lemma (no DecidableEq required)
-- ============================================================

private theorem perm_cons_append_swap {α : Type _} (x : α) (pre post : List α) :
    (x :: (pre ++ post)).Perm (pre ++ x :: post) := by
  induction pre with
  | nil => exact List.Perm.refl _
  | cons y prest ihP =>
      have h1 : (x :: ((y :: prest) ++ post)).Perm (y :: x :: (prest ++ post)) := by
        show (x :: y :: (prest ++ post)).Perm (y :: x :: (prest ++ post))
        exact List.Perm.swap _ _ _
      have h2 : (y :: x :: (prest ++ post)).Perm (y :: (prest ++ x :: post)) :=
        List.Perm.cons y ihP
      exact h1.trans h2

/-- Two `Nodup` lists with same length and mutual containment are
    permutations.  Proved by induction on the first list, splitting
    the second at the membership-witness position. -/
private theorem nodup_perm_of_subset_subset {α : Type _}
    (l₁ l₂ : List α) (hN1 : l₁.Nodup) (hN2 : l₂.Nodup)
    (hLen : l₁.length = l₂.length)
    (hSub : ∀ x ∈ l₁, x ∈ l₂) :
    l₁.Perm l₂ := by
  classical
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ with
      | nil => exact List.Perm.nil
      | cons _ _ => simp at hLen
  | cons x rest ih =>
      have hx2 : x ∈ l₂ := hSub x List.mem_cons_self
      obtain ⟨pre, post, hSplit⟩ := List.append_of_mem hx2
      subst hSplit
      have hN_post : (pre ++ post).Nodup := by
        rw [List.nodup_append]
        rw [List.nodup_append, List.nodup_cons] at hN2
        refine ⟨hN2.1, hN2.2.1.2, ?_⟩
        intro a ha b hb hab
        exact hN2.2.2 a ha b (List.mem_cons_of_mem _ hb) hab
      have hRestSub : ∀ y ∈ rest, y ∈ pre ++ post := by
        intro y hy
        have hy2 : y ∈ pre ++ x :: post := hSub y (List.mem_cons_of_mem _ hy)
        rw [List.mem_append, List.mem_cons] at hy2
        rcases hy2 with hP | hX | hPost
        · exact List.mem_append.mpr (Or.inl hP)
        · exfalso
          rw [List.nodup_cons] at hN1
          exact hN1.1 (hX ▸ hy)
        · exact List.mem_append.mpr (Or.inr hPost)
      have hLen' : rest.length = (pre ++ post).length := by
        have : (x :: rest).length = (pre ++ x :: post).length := hLen
        simp only [List.length_cons, List.length_append] at this ⊢
        omega
      have hRestNodup : rest.Nodup := by
        rw [List.nodup_cons] at hN1; exact hN1.2
      have hPermRest : rest.Perm (pre ++ post) :=
        ih (pre ++ post) hRestNodup hN_post hLen' hRestSub
      have step1 : (x :: rest).Perm (x :: (pre ++ post)) := List.Perm.cons x hPermRest
      exact step1.trans (perm_cons_append_swap x pre post)

-- ============================================================
-- 13. THE BRIDGE: extensionList ~ enumerateWorlds (Perm)
-- ============================================================

/-- **THE BRIDGE LEMMA.**  `extensionList (finRange O.length) ctx` and
    `enumerateWorlds O.length` are permutations of each other.  Proved
    by mutual containment + length match + Nodup. -/
theorem extensionList_finRange_perm_enumerateWorlds {O : Ontology}
    (ctx : Assignment (DispAtom O)) :
    (extensionList (List.finRange O.length) ctx).Perm
    (enumerateWorlds O.length) := by
  apply nodup_perm_of_subset_subset
  · exact extensionList_Nodup (List.finRange O.length) ctx (finRange_Nodup _)
  · exact enumerateWorlds_Nodup O.length
  · rw [extensionList_length, enumerateWorlds_length, List.length_finRange]
  · intro M _
    exact mem_enumerateWorlds O.length M

-- ============================================================
-- 14. UNCONDITIONAL DISPONTE CORRESPONDENCE
-- ============================================================

/-- **The unconditional DISPONTE correspondence theorem.**  The WMC of
    the verified compiled SDD `compileSat O C D` equals the DISPONTE
    distribution-semantics probability `disponteWMC O C D w` for every
    weight function `w`.  *No free hypothesis* — all premises (incl.
    the SDD wmc-sum-form identity and the SDDEncodesQuery condition)
    are discharged. -/
theorem wmc_compileSat_eq_disponteWMC (O : Ontology) (C D : Concept)
    (w : DispAtom O → Bool → Nat) :
    SDD.wmc (compileSat O C D) w = disponteWMC O C D w := by
  classical
  -- Step 1: WMC = shannonSatSum on finRange (proved above).
  rw [wmc_compileSat_eq_shannonSatSum]
  -- Step 2: shannonSatSum on Nodup finRange = foldr over extensionList.
  rw [shannonSatSum_eq_foldr_extensionList O C D
        (List.finRange O.length) (fun _ => false) w (finRange_Nodup _)]
  -- Step 3: weightAlong (finRange) M = worldWeight O M (definitional).
  have hSummand :
      ∀ M ∈ extensionList (List.finRange O.length) (fun _ => false : Assignment (DispAtom O)),
        (if Sat (selectedAxioms O M) C D then weightAlong (List.finRange O.length) M w else 0) =
        (if Sat (selectedAxioms O M) C D then worldWeight O M w else 0) := by
    intro M _
    rw [weightAlong_finRange_eq_worldWeight]
  rw [foldr_add_eq_of_eqOn _ _ _ hSummand]
  -- Step 4: Apply Perm to bridge extensionList ~ enumerateWorlds.
  have hPerm := extensionList_finRange_perm_enumerateWorlds (O := O) (fun _ => false)
  rw [Perm_foldr_add_eq_fn _ _ _ hPerm]
  -- Step 5: This matches disponteWMC's definition.
  rfl

/-- **Unconditional DISPONTE correspondence — clean restatement.**  For
    every ontology `O`, query `(C, D)`, and weight function `w`, the
    WMC of the compiled SDD equals the DISPONTE probability. -/
theorem compileSat_disponte_correspondence (O : Ontology) (C D : Concept) :
    ∀ w : DispAtom O → Bool → Nat,
      SDD.wmc (compileSat O C D) w = disponteWMC O C D w :=
  fun w => wmc_compileSat_eq_disponteWMC O C D w

/-- **Existence form.**  There exists a verified SDD tree such that:
    (a) it correctly encodes the Sat-query, and (b) its WMC equals the
    DISPONTE probability for every weight function. -/
theorem exists_disponte_correspondence (O : Ontology) (C D : Concept) :
    ∃ tree : Tree (DispAtom O),
      SDDEncodesQuery O C D tree ∧
      ∀ w : DispAtom O → Bool → Nat, SDD.wmc tree w = disponteWMC O C D w :=
  ⟨compileSat O C D,
   compileSat_correct O C D,
   compileSat_disponte_correspondence O C D⟩

-- ============================================================
-- 15. Audit
-- ============================================================

#print axioms wmc_compileSatAux_eq
#print axioms wmc_compileSat_eq_shannonSatSum
#print axioms Perm_foldr_add_eq
#print axioms Perm_foldr_add_eq_fn
#print axioms shannonSatSum_eq_foldr_extensionList
#print axioms weightAlong_finRange_eq_worldWeight
#print axioms extensionList_length
#print axioms enumerateWorlds_length
#print axioms mem_extensionList_finRange
#print axioms mem_enumerateWorlds
#print axioms extensionList_Nodup
#print axioms enumerateWorlds_Nodup
#print axioms extensionList_finRange_perm_enumerateWorlds
#print axioms wmc_compileSat_eq_disponteWMC
#print axioms compileSat_disponte_correspondence
#print axioms exists_disponte_correspondence

end ELpp
end ELKSDD
