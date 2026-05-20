/-
  ELKSDD/SROIQCompilationWMC.lean
  --------------------------------
  *Shannon-recursive WMC + DISPONTE-style correspondence* for the
  SROIQ consequence-based saturation predicate `SROIQ.SatC R O C D`.

  Background.  `moose.sroiq.cb_saturation` saturates an SROIQ
  ontology (TBox `O : ALCHOQ.Ontology`, RBox `R : SROIQ.RBox`) into
  a set of consequences whose Boolean closure is compiled to an SDD
  by the Python pipeline.  This module mirrors the EL++ WMC
  correspondence in `ELKSDD/CompilationWMC.lean` for the SROIQ
  predicate, parametric in the RBox.

  *What this module proves.*

    * `compileSatC O R C D` — a verified Shannon tree branching on
      every TBox axiom-inclusion variable, with `SROIQ.SatC R
      (selectedAxiomsS O M) C D` decided classically at the leaf.
    * `compileSatC_correct` — the tree satisfies `SDDEncodesSatCQuery`:
      `model (compileSatC O R C D) M ↔ SatC R (selectedAxiomsS O M) C D`
      for every world `M`.
    * `disponteWMCSatC O R C D w` — the DISPONTE-style sum:
      `Σ_M (if SatC R (selectedAxiomsS O M) C D then worldWeightS O M w else 0)`.
    * **`wmc_compileSatC_eq_disponteWMCSatC`** — the unconditional
      correspondence: for every weight function `w`,
      `SDD.wmc (compileSatC O R C D) w = disponteWMCSatC O R C D w`.

  Proof mirrors `ELKSDD/CompilationWMC.lean` structurally: WMC
  matches a Shannon recursion (induction on the variable list),
  the Shannon recursion matches a foldr over an extension list,
  the extension list is a permutation of the canonical enumeration
  of worlds, and the foldr identity is the DISPONTE definition.

  Foundation-only axiom budget: no `axiom`, no `sorry`; every
  theorem closes under `[propext, Classical.choice, Quot.sound]`.

  *What this is NOT.*  This module does not establish completeness
  of SROIQ saturation — it establishes that *whatever* SROIQ.SatC
  decides at the leaf, the SDD WMC matches the world-summed
  DISPONTE distribution.  Completeness for the full SROIQ surface
  is handled separately via the Tena-Cucala bridge in
  `SROIQCompletenessSkeleton.lean` / `SROIQContextBridge.lean`.
-/

import ELKSDD.SDD
import ELKSDD.ALCHOQ
import ELKSDD.SROIQ
import ELKSDD.SROIQCompleteness

namespace ELKSDD
namespace SROIQ
namespace WMC

open SDD
open ALCHOQ (Concept)

/-- A SROIQ DISPONTE atom — an index into the TBox axiom list. -/
abbrev DispAtomS (O : ALCHOQ.Ontology) : Type := Fin O.length

/-- A SROIQ world: a propositional assignment over TBox axiom indices. -/
abbrev WorldS (O : ALCHOQ.Ontology) : Type := DispAtomS O → Bool

/-- Selected TBox under a world: keep axiom `i` iff `M i = true`. -/
def selectedAxiomsS (O : ALCHOQ.Ontology) (M : WorldS O) : ALCHOQ.Ontology :=
  (List.finRange O.length).filterMap
    (fun i => if M i then some (O.get i) else none)

/-- World weight: product of per-axiom weight along all TBox indices. -/
def worldWeightS (O : ALCHOQ.Ontology) (M : WorldS O)
    (w : DispAtomS O → Bool → Nat) : Nat :=
  (List.finRange O.length).foldr (fun i acc => w i (M i) * acc) 1

/-- Path weight along an explicit variable list. -/
def weightAlongS {O : ALCHOQ.Ontology} (vs : List (DispAtomS O))
    (M : Assignment (DispAtomS O)) (w : DispAtomS O → Bool → Nat) : Nat :=
  vs.foldr (fun p acc => w p (M p) * acc) 1

@[simp] theorem weightAlongS_nil {O : ALCHOQ.Ontology}
    (M : Assignment (DispAtomS O)) (w : DispAtomS O → Bool → Nat) :
    weightAlongS [] M w = 1 := rfl

theorem weightAlongS_cons {O : ALCHOQ.Ontology} (p : DispAtomS O)
    (rest : List (DispAtomS O)) (M : Assignment (DispAtomS O))
    (w : DispAtomS O → Bool → Nat) :
    weightAlongS (p :: rest) M w =
    w p (M p) * weightAlongS rest M w := rfl

theorem weightAlongS_finRange_eq_worldWeightS (O : ALCHOQ.Ontology)
    (M : Assignment (DispAtomS O)) (w : DispAtomS O → Bool → Nat) :
    weightAlongS (List.finRange O.length) M w = worldWeightS O M w := rfl

-- ============================================================
-- 1. Enumerate worlds (atom-generic, mirrors ELpp.enumerateWorlds)
-- ============================================================

/-- All `2^n` Boolean functions on `Fin n`. -/
def enumerateWorldsS : (n : Nat) → List (Fin n → Bool)
  | 0     => [Fin.elim0]
  | n + 1 =>
      let prev := enumerateWorldsS n
      prev.flatMap (fun M =>
        [fun i : Fin (n + 1) =>
            if h : i.val < n then M ⟨i.val, h⟩ else true,
         fun i : Fin (n + 1) =>
            if h : i.val < n then M ⟨i.val, h⟩ else false])

-- ============================================================
-- 2. Shannon compile for SatC
-- ============================================================

/-- Shannon expansion compiling the SROIQ saturation query.  At
    each step we branch on whether the next TBox axiom is in the
    selected world; at the leaf we classically decide `SatC`. -/
noncomputable def compileSatCAux (O : ALCHOQ.Ontology) (R : SROIQ.RBox)
    (C D : Concept) :
    List (DispAtomS O) → Assignment (DispAtomS O) → Tree (DispAtomS O)
  | [], ctx =>
      have : Decidable (SROIQ.SatC R (selectedAxiomsS O ctx) C D) :=
        Classical.propDecidable _
      if SROIQ.SatC R (selectedAxiomsS O ctx) C D then .leaf true else .leaf false
  | p :: rest, ctx =>
      .branch p
        (compileSatCAux O R C D rest (setAt ctx p true))
        (compileSatCAux O R C D rest (setAt ctx p false))

/-- Verified compiled SDD tree for the SROIQ saturation query. -/
noncomputable def compileSatC (O : ALCHOQ.Ontology) (R : SROIQ.RBox)
    (C D : Concept) : Tree (DispAtomS O) :=
  compileSatCAux O R C D (List.finRange O.length) (fun _ => false)

/-- Shannon-recursive sum mirroring `wmc`. -/
noncomputable def shannonSatCSum (O : ALCHOQ.Ontology) (R : SROIQ.RBox)
    (C D : Concept) :
    List (DispAtomS O) → Assignment (DispAtomS O) →
    (DispAtomS O → Bool → Nat) → Nat
  | [], ctx, _ =>
      have : Decidable (SROIQ.SatC R (selectedAxiomsS O ctx) C D) :=
        Classical.propDecidable _
      if SROIQ.SatC R (selectedAxiomsS O ctx) C D then 1 else 0
  | p :: rest, ctx, w =>
      w p true * shannonSatCSum O R C D rest (setAt ctx p true) w +
      w p false * shannonSatCSum O R C D rest (setAt ctx p false) w

theorem wmc_compileSatCAux_eq (O : ALCHOQ.Ontology) (R : SROIQ.RBox)
    (C D : Concept) (vs : List (DispAtomS O))
    (ctx : Assignment (DispAtomS O))
    (w : DispAtomS O → Bool → Nat) :
    SDD.wmc (compileSatCAux O R C D vs ctx) w =
    shannonSatCSum O R C D vs ctx w := by
  classical
  induction vs generalizing ctx with
  | nil =>
      unfold compileSatCAux shannonSatCSum
      by_cases h : SROIQ.SatC R (selectedAxiomsS O ctx) C D
      · rw [if_pos h, if_pos h]; rfl
      · rw [if_neg h, if_neg h]; rfl
  | cons p rest ih =>
      unfold compileSatCAux shannonSatCSum
      rw [SDD.wmc, ih, ih]

theorem wmc_compileSatC_eq_shannonSatCSum (O : ALCHOQ.Ontology)
    (R : SROIQ.RBox) (C D : Concept) (w : DispAtomS O → Bool → Nat) :
    SDD.wmc (compileSatC O R C D) w =
    shannonSatCSum O R C D (List.finRange O.length) (fun _ => false) w := by
  unfold compileSatC
  exact wmc_compileSatCAux_eq O R C D _ _ w

-- ============================================================
-- 3. Foldr-add helpers (α-generic; could in principle reuse from
-- ELpp but we duplicate for namespace isolation and clarity).
-- ============================================================

theorem foldr_add_append {α : Type _} (l1 l2 : List α) (f : α → Nat) :
    (l1 ++ l2).foldr (fun a acc => f a + acc) 0 =
    l1.foldr (fun a acc => f a + acc) 0 +
    l2.foldr (fun a acc => f a + acc) 0 := by
  induction l1 with
  | nil => simp
  | cons _ rest ih =>
      simp only [List.cons_append, List.foldr_cons]
      rw [ih]; omega

theorem foldr_add_const_mul {α : Type _} (l : List α) (k : Nat) (h : α → Nat) :
    l.foldr (fun a acc => k * h a + acc) 0 =
    k * l.foldr (fun a acc => h a + acc) 0 := by
  induction l with
  | nil => simp
  | cons _ rest ih =>
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
-- 4. Extension list (mirror of EL++)
-- ============================================================

noncomputable def extensionListS {O : ALCHOQ.Ontology} :
    List (DispAtomS O) → Assignment (DispAtomS O) → List (Assignment (DispAtomS O))
  | [], ctx => [ctx]
  | p :: rest, ctx =>
      extensionListS rest (setAt ctx p true) ++
      extensionListS rest (setAt ctx p false)

theorem setAt_comm_S {α : Type _} (ctx : Assignment α) (p q : α)
    (hpq : p ≠ q) (a b : Bool) :
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

theorem mem_extensionListS_value {O : ALCHOQ.Ontology} (vs : List (DispAtomS O))
    (ctx : Assignment (DispAtomS O)) (p : DispAtomS O) (b : Bool)
    (hp : p ∉ vs) (M : Assignment (DispAtomS O))
    (hM : M ∈ extensionListS vs (setAt ctx p b)) :
    M p = b := by
  classical
  induction vs generalizing ctx with
  | nil =>
      simp only [extensionListS, List.mem_singleton] at hM
      subst hM
      simp [setAt]
  | cons q rest ih =>
      have hpne_q : p ≠ q := fun h => hp (h ▸ List.mem_cons_self)
      have hp_rest : p ∉ rest := fun h => hp (List.mem_cons_of_mem _ h)
      simp only [extensionListS, List.mem_append] at hM
      cases hM with
      | inl hT =>
          rw [setAt_comm_S ctx p q hpne_q b true] at hT
          exact ih (setAt ctx q true) hp_rest hT
      | inr hF =>
          rw [setAt_comm_S ctx p q hpne_q b false] at hF
          exact ih (setAt ctx q false) hp_rest hF

theorem shannonSatCSum_eq_foldr_extensionListS
    (O : ALCHOQ.Ontology) (R : SROIQ.RBox) (C D : Concept)
    (vs : List (DispAtomS O)) (ctx : Assignment (DispAtomS O))
    (w : DispAtomS O → Bool → Nat) (hNodup : vs.Nodup) :
    letI : ∀ M : Assignment (DispAtomS O),
        Decidable (SROIQ.SatC R (selectedAxiomsS O M) C D) :=
      fun _ => Classical.propDecidable _
    shannonSatCSum O R C D vs ctx w =
    (extensionListS vs ctx).foldr
      (fun M acc =>
        (if SROIQ.SatC R (selectedAxiomsS O M) C D then weightAlongS vs M w else 0) + acc) 0 := by
  classical
  induction vs generalizing ctx with
  | nil =>
      simp only [shannonSatCSum, extensionListS, List.foldr_cons, List.foldr_nil]
      by_cases h : SROIQ.SatC R (selectedAxiomsS O ctx) C D
      · rw [if_pos h, if_pos h]; simp [weightAlongS]
      · rw [if_neg h, if_neg h]
  | cons p rest ih =>
      have hpNotInRest : p ∉ rest := by
        rw [List.nodup_cons] at hNodup; exact hNodup.1
      have hRestNodup : rest.Nodup := by
        rw [List.nodup_cons] at hNodup; exact hNodup.2
      simp only [shannonSatCSum, extensionListS]
      rw [ih (setAt ctx p true) hRestNodup, ih (setAt ctx p false) hRestNodup]
      rw [foldr_add_append]
      have key : ∀ b : Bool,
          w p b *
            (extensionListS rest (setAt ctx p b)).foldr
              (fun M acc =>
                (if SROIQ.SatC R (selectedAxiomsS O M) C D then weightAlongS rest M w else 0) + acc) 0 =
          (extensionListS rest (setAt ctx p b)).foldr
            (fun M acc =>
              (if SROIQ.SatC R (selectedAxiomsS O M) C D then weightAlongS (p :: rest) M w else 0) + acc) 0 := by
        intro b
        have hVal : ∀ M ∈ extensionListS rest (setAt ctx p b),
            (if SROIQ.SatC R (selectedAxiomsS O M) C D then weightAlongS (p :: rest) M w else 0) =
            (if SROIQ.SatC R (selectedAxiomsS O M) C D then w p b * weightAlongS rest M w else 0) := by
          intro M hM
          have hMp : M p = b :=
            mem_extensionListS_value rest ctx p b hpNotInRest M hM
          show (if _ then weightAlongS (p :: rest) M w else 0) = _
          unfold weightAlongS
          simp only [List.foldr_cons]
          rw [hMp]
        rw [foldr_add_eq_of_eqOn _ _ _ hVal]
        have hFactor : ∀ M ∈ extensionListS rest (setAt ctx p b),
            (if SROIQ.SatC R (selectedAxiomsS O M) C D then w p b * weightAlongS rest M w else 0) =
            w p b * (if SROIQ.SatC R (selectedAxiomsS O M) C D then weightAlongS rest M w else 0) := by
          intro M _
          exact if_then_mul_zero (w p b) (weightAlongS rest M w)
        rw [foldr_add_eq_of_eqOn _ _ _ hFactor]
        rw [foldr_add_const_mul]
      rw [← key true, ← key false]

-- ============================================================
-- 5. Length / membership / Nodup of extensionListS and enumerateWorldsS
-- ============================================================

theorem extensionListS_length {O : ALCHOQ.Ontology} (vs : List (DispAtomS O))
    (ctx : Assignment (DispAtomS O)) :
    (extensionListS vs ctx).length = 2 ^ vs.length := by
  classical
  induction vs generalizing ctx with
  | nil => simp [extensionListS]
  | cons p rest ih =>
      simp only [extensionListS, List.length_append, List.length_cons]
      rw [ih, ih, Nat.pow_succ]
      omega

theorem enumerateWorldsS_length (n : Nat) :
    (enumerateWorldsS n).length = 2 ^ n := by
  induction n with
  | zero => simp [enumerateWorldsS]
  | succ k ih =>
      simp only [enumerateWorldsS]
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

theorem mem_extensionListS_of_agrees {O : ALCHOQ.Ontology}
    (vs : List (DispAtomS O)) (ctx : Assignment (DispAtomS O))
    (M : Assignment (DispAtomS O))
    (hAgree : ∀ q, q ∉ vs → M q = ctx q) :
    M ∈ extensionListS vs ctx := by
  classical
  induction vs generalizing ctx with
  | nil =>
      simp only [extensionListS, List.mem_singleton]
      funext q
      exact hAgree q (List.not_mem_nil)
  | cons p rest ih =>
      simp only [extensionListS, List.mem_append]
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

theorem mem_extensionListS_finRange {O : ALCHOQ.Ontology}
    (M : Assignment (DispAtomS O)) (ctx : Assignment (DispAtomS O)) :
    M ∈ extensionListS (List.finRange O.length) ctx := by
  apply mem_extensionListS_of_agrees
  intro q hq
  exact absurd (List.mem_finRange q) hq

theorem mem_enumerateWorldsS (n : Nat) (M : Fin n → Bool) :
    M ∈ enumerateWorldsS n := by
  induction n with
  | zero =>
      simp only [enumerateWorldsS, List.mem_singleton]
      funext q
      exact q.elim0
  | succ k ih =>
      simp only [enumerateWorldsS, List.mem_flatMap]
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

theorem extensionListS_Nodup {O : ALCHOQ.Ontology} (vs : List (DispAtomS O))
    (ctx : Assignment (DispAtomS O)) (hNodup : vs.Nodup) :
    (extensionListS vs ctx).Nodup := by
  classical
  induction vs generalizing ctx with
  | nil => simp [extensionListS]
  | cons p rest ih =>
      have hpNotInRest : p ∉ rest := by
        rw [List.nodup_cons] at hNodup; exact hNodup.1
      have hRestNodup : rest.Nodup := by
        rw [List.nodup_cons] at hNodup; exact hNodup.2
      simp only [extensionListS]
      rw [List.nodup_append]
      refine ⟨ih (setAt ctx p true) hRestNodup,
              ih (setAt ctx p false) hRestNodup, ?_⟩
      intro M1 hM1 M2 hM2 hEq
      have h1 : M1 p = true :=
        mem_extensionListS_value rest ctx p true hpNotInRest M1 hM1
      have h2 : M2 p = false :=
        mem_extensionListS_value rest ctx p false hpNotInRest M2 hM2
      rw [hEq, h2] at h1
      exact (Bool.noConfusion h1)

theorem ext_lift_inj_S {k : Nat} (b : Bool) (M M' : Fin k → Bool)
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

theorem ext_T_ne_ext_F_S {k : Nat} (M M' : Fin k → Bool) :
    (fun i : Fin (k+1) => if h : i.val < k then M ⟨i.val, h⟩ else true) ≠
    (fun i : Fin (k+1) => if h : i.val < k then M' ⟨i.val, h⟩ else false) := by
  intro hEq
  have h := congrFun hEq ⟨k, by omega⟩
  simp at h

theorem nodup_map_injective_S {α β : Type _} (f : α → β)
    (hf : ∀ a b, f a = f b → a = b) (l : List α) (h : l.Nodup) :
    (l.map f).Nodup := by
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

theorem finRange_Nodup_S (n : Nat) : (List.finRange n).Nodup := by
  induction n with
  | zero => simp [List.finRange]
  | succ k ih =>
      rw [List.finRange_succ, List.nodup_cons]
      refine ⟨?_, ?_⟩
      · intro hMem
        rw [List.mem_map] at hMem
        obtain ⟨x, _, hx⟩ := hMem
        exact Fin.succ_ne_zero _ hx
      · exact nodup_map_injective_S Fin.succ (fun _ _ h => Fin.succ_inj.mp h) _ ih

theorem enumerateWorldsS_Nodup (n : Nat) : (enumerateWorldsS n).Nodup := by
  induction n with
  | zero => simp [enumerateWorldsS]
  | succ k ih =>
      simp only [enumerateWorldsS]
      generalize hL : enumerateWorldsS k = L at ih
      clear hL
      induction L with
      | nil => simp
      | cons M rest ihL =>
          rw [List.flatMap_cons, List.nodup_append]
          rw [List.nodup_cons] at ih
          have ihL' := ihL ih.2
          refine ⟨?_, ihL', ?_⟩
          · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
                       List.nodup_nil, and_true, or_false, not_false_eq_true]
            exact ext_T_ne_ext_F_S M M
          · intro x hxAB y hyRest hxy
            simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hxAB
            rw [List.mem_flatMap] at hyRest
            obtain ⟨M', hM'Rest, hyMM'⟩ := hyRest
            simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hyMM'
            apply ih.1
            cases hxAB with
            | inl hxT =>
                cases hyMM' with
                | inl hyT =>
                    have hMM' : M = M' := ext_lift_inj_S true M M' (hxT.symm.trans (hxy.trans hyT))
                    rw [hMM']; exact hM'Rest
                | inr hyF =>
                    exfalso
                    exact ext_T_ne_ext_F_S M M' (hxT.symm.trans (hxy.trans hyF))
            | inr hxF =>
                cases hyMM' with
                | inl hyT =>
                    exfalso
                    exact ext_T_ne_ext_F_S M' M (hyT.symm.trans (hxy.symm.trans hxF))
                | inr hyF =>
                    have hMM' : M = M' := ext_lift_inj_S false M M' (hxF.symm.trans (hxy.trans hyF))
                    rw [hMM']; exact hM'Rest

-- ============================================================
-- 6. Bridge: extensionListS ~ enumerateWorldsS (Perm)
-- ============================================================

private theorem perm_cons_append_swap_S {α : Type _} (x : α) (pre post : List α) :
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

private theorem nodup_perm_of_subset_subset_S {α : Type _}
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
      exact step1.trans (perm_cons_append_swap_S x pre post)

theorem extensionListS_finRange_perm_enumerateWorldsS
    {O : ALCHOQ.Ontology} (ctx : Assignment (DispAtomS O)) :
    (extensionListS (List.finRange O.length) ctx).Perm
    (enumerateWorldsS O.length) := by
  apply nodup_perm_of_subset_subset_S
  · exact extensionListS_Nodup (List.finRange O.length) ctx (finRange_Nodup_S _)
  · exact enumerateWorldsS_Nodup O.length
  · rw [extensionListS_length, enumerateWorldsS_length, List.length_finRange]
  · intro M _
    exact mem_enumerateWorldsS O.length M

-- ============================================================
-- 7. DISPONTE-style sum for SatC and the headline correspondence
-- ============================================================

/-- DISPONTE-style WMC for the SROIQ saturation predicate:
    sum over all worlds of `worldWeightS · [SatC R (selected M) C D]`. -/
noncomputable def disponteWMCSatC (O : ALCHOQ.Ontology) (R : SROIQ.RBox)
    (C D : Concept) (w : DispAtomS O → Bool → Nat) : Nat := by
  classical
  exact (enumerateWorldsS O.length).foldr
    (fun M acc =>
      (if SROIQ.SatC R (selectedAxiomsS O M) C D then worldWeightS O M w else 0) + acc) 0

/-- **The SROIQ-WMC correspondence.**  For every ontology, RBox,
    concept pair, and weight function, the WMC of the compiled SDD
    equals the DISPONTE-style world-sum. -/
theorem wmc_compileSatC_eq_disponteWMCSatC
    (O : ALCHOQ.Ontology) (R : SROIQ.RBox) (C D : Concept)
    (w : DispAtomS O → Bool → Nat) :
    SDD.wmc (compileSatC O R C D) w = disponteWMCSatC O R C D w := by
  classical
  rw [wmc_compileSatC_eq_shannonSatCSum]
  rw [shannonSatCSum_eq_foldr_extensionListS O R C D
        (List.finRange O.length) (fun _ => false) w (finRange_Nodup_S _)]
  have hSummand :
      ∀ M ∈ extensionListS (List.finRange O.length)
              (fun _ => false : Assignment (DispAtomS O)),
        (if SROIQ.SatC R (selectedAxiomsS O M) C D then
            weightAlongS (List.finRange O.length) M w else 0) =
        (if SROIQ.SatC R (selectedAxiomsS O M) C D then
            worldWeightS O M w else 0) := by
    intro M _
    rw [weightAlongS_finRange_eq_worldWeightS]
  rw [foldr_add_eq_of_eqOn _ _ _ hSummand]
  have hPerm := extensionListS_finRange_perm_enumerateWorldsS
                  (O := O) (fun _ => false)
  rw [Perm_foldr_add_eq_fn _ _ _ hPerm]
  rfl

-- ============================================================
-- 8. SDDEncodesSatCQuery + correctness of compileSatC
-- ============================================================

/-- The compiled SDD encodes the SatC query exactly. -/
def SDDEncodesSatCQuery (O : ALCHOQ.Ontology) (R : SROIQ.RBox)
    (C D : Concept) (tree : Tree (DispAtomS O)) : Prop :=
  ∀ M : WorldS O, model tree M ↔ SROIQ.SatC R (selectedAxiomsS O M) C D

theorem compileSatCAux_model (O : ALCHOQ.Ontology) (R : SROIQ.RBox)
    (C D : Concept) (vs : List (DispAtomS O))
    (ctx : Assignment (DispAtomS O)) (M : Assignment (DispAtomS O))
    (hAgree : ∀ q, q ∉ vs → M q = ctx q) :
    model (compileSatCAux O R C D vs ctx) M ↔
    SROIQ.SatC R (selectedAxiomsS O (fun i => M i)) C D := by
  classical
  induction vs generalizing ctx with
  | nil =>
      unfold compileSatCAux
      have hCtx : (fun i => M i) = ctx := by
        funext q; exact hAgree q List.not_mem_nil
      by_cases h : SROIQ.SatC R (selectedAxiomsS O ctx) C D
      · rw [if_pos h]
        constructor
        · intro _; rw [hCtx]; exact h
        · intro _; exact rfl
      · rw [if_neg h]
        constructor
        · intro hMod; exact absurd hMod Bool.false_ne_true
        · intro hSat; rw [hCtx] at hSat; exact absurd hSat h
  | cons p rest ih =>
      unfold compileSatCAux model
      by_cases hMp : M p = true
      · rw [if_pos hMp]
        apply ih
        intro q hq_not_rest
        by_cases hqp : q = p
        · subst hqp; simp [setAt]; exact hMp
        · have hq_not_cons : q ∉ p :: rest := by
            intro h
            cases List.mem_cons.mp h with
            | inl h1 => exact hqp h1
            | inr h2 => exact hq_not_rest h2
          rw [hAgree q hq_not_cons]
          simp [setAt, hqp]
      · have hMp' : M p = false := by
          cases h : M p with
          | true => exact absurd h hMp
          | false => rfl
        rw [if_neg hMp]
        apply ih
        intro q hq_not_rest
        by_cases hqp : q = p
        · subst hqp; simp [setAt]; exact hMp'
        · have hq_not_cons : q ∉ p :: rest := by
            intro h
            cases List.mem_cons.mp h with
            | inl h1 => exact hqp h1
            | inr h2 => exact hq_not_rest h2
          rw [hAgree q hq_not_cons]
          simp [setAt, hqp]

theorem compileSatC_correct (O : ALCHOQ.Ontology) (R : SROIQ.RBox)
    (C D : Concept) :
    SDDEncodesSatCQuery O R C D (compileSatC O R C D) := by
  intro M
  unfold compileSatC
  have h := compileSatCAux_model O R C D (List.finRange O.length)
              (fun _ => false) M
              (fun q hq => absurd (List.mem_finRange q) hq)
  have hM_eq : (fun i => M i) = M := rfl
  rw [hM_eq] at h
  exact h

/-- **Existence form** of the SROIQ-WMC correspondence. -/
theorem exists_sroiq_disponte_correspondence
    (O : ALCHOQ.Ontology) (R : SROIQ.RBox) (C D : Concept) :
    ∃ tree : Tree (DispAtomS O),
      SDDEncodesSatCQuery O R C D tree ∧
      ∀ w : DispAtomS O → Bool → Nat,
        SDD.wmc tree w = disponteWMCSatC O R C D w :=
  ⟨compileSatC O R C D,
   compileSatC_correct O R C D,
   fun w => wmc_compileSatC_eq_disponteWMCSatC O R C D w⟩

end WMC
end SROIQ
end ELKSDD
