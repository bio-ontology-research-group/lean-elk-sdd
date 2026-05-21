/-
  ELKSDD/RSIA.lean
  ----------------
  *Reasoning shortcuts under the independence assumption (RS-IA)*,
  formalised in Lean 4 for the SROIQ-WMC setting of MOOSE.

  Source. van Krieken, Minervini, Ponti, Vergari,
  "Neurosymbolic Reasoning Shortcuts under the Independence
  Assumption", NeSy 2025 (arXiv:2507.11357).

  Headline result.

    * `weak_RS_aware_implicant` — van Krieken et al. (2025),
      Theorem 11: if the UCI (universal conditionally
      independent) model class weakly represents a strictly-mixed
      RS mixture, then the deterministic part of its marginals is
      an *implicant* of the constraint, and the cover of that
      implicant equals the confusion set `{α(c*) | α ∈ A}`.

    * `sroiq_RSIA_necessary` — instantiation to MOOSE's SROIQ
      DISPONTE-style WMC: the same conclusion for the SROIQ
      saturation predicate.

    * `RS_mixture_in_mixOfUCI` — the **positive complement** to
      Theorem 11: every RS mixture is representable in the
      mixture-of-UCI family.  The family generalises UCI by
      categorical mixing over multiple UCI cells; in SROIQ, each
      cell corresponds to a justification's "deterministic part"
      and admits the corresponding RS-induced concept distribution.

    * `sroiq_RSIA_sufficient` — instantiation of the positive
      complement to the SROIQ saturation predicate.

  Foundation-only axiom budget: no `axiom`, no `sorry`.
-/

import ELKSDD.SROIQCompilationWMC
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Tactic.Linarith

namespace ELKSDD
namespace RSIA

open Classical

-- ============================================================
-- 1. Worlds, marginals, factorised (UCI) distributions
-- ============================================================

/-- A `World k` is a Boolean assignment over `k` atoms. -/
abbrev World (k : Nat) : Type := Fin k → Bool

/-- A constraint (label-classifier) over worlds, valued in `Prop`. -/
abbrev Constraint (k : Nat) : Type := World k → Prop

/-- Per-atom marginal of a UCI distribution. -/
abbrev Marginal (k : Nat) : Type := Fin k → Rat

/-- Per-coordinate factor of a UCI distribution at world `M`. -/
def factor {k : Nat} (μ : Marginal k) (M : World k) (i : Fin k) : Rat :=
  if M i then μ i else 1 - μ i

/-- UCI (universal conditionally independent) distribution
    parameterised by per-atom marginals `μ`. -/
def UCI {k : Nat} (μ : Marginal k) (M : World k) : Rat :=
  (List.finRange k).foldr (fun i acc => factor μ M i * acc) 1

/-- Admissibility: every marginal lies in `[0, 1]`. -/
def Admissible {k : Nat} (μ : Marginal k) : Prop := ∀ i, 0 ≤ μ i ∧ μ i ≤ 1

/-- The deterministic part of `μ`: an incomplete concept fixing
    atom `i` whenever `μ i ∈ {0, 1}` and leaving it free otherwise. -/
noncomputable def detPart {k : Nat} (μ : Marginal k) : Fin k → Option Bool :=
  fun i =>
    if μ i = 0 then some false
    else if μ i = 1 then some true
    else none

/-- Cover of an incomplete concept: the worlds consistent with the
    fixed atoms. -/
def inCover {k : Nat} (cD : Fin k → Option Bool) (M : World k) : Prop :=
  ∀ i b, cD i = some b → M i = b

-- ============================================================
-- 2. Foldr-product positivity helpers
-- ============================================================

theorem foldr_mul_nonneg {α : Type _} (l : List α) (f : α → Rat)
    (hNN : ∀ a ∈ l, 0 ≤ f a) :
    0 ≤ l.foldr (fun a acc => f a * acc) 1 := by
  induction l with
  | nil => exact zero_le_one
  | cons x rest ih =>
      simp only [List.foldr_cons]
      exact mul_nonneg (hNN x List.mem_cons_self)
        (ih (fun a ha => hNN a (List.mem_cons_of_mem _ ha)))

theorem foldr_mul_pos_of_all_pos {α : Type _} (l : List α) (f : α → Rat)
    (h : ∀ a ∈ l, 0 < f a) :
    0 < l.foldr (fun a acc => f a * acc) 1 := by
  induction l with
  | nil => exact one_pos
  | cons x rest ih =>
      simp only [List.foldr_cons]
      exact mul_pos (h x List.mem_cons_self)
        (ih (fun a ha => h a (List.mem_cons_of_mem _ ha)))

theorem foldr_mul_pos_imp_each_pos {α : Type _} (l : List α) (f : α → Rat)
    (hNN : ∀ a ∈ l, 0 ≤ f a)
    (h : 0 < l.foldr (fun a acc => f a * acc) 1) :
    ∀ a ∈ l, 0 < f a := by
  induction l with
  | nil => intro a ha; exact absurd ha List.not_mem_nil
  | cons x rest ih =>
      simp only [List.foldr_cons] at h
      have hxNN : 0 ≤ f x := hNN x List.mem_cons_self
      have hRestNN : ∀ a ∈ rest, 0 ≤ f a :=
        fun a ha => hNN a (List.mem_cons_of_mem _ ha)
      have hRestProdNN :
          0 ≤ rest.foldr (fun a acc => f a * acc) 1 :=
        foldr_mul_nonneg rest f hRestNN
      have hfx_pos : 0 < f x := by
        rcases eq_or_lt_of_le hxNN with hz | hp
        · exfalso; rw [← hz, zero_mul] at h; exact lt_irrefl 0 h
        · exact hp
      have hRest_pos :
          0 < rest.foldr (fun a acc => f a * acc) 1 := by
        rcases eq_or_lt_of_le hRestProdNN with hz | hp
        · exfalso; rw [← hz, mul_zero] at h; exact lt_irrefl 0 h
        · exact hp
      intro a ha
      rcases List.mem_cons.mp ha with hxa | hMem
      · exact hxa ▸ hfx_pos
      · exact ih hRestNN hRest_pos a hMem

theorem foldr_mul_pos_iff {α : Type _} (l : List α) (f : α → Rat)
    (hNN : ∀ a ∈ l, 0 ≤ f a) :
    0 < l.foldr (fun a acc => f a * acc) 1 ↔ ∀ a ∈ l, 0 < f a :=
  ⟨foldr_mul_pos_imp_each_pos l f hNN, foldr_mul_pos_of_all_pos l f⟩

-- ============================================================
-- 3. UCI support characterisation
-- ============================================================

theorem factor_nonneg {k : Nat} (μ : Marginal k) (hAdm : Admissible μ)
    (M : World k) (i : Fin k) : 0 ≤ factor μ M i := by
  unfold factor
  by_cases hM : M i = true
  · rw [hM]; simp only [if_true]; exact (hAdm i).1
  · have hMf : M i = false := by
      cases h : M i with
      | true => exact absurd h hM
      | false => rfl
    rw [hMf]; simp only [Bool.false_eq_true, if_false]; linarith [(hAdm i).2]

theorem factor_pos_iff_inCover_at {k : Nat} (μ : Marginal k)
    (hAdm : Admissible μ) (M : World k) (i : Fin k) :
    0 < factor μ M i ↔ ∀ b, detPart μ i = some b → M i = b := by
  classical
  unfold factor detPart
  have hLo := (hAdm i).1
  have hHi := (hAdm i).2
  constructor
  · intro hPos b hEq
    by_cases hz : μ i = 0
    · -- detPart i = some false
      rw [if_pos hz] at hEq
      have hb : b = false := by injection hEq with h; exact h.symm
      subst hb
      by_cases hM : M i = true
      · rw [hM] at hPos; simp only [if_true] at hPos
        exact absurd hz (ne_of_gt hPos)
      · cases h : M i with
        | true => exact absurd h hM
        | false => rfl
    · by_cases ho : μ i = 1
      · rw [if_neg hz, if_pos ho] at hEq
        have hb : b = true := by injection hEq with h; exact h.symm
        subst hb
        by_cases hM : M i = true
        · exact hM
        · have hMf : M i = false := by
            cases h : M i with
            | true => exact absurd h hM
            | false => rfl
          rw [hMf] at hPos
          simp only [Bool.false_eq_true, if_false] at hPos
          rw [ho] at hPos
          linarith
      · rw [if_neg hz, if_neg ho] at hEq
        exact absurd hEq (by intro h; cases h)
  · intro hAll
    by_cases hM : M i = true
    · rw [hM]; simp only [if_true]
      rcases eq_or_lt_of_le hLo with hz | hp
      · exfalso
        have hμz : μ i = 0 := hz.symm
        have hDet : (if μ i = 0 then some false
                     else if μ i = 1 then some true
                     else none) = some false := by rw [if_pos hμz]
        have := hAll false hDet
        rw [hM] at this
        exact Bool.noConfusion this
      · exact hp
    · have hMf : M i = false := by
        cases h : M i with
        | true => exact absurd h hM
        | false => rfl
      rw [hMf]
      simp only [Bool.false_eq_true, if_false]
      rcases eq_or_lt_of_le hHi with ho | hh
      · exfalso
        have hμ1 : μ i = 1 := ho
        have hμz : μ i ≠ 0 := by rw [hμ1]; norm_num
        have hDet : (if μ i = 0 then some false
                     else if μ i = 1 then some true
                     else none) = some true := by
          rw [if_neg hμz, if_pos hμ1]
        have := hAll true hDet
        rw [hMf] at this
        exact Bool.noConfusion this
      · linarith

/-- **UCI support.**  The UCI distribution at world `M` is strictly
    positive iff `M` lies in the cover of the deterministic part of
    its marginals. -/
theorem UCI_pos_iff_inCover {k : Nat} (μ : Marginal k) (hAdm : Admissible μ)
    (M : World k) :
    0 < UCI μ M ↔ inCover (detPart μ) M := by
  classical
  unfold UCI inCover
  rw [foldr_mul_pos_iff _ _ (fun i _ => factor_nonneg μ hAdm M i)]
  constructor
  · intro h i b hEq
    exact (factor_pos_iff_inCover_at μ hAdm M i).mp (h i (List.mem_finRange i)) b hEq
  · intro h i _
    exact (factor_pos_iff_inCover_at μ hAdm M i).mpr (fun b hEq => h i b hEq)

-- ============================================================
-- 4. RS-mixture distribution and its support
-- ============================================================

/-- A summand of an RS mixture: weight `p` if `M = α c*`, else `0`. -/
noncomputable def mixSummand {k : Nat} (cstar M : World k)
    (ap : (World k → World k) × Rat) : Rat :=
  if M = ap.1 cstar then ap.2 else 0

theorem mixSummand_nonneg {k : Nat} {cstar M : World k}
    (ap : (World k → World k) × Rat) (hp : 0 ≤ ap.2) :
    0 ≤ mixSummand cstar M ap := by
  unfold mixSummand
  split_ifs
  · exact hp
  · exact le_refl 0

/-- The RS mixture, indexed by a list of (remapping, weight) pairs. -/
noncomputable def pMixZip {k : Nat} (zipped : List ((World k → World k) × Rat))
    (cstar M : World k) : Rat :=
  zipped.foldr (fun ap acc => mixSummand cstar M ap + acc) 0

theorem pMixZip_nonneg {k : Nat}
    (zipped : List ((World k → World k) × Rat))
    (hπ_nn : ∀ ap ∈ zipped, 0 ≤ ap.2)
    (cstar M : World k) :
    0 ≤ pMixZip zipped cstar M := by
  unfold pMixZip
  induction zipped with
  | nil => simp
  | cons ap rest ih =>
      simp only [List.foldr_cons]
      have hap : 0 ≤ ap.2 := hπ_nn ap List.mem_cons_self
      have hRest : ∀ q ∈ rest, 0 ≤ q.2 :=
        fun q hq => hπ_nn q (List.mem_cons_of_mem _ hq)
      have hSum := mixSummand_nonneg (cstar := cstar) (M := M) ap hap
      linarith [ih hRest]

/-- **RS-mixture support.**  Under strictly-positive weights, the
    mixture at `M` is strictly positive iff `M = α c*` for some
    `α` in the list. -/
theorem pMixZip_pos_iff_mem {k : Nat}
    (zipped : List ((World k → World k) × Rat))
    (hπ_pos : ∀ ap ∈ zipped, 0 < ap.2)
    (cstar M : World k) :
    0 < pMixZip zipped cstar M ↔ ∃ ap ∈ zipped, M = ap.1 cstar := by
  classical
  unfold pMixZip
  induction zipped with
  | nil =>
      simp [List.foldr_nil]
  | cons ap rest ih =>
      have hap_pos : 0 < ap.2 := hπ_pos ap List.mem_cons_self
      have hRest_pos : ∀ q ∈ rest, 0 < q.2 :=
        fun q hq => hπ_pos q (List.mem_cons_of_mem _ hq)
      have hRest_nn : ∀ q ∈ rest, 0 ≤ q.2 :=
        fun q hq => le_of_lt (hRest_pos q hq)
      have hRest_sum_nn : 0 ≤ rest.foldr
          (fun ap acc => mixSummand cstar M ap + acc) 0 := by
        have := pMixZip_nonneg rest hRest_nn cstar M
        unfold pMixZip at this; exact this
      simp only [List.foldr_cons]
      refine ⟨?_, ?_⟩
      · intro hPos
        by_cases hMatch : M = ap.1 cstar
        · exact ⟨ap, List.mem_cons_self, hMatch⟩
        · have h0 : mixSummand cstar M ap = 0 := by
            unfold mixSummand
            rw [if_neg hMatch]
          rw [h0, zero_add] at hPos
          obtain ⟨q, hq, hQ⟩ := (ih hRest_pos).mp hPos
          exact ⟨q, List.mem_cons_of_mem _ hq, hQ⟩
      · rintro ⟨q, hq, hQ⟩
        rcases List.mem_cons.mp hq with hapEq | hqInRest
        · -- hapEq : q = ap; rewrite hQ to get M = ap.1 cstar
          rw [hapEq] at hQ
          have hsum_pos : 0 < mixSummand cstar M ap := by
            unfold mixSummand
            rw [if_pos hQ]
            exact hap_pos
          have hap_summand_nn_rest : 0 ≤ rest.foldr
              (fun ap acc => mixSummand cstar M ap + acc) 0 := by
            have := pMixZip_nonneg rest hRest_nn cstar M
            unfold pMixZip at this; exact this
          linarith
        · have hap_summand_nn : 0 ≤ mixSummand cstar M ap :=
            mixSummand_nonneg ap (le_of_lt hap_pos)
          have hRest_pos_sum : 0 < rest.foldr
              (fun ap acc => mixSummand cstar M ap + acc) 0 :=
            (ih hRest_pos).mpr ⟨q, hqInRest, hQ⟩
          linarith

-- ============================================================
-- 5. Weak RS-awareness and the necessary condition
-- ============================================================

/-- A list of concept remappings each preserving the constraint. -/
def IsRemappingList {k : Nat} (φ : Constraint k)
    (A : List (World k → World k)) : Prop :=
  ∀ α ∈ A, ∀ M, (φ (α M) ↔ φ M)

/-- The confusion set associated to `A` and ground-truth `c*`. -/
def confusion {k : Nat} (A : List (World k → World k))
    (cstar M : World k) : Prop :=
  ∃ α ∈ A, M = α cstar

/-- Helper: in `List.zip A π`, both projections are in their
    respective source lists. -/
theorem mem_zip_of_mem {α β : Type _} {l₁ : List α} {l₂ : List β}
    {ap : α × β} (h : ap ∈ List.zip l₁ l₂) :
    ap.1 ∈ l₁ ∧ ap.2 ∈ l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp at h
  | cons x rest ih =>
      cases l₂ with
      | nil => simp at h
      | cons y rest₂ =>
          simp only [List.zip_cons_cons, List.mem_cons] at h
          rcases h with hEq | hMem
          · subst hEq; exact ⟨List.mem_cons_self, List.mem_cons_self⟩
          · obtain ⟨h1, h2⟩ := ih hMem
            exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

/-- Helper: for an index `n < min(A.length, π.length)`,
    `(A[n], π[n]) ∈ List.zip A π`. -/
theorem zip_get_mem {α β : Type _} (l₁ : List α) (l₂ : List β)
    (n : Nat) (h1 : n < l₁.length) (h2 : n < l₂.length) :
    (l₁.get ⟨n, h1⟩, l₂.get ⟨n, h2⟩) ∈ List.zip l₁ l₂ := by
  induction l₁ generalizing l₂ n with
  | nil => exact absurd h1 (by simp)
  | cons x rest ih =>
      cases l₂ with
      | nil => exact absurd h2 (by simp)
      | cons y rest₂ =>
          cases n with
          | zero =>
              simp only [List.get, List.zip_cons_cons]
              exact List.mem_cons_self
          | succ m =>
              simp only [List.zip_cons_cons]
              apply List.mem_cons_of_mem
              have hm1 : m < rest.length := by
                simp only [List.length_cons] at h1; omega
              have hm2 : m < rest₂.length := by
                simp only [List.length_cons] at h2; omega
              -- Recursive call
              have := ih rest₂ m hm1 hm2
              -- The goal is `(rest.get ⟨m, hm1⟩, rest₂.get ⟨m, hm2⟩) ∈ List.zip rest rest₂`
              exact this

/-- **Cover equals confusion set.**  If a UCI distribution agrees
    pointwise with a strictly-mixed RS mixture, the cover of its
    deterministic part is exactly the confusion set. -/
theorem weak_RS_aware_cover_eq_confusion {k : Nat}
    (μ : Marginal k) (hAdm : Admissible μ)
    (A : List (World k → World k))
    (πs : List Rat)
    (hLen : πs.length = A.length)
    (hπ_pos : ∀ p ∈ πs, 0 < p)
    (cstar : World k)
    (hRep : ∀ M, UCI μ M =
      pMixZip (List.zip A πs) cstar M) :
    ∀ M, inCover (detPart μ) M ↔ confusion A cstar M := by
  classical
  intro M
  have hZipPos : ∀ ap ∈ List.zip A πs, 0 < ap.2 := by
    intro ap hap
    exact hπ_pos ap.2 (mem_zip_of_mem hap).2
  rw [← UCI_pos_iff_inCover μ hAdm M, hRep M]
  rw [pMixZip_pos_iff_mem _ hZipPos cstar M]
  unfold confusion
  constructor
  · rintro ⟨ap, hap, hEq⟩
    exact ⟨ap.1, (mem_zip_of_mem hap).1, hEq⟩
  · rintro ⟨α, hα, hEq⟩
    -- Find the index of α in A and use the corresponding zip pair.
    rw [List.mem_iff_get] at hα
    obtain ⟨n, hnEq⟩ := hα
    have hn_lt_πlen : n.val < πs.length := by rw [hLen]; exact n.isLt
    refine ⟨(A.get n, πs.get ⟨n.val, hn_lt_πlen⟩), ?_, ?_⟩
    · exact zip_get_mem A πs n.val n.isLt hn_lt_πlen
    · -- M = α c* and α = A.get n, so M = (A.get n) cstar
      show M = A.get n cstar
      rw [hnEq]; exact hEq

/-- **van Krieken et al. (2025), Theorem 11.**  If a UCI
    distribution `UCI μ` weakly represents a strictly-mixed RS
    mixture `pMixZip (zip A πs) c*`, then the deterministic part
    of `μ` is an *implicant* of the constraint `φ`: every world in
    its cover satisfies `φ M ↔ φ cstar`. -/
theorem weak_RS_aware_implicant {k : Nat}
    (φ : Constraint k)
    (μ : Marginal k) (hAdm : Admissible μ)
    (A : List (World k → World k))
    (πs : List Rat)
    (hLen : πs.length = A.length)
    (hπ_pos : ∀ p ∈ πs, 0 < p)
    (hRemap : IsRemappingList φ A)
    (cstar : World k)
    (hRep : ∀ M, UCI μ M = pMixZip (List.zip A πs) cstar M) :
    ∀ M, inCover (detPart μ) M → (φ M ↔ φ cstar) := by
  intro M hInCover
  obtain ⟨α, hαA, hM⟩ :=
    (weak_RS_aware_cover_eq_confusion μ hAdm A πs hLen hπ_pos cstar hRep M).mp hInCover
  rw [hM]
  exact hRemap α hαA cstar

-- ============================================================
-- 6. SROIQ-WMC instantiation
-- ============================================================

open ELKSDD.SROIQ.WMC
open ELKSDD.ALCHOQ (Concept)
open ELKSDD.SROIQ (RBox)

/-- SROIQ constraint induced by a saturation query.  Returns a
    `Prop` (avoiding the need for a `Decidable` instance on the
    SROIQ consequence-based predicate). -/
def sroiqConstraint (O : ELKSDD.ALCHOQ.Ontology)
    (R : RBox) (C D : Concept) : Constraint O.length :=
  fun M => ELKSDD.SROIQ.SatC R (selectedAxiomsS O M) C D

/-- **SROIQ RS-IA necessary condition.**  Instantiation of Theorem
    11 to the SROIQ-WMC setting of MOOSE.  If a UCI marginal `μ`
    represents a strictly-mixed RS mixture over remappings that
    preserve `SROIQ.SatC R (selectedAxiomsS O ·) C D`, then every
    world in the cover of the deterministic part of `μ` agrees
    with the ground-truth `c*` on the SROIQ saturation query. -/
theorem sroiq_RSIA_necessary
    (O : ELKSDD.ALCHOQ.Ontology) (R : RBox) (C D : Concept)
    (A : List (World O.length → World O.length))
    (πs : List Rat)
    (hLen : πs.length = A.length)
    (hπ_pos : ∀ p ∈ πs, 0 < p)
    (hRemap : IsRemappingList (sroiqConstraint O R C D) A)
    (μ : Marginal O.length) (hAdm : Admissible μ)
    (cstar : World O.length)
    (hRep : ∀ M, UCI μ M = pMixZip (List.zip A πs) cstar M) :
    ∀ M, inCover (detPart μ) M →
      (ELKSDD.SROIQ.SatC R (selectedAxiomsS O M) C D ↔
       ELKSDD.SROIQ.SatC R (selectedAxiomsS O cstar) C D) :=
  weak_RS_aware_implicant (sroiqConstraint O R C D) μ hAdm A πs
    hLen hπ_pos hRemap cstar hRep

-- ============================================================
-- 7. Justification-indexed (mixture-of-UCI) perception family
-- ============================================================

/-- Deterministic marginal: `1` where `w i = true`, `0` otherwise. -/
def deltaMarginal {k : Nat} (w : World k) : Marginal k :=
  fun i => if w i then 1 else 0

theorem deltaMarginal_admissible {k : Nat} (w : World k) :
    Admissible (deltaMarginal w) := by
  intro i
  unfold deltaMarginal
  by_cases hw : w i = true
  · rw [hw]; simp only [if_true]; refine ⟨?_, ?_⟩ <;> norm_num
  · have hwF : w i = false := by
      cases h : w i with | true => exact absurd h hw | false => rfl
    rw [hwF]; simp only [Bool.false_eq_true, if_false]
    refine ⟨?_, ?_⟩ <;> norm_num

/-- The per-coordinate factor of a `deltaMarginal w` is the indicator
    of `M i = w i`. -/
theorem factor_delta_eq {k : Nat} (w : World k) (M : World k) (i : Fin k) :
    factor (deltaMarginal w) M i = (if M i = w i then (1 : Rat) else 0) := by
  unfold factor deltaMarginal
  cases hM : M i <;> cases hW : w i <;> simp

/-- The foldr of `deltaMarginal`-factors over a list equals the
    indicator of "all listed coordinates agree". -/
theorem foldr_factor_delta_eq {k : Nat} (w : World k) (M : World k)
    (l : List (Fin k)) :
    l.foldr (fun i acc => factor (deltaMarginal w) M i * acc) 1 =
    (if ∀ i ∈ l, M i = w i then (1 : Rat) else 0) := by
  classical
  induction l with
  | nil => simp
  | cons x rest ih =>
      simp only [List.foldr_cons]
      rw [factor_delta_eq, ih]
      by_cases hX : M x = w x
      · rw [if_pos hX, one_mul]
        by_cases hRest : ∀ i ∈ rest, M i = w i
        · rw [if_pos hRest]
          have h : ∀ i ∈ (x :: rest), M i = w i := by
            intro i hi
            rcases List.mem_cons.mp hi with hxi | hi'
            · exact hxi ▸ hX
            · exact hRest i hi'
          rw [if_pos h]
        · rw [if_neg hRest]
          have h : ¬ ∀ i ∈ (x :: rest), M i = w i := fun h =>
            hRest (fun i hi => h i (List.mem_cons_of_mem _ hi))
          rw [if_neg h]
      · rw [if_neg hX, zero_mul]
        have h : ¬ ∀ i ∈ (x :: rest), M i = w i := fun h =>
          hX (h x List.mem_cons_self)
        rw [if_neg h]

/-- **UCI of a deterministic marginal is the world indicator.** -/
theorem UCI_delta_eq_indicator {k : Nat} (w : World k) (M : World k) :
    UCI (deltaMarginal w) M = (if M = w then (1 : Rat) else 0) := by
  unfold UCI
  rw [foldr_factor_delta_eq]
  by_cases hEq : M = w
  · rw [if_pos hEq]
    have h : ∀ i ∈ List.finRange k, M i = w i := by
      intro i _; rw [hEq]
    rw [if_pos h]
  · rw [if_neg hEq]
    have h : ¬ ∀ i ∈ List.finRange k, M i = w i := by
      intro hAll
      apply hEq
      funext i
      exact hAll i (List.mem_finRange i)
    rw [if_neg h]

/-- Mixture-of-UCI distribution: a categorical-weighted sum of UCI
    distributions, each given by its own marginal vector.  The
    *justification-indexed* perception family. -/
noncomputable def mixOfUCI {k : Nat}
    (cells : List ((Marginal k) × Rat)) (M : World k) : Rat :=
  cells.foldr (fun cell acc => cell.2 * UCI cell.1 M + acc) 0

/-- An auxiliary list-mapping lemma: the foldr over `A.zip πs` of an
    indicator-summand equals the foldr over `(A.map δ).zip πs` of the
    corresponding UCI-summand. -/
theorem mixOfUCI_eq_pMixZip_aux {k : Nat}
    (A : List (World k → World k)) (πs : List Rat)
    (cstar M : World k) :
    (List.zip A πs).foldr
        (fun ap acc => mixSummand cstar M ap + acc) 0 =
    (List.zip (A.map (fun α => deltaMarginal (α cstar))) πs).foldr
        (fun cell acc => cell.2 * UCI cell.1 M + acc) 0 := by
  classical
  induction A generalizing πs with
  | nil => simp
  | cons α restA ih =>
      cases πs with
      | nil => simp
      | cons p restπ =>
          simp only [List.zip_cons_cons, List.foldr_cons, List.map_cons]
          rw [ih restπ]
          -- Show: mixSummand cstar M (α, p) = p * UCI (deltaMarginal (α cstar)) M
          have hSum : mixSummand cstar M (α, p) =
              p * UCI (deltaMarginal (α cstar)) M := by
            unfold mixSummand
            rw [UCI_delta_eq_indicator]
            split_ifs with h
            · simp
            · simp
          rw [hSum]

/-- **van Krieken positive complement / Theorem 11 converse.**
    Every RS mixture is representable in the mixture-of-UCI family
    using deterministic-marginal cells (one per remapping).

    Concretely: given any list `A` of concept remappings and weights
    `πs`, the RS-mixture distribution `pMixZip (zip A πs) c*`
    coincides pointwise with `mixOfUCI (zip (map δ_{α(c*)} A) πs)`,
    where each cell uses the deterministic marginal pinning the
    corresponding `α(c*)`.

    No remapping or admissibility hypothesis is required for the
    *representability* itself; the deterministic marginals are
    admissible by `deltaMarginal_admissible`. -/
theorem RS_mixture_in_mixOfUCI {k : Nat}
    (A : List (World k → World k)) (πs : List Rat)
    (cstar : World k) :
    ∀ M,
      pMixZip (List.zip A πs) cstar M =
      mixOfUCI (List.zip (A.map (fun α => deltaMarginal (α cstar))) πs) M := by
  intro M
  unfold pMixZip mixOfUCI
  exact mixOfUCI_eq_pMixZip_aux A πs cstar M

/-- Every cell in the canonical mixture-of-UCI representation has an
    admissible marginal. -/
theorem RS_mixture_cells_admissible {k : Nat}
    (A : List (World k → World k)) (cstar : World k) :
    ∀ μ ∈ A.map (fun α => deltaMarginal (α cstar)), Admissible μ := by
  intro μ hμ
  rw [List.mem_map] at hμ
  obtain ⟨α, _, hEq⟩ := hμ
  rw [← hEq]
  exact deltaMarginal_admissible (α cstar)

-- ============================================================
-- 8. SROIQ-WMC instantiation of the positive complement
-- ============================================================

/-- **SROIQ RS-IA sufficient condition.**  The positive complement
    of `sroiq_RSIA_necessary`: for any list of concept remappings
    and weights, the RS mixture is representable in the
    mixture-of-UCI perception family.  This is unconditional: it
    holds for arbitrary remappings (in particular, the family is
    expressive enough to capture every RS mixture for any SROIQ
    query). -/
theorem sroiq_RSIA_sufficient
    (O : ELKSDD.ALCHOQ.Ontology) (R : RBox) (C D : Concept)
    (A : List (World O.length → World O.length))
    (πs : List Rat)
    (cstar : World O.length) :
    ∀ M,
      pMixZip (List.zip A πs) cstar M =
      mixOfUCI (List.zip (A.map (fun α => deltaMarginal (α cstar))) πs) M := by
  -- The result is independent of the SROIQ-specific constraint;
  -- it depends only on the world/marginal structure.  We expose it
  -- as a SROIQ-named theorem for symmetry with `sroiq_RSIA_necessary`.
  intro M
  exact RS_mixture_in_mixOfUCI A πs cstar M

end RSIA
end ELKSDD
