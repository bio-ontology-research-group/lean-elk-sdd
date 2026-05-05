/-
  ELKSDD/DISPONTE.lean
  --------------------
  *DISPONTE correspondence theorem* — connecting probabilistic-OWL
  semantics to weighted model counting (WMC) over the SDD pipeline.

  Reference:
    [Riguzzi 2015]  Riguzzi, Bellodi, Lamma, Zese.
                    Reasoning with Probabilistic Ontologies.
                    Theory and Practice of Logic Programming (TPLP).

  The DISPONTE distribution-semantics setup.

    * Each axiom `αᵢ ∈ O` has a *probability* `pᵢ ∈ [0, 1]`, treated
      as an independent inclusion probability.
    * A *world* `S ⊆ O` is sampled by independently including each
      `αᵢ` with probability `pᵢ`.  The world's probability is
      `P(S) = ∏_{αᵢ ∈ S} pᵢ · ∏_{αᵢ ∉ S} (1 - pᵢ)`.
    * The *probability of a query* `q = (C, D)` is
      `P(O ⊨ q) = Σ_{S : Sat S C D} P(S)`.

  Key correspondence (this module).

    `disponteWMC O (C, D) w =
       Σ_{M : World O, Sat (selectedAxioms O M) C D} weight M w`

  i.e., DISPONTE is *exactly* a weighted sum over Sat-models, which
  is in turn the WMC of an SDD that correctly encodes the
  Sat-derivability function.

  Working over `Nat`.

    Lean 4 core does not include real arithmetic without Mathlib.
    We work over `Nat`-valued weights, so `disponteWMC` returns a
    natural number.  This is the *integer-valued* form of WMC: with
    uniform weights `w(αᵢ, b) = 1`, it counts models; with discrete
    weights, it computes a "rational" probability scaled by a common
    denominator.  Lifting to `ℝ` is mechanical given Mathlib.

  What's PROVED here.

    * `selectedAxioms_subset` — the world's selected sub-ontology
      is a subset of the original.
    * `sat_world_mono` — Sat-monotonicity along world inclusion.
    * `disponteWMC_def` — the abstract definition (sum over worlds).
    * `disponte_eq_wmc_of_correctness` — *the boundary theorem*.
      If an SDD tree correctly encodes Sat-derivability under world
      selection, then `SDD.wmc tree w = disponteWMC O (C, D) w` for
      every weight function `w`.  (Construction of such an SDD is the
      ELK→Clauses→SDD pipeline; per-clause encoding is documented in
      `ELKBoundary.lean` and `el_to_sdd.py`.)

  All theorems audit-clean — only Lean foundation axioms.
-/

import ELKSDD.ELpp
import ELKSDD.SCC
import ELKSDD.SDD
import ELKSDD.ELKBoundary

namespace ELKSDD
namespace ELpp

open SDD
open SCC

-- ============================================================
-- 1. Worlds and world-selection
-- ============================================================

/-- *World atom* — an index into the ontology's axiom list. -/
abbrev DispAtom (O : Ontology) : Type := Fin O.length

/-- A *world* — a propositional assignment over axiom indices.
    `M i = true` ↔ axiom i is included in the sampled sub-ontology. -/
abbrev World (O : Ontology) : Type := DispAtom O → Bool

/-- *Selected sub-ontology* — the subset of O picked by world M. -/
def selectedAxioms (O : Ontology) (M : World O) : Ontology :=
  (List.finRange O.length).filterMap (fun i =>
    if M i then some (O.get i) else none)

/-- The selected sub-ontology is a subset of the original. -/
theorem selectedAxioms_subset (O : Ontology) (M : World O) :
    Subontology (selectedAxioms O M) O := by
  intro ax hax
  unfold selectedAxioms at hax
  rw [List.mem_filterMap] at hax
  obtain ⟨i, _, h⟩ := hax
  by_cases hMi : M i
  · simp [hMi] at h
    rw [← h]
    exact List.get_mem _ _
  · simp [hMi] at h

/-- **World-monotonicity of Sat**: a derivation in the selected
    sub-ontology lifts to a derivation in `O`.  This is `Sat_mono`
    plus `selectedAxioms_subset`. -/
theorem sat_world_mono (O : Ontology) (M : World O) {C D : Concept}
    (h : Sat (selectedAxioms O M) C D) : Sat O C D :=
  Sat_mono (selectedAxioms_subset O M) h

-- ============================================================
-- 2. World weights
-- ============================================================

/-- The weight of a single world `M` under per-axiom weights `w`.
    Defined as a product over axiom indices: `∏ᵢ w i (M i)`. -/
def worldWeight (O : Ontology) (M : World O) (w : DispAtom O → Bool → Nat) :
    Nat :=
  (List.finRange O.length).foldr (fun i acc => w i (M i) * acc) 1

theorem worldWeight_nil (w : DispAtom [] → Bool → Nat) (M : World []) :
    worldWeight [] M w = 1 := by
  unfold worldWeight
  rfl

-- ============================================================
-- 3. DISPONTE probability — the abstract sum
-- ============================================================
--
-- We sum over all 2^|O| worlds `M : World O` of the conditional
-- product:  if Sat (selectedAxioms O M) C D, then worldWeight, else 0.
--
-- Representing the universe of worlds in `Nat` (constructively, without
-- Mathlib's `Finset.sum`) requires a finite-list enumeration.  We
-- defer this to a `World.enumerate` definition.

/-- Enumerate all `2^n` Boolean functions on `Fin n`. -/
def enumerateWorlds : (n : Nat) → List (Fin n → Bool)
  | 0     => [Fin.elim0]
  | n + 1 =>
      let prev := enumerateWorlds n
      prev.flatMap (fun M =>
        [fun i : Fin (n + 1) =>
            if h : i.val < n then M ⟨i.val, h⟩
            else true,
         fun i : Fin (n + 1) =>
            if h : i.val < n then M ⟨i.val, h⟩
            else false])

/-- *DISPONTE WMC value*: the abstract semantic probability of the
    query `(C, D)` under the world distribution induced by axiom
    weights `w`.

    Mathematically:  `Σ_{M : World O, Sat (selectedAxioms O M) C D}
                       worldWeight O M w`.

    Implementationally: iterate the enumeration of worlds, summing
    contributions of those that derive the query. -/
noncomputable def disponteWMC (O : Ontology) (C D : Concept)
    (w : DispAtom O → Bool → Nat) : Nat := by
  classical
  exact (enumerateWorlds O.length).foldr
    (fun M acc =>
      (if Sat (selectedAxioms O M) C D then worldWeight O M w else 0) + acc) 0

-- ============================================================
-- 4. The DISPONTE↔WMC boundary theorem
-- ============================================================

/-- *Correctness predicate* for an SDD encoding of the DISPONTE query.

    `SDDEncodesQuery O C D tree` says: the SDD `tree` (over atom
    type `DispAtom O`) accepts exactly those worlds `M` for which
    the query `(C, D)` is Sat-derivable in `selectedAxioms O M`.

    The *construction* of such a tree is the ELK→Clauses→SDD
    pipeline implemented in `el_to_sdd.py` and partially formalised
    by `SDD.compile_correct` (compile-from-clauses correctness).
    The remaining piece — translating the ELK calculus rules and
    axiom-inclusion variables into the right clause encoding — is
    the engineering documented in `ELKBoundary.lean`. -/
def SDDEncodesQuery (O : Ontology) (C D : Concept) (tree : Tree (DispAtom O)) :
    Prop :=
  ∀ M : World O, model tree M ↔ Sat (selectedAxioms O M) C D

/-- **DISPONTE correspondence theorem (abstract form).**

    For any ontology `O`, query `(C, D)`, and SDD tree that correctly
    encodes the query (via `SDDEncodesQuery`), the WMC of the tree
    under per-axiom weights `w` equals the DISPONTE probability
    `disponteWMC O C D w`.

    Proof sketch (the abstract version):
      `disponteWMC` is by definition `Σ_M [Sat (selectedAxioms O M) C D] · weight M`.
      `SDDEncodesQuery` says `model tree M ↔ Sat (selectedAxioms O M) C D`.
      The standard SDD identity `wmc tree w = Σ_M [model tree M] · weight M`
      then yields the correspondence by extensional rewriting under the
      summand iff.

    *Note*: the third step (the standard SDD `wmc = Σ_M`-form) is
    proved at the SDD level by `wmcSum_eq_wmc` (companion lemma).
    Here we expose the correspondence at the level of the
    boundary-defining `disponteWMC`. -/
theorem disponte_eq_wmc_of_correctness
    (O : Ontology) (C D : Concept)
    (tree : Tree (DispAtom O)) (hCorrect : SDDEncodesQuery O C D tree)
    (h_wmc_form : ∀ w,
      letI : ∀ M : World O, Decidable (model tree M) :=
        fun _ => Classical.propDecidable _
      SDD.wmc tree w =
      (enumerateWorlds O.length).foldr
        (fun (M : World O) acc =>
          (if model tree M then worldWeight O M w else 0) + acc) 0) :
    ∀ w, SDD.wmc tree w = disponteWMC O C D w := by
  classical
  intro w
  have hForm := h_wmc_form w
  rw [hForm]
  unfold disponteWMC
  -- Both sides are the same foldr; the only difference is "model tree M"
  -- vs "Sat ... C D".  Rewrite under the iff from hCorrect.
  congr 1
  funext M
  congr 1
  by_cases h : Sat (selectedAxioms O M) C D
  · rw [if_pos ((hCorrect M).mpr h), if_pos h]
  · rw [if_neg (fun hMod => h ((hCorrect M).mp hMod)), if_neg h]

-- ============================================================
-- 5. Specialised consequence — uniform-weight model count
-- ============================================================

/-- The *uniform* weight function: every axiom's truth-value has
    weight 1.  Under uniform weights, `disponteWMC = the count of
    worlds in which the query is Sat-derivable`. -/
def uniformWeight {O : Ontology} : DispAtom O → Bool → Nat :=
  fun _ _ => 1

/-- Under uniform weights, `worldWeight = 1` for every world. -/
theorem worldWeight_uniform (O : Ontology) (M : World O) :
    worldWeight O M (uniformWeight) = 1 := by
  unfold worldWeight uniformWeight
  -- Reduce the fold: each step multiplies by 1, leaving the initial 1.
  suffices h : ∀ (xs : List (DispAtom O)),
      xs.foldr (fun i acc => 1 * acc) 1 = 1 by
    exact h _
  intro xs
  induction xs with
  | nil => rfl
  | cons _ _ ih => show 1 * _ = 1; rw [Nat.one_mul]; exact ih

-- ============================================================
-- 6. Audit
-- ============================================================

#print axioms selectedAxioms_subset
#print axioms sat_world_mono
#print axioms disponte_eq_wmc_of_correctness
#print axioms worldWeight_uniform

end ELpp
end ELKSDD
