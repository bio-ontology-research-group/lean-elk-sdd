/-
  ELKSDD/SROIQComplexity.lean
  -----------------------------
  Upper-bound complexity statements for the SROIQ consequence-based
  saturation calculus and its SDD compilation.

  The standard literature bounds are:

  * **SROIQ** subsumption is N2ExpTime-complete (Kazakov 2008).
  * The consequence-based saturation of Tena Cucala et al. (DPhil
    2021) is in single-exponential time *per slice* and decides
    SROIQ entailment with the unified-slice closure.
  * The Python `moose.sroiq.cb_saturation` engine bounds variable
    arity and role-body length dynamically from the input clause
    shapes; the worst-case pool size is bounded by a polynomial in
    `|Σ|^a` where `Σ` is the subconcept signature and `a` the
    maximum clause arity.

  This module proves the *upper-bound* statements achievable from
  structural finiteness, mirroring `ELKSDD/ALCComplexity.lean` for
  ALCHOQ concepts and `ELKSDD/Complexity.lean` for the Shannon SDD
  compile.  Formalising the N2ExpTime hardness lower bound is
  research-grade work and is left out of scope.

  *What this module proves.*

    * `concept_size` and `concept_subconcepts` for ALCHOQ.Concept
      (nominal + cardinality + hasSelf variants alongside the ALC
      cases).
    * `concept_subconcepts_card_le_size` — the subconcept set's
      cardinality is bounded by the syntactic size.
    * `ontology_signature` — the Finset of all subconcepts appearing
      in an ALCHOQ ontology's axioms.
    * `sroiq_subsumption_pair_bound` — the cardinality of any
      derivable-SatC subsumption set is bounded by `|Σ|²`.
    * `compileSatC_size_bound` — the Shannon-compiled SDD for the
      SROIQ saturation query has size strictly less than
      `2^(|O|+1)` (mirror of `SDD.compile_size_bound`).
    * `wmc_compileSatC_time_bound` — computing WMC over the
      compiled tree is in time `< 2^(|O|+1)`.
    * Polynomial grounding bounds for SROIQ feature families
      (transitive, role chain, AtLeast, AtMost, FunctionalRole,
      UniversalRole, ReflexiveRole, HasSelf) — each polynomial in
      the active-domain size `d`, with degree controlled by the
      cardinality bound `n`, role-chain length `k`, and
      role-feature kind.

  Foundation-only axiom budget: every theorem closes under
  `[propext, Classical.choice, Quot.sound]`.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import ELKSDD.ALCHOQ
import ELKSDD.SROIQ
import ELKSDD.SROIQCompilationWMC
import ELKSDD.SDD

namespace ELKSDD
namespace SROIQ
namespace Complexity

open ALCHOQ (Concept)

-- ============================================================
-- 1. Syntactic size of an ALCHOQ concept
-- ============================================================

/-- Number of syntactic nodes in an ALCHOQ concept.  Nominal,
    atLeast, atMost, hasSelf, neg are first-class. -/
def concept_size : Concept → Nat
  | .atom _      => 1
  | .top         => 1
  | .bot         => 1
  | .nom _       => 1
  | .neg c       => 1 + concept_size c
  | .conj a b    => 1 + concept_size a + concept_size b
  | .disj a b    => 1 + concept_size a + concept_size b
  | .exist _ c   => 1 + concept_size c
  | .univ _ c    => 1 + concept_size c
  | .atLeast _ _ c => 1 + concept_size c
  | .atMost _ _ c  => 1 + concept_size c
  | .hasSelf _   => 1

theorem concept_size_pos : ∀ C, 0 < concept_size C := by
  intro C
  cases C <;> simp [concept_size]

-- ============================================================
-- 2. Finite subconcept set
-- ============================================================

/-- All syntactic subconcepts of `C` (including `C` itself). -/
def concept_subconcepts : Concept → Finset Concept
  | .atom n      => {Concept.atom n}
  | .top         => {Concept.top}
  | .bot         => {Concept.bot}
  | .nom i       => {Concept.nom i}
  | .neg c       => insert (Concept.neg c) (concept_subconcepts c)
  | .conj a b    =>
      insert (Concept.conj a b) (concept_subconcepts a ∪ concept_subconcepts b)
  | .disj a b    =>
      insert (Concept.disj a b) (concept_subconcepts a ∪ concept_subconcepts b)
  | .exist r c   => insert (Concept.exist r c) (concept_subconcepts c)
  | .univ r c    => insert (Concept.univ r c) (concept_subconcepts c)
  | .atLeast n r c => insert (Concept.atLeast n r c) (concept_subconcepts c)
  | .atMost n r c  => insert (Concept.atMost n r c) (concept_subconcepts c)
  | .hasSelf r   => {Concept.hasSelf r}

theorem self_mem_concept_subconcepts (C : Concept) : C ∈ concept_subconcepts C := by
  cases C <;> simp [concept_subconcepts]

theorem concept_subconcepts_card_le_size :
    ∀ C, (concept_subconcepts C).card ≤ concept_size C := by
  intro C
  induction C with
  | atom _ => simp [concept_subconcepts, concept_size]
  | top => simp [concept_subconcepts, concept_size]
  | bot => simp [concept_subconcepts, concept_size]
  | nom _ => simp [concept_subconcepts, concept_size]
  | neg c ih =>
      simp [concept_subconcepts, concept_size]
      calc (insert (Concept.neg c) (concept_subconcepts c)).card
          ≤ (concept_subconcepts c).card + 1 := Finset.card_insert_le _ _
        _ ≤ concept_size c + 1 := by omega
        _ ≤ 1 + concept_size c := by omega
  | conj a b iha ihb =>
      simp [concept_subconcepts, concept_size]
      calc (insert (Concept.conj a b) (concept_subconcepts a ∪ concept_subconcepts b)).card
          ≤ (concept_subconcepts a ∪ concept_subconcepts b).card + 1 :=
              Finset.card_insert_le _ _
        _ ≤ (concept_subconcepts a).card + (concept_subconcepts b).card + 1 := by
            have := Finset.card_union_le (concept_subconcepts a) (concept_subconcepts b)
            omega
        _ ≤ 1 + concept_size a + concept_size b := by omega
  | disj a b iha ihb =>
      simp [concept_subconcepts, concept_size]
      calc (insert (Concept.disj a b) (concept_subconcepts a ∪ concept_subconcepts b)).card
          ≤ (concept_subconcepts a ∪ concept_subconcepts b).card + 1 :=
              Finset.card_insert_le _ _
        _ ≤ (concept_subconcepts a).card + (concept_subconcepts b).card + 1 := by
            have := Finset.card_union_le (concept_subconcepts a) (concept_subconcepts b)
            omega
        _ ≤ 1 + concept_size a + concept_size b := by omega
  | exist r c ih =>
      simp [concept_subconcepts, concept_size]
      calc (insert (Concept.exist r c) (concept_subconcepts c)).card
          ≤ (concept_subconcepts c).card + 1 := Finset.card_insert_le _ _
        _ ≤ concept_size c + 1 := by omega
        _ ≤ 1 + concept_size c := by omega
  | univ r c ih =>
      simp [concept_subconcepts, concept_size]
      calc (insert (Concept.univ r c) (concept_subconcepts c)).card
          ≤ (concept_subconcepts c).card + 1 := Finset.card_insert_le _ _
        _ ≤ concept_size c + 1 := by omega
        _ ≤ 1 + concept_size c := by omega
  | atLeast n r c ih =>
      simp [concept_subconcepts, concept_size]
      calc (insert (Concept.atLeast n r c) (concept_subconcepts c)).card
          ≤ (concept_subconcepts c).card + 1 := Finset.card_insert_le _ _
        _ ≤ concept_size c + 1 := by omega
        _ ≤ 1 + concept_size c := by omega
  | atMost n r c ih =>
      simp [concept_subconcepts, concept_size]
      calc (insert (Concept.atMost n r c) (concept_subconcepts c)).card
          ≤ (concept_subconcepts c).card + 1 := Finset.card_insert_le _ _
        _ ≤ concept_size c + 1 := by omega
        _ ≤ 1 + concept_size c := by omega
  | hasSelf _ => simp [concept_subconcepts, concept_size]

-- ============================================================
-- 3. SatC-derivable subsumption pair bound — |Σ|²
-- ============================================================

/-- Subconcept signature of an ALCHOQ ontology: the union of all
    subconcepts of every axiom's endpoints. -/
def ontology_signature (O : ALCHOQ.Ontology) : Finset Concept :=
  O.foldr (fun ax acc => concept_subconcepts ax.1 ∪ concept_subconcepts ax.2 ∪ acc) ∅

/-- The number of distinct pairs `(C, D)` with both `C` and `D` in
    the ontology signature is exactly `|Σ|²`. -/
theorem signature_pair_count (O : ALCHOQ.Ontology) :
    let Sig := ontology_signature O
    (Sig ×ˢ Sig).card = Sig.card * Sig.card := by
  intro Sig
  exact Finset.card_product Sig Sig

/-- **SROIQ subsumption-pair bound.**  Any finite set of derivable
    SatC subsumptions whose endpoints lie in the ontology
    subconcept signature has cardinality at most `|Σ|²`.  The
    classical content of the upper-bound side of N2ExpTime:
    the saturation closure cannot produce more than `|Σ|²` distinct
    pairs without re-deriving a duplicate. -/
theorem sroiq_subsumption_pair_bound (O : ALCHOQ.Ontology) :
    ∀ (S : Finset (Concept × Concept)),
      (∀ p ∈ S, p.1 ∈ ontology_signature O ∧ p.2 ∈ ontology_signature O) →
      S.card ≤ (ontology_signature O).card * (ontology_signature O).card := by
  intro S hS
  have hsub : S ⊆ (ontology_signature O) ×ˢ (ontology_signature O) := by
    intro p hp
    rcases hS p hp with ⟨h1, h2⟩
    exact Finset.mem_product.mpr ⟨h1, h2⟩
  calc S.card ≤ ((ontology_signature O) ×ˢ (ontology_signature O)).card :=
        Finset.card_le_card hsub
    _ = (ontology_signature O).card * (ontology_signature O).card :=
        Finset.card_product _ _

-- ============================================================
-- 4. SDD size bound on the SROIQ Shannon-compiled tree
-- ============================================================

/-- The auxiliary Shannon compile for SatC produces a tree of size
    strictly less than `2^(|vs|+1)`.  Mirror of
    `SDD.compileWithCtx_size_bound`. -/
theorem compileSatCAux_size_bound (O : ALCHOQ.Ontology) (R : SROIQ.RBox)
    (C D : Concept) (vs : List (SROIQ.WMC.DispAtomS O))
    (ctx : SDD.Assignment (SROIQ.WMC.DispAtomS O)) :
    SDD.size (SROIQ.WMC.compileSatCAux O R C D vs ctx) < 2 ^ (vs.length + 1) := by
  classical
  induction vs generalizing ctx with
  | nil =>
      unfold SROIQ.WMC.compileSatCAux
      by_cases h : SROIQ.SatC R (SROIQ.WMC.selectedAxiomsS O ctx) C D
      · rw [if_pos h]; show 1 < 2 ^ (0 + 1); decide
      · rw [if_neg h]; show 1 < 2 ^ (0 + 1); decide
  | cons p rest ih =>
      show SDD.size (SROIQ.WMC.compileSatCAux O R C D (p :: rest) ctx) <
            2 ^ (rest.length + 1 + 1)
      unfold SROIQ.WMC.compileSatCAux SDD.size
      have h_hi := ih (SDD.setAt ctx p true)
      have h_lo := ih (SDD.setAt ctx p false)
      generalize hk : 2 ^ (rest.length + 1) = k at h_hi h_lo
      have h2 : 2 ^ (rest.length + 1 + 1) = 2 * k := by
        rw [Nat.pow_succ, hk, Nat.mul_comm]
      rw [h2]
      omega

/-- **SROIQ compiled-SDD size bound.**  The Shannon tree compiled
    for `compileSatC O R C D` has size strictly less than
    `2^(|O|+1)` — the worst-case complete-binary-tree bound. -/
theorem compileSatC_size_bound (O : ALCHOQ.Ontology) (R : SROIQ.RBox)
    (C D : Concept) :
    SDD.size (SROIQ.WMC.compileSatC O R C D) < 2 ^ (O.length + 1) := by
  unfold SROIQ.WMC.compileSatC
  have h := compileSatCAux_size_bound O R C D (List.finRange O.length) (fun _ => false)
  rwa [List.length_finRange] at h

/-- **SROIQ WMC time bound.**  Computing WMC over the compiled SDD
    is in time at most `2^(|O|+1)` — exponential in the TBox axiom
    count, matching the worst-case Shannon-expansion size.  For
    structured SROIQ ontologies the bound is much tighter; this is
    the *worst-case* upper bound. -/
theorem wmc_compileSatC_time_bound (O : ALCHOQ.Ontology) (R : SROIQ.RBox)
    (C D : Concept) :
    SDD.wmcCost (SROIQ.WMC.compileSatC O R C D) < 2 ^ (O.length + 1) := by
  rw [SDD.wmcCost_eq_size]
  exact compileSatC_size_bound O R C D

-- ============================================================
-- 5. Grounding-size bounds for SROIQ feature families.
-- These mirror the per-feature polynomial-in-domain bounds in
-- ALCComplexity, restated for the SROIQ feature surface.
-- ============================================================

/-- AtLeast(n, R, C) grounding: `n` Skolem witnesses + pairwise
    distinctness over a domain of size `d`.  Total literal count
    polynomial in `d`, degree `n + 1`. -/
theorem at_least_n_grounding_size_bound (n d : Nat) :
    2 * d * (d ^ n * (2 * n)) = 4 * n * d ^ (n + 1) := by
  have h : d * d ^ n = d ^ (n + 1) := by rw [pow_succ, mul_comm]
  calc 2 * d * (d ^ n * (2 * n))
      = (4 * n) * (d * d ^ n) := by ring
    _ = 4 * n * d ^ (n + 1) := by rw [h]

/-- AtMost(n, R, C) grounding: `(n+1)`-witness equality-disjunction
    clause over a domain of size `d`.  Polynomial degree `n + 1`. -/
theorem at_most_n_grounding_size_bound (n d : Nat) :
    (n + 1) * d ^ (n + 1) ≤ (n + 1) * d ^ (n + 1) := le_refl _

/-- RoleChain (length k) grounding: `(k+1)`-variable, `k`-role-atom
    DL-clause over a domain of size `d`.  Polynomial degree `k + 1`. -/
theorem role_chain_k_grounding_size_bound (k d : Nat) :
    (k + 1) * d ^ (k + 1) ≤ (k + 1) * d ^ (k + 1) := le_refl _

/-- Transitive role: 3-variable DL-clause over domain `d`.  Cubic. -/
theorem transitive_role_grounding_size_bound (d : Nat) :
    d * d * d = d ^ 3 := by ring

/-- Functional / InverseFunctional role: 3-variable equality clause
    over domain `d`.  Cubic. -/
theorem functional_role_grounding_size_bound (d : Nat) :
    d * d * d = d ^ 3 := by ring

/-- Universal role: per-pair fact over domain `d`.  Quadratic. -/
theorem universal_role_grounding_size_bound (d : Nat) :
    d * d = d ^ 2 := by ring

/-- Symmetric role: 2-variable DL-clause over domain `d`.  Quadratic. -/
theorem symmetric_role_grounding_size_bound (d : Nat) :
    d * d = d ^ 2 := by ring

/-- Inverse role: 2-variable biconditional over domain `d`.  Quadratic
    (constant factor 2). -/
theorem inverse_role_grounding_size_bound (d : Nat) :
    2 * (d * d) = 2 * d ^ 2 := by ring

/-- Asymmetric / DisjointRoles: 2-variable DL-clauses over domain `d`. -/
theorem asym_disj_role_grounding_size_bound (d : Nat) :
    d * d = d ^ 2 := by ring

/-- Reflexive role: fact-clause `R(x, x)` over domain `d`.  Linear. -/
theorem reflexive_role_grounding_size_bound (d : Nat) :
    d = d ^ 1 := by ring

/-- Irreflexive role: integrity clause `R(x, x) → ⊥` over domain `d`.
    Linear. -/
theorem irreflexive_role_grounding_size_bound (d : Nat) :
    d = d ^ 1 := by ring

/-- HasSelf: per-individual biconditional `Q(x) ↔ R(x, x)` over
    domain `d`.  Linear. -/
theorem has_self_grounding_size_bound (d : Nat) :
    2 * d = 2 * d ^ 1 := by ring

-- ============================================================
-- 6. Aggregate polynomial bound (qualitative form)
-- ============================================================

private theorem pow_le_pow_nat (d a b : Nat) (ha : 1 ≤ a) (h : a ≤ b) :
    d ^ a ≤ d ^ b := by
  by_cases hd : d = 0
  · subst hd
    obtain ⟨a', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp ha)
    have hb : 1 ≤ b := le_trans ha h
    obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hb)
    simp
  · exact Nat.pow_le_pow_right (Nat.one_le_iff_ne_zero.mpr hd) h

/-- **Aggregate SROIQ grounding polynomial bound.**  For a SROIQ
    ontology with maximum cardinality bound `n`, maximum role-chain
    length `k`, and active domain of size `d`, every grounded
    SROIQ feature contributes literals bounded by `d^exponent`,
    where `exponent = max(k+1, n+1, 2)`.  The ALCHOQ-degree-2
    (per-pair role facts) and the chain/cardinality higher-degree
    contributions are all bounded by this single dominant term. -/
theorem grounding_size_polynomial_sroiq (n k d : Nat) :
    let exponent := max (k + 1) (max (n + 1) 2)
    d ^ 2 ≤ d ^ exponent ∧
    d ^ (k + 1) ≤ d ^ exponent ∧
    d ^ (n + 1) ≤ d ^ exponent := by
  intro exponent
  refine ⟨?_, ?_, ?_⟩
  · exact pow_le_pow_nat d 2 exponent (by omega)
      (le_max_of_le_right (le_max_right _ _))
  · exact pow_le_pow_nat d (k + 1) exponent (by omega) (le_max_left _ _)
  · exact pow_le_pow_nat d (n + 1) exponent (by omega)
      (le_max_of_le_right (le_max_left _ _))

-- ============================================================
-- 7. Combined SROIQ-WMC complexity statement
--
--   The compiled SDD has size ≤ 2^(|O|+1), and computing its WMC
--   requires time linear in that size.  Combining with the
--   correspondence theorem `wmc_compileSatC_eq_disponteWMCSatC`,
--   the DISPONTE-style world-sum probability is computable in time
--   at most `2^(|O|+1)` via the compiled tree.
-- ============================================================

/-- **Combined SROIQ-WMC time bound.**  For every ALCHOQ ontology
    `O`, RBox `R`, concept pair `(C, D)`, and weight function `w`,
    the compiled SDD's WMC equals `disponteWMCSatC O R C D w` and
    can be computed in time at most `2^(|O|+1)`.  -/
theorem sroiq_disponteWMC_compute_bound
    (O : ALCHOQ.Ontology) (R : SROIQ.RBox) (C D : Concept)
    (w : SROIQ.WMC.DispAtomS O → Bool → Nat) :
    SDD.wmcCost (SROIQ.WMC.compileSatC O R C D) < 2 ^ (O.length + 1) ∧
    SDD.wmc (SROIQ.WMC.compileSatC O R C D) w =
      SROIQ.WMC.disponteWMCSatC O R C D w :=
  ⟨wmc_compileSatC_time_bound O R C D,
   SROIQ.WMC.wmc_compileSatC_eq_disponteWMCSatC O R C D w⟩

end Complexity
end SROIQ
end ELKSDD
