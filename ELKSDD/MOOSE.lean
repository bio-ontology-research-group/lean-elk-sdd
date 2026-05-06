/-
  ELKSDD/MOOSE.lean
  -----------------
  *Bow-tied paper-citation theorems for the MOOSE inference pipeline.*

  This module assembles the end-to-end formal results of the MOOSE
  pipeline into single-statement theorems suitable for direct citation
  from the paper.  Each theorem is *unconditional* (no free hypotheses)
  and audit-clean (only Lean foundation axioms).

  Citation index.

    * `moose_inference_correct` — the bow-tied end-to-end correctness
      theorem: there exists a verified compiled SDD that
        (a) soundly encodes the Sat-query (`SDDEncodesQuery`),
        (b) computes the DISPONTE distribution-semantics marginal
            via weighted model count (`SDD.wmc = disponteWMC`),
        (c) has bounded size (exact: `2^(|O|+1) - 1`).
      Witness: `compileSat O C D`.

    * `sat_decision_polynomial` — Sat decision is polynomial:
      a finite list of size at most `|Sub(O)|²` decides
      Sat-derivability on bounded named atoms.

    * `moose_pipeline_complete` — combined statement: Saturation +
      polynomial Sat decision + verified SDD + DISPONTE
      correspondence in a single packaged theorem.

  Components in detail.

    (1) **Saturation** — `derivableClosure O` lists every Sat-
        derivable bounded atom and has size at most `|Sub(O)|²`
        (`Saturation.lean`).
    (2) **Sat decision** — membership in the saturation decides
        Sat (`sat_iff_in_derivableClosure`).
    (3) **SDD compilation** — `compileSat O C D` is a verified
        Shannon-expansion tree of size exactly `2^(|O|+1) - 1`
        encoding the Sat-query (`Compilation.lean` + A6).
    (4) **DISPONTE correspondence** — the WMC of the compiled SDD
        equals the DISPONTE marginal for every weight function
        (`CompilationWMC.lean`, unconditional).

  Caveats — what is *not* formalised here.

    * Polynomial *SDD size* via vtree-aware compilation is folklore
      (Riguzzi 2015 TPLP).  Our polynomial result is for *Sat
      decision* only; SDD size is the worst-case exponential
      Shannon-tree bound.  The conditional polynomial bound via
      essential variables (`essential_polynomial_bound`) is
      provided in `Compilation.lean`.
    * Real-valued probabilities (ℝ-valued DISPONTE) require Mathlib
      and are deferred (A5).

  All theorems audit-clean — only Lean foundation axioms.
-/

import ELKSDD.Compilation
import ELKSDD.CompilationWMC
import ELKSDD.Saturation

namespace ELKSDD
namespace ELpp

open SDD

-- ============================================================
-- (1) End-to-end inference correctness
-- ============================================================

/-- **MOOSE inference correctness theorem.**

    For every OWL 2 EL ontology `O` and Sat-query `(C, D)`, there
    exists a verified compiled SDD that simultaneously:

      (a) **soundly encodes the query**: a world `M : World O`
          satisfies the SDD iff `Sat (selectedAxioms O M) C D`;
      (b) **computes the DISPONTE marginal**: for every per-axiom
          weight function `w`, the weighted model count of the SDD
          equals the DISPONTE distribution-semantics probability
          `disponteWMC O C D w`;
      (c) **has bounded size**: exactly `2^(|O|+1) - 1` nodes (the
          worst-case Shannon-tree count, A6).

    The witness is `compileSat O C D`. -/
theorem moose_inference_correct (O : Ontology) (C D : Concept) :
    ∃ tree : Tree (DispAtom O),
      (∀ M : World O, model tree M ↔ Sat (selectedAxioms O M) C D) ∧
      (∀ w : DispAtom O → Bool → Nat, SDD.wmc tree w = disponteWMC O C D w) ∧
      size tree = 2 ^ (O.length + 1) - 1 :=
  ⟨compileSat O C D,
   compileSat_correct O C D,
   compileSat_disponte_correspondence O C D,
   compileSat_size_eq O C D⟩

-- ============================================================
-- (2) Polynomial-time Sat decision
-- ============================================================

/-- **Polynomial-time Sat decision theorem.**

    For every OWL 2 EL ontology `O`, the Sat-derivability relation
    on bounded named atoms is decidable via a finite list
    `L = derivableClosure O` whose size is at most `(numSubexprs O)²`:

      (a) `|L| ≤ |Sub(O)|²` (polynomial saturation bound);
      (b) `(C, D) ∈ L ↔ Sat O C D` for any `C, D ∈ Sub(O)`.

    This is the polynomial-time *decision* component of the MOOSE
    inference pipeline.  The probabilistic-marginal component (WMC
    over the SDD) has Shannon-tree exponential worst-case size;
    polynomial bounds via vtree-aware compilation are folklore
    (Riguzzi 2015 TPLP) and not formalised here. -/
theorem sat_decision_polynomial (O : Ontology) :
    ∃ L : List (Concept × Concept),
      L.length ≤ (numSubexprs O) ^ 2 ∧
      (∀ {C D : Concept},
          C ∈ subsOfOntology O → D ∈ subsOfOntology O →
          (Sat O C D ↔ (C, D) ∈ L)) :=
  ⟨derivableClosure O,
   derivableClosure_length O,
   fun hC hD => sat_iff_in_derivableClosure O hC hD⟩

-- ============================================================
-- (3) Combined complexity decomposition
-- ============================================================

/-- **MOOSE inference pipeline — complete factorisation.**

    For every OWL 2 EL ontology `O` and query `(C, D)`, the MOOSE
    inference pipeline factors as:

      (1) **Saturation** + **polynomial Sat decision**: a list of
          size at most `|Sub(O)|²` decides Sat-derivability on
          bounded named atoms.
      (2) **Verified SDD with DISPONTE correspondence**: a Shannon-
          expansion tree of exactly `2^(|O|+1) - 1` nodes correctly
          encodes the query, and its WMC equals the DISPONTE
          distribution-semantics marginal for every weight function.

    Components compose: Sat decision and SDD-model coincide on every
    world; the SDD's WMC is the DISPONTE marginal. -/
theorem moose_pipeline_complete (O : Ontology) (C D : Concept) :
    -- (1) Saturation + polynomial Sat decision.
    (∃ L : List (Concept × Concept),
        L.length ≤ (numSubexprs O) ^ 2 ∧
        (∀ {C' D' : Concept},
            C' ∈ subsOfOntology O → D' ∈ subsOfOntology O →
            (Sat O C' D' ↔ (C', D') ∈ L))) ∧
    -- (2) Verified SDD with DISPONTE correspondence.
    (∃ tree : Tree (DispAtom O),
        (∀ M : World O, model tree M ↔ Sat (selectedAxioms O M) C D) ∧
        (∀ w : DispAtom O → Bool → Nat, SDD.wmc tree w = disponteWMC O C D w) ∧
        size tree = 2 ^ (O.length + 1) - 1) :=
  ⟨sat_decision_polynomial O, moose_inference_correct O C D⟩

-- ============================================================
-- Audit
-- ============================================================

#print axioms moose_inference_correct
#print axioms sat_decision_polynomial
#print axioms moose_pipeline_complete

end ELpp
end ELKSDD
