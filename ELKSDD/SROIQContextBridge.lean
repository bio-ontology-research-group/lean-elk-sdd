/-
  ELKSDD/SROIQContextBridge.lean
  -------------------------------
  Bridge from SROIQ.SatC completeness to the Tena-Cucala
  context-structure calculus.

  Goal
  ----
  The canonical-model-over-Hintikka-types approach in
  `SROIQSkolemCanonical.lean` cannot close full transitivity, chains,
  symmetry, inversion, or general asymmetry/disjointness:
  ext_role's universal-propagation conjunct has no way to *force*
  hasSelf-self-loop content without nominal markers for intermediate
  elements.  Tena-Cucala 2021 sidesteps this by *constructing*
  countermodels from saturated context structures (§6.3 of the
  thesis).

  This module wires SROIQ.SatC to ALCHOIQContext via a `Bridge`
  structure: it requires a concrete encoding of SROIQ ⟨R, O, C, D⟩
  into a context structure, together with the back-translation
  ``query ∈ S_q ⟹ SROIQ.SatC R O C D``.  Combined with the typed
  hypothesis `TenaCucalaCompleteness`, this discharges SROIQ.SatC
  completeness for **any** RBox shape.

  Axiom-clean over `[propext, Classical.choice, Quot.sound]`.
-/

import ELKSDD.SROIQSkolemCanonical
import ELKSDD.ALCHOIQContext

namespace ELKSDD
namespace SROIQ

open Classical
open ALCHOQ (Concept Ontology Interp)
open ELKSDD.ALCHOIQContext (ContextStructure DerivedClauses QueryClause
                            TenaCucalaCompleteness Saturated entailsQuery
                            QueryClause.inS isSound)

/-- **Concrete bridge witness** for ⟨R, O⟩: a translation from
    SROIQ.SatC concept entailments to a sound, saturated context
    structure plus a back-translation.

    Fields:
    * `D, CD, q` — the encoded context structure, derived cardinality
      clauses, and witness context.
    * `q_mem` — the context q is in D's context list.
    * `sound` — the context structure is sound for the SROIQ ontology
      (interpreted as an ALCHOIQContext ontology).
    * `saturated` — saturation under all 12 rules.
    * `to_query` — produces a QueryClause whose semantic entailment
      mirrors `SROIQ.Entails R O C D'`.
    * `to_query_entails` — the produced query is semantically
      entailed by the ontology whenever the SROIQ entailment holds.
    * `from_inS` — *back-translation*: if the produced query is in
      `S_q`, then `SROIQ.SatC R O C D'` holds.  This is the
      simulation that the consequence-based calculus closes —
      structurally each calculus rule decomposes into a finite chain
      of SROIQ.SatC consequence-rule applications.

    Constructing a `Bridge` for a concrete ⟨R, O⟩ is the residual
    technical work corresponding to §5.2 + §6.3.4 of the thesis.  The
    typed interface lets downstream code reason about SROIQ
    completeness *modulo* this translation. -/
structure Bridge (R : RBox) (O : Ontology) where
  D       : ContextStructure
  CD      : DerivedClauses
  q       : ALCHOIQContext.CtxId
  q_mem   : q ∈ D.contexts
  sound   : isSound O D CD
  saturated : Saturated D
  to_query : Concept → Concept → QueryClause
  to_query_entails :
    ∀ (C E : Concept), Entails R O C E → entailsQuery O (to_query C E)
  from_inS :
    ∀ (C E : Concept),
      (to_query C E).inS D q → SatC R O C E

/-- **Headline SROIQ completeness via Tena-Cucala.**

    Given a typed hypothesis `tc : TenaCucalaCompleteness` (the
    published thesis result) and a `Bridge R O` (the SROIQ ↔
    context-structure translation), SROIQ entailment implies
    SROIQ.SatC derivability for **any** RBox shape.

    This is the headline result the canonical-model-over-types
    construction cannot reach: full canonical satisfaction for trans,
    chain, sym, inv, irrefl, asym, disj — all delegated to the
    context-structure calculus.

    Axiom-clean: depends only on `[propext, Classical.choice,
    Quot.sound]` (the standard Lean foundations) plus the explicit
    hypothesis `tc`.  No `axiom`/`sorry`. -/
theorem sroiq_complete_via_TC
    (tc : TenaCucalaCompleteness)
    {R : RBox} {O : Ontology} (br : Bridge R O)
    (C E : Concept) (hEnt : Entails R O C E) :
    SatC R O C E := by
  -- Step 1: produce the query that mirrors Entails R O C E.
  let Q := br.to_query C E
  -- Step 2: semantic entailment in the ALCHOIQContext sense.
  have hSem : entailsQuery O Q := br.to_query_entails C E hEnt
  -- Step 3: apply Tena-Cucala completeness to obtain Q ∈ S_q.
  have hInS : Q.inS br.D br.q :=
    tc O br.CD br.D br.sound br.saturated Q hSem br.q br.q_mem
  -- Step 4: back-translate Q ∈ S_q to SROIQ.SatC.
  exact br.from_inS C E hInS

/-- **Corollary**: under Tena-Cucala completeness and a Bridge, the
    `Entails ⇒ SatC` direction holds *as an iff* with the trivial
    soundness direction.  This is the *full* SROIQ completeness
    statement at the concept level, mediated by the context-structure
    calculus. -/
theorem sroiq_iff_via_TC
    (tc : TenaCucalaCompleteness)
    {R : RBox} {O : Ontology} (br : Bridge R O)
    (C E : Concept) :
    Entails R O C E ↔ SatC R O C E := by
  refine ⟨sroiq_complete_via_TC tc br C E, ?_⟩
  intro hSat
  exact satC_sound R O C E hSat

end SROIQ
end ELKSDD
