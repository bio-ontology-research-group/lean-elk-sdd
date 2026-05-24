/-
  Root module for ELKSDD.

  The Lean 4 mechanisation of the MOOSE neuro-symbolic reasoner ---
  from EL through full SROIQ (OWL 2 DL), with Sentential Decision
  Diagrams, weighted model counting, the DISPONTE distribution
  semantics, and a verified treatment of reasoning shortcuts under
  the independence assumption.

  Layers (each import-block corresponds to one):

    * Generic infrastructure: `Util`, `SDD`, `DISPONTE`,
      `DISPONTERat`.
    * EL family (Horn): `MiniEL` (zero axioms), `EL`, `ELpp`,
      `Normalize` + `RangeNorm` + `Merging` + `OWL2EL`,
      `ELKBoundary`; saturation machinery (`Saturation`, `SCC`,
      `SCCWorld`, `SCCWMCUniform`, `SCCNomLHS`,
      `SatFactorGeneral`, `SatComplexity`, `Stratified`); compile
      (`Compilation`, `CompilationWMC`, `Complexity`); citation
      theorems (`MOOSE`).
    * ALC: `ALC`, `Completeness`, `CompletenessExamples`,
      `ALCComplexity`.
    * ALCHOQ (nominals + qualified cardinality): `ALCHOQ`
      (zero-axiom saturation soundness), `ALCHOQCompleteness`,
      and the Tena Cucala context-structure calculus
      (`ALCHOIQContext`, indirectly via the SROIQ bridge).
    * SROIQ (full OWL 2 DL): `SROIQ` (RBox semantics with per-shape
      soundness), `SROIQCompleteness`, `SROIQComplexity`,
      `SROIQPythonParity`, headline correspondence
      `SROIQCompilationWMC`.
    * RS-IA: `RSIA` --- van Krieken et al. (NeSy 2025) Theorem 11
      and its positive complement, both mechanised for the SROIQ
      saturation predicate.

  Axiom hygiene.  All exposed theorems audit to only
  `propext`, `Classical.choice`, `Quot.sound`.  Two notable cases
  of stronger hygiene: `MiniEL` (atomic-subsumption fragment) is
  *fully* axiom-free; `ALCHOQ.sat_sound` reports zero axioms.  No
  user axioms, no `sorry`s.

  `Mathlib` is required only for the `Rat`-valued layers
  (`DISPONTERat`, `RSIA`).  The classical-DL layers are Lean 4 core
  only.

  See `README.md` for module-by-module details and quick examples.
-/

import ELKSDD.Util
import ELKSDD.MiniEL
import ELKSDD.EL
import ELKSDD.ELpp
import ELKSDD.Normalize
import ELKSDD.RangeNorm
import ELKSDD.Merging
import ELKSDD.OWL2EL
import ELKSDD.ELKBoundary
import ELKSDD.DISPONTE
import ELKSDD.Compilation
import ELKSDD.CompilationWMC
import ELKSDD.Complexity
import ELKSDD.SatComplexity
import ELKSDD.Stratified
import ELKSDD.Saturation
import ELKSDD.SCC
import ELKSDD.SDD
import ELKSDD.MOOSE
import ELKSDD.SatFactorGeneral
import ELKSDD.SCCWorld
import ELKSDD.DISPONTERat
import ELKSDD.SCCWMCUniform
import ELKSDD.SCCNomLHS
import ELKSDD.ALC
import ELKSDD.Completeness
import ELKSDD.CompletenessExamples
import ELKSDD.ALCComplexity
import ELKSDD.ALCHOQ
import ELKSDD.ALCHOQCompleteness
import ELKSDD.SROIQ
import ELKSDD.SROIQCompleteness
import ELKSDD.SROIQPythonParity
import ELKSDD.SROIQCompilationWMC
import ELKSDD.SROIQComplexity
import ELKSDD.RSIA
import ELKSDD.ModularBEARSMultilinear
