/-
  Root module for ELKSDD.

  ELKSDD bundles four reusable Lean 4 modules:

    * ELKSDD.Util    — list-length lemmas for flatMap/map patterns,
                       triangular numbers (`K(K-1)/2` arithmetic).
    * ELKSDD.MiniEL  — atomic-subsumption EL with first-principles
                       ELK soundness + completeness (zero axioms).
    * ELKSDD.EL      — full conjunction + existential fragment of
                       EL with ELK rules R₀, R_⊤, R_⊑, R⁻_⊓, R⁺_⊓,
                       R_⊥, R⁺_∃, R_⊥-∃; soundness end-to-end;
                       completeness via canonical model with role
                       extension.
    * ELKSDD.SDD     — BDD-style sentential decision diagrams
                       generic over the atom type; Shannon-
                       expansion compile from CNF; structural
                       linear-time WMC; compile correctness proved
                       end-to-end.

  All non-foundational dependencies are tracked: `#print axioms
  <theorem>` reveals only `propext`, `Classical.choice`,
  `Quot.sound` (Lean's standard foundation) for theorems that need
  classical reasoning, and no axioms at all for the constructive
  fragment in MiniEL.

  No Mathlib dependency — Lean 4 core only.
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
import ELKSDD.Complexity
import ELKSDD.Stratified
import ELKSDD.SCC
import ELKSDD.SDD
