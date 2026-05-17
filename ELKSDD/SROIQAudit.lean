/-
  ELKSDD/SROIQAudit.lean
  -----------------------
  Axiom-budget audit for the SROIQ-direction Lean modules.  Every
  ``#print axioms`` line below must report at most
  ``propext, Classical.choice, Quot.sound`` (the standard Lean
  foundational axioms); anything more is a leak.

  Build with ``lake env lean ELKSDD/SROIQAudit.lean`` and read the
  ``info:`` lines.
-/

import ELKSDD.SROIQ
import ELKSDD.ALCHOQ
import ELKSDD.ALCHOQCompleteness
import ELKSDD.SROIQCompleteness
import ELKSDD.ALCHOIQContext

namespace ELKSDD

-- ============================================================
-- ALCHOQ: full set-extension semantics + sound CB calculus, plus
-- the classical extension with full soundness.
-- ============================================================
#print axioms ALCHOQ.sat_sound
#print axioms ALCHOQ.satC_sound
#print axioms ALCHOQ.Interp.eval_nom_iff
#print axioms ALCHOQ.Interp.eval_atLeast_zero
#print axioms ALCHOQ.Interp.eval_atMost_zero
#print axioms ALCHOQ.Interp.eval_atLeast_one_iff_exist

-- ============================================================
-- SROIQ: RBox semantics + per-feature soundness lemmas.
-- ============================================================
#print axioms SROIQ.incl_sound
#print axioms SROIQ.trans_sound
#print axioms SROIQ.sym_sound
#print axioms SROIQ.asym_sound
#print axioms SROIQ.refl_sound
#print axioms SROIQ.irrefl_sound
#print axioms SROIQ.inv_sound
#print axioms SROIQ.disj_sound
#print axioms SROIQ.chain_two_sound
#print axioms SROIQ.trans_iff_chain
#print axioms SROIQ.sym_iff_self_inverse
#print axioms SROIQ.Interp.nom_singleton
#print axioms SROIQ.Interp.has_self_iff
#print axioms SROIQ.universal_implies_role_features

-- ============================================================
-- SROIQ classical extension: full soundness, completeness deferred.
-- ============================================================
#print axioms SROIQ.satC_sound
#print axioms SROIQ.satC_of_alchoq

-- ============================================================
-- Tena-Cucala ALCHOIQ+ context-structure calculus
-- (DPhil thesis, Oxford 2019, Chapters 5-6).
-- Headline soundness + completeness results.
-- ============================================================
#print axioms ALCHOIQContext.step_sound
#print axioms ALCHOIQContext.deriv_sound
#print axioms ALCHOIQContext.completeness

end ELKSDD
