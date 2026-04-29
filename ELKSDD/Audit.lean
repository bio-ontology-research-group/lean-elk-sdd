/-
  ELKSDD/Audit.lean
  -----------------
  Print the axiom dependencies of every key theorem in ELKSDD.
  Each `#print axioms` line lists the axioms the proof actually
  uses; if anything beyond `propext`, `Classical.choice`,
  `Quot.sound` (the standard Lean foundation) appears, we have a
  leak.

  Build with `lake build ELKSDD.Audit` and read the `info:` lines.
-/

import ELKSDD.Util
import ELKSDD.MiniEL
import ELKSDD.EL
import ELKSDD.SDD

namespace ELKSDD

-- ============================================================
-- Util
-- ============================================================
#print axioms Util.length_flatMap_map_const
#print axioms Util.length_flatMap_const_length
#print axioms Util.triangle_double_eq
#print axioms Util.triangle_eq

-- ============================================================
-- MiniEL — atomic-subsumption fragment, fully zero-axiom proofs
-- ============================================================
-- Every theorem below should depend on NO axioms whatsoever.
#print axioms MiniEL.el0_sound
#print axioms MiniEL.el0_complete
#print axioms MiniEL.el0_correct
#print axioms MiniEL.example_sat
#print axioms MiniEL.example_entails

-- ============================================================
-- EL — conjunction + existential fragment with ELK soundness
--      and completeness end-to-end
-- ============================================================
#print axioms EL.sound
#print axioms EL.sound_atomSub
#print axioms EL.complete_atomSub
#print axioms EL.sound_disj
#print axioms EL.complete_disj
#print axioms EL.sound_unsat
#print axioms EL.complete_unsat
#print axioms EL.sound_link
#print axioms EL.complete_link
#print axioms EL.complete_via_canon
#print axioms EL.cyclicO_unbounded_sat
#print axioms EL.nestedExist_atom_inj
#print axioms EL.example_entails

-- ============================================================
-- SDD — BDD with linear-time WMC + Shannon-expansion compile
--       end-to-end correctness
-- ============================================================
#print axioms SDD.wmcCost_eq_size
#print axioms SDD.wmc_linear
#print axioms SDD.compileWithCtx_correct
#print axioms SDD.compile_correct

end ELKSDD
