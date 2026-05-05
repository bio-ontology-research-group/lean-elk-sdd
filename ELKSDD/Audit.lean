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
import ELKSDD.ELpp
import ELKSDD.Normalize
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
-- ELpp — full EL_⊥^+ (= EL++ minus nominals/concrete domains):
--        EL with role inclusions R ⊑ S and role chains R₁ ∘ R₂ ⊑ S.
--        ELK 2014 calculus end-to-end (sound + complete via the
--        canonical-model construction of ELK 2014 §3.3).
-- Expected axiom surface: propext, Classical.choice, Quot.sound
-- (Lean foundation axioms only).
-- ============================================================
#print axioms ELpp.sound
#print axioms ELpp.canon_eval
#print axioms ELpp.canon_satisfies
#print axioms ELpp.complete_via_canon
#print axioms ELpp.sound_atomSub
#print axioms ELpp.complete_atomSub
#print axioms ELpp.correct_atomSub
#print axioms ELpp.exampleRH_sat
#print axioms ELpp.exampleRH_entails
#print axioms ELpp.exampleChain_sat
#print axioms ELpp.exampleChain_entails

-- ============================================================
-- Normalize — BBL 2005 normalization (Layer 2, in progress).
--             Currently formalised: NF7 (split conjunctive RHS,
--             no fresh names) and NF4 (drop ⊥ ⊑ D tautology),
--             both with full conservative-extension proofs.
--             NF1, NF2, NF3, NF5, NF6 (which introduce fresh
--             names) are pending — they require the model-
--             extension construction of BBL 2005 §3.1.
-- ============================================================
#print axioms Normalize.applyNF7_satisfies_orig
#print axioms Normalize.orig_satisfies_applyNF7
#print axioms Normalize.applyNF7_conservative
#print axioms Normalize.applyNF7_entails_iff
#print axioms Normalize.gci_bot_trivially_satisfied
#print axioms Normalize.applyNF4_satisfies_orig
#print axioms Normalize.orig_satisfies_applyNF4
#print axioms Normalize.applyNF4_conservative
#print axioms Normalize.applyNF4_entails_iff

-- ============================================================
-- SDD — BDD with linear-time WMC + Shannon-expansion compile
--       end-to-end correctness
-- ============================================================
#print axioms SDD.wmcCost_eq_size
#print axioms SDD.wmc_linear
#print axioms SDD.compileWithCtx_correct
#print axioms SDD.compile_correct

end ELKSDD
