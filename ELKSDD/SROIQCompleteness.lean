/-
  ELKSDD/SROIQCompleteness.lean
  -------------------------------
  SROIQ-direction classical extension + soundness, matched in style to
  `ELKSDD.ALCHOQCompleteness`.

  The propositional / role-axis ALC and ALCHOQ rules are inherited via
  `ofAlchoq`.  The new SROIQ-specific rules in this file are exactly the
  *consequence-based* role-axis rules that the Python grounder (in
  `moose/sroiq/grounding.py`) realises at ground time:

  * role inclusion `r ⊑ s`,
  * role chain `r₁ ∘ r₂ ⊑ s` (binary chain),
  * transitivity `Trans(r)`,
  * reflexivity `Refl(r)`,
  * universal role: `(U a b)` for every pair, captured at the concept
    level by `∃U.C ↔ ∃-something-implied-by-anything.C` — we encode the
    only consequence used downstream (``∃U.⊤`` is `⊤``).

  Rules that act as global *constraints* (asymmetric, irreflexive,
  disjoint, functional) do not produce consequence-rules on `Concept`s
  in the forward direction; they participate only in consistency checks
  and so do not appear in `SatC`.

  As with `ALCHOQCompleteness`, the headline SROIQ completeness theorem
  is left as an *explicit conjecture* (no `axiom`, no `sorry`).  The
  full canonical-model construction would require the role-chain
  closure machinery from Motik–Shearer–Horrocks JAIR 2009 lifted into
  Lean, which is multi-month formalisation effort.

  Every named theorem in this file depends only on the standard Lean
  foundational axioms (propext, Classical.choice, Quot.sound).
-/

import ELKSDD.ALCHOQCompleteness
import ELKSDD.SROIQ

namespace ELKSDD
namespace SROIQ

open ALCHOQ (Concept Ontology Interp)

/-- Concept-level encoding of a role-chain existential: for a chain
    ``r₁ · r₂ · … · rₖ`` and filler ``C``, this is the iterated
    existential
    ``∃r₁. (∃r₂. … (∃rₖ. C))``.  Empty chain ↦ ``C`` (degenerate). -/
def existChain : List Nat → Concept → Concept
  | [],       C => C
  | r :: rs,  C => .exist r (existChain rs C)

-- ============================================================
-- 1. SROIQ entailment: must respect both ontology and RBox.
-- ============================================================

/-- Entailment over ALCHOQ concept syntax, an ALCHOQ ontology, and a
    SROIQ RBox.  Every interpretation satisfying both the ontology and
    the RBox must respect the entailment. -/
def Entails (R : RBox) (O : Ontology) (C D : Concept) : Prop :=
  ∀ {α : Type} (I : Interp α),
    R.eval I → I.satisfies O →
    ∀ x, I.eval C x → I.eval D x

-- ============================================================
-- 2. Classical SROIQ calculus on top of `ALCHOQ.SatC`.
-- ============================================================

/-- Consequence-based classical SROIQ calculus.

    `ofAlchoq` lifts every ALCHOQ classical rule; the remaining
    constructors are the role-axis consequence rules made available by
    the RBox membership hypotheses.

    All membership hypotheses are explicit on the rule, so soundness is
    a straightforward case-split that quotes the corresponding RBox
    semantics. -/
inductive SatC (R : RBox) (O : Ontology) : Concept → Concept → Prop where
  | ofAlchoq        : ∀ {C D}, ALCHOQ.SatC O C D → SatC R O C D
  -- r ⊑ s  ⟹  ∃r.C ⊑ ∃s.C   and   ∀s.C ⊑ ∀r.C
  | roleIncl_exist  : ∀ {r s} (C : Concept),
      RAxiom.incl r s ∈ R → SatC R O (.exist r C) (.exist s C)
  | roleIncl_univ   : ∀ {r s} (C : Concept),
      RAxiom.incl r s ∈ R → SatC R O (.univ s C) (.univ r C)
  -- r₁ ∘ r₂ ⊑ s  ⟹  ∃r₁.∃r₂.C ⊑ ∃s.C
  | roleChain_two   : ∀ {r₁ r₂ s} (C : Concept),
      RAxiom.chain [r₁, r₂] s ∈ R →
      SatC R O (.exist r₁ (.exist r₂ C)) (.exist s C)
  -- General k-ary role chain  r₁ ∘ … ∘ rₖ ⊑ s  ⟹
  --   ∃r₁. ∃r₂. … ∃rₖ. C ⊑ ∃s.C
  -- (degenerate empty-chain case yields the reflexivity-like rule
  -- C ⊑ ∃s.C, sound because chain [] s ↔ ∀x, s(x,x).)
  | roleChain_n     : ∀ {rs s} (C : Concept),
      RAxiom.chain rs s ∈ R →
      SatC R O (existChain rs C) (.exist s C)
  -- Trans(r) ⟹  ∃r.∃r.C ⊑ ∃r.C
  | roleTrans_exist : ∀ {r} (C : Concept),
      RAxiom.trans r ∈ R →
      SatC R O (.exist r (.exist r C)) (.exist r C)
  -- Refl(r) ⟹  C ⊑ ∃r.C   and   ∀r.C ⊑ C
  | roleRefl_exist  : ∀ {r} (C : Concept),
      RAxiom.refl r ∈ R → SatC R O C (.exist r C)
  | roleRefl_univ   : ∀ {r} (C : Concept),
      RAxiom.refl r ∈ R → SatC R O (.univ r C) C
  -- Irrefl(r) ⟹  ∃r.{i} ⊓ {i} ⊑ ⊥   (the i-witness has r(i,i), contradicting irreflexivity)
  | roleIrrefl_self : ∀ {r} (i : Nat),
      RAxiom.irrefl r ∈ R →
      SatC R O (.conj (.exist r (.nom i)) (.nom i)) .bot
  -- Disj(r, s) ⟹  ∃r.{i} ⊓ ∃s.{i} ⊑ ⊥   (a single i-witness would have to be in both r and s)
  --   (Disjoint roles are stronger; for the concept-level fragment we
  --   record only the nominal-witness instance, which is what the
  --   grounder needs.)
  | roleDisj_self   : ∀ {r s} (i : Nat),
      RAxiom.disj r s ∈ R →
      SatC R O (.conj (.exist r (.nom i)) (.exist s (.nom i))) .bot
  -- Transitivity of the SatC relation.
  | trans : ∀ {C D E}, SatC R O C D → SatC R O D E → SatC R O C E

-- ============================================================
-- 3. Helpers used in the soundness proof.
-- ============================================================

private theorem alchoq_entails_of_satC
    {O : Ontology} {C D : Concept} (h : ALCHOQ.SatC O C D) :
    ALCHOQ.Entails O C D :=
  ALCHOQ.satC_sound O C D h

/-- An RBox-satisfying interpretation in particular respects each
    membership-conditioned semantic shape. -/
private theorem incl_of_mem {α} {I : Interp α} {R : RBox} {r s : Nat}
    (hR : R.eval I) (hMem : RAxiom.incl r s ∈ R) :
    ∀ x y, I.ext_role r x y → I.ext_role s x y :=
  hR _ hMem

private theorem chain_two_of_mem {α} {I : Interp α} {R : RBox}
    {r₁ r₂ s : Nat}
    (hR : R.eval I) (hMem : RAxiom.chain [r₁, r₂] s ∈ R) :
    ∀ x z, (∃ y, I.ext_role r₁ x y ∧ I.ext_role r₂ y z) →
            I.ext_role s x z := by
  have hAx : (RAxiom.chain [r₁, r₂] s).eval I := hR _ hMem
  exact fun x z ⟨y, h1, h2⟩ =>
    (chain_two_sound (I := I) r₁ r₂ s).mp hAx x y z h1 h2

/-- ``existChain rs C`` evaluated at ``x`` exposes a chain-of-witnesses
    terminating at a point where ``C`` holds.  By induction on ``rs``. -/
private theorem existChain_eval_iff
    {α} (I : Interp α) (rs : List Nat) (C : Concept) (x : α) :
    I.eval (existChain rs C) x ↔
      ∃ y, holdsAlong I rs x y ∧ I.eval C y := by
  induction rs generalizing x with
  | nil =>
      -- existChain [] C = C; holdsAlong I [] x y = (x = y)
      refine ⟨fun h => ⟨x, rfl, h⟩, ?_⟩
      rintro ⟨y, hxy, hCy⟩
      cases hxy
      exact hCy
  | cons r rs ih =>
      -- existChain (r :: rs) C = ∃r. existChain rs C
      constructor
      · rintro ⟨z, hxz, hrest⟩
        obtain ⟨y, hzy_chain, hCy⟩ := (ih (x := z)).mp hrest
        exact ⟨y, ⟨z, hxz, hzy_chain⟩, hCy⟩
      · rintro ⟨y, ⟨z, hxz, hzy_chain⟩, hCy⟩
        refine ⟨z, hxz, ?_⟩
        exact (ih (x := z)).mpr ⟨y, hzy_chain, hCy⟩

private theorem trans_of_mem {α} {I : Interp α} {R : RBox} {r : Nat}
    (hR : R.eval I) (hMem : RAxiom.trans r ∈ R) :
    ∀ x y z, I.ext_role r x y → I.ext_role r y z → I.ext_role r x z :=
  hR _ hMem

private theorem refl_of_mem {α} {I : Interp α} {R : RBox} {r : Nat}
    (hR : R.eval I) (hMem : RAxiom.refl r ∈ R) :
    ∀ x, I.ext_role r x x :=
  hR _ hMem

private theorem irrefl_of_mem {α} {I : Interp α} {R : RBox} {r : Nat}
    (hR : R.eval I) (hMem : RAxiom.irrefl r ∈ R) :
    ∀ x, ¬ I.ext_role r x x :=
  hR _ hMem

private theorem disj_of_mem {α} {I : Interp α} {R : RBox} {r s : Nat}
    (hR : R.eval I) (hMem : RAxiom.disj r s ∈ R) :
    ∀ x y, ¬ (I.ext_role r x y ∧ I.ext_role s x y) :=
  hR _ hMem

-- ============================================================
-- 4. Soundness of the classical SROIQ calculus.
-- ============================================================

theorem satC_sound (R : RBox) (O : Ontology) (C D : Concept)
    (h : SatC R O C D) : Entails R O C D := by
  intro α I hR hO x hC
  induction h generalizing x with
  | ofAlchoq hAlc =>
      exact alchoq_entails_of_satC hAlc I hO x hC
  | roleIncl_exist C hMem =>
      obtain ⟨y, hr, hCy⟩ := hC
      exact ⟨y, incl_of_mem hR hMem x y hr, hCy⟩
  | roleIncl_univ C hMem =>
      intro y hr
      exact hC y (incl_of_mem hR hMem x y hr)
  | roleChain_two C hMem =>
      obtain ⟨y, hxy, hy_rest⟩ := hC
      obtain ⟨z, hyz, hCz⟩ := hy_rest
      refine ⟨z, ?_, hCz⟩
      exact chain_two_of_mem hR hMem x z ⟨y, hxy, hyz⟩
  | @roleChain_n rs s C hMem =>
      have hAx : (RAxiom.chain rs s).eval I := hR _ hMem
      obtain ⟨y, hxy_chain, hCy⟩ := (existChain_eval_iff I rs C x).mp hC
      exact ⟨y, hAx x y hxy_chain, hCy⟩
  | roleTrans_exist C hMem =>
      obtain ⟨y, hxy, hyrest⟩ := hC
      obtain ⟨z, hyz, hCz⟩ := hyrest
      exact ⟨z, trans_of_mem hR hMem x y z hxy hyz, hCz⟩
  | roleRefl_exist C hMem =>
      exact ⟨x, refl_of_mem hR hMem x, hC⟩
  | roleRefl_univ C hMem =>
      exact hC x (refl_of_mem hR hMem x)
  | @roleIrrefl_self r i hMem =>
      obtain ⟨hex, hnom⟩ := hC
      obtain ⟨y, hr, hy_eq⟩ := hex
      have hx_eq_y : x = y := by
        rw [hnom, hy_eq]
      have hrxx : I.ext_role r x x := hx_eq_y ▸ hr
      exact irrefl_of_mem hR hMem x hrxx
  | @roleDisj_self r s i hMem =>
      obtain ⟨hexR, hexS⟩ := hC
      obtain ⟨y, hrxy, hy_eq⟩ := hexR
      obtain ⟨z, hsxz, hz_eq⟩ := hexS
      have hyz : y = z := by rw [hy_eq, hz_eq]
      have hrxz : I.ext_role r x z := hyz ▸ hrxy
      exact disj_of_mem hR hMem x z ⟨hrxz, hsxz⟩
  | trans hCD hDE ihCD ihDE =>
      exact ihDE x (ihCD x hC)

-- ============================================================
-- 5. Worked corollaries: each rule sound, plus their composition.
-- ============================================================

/-- The classical extension subsumes ALCHOQ classical: every ALCHOQ
    classical derivation is a SROIQ derivation. -/
theorem satC_of_alchoq {R : RBox} {O : Ontology} {C D : Concept}
    (h : ALCHOQ.SatC O C D) : SatC R O C D :=
  SatC.ofAlchoq h

/-- Worked example: with `r ⊑ s` and `Trans(r)`, the nested `∃r.∃r.C`
    contracts via transitivity, then weakens to `∃s.C`. -/
example (r s : Nat) (C : Concept)
    (hRBox : RBox) (h_incl : RAxiom.incl r s ∈ hRBox)
    (h_trans : RAxiom.trans r ∈ hRBox)
    (O : Ontology) :
    SatC hRBox O (.exist r (.exist r C)) (.exist s C) :=
  SatC.trans
    (SatC.roleTrans_exist C h_trans)
    (SatC.roleIncl_exist C h_incl)

/-- Reflexivity of `r` collapses `∀r.C` to `C`. -/
example (r : Nat) (C : Concept)
    (hRBox : RBox) (h_refl : RAxiom.refl r ∈ hRBox) (O : Ontology) :
    SatC hRBox O (.univ r C) C :=
  SatC.roleRefl_univ C h_refl

/-- General role chains: ``r₁ ∘ r₂ ∘ r₃ ⊑ s``  yields
    ``∃r₁.∃r₂.∃r₃.C ⊑ ∃s.C`` directly.  Demonstrates that
    ``roleChain_n`` subsumes ``roleChain_two``. -/
example (r₁ r₂ r₃ s : Nat) (C : Concept) (hRBox : RBox)
    (h_chain : RAxiom.chain [r₁, r₂, r₃] s ∈ hRBox)
    (O : Ontology) :
    SatC hRBox O
      (.exist r₁ (.exist r₂ (.exist r₃ C)))
      (.exist s C) := by
  have : (.exist r₁ (.exist r₂ (.exist r₃ C)) : Concept)
          = existChain [r₁, r₂, r₃] C := rfl
  rw [this]
  exact SatC.roleChain_n C h_chain

-- ============================================================
-- 6. Headline conjecture: SROIQ completeness.
--
-- Mechanising the SROIQ canonical model construction in Lean would
-- require:
--
--   1. cardinality-aware successor enumeration (already needed for
--      ALCHOQ; future work);
--   2. role-chain closure under the RBox, with Motik–Shearer–Horrocks
--      JAIR 2009 "regularity" assumption to ensure termination of
--      closure;
--   3. nominal-equality reasoning under the canonical quotient.
--
-- We state the conjecture with the same shape as the ALC and ALCHOQ
-- completeness theorems and leave its proof as future work.
-- ============================================================

/-- SROIQ completeness — *conjectured*.  Stated for downstream users
    who want to refer to it; intentionally not proved here.  See the
    ALC completeness theorem in `ELKSDD.Completeness` for the proved
    base case. -/
def sroiq_complete_conjecture : Prop :=
  ∀ (R : RBox) (O : Ontology) (C D : Concept),
    Entails R O C D → SatC R O C D

end SROIQ
end ELKSDD
