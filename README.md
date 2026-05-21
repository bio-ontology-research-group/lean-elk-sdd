# elk-sdd

Lean 4 mechanisation of the **MOOSE** neuro-symbolic reasoner ---
from EL through full **SROIQ** (OWL 2 DL), with Sentential Decision
Diagrams, weighted model counting, the DISPONTE distribution
semantics, and a verified treatment of reasoning shortcuts under the
independence assumption.

Foundation-only axiom budget across the whole library: `propext`,
`Classical.choice`, `Quot.sound`. No `Mathlib` dependency in the
core; `Mathlib` is required only for the `Rat`-valued DISPONTE and
RSIA modules.

## What's inside

The library is organised in layers, each extending the previous
with new description-logic constructs.  All exposed theorems audit
to the three Lean foundation axioms above.

### Generic infrastructure

| Module | Content |
|---|---|
| `ELKSDD.Util`    | List-length lemmas (`flatMap`/`map` patterns), triangular numbers `K(K-1)/2`. |
| `ELKSDD.SDD`     | BDD-style Sentential Decision Diagrams generic over the atom type.  Shannon-path semantics, structural WMC with `wmcCost_eq_size` (linear-time WMC), Shannon-expansion compile from CNF, end-to-end `compile_correct`. |
| `ELKSDD.DISPONTE` | DISPONTE distribution semantics over EL+ axioms: world-sum, the WMC correspondence `wmc_compileSat_eq_disponteWMC`. |
| `ELKSDD.DISPONTERat` | `Rat`-valued DISPONTE — proper probability semantics on rationals.  `wmc_compileSat_eq_disponteWMC_rat`. |

### EL family (Horn fragment)

| Module | Content |
|---|---|
| `ELKSDD.MiniEL`  | Atomic-subsumption fragment of EL with **fully constructive** ELK soundness/completeness — `el0_sound`, `el0_complete` use **zero axioms**. |
| `ELKSDD.EL`      | Full conjunction + existential fragment ⊓, ⊤, ⊥, ∃R.C.  ELK rules R₀, R⊤, R⊑, R⁻⊓, R⁺⊓, R⊥, R⁺∃, R⊥-∃ as inductive `Sat`; soundness end-to-end; completeness via canonical (term) model with role extension.  `cyclicO_unbounded_sat` exhibits the classic `{ D₀ ⊑ ∃R.D₀ }` counterexample showing the necessity of the side condition on R⁺∃. |
| `ELKSDD.ELpp`    | EL++: range restrictions, role chains, concrete domains.  Full saturation calculus. |
| `ELKSDD.Normalize`, `ELKSDD.RangeNorm`, `ELKSDD.RangeNormConservativity` | Structural transformations that bring axioms into normal form; conservativity proofs. |
| `ELKSDD.Merging`, `ELKSDD.OWL2EL` | OWL 2 EL surface-syntax translation. |
| `ELKSDD.ELKBoundary` | Boundary results separating EL from EL++. |
| `ELKSDD.Saturation`, `ELKSDD.SCC`, `ELKSDD.SCCWorld`, `ELKSDD.SCCWMCUniform`, `ELKSDD.SCCNomLHS` | Strongly-connected-component decomposition of the saturation graph; factored WMC; nominal LHS handling. |
| `ELKSDD.SatComplexity`, `ELKSDD.SatFactorGeneral` | Polynomial complexity of EL+ saturation; general factorisation lemmas. |
| `ELKSDD.Stratified` | Stratified semantics. |
| `ELKSDD.Compilation`, `ELKSDD.CompilationWMC`, `ELKSDD.Complexity` | Shannon-expansion compile from saturated EL+ to SDD, with WMC correspondence and size bound. |
| `ELKSDD.MOOSE`   | Single-statement citation theorems: `moose_inference_correct` (sound SDD encoding + DISPONTE WMC marginal + bounded size), `sat_decision_polynomial`, `moose_pipeline_complete`. |

### ALC (Boolean closure)

| Module | Content |
|---|---|
| `ELKSDD.ALC`     | Syntax and Tarskian semantics for full Boolean ALC: negation `¬C`, disjunction `C ⊔ D`, universal restriction `∀R.C`.  De Morgan / role-axis duality lemmas; sound CB calculus `ALC.Sat` with `monoExist`/`monoUniv` monotonicity rules. |
| `ELKSDD.Completeness`, `ELKSDD.CompletenessExamples` | Lindenbaum maximal-consistent-type construction; canonical-model completeness `ALC.SatC`. |
| `ELKSDD.ALCComplexity` | Polynomial-degree grounding bounds for ALC. |

### ALCHOQ (nominals + qualified cardinality)

| Module | Content |
|---|---|
| `ELKSDD.ALCHOQ`  | Adds nominals `{a}` and qualified number restrictions `≥n R.C` / `≤n R.C`; cardinality predicates `atLeastCard`/`atMostCard`; filler-monotonicity rules `monoAtLeast` (covariant) and `monoAtMost` (contravariant).  `ALCHOQ.sat_sound` reports **zero axioms** (fully constructive). |
| `ELKSDD.ALCHOQCanonical`, `ELKSDD.ALCHOQCanonicalAudit`, `ELKSDD.ALCHOQCompleteness` | Canonical-model completeness for ALCHOQ. |
| `ELKSDD.ALCHOQSkolem` | Skolemisation for the cardinality / nominal expansions. |
| `ELKSDD.ALCHOIQContext` | The Tena Cucala context-structure calculus: all twelve inference rules of Tables 5.1 and 5.2 of Tena Cucala (2021), each with a per-rule soundness lemma. |

### SROIQ (full OWL 2 DL)

| Module | Content |
|---|---|
| `ELKSDD.SROIQ`   | RBox semantics for the full set of SROIQ role-axiom shapes: `RAxiom.incl` (R ⊑ S), `chain` (R₁ ∘ ⋯ ∘ Rₖ ⊑ S), `trans`, `sym`, `asym`, `refl`, `irrefl`, `inv`, `disj`.  One Tarskian soundness lemma per shape (`incl_sound`, `chain_two_sound`, `trans_sound`, …).  Role identities `trans_iff_chain` and `sym_iff_self_inverse` justify grounder reductions. |
| `ELKSDD.SROIQAudit` | Per-theorem axiom-dependency listing for the SROIQ layer. |
| `ELKSDD.SROIQCanonical`, `ELKSDD.SROIQCompleteness`, `ELKSDD.SROIQCompletenessSkeleton` | Canonical-model completeness for SROIQ; saturation closure under the role-axis rules. |
| `ELKSDD.SROIQSkolem`, `ELKSDD.SROIQSkolemCanonical` | Skolemisation. |
| `ELKSDD.SROIQContextBridge` | Bridge between the SROIQ proof skeleton and the Tena Cucala context-structure calculus in `ALCHOIQContext.lean`. |
| `ELKSDD.SROIQComplexity` | Polynomial-degree grounding bounds: each hook contributes at most `d^k` ground clauses where `d = |Δ|` and `k` is bounded by the maximum chain length, cardinality, or feature arity. |
| `ELKSDD.SROIQCompilationWMC` | The headline WMC correspondence for SROIQ: `wmc_compileSatC_eq_disponteWMCSatC` — the WMC of the verified compiled SDD equals the DISPONTE-style world-sum over the SROIQ saturation predicate.  Foundation-only. |
| `ELKSDD.SROIQPythonParity` | Soundness manifest for the Python calculus: each Python rule pairs with a Lean lemma. |

### RS-IA: reasoning shortcuts under the independence assumption

| Module | Content |
|---|---|
| `ELKSDD.RSIA`    | Formalises [van Krieken et al. (NeSy 2025)](https://arxiv.org/abs/2507.11357) for the SROIQ-WMC setting of MOOSE.  Both the **necessary** condition (Theorem 11) and the **positive complement** are mechanised. |

Headline theorems of `RSIA.lean`:

* `UCI_pos_iff_inCover` — the support of a factorised (UCI) distribution is exactly the cover of its deterministic part.
* `pMixZip_pos_iff_mem` — the support of a strictly-mixed RS mixture is exactly the confusion set `{α(c*) | α ∈ A}`.
* `weak_RS_aware_implicant` — **van Krieken et al. (2025), Theorem 11** for SROIQ: if a UCI distribution `UCI μ` weakly represents an RS mixture, the deterministic part of `μ` is an *implicant* of the constraint.
* `sroiq_RSIA_necessary` — instantiation to MOOSE's SROIQ saturation predicate `SatC R (selectedAxiomsS O ·) C D`.
* `UCI_delta_eq_indicator`, `RS_mixture_in_mixOfUCI` — the **positive complement**: every RS mixture is representable in the *mixture-of-UCI* family via deterministic-marginal cells.
* `sroiq_RSIA_sufficient` — SROIQ instantiation of the positive complement.

The pair `(sroiq_RSIA_necessary, sroiq_RSIA_sufficient)` jointly
characterise when independence-assumption WMC is RS-aware in SROIQ:
it cannot be in single-UCI, but always can be in the mixture-of-UCI
family.

### Audit

| Module | Content |
|---|---|
| `ELKSDD.Audit`   | `#print axioms` block listing every key theorem's exact axiom dependencies.  Build with `lake build ELKSDD.Audit`. |

## Axiom hygiene

Across the entire library, the axiom budget is exactly:

* `propext` --- Lean foundation (propositional extensionality)
* `Classical.choice` --- Lean foundation (classical reasoning, used
  by canonical-model completeness and by the noncomputable
  Shannon-expansion compile)
* `Quot.sound` --- Lean foundation (quotient soundness)

No `axiom` declarations, no `sorry`s, no admitted prior-work
results.

Two notable cases of *stronger* axiom hygiene:

* `ELKSDD.MiniEL` --- atomic-subsumption fragment.  `el0_sound`,
  `el0_complete`, and the supporting lemmas use **zero axioms**.
  Fully constructive.
* `ELKSDD.ALCHOQ` --- the saturation-soundness theorem
  `ALCHOQ.sat_sound` reports **zero axioms** despite the surface
  signature including nominals and qualified cardinality; the
  classical hidings are confined to the Lindenbaum completeness
  proof in `ALCHOQCompleteness.lean`.

## Building

Requires Lean 4 (toolchain `leanprover/lean4:v4.30.0-rc2`,
auto-installed by `lake`).  The non-Rat layers compile against Lean
4 core only; `DISPONTERat` and `RSIA` import `Mathlib` for
`Rat`-ordered-ring instances and `linarith`.

```bash
lake build              # build the whole library
lake build ELKSDD.RSIA  # build just the RS-IA module
lake build ELKSDD.Audit # build & print axiom dependencies
```

A quick sanity check:

```bash
echo 'import ELKSDD.RSIA
#print axioms ELKSDD.RSIA.sroiq_RSIA_necessary
#print axioms ELKSDD.RSIA.sroiq_RSIA_sufficient
' | lake env lean --stdin
```

should print only `[propext, Classical.choice, Quot.sound]` for
each.

## Quick examples

**MiniEL:** prove `O = { 0 ⊑ 1, 1 ⊑ 2 } ⊨ 0 ⊑ 2` constructively
(zero axioms).

```lean
import ELKSDD.MiniEL
open ELKSDD.MiniEL

example : Entails [(0, 1), (1, 2)] 0 2 :=
  el0_sound _ _ _ (Sat.trans 0 1 2
    (Sat.base 0 1 (by simp))
    (Sat.base 1 2 (by simp)))
```

**EL:** prove `O = { 0 ⊑ ∃R.1, 1 ⊑ 2 } ⊨ 0 ⊑ ∃R.2`.

```lean
import ELKSDD.EL
open ELKSDD.EL

example : Entails exampleOntology (.atom 0) (.exist 0 (.atom 2)) :=
  example_entails
```

**SDD:** compile a propositional CNF over atoms of any type to a
BDD and verify the compiled diagram preserves models.

```lean
import ELKSDD.SDD
open ELKSDD.SDD

example (Γ : List (Clause Nat)) (M : Assignment Nat) :
    model (compile Γ) M ↔ satisfiesAll M Γ :=
  compile_correct Γ M
```

**SROIQ-WMC correspondence:** the WMC of the compiled SDD equals
the DISPONTE world-sum for the SROIQ saturation predicate.

```lean
import ELKSDD.SROIQCompilationWMC
open ELKSDD.SROIQ.WMC

example (O : ELKSDD.ALCHOQ.Ontology) (R : ELKSDD.SROIQ.RBox)
    (C D : ELKSDD.ALCHOQ.Concept) (w : DispAtomS O → Bool → Nat) :
    SDD.wmc (compileSatC O R C D) w = disponteWMCSatC O R C D w :=
  wmc_compileSatC_eq_disponteWMCSatC O R C D w
```

**RS-IA positive complement:** every RS mixture is representable in
the mixture-of-UCI family.

```lean
import ELKSDD.RSIA
open ELKSDD.RSIA

example {k : Nat} (A : List (World k → World k)) (πs : List Rat)
    (cstar : World k) :
    ∀ M, pMixZip (List.zip A πs) cstar M =
         mixOfUCI (List.zip (A.map (fun α => deltaMarginal (α cstar))) πs) M :=
  RS_mixture_in_mixOfUCI A πs cstar
```

## Mathematical content

### EL / ELK

The EL family of description logics underpins the OWL 2 EL profile,
used heavily in the bio-ontology community (SNOMED CT, GO, ChEBI,
the OBO Foundry stack).  The ELK calculus is a polynomial-time
saturation procedure that decides EL entailment.

`ELKSDD.EL` formalises EL with conjunction (⊓), top, bottom, and
existential restrictions (∃R.C), and proves ELK sound and complete
relative to Tarskian semantics.  The completeness proof builds the
standard term/canonical model in `CanonDom O := { C : Concept // ¬
Sat O C ⊥ }` with a role-extension construction that handles
inconsistent codomains via `exist_bot`.

### SDDs and WMC

Sentential Decision Diagrams (SDDs) generalise Binary Decision
Diagrams.  They support polynomial-time exact WMC, which is the
load-bearing inference primitive in many neuro-symbolic
architectures (Semantic Probabilistic Layers, Semantic Loss,
Probabilistic Logic Programming).

`ELKSDD.SDD` formalises the BDD subfragment.  `wmcCost_eq_size`
proves the recursive WMC traversal cost equals the node count by
structural induction --- a genuine linear-time WMC bound.
`compileWithCtx` / `compile_correct` give Shannon-expansion compile
from CNF, end-to-end, with no admitted bridging axiom.

### SROIQ (OWL 2 DL)

SROIQ is the description logic underlying OWL 2 DL.  It extends
ALCHOQ with role chains, transitive / symmetric / asymmetric /
reflexive / irreflexive / inverse / disjoint roles, and the
universal role.  Each role-axiom shape is encoded in `ELKSDD.SROIQ`
as a constructor of the `RAxiom` inductive type with a per-shape
soundness lemma against Tarskian semantics; the role-identity
lemmas (`trans_iff_chain`, `sym_iff_self_inverse`) justify the
shape-reduction shortcuts the Python grounder takes at
ground-time.

The `SROIQCompilationWMC` module ports the EL-style DISPONTE
correspondence (`wmc_compileSat_eq_disponteWMC`) to the SROIQ
saturation predicate, producing the headline theorem
`wmc_compileSatC_eq_disponteWMCSatC` that links MOOSE's compiled
SDD to its declarative DISPONTE marginal.

### Reasoning shortcuts under the independence assumption

`ELKSDD.RSIA` formalises the analysis of [van Krieken et al.
(NeSy 2025)](https://arxiv.org/abs/2507.11357) for the SROIQ-WMC
setting.

* **Necessary side (Theorem 11).**  Under the universal
  conditionally independent (UCI) perception class `p_μ(c) = ∏ μ_i^{c_i}
  (1-μ_i)^{1-c_i}`, no UCI distribution can weakly represent an
  RS mixture whose support is not the cover of an implicant of the
  constraint.  For SROIQ queries `SatC R (selectedAxiomsS O ·) C D`,
  the implicants are exactly the *justifications* (minimal
  axiom subsets entailing `C ⊑ D`), which are decidable and finite.

* **Positive complement.**  Every RS mixture *is* representable in
  the mixture-of-UCI family `p_Just(c) = Σ_k π_k · UCI(μ_k)(c)` via
  deterministic-marginal cells (one per remapping).  This is the
  theoretical floor for any "single-trained-model RS-aware
  perception" architecture.

Together the two theorems jointly characterise the RS-awareness
gap: it is the gap between UCI and mixture-of-UCI, in a way that
respects exactly the symbolic structure SROIQ's saturation gives
us.  The MOOSE Python implementation of the mixture-of-UCI
architecture is `experiments/run_kinship_sroiq.py` and
`experiments/run_disjunction_sroiq.py` in the MOOSE repository.

## Provenance

These modules form the verification layer of the **MOOSE**
neuro-symbolic reasoner, the NeSy 2026 submission "NeSy over OWL 2
DL: compiling SROIQ ontologies to SDDs for differentiable WMC"
(KAUST Bio-Ontology Research Group).  The Python implementation
lives in the parent [MOOSE
repository](https://github.com/bio-ontology-research-group/moose);
this repository is its `proofs/lean-elk-sdd/` submodule.

Earlier KDD-style usage of the EL fragment alone is preserved in
`ELKSDD.MiniEL` / `ELKSDD.EL` / `ELKSDD.SDD`.

## License

Apache 2.0.  See [LICENSE](LICENSE).
