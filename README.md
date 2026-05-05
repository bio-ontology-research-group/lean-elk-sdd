# elk-sdd

Reusable Lean 4 formalisations for **EL ontology reasoning (ELK)** and
**Sentential Decision Diagrams (SDDs)** with structural weighted model
counting and Shannon-expansion compile correctness.

Lean 4 only, no Mathlib. Verifiable axiom dependencies via the
included `Audit` module.

## What's inside

| Module | Content |
|---|---|
| `ELKSDD.MiniEL` | Atomic-subsumption fragment of EL with **fully constructive** ELK soundness and completeness — `el0_sound` and `el0_complete` use **zero axioms**. |
| `ELKSDD.EL`     | Full conjunction + existential fragment of EL: ⊓, ⊤, ⊥, ∃R.C. ELK rules R₀, R_⊤, R_⊑, R⁻_⊓, R⁺_⊓, R_⊥, R⁺_∃, R_⊥-∃ encoded as inductive `Sat`. Soundness end-to-end. Completeness via canonical (term) model with role extension. Cyclic-ontology counterexample showing the necessity of the side condition on R⁺_∃. |
| `ELKSDD.SDD`    | BDD-style SDDs generic over the atom type. Recursive Shannon-path semantics, structural WMC with `wmcCost_eq_size` (linear-time WMC), Shannon-expansion compile from CNF, and `compile_correct` end-to-end. |
| `ELKSDD.Util`   | List-length lemmas for nested `flatMap`/`map` patterns; triangular numbers (`K(K-1)/2`). |
| `ELKSDD.Audit`  | `#print axioms` block listing every theorem's exact axiom dependencies. |

## Axiom hygiene

`lake build ELKSDD.Audit` reports for every theorem the axioms its
proof depends on. The full list of axioms used anywhere in the
library is exactly:

* `propext` — Lean foundation (propositional extensionality)
* `Classical.choice` — Lean foundation (classical reasoning, used
  by canonical-model completeness and by the noncomputable
  Shannon-expansion compile)
* `Quot.sound` — Lean foundation (quotient soundness)

There are **no admitted prior-work axioms**, no `sorry`, no
`Mathlib`. The MiniEL fragment uses **none of the above**: its
soundness and completeness are fully constructive.

## Building

Requires Lean 4 (toolchain `leanprover/lean4:v4.30.0-rc2`,
auto-installed by `lake`).

```bash
lake build              # build the whole library
lake build ELKSDD.Audit # build & print axiom dependencies
```

## Quick examples

**MiniEL:** prove `O = { 0 ⊑ 1, 1 ⊑ 2 } ⊨ 0 ⊑ 2` constructively.

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

-- Atoms are just `Nat` here; you can use any type.
example (Γ : List (Clause Nat)) (M : Assignment Nat) :
    model (compile Γ) M ↔ satisfiesAll M Γ :=
  compile_correct Γ M
```

## Mathematical content

### EL / ELK

The EL family of description logics underpins the OWL 2 EL profile,
used heavily in the bio-ontology community (SNOMED CT, GO, ChEBI,
the OBO Foundry stack). The ELK calculus is a polynomial-time
saturation procedure that decides EL entailment.

`ELKSDD.EL` formalises EL with conjunction (⊓), top, bottom, and
existential restrictions (∃R.C), and proves ELK sound and complete
relative to Tarskian semantics. The completeness proof builds the
standard term/canonical model in `CanonDom O := { C : Concept // ¬
Sat O C ⊥ }` with a role-extension construction that handles
inconsistent codomains via `exist_bot`.

`cyclicO_unbounded_sat` exhibits the classic cyclic-ontology
counterexample (`{ D₀ ⊑ ∃R.D₀ }`) producing infinitely many
distinct atoms `D₀ ⊑ ∃R.∃R…∃R.D₀` when the `∃R.E ∈ Sub(O)` side
condition on R⁺_∃ is dropped. `nestedExist_atom_inj` proves the
generated sequence is injective, so the would-be saturation is
genuinely Dedekind-infinite.

### SDDs and WMC

Sentential Decision Diagrams (SDDs) generalise Binary Decision
Diagrams. They support polynomial-time exact WMC, which is the
load-bearing inference primitive in many neuro-symbolic
architectures (Semantic Probabilistic Layers, Semantic Loss,
Probabilistic Logic Programming, etc.).

`ELKSDD.SDD` formalises the BDD subfragment of SDDs:

* `Tree` is the standard Shannon decision tree (`leaf Bool` +
  `branch atom hi lo`). BDD-form trees are decomposable and
  deterministic by construction, so the textbook recursive WMC
  formula is correct.
* `wmcCost_eq_size` proves the recursive WMC traversal cost equals
  the node count by structural induction — a genuine linear-time
  WMC bound, not a trivialised one.
* `compileWithCtx` performs Shannon-expansion compile from CNF by
  threading a partial-assignment context through the variable
  list. `compile_correct` proves the resulting BDD accepts exactly
  the satisfying assignments of the CNF, end-to-end, no admitted
  bridging axiom.

The compile is `noncomputable` because it uses
`Classical.propDecidable` to decide propositional satisfaction at
the leaves; this introduces `Classical.choice` as a Lean
foundation axiom, not a project-specific admit.

## Provenance

These modules were extracted from the Lean proof skeleton
accompanying the Moose paper (KAUST Bio-Ontology Research Group)
and generalised for reuse. The Moose paper's domain-specific
machinery (concept-instance Boolean atoms, Γ_EL/Φ_clos extractors,
ABox individuals) is not included here — only the parts that are
generic enough to plug into other projects.

## License

Apache 2.0. See [LICENSE](LICENSE).
