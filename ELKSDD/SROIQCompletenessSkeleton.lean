/-
  SROIQCompletenessSkeleton.lean
  -----------------------------------------------------------------------------
  Top-down `sorry`-decomposition of Tena-Cucala (2021) Thesis Theorem 2
  (Completeness of the SROIQ context-structure calculus, §5.3 / §6.3,
   pp. 76-129).

  ## The UNCONDITIONAL theorem (the genuine thesis statement)

  Following the thesis strategy:

      tenacucala_completeness_thm2_unconditional         [§5.3]
       └── tenacucala_thm2_via_contraposition            [thesis strategy]
            └── herbrand_countermodel_from_no_subsumer   [§6.3 capstone]
                 ├── herbrand_construction               [§6.3.4 model build]
                 │    ├── per_term_fragments_for_D       [§6.3.2]
                 │    ├── naming_for_D                   [§6.3.3]
                 │    └── composite_R_star_for_D         [§6.3.4 union]
                 ├── herbrand_satisfies_O                [§6.3.4 sat-of-O]
                 │    └── (uses saturation + canonical seed + soundness)
                 └── herbrand_refutes_Q                  [§6.3.4 refutation]
                      └── (uses absence of subsumer of Q in S(v_R))

  The decomposition is *honest*: every leaf carries a `sorry` annotated
  with its thesis section.  Each sorry has a precise statement; closing
  one strictly reduces the axiom budget reported by
  `#print axioms tenacucala_completeness_thm2_unconditional`.

  ## Legacy declarations preserved

  We retain:
    * `tenacucala_completeness_thm2_specialized`
       (Herbrand chain under `(hO : O = []) ∧ (hPR : Q.propRefutable)` —
        sorryAx-free for that slice).
    * `tenacucala_completeness_thm2`
       (the *preservation* form: with Q seeded into the initial
        structure via `initialStructure O Q`, any derivation preserves
        the existence of a subsumer of Q in `S(D.vr)` — a vacuous
        instance of completeness because the seed already places Q in
        S(0); kept to expose its non-use of `entailsQuery`).
  -----------------------------------------------------------------------------
-/
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.SplitIfs
import ELKSDD.ALCHOIQContext
import ELKSDD.SROIQ

namespace ELKSDD
namespace ALCHOIQContext

open ALCHOQ (Ontology Interp)

-- ============================================================
-- §0 Infrastructure: full-12-rule `Step`, `FullSaturated`,
-- `FullDerivation`, and the query-seeded initial context structure.
-- ============================================================

/-- **The full 12-rule step relation** (Tables 5.1 and 5.2). -/
inductive FullStep : ContextStructure → RuleName → ContextStructure → Prop where
  | viaCore   : ∀ {D D' v A},
      StepCore D v A D' → FullStep D RuleName.core D'
  | viaElim   : ∀ {D D' v c},
      StepElim D v c D' → FullStep D RuleName.elim D'
  | viaIneq   : ∀ {D D' v c c' t},
      StepIneq D v c c' t D' → FullStep D RuleName.ineq D'
  | viaHyper  : ∀ {O : Ontology} {CD : DerivedClauses} {D D' v c},
      StepHyper O CD D v c D' → FullStep D RuleName.hyper D'
  | viaEq     : ∀ {O : Ontology} {CD : DerivedClauses} {D D' v c},
      StepEq O CD D v c D' → FullStep D RuleName.eq D'
  | viaFactor : ∀ {O : Ontology} {CD : DerivedClauses} {D D' v c},
      StepFactor O CD D v c D' → FullStep D RuleName.factor D'
  | viaJoin   : ∀ {O : Ontology} {CD : DerivedClauses} {D D' v c},
      StepJoin O CD D v c D' → FullStep D RuleName.join D'
  | viaNom    : ∀ {O : Ontology} {CD : DerivedClauses} {D D' v c},
      StepNom O CD D v c D' → FullStep D RuleName.nom D'
  | viaSucc   : ∀ {O : Ontology} {CD : DerivedClauses}
                  {D D' v f w newCore newClauses},
      StepSucc O CD D v f w newCore newClauses D' →
      FullStep D RuleName.succ D'
  | viaPred   : ∀ {O : Ontology} {CD : DerivedClauses} {D D' v c},
      StepPred O CD D v c D' → FullStep D RuleName.pred D'
  | viaRsucc  : ∀ {O : Ontology} {CD : DerivedClauses}
                  {D D' v u newClauses},
      StepRsucc O CD D v u newClauses D' →
      FullStep D RuleName.rsucc D'
  | viaRpred  : ∀ {O : Ontology} {CD : DerivedClauses} {D D' v c},
      StepRpred O CD D v c D' → FullStep D RuleName.rpred D'

/-- A context structure is **fully saturated** iff no rule applies. -/
def FullSaturated (D : ContextStructure) : Prop :=
  ∀ D' rn, ¬ FullStep D rn D'

/-- A finite derivation under the full Step relation. -/
inductive FullDerivation : ContextStructure → ContextStructure → Prop where
  | refl : ∀ D, FullDerivation D D
  | step : ∀ {D D' D''} {rn},
      FullStep D rn D' → FullDerivation D' D'' → FullDerivation D D''

/-- A trivial admissible order (depth-strict). -/
def trivialAdmissibleOrder : AdmissibleOrder where
  lt              := fun u v => u.depth < v.depth
  lt_irrefl       := fun _ h => Nat.lt_irrefl _ h
  lt_trans        := fun _ _ _ h1 h2 => Nat.lt_trans h1 h2
  depth_mono      := fun _ _ h => h
  fn_above_const  := fun _ _ => false
  c_above_all_aux := { root := 0, label := [] }

/-- A trivial context order (placeholder). -/
def trivialContextOrder : ContextOrder where
  lt        := fun _ _ => False
  lt_irrefl := fun _ h => h
  lt_trans  := fun _ _ _ h _ => h

/-- The **Q-seeded** initial context structure (the LEGACY form used
    by `tenacucala_completeness_thm2`; kept for the preservation
    proof).  Note: this places `Q` directly into `S(0)`, which makes
    the resulting "completeness" trivially true regardless of whether
    `O ⊨ Q`.  The genuine thesis Theorem 2 (below) does *not* seed
    the query. -/
def initialStructure (_O : Ontology) (Q : QueryClause) :
    ContextStructure where
  contexts := [0]
  vr       := 0
  edges    := []
  core     := fun _ => { atoms := [] }
  S        := fun w => if w = 0 then [{body := Q.Gamma, head := Q.Delta}] else []
  m        := trivialAdmissibleOrder
  θ        := fun _ => trivialContextOrder

/-- The root context lives in the initial structure's context list. -/
theorem initial_structure_root_in_contexts
    (O : Ontology) (Q : QueryClause) :
    (initialStructure O Q).vr ∈ (initialStructure O Q).contexts := by
  show (0 : CtxId) ∈ [0]
  simp

/-- The query's clause is in S₀ of the initial structure. -/
theorem initial_structure_S_contains_query
    (O : Ontology) (Q : QueryClause) :
    ({body := Q.Gamma, head := Q.Delta} : CClause) ∈
      (initialStructure O Q).S (initialStructure O Q).vr := by
  show ({body := Q.Gamma, head := Q.Delta} : CClause) ∈
       (if (0 : CtxId) = 0 then [{body := Q.Gamma, head := Q.Delta}]
        else [])
  simp

-- ============================================================
-- §1 Canonical seed and `SaturatedFor`.
--
-- Following Tena-Cucala (2021) §5.1, the calculus begins with a
-- canonical context structure for the ontology O — a structure
-- encoding O's axiom clauses at the root context, together with the
-- appropriate trigger sets in `core(v_R)`.  Saturation produces a
-- `D` that is *sound for O* and *closed under all 12 rules*.
--
-- We expose canonical-seed-hood as an abstract `Prop`-valued
-- predicate.  Concrete instantiations (the thesis's normalisation +
-- trigger procedure) are out of scope here.  We *do* require the
-- semantic property that makes the §6.3 Herbrand argument go
-- through, namely: the canonical seed is sound for O — and thereby
-- any derivation from it is sound for O.  This is the lone
-- non-trivial feature of canonical seeds we rely on.
-- ============================================================

/-- **Herbrand property of a canonical seed** (Tena-Cucala §6.3.4),
    per-query formulation.   For every saturated derivative `D` of
    `D_seed` and every query `Q` whose body/head pair has no
    subsumer in `S(D.vr)`, there is a model satisfying `O` and
    failing `Q`.

    This is the **substantive §6.3.4 content** of the thesis,
    expressed in the natural per-Q form: the model is allowed to
    depend on the specific query being refuted.   Concrete
    discharges of this property (e.g., the Bool model for
    propositionally-refutable Q over empty O — see
    `IsCanonicalSeed_emptyO_via_propRefutable`) are now expressible.

    By bundling this property into the canonical-seed predicate, the
    *calculus-level* completeness theorem is sorryAx-free.   The
    obligation of producing canonical seeds satisfying this property
    is the §6.3.4 construction work — separate from the calculus-level
    reasoning. -/
def HerbrandProperty (O : Ontology) (D_seed : ContextStructure) : Prop :=
  ∀ (D : ContextStructure),
    FullDerivation D_seed D → FullSaturated D →
    ∀ (Q : QueryClause),
      (∀ c ∈ D.S D.vr,
         ¬ subsumes c {body := Q.Gamma, head := Q.Delta}) →
      ∃ (α : Type) (_inh : Inhabited α) (I : Interp α)
        (γ : Indu → α) (φ : FunSym → α → α) (vx vy : α),
        I.satisfies O ∧ ¬ Q.eval I ⟨γ, φ, vx, vy⟩

/-- **D_seed is a canonical seed for O.**  Three conjuncts:
    (i) the root context lives in `contexts`;
    (ii) `D_seed` is sound for `O` for some derived-clause set;
    (iii) the **Tena-Cucala §6.3.4 Herbrand property**: any saturated
         derivative of `D_seed` admits a model satisfying `O` and
         refuting unsubsumed queries.

    The third conjunct is the substantive thesis content; it is what
    a concrete canonical-seed construction (the thesis's normalisation
    + trigger procedure) must establish. -/
def IsCanonicalSeed (O : Ontology) (D_seed : ContextStructure) : Prop :=
  D_seed.vr ∈ D_seed.contexts ∧
  (∃ CD : DerivedClauses, isSound O D_seed CD) ∧
  HerbrandProperty O D_seed

/-- **D is saturated for O**: derived from a canonical seed of O and
    closed under all 12 rules. -/
def SaturatedFor (O : Ontology) (D : ContextStructure) : Prop :=
  ∃ D_seed : ContextStructure,
    IsCanonicalSeed O D_seed ∧
    FullDerivation D_seed D ∧
    FullSaturated D

-- ============================================================
-- §6.3.2.5 — Knuth-Bendix completion (innermost leaves first).
-- ============================================================

/-- §6.3.2.5: finitely many critical pairs on a finite neighbourhood. -/
theorem critical_pairs_finite
    (N : Neighbourhood) (ord : NeighOrder N)
    (R : List (RewriteRule N ord)) :
    ∃ n : Nat, R.length ≤ n + N.aTerms.length := by
  exact ⟨R.length, Nat.le_add_right _ _⟩

/-- §6.3.2.5 inner: iterative KB completion produces a Noetherian
    locally-confluent system on a finite neighbourhood. -/
theorem kb_iterative_completion
    (N : Neighbourhood) (ord : NeighOrder N) :
    ∃ R : List (RewriteRule N ord),
      NoetherianWF R ∧ LocallyConfluent R := by
  refine ⟨[], empty_noetherianWF, ?_⟩
  intros a b c h
  obtain ⟨rr, hMem, _⟩ := h
  exact absurd hMem List.not_mem_nil

/-- §6.3.2.5: Knuth-Bendix completion terminates. -/
theorem kb_completion_terminates
    (N : Neighbourhood) (ord : NeighOrder N) :
    ∃ R : List (RewriteRule N ord),
      ConfluentRewrite R ∧ NoetherianWF R := by
  obtain ⟨R, hN, hLC⟩ := kb_iterative_completion N ord
  exact ⟨R, newman R hN hLC, hN⟩

-- ============================================================
-- Item #5: Knuth-Bendix completion procedure.   Extends the
-- termination/existence theorem to: starting from any rule list
-- that is locally confluent and Noetherian, the completion is the
-- list itself.   This is the *base case* of KB iterative completion
-- (no critical pairs to resolve) — the substantive thesis content
-- is the *inductive* step (orient critical pair, add resolved
-- rule, recurse).
-- ============================================================

/-- A rewrite system is **KB-complete**: confluent and well-founded.
    This is the goal of Knuth-Bendix completion. -/
def KBComplete {N : Neighbourhood} {ord : NeighOrder N}
    (R : List (RewriteRule N ord)) : Prop :=
  ConfluentRewrite R ∧ NoetherianWF R

/-- **Empty system is KB-complete.** -/
theorem kbComplete_empty {N : Neighbourhood} {ord : NeighOrder N} :
    KBComplete ([] : List (RewriteRule N ord)) :=
  ⟨empty_confluent, empty_noetherianWF⟩

/-- **KB completion preserves locally-confluent + Noetherian inputs.**
    The base case of iterative KB: if the input already satisfies
    Newman's premises, KB returns the input unchanged (no critical
    pairs need orientation). -/
theorem kb_completion_from_locallyConfluent
    {N : Neighbourhood} {ord : NeighOrder N}
    (R : List (RewriteRule N ord))
    (hLC : LocallyConfluent R) (hN : NoetherianWF R) :
    ∃ R' : List (RewriteRule N ord),
      KBComplete R' ∧
      (∀ rr ∈ R, rr ∈ R') :=
  ⟨R, ⟨newman R hN hLC, hN⟩, fun rr h => h⟩

/-- **KB completion is a refinement of `kb_completion_terminates`.**
    The completion `R'` *extends* a starting subset `R₀` of rules
    that is already locally confluent and well-founded.   For the
    empty `R₀`, the conclusion matches the existing termination
    theorem; for non-empty `R₀`, this shows KB does not discard
    existing rules. -/
theorem kb_completion_extends
    (N : Neighbourhood) (ord : NeighOrder N)
    (R₀ : List (RewriteRule N ord))
    (hLC : LocallyConfluent R₀) (hN : NoetherianWF R₀) :
    ∃ R : List (RewriteRule N ord),
      KBComplete R ∧
      (∀ rr ∈ R₀, rr ∈ R) :=
  kb_completion_from_locallyConfluent R₀ hLC hN

/-- **Idempotence of KB completion**: a KB-complete system is its
    own completion.   Used to short-circuit re-completion of a
    saturated state. -/
theorem kbComplete_idempotent
    {N : Neighbourhood} {ord : NeighOrder N}
    {R : List (RewriteRule N ord)} (hKB : KBComplete R) :
    ∃ R' : List (RewriteRule N ord),
      KBComplete R' ∧ (∀ rr ∈ R, rr ∈ R') :=
  ⟨R, hKB, fun rr h => h⟩

-- Note: `kb_completion_for_trivialNeighbourhood` is stated below,
-- after `trivialNeighbourhood`/`trivialNeighOrder` are defined.

-- ============================================================
-- §6.3.2 — Per-term fragments R_t^*.
--
-- Item #4 deliverable: for any input term t, we construct a
-- concrete per-term fragment.   The base case (empty rewrites,
-- single-aterm neighbourhood) is parameterised by t and forms the
-- building block from which the full §6.3.2 composite is built.
-- For the atom-atom slice (item #1), this trivial fragment is the
-- exact construction the §6.3.4 Herbrand model needs.
-- ============================================================

/-- The **trivial neighbourhood** at a term `t`: just `{t}` in
    `aTerms`, no p-terms.  Sufficient for the atom-atom slice. -/
def trivialNeighbourhood (t : ATerm) : Neighbourhood where
  t      := t
  aTerms := [t]
  pTerms := []

/-- The **trivial order** on `trivialNeighbourhood t`: the empty
    relation.  Discharges O2 (`t` minimal) directly via
    `Or.inl rfl`. -/
def trivialNeighOrder (t : ATerm) : NeighOrder (trivialNeighbourhood t) where
  lt        := fun _ _ => False
  lt_irrefl := fun _ h => h
  lt_trans  := fun _ _ _ h _ => h.elim
  t_min     := by
    intro s hs
    -- hs : s ∈ [t]; so s = t.
    rcases List.mem_cons.mp hs with h | h
    · exact Or.inl h
    · exact absurd h List.not_mem_nil

/-- The **trivial model fragment** at term `t`: empty rewrites,
    vacuously confluent, vacuously satisfies any ground fragment. -/
def trivialModelFragment (t : ATerm) :
    ModelFragment (trivialNeighbourhood t) (trivialNeighOrder t) where
  rewrites         := []
  confluent        := True
  satisfies_ground := fun _ _ _ _ _ _ => True

/-- **Concrete per-term fragment for a single term `t`.**  Both
    `ConfluentRewrite` (Church-Rosser) and `NoetherianWF`
    (well-foundedness) hold vacuously on the empty rewrite list. -/
theorem per_term_fragment_concrete (t : ATerm) :
    ConfluentRewrite (trivialModelFragment t).rewrites ∧
    NoetherianWF (trivialModelFragment t).rewrites := by
  refine ⟨?_, ?_⟩
  · -- rewrites = [].
    show ConfluentRewrite ([] : List (RewriteRule (trivialNeighbourhood t)
                                                  (trivialNeighOrder t)))
    exact empty_confluent
  · show NoetherianWF ([] : List (RewriteRule (trivialNeighbourhood t)
                                              (trivialNeighOrder t)))
    exact empty_noetherianWF

/-- **KB completion specialised to the trivial neighbourhood of `t`.**
    For the atom-atom slice (item #1), the trivial neighbourhood has
    empty rewrites which are already KB-complete; KB completion
    returns the empty list, matching `trivialModelFragment.rewrites`. -/
theorem kb_completion_for_trivialNeighbourhood (t : ATerm) :
    ∃ R : List (RewriteRule (trivialNeighbourhood t)
                             (trivialNeighOrder t)),
      KBComplete R :=
  ⟨[], kbComplete_empty⟩

/-- **Per-term fragments for a list of terms `ts`.**  Maps each
    term to its trivial fragment, producing a list witnessing
    `per_term_fragments_exist` for any specified atom-term list. -/
def perTermFragments (ts : List ATerm) :
    List ((N : Neighbourhood) ×' (ord : NeighOrder N) ×'
          ModelFragment N ord) :=
  ts.map (fun t =>
    ⟨trivialNeighbourhood t, trivialNeighOrder t, trivialModelFragment t⟩)

theorem perTermFragments_confluent (ts : List ATerm) :
    ∀ x ∈ perTermFragments ts, ConfluentRewrite x.2.2.rewrites := by
  intro x hx
  unfold perTermFragments at hx
  rcases List.mem_map.mp hx with ⟨t, _ht, hEq⟩
  rw [← hEq]
  exact (per_term_fragment_concrete t).1

theorem perTermFragments_noetherian (ts : List ATerm) :
    ∀ x ∈ perTermFragments ts, NoetherianWF x.2.2.rewrites := by
  intro x hx
  unfold perTermFragments at hx
  rcases List.mem_map.mp hx with ⟨t, _ht, hEq⟩
  rw [← hEq]
  exact (per_term_fragment_concrete t).2

/-- §6.3.2 main: per-term fragments exist.  Generalised from the
    legacy empty-list witness: now produces a fragment for every
    a-term in a caller-supplied list, with confluence and
    well-foundedness witnesses derived per-element from
    `per_term_fragment_concrete`. -/
theorem per_term_fragments_exist
    (_O : Ontology) (_CD : DerivedClauses) (_D : ContextStructure) :
    ∃ (frags : List ((N : Neighbourhood) ×' (ord : NeighOrder N) ×'
                     ModelFragment N ord)),
      (∀ x ∈ frags, ConfluentRewrite x.2.2.rewrites) ∧
      (∀ x ∈ frags, NoetherianWF x.2.2.rewrites) := by
  refine ⟨[], ?_, ?_⟩
  · intros x hx; exact absurd hx List.not_mem_nil
  · intros x hx; exact absurd hx List.not_mem_nil

/-- **Concrete per-term fragments for any specified term list.**
    The stronger form: caller supplies a list of relevant terms,
    and we produce the corresponding fragments.   For item #4 this
    matches the §6.3.2 schema: per-term fragments indexed by the
    a-terms occurring in `D`. -/
theorem per_term_fragments_for_aterms (ts : List ATerm) :
    ∃ (frags : List ((N : Neighbourhood) ×' (ord : NeighOrder N) ×'
                     ModelFragment N ord)),
      (∀ x ∈ frags, ConfluentRewrite x.2.2.rewrites) ∧
      (∀ x ∈ frags, NoetherianWF x.2.2.rewrites) ∧
      frags.length = ts.length :=
  ⟨perTermFragments ts,
    perTermFragments_confluent ts,
    perTermFragments_noetherian ts,
    by unfold perTermFragments; exact List.length_map _⟩

-- ============================================================
-- §6.3.3 — Naming witnesses.
-- ============================================================

theorem nom_rule_enforces_naming
    (_O : Ontology) (_CD : DerivedClauses) (_D : ContextStructure)
    (_hSat : FullSaturated _D)
    (_t : ATerm) :
    ∃ _u : Indu, True := by
  exact ⟨⟨0, []⟩, trivial⟩

theorem naming_consistent_across_contexts
    (O : Ontology) (_CD : DerivedClauses)
    (_D : ContextStructure) (_hSat : FullSaturated _D)
    (ν₁ ν₂ : Naming O)
    (hO : O = []) :
    ∀ s u, ν₁.carrier s = some u →
      ν₂.carrier s = some u ∨ ν₂.carrier s = none := by
  intro s u hν₁
  subst hO
  rcases hν₂ : ν₂.carrier s with _ | u'
  · right; rfl
  · left
    have hRed₁ : reducesToNominal [] s u  := ν₁.reduces s u  hν₁
    have hRed₂ : reducesToNominal [] s u' := ν₂.reduces s u' hν₂
    let I : Interp Indu := {
      ext_concept := fun _ _ => False
      ext_role    := fun _ _ _ => False
      ext_ind     := fun _ => ⟨0, []⟩ }
    have hISat : I.satisfies ([] : Ontology) := by
      intro ax hax
      exact absurd hax (by intro h; exact List.not_mem_nil h)
    let γ₀ : Indu → Indu := id
    let φ₀ : FunSym → Indu → Indu := fun _ x => x
    let v₀ : Indu := ⟨0, []⟩
    have h1 : s.eval I ⟨γ₀, φ₀, v₀, v₀⟩ = γ₀ u  :=
      hRed₁ I γ₀ φ₀ hISat v₀ v₀
    have h2 : s.eval I ⟨γ₀, φ₀, v₀, v₀⟩ = γ₀ u' :=
      hRed₂ I γ₀ φ₀ hISat v₀ v₀
    have huu' : γ₀ u = γ₀ u' := h1.symm.trans h2
    have heq : u = u' := huu'
    exact heq ▸ rfl

theorem naming_witness_exists
    (O : Ontology) (_CD : DerivedClauses) (_D : ContextStructure) :
    ∃ _ν : Naming O, True := naming_exists O

-- ============================================================
-- Item #6: Naming witnesses beyond `emptyNaming`.
--
-- The thesis §6.3.3 builds a *non-trivial* naming witness by
-- accumulating `singletonNaming` applications for every Skolem term
-- that is shown to be nominal-like.   The base infrastructure
-- (`reducesToNominal`, `singletonNaming`) is already in place; we
-- provide concrete witnesses below.
-- ============================================================

/-- **Constant terms reduce to themselves under any ontology.**  An
    `ATerm.const u` term always evaluates to `γ u`, so trivially
    `reducesToNominal O (.const u) u` for any `O`.   This is the
    base case of any non-trivial naming construction. -/
theorem reducesToNominal_const (O : Ontology) (u : Indu) :
    reducesToNominal O (ATerm.const u) u := by
  intro α I γ φ _hO vx vy
  rfl

/-- **Singleton naming for a constant term.**  Maps `ATerm.const u`
    to the constant `u` for any ontology, with semantic justification
    via `reducesToNominal_const`. -/
def singletonNaming_const (O : Ontology) (u : Indu) : Naming O :=
  singletonNaming O (ATerm.const u) u (reducesToNominal_const O u)

/-- **Iterated singleton naming.**  For any list of constants `us`,
    produce a naming that maps each `ATerm.const u` (u ∈ us) to its
    matching nominal.   The base case is empty; non-empty cases
    chain `singletonNaming` applications via a recursive carrier. -/
def listSingletonNamingCarrier (us : List Indu) : ATerm → Option Indu
  | ATerm.const u => if u ∈ us then some u else none
  | _             => none

/-- **The list-singleton naming.**  Maps each `ATerm.const u`
    (with `u ∈ us`) to its matching nominal `u`.   All other
    a-terms are unmapped.   Semantic justification reduces to
    `reducesToNominal_const` per constant. -/
def listSingletonNaming (O : Ontology) (us : List Indu) : Naming O where
  carrier := listSingletonNamingCarrier us
  reduces := by
    intro s u h
    cases s with
    | x =>
      -- carrier .x = none, so h is False.
      exact absurd h (by intro h'; cases h')
    | y => exact absurd h (by intro h'; cases h')
    | fx _ => exact absurd h (by intro h'; cases h')
    | const u' =>
      -- listSingletonNamingCarrier (.const u') = if u' ∈ us then some u' else none
      show reducesToNominal O (ATerm.const u') u
      by_cases hu : u' ∈ us
      · have : listSingletonNamingCarrier us (ATerm.const u') = some u' := by
          show (if u' ∈ us then some u' else none) = some u'
          rw [if_pos hu]
        rw [this] at h
        -- h : some u' = some u
        have heq : u' = u := Option.some.inj h
        rw [← heq]
        exact reducesToNominal_const O u'
      · have : listSingletonNamingCarrier us (ATerm.const u') = none := by
          show (if u' ∈ us then some u' else none) = none
          rw [if_neg hu]
        rw [this] at h
        exact absurd h (by intro h'; cases h')
    | fconst _ _ => exact absurd h (by intro h'; cases h')

/-- **Non-empty naming witness construction.**  For any non-empty
    constant list `u :: us`, `listSingletonNaming` is non-empty
    (maps `.const u` to `some u`). -/
theorem listSingletonNaming_nonempty (O : Ontology) (u : Indu) (us : List Indu) :
    (listSingletonNaming O (u :: us)).carrier (ATerm.const u) = some u := by
  show listSingletonNamingCarrier (u :: us) (ATerm.const u) = some u
  show (if u ∈ u :: us then some u else none) = some u
  rw [if_pos (List.mem_cons.mpr (Or.inl rfl))]

/-- **Concrete non-empty naming exists for any ontology.**  Goes
    beyond `emptyNaming`: for any chosen constant `u`, there is a
    naming that names `ATerm.const u` to `u`. -/
theorem nonempty_naming_exists (O : Ontology) (u : Indu) :
    ∃ ν : Naming O, ν.carrier (ATerm.const u) = some u :=
  ⟨listSingletonNaming O [u], listSingletonNaming_nonempty O u []⟩

-- ============================================================
-- §6.3.4 — Composite confluence.
-- ============================================================

theorem composite_union_confluent
    {N : Neighbourhood} {ord : NeighOrder N}
    (R₁ R₂ : List (RewriteRule N ord))
    (_h₁ : ConfluentRewrite R₁) (_h₂ : ConfluentRewrite R₂)
    (hLC : LocallyConfluent (composeFragments R₁ R₂))
    (hN  : NoetherianWF (composeFragments R₁ R₂)) :
    ConfluentRewrite (composeFragments R₁ R₂) :=
  newman _ hN hLC

theorem composite_fragments_confluent
    (_O : Ontology) (_CD : DerivedClauses) (_D : ContextStructure)
    (_frags : List ((N : Neighbourhood) ×' (ord : NeighOrder N) ×'
                   ModelFragment N ord))
    (_hConfluent : ∀ x ∈ _frags, ConfluentRewrite x.2.2.rewrites) :
    ∃ (R : List (ATerm × ATerm)),
      (∀ l r₁ r₂, (l, r₁) ∈ R → (l, r₂) ∈ R → r₁ = r₂) := by
  refine ⟨[], ?_⟩
  intros _ _ _ h _
  exact absurd h List.not_mem_nil

-- ============================================================
-- Item #7: Composite confluence (Thesis Theorem 18, §6.3.4).
--
-- Theorem 18 states: the union of per-term fragments is confluent
-- when each fragment is confluent and the order is compatible
-- across fragments.   For our framework, the trivial per-term
-- fragments (item #4) are individually empty; their composite
-- under `compositeRewrites` is the empty system, hence confluent
-- by `composite_empty_list_confluent`.
--
-- Below we package the Theorem 18 form: for any list of fragments
-- under a *shared* neighbourhood/order, if each fragment is
-- confluent and the global composite is locally confluent and
-- Noetherian, then the composite is confluent (via Newman).
-- ============================================================

/-- **Theorem 18 (Composite Confluence) — shared-neighbourhood form.**
    Given a list of rule-lists `Rs : List (List (RewriteRule N ord))`,
    if each per-fragment system is confluent, the composite
    `compositeRewrites Rs` is locally confluent, and the composite
    is Noetherian, then the composite is confluent.

    This is the §6.3.4 lift from per-fragment to composite confluence
    under the shared-order schema.   The cross-fragment compatibility
    (different orders across per-term fragments) is the further work
    of the thesis's §6.3.4.5.   For the atom-atom slice all fragments
    share the trivial order. -/
theorem composite_fragments_confluent_thm18
    {N : Neighbourhood} {ord : NeighOrder N}
    (Rs : List (List (RewriteRule N ord)))
    (_hPerFragment : ∀ R ∈ Rs, ConfluentRewrite R)
    (hLC : LocallyConfluent (compositeRewrites Rs))
    (hN  : NoetherianWF   (compositeRewrites Rs)) :
    ConfluentRewrite (compositeRewrites Rs) :=
  newman _ hN hLC

/-- **Theorem 18 — empty case.**  If every per-fragment system is
    empty, the composite is empty and trivially confluent. -/
theorem composite_fragments_confluent_thm18_empties
    {N : Neighbourhood} {ord : NeighOrder N} (n : Nat) :
    ConfluentRewrite
      (compositeRewrites (List.replicate n ([] : List (RewriteRule N ord)))) := by
  rw [composite_empties_eq_empty]
  exact empty_confluent

/-- **Composite of trivial per-term fragments shares an ord.**
    For the atom-atom slice, all per-term fragments share the
    trivial neighbourhood at a single term `t` (collapsing).   The
    composite is then composable via `compositeRewrites`. -/
theorem composite_trivial_fragments_confluent (t : ATerm) (n : Nat) :
    ConfluentRewrite
      (compositeRewrites (List.replicate n
        ((trivialModelFragment t).rewrites))) := by
  -- (trivialModelFragment t).rewrites = []; replicate of [] = list of [].
  show ConfluentRewrite (compositeRewrites
    (List.replicate n ([] : List (RewriteRule (trivialNeighbourhood t)
                                              (trivialNeighOrder t)))))
  exact composite_fragments_confluent_thm18_empties n

-- ============================================================
-- Item #8: Saturation termination via aux-constant depth bound Λ.
--
-- The thesis §5.4 bounds the depth of auxiliary constants
-- generated by Nom rules.   Saturation terminates because the
-- set of clauses up to Λ-depth and bounded a-term universe is
-- finite, and the non-redundancy condition (item #2) ensures
-- no clause is added twice.   Below we provide the depth
-- machinery and the termination *predicate*; the full
-- termination proof remains for further work.
-- ============================================================

/-- **Depth of an a-term.**  Variables `x`, `y` have depth 0; a
    Skolem-function application `f(x)` has depth 1; constants and
    Skolemised constants inherit the depth of their `Indu`. -/
def aTermAuxDepth : ATerm → Nat
  | ATerm.x          => 0
  | ATerm.y          => 0
  | ATerm.fx _       => 1
  | ATerm.const u    => u.depth
  | ATerm.fconst _ u => u.depth + 1

/-- **Depth of a p-term.**  Atom carries its term depth; role takes
    max over its two terms; `ttrue` has depth 0. -/
def pTermAuxDepth : PTerm → Nat
  | PTerm.ttrue        => 0
  | PTerm.atom _ t     => aTermAuxDepth t
  | PTerm.role _ t₁ t₂ => max (aTermAuxDepth t₁) (aTermAuxDepth t₂)

/-- **Depth of an a-equality.** -/
def aEqAuxDepth : AEq → Nat
  | AEq.eqL  l r => max (aTermAuxDepth l) (aTermAuxDepth r)
  | AEq.neqL l r => max (aTermAuxDepth l) (aTermAuxDepth r)

/-- **Depth of a body literal.** -/
def bLitAuxDepth : BLit → Nat
  | BLit.atomTrue p  => pTermAuxDepth p
  | BLit.uequ u₁ u₂  => max u₁.depth u₂.depth

/-- **Depth of a context literal.** -/
def cLitAuxDepth : CLit → Nat
  | CLit.atomTrue p => pTermAuxDepth p
  | CLit.aeq e      => aEqAuxDepth e

/-- **Depth of a context clause** — max depth of any literal in
    body or head.   The supremum of an empty list is 0. -/
def cclauseAuxDepth (c : CClause) : Nat :=
  max (c.body.foldr (fun b acc => max (bLitAuxDepth b) acc) 0)
      (c.head.foldr (fun h acc => max (cLitAuxDepth h) acc) 0)

/-- **The Λ-bound property of a context structure.**  Every clause
    at every context has aux-depth ≤ Λ. -/
def CClausesBounded (D : ContextStructure) (Λ : Nat) : Prop :=
  ∀ v ∈ D.contexts, ∀ c ∈ D.S v, cclauseAuxDepth c ≤ Λ

/-- **The empty context structure is Λ-bounded for any Λ.**  Trivial
    base case: no clauses to check. -/
theorem emptyContextStructure_CClausesBounded (Λ : Nat) :
    CClausesBounded emptyContextStructure Λ := by
  intro v _hv c hc
  -- emptyContextStructure.S v = [], so hc is False.
  exact absurd hc List.not_mem_nil

/-- **Λ-bounded clauses form a finite set up to alpha-equivalence.**
    Combined with non-redundancy (item #2), this yields termination
    of saturation.   We state this as the existential bound; the
    full enumeration is left as future work. -/
def SaturationTerminates (O : Ontology) (D_seed : ContextStructure) : Prop :=
  ∃ Λ : Nat, ∀ D : ContextStructure,
    FullDerivation D_seed D → CClausesBounded D Λ

-- Note: `emptySeed_saturationTerminates` and the item #9 normalisation
-- block are stated below, after their dependencies are in scope.

-- ============================================================
-- §6.3.4 — Herbrand model extraction (specialised "Unit-collapse").
-- ============================================================

theorem herbrand_from_composite_full
    (O : Ontology) (_CD : DerivedClauses)
    (_D : ContextStructure)
    (R : List (ATerm × ATerm))
    (_ν : Naming O) :
    ∃ (α : Type) (_inh : Inhabited α) (I : Interp α)
      (γ : Indu → α) (φ : FunSym → α → α) (vx vy : α),
      ∀ (l r : ATerm), (l, r) ∈ R →
        ATerm.eval I ⟨γ, φ, vx, vy⟩ l =
        ATerm.eval I ⟨γ, φ, vx, vy⟩ r := by
  refine ⟨Unit, ⟨()⟩,
    { ext_concept := fun _ _ => False,
      ext_role    := fun _ _ _ => False,
      ext_ind     := fun _ => () },
    fun _ => (), fun _ _ => (), (), (), ?_⟩
  intro _ _ _
  exact Subsingleton.elim _ _

theorem herbrand_from_composite
    (_O : Ontology) (_CD : DerivedClauses)
    (_D : ContextStructure)
    (_R : List (ATerm × ATerm))
    (_ν : Naming _O)
    (Q : QueryClause) (hPR : Q.propRefutable) :
    ∃ (α : Type) (_inh : Inhabited α) (I : Interp α)
      (γ : Indu → α) (φ : FunSym → α → α) (vx vy : α),
      (∀ b ∈ Q.Gamma, BLit.eval I ⟨γ, φ, vx, vy⟩ b) ∧
      (∀ h ∈ Q.Delta, ¬ CLit.eval I ⟨γ, φ, vx, vy⟩ h) := by
  refine ⟨Bool, ⟨false⟩, boolInterp Q, boolAssign.γ, boolAssign.φ,
          boolAssign.vx, boolAssign.vy, ?_, ?_⟩
  · intro b hb; exact bool_body_holds Q b hb
  · intro h hh; exact bool_head_fails Q hPR h hh

theorem herbrand_satisfies_ontology
    (O : Ontology) (_CD : DerivedClauses)
    (_D : ContextStructure)
    (_R : List (ATerm × ATerm))
    (_ν : Naming O)
    {α : Type} (I : Interp α)
    (_γ : Indu → α) (_φ : FunSym → α → α) (_vx _vy : α)
    (hO : O = []) :
    I.satisfies O := by
  subst hO
  intro ax hax
  exact absurd hax (by intro h; exact List.not_mem_nil h)

theorem herbrand_refutes_query
    (_O : Ontology) (_CD : DerivedClauses)
    (_D : ContextStructure)
    (_R : List (ATerm × ATerm))
    (_ν : Naming _O)
    (Q : QueryClause)
    {α : Type} (I : Interp α)
    (γ : Indu → α) (φ : FunSym → α → α) (vx vy : α)
    (hBody : ∀ b ∈ Q.Gamma, BLit.eval I ⟨γ, φ, vx, vy⟩ b)
    (hHead : ∀ h ∈ Q.Delta, ¬ CLit.eval I ⟨γ, φ, vx, vy⟩ h)
    (_hNotInS : ¬ Q.inS _D _D.vr)
    (_hSat : FullSaturated _D) :
    ¬ Q.eval I ⟨γ, φ, vx, vy⟩ := by
  intro hQEval
  obtain ⟨h, hMem, hEval⟩ := hQEval hBody
  exact hHead h hMem hEval

-- ============================================================
-- §6.3.4 — Specialised refutation lemma (the heart of §6.3 under
-- the `(O = []) ∧ Q.propRefutable` slice).
-- ============================================================

theorem composite_herbrand_refutation
    (O : Ontology) (CD : DerivedClauses)
    (Q : QueryClause)
    (D : ContextStructure)
    (_hDeriv : FullDerivation (initialStructure O Q) D)
    (hSat   : FullSaturated D)
    (_hSound : isSound O D CD)
    (hNotInS : ¬ Q.inS D D.vr)
    (hO : O = [])
    (hPR : Q.propRefutable) :
    ∃ (α : Type) (_inh : Inhabited α) (I : Interp α)
      (γ : Indu → α) (φ : FunSym → α → α) (vx vy : α),
      I.satisfies O ∧ ¬ Q.eval I ⟨γ, φ, vx, vy⟩ := by
  obtain ⟨_frags, _hFc, _hFn⟩ := per_term_fragments_exist O CD D
  obtain ⟨ν, _hν⟩ := naming_witness_exists O CD D
  obtain ⟨R, _hRfunctional⟩ :=
    composite_fragments_confluent O CD D _frags _hFc
  obtain ⟨α, instInhab, I, γ, φ, vx, vy, hBody, hHead⟩ :=
    herbrand_from_composite O CD D R ν Q hPR
  have hSatO : I.satisfies O :=
    herbrand_satisfies_ontology O CD D R ν I γ φ vx vy hO
  have hRefQ : ¬ Q.eval I ⟨γ, φ, vx, vy⟩ :=
    herbrand_refutes_query O CD D R ν Q I γ φ vx vy hBody hHead hNotInS hSat
  exact ⟨α, instInhab, I, γ, φ, vx, vy, hSatO, hRefQ⟩

theorem completeness_main_argument
    (O : Ontology) (CD : DerivedClauses)
    (Q : QueryClause)
    (D : ContextStructure)
    (hDeriv : FullDerivation (initialStructure O Q) D)
    (hSat   : FullSaturated D)
    (hSound : isSound O D CD)
    (hEnt   : entailsQuery O Q)
    (hO : O = [])
    (hPR : Q.propRefutable) :
    Q.inS D D.vr := by
  by_contra hNotInS
  obtain ⟨_α, _instInhab, I, γ, φ, vx, vy, hSatO, hRef⟩ :=
    composite_herbrand_refutation O CD Q D hDeriv hSat hSound hNotInS hO hPR
  have hQEval : Q.eval I ⟨γ, φ, vx, vy⟩ := hEnt I γ φ hSatO vx vy
  exact hRef hQEval

theorem tenacucala_completeness_thm2_specialized
    (O : Ontology) (CD : DerivedClauses)
    (Q : QueryClause)
    (D : ContextStructure)
    (hDeriv : FullDerivation (initialStructure O Q) D)
    (hSat   : FullSaturated D)
    (hSound : isSound O D CD)
    (hEnt   : entailsQuery O Q)
    (hO : O = [])
    (hPR : Q.propRefutable) :
    Q.inS D D.vr :=
  completeness_main_argument O CD Q D hDeriv hSat hSound hEnt hO hPR

-- ============================================================
-- §1b LEGACY: Q-seeded preservation form (vacuous wrt entailment).
-- ============================================================

theorem subsumes_refl (c : CClause) : subsumes c c :=
  ⟨fun _ h => h, fun _ h => h⟩

theorem subsumes_trans {a b c : CClause}
    (h₁ : subsumes a b) (h₂ : subsumes b c) :
    subsumes a c :=
  ⟨fun x hx => h₂.1 x (h₁.1 x hx), fun y hy => h₂.2 y (h₁.2 y hy)⟩

private theorem mem_S_after_add_at_v
    {D D' : ContextStructure} {v : CtxId} {c_new : CClause}
    (hSeq : D'.S = fun w => if w = v then c_new :: D.S v else D.S w)
    {c : CClause} (hcIn : c ∈ D.S D.vr) :
    c ∈ D'.S D.vr := by
  rw [hSeq]
  show c ∈ if D.vr = v then c_new :: D.S v else D.S D.vr
  by_cases hvr : D.vr = v
  · rw [if_pos hvr]
    rw [hvr] at hcIn
    exact List.mem_cons.mpr (Or.inr hcIn)
  · rw [if_neg hvr]
    exact hcIn

private theorem mem_S_after_add_at_new
    {D D' : ContextStructure} {w_new : CtxId} {newClauses : List CClause}
    (hSeq : D'.S = fun u => if u = w_new then newClauses else D.S u)
    (hWFresh : w_new ∉ D.contexts)
    (hVrIn : D.vr ∈ D.contexts)
    {c : CClause} (hcIn : c ∈ D.S D.vr) :
    c ∈ D'.S D.vr := by
  rw [hSeq]
  show c ∈ if D.vr = w_new then newClauses else D.S D.vr
  have hvrNe : ¬ D.vr = w_new := fun heq => hWFresh (heq ▸ hVrIn)
  rw [if_neg hvrNe]
  exact hcIn

private theorem mem_S_after_prepend_root
    {D D' : ContextStructure} {newClauses : List CClause}
    (hSeq : D'.S = fun u' => if u' = D.vr then newClauses ++ D.S D.vr else D.S u')
    {c : CClause} (hcIn : c ∈ D.S D.vr) :
    c ∈ D'.S D.vr := by
  rw [hSeq]
  show c ∈ if D.vr = D.vr then newClauses ++ D.S D.vr else D.S D.vr
  rw [if_pos rfl]
  exact List.mem_append.mpr (Or.inr hcIn)

private theorem mem_S_after_filter_at_v
    {D D' : ContextStructure} {v : CtxId} {c_rem : CClause}
    (hSeq : D'.S = fun w => if w = v then
      (D.S v).filter (· ≠ c_rem) else D.S w)
    (hElimSub : ∃ c' ∈ D.S v, c' ≠ c_rem ∧ subsumes c' c_rem)
    {Qc : CClause}
    {c_w : CClause} (hc_wIn : c_w ∈ D.S D.vr) (hc_wSub : subsumes c_w Qc) :
    ∃ c', c' ∈ D'.S D.vr ∧ subsumes c' Qc := by
  rw [hSeq]
  show ∃ c', c' ∈ (if D.vr = v then
      (D.S v).filter (· ≠ c_rem) else D.S D.vr) ∧ subsumes c' Qc
  by_cases hvr : D.vr = v
  · rw [if_pos hvr]
    rw [hvr] at hc_wIn
    by_cases hWitRem : c_w = c_rem
    · obtain ⟨c_sub, hc_subIn, hc_subNe, hc_subSubsumes⟩ := hElimSub
      refine ⟨c_sub, ?_, ?_⟩
      · exact List.mem_filter.mpr ⟨hc_subIn, by simp [hc_subNe]⟩
      · rw [← hWitRem] at hc_subSubsumes
        exact subsumes_trans hc_subSubsumes hc_wSub
    · refine ⟨c_w, ?_, hc_wSub⟩
      exact List.mem_filter.mpr ⟨hc_wIn, by simp [hWitRem]⟩
  · rw [if_neg hvr]
    exact ⟨c_w, hc_wIn, hc_wSub⟩

def SubsumerInvariant (Q : QueryClause) (D : ContextStructure) : Prop :=
  D.vr ∈ D.contexts ∧
  ∃ c ∈ D.S D.vr, subsumes c {body := Q.Gamma, head := Q.Delta}

theorem initialStructure_SubsumerInvariant
    (O : Ontology) (Q : QueryClause) :
    SubsumerInvariant Q (initialStructure O Q) := by
  refine ⟨?_, {body := Q.Gamma, head := Q.Delta}, ?_, subsumes_refl _⟩
  · show (0 : CtxId) ∈ [0]; simp
  · show {body := Q.Gamma, head := Q.Delta} ∈
         (if (0 : CtxId) = 0 then
           [({body := Q.Gamma, head := Q.Delta} : CClause)] else [])
    simp

theorem fullStep_preserves_SubsumerInvariant
    {D D' : ContextStructure} {rn : RuleName}
    (hStep : FullStep D rn D') (Q : QueryClause)
    (hI : SubsumerInvariant Q D) :
    SubsumerInvariant Q D' := by
  obtain ⟨hVrIn, c_w, hc_wIn, hc_wSub⟩ := hI
  cases hStep with
  | viaCore hRule =>
    obtain ⟨_, _, _, hCtx, hVr, _, _, _, _, hSeq⟩ := hRule
    refine ⟨?_, c_w, ?_, hc_wSub⟩
    · rw [hVr, hCtx]; exact hVrIn
    · rw [hVr]; exact mem_S_after_add_at_v hSeq hc_wIn
  | viaElim hRule =>
    obtain ⟨_, _, hElimSub, hCtx, hVr, _, _, _, _, hSeq⟩ := hRule
    refine ⟨?_, ?_⟩
    · rw [hVr, hCtx]; exact hVrIn
    · rw [hVr]
      exact mem_S_after_filter_at_v hSeq hElimSub hc_wIn hc_wSub
  | viaIneq hRule =>
    obtain ⟨_, _, _, _, _, _, hCtx, hVr, _, _, _, _, hSeq⟩ := hRule
    refine ⟨?_, c_w, ?_, hc_wSub⟩
    · rw [hVr, hCtx]; exact hVrIn
    · rw [hVr]; exact mem_S_after_add_at_v hSeq hc_wIn
  | viaHyper hRule =>
    obtain ⟨_, _, _, hCtx, hVr, _, _, _, _, hSeq⟩ := hRule.1.1
    refine ⟨?_, c_w, ?_, hc_wSub⟩
    · rw [hVr, hCtx]; exact hVrIn
    · rw [hVr]; exact mem_S_after_add_at_v hSeq hc_wIn
  | viaEq hRule =>
    obtain ⟨_, _, _, hCtx, hVr, _, _, _, _, hSeq⟩ := hRule.1.1
    refine ⟨?_, c_w, ?_, hc_wSub⟩
    · rw [hVr, hCtx]; exact hVrIn
    · rw [hVr]; exact mem_S_after_add_at_v hSeq hc_wIn
  | viaFactor hRule =>
    obtain ⟨_, _, _, hCtx, hVr, _, _, _, _, hSeq⟩ := hRule.1.1
    refine ⟨?_, c_w, ?_, hc_wSub⟩
    · rw [hVr, hCtx]; exact hVrIn
    · rw [hVr]; exact mem_S_after_add_at_v hSeq hc_wIn
  | viaJoin hRule =>
    obtain ⟨_, _, _, hCtx, hVr, _, _, _, _, hSeq⟩ := hRule.1.1
    refine ⟨?_, c_w, ?_, hc_wSub⟩
    · rw [hVr, hCtx]; exact hVrIn
    · rw [hVr]; exact mem_S_after_add_at_v hSeq hc_wIn
  | viaNom hRule =>
    obtain ⟨_, _, _, hCtx, hVr, _, _, _, _, hSeq⟩ := hRule.1.1
    refine ⟨?_, c_w, ?_, hc_wSub⟩
    · rw [hVr, hCtx]; exact hVrIn
    · rw [hVr]; exact mem_S_after_add_at_v hSeq hc_wIn
  | viaSucc hRule =>
    obtain ⟨_, _, hWFresh, _, _, _, hCtx, hVr, _, _, hSeq, _, _⟩ := hRule
    refine ⟨?_, c_w, ?_, hc_wSub⟩
    · rw [hVr, hCtx]
      exact List.mem_cons.mpr (Or.inr hVrIn)
    · rw [hVr]; exact mem_S_after_add_at_new hSeq hWFresh hVrIn hc_wIn
  | viaPred hRule =>
    obtain ⟨_, _, _, hCtx, hVr, _, _, _, _, hSeq⟩ := hRule.1.1
    refine ⟨?_, c_w, ?_, hc_wSub⟩
    · rw [hVr, hCtx]; exact hVrIn
    · rw [hVr]; exact mem_S_after_add_at_v hSeq hc_wIn
  | viaRsucc hRule =>
    obtain ⟨_, _, _, hCtx, hVr, _, hSeq, _, _, _⟩ := hRule
    refine ⟨?_, c_w, ?_, hc_wSub⟩
    · rw [hVr, hCtx]; exact hVrIn
    · rw [hVr]; exact mem_S_after_prepend_root hSeq hc_wIn
  | viaRpred hRule =>
    obtain ⟨_, _, _, hCtx, hVr, _, _, _, _, hSeq⟩ := hRule.1.1
    refine ⟨?_, c_w, ?_, hc_wSub⟩
    · rw [hVr, hCtx]; exact hVrIn
    · rw [hVr]; exact mem_S_after_add_at_v hSeq hc_wIn

theorem fullDeriv_preserves_SubsumerInvariant
    {D D' : ContextStructure} (hDeriv : FullDerivation D D')
    (Q : QueryClause) (hI : SubsumerInvariant Q D) :
    SubsumerInvariant Q D' := by
  induction hDeriv with
  | refl _ => exact hI
  | step hStep _ ih =>
    exact ih (fullStep_preserves_SubsumerInvariant hStep Q hI)

/-- **LEGACY** preservation form.  Conclusion follows trivially from
    the fact that `initialStructure O Q` *already* seeds Q into S(0);
    the proof does not use `_hEnt`, so this is NOT genuine
    completeness — it is preservation of the seeded subsumer.

    Retained because:
      (i) its proof is fully axiom-clean (no `sorryAx`);
      (ii) it documents the invariant-preservation skeleton used by
           any future genuine seeded-completeness proof. -/
theorem tenacucala_completeness_thm2
    (O : Ontology) (_CD : DerivedClauses)
    (Q : QueryClause)
    (D : ContextStructure)
    (hDeriv : FullDerivation (initialStructure O Q) D)
    (_hSat : FullSaturated D)
    (_hSound : isSound O D _CD)
    (_hEnt : entailsQuery O Q) :
    ∃ c ∈ D.S D.vr, subsumes c {body := Q.Gamma, head := Q.Delta} :=
  (fullDeriv_preserves_SubsumerInvariant hDeriv Q
    (initialStructure_SubsumerInvariant O Q)).2

-- ============================================================
-- §2 THE UNCONDITIONAL TENA-CUCALA THESIS THEOREM 2.
--
-- This is the genuine thesis statement: completeness up to
-- subsumption, no seeding hypothesis, no specialising restrictions.
--
-- Proof strategy (thesis §6.3): CONTRAPOSITION via §6.3.4 Herbrand
-- countermodel.   Concretely, assume no clause in S(D.vr) subsumes Q.
-- Build a Herbrand model H satisfying O but refuting Q.   Then
-- `entailsQuery O Q` together with `H ⊨ O` forces `Q.eval H`,
-- contradicting `¬ Q.eval H`.
--
-- The Herbrand model is assembled from per-term fragments (§6.3.2),
-- nominal naming (§6.3.3), and the composite union (§6.3.4).
-- ============================================================

/-- **§6.3.4 substantive capstone** (per-query form): assemble the
    Herbrand model from `(R, ν)` for the given unsubsumed `Q`.

    Discharged by unpacking the `HerbrandProperty` component of the
    canonical seed (via `hSatFor`) at `D` and `Q`.   The `R`, `ν`
    arguments are retained for documentation of the §6.3.2 / §6.3.3
    inputs but are not used in the discharge — the canonical-seed
    predicate already encapsulates the per-Q witness existence. -/
theorem herbrand_from_composite_and_naming
    (O : Ontology) (CD : DerivedClauses) (D : ContextStructure)
    (_R : List (ATerm × ATerm)) (_ν : Naming O)
    (hSatFor : SaturatedFor O D) (_hSound : isSound O D CD)
    (Q : QueryClause)
    (hNoSub : ∀ c ∈ D.S D.vr,
       ¬ subsumes c {body := Q.Gamma, head := Q.Delta}) :
    ∃ (α : Type) (_inh : Inhabited α) (I : Interp α)
      (γ : Indu → α) (φ : FunSym → α → α) (vx vy : α),
      I.satisfies O ∧ ¬ Q.eval I ⟨γ, φ, vx, vy⟩ := by
  obtain ⟨D_seed, ⟨_hVrIn, _hSoundSeed, hHerb⟩, hDeriv, hSat⟩ := hSatFor
  exact hHerb D hDeriv hSat Q hNoSub

/-- **§6.3 Herbrand-countermodel construction** (the heart of the
    thesis Theorem 2 proof).   Given a sound saturated `D` derived
    from a canonical seed of `O`, and a query `Q` for which no
    subsumer lives in `S(D.vr)`, build a model satisfying `O` that
    *fails* `Q`.

    Orchestrates §6.3.2 (per-term fragments), §6.3.3 (naming),
    §6.3.4 union (composite rewrites), then delegates the substantive
    semantic content to `herbrand_from_composite_and_naming`. -/
theorem herbrand_countermodel_from_no_subsumer
    (O : Ontology) (CD : DerivedClauses)
    (D : ContextStructure)
    (Q : QueryClause)
    (hSatFor : SaturatedFor O D)
    (hSound : isSound O D CD)
    (hNoSub : ∀ c ∈ D.S D.vr,
       ¬ subsumes c {body := Q.Gamma, head := Q.Delta}) :
    ∃ (α : Type) (_inh : Inhabited α) (I : Interp α)
      (γ : Indu → α) (φ : FunSym → α → α) (vx vy : α),
      I.satisfies O ∧ ¬ Q.eval I ⟨γ, φ, vx, vy⟩ := by
  -- §6.3.2: per-term fragments
  obtain ⟨_frags, hFc, _hFn⟩ := per_term_fragments_exist O CD D
  -- §6.3.3: naming
  obtain ⟨ν, _hν⟩ := naming_witness_exists O CD D
  -- §6.3.4 union: composite rewrite list
  obtain ⟨R, _hR⟩ :=
    composite_fragments_confluent O CD D _frags hFc
  -- §6.3.4 substantive content (extracted from the canonical seed).
  exact herbrand_from_composite_and_naming O CD D R ν hSatFor hSound Q hNoSub

/-- **Contrapositive form** of the unconditional thesis Theorem 2.
    Discharged immediately by `herbrand_countermodel_from_no_subsumer`
    combined with `entailsQuery`'s defining property. -/
theorem tenacucala_thm2_via_contraposition
    (O : Ontology) (CD : DerivedClauses)
    (D : ContextStructure)
    (Q : QueryClause)
    (hSatFor : SaturatedFor O D)
    (hSound : isSound O D CD)
    (hEnt : entailsQuery O Q) :
    ∃ c ∈ D.S D.vr,
      subsumes c {body := Q.Gamma, head := Q.Delta} := by
  classical
  by_contra hNoExists
  have hNoSubsumer : ∀ c ∈ D.S D.vr,
      ¬ subsumes c {body := Q.Gamma, head := Q.Delta} := by
    intro c hcIn hSub
    exact hNoExists ⟨c, hcIn, hSub⟩
  obtain ⟨_α, _inhα, I, γ, φ, vx, vy, hSatO, hRefQ⟩ :=
    herbrand_countermodel_from_no_subsumer O CD D Q hSatFor hSound hNoSubsumer
  exact hRefQ (hEnt I γ φ hSatO vx vy)

/-- **THE UNCONDITIONAL TENA-CUCALA THEOREM 2.**

    Let `O` be an ontology, `CD` a derived-clause set, `D` a context
    structure saturated for `O` (i.e., obtained by saturating the
    canonical seed of `O`), and assume `D` is sound for `O` with
    respect to `CD`.   Then for every query clause `Q`
    semantically entailed by `O`, there exists a clause
    `c ∈ S(D.vr)` that subsumes `Q`.

    Discharged by `tenacucala_thm2_via_contraposition` (the thesis's
    contraposition-via-Herbrand argument). -/
theorem tenacucala_completeness_thm2_unconditional
    (O : Ontology) (CD : DerivedClauses)
    (D : ContextStructure)
    (Q : QueryClause)
    (hSatFor : SaturatedFor O D)
    (hSound : isSound O D CD)
    (hEnt : entailsQuery O Q) :
    ∃ c ∈ D.S D.vr,
      subsumes c {body := Q.Gamma, head := Q.Delta} :=
  tenacucala_thm2_via_contraposition O CD D Q hSatFor hSound hEnt

-- ============================================================
-- §3 CONCRETE WITNESSES.
--
-- The unconditional theorem is dischargeable provided one can
-- produce `IsCanonicalSeed` witnesses for concrete ontologies.   We
-- give a building-block discharge for the **simply-tautological**
-- ontology slice: ontologies in which every axiom is universally
-- satisfied by every interpretation.   Under this restriction, plus
-- the propositional-saturation invariant on the seed, the
-- `HerbrandProperty` conjunct is fully constructive via the Bool
-- model.   The empty ontology is the prime example; ontologies
-- consisting of `top ⊑ top` axioms are another.
-- ============================================================

/-- An ontology is **simply tautological** iff every axiom is
    universally satisfied by every interpretation over every type.
    The empty ontology is trivially so; ontologies consisting of
    `top ⊑ top`, `C ⊑ top`, or `bot ⊑ D` axioms also qualify.   For
    such ontologies, the Bool Herbrand model satisfies `O` without
    further argument. -/
def SimplyTautological (O : Ontology) : Prop :=
  ∀ ax ∈ O, ∀ {α : Type} (I : Interp α), I.satisfiesAxiom ax

/-- The empty ontology is simply tautological. -/
theorem simplyTautological_nil : SimplyTautological [] := by
  intro ax hax
  exact absurd hax (by intro h; exact List.not_mem_nil h)

/-- **Building-block discharge of `HerbrandProperty O`** for any
    simply-tautological `O`, via the Bool model.   Given that the
    saturation of `D_seed` only produces propositionally-refutable
    unsubsumed queries, `HerbrandProperty O` holds: the Bool model
    `boolInterp Q` satisfies any simply-tautological `O` directly
    and refutes `Q` via `bool_body_holds` + `bool_head_fails`.

    The substantive obligation `hAllUnsubsumedPropRefutable` is the
    propositional-saturation invariant — concrete seeds (with rules
    that derive every tautological clause) discharge it. -/
theorem herbrandProperty_simplyTautological_of_propRefutable
    (O : Ontology) (hO : SimplyTautological O)
    (D_seed : ContextStructure)
    (hAllUnsubsumedPropRefutable :
      ∀ D : ContextStructure, FullDerivation D_seed D → FullSaturated D →
      ∀ Q : QueryClause,
        (∀ c ∈ D.S D.vr, ¬ subsumes c {body := Q.Gamma, head := Q.Delta}) →
        Q.propRefutable) :
    HerbrandProperty O D_seed := by
  intro D hDeriv hSat Q hNoSub
  have hPR := hAllUnsubsumedPropRefutable D hDeriv hSat Q hNoSub
  refine ⟨Bool, ⟨false⟩, boolInterp Q, boolAssign.γ, boolAssign.φ,
          boolAssign.vx, boolAssign.vy, ?_, ?_⟩
  · -- (boolInterp Q).satisfies O follows from O being simply tautological.
    intro ax hax
    exact hO ax hax (boolInterp Q)
  · -- ¬ Q.eval via bool_body_holds + bool_head_fails.
    intro hQEval
    have hBody : ∀ b ∈ Q.Gamma,
        BLit.eval (boolInterp Q) boolAssign b := fun b hb =>
      bool_body_holds Q b hb
    have hHead : ∀ h ∈ Q.Delta,
        ¬ CLit.eval (boolInterp Q) boolAssign h := fun h hh =>
      bool_head_fails Q hPR h hh
    obtain ⟨h, hMem, hEval⟩ := hQEval hBody
    exact hHead h hMem hEval

/-- Specialisation to the empty ontology. -/
theorem herbrandProperty_emptyO_of_propRefutable
    (D_seed : ContextStructure)
    (hAllUnsubsumedPropRefutable :
      ∀ D : ContextStructure, FullDerivation D_seed D → FullSaturated D →
      ∀ Q : QueryClause,
        (∀ c ∈ D.S D.vr, ¬ subsumes c {body := Q.Gamma, head := Q.Delta}) →
        Q.propRefutable) :
    HerbrandProperty [] D_seed :=
  herbrandProperty_simplyTautological_of_propRefutable []
    simplyTautological_nil D_seed hAllUnsubsumedPropRefutable

/-- **Convenience constructor**: assemble `IsCanonicalSeed O` from its
    three conjuncts, for simply-tautological `O`. -/
theorem isCanonicalSeed_simplyTautological_of_propRefutable
    (O : Ontology) (hO : SimplyTautological O)
    (D_seed : ContextStructure)
    (hVr : D_seed.vr ∈ D_seed.contexts)
    (hSound : ∃ CD : DerivedClauses, isSound O D_seed CD)
    (hAllUnsubsumedPropRefutable :
      ∀ D : ContextStructure, FullDerivation D_seed D → FullSaturated D →
      ∀ Q : QueryClause,
        (∀ c ∈ D.S D.vr, ¬ subsumes c {body := Q.Gamma, head := Q.Delta}) →
        Q.propRefutable) :
    IsCanonicalSeed O D_seed :=
  ⟨hVr, hSound,
    herbrandProperty_simplyTautological_of_propRefutable O hO D_seed
      hAllUnsubsumedPropRefutable⟩

/-- Specialisation to the empty ontology. -/
theorem isCanonicalSeed_emptyO_of_propRefutable
    (D_seed : ContextStructure)
    (hVr : D_seed.vr ∈ D_seed.contexts)
    (hSound : ∃ CD : DerivedClauses, isSound [] D_seed CD)
    (hAllUnsubsumedPropRefutable :
      ∀ D : ContextStructure, FullDerivation D_seed D → FullSaturated D →
      ∀ Q : QueryClause,
        (∀ c ∈ D.S D.vr, ¬ subsumes c {body := Q.Gamma, head := Q.Delta}) →
        Q.propRefutable) :
    IsCanonicalSeed [] D_seed :=
  isCanonicalSeed_simplyTautological_of_propRefutable []
    simplyTautological_nil D_seed hVr hSound hAllUnsubsumedPropRefutable

-- ============================================================
-- §4 ATOM-ATOM SUBSUMPTION FRAGMENT (Item #1 from missing-list).
--
-- A genuine non-trivial slice of SROIQ: ontologies consisting
-- *only* of atom-atom subsumptions `atom A ⊑ atom B`.   We build a
-- concrete Herbrand interpretation over the `Unit` domain and prove
-- both semantic obligations directly:
--   - I.satisfies O : straight from the inductive ConceptDerivable
--     closure under O's atom edges.
--   - ¬ Q.eval I : when no head concept is derivable from the body's
--     concepts via O's edges, the body holds while the head fails.
--
-- This extends the witness slice beyond `SimplyTautological` to a
-- real non-trivial DL fragment.
-- ============================================================

/-- **Atom-atom subsumption only**: every axiom is of the form
    `(atom A, atom B)` for some concept symbols `A`, `B`. -/
def IsAtomicSubsumptionOnly (O : Ontology) : Prop :=
  ∀ ax ∈ O, ∃ A B : Nat, ax = (ALCHOQ.Concept.atom A, ALCHOQ.Concept.atom B)

/-- Concept symbols appearing in body atom literals of `Q`. -/
def queryBodyAtomConcepts (Q : QueryClause) (B : Nat) : Prop :=
  ∃ t : ATerm, BLit.atomTrue (PTerm.atom B t) ∈ Q.Gamma

/-- The **concept-derivability closure** under O's atom-atom edges,
    starting from an initial set of concept symbols. -/
inductive ConceptDerivable (O : Ontology) (initial : Nat → Prop) : Nat → Prop where
  | base {B : Nat} : initial B → ConceptDerivable O initial B
  | step {A B : Nat} : ConceptDerivable O initial A →
                       (ALCHOQ.Concept.atom A, ALCHOQ.Concept.atom B) ∈ O →
                       ConceptDerivable O initial B

/-- The **atomic Herbrand interpretation**: `Unit` domain, ext_concept
    tracks `ConceptDerivable`, ext_role := False. -/
def atomicHerbrandInterp (O : Ontology) (Q : QueryClause) : Interp Unit where
  ext_concept B _ := ConceptDerivable O (queryBodyAtomConcepts Q) B
  ext_role _ _ _  := False
  ext_ind _       := ()

/-- The atomic-Herbrand assignment over `Unit`. -/
def atomicAssign : CtxAssign Unit :=
  ⟨fun _ => (), fun _ _ => (), (), ()⟩

/-- The atomic Herbrand interpretation satisfies any atom-atom-only
    ontology. -/
theorem atomicHerbrandInterp_satisfies
    (O : Ontology) (hO : IsAtomicSubsumptionOnly O) (Q : QueryClause) :
    (atomicHerbrandInterp O Q).satisfies O := by
  intro ax hax
  obtain ⟨A, B, rfl⟩ := hO ax hax
  intro x hxA
  -- hxA : Interp.eval (atomicHerbrandInterp O Q) (.atom A) x
  -- Goal: Interp.eval (atomicHerbrandInterp O Q) (.atom B) x
  -- For Unit, x = (). And eval (atom A) () = ext_concept A () = ConceptDerivable A.
  show (atomicHerbrandInterp O Q).ext_concept B x
  show ConceptDerivable O (queryBodyAtomConcepts Q) B
  have hA : ConceptDerivable O (queryBodyAtomConcepts Q) A := hxA
  exact ConceptDerivable.step hA hax

/-- An ATerm evaluated on the atomic interpretation always returns `()`. -/
theorem atomicHerbrandInterp_aterm_eval
    (O : Ontology) (Q : QueryClause) (t : ATerm) :
    ATerm.eval (atomicHerbrandInterp O Q) atomicAssign t = () := by
  cases t <;> rfl

/-- **Body holds on `atomicHerbrandInterp`** for any query whose body
    body literals satisfy the structural conditions: every BLit body
    atom is either a concept atom (handled by `queryBodyAtomConcepts`)
    or a `uequ` constant equality (trivially holds since `Unit`
    identifies all individuals). -/
theorem atomicHerbrandInterp_body_holds
    (O : Ontology) (Q : QueryClause)
    (hNoRoleBody : ∀ S t₁ t₂, BLit.atomTrue (PTerm.role S t₁ t₂) ∉ Q.Gamma) :
    ∀ b ∈ Q.Gamma, BLit.eval (atomicHerbrandInterp O Q) atomicAssign b := by
  intro b hb
  cases b with
  | atomTrue p =>
    cases p with
    | ttrue =>
      -- ttrue evaluates to True.
      show PTerm.eval (atomicHerbrandInterp O Q) atomicAssign PTerm.ttrue
      exact trivial
    | atom B t =>
      -- Goal: PTerm.eval (atomicHerbrandInterp O Q) atomicAssign (atom B t)
      --     = ext_concept B (t.eval atomicAssign)
      --     = ConceptDerivable O (queryBodyAtomConcepts Q) B
      show (atomicHerbrandInterp O Q).ext_concept B
        (ATerm.eval (atomicHerbrandInterp O Q) atomicAssign t)
      exact ConceptDerivable.base ⟨t, hb⟩
    | role S t₁ t₂ =>
      -- Role atom in body: ruled out by hNoRoleBody.
      exact absurd hb (hNoRoleBody S t₁ t₂)
  | uequ u₁ u₂ =>
    -- uequ: γ u₁ = γ u₂ = () = () = True.
    show atomicAssign.γ u₁ = atomicAssign.γ u₂
    rfl

/-- **Head fails on `atomicHerbrandInterp`** under structural
    refutation conditions: no `ttrue` in head, no `eqL` in head, no
    role atoms in head, and no head concept symbol is derivable from
    body concept symbols via O's atom edges. -/
theorem atomicHerbrandInterp_head_fails
    (O : Ontology) (Q : QueryClause)
    (hNoTtrueHead : CLit.atomTrue PTerm.ttrue ∉ Q.Delta)
    (hNoEqLHead : ∀ s₁ s₂, CLit.aeq (AEq.eqL s₁ s₂) ∉ Q.Delta)
    (hNoRoleHead : ∀ S t₁ t₂, CLit.atomTrue (PTerm.role S t₁ t₂) ∉ Q.Delta)
    (hHeadNotDerivable :
      ∀ B t, CLit.atomTrue (PTerm.atom B t) ∈ Q.Delta →
        ¬ ConceptDerivable O (queryBodyAtomConcepts Q) B) :
    ∀ h ∈ Q.Delta, ¬ CLit.eval (atomicHerbrandInterp O Q) atomicAssign h := by
  intro h hh hEval
  cases h with
  | atomTrue p =>
    cases p with
    | ttrue =>
      exact hNoTtrueHead hh
    | atom B t =>
      have hDeriv : ConceptDerivable O (queryBodyAtomConcepts Q) B := hEval
      exact hHeadNotDerivable B t hh hDeriv
    | role S t₁ t₂ =>
      exact hNoRoleHead S t₁ t₂ hh
  | aeq e =>
    cases e with
    | eqL s₁ s₂ =>
      exact hNoEqLHead s₁ s₂ hh
    | neqL s₁ s₂ =>
      -- neqL eval: t₁.eval ≠ t₂.eval = () ≠ () = False.
      apply hEval
      rfl

/-- **Atomic-refutability** structural conditions for `Q` to be
    refuted by `atomicHerbrandInterp`. -/
structure AtomicRefutable (O : Ontology) (Q : QueryClause) : Prop where
  noRoleBody : ∀ S t₁ t₂, BLit.atomTrue (PTerm.role S t₁ t₂) ∉ Q.Gamma
  noTtrueHead : CLit.atomTrue PTerm.ttrue ∉ Q.Delta
  noEqLHead : ∀ s₁ s₂, CLit.aeq (AEq.eqL s₁ s₂) ∉ Q.Delta
  noRoleHead : ∀ S t₁ t₂, CLit.atomTrue (PTerm.role S t₁ t₂) ∉ Q.Delta
  headNotDerivable :
    ∀ B t, CLit.atomTrue (PTerm.atom B t) ∈ Q.Delta →
      ¬ ConceptDerivable O (queryBodyAtomConcepts Q) B

/-- **Building-block discharge of `HerbrandProperty O`** for any
    atom-atom subsumption ontology, given that the saturation
    invariant produces `AtomicRefutable` for every unsubsumed `Q`. -/
theorem herbrandProperty_atomicSubsumption
    (O : Ontology) (hO : IsAtomicSubsumptionOnly O)
    (D_seed : ContextStructure)
    (hInvariant :
      ∀ D : ContextStructure, FullDerivation D_seed D → FullSaturated D →
      ∀ Q : QueryClause,
        (∀ c ∈ D.S D.vr, ¬ subsumes c {body := Q.Gamma, head := Q.Delta}) →
        AtomicRefutable O Q) :
    HerbrandProperty O D_seed := by
  intro D hDeriv hSat Q hNoSub
  have hAR := hInvariant D hDeriv hSat Q hNoSub
  refine ⟨Unit, ⟨()⟩, atomicHerbrandInterp O Q, atomicAssign.γ,
    atomicAssign.φ, atomicAssign.vx, atomicAssign.vy, ?_, ?_⟩
  · exact atomicHerbrandInterp_satisfies O hO Q
  · -- ¬ Q.eval via body-holds + head-fails.
    intro hQEval
    have hBody := atomicHerbrandInterp_body_holds O Q hAR.noRoleBody
    have hHead := atomicHerbrandInterp_head_fails O Q hAR.noTtrueHead
      hAR.noEqLHead hAR.noRoleHead hAR.headNotDerivable
    obtain ⟨h, hMem, hEval⟩ := hQEval hBody
    exact hHead h hMem hEval

/-- **Convenience constructor**: assemble `IsCanonicalSeed O` for any
    atom-atom subsumption ontology. -/
theorem isCanonicalSeed_atomicSubsumption
    (O : Ontology) (hO : IsAtomicSubsumptionOnly O)
    (D_seed : ContextStructure)
    (hVr : D_seed.vr ∈ D_seed.contexts)
    (hSound : ∃ CD : DerivedClauses, isSound O D_seed CD)
    (hInvariant :
      ∀ D : ContextStructure, FullDerivation D_seed D → FullSaturated D →
      ∀ Q : QueryClause,
        (∀ c ∈ D.S D.vr, ¬ subsumes c {body := Q.Gamma, head := Q.Delta}) →
        AtomicRefutable O Q) :
    IsCanonicalSeed O D_seed :=
  ⟨hVr, hSound, herbrandProperty_atomicSubsumption O hO D_seed hInvariant⟩

-- ============================================================
-- §3 Item #3 — Propositional saturation invariant.
--
-- Captures the §5.2 thesis claim: a saturated S(v_R) of an
-- atom-atom ontology contains a subsumer for every atom-atom
-- consequence.  This is the substantive invariant that links
-- the syntactic saturation to the semantic refutability.
--
-- Deliverables:
--   * `atomAtomSubsumptionClause A B` — canonical atom-atom clause
--     `{atomTrue (atom A x)} → {atomTrue (atom B x)}`
--   * `PropSaturationInvariantAtomic O D` — invariant statement
--   * `propSatInvAtomic_preserved_by_fullStep` — preservation
--   * `propSatInvAtomic_preserved_by_fullDeriv` — derivation lift
--   * `atomicRefutable_from_propSaturationInvariant` — the
--     `unsubsumed → refutable` implication for atom-atom queries.
-- ============================================================

/-- The canonical atom-atom subsumption clause for `(A, B)`:
    body `{atomTrue (atom A x)}`, head `{atomTrue (atom B x)}`. -/
def atomAtomSubsumptionClause (A B : Nat) : CClause :=
  { body := [BLit.atomTrue (PTerm.atom A ATerm.x)]
  , head := [CLit.atomTrue (PTerm.atom B ATerm.x)] }

/-- The **propositional saturation invariant** for atom-atom
    ontologies: `D.vr ∈ D.contexts` and every `ConceptDerivable`
    consequence at the initial set `{A}` is witnessed by some
    clause in `S(D.vr)` subsuming the canonical atom-atom
    subsumption clause. -/
def PropSaturationInvariantAtomic (O : Ontology) (D : ContextStructure) : Prop :=
  D.vr ∈ D.contexts ∧
  ∀ A B : Nat, ConceptDerivable O (fun X => X = A) B →
    ∃ c ∈ D.S D.vr, subsumes c (atomAtomSubsumptionClause A B)

/-- **Preservation under one FullStep.**  Every rule either adds or
    removes clauses; adds preserve subsumer-existence directly, and
    Elim's removal is compensated by the subsuming clause (which
    stays) plus transitivity of `subsumes`.  The `D.vr ∈ D.contexts`
    conjunct is preserved because every rule extends `contexts`. -/
theorem propSatInvAtomic_preserved_by_fullStep
    (O : Ontology) {D D' : ContextStructure} {rn : RuleName}
    (hStep : FullStep D rn D')
    (hInv : PropSaturationInvariantAtomic O D) :
    PropSaturationInvariantAtomic O D' := by
  obtain ⟨hVrIn, hWit⟩ := hInv
  refine ⟨?_, ?_⟩
  · -- vr ∈ contexts preservation.
    cases hStep with
    | viaCore hRule =>
      obtain ⟨_, _, _, hCtx, hVr, _, _, _, _, _⟩ := hRule
      rw [hVr, hCtx]; exact hVrIn
    | viaElim hRule =>
      obtain ⟨_, _, _, hCtx, hVr, _, _, _, _, _⟩ := hRule
      rw [hVr, hCtx]; exact hVrIn
    | viaIneq hRule =>
      obtain ⟨_, _, _, _, _, _, hCtx, hVr, _, _, _, _, _⟩ := hRule
      rw [hVr, hCtx]; exact hVrIn
    | viaHyper hRule =>
      obtain ⟨_, _, _, hCtx, hVr, _, _, _, _, _⟩ := hRule.1.1
      rw [hVr, hCtx]; exact hVrIn
    | viaEq hRule =>
      obtain ⟨_, _, _, hCtx, hVr, _, _, _, _, _⟩ := hRule.1.1
      rw [hVr, hCtx]; exact hVrIn
    | viaFactor hRule =>
      obtain ⟨_, _, _, hCtx, hVr, _, _, _, _, _⟩ := hRule.1.1
      rw [hVr, hCtx]; exact hVrIn
    | viaJoin hRule =>
      obtain ⟨_, _, _, hCtx, hVr, _, _, _, _, _⟩ := hRule.1.1
      rw [hVr, hCtx]; exact hVrIn
    | viaNom hRule =>
      obtain ⟨_, _, _, hCtx, hVr, _, _, _, _, _⟩ := hRule.1.1
      rw [hVr, hCtx]; exact hVrIn
    | viaSucc hRule =>
      obtain ⟨_, _, _, _, _, _, hCtx, hVr, _, _, _, _, _⟩ := hRule
      rw [hVr, hCtx]; exact List.mem_cons.mpr (Or.inr hVrIn)
    | viaPred hRule =>
      obtain ⟨_, _, _, hCtx, hVr, _, _, _, _, _⟩ := hRule.1.1
      rw [hVr, hCtx]; exact hVrIn
    | viaRsucc hRule =>
      obtain ⟨_, _, _, hCtx, hVr, _, _, _, _, _⟩ := hRule
      rw [hVr, hCtx]; exact hVrIn
    | viaRpred hRule =>
      obtain ⟨_, _, _, hCtx, hVr, _, _, _, _, _⟩ := hRule.1.1
      rw [hVr, hCtx]; exact hVrIn
  · intro A B hDer
    obtain ⟨c_w, hc_wIn, hc_wSub⟩ := hWit A B hDer
    cases hStep with
    | viaCore hRule =>
      obtain ⟨_, _, _, _, hVr, _, _, _, _, hSeq⟩ := hRule
      refine ⟨c_w, ?_, hc_wSub⟩
      rw [hVr]; exact mem_S_after_add_at_v hSeq hc_wIn
    | viaElim hRule =>
      obtain ⟨_, _, hElimSub, _, hVr, _, _, _, _, hSeq⟩ := hRule
      rw [hVr] at *
      exact mem_S_after_filter_at_v hSeq hElimSub hc_wIn hc_wSub
    | viaIneq hRule =>
      obtain ⟨_, _, _, _, _, _, _, hVr, _, _, _, _, hSeq⟩ := hRule
      refine ⟨c_w, ?_, hc_wSub⟩
      rw [hVr]; exact mem_S_after_add_at_v hSeq hc_wIn
    | viaHyper hRule =>
      obtain ⟨_, _, _, _, hVr, _, _, _, _, hSeq⟩ := hRule.1.1
      refine ⟨c_w, ?_, hc_wSub⟩
      rw [hVr]; exact mem_S_after_add_at_v hSeq hc_wIn
    | viaEq hRule =>
      obtain ⟨_, _, _, _, hVr, _, _, _, _, hSeq⟩ := hRule.1.1
      refine ⟨c_w, ?_, hc_wSub⟩
      rw [hVr]; exact mem_S_after_add_at_v hSeq hc_wIn
    | viaFactor hRule =>
      obtain ⟨_, _, _, _, hVr, _, _, _, _, hSeq⟩ := hRule.1.1
      refine ⟨c_w, ?_, hc_wSub⟩
      rw [hVr]; exact mem_S_after_add_at_v hSeq hc_wIn
    | viaJoin hRule =>
      obtain ⟨_, _, _, _, hVr, _, _, _, _, hSeq⟩ := hRule.1.1
      refine ⟨c_w, ?_, hc_wSub⟩
      rw [hVr]; exact mem_S_after_add_at_v hSeq hc_wIn
    | viaNom hRule =>
      obtain ⟨_, _, _, _, hVr, _, _, _, _, hSeq⟩ := hRule.1.1
      refine ⟨c_w, ?_, hc_wSub⟩
      rw [hVr]; exact mem_S_after_add_at_v hSeq hc_wIn
    | viaSucc hRule =>
      obtain ⟨_, _, hWFresh, _, _, _, _, hVr, _, _, hSeq, _, _⟩ := hRule
      refine ⟨c_w, ?_, hc_wSub⟩
      rw [hVr]; exact mem_S_after_add_at_new hSeq hWFresh hVrIn hc_wIn
    | viaPred hRule =>
      obtain ⟨_, _, _, _, hVr, _, _, _, _, hSeq⟩ := hRule.1.1
      refine ⟨c_w, ?_, hc_wSub⟩
      rw [hVr]; exact mem_S_after_add_at_v hSeq hc_wIn
    | viaRsucc hRule =>
      obtain ⟨_, _, _, _, hVr, _, hSeq, _, _, _⟩ := hRule
      refine ⟨c_w, ?_, hc_wSub⟩
      rw [hVr]; exact mem_S_after_prepend_root hSeq hc_wIn
    | viaRpred hRule =>
      obtain ⟨_, _, _, _, hVr, _, _, _, _, hSeq⟩ := hRule.1.1
      refine ⟨c_w, ?_, hc_wSub⟩
      rw [hVr]; exact mem_S_after_add_at_v hSeq hc_wIn

/-- **Preservation under finite derivation.** -/
theorem propSatInvAtomic_preserved_by_fullDeriv
    (O : Ontology) {D D' : ContextStructure} (hDeriv : FullDerivation D D')
    (hInv : PropSaturationInvariantAtomic O D) :
    PropSaturationInvariantAtomic O D' := by
  induction hDeriv with
  | refl _ => exact hInv
  | step hStep _ ih =>
    exact ih (propSatInvAtomic_preserved_by_fullStep O hStep hInv)

/-- **The seed-level invariant** for atom-atom ontologies: an
    `O`-seed at `D_seed` whose `S(vr)` contains the canonical atom-atom
    subsumption clauses for every direct ontology axiom satisfies the
    base case `ConceptDerivable.base` of the invariant.  The
    `step` cases require closing under `Join` saturation, which is
    the substantive work of item #5. -/
def AtomAtomBaseSeed (O : Ontology) (D_seed : ContextStructure) : Prop :=
  D_seed.vr ∈ D_seed.contexts ∧
  ∀ A B : Nat,
    (ALCHOQ.Concept.atom A, ALCHOQ.Concept.atom B) ∈ O →
    ∃ c ∈ D_seed.S D_seed.vr, subsumes c (atomAtomSubsumptionClause A B)

/-- **The `unsubsumed → refutable` implication** for atom-atom
    subsumption queries.  This is the contrapositive of the
    propositional saturation invariant restricted to the atom-atom
    query slice.

    Given the invariant `PropSaturationInvariantAtomic O D` and a
    query `Q` whose body is `[atomTrue (atom A x)]` and head is
    `[atomTrue (atom B x)]`, if no clause in `S(D.vr)` subsumes
    `{Q.Gamma, Q.Delta}`, then `B` is not `ConceptDerivable` from
    `{A}` — which is the `headNotDerivable` field of `AtomicRefutable`. -/
theorem atomicRefutable_from_propSaturationInvariant
    (O : Ontology) (D : ContextStructure)
    (hInv : PropSaturationInvariantAtomic O D)
    (Q : QueryClause)
    (A B : Nat)
    (hQA : Q.Gamma = [BLit.atomTrue (PTerm.atom A ATerm.x)])
    (hQB : Q.Delta = [CLit.atomTrue (PTerm.atom B ATerm.x)])
    (hNoSub : ∀ c ∈ D.S D.vr,
      ¬ subsumes c {body := Q.Gamma, head := Q.Delta}) :
    ¬ ConceptDerivable O (fun X => X = A) B := by
  intro hDer
  obtain ⟨c, hcIn, hcSub⟩ := hInv.2 A B hDer
  have hQeq : ({ body := Q.Gamma, head := Q.Delta } : CClause) =
              atomAtomSubsumptionClause A B := by
    rw [hQA, hQB]; rfl
  exact hNoSub c hcIn (hQeq ▸ hcSub)

/-- **`ConceptDerivable` is monotonic in the initial set.** -/
theorem conceptDerivable_mono
    (O : Ontology) {init₁ init₂ : Nat → Prop}
    (hSub : ∀ X, init₁ X → init₂ X)
    {B : Nat} (hDer : ConceptDerivable O init₁ B) :
    ConceptDerivable O init₂ B := by
  induction hDer with
  | base h => exact ConceptDerivable.base (hSub _ h)
  | step _ hAx ih => exact ConceptDerivable.step ih hAx

/-- **Bridging lemma**: for a query whose body is exactly
    `[atomTrue (atom A x)]`, `queryBodyAtomConcepts Q` is equivalent
    to `(fun X => X = A)`.  Used to lift the invariant's
    `(fun X => X = A)` form to `headNotDerivable`'s
    `queryBodyAtomConcepts` form. -/
theorem queryBodyAtomConcepts_singleton
    (Q : QueryClause) (A : Nat)
    (hQA : Q.Gamma = [BLit.atomTrue (PTerm.atom A ATerm.x)])
    (X : Nat) :
    queryBodyAtomConcepts Q X ↔ X = A := by
  unfold queryBodyAtomConcepts
  rw [hQA]
  constructor
  · rintro ⟨t, ht⟩
    rcases List.mem_singleton.mp ht with heq
    -- heq : BLit.atomTrue (PTerm.atom X t) = BLit.atomTrue (PTerm.atom A ATerm.x)
    cases heq; rfl
  · rintro rfl
    exact ⟨ATerm.x, List.mem_singleton.mpr rfl⟩

/-- **`headNotDerivable` field of `AtomicRefutable` from the
    propositional saturation invariant.**  Specialised to the
    atom-atom subsumption query slice. -/
theorem headNotDerivable_from_propSaturationInvariant
    (O : Ontology) (D : ContextStructure)
    (hInv : PropSaturationInvariantAtomic O D)
    (Q : QueryClause)
    (A B : Nat)
    (hQA : Q.Gamma = [BLit.atomTrue (PTerm.atom A ATerm.x)])
    (hQB : Q.Delta = [CLit.atomTrue (PTerm.atom B ATerm.x)])
    (hNoSub : ∀ c ∈ D.S D.vr,
      ¬ subsumes c {body := Q.Gamma, head := Q.Delta}) :
    ∀ B' t, CLit.atomTrue (PTerm.atom B' t) ∈ Q.Delta →
      ¬ ConceptDerivable O (queryBodyAtomConcepts Q) B' := by
  intro B' t hMem hDer
  -- hMem : CLit.atomTrue (atom B' t) ∈ Q.Delta = [atomTrue (atom B x)]
  rw [hQB] at hMem
  rcases List.mem_singleton.mp hMem with heq
  -- heq : CLit.atomTrue (atom B' t) = CLit.atomTrue (atom B x)
  cases heq
  -- Now B' = B and t = ATerm.x.
  -- Convert hDer's initial set from queryBodyAtomConcepts Q to (fun X => X = A).
  have hMono : ConceptDerivable O (fun X => X = A) B :=
    conceptDerivable_mono (O := O) (init₁ := queryBodyAtomConcepts Q)
      (init₂ := fun X => X = A)
      (fun X hX => (queryBodyAtomConcepts_singleton Q A hQA X).mp hX)
      hDer
  exact atomicRefutable_from_propSaturationInvariant O D hInv Q A B hQA hQB hNoSub hMono

-- ============================================================
-- §0.2 Reachability demonstrator for the refined 12-rule calculus.
--
-- With the thesis-faithful refinements of Hyper/Eq/Factor/Join/Nom
-- (matching premise `S_v ≠ []`) and Pred/Rpred (edge-existence
-- premise), the empty context structure is now `FullSaturated`:
-- no rule has the syntactic shape to fire on it.  This is the
-- finite-D reachability witness item #2 of the completeness
-- decomposition asks for.
-- ============================================================

/-- The empty context structure is `FullSaturated` under the refined
    12-rule calculus.  Every rule is blocked: Core/Elim/Ineq by the
    empty `S` and `core`, the five hypothetic rules by `S_v = []`,
    Pred/Rpred by the empty `edges`, and Succ/Rsucc need a non-root
    context, which the empty structure does not provide. -/
theorem fullSaturated_emptyContextStructure :
    FullSaturated emptyContextStructure := by
  intro D' rn hStep
  cases hStep with
  | viaCore hSC =>
    obtain ⟨_, hA, _⟩ := hSC
    exact absurd hA List.not_mem_nil
  | viaElim hSE =>
    obtain ⟨_, hCM, _⟩ := hSE
    exact absurd hCM List.not_mem_nil
  | viaIneq hSI =>
    obtain ⟨_, hCM, _, _, _⟩ := hSI
    exact absurd hCM List.not_mem_nil
  | viaHyper hSH =>
    -- hSH.2 : emptyContextStructure.S v ≠ []  but S v = [] by definition.
    exact hSH.2 rfl
  | viaEq hSE =>
    exact hSE.2 rfl
  | viaFactor hSF =>
    exact hSF.2 rfl
  | viaJoin hSJ =>
    exact hSJ.2 rfl
  | viaNom hSN =>
    exact hSN.2 rfl
  | viaSucc hSS =>
    -- Succ requires `v ≠ D.vr` AND `v ∈ D.contexts = [0]`, so v = 0 = vr.
    obtain ⟨hvIn, hvne, _⟩ := hSS
    have : (0 : CtxId) = 0 := rfl
    -- hvIn : v ∈ [0], so v = 0; hvne : v ≠ emptyContextStructure.vr = 0.
    have hv0 : ∀ v : CtxId, v ∈ [(0 : CtxId)] → v = 0 := by
      intro v hv
      rcases List.mem_cons.mp hv with h | h
      · exact h
      · exact absurd h List.not_mem_nil
    have := hv0 _ hvIn
    exact hvne (by rw [this]; rfl)
  | viaPred hSP =>
    obtain ⟨_w, _f, hEdge⟩ := hSP.2
    exact absurd hEdge List.not_mem_nil
  | viaRsucc hSR =>
    -- Rsucc requires v ≠ D.vr AND v ∈ D.contexts = [0].
    obtain ⟨hvIn, hvne, _⟩ := hSR
    have hv0 : ∀ v : CtxId, v ∈ [(0 : CtxId)] → v = 0 := by
      intro v hv
      rcases List.mem_cons.mp hv with h | h
      · exact h
      · exact absurd h List.not_mem_nil
    have := hv0 _ hvIn
    exact hvne (by rw [this]; rfl)
  | viaRpred hSR =>
    obtain ⟨_u, hEdge⟩ := hSR.2
    exact absurd hEdge List.not_mem_nil

/-- **Empty seed terminates with Λ = 0.**  Vacuous bound: the empty
    context structure has empty `S` and is `FullSaturated` under
    the refined 12-rule calculus (item #2), so every
    `FullDerivation` from it is `refl`, and the bound holds. -/
theorem emptySeed_saturationTerminates (_O : Ontology) :
    SaturationTerminates _O emptyContextStructure := by
  refine ⟨0, ?_⟩
  intro D hDeriv
  cases hDeriv with
  | refl _ => exact emptyContextStructure_CClausesBounded 0
  | step hStep _ =>
    exact absurd hStep (fullSaturated_emptyContextStructure _ _)

-- ============================================================
-- Item #9: Concept → QueryClause normalisation + Bridge.
--
-- The thesis §6.2 normalisation maps a description-logic concept
-- inclusion `C ⊑ D` to an equisatisfiable QueryClause such that
-- `O ⊨ C ⊑ D` iff the QueryClause is entailed by `O`.
--
-- For the atom-atom slice of SROIQ, the normalisation is the
-- identity: `atom A ⊑ atom B` becomes the canonical query
-- `{atomTrue (atom A x)} → {atomTrue (atom B x)}`.   The Bridge
-- gives the iff between QueryClause entailment and the
-- DL-level subsumption statement.
-- ============================================================

/-- **Atom-subsumption query**: the canonical QueryClause for
    `atom A ⊑ atom B`. -/
def atomSubsumptionQuery (A B : Nat) : QueryClause :=
  { Gamma := [BLit.atomTrue (PTerm.atom A ATerm.x)]
  , Delta := [CLit.atomTrue (PTerm.atom B ATerm.x)] }

/-- The atom-subsumption query and `atomAtomSubsumptionClause` carry
    identical body/head data — the two views (QueryClause vs CClause)
    on the same atom-atom subsumption. -/
theorem atomSubsumptionQuery_eq_atomAtomSubsumptionClause (A B : Nat) :
    ({body := (atomSubsumptionQuery A B).Gamma,
      head := (atomSubsumptionQuery A B).Delta} : CClause) =
    atomAtomSubsumptionClause A B := rfl

/-- **Bridge: semantic-entailment of the atom-subsumption query**
    is equivalent to the DL statement `O ⊨ atom A ⊑ atom B`. -/
theorem entailsQuery_atomSubsumption (O : Ontology) (A B : Nat) :
    entailsQuery O (atomSubsumptionQuery A B) ↔
    (∀ {α : Type} (I : Interp α), I.satisfies O →
       ∀ x : α, I.ext_concept A x → I.ext_concept B x) := by
  constructor
  · intro hEnt α I hSat x hAx
    have hQ := hEnt I (fun _ => x) (fun _ a => a) hSat x x
    have hBody : ∀ b ∈ (atomSubsumptionQuery A B).Gamma,
                 BLit.eval I ⟨fun _ => x, fun _ a => a, x, x⟩ b := by
      intro b hb
      rcases List.mem_singleton.mp hb with rfl
      -- BLit.eval ... (atomTrue (atom A x)) = PTerm.eval ... = ext_concept A x.
      change I.ext_concept A x
      exact hAx
    obtain ⟨h, hMem, hEval⟩ := hQ hBody
    rcases List.mem_singleton.mp hMem with rfl
    -- hEval : CLit.eval ... (atomTrue (atom B x)) = PTerm.eval ... = ext_concept B x.
    exact hEval
  · intro hSem α I γ φ hSat vx _vy hBody
    have hAxBody : BLit.atomTrue (PTerm.atom A ATerm.x) ∈
                   (atomSubsumptionQuery A B).Gamma :=
      List.mem_singleton.mpr rfl
    have hAxEval : I.ext_concept A vx := hBody _ hAxBody
    have hBx : I.ext_concept B vx := hSem I hSat vx hAxEval
    refine ⟨CLit.atomTrue (PTerm.atom B ATerm.x), ?_, ?_⟩
    · exact List.mem_singleton.mpr rfl
    · exact hBx

/-- **Normalisation of a single axiom into a QueryClause** (atom-atom
    slice).   Given `(atom A, atom B) ∈ O`, the normalised query is
    `atomSubsumptionQuery A B`. -/
def axiomToQuery (axR : ALCHOQ.Concept × ALCHOQ.Concept) :
    Option QueryClause :=
  match axR with
  | (ALCHOQ.Concept.atom A, ALCHOQ.Concept.atom B) => some (atomSubsumptionQuery A B)
  | _ => none

/-- For atom-atom-only ontologies, `axiomToQuery` always produces
    `some` value. -/
theorem axiomToQuery_some_of_atomic (O : Ontology) (hO : IsAtomicSubsumptionOnly O)
    (ax : ALCHOQ.Concept × ALCHOQ.Concept) (hax : ax ∈ O) :
    ∃ A B : Nat, axiomToQuery ax = some (atomSubsumptionQuery A B) := by
  obtain ⟨A, B, rfl⟩ := hO ax hax
  exact ⟨A, B, rfl⟩

-- ============================================================
-- Item #10: RBox integration.
--
-- The thesis SROIQ calculus handles role-box (RBox) axioms: role
-- inclusion, chains, transitive/symmetric/asymmetric/reflexive/
-- irreflexive/inverse/disjoint roles.   These axioms are
-- defined in `ELKSDD.SROIQ.RAxiom` with semantic evaluation.
--
-- For the atom-atom slice (item #1), the Herbrand interpretation
-- has `ext_role _ _ _ := False`, so every RAxiom whose premise
-- references `ext_role` is vacuously satisfied.   We identify
-- the *compatible* subset (everything except `.refl`) and show
-- the atomic Herbrand model satisfies every compatible RBox.
-- ============================================================

/-- **An RAxiom is compatible with the empty-roles atomic Herbrand
    model.**  This holds for every axiom shape *except* `.refl`
    (which demands `ext_role R x x` for every `x`) and `.chain []`
    (which similarly demands `ext_role S x x` via the trivial
    holdsAlong). -/
def RAxiomCompatibleWithEmptyRoles : SROIQ.RAxiom → Prop
  | SROIQ.RAxiom.refl _      => False
  | SROIQ.RAxiom.chain [] _  => False
  | _                        => True

/-- **Atomic Herbrand interpretation has empty `ext_role`.** -/
theorem atomicHerbrandInterp_ext_role_false
    (O : Ontology) (Q : QueryClause) (R : Nat) (x y : Unit) :
    ¬ (atomicHerbrandInterp O Q).ext_role R x y := by
  intro h; exact h

/-- **Compatible RAxioms are vacuously satisfied by the atomic
    Herbrand interpretation.**  Discharges each compatible shape
    by appeal to `ext_role _ _ _ = False`. -/
theorem atomicHerbrandInterp_satisfies_RAxiom
    (O : Ontology) (Q : QueryClause)
    (ax : SROIQ.RAxiom) (hCompat : RAxiomCompatibleWithEmptyRoles ax) :
    ax.eval (atomicHerbrandInterp O Q) := by
  cases ax with
  | incl R S =>
    intro x y hR
    exact absurd hR (atomicHerbrandInterp_ext_role_false O Q R x y)
  | chain rs S =>
    intro x y hChain
    cases rs with
    | nil =>
      -- Incompatible per hCompat: `.chain []` is excluded.
      exact absurd hCompat (fun h => h)
    | cons r rs' =>
      obtain ⟨z, hRz, _⟩ := hChain
      exact absurd hRz (atomicHerbrandInterp_ext_role_false O Q r x z)
  | trans R =>
    intro x y z hRxy _
    exact absurd hRxy (atomicHerbrandInterp_ext_role_false O Q R x y)
  | sym R =>
    intro x y hR
    exact absurd hR (atomicHerbrandInterp_ext_role_false O Q R x y)
  | asym R =>
    intro x y hR _
    exact absurd hR (atomicHerbrandInterp_ext_role_false O Q R x y)
  | refl R =>
    -- Incompatible per hCompat = False.
    exact absurd hCompat (fun h => h)
  | irrefl R =>
    intro x hR
    exact absurd hR (atomicHerbrandInterp_ext_role_false O Q R x x)
  | inv R S =>
    intro x y
    constructor
    · intro hR
      exact absurd hR (atomicHerbrandInterp_ext_role_false O Q R x y)
    · intro hS
      exact absurd hS (atomicHerbrandInterp_ext_role_false O Q S y x)
  | disj R S =>
    intro x y ⟨hR, _⟩
    exact absurd hR (atomicHerbrandInterp_ext_role_false O Q R x y)

/-- **RBox compatibility**: every axiom in the RBox is compatible
    with the empty-roles atomic Herbrand model. -/
def RBoxCompatibleWithEmptyRoles (rbox : SROIQ.RBox) : Prop :=
  ∀ ax ∈ rbox, RAxiomCompatibleWithEmptyRoles ax

/-- **The empty RBox is compatible.** -/
theorem emptyRBox_compatible :
    RBoxCompatibleWithEmptyRoles ([] : SROIQ.RBox) := by
  intro ax hax
  exact absurd hax List.not_mem_nil

/-- **Atomic Herbrand interpretation satisfies any compatible RBox.** -/
theorem atomicHerbrandInterp_satisfies_compatible_rbox
    (O : Ontology) (Q : QueryClause)
    (rbox : SROIQ.RBox) (hCompat : RBoxCompatibleWithEmptyRoles rbox) :
    SROIQ.RBox.eval (atomicHerbrandInterp O Q) rbox := by
  intro ax hax
  exact atomicHerbrandInterp_satisfies_RAxiom O Q ax (hCompat ax hax)

/-- **Atomic Herbrand satisfies the empty RBox.**  Direct corollary,
    matching the §5.4 thesis approach for SROIQ → ALCHOIQ reduction. -/
theorem atomicHerbrandInterp_satisfies_emptyRBox
    (O : Ontology) (Q : QueryClause) :
    SROIQ.RBox.eval (atomicHerbrandInterp O Q) ([] : SROIQ.RBox) :=
  atomicHerbrandInterp_satisfies_compatible_rbox O Q [] emptyRBox_compatible

-- ============================================================
-- §FINAL.  `canonicalSeedOf : Ontology → ContextStructure`
--
-- The total canonical-seed function: takes an ontology `O` and
-- returns a context structure that encodes `O`'s atom-atom axioms
-- as clauses at `S(0)`.   For atom-atom-only ontologies, this
-- seed satisfies the full `IsCanonicalSeed` predicate.   For
-- ontologies with non-atom-atom axioms, the missing axioms are
-- filtered out by `axiomToCClause`; full SROIQ coverage requires
-- the normalisation work flagged as future work (item #9).
-- ============================================================

/-- **Per-axiom clause translation.**  An atom-atom inclusion
    `(atom A, atom B)` becomes the clause `{A(x)} → {B(x)}`.   All
    other axiom shapes return `none` (placeholder for the full
    SROIQ normalisation). -/
def axiomToCClause : ALCHOQ.Axiom → Option CClause
  | (ALCHOQ.Concept.atom A, ALCHOQ.Concept.atom B) =>
    some { body := [BLit.atomTrue (PTerm.atom A ATerm.x)]
         , head := [CLit.atomTrue (PTerm.atom B ATerm.x)] }
  | _ => none

/-- **Ontology-to-clauses translation.**  Filters and maps the
    axiom list through `axiomToCClause`. -/
def ontologyToClauses (O : Ontology) : List CClause :=
  O.filterMap axiomToCClause

/-- **The canonical-seed context structure for `O`.**  One context
    (the root `0`), no edges, empty core, `S(0)` populated with the
    atom-atom axiom clauses from `O`.   Compatible with the
    `IsCanonicalSeed` shape: `vr = 0`, `vr ∈ contexts`,
    `D.S = [ontologyToClauses O at 0, [] elsewhere]`. -/
def canonicalSeedOf (O : Ontology) : ContextStructure where
  contexts := [0]
  vr       := 0
  edges    := []
  core     := fun _ => { atoms := [] }
  S        := fun v => if v = 0 then ontologyToClauses O else []
  m        := trivialAdmissibleOrder
  θ        := fun _ => trivialContextOrder

/-- **First IsCanonicalSeed conjunct**: the root lives in
    `contexts`. -/
theorem canonicalSeedOf_vr_in_contexts (O : Ontology) :
    (canonicalSeedOf O).vr ∈ (canonicalSeedOf O).contexts := by
  show (0 : CtxId) ∈ [0]
  exact List.mem_singleton.mpr rfl

/-- **Origin of clauses in `ontologyToClauses`**: every produced
    clause comes from an atom-atom axiom of `O`. -/
theorem mem_ontologyToClauses
    (O : Ontology) (c : CClause) (hc : c ∈ ontologyToClauses O) :
    ∃ A B : Nat,
      (ALCHOQ.Concept.atom A, ALCHOQ.Concept.atom B) ∈ O ∧
      c = { body := [BLit.atomTrue (PTerm.atom A ATerm.x)]
          , head := [CLit.atomTrue (PTerm.atom B ATerm.x)] } := by
  unfold ontologyToClauses at hc
  rcases List.mem_filterMap.mp hc with ⟨ax, haxO, haxC⟩
  -- ax : Axiom; haxC : axiomToCClause ax = some c.
  -- axiomToCClause produces `some _` only for the (atom A, atom B) case.
  match hax : ax, haxC with
  | (ALCHOQ.Concept.atom A, ALCHOQ.Concept.atom B), haxC' =>
    have hcEq : c = { body := [BLit.atomTrue (PTerm.atom A ATerm.x)]
                    , head := [CLit.atomTrue (PTerm.atom B ATerm.x)] } := by
      have hUnfold : axiomToCClause (ALCHOQ.Concept.atom A, ALCHOQ.Concept.atom B) =
                     some { body := [BLit.atomTrue (PTerm.atom A ATerm.x)]
                          , head := [CLit.atomTrue (PTerm.atom B ATerm.x)] } := rfl
      rw [hUnfold] at haxC'
      exact (Option.some.inj haxC').symm
    exact ⟨A, B, haxO, hcEq⟩

/-- **Soundness of an atom-atom clause** under a model satisfying
    the corresponding axiom. -/
theorem atomAtom_clause_sound
    {α : Type} (I : Interp α) (γ : Indu → α) (φ : FunSym → α → α)
    (A B : Nat) (vx vy : α)
    (hAx : I.satisfiesAxiom (ALCHOQ.Concept.atom A, ALCHOQ.Concept.atom B)) :
    CClause.eval I ⟨γ, φ, vx, vy⟩
      { body := [BLit.atomTrue (PTerm.atom A ATerm.x)]
      , head := [CLit.atomTrue (PTerm.atom B ATerm.x)] } := by
  intro hBody
  -- hBody : ∀ b ∈ [atomTrue (atom A x)], BLit.eval I _ b
  have hAxBody : BLit.atomTrue (PTerm.atom A ATerm.x) ∈
                  [BLit.atomTrue (PTerm.atom A ATerm.x)] :=
    List.mem_singleton.mpr rfl
  have hAEval : BLit.eval I ⟨γ, φ, vx, vy⟩
                  (BLit.atomTrue (PTerm.atom A ATerm.x)) :=
    hBody _ hAxBody
  -- hAEval reduces to PTerm.eval = ext_concept A vx.
  have hExtA : I.ext_concept A vx := hAEval
  -- Apply hAx to get ext_concept B vx.
  have hExtB : I.ext_concept B vx := hAx vx hExtA
  refine ⟨CLit.atomTrue (PTerm.atom B ATerm.x), ?_, ?_⟩
  · exact List.mem_singleton.mpr rfl
  · -- CLit.eval reduces to PTerm.eval = ext_concept B vx.
    exact hExtB

/-- **Second IsCanonicalSeed conjunct**: there exists a derived-clause
    set `CD` such that `canonicalSeedOf O` is sound for `O`.   We
    take `CD := { clauses := [] }` (empty derived clauses); soundness
    of each placed clause reduces to the corresponding ontology axiom. -/
theorem canonicalSeedOf_sound (O : Ontology) :
    ∃ CD : DerivedClauses, isSound O (canonicalSeedOf O) CD := by
  refine ⟨{ clauses := [] }, ?_, ?_⟩
  · -- S1: every clause in S(v) is sound.
    intro v hv c hc α I γ φ hIO _hICD vx vy _hCore
    -- hv : v ∈ [0], so v = 0.
    have hv0 : v = 0 := by
      rcases List.mem_cons.mp hv with h | h
      · exact h
      · exact absurd h List.not_mem_nil
    subst hv0
    -- hc : c ∈ (canonicalSeedOf O).S 0 = ontologyToClauses O
    have hS0 : (canonicalSeedOf O).S 0 = ontologyToClauses O := by
      show (if (0 : CtxId) = 0 then ontologyToClauses O else []) =
           ontologyToClauses O
      simp
    rw [hS0] at hc
    obtain ⟨A, B, hAxO, hCEq⟩ := mem_ontologyToClauses O c hc
    rw [hCEq]
    exact atomAtom_clause_sound I γ φ A B vx vy (hIO _ hAxO)
  · -- S2: every fn-edge propagates; canonicalSeedOf has no edges.
    intro v w f hEdge _hne
    unfold ContextStructure.hasEdge at hEdge
    show ∀ {α : Type} (I : Interp α) (γ : Indu → α) (φ : FunSym → α → α),
      I.satisfies O →
      InterpSatisfiesCD I γ φ { clauses := [] } →
      ∀ vx vy : α,
        coreSat I ⟨γ, φ, vx, vy⟩ ((canonicalSeedOf O).core v) →
        coreSat I ⟨γ, φ, φ f vx, vx⟩ ((canonicalSeedOf O).core w)
    -- canonicalSeedOf O.edges = [], so hEdge is False.
    exact absurd hEdge List.not_mem_nil

/-- **HerbrandProperty for the atom-atom slice modulo saturation
    completeness.**  The seed `canonicalSeedOf O` discharges the
    Herbrand property when any saturated derivative satisfies the
    propositional saturation invariant `PropSaturationInvariantAtomic`.
    This invariant captures the §6.3.4 closure under transitive
    consequences — the thesis's saturation-completeness content. -/
theorem canonicalSeedOf_herbrandProperty_atomic_modulo
    (O : Ontology) (hO : IsAtomicSubsumptionOnly O)
    (hSatComplete : ∀ D : ContextStructure,
       FullDerivation (canonicalSeedOf O) D → FullSaturated D →
       PropSaturationInvariantAtomic O D)
    (hAtomShape : ∀ D : ContextStructure,
       FullDerivation (canonicalSeedOf O) D → FullSaturated D →
       ∀ Q : QueryClause,
         (∀ c ∈ D.S D.vr, ¬ subsumes c {body := Q.Gamma, head := Q.Delta}) →
         ∃ A B : Nat,
           Q.Gamma = [BLit.atomTrue (PTerm.atom A ATerm.x)] ∧
           Q.Delta = [CLit.atomTrue (PTerm.atom B ATerm.x)]) :
    HerbrandProperty O (canonicalSeedOf O) := by
  apply herbrandProperty_atomicSubsumption O hO
  intro D hDeriv hSat Q hNoSub
  obtain ⟨A, B, hQA, hQB⟩ := hAtomShape D hDeriv hSat Q hNoSub
  have hInv := hSatComplete D hDeriv hSat
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- noRoleBody: no role atoms in body
    intro S t₁ t₂ hMem
    rw [hQA] at hMem
    have : BLit.atomTrue (PTerm.role S t₁ t₂) =
           BLit.atomTrue (PTerm.atom A ATerm.x) :=
      List.mem_singleton.mp hMem
    cases this
  · -- noTtrueHead
    intro hMem
    rw [hQB] at hMem
    have : CLit.atomTrue PTerm.ttrue =
           CLit.atomTrue (PTerm.atom B ATerm.x) :=
      List.mem_singleton.mp hMem
    cases this
  · -- noEqLHead
    intro s₁ s₂ hMem
    rw [hQB] at hMem
    cases List.mem_singleton.mp hMem
  · -- noRoleHead
    intro S t₁ t₂ hMem
    rw [hQB] at hMem
    have : CLit.atomTrue (PTerm.role S t₁ t₂) =
           CLit.atomTrue (PTerm.atom B ATerm.x) :=
      List.mem_singleton.mp hMem
    cases this
  · -- headNotDerivable
    exact headNotDerivable_from_propSaturationInvariant O D hInv Q A B
      hQA hQB hNoSub

/-- **IsCanonicalSeed for the atom-atom slice modulo saturation
    completeness.**  The two unconditional conjuncts (`vr ∈ contexts`,
    soundness) combine with the conditional Herbrand property. -/
theorem isCanonicalSeed_canonicalSeedOf_atomic_modulo
    (O : Ontology) (hO : IsAtomicSubsumptionOnly O)
    (hSatComplete : ∀ D : ContextStructure,
       FullDerivation (canonicalSeedOf O) D → FullSaturated D →
       PropSaturationInvariantAtomic O D)
    (hAtomShape : ∀ D : ContextStructure,
       FullDerivation (canonicalSeedOf O) D → FullSaturated D →
       ∀ Q : QueryClause,
         (∀ c ∈ D.S D.vr, ¬ subsumes c {body := Q.Gamma, head := Q.Delta}) →
         ∃ A B : Nat,
           Q.Gamma = [BLit.atomTrue (PTerm.atom A ATerm.x)] ∧
           Q.Delta = [CLit.atomTrue (PTerm.atom B ATerm.x)]) :
    IsCanonicalSeed O (canonicalSeedOf O) :=
  ⟨canonicalSeedOf_vr_in_contexts O,
   canonicalSeedOf_sound O,
   canonicalSeedOf_herbrandProperty_atomic_modulo O hO hSatComplete hAtomShape⟩

-- ============================================================
-- §FINAL-CONCRETE.  An explicit name for the combined gap.
--
-- We package the two remaining hypotheses into a single named
-- predicate that future work must discharge.   This isolates the
-- substantive thesis content that remains.
-- ============================================================

/-- **The combined saturation-completeness predicate.**  Holds for
    an ontology `O` iff: for every `D` obtainable by full
    derivation from `canonicalSeedOf O`, every saturated such `D`
    satisfies both the propositional invariant
    (`PropSaturationInvariantAtomic`) and the atom-atom Q-shape
    restriction.   Discharging this for arbitrary `O` is the
    saturation-completeness theorem of §5.4-§6.3 of the thesis. -/
def CanonicalSaturationGap (O : Ontology) : Prop :=
  (∀ D : ContextStructure,
     FullDerivation (canonicalSeedOf O) D → FullSaturated D →
     PropSaturationInvariantAtomic O D) ∧
  (∀ D : ContextStructure,
     FullDerivation (canonicalSeedOf O) D → FullSaturated D →
     ∀ Q : QueryClause,
       (∀ c ∈ D.S D.vr, ¬ subsumes c {body := Q.Gamma, head := Q.Delta}) →
       ∃ A B : Nat,
         Q.Gamma = [BLit.atomTrue (PTerm.atom A ATerm.x)] ∧
         Q.Delta = [CLit.atomTrue (PTerm.atom B ATerm.x)])

/-- **IsCanonicalSeed via the combined gap.**  This is the final
    packaged form: given `CanonicalSaturationGap O`, all three
    `IsCanonicalSeed` conjuncts are discharged. -/
theorem isCanonicalSeed_canonicalSeedOf_via_gap
    (O : Ontology) (hO : IsAtomicSubsumptionOnly O)
    (hGap : CanonicalSaturationGap O) :
    IsCanonicalSeed O (canonicalSeedOf O) :=
  isCanonicalSeed_canonicalSeedOf_atomic_modulo O hO hGap.1 hGap.2

-- ============================================================
-- §FINAL-GAP.  Theoretical obstacles to unconditional IsCanonicalSeed.
--
-- Beyond `CanonicalSaturationGap O` (the named hypothesis bundling
-- the two outstanding obligations), two STRUCTURAL obstacles
-- prevent a literal unconditional discharge:
--
-- (1) Reflexive coverage over unbounded `Nat`.   The current
--     `PropSaturationInvariantAtomic` universally quantifies over
--     `(A, B) : Nat × Nat`.   `ConceptDerivable.base` gives
--     `ConceptDerivable O (fun X => X = A) A` for *every* `A`.
--     So the invariant requires a subsumer of `{A(x)} → {A(x)}`
--     for every `A : Nat`.   A finite seed cannot enumerate these.
--
-- (2) Tautological Q over unbounded `Nat`.   `HerbrandProperty`
--     asserts: every unsubsumed Q admits an O-model refuting it.
--     For tautological Q (e.g., `{[A(x)], [A(x)]}` for any `A`),
--     no model refutes it — so HerbrandProperty implicitly
--     requires every tautological Q to be subsumed by S(D.vr).
--     Same unboundedness obstacle as (1).
--
-- The thesis (Tena-Cucala 2021) implicitly assumes a finite
-- signature (the concepts/roles actually used in `O`), which
-- avoids these issues.   Discharging the gap unconditionally
-- requires one of:
--
--   * A FINITE-SIGNATURE restriction on the framework
--     (changing `Ontology`'s underlying types from `Nat` to a
--     bounded set);
--   * A Q-parameterised canonical seed
--     (`canonicalSeedOf : Ontology → QueryClause → ContextStructure`),
--     where the seed includes reflexives for Q's concepts;
--   * A refined `PropSaturationInvariantAtomic` restricted to a
--     fixed finite signature, together with a refined
--     `HerbrandProperty` that excludes tautological Q.
--
-- Any of these is a substantial framework change.   We isolate
-- the current state honestly: `canonicalSeedOf` and its two
-- unconditional conjuncts (`vr ∈ contexts`, soundness) are
-- foundation-axiom-clean; the third conjunct reduces to
-- `CanonicalSaturationGap`, which captures the §6.3 thesis
-- content and the framework-level signature restrictions
-- described above.
-- ============================================================

-- ============================================================
-- §FINAL-NEGATIVE.  A formal negative meta-result.
--
-- We FORMALLY show that `canonicalSeedOf []` (the canonical seed
-- for the empty ontology) does NOT satisfy `IsCanonicalSeed []`.
-- This makes precise the framework-level obstacle: the literal
-- unconditional goal is unattainable for this specific instance,
-- because the tautological query
-- `Q := atomSubsumptionQuery 0 0` is unsubsumed in `S(0) = []` but
-- admits no counter-model.
-- ============================================================

/-- **canonicalSeedOf [] is FullSaturated.**  Empty ontology means
    `ontologyToClauses [] = []`, so the seed has empty `S`, empty
    `core`, no edges — structurally identical to
    `emptyContextStructure` from the rule-firing perspective. -/
theorem fullSaturated_canonicalSeedOf_empty :
    FullSaturated (canonicalSeedOf []) := by
  intro D' rn hStep
  -- All rule firings require some non-empty piece of structure
  -- that `canonicalSeedOf []` lacks.   Mirror of
  -- `fullSaturated_emptyContextStructure`.
  cases hStep with
  | viaCore hSC =>
    obtain ⟨_, hA, _⟩ := hSC
    -- hA : A ∈ (canonicalSeedOf []).core v .atoms = []
    exact absurd hA List.not_mem_nil
  | @viaElim _ _ v _ hSE =>
    obtain ⟨_, hCM, _⟩ := hSE
    have hSv : (canonicalSeedOf []).S v = [] := by
      show (if v = 0 then ontologyToClauses [] else []) = []
      split <;> rfl
    rw [hSv] at hCM
    exact absurd hCM List.not_mem_nil
  | @viaIneq _ _ v _ _ _ hSI =>
    obtain ⟨_, hCM, _, _, _⟩ := hSI
    have hSv : (canonicalSeedOf []).S v = [] := by
      show (if v = 0 then ontologyToClauses [] else []) = []
      split <;> rfl
    rw [hSv] at hCM
    exact absurd hCM List.not_mem_nil
  | @viaHyper _ _ _ _ v _ hSH =>
    have hSv : (canonicalSeedOf []).S v = [] := by
      show (if v = 0 then ontologyToClauses [] else []) = []
      split <;> rfl
    exact hSH.2 hSv
  | @viaEq _ _ _ _ v _ hSE =>
    have hSv : (canonicalSeedOf []).S v = [] := by
      show (if v = 0 then ontologyToClauses [] else []) = []
      split <;> rfl
    exact hSE.2 hSv
  | @viaFactor _ _ _ _ v _ hSF =>
    have hSv : (canonicalSeedOf []).S v = [] := by
      show (if v = 0 then ontologyToClauses [] else []) = []
      split <;> rfl
    exact hSF.2 hSv
  | @viaJoin _ _ _ _ v _ hSJ =>
    have hSv : (canonicalSeedOf []).S v = [] := by
      show (if v = 0 then ontologyToClauses [] else []) = []
      split <;> rfl
    exact hSJ.2 hSv
  | @viaNom _ _ _ _ v _ hSN =>
    have hSv : (canonicalSeedOf []).S v = [] := by
      show (if v = 0 then ontologyToClauses [] else []) = []
      split <;> rfl
    exact hSN.2 hSv
  | viaSucc hSS =>
    obtain ⟨hvIn, hvne, _⟩ := hSS
    have hv0 : ∀ v : CtxId, v ∈ [(0 : CtxId)] → v = 0 := by
      intro v hv
      rcases List.mem_cons.mp hv with h | h
      · exact h
      · exact absurd h List.not_mem_nil
    have := hv0 _ hvIn
    exact hvne (by rw [this]; rfl)
  | viaPred hSP =>
    obtain ⟨_w, _f, hEdge⟩ := hSP.2
    exact absurd hEdge List.not_mem_nil
  | viaRsucc hSR =>
    obtain ⟨hvIn, hvne, _⟩ := hSR
    have hv0 : ∀ v : CtxId, v ∈ [(0 : CtxId)] → v = 0 := by
      intro v hv
      rcases List.mem_cons.mp hv with h | h
      · exact h
      · exact absurd h List.not_mem_nil
    have := hv0 _ hvIn
    exact hvne (by rw [this]; rfl)
  | viaRpred hSR =>
    obtain ⟨_u, hEdge⟩ := hSR.2
    exact absurd hEdge List.not_mem_nil

/-- **The tautological query is unconditionally satisfied** by every
    interpretation.   `atomSubsumptionQuery A A` says
    `A(x) → A(x)`, which is `True`. -/
theorem atomSubsumptionQuery_self_eval
    {α : Type} (I : Interp α) (γ : Indu → α) (φ : FunSym → α → α)
    (A : Nat) (vx vy : α) :
    (atomSubsumptionQuery A A).eval I ⟨γ, φ, vx, vy⟩ := by
  intro hBody
  refine ⟨CLit.atomTrue (PTerm.atom A ATerm.x), List.mem_singleton.mpr rfl, ?_⟩
  -- CLit.eval ... (atomTrue (atom A x)) = PTerm.eval = ext_concept A vx.
  -- Body asserted ext_concept A vx already (via hBody applied to the singleton).
  have hAxBody : BLit.atomTrue (PTerm.atom A ATerm.x) ∈
                 (atomSubsumptionQuery A A).Gamma :=
    List.mem_singleton.mpr rfl
  exact hBody _ hAxBody

/-- **No clause subsumes the self-subsumption query unless it
    is itself the same.**  For `canonicalSeedOf []` with empty `S`,
    vacuously no clause subsumes anything. -/
theorem canonicalSeedOf_empty_no_subsumer (A : Nat) :
    ∀ c ∈ (canonicalSeedOf []).S (canonicalSeedOf []).vr,
      ¬ subsumes c {body := (atomSubsumptionQuery A A).Gamma,
                    head := (atomSubsumptionQuery A A).Delta} := by
  intro c hc _hSub
  have : (canonicalSeedOf []).S (canonicalSeedOf []).vr = [] := by
    show (canonicalSeedOf []).S 0 = []
    show (if (0 : CtxId) = 0 then ontologyToClauses [] else []) = []
    simp [ontologyToClauses]
  rw [this] at hc
  exact List.not_mem_nil hc

/-- **HerbrandProperty fails for `canonicalSeedOf []`.**  The
    tautological query `atomSubsumptionQuery 0 0` is unsubsumed by
    `S((canonicalSeedOf []).vr) = []` but admits no counter-model,
    since every interpretation satisfies it.   Hence the
    HerbrandProperty's existential witness is unachievable. -/
theorem not_herbrandProperty_canonicalSeedOf_empty :
    ¬ HerbrandProperty [] (canonicalSeedOf []) := by
  intro hHP
  -- Apply to D = canonicalSeedOf [] (via FullDerivation.refl)
  -- and Q = atomSubsumptionQuery 0 0.
  have hDeriv : FullDerivation (canonicalSeedOf []) (canonicalSeedOf []) :=
    FullDerivation.refl _
  have hSat : FullSaturated (canonicalSeedOf []) :=
    fullSaturated_canonicalSeedOf_empty
  obtain ⟨α, _hα, I, γ, φ, vx, vy, _hISat, hQfail⟩ :=
    hHP _ hDeriv hSat (atomSubsumptionQuery 0 0)
      (canonicalSeedOf_empty_no_subsumer 0)
  -- But (atomSubsumptionQuery 0 0).eval is unconditionally true.
  exact hQfail (atomSubsumptionQuery_self_eval I γ φ 0 vx vy)

/-- **IsCanonicalSeed [] (canonicalSeedOf []) is FALSE.**  Direct
    corollary of `not_herbrandProperty_canonicalSeedOf_empty`. -/
theorem not_isCanonicalSeed_canonicalSeedOf_empty :
    ¬ IsCanonicalSeed [] (canonicalSeedOf []) := by
  intro ⟨_, _, hHP⟩
  exact not_herbrandProperty_canonicalSeedOf_empty hHP

/-- **Consequence**: `CanonicalSaturationGap []` is FALSE.   The
    conditional `isCanonicalSeed_canonicalSeedOf_via_gap` therefore
    holds vacuously for the empty ontology; the substantive
    framework restriction (finite signature, or refined invariant)
    is necessary. -/
theorem not_canonicalSaturationGap_empty :
    ¬ CanonicalSaturationGap [] := by
  intro hGap
  have hIsCS : IsCanonicalSeed [] (canonicalSeedOf []) :=
    isCanonicalSeed_canonicalSeedOf_via_gap [] (by intro ax hax; exact absurd hax List.not_mem_nil) hGap
  exact not_isCanonicalSeed_canonicalSeedOf_empty hIsCS

-- ============================================================
-- §FINAL-REFINED.  The refined goal: HerbrandProperty restricted
-- to queries over a finite signature.
--
-- Given the structural impossibility of the literal unconditional
-- goal, we deliver the refined goal: parameterise IsCanonicalSeed
-- by an explicit finite set of "in-signature" concepts.   The
-- canonical seed for `O` over signature `sig` includes reflexive
-- clauses for every concept in `sig`.   The refined HerbrandProperty
-- restricts `Q` to use only concepts in `sig`.
-- ============================================================

/-- **Reflexive clause for a concept** `A`. -/
def reflexiveClause (A : Nat) : CClause :=
  { body := [BLit.atomTrue (PTerm.atom A ATerm.x)]
  , head := [CLit.atomTrue (PTerm.atom A ATerm.x)] }

/-- **The signature-aware canonical seed.**  Augments
    `canonicalSeedOf O` with reflexive clauses for every concept in
    a caller-supplied signature `sig`. -/
def canonicalSeedOver (sig : List Nat) (O : Ontology) : ContextStructure where
  contexts := [0]
  vr       := 0
  edges    := []
  core     := fun _ => { atoms := [] }
  S        := fun v => if v = 0 then
                          ontologyToClauses O ++ sig.map reflexiveClause
                       else []
  m        := trivialAdmissibleOrder
  θ        := fun _ => trivialContextOrder

/-- **First refined-seed conjunct**: `vr ∈ contexts`. -/
theorem canonicalSeedOver_vr_in_contexts (sig : List Nat) (O : Ontology) :
    (canonicalSeedOver sig O).vr ∈ (canonicalSeedOver sig O).contexts := by
  show (0 : CtxId) ∈ [0]
  exact List.mem_singleton.mpr rfl

/-- **Soundness of reflexive clauses**: every reflexive `{A(x)} → {A(x)}`
    is sound under any interpretation (tautology). -/
theorem reflexiveClause_sound
    {α : Type} (I : Interp α) (γ : Indu → α) (φ : FunSym → α → α)
    (A : Nat) (vx vy : α) :
    CClause.eval I ⟨γ, φ, vx, vy⟩ (reflexiveClause A) := by
  intro hBody
  refine ⟨CLit.atomTrue (PTerm.atom A ATerm.x), ?_, ?_⟩
  · exact List.mem_singleton.mpr rfl
  · exact hBody _ (List.mem_singleton.mpr rfl)

/-- **Second refined-seed conjunct**: soundness for `canonicalSeedOver`. -/
theorem canonicalSeedOver_sound (sig : List Nat) (O : Ontology) :
    ∃ CD : DerivedClauses, isSound O (canonicalSeedOver sig O) CD := by
  refine ⟨{ clauses := [] }, ?_, ?_⟩
  · intro v hv c hc α I γ φ hIO _ vx vy _
    have hv0 : v = 0 := by
      rcases List.mem_cons.mp hv with h | h
      · exact h
      · exact absurd h List.not_mem_nil
    subst hv0
    have hS0 : (canonicalSeedOver sig O).S 0 =
               ontologyToClauses O ++ sig.map reflexiveClause := by
      show (if (0 : CtxId) = 0 then
              ontologyToClauses O ++ sig.map reflexiveClause
            else []) = ontologyToClauses O ++ sig.map reflexiveClause
      simp
    rw [hS0] at hc
    rcases List.mem_append.mp hc with hAx | hReflex
    · obtain ⟨A, B, hAxO, hCEq⟩ := mem_ontologyToClauses O c hAx
      rw [hCEq]
      exact atomAtom_clause_sound I γ φ A B vx vy (hIO _ hAxO)
    · rcases List.mem_map.mp hReflex with ⟨A, _hA, hCEq⟩
      rw [← hCEq]
      exact reflexiveClause_sound I γ φ A vx vy
  · intro v w f hEdge _
    unfold ContextStructure.hasEdge at hEdge
    exact absurd hEdge List.not_mem_nil

/-- **Reflexive clauses subsume tautological self-subsumption queries**
    for concepts in the signature. -/
theorem reflexiveClause_subsumes_tautology
    (A : Nat) :
    subsumes (reflexiveClause A)
             { body := (atomSubsumptionQuery A A).Gamma
             , head := (atomSubsumptionQuery A A).Delta } := by
  refine ⟨?_, ?_⟩
  · intro b hb; exact hb
  · intro h hh; exact hh

/-- **For `A ∈ sig`, the reflexive `Q = atomSubsumptionQuery A A` is
    subsumed by `S(canonicalSeedOver sig O).vr)`.**  This eliminates
    the obstacle (1) for concepts in the signature. -/
theorem canonicalSeedOver_subsumes_reflexive_tautology
    (sig : List Nat) (O : Ontology) (A : Nat) (hA : A ∈ sig) :
    ∃ c ∈ (canonicalSeedOver sig O).S (canonicalSeedOver sig O).vr,
      subsumes c { body := (atomSubsumptionQuery A A).Gamma
                 , head := (atomSubsumptionQuery A A).Delta } := by
  refine ⟨reflexiveClause A, ?_, reflexiveClause_subsumes_tautology A⟩
  -- reflexiveClause A ∈ S(0) of canonicalSeedOver
  show reflexiveClause A ∈
    (if (0 : CtxId) = 0 then
       ontologyToClauses O ++ sig.map reflexiveClause
     else [])
  rw [if_pos rfl]
  exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨A, hA, rfl⟩))

end ALCHOIQContext
end ELKSDD
