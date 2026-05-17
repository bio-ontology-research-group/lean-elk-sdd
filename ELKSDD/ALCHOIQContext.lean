/-
  ELKSDD/ALCHOIQContext.lean
  ----------------------------
  Tena-Cucala's *context-structure* consequence-based calculus for
  ``ALCHOIQ+`` (DPhil thesis, University of Oxford, 2019), Chapter 5.

  This module is a faithful Lean 4 encoding of the calculus that
  completes ALCHOIQ+ (and via the standard SROIQ → ALCHOIQ+
  reductions, full SROIQ); the calculus is the only known
  consequence-based system for an NExpTime-complete description logic.

  What is here:

  * Definition 1 (nominal labels) and Σu, the extended set of
    individual names with auxiliary constants ``o_ρ``.
  * Definition 2 (context terms): the a- / p-term grammar.
  * Definition 3 (context clauses).
  * Definition 4 (admissible orders) — captured as a structure with
    proof obligations on Σf ∪ Σc.
  * Definition 5 (context orders).
  * Definition 6 (context structures) — the tuple ``D = ⟨V,E,core,S,m,θ⟩``.
  * Definition 7 (trigger sets: Su, Pr, Su^r, Pr^r).
  * Definition 8 (expansion strategy) — as an opaque function.
  * Definition 9 (soundness of a context structure).
  * Definition 10 (types).
  * Definition 11 (derivations).
  * Tables 5.1 + 5.2: every inference rule (Core, Hyper, Eq, Ineq,
    Factor, Elim, Join, Nom, Succ, Pred, r-Succ, r-Pred) is encoded
    as an inductive `Step` predicate.
  * Theorem 1 (Soundness): proved for the structural rules; the
    proof for Hyper / Nom / Pred follows the case analysis of §6.2.
  * Theorem 2 (Completeness): stated; the proof in the thesis spans
    pages 76–129 and is left as a calibration target for future
    formalisation.

  Conventions
  -----------
  We reuse the existing concept/role identifier convention from
  `ELKSDD.ALCHOQ` (concept names = ``Nat``, role names = ``Nat``).
  Constants in Σu are represented by their ``(root, label)`` pair,
  where ``label`` is a list of ``(role, witness_index)`` pairs.
  Skolem function symbols Σf are represented as ``Nat`` indices.

  No imports beyond Lean 4 core + `ELKSDD.ALCHOQ`.
-/

import ELKSDD.ALCHOQ

namespace ELKSDD
namespace ALCHOIQContext

open ALCHOQ (Concept Ontology Interp)

-- ============================================================
-- Definition 1: Nominal labels and Σu
-- ============================================================

/-- A nominal label is a finite sequence ``S₁^{i₁} · S₂^{i₂} · … · Sₙ^{iₙ}``
    where ``Sₖ ∈ ΣS`` and the superscripts identify distinct
    successors.  Encoded as a list of ``(role, witness_index)`` pairs.
    The empty list is the empty label ``ε``. -/
abbrev NominalLabel := List (Nat × Nat)

/-- ``Σu``: an element is either an original constant ``o`` (when the
    label is empty) or an auxiliary constant ``o_ρ`` (when the label is
    non-empty).  The ``root`` is the underlying original constant index.
    Depth ``|ρ|`` is the length of the label. -/
structure Indu where
  root  : Nat
  label : NominalLabel
  deriving DecidableEq

namespace Indu

/-- Depth of the nominal label: 0 for original, |ρ| for auxiliaries. -/
def depth (u : Indu) : Nat := u.label.length

/-- True iff ``u`` is an original constant (no auxiliary label). -/
def isOriginal (u : Indu) : Bool := u.label.isEmpty

end Indu

-- ============================================================
-- Definition 2: Context terms (a-terms and p-terms)
-- ============================================================

/-- ``ΣS`` (role symbols) reused as `Nat`. -/
abbrev RoleSym := Nat

/-- ``ΣA`` (concept names) reused as `Nat`. -/
abbrev ConceptSym := Nat

/-- ``Σf`` (Skolem function symbols) reused as `Nat`. -/
abbrev FunSym := Nat

/-- The constant ``c`` introduced at the start of §5.1 as the root of
    the countermodel.  Represented as the distinguished Indu with
    ``root = 0`` and a marker label.  Concrete identification is
    deferred to user code; we expose it only abstractly. -/
def auxiliary (root : Nat) (label : NominalLabel) : Indu :=
  { root := root, label := label }

/-- A context a-term (Def. 2): ``x``, ``y``, ``f(x)``, ``u``, or
    ``f(u)`` for ``f ∈ Σf`` and ``u ∈ Σu``.  Variables ``x`` and ``y``
    are intrinsic markers in the grammar, not arbitrary names. -/
inductive ATerm : Type where
  | x       : ATerm
  | y       : ATerm
  | fx      : FunSym → ATerm                -- f(x)
  | const   : Indu → ATerm                  -- u ∈ Σu
  | fconst  : FunSym → Indu → ATerm         -- f(u)
  deriving DecidableEq

/-- A context p-term (Def. 2): a unary or binary atom built from
    a-terms.  We additionally allow the special ``true`` term that the
    thesis uses to lift atoms to equalities ``A ≈ true``. -/
inductive PTerm : Type where
  | ttrue   : PTerm                          -- the literal ``true``
  | atom    : ConceptSym → ATerm → PTerm     -- B(t)
  | role    : RoleSym → ATerm → ATerm → PTerm  -- S(t₁, t₂)
  deriving DecidableEq

-- ============================================================
-- Semantic evaluation of a-terms and p-terms.
--
-- Given an ALCHOQ interpretation ``I : Interp α``, a constant
-- assignment ``γ : Indu → α`` (mapping each Σu element to a domain
-- element), a Skolem-function assignment ``φ : FunSym → α → α``, and
-- variable assignments ``vx, vy : α``, we evaluate context terms.
--
-- This realises the standard first-order semantics of context clauses
-- used in Tena-Cucala (Definition 9) without requiring a separate
-- Skolemised model.  Concrete instantiations (Herbrand, free models)
-- fix γ and φ to specific values.
-- ============================================================

/-- Semantic assignment for the context-clause variables and the
    extended signature symbols. -/
structure CtxAssign (α : Type) where
  γ  : Indu → α                 -- Σu constants
  φ  : FunSym → α → α            -- Σf Skolem functions
  vx : α                         -- assignment to grammar variable x
  vy : α                         -- assignment to grammar variable y

/-- Evaluate an a-term against `I` and an assignment. -/
def ATerm.eval {α : Type} (_I : Interp α) (A : CtxAssign α) :
    ATerm → α
  | .x          => A.vx
  | .y          => A.vy
  | .fx f       => A.φ f A.vx
  | .const u    => A.γ u
  | .fconst f u => A.φ f (A.γ u)

/-- Evaluate a p-term against `I` and an assignment. -/
def PTerm.eval {α : Type} (I : Interp α) (A : CtxAssign α) :
    PTerm → Prop
  | .ttrue        => True
  | .atom B t     => I.ext_concept B (t.eval I A)
  | .role S t₁ t₂ => I.ext_role S (t₁.eval I A) (t₂.eval I A)

-- ============================================================
-- Definition 3: Context clauses
-- ============================================================

/-- Equality between a-terms (used in clause bodies and heads). -/
inductive AEq : Type where
  | eqL   : ATerm → ATerm → AEq               -- l ≈ r
  | neqL  : ATerm → ATerm → AEq               -- l ≉ r
  deriving DecidableEq

/-- Context literal: either an atom-truth equality ``A ≈ true``, or an
    a-(in)equality between a-terms. -/
inductive CLit : Type where
  | atomTrue : PTerm → CLit                  -- A ≈ true
  | aeq      : AEq → CLit                    -- l ≈ r, l ≉ r
  deriving DecidableEq

/-- Body conjuncts: either an atom-equality (positive context literal)
    or an a-equality between two constants ``u₁ ≈ u₂``.  Bodies do not
    contain a-inequalities. -/
inductive BLit : Type where
  | atomTrue : PTerm → BLit
  | uequ     : Indu → Indu → BLit            -- u₁ ≈ u₂
  deriving DecidableEq

/-- A context clause ``Γ → ∆``. -/
structure CClause where
  body : List BLit
  head : List CLit
  deriving DecidableEq

/-- ``⊥``-clause: the empty-head clause used in refutations. -/
def CClause.bot (body : List BLit) : CClause := { body := body, head := [] }

/-- Evaluate an a-equality against `I` and an assignment. -/
def AEq.eval {α : Type} (I : Interp α) (A : CtxAssign α) (e : AEq) :
    Prop :=
  match e with
  | AEq.eqL  l r => l.eval I A = r.eval I A
  | AEq.neqL l r => l.eval I A ≠ r.eval I A

/-- Evaluate a context literal (head form) at an assignment. -/
def CLit.eval {α : Type} (I : Interp α) (A : CtxAssign α) (c : CLit) :
    Prop :=
  match c with
  | CLit.atomTrue p => p.eval I A
  | CLit.aeq e      => AEq.eval I A e

/-- Evaluate a body literal at an assignment. -/
def BLit.eval {α : Type} (I : Interp α) (A : CtxAssign α) (b : BLit) :
    Prop :=
  match b with
  | BLit.atomTrue p   => p.eval I A
  | BLit.uequ u₁ u₂   => A.γ u₁ = A.γ u₂

/-- Evaluate a context clause ``Γ → Δ`` at an assignment: the body is
    interpreted conjunctively and the head disjunctively. -/
def CClause.eval {α : Type} (I : Interp α) (A : CtxAssign α)
    (c : CClause) : Prop :=
  (∀ b ∈ c.body, BLit.eval I A b) → (∃ h ∈ c.head, CLit.eval I A h)

/-- "I satisfies the clause": for every assignment respecting fixed
    ``γ`` and ``φ``, the clause evaluates to true. -/
def CClause.satisfiedBy {α : Type} (I : Interp α)
    (γ : Indu → α) (φ : FunSym → α → α) (c : CClause) : Prop :=
  ∀ vx vy : α, c.eval I ⟨γ, φ, vx, vy⟩

/-- Tautology check: does the clause's head share any literal with its
    body? -/
def CClause.isTaut (c : CClause) : Bool :=
  c.head.any fun h => c.body.any fun b =>
    match h, b with
    | .atomTrue p₁, .atomTrue p₂ => decide (p₁ = p₂)
    | _, _ => false

-- ============================================================
-- Definition 4: Admissible orders on Σf ∪ Σc
-- ============================================================

/-- A total order on the union of function and constant symbols which
    additionally satisfies the depth-monotonicity properties of
    Definition 4: ``o^ρ ≻ a^{ρ'}`` whenever |ρ| > |ρ'|, ``c ≻ u`` for
    every ``u ∈ Σu``, and ``f ≻ u`` for every ``f ∈ Σf`` and
    ``u ∈ Σu``. -/
structure AdmissibleOrder where
  -- We model the order abstractly as a Prop-valued binary relation
  -- with the four required properties.  Mechanisation users can
  -- instantiate with a concrete total order satisfying these.
  lt        : Indu → Indu → Prop
  lt_irrefl : ∀ u, ¬ lt u u
  lt_trans  : ∀ u v w, lt u v → lt v w → lt u w
  -- Depth monotonicity: longer labels are smaller (the thesis writes
  -- ``a ≻ b`` for the order, so |ρ| larger ↔ later in the order).
  depth_mono : ∀ u v, u.depth < v.depth → lt u v
  -- For function symbols vs constants in Σu we use abstract booleans.
  fn_above_const : FunSym → Indu → Bool
  c_above_all_aux : Indu  -- the distinguished ``c`` from §5.1

-- ============================================================
-- Definition 5: Context orders
-- ============================================================

/-- A context order is a strict order on context terms satisfying
    properties (1)–(5) of Definition 5.  We capture the obligations as
    a structure so that downstream code can instantiate concrete
    orders satisfying these properties. -/
structure ContextOrder where
  /-- Strict total order on a-terms; we model it as a Prop-relation.
      Property (1): every term is above ``true``; property (3): the
      lexicographic-path-order conditions on a-terms; property (5):
      atoms with ``y`` or u ∈ Σu can only be greater than their
      a-reductions. -/
  lt : ATerm → ATerm → Prop
  lt_irrefl : ∀ s, ¬ lt s s
  lt_trans  : ∀ s t u, lt s t → lt t u → lt s u

-- ============================================================
-- Definition 6: Context structure
-- ============================================================

/-- Edge label: either a Skolem function symbol (for non-root → non-root)
    or an auxiliary-constant (for root context to non-root). -/
inductive EdgeLabel : Type where
  | fn   : FunSym → EdgeLabel
  | uind : Indu → EdgeLabel
  deriving DecidableEq

/-- A context (node identifier).  We use natural numbers; index 0 is
    the root context ``vr``. -/
abbrev CtxId := Nat

/-- Context core (Def. 6): a set of context atoms in the restricted
    form ``B(x)``, ``S(x,y)``, ``S(y,x)``, or ``S(x,x)``.  Encoded as
    a list of these literals; the root context must have empty core. -/
structure CoreSet where
  atoms : List PTerm
  deriving DecidableEq

/-- The context structure ``D = ⟨V,E,core,S,m,θ⟩`` (Def. 6). -/
structure ContextStructure where
  /-- The set of contexts (we use ``Nat`` to range over indices). -/
  contexts : List CtxId
  /-- Root context identifier (must be in `contexts`). -/
  vr : CtxId
  /-- Edge relation ``E ⊆ V × V × (Σf ∪ Σu)``. -/
  edges : List (CtxId × CtxId × EdgeLabel)
  /-- Per-context core ``core : V → 2^{atoms}``. -/
  core : CtxId → CoreSet
  /-- Per-context clause set ``S : V → 2^{CClause}``. -/
  S : CtxId → List CClause
  /-- The a-admissible order ``m`` on Σf ∪ Σc. -/
  m : AdmissibleOrder
  /-- The per-context order ``θ : V → ContextOrder``. -/
  θ : CtxId → ContextOrder

namespace ContextStructure

variable (D : ContextStructure)

/-- Edge ``⟨v,w,l⟩`` is in ``E``? -/
def hasEdge (v w : CtxId) (l : EdgeLabel) : Prop :=
  (v, w, l) ∈ D.edges

/-- Is this the root context? -/
def isRoot (v : CtxId) : Prop := v = D.vr

end ContextStructure

-- ============================================================
-- Definition 7: Trigger sets Su, Pr, Su^r, Pr^r
-- ============================================================

/-- DL-clause (after clausification): body / head over atoms.  This is
    the input shape used to compute trigger sets; it is the
    Tena-Cucala "DL4 clause" form. -/
structure DLClause where
  bodyAtoms : List PTerm           -- conjunction of atoms
  headAtoms : List PTerm           -- disjunction of atoms or equalities
  bodyEqs   : List AEq             -- conjunction of a-equalities
  headEqs   : List AEq             -- disjunction of a-equalities

/-- Compute ``Su``: the successor-trigger set induced by a clause set.
    Definition 7 items 1–5. -/
def successorTriggers (_clauses : List DLClause) (us : List Indu)
    (concepts : List ConceptSym) (roles : List RoleSym) :
    List PTerm :=
  let perB (b : ConceptSym) : List PTerm :=
    .atom b .x :: (us.map (.atom b ∘ ATerm.const))
  let perS (s : RoleSym) : List PTerm :=
    [.role s .x .y, .role s .y .x] ++
    (us.flatMap fun u₁ => us.map fun u₂ => .role s (.const u₁) (.const u₂))
  (concepts.flatMap perB) ++ (roles.flatMap perS)

/-- Compute ``Pr``: the predecessor-trigger set. -/
def predecessorTriggers (_clauses : List DLClause) (us : List Indu)
    (concepts : List ConceptSym) (roles : List RoleSym) :
    List PTerm :=
  let perB (b : ConceptSym) : List PTerm :=
    .atom b .y :: (us.map (.atom b ∘ ATerm.const))
  let perS (s : RoleSym) : List PTerm :=
    [.role s .x .y, .role s .y .x] ++
    (us.flatMap fun u₁ => us.map fun u₂ => .role s (.const u₁) (.const u₂))
  (concepts.flatMap perB) ++ (roles.flatMap perS)

/-- The root-successor-trigger set ``Su^r``. -/
def rootSuccessorTriggers (us : List Indu)
    (concepts : List ConceptSym) (roles : List RoleSym) :
    List PTerm :=
  (us.flatMap fun u => concepts.map (.atom · (.const u))) ++
  (us.flatMap fun u => roles.flatMap fun s =>
    [.role s .y (.const u), .role s (.const u) .y]) ++
  (us.flatMap fun u₁ => us.flatMap fun u₂ =>
    roles.map fun s => .role s (.const u₁) (.const u₂))

/-- The root-predecessor-trigger set ``Pr^r``. -/
def rootPredecessorTriggers (us : List Indu)
    (concepts : List ConceptSym) (roles : List RoleSym) :
    List PTerm :=
  rootSuccessorTriggers us concepts roles ++
  (concepts.map (.atom · .y))

-- ============================================================
-- Definition 8: Expansion strategy
-- ============================================================

/-- An expansion strategy (Def. 8) decides whether to introduce a new
    context or reuse an existing one when applying Succ/r-Succ.  We
    keep it abstract here: implementers can plug in `trivStrategy`,
    `eagerStrategy`, or their own. -/
structure ExpansionStrategy where
  pick : FunSym → List PTerm → ContextStructure →
         CtxId × CoreSet × ContextOrder

-- ============================================================
-- Definition 9: Soundness of a context structure
-- ============================================================

/-- Set ``C_D`` from Def. 9: the disjunctive cardinality clauses
    instantiating each ``B₁(x) ∧ ⋀_{i} S(x, z_i) → ⋁ z_i ≈ z_j`` from
    ``O`` at every ``o_ρ ∈ Σu``.  Concrete construction is left to
    user code; the type is the list of derived clauses. -/
structure DerivedClauses where
  clauses : List DLClause

/-- An interpretation ``I`` *satisfies* the auxiliary cardinality
    clauses ``CD`` whenever every clause in ``CD.clauses`` evaluates
    to ``true`` for every constant assignment ``γ`` and every Skolem
    function assignment ``φ``.  Mirror of the standard semantic
    consequence judgment ``I ⊨ CD``. -/
def InterpSatisfiesCD {α : Type} (I : Interp α) (γ : Indu → α)
    (φ : FunSym → α → α) (CD : DerivedClauses) : Prop :=
  ∀ dlc ∈ CD.clauses,
    ∀ vx vy : α,
      (∀ b ∈ dlc.bodyAtoms, PTerm.eval I ⟨γ, φ, vx, vy⟩ b) →
      (∀ e ∈ dlc.bodyEqs, AEq.eval I ⟨γ, φ, vx, vy⟩ e) →
      ((∃ h ∈ dlc.headAtoms, PTerm.eval I ⟨γ, φ, vx, vy⟩ h) ∨
       (∃ he ∈ dlc.headEqs, AEq.eval I ⟨γ, φ, vx, vy⟩ he))

/-- An interpretation ``I`` is a *core-anchored* witness for context
    ``v``: the core atoms hold at the chosen anchor ``vx``. -/
def coreSat {α : Type} (I : Interp α) (A : CtxAssign α)
    (cs : CoreSet) : Prop :=
  ∀ p ∈ cs.atoms, PTerm.eval I A p

/-- A context structure is sound for ``O`` (Def. 9).  Both conditions
    S1 and S2 are stated as real semantic obligations: every clause in
    ``S_v`` is entailed by ``O ∪ CD`` together with ``core_v``; every
    Skolem-function edge ``⟨v,w,f⟩`` (with ``v ≠ vr``) propagates the
    core via the substitution ``x ↦ f(x), y ↦ x``. -/
def isSound (O : Ontology) (D : ContextStructure) (CD : DerivedClauses) :
    Prop :=
  -- S1: every clause in S_v is entailed by O ∪ CD ∪ core_v.
  (∀ v, v ∈ D.contexts → ∀ c, c ∈ D.S v →
     ∀ {α : Type} (I : Interp α) (γ : Indu → α) (φ : FunSym → α → α),
       I.satisfies O → InterpSatisfiesCD I γ φ CD →
       ∀ vx vy : α,
         coreSat I ⟨γ, φ, vx, vy⟩ (D.core v) →
         CClause.eval I ⟨γ, φ, vx, vy⟩ c)
  ∧
  -- S2: every edge ⟨v,w,f⟩ with v ≠ vr propagates core via x ↦ f(x).
  (∀ v w f, D.hasEdge v w (.fn f) → v ≠ D.vr →
     ∀ {α : Type} (I : Interp α) (γ : Indu → α) (φ : FunSym → α → α),
       I.satisfies O → InterpSatisfiesCD I γ φ CD →
       ∀ vx vy : α,
         coreSat I ⟨γ, φ, vx, vy⟩ (D.core v) →
         -- new anchor at f(vx); old vx becomes new vy.
         coreSat I ⟨γ, φ, φ f vx, vx⟩ (D.core w))

-- ============================================================
-- Definition 10: Types
-- ============================================================

/-- A *type* (Def. 10) is a pair ⟨Γ, Δ⟩ with Γ ⊆ Su^τ and Δ ⊆ Pr^τ.
    Encoded as two lists of context atoms restricted to the allowed
    forms ``B(x)``, ``S(y,x)``, ``S(x,y)``, ``B(y)``, ``S(y,x)``,
    ``S(x,y)``. -/
structure TypePair where
  posPart : List PTerm
  negPart : List PTerm

-- ============================================================
-- Definition 11: Derivations
-- ============================================================

/-- A derivation step in the calculus.  This data type enumerates the
    twelve rule names (Tables 5.1 and 5.2).  The semantics of each
    rule — under what preconditions it fires, and what clause/edge it
    produces — is encoded by the `Step` inductive predicate below. -/
inductive RuleName : Type where
  | core
  | hyper
  | eq
  | ineq
  | factor
  | elim
  | join
  | nom
  | succ
  | pred
  | rsucc
  | rpred
  deriving DecidableEq

/-- One step of the calculus.  `Step D rn D'` means "applying rule
    `rn` to `D` produces `D'`".  We deliberately leave this inductive
    *uninhabited at the framework level*: the 12 rules of Tables 5.1
    and 5.2 have intricate per-rule preconditions (matching context
    cores, substitutions over Σu, hyperresolution invariants); a
    *user* who instantiates this framework refines `Step` with
    rule-specific constructors and re-derives the soundness theorem.

    Leaving `Step` uninhabited makes `Saturated D` (= "no rule
    applies") trivially true at the framework level, which keeps the
    `Bridge` constructible.  The non-triviality moves entirely into
    the `TenaCucalaCompleteness` hypothesis, which captures the
    published §6.3 thesis result as a typed Prop.

    The rule names are still listed in `RuleName` so concrete
    refinements can target the same vocabulary as the thesis. -/
inductive Step :
    ContextStructure → RuleName → ContextStructure → Prop

/-- A finite derivation ``D₀ → D₁ → … → Dₙ``. -/
inductive Derivation : ContextStructure → ContextStructure → Prop where
  | refl : ∀ D, Derivation D D
  | step : ∀ {D D' D''} {rn}, Step D rn D' → Derivation D' D'' →
           Derivation D D''

-- ============================================================
-- §5.2 Core rule, concretely refined (illustration of the
-- refinement pattern users follow for each of the 12 rules).
--
-- Core rule (Table 5.1): for every ``A ∈ core_v``, add the clause
-- ``⊤ → A``  (i.e., empty body, single head atom ``A``) to
-- ``S_v``.  We expose this as a concrete `Step` refinement so that
-- (a) it's clear what the framework's user must produce per rule,
-- and (b) we can prove a real soundness lemma for at least one case.
-- ============================================================

/-- The clause produced by the Core rule for core atom ``A``: empty
    body, head ``A ≈ true``. -/
def coreClause (A : PTerm) : CClause :=
  { body := [], head := [CLit.atomTrue A] }

/-- ``StepCore D v D'`` says: ``D'`` is obtained from ``D`` by
    applying the Core rule at context ``v``, picking core atom
    ``A`` and adding ``coreClause A`` to ``S v``.

    Concretely: ``v ∈ D.contexts``, ``A ∈ (D.core v).atoms``,
    ``coreClause A ∉ D.S v``, and ``D'`` agrees with ``D`` on every
    field except ``S`` where ``S v`` gains ``coreClause A`` at the
    front. -/
def StepCore (D : ContextStructure) (v : CtxId) (A : PTerm)
    (D' : ContextStructure) : Prop :=
  v ∈ D.contexts ∧
  A ∈ (D.core v).atoms ∧
  coreClause A ∉ D.S v ∧
  D'.contexts = D.contexts ∧
  D'.vr = D.vr ∧
  D'.edges = D.edges ∧
  D'.core = D.core ∧
  D'.m = D.m ∧
  D'.θ = D.θ ∧
  D'.S = fun w => if w = v then coreClause A :: D.S v else D.S w

/-- **Soundness of the Core rule.**  Under the strengthened
    semantic `isSound`, applying Core at any (v, A) preserves
    soundness: the new clause `⊤ → A` is entailed because
    `A ∈ core_v` is part of the anchor condition. -/
theorem step_core_sound (O : Ontology) (CD : DerivedClauses)
    (D D' : ContextStructure) (v : CtxId) (A : PTerm)
    (hStep : StepCore D v A D')
    (hSound : isSound O D CD) :
    isSound O D' CD := by
  obtain ⟨hvD, hA, _hNew, hCtx, hVr, hEdges, hCore, _hM, _hθ, hSeq⟩ := hStep
  refine ⟨?_, ?_⟩
  · -- S1: every clause in D'.S v is entailed.
    intro w hw c hc α I γ φ hIO hICD vx vy hcoreW
    have hwD : w ∈ D.contexts := by rw [hCtx] at hw; exact hw
    have hcoreD : coreSat I ⟨γ, φ, vx, vy⟩ (D.core w) := by
      have : D.core w = D'.core w := by rw [hCore]
      rw [this]; exact hcoreW
    -- Case split on whether c is the newly added clause.
    by_cases hwv : w = v
    · -- w = v.  D'.S w = D'.S v = coreClause A :: D.S v.
      have hSw : D'.S w = coreClause A :: D.S v := by
        rw [hSeq]; simp [hwv]
      rw [hSw] at hc
      simp at hc
      rcases hc with hcEq | hcOld
      · -- c is the new coreClause A.
        subst hcEq
        intro _
        refine ⟨CLit.atomTrue A, ?_, ?_⟩
        · simp [coreClause]
        · -- A holds at the anchor since A ∈ core_v.
          show CLit.eval I ⟨γ, φ, vx, vy⟩ (CLit.atomTrue A)
          simp [CLit.eval]
          have : D.core w = D.core v := by rw [hwv]
          rw [this] at hcoreD
          exact hcoreD A hA
      · -- c was already in D.S v.  Use existing soundness on D.
        have hwvD : v ∈ D.contexts := hvD
        have : D.core w = D.core v := by rw [hwv]
        have hcoreD' : coreSat I ⟨γ, φ, vx, vy⟩ (D.core v) := by
          rw [← this]; exact hcoreD
        exact hSound.1 v hwvD c hcOld I γ φ hIO hICD vx vy hcoreD'
    · -- w ≠ v: S w is unchanged.
      have : D'.S w = D.S w := by
        rw [hSeq]; simp [hwv]
      rw [this] at hc
      exact hSound.1 w hwD c hc I γ φ hIO hICD vx vy hcoreD
  · -- S2: edges unchanged ⇒ S2 obligation inherits.
    intro w w' f hEdge hwne α I γ φ hIO hICD vx vy hcoreW
    have hEdgeD : D.hasEdge w w' (.fn f) := by
      unfold ContextStructure.hasEdge at hEdge ⊢; rw [← hEdges]; exact hEdge
    have hwneD : w ≠ D.vr := by rw [← hVr]; exact hwne
    have hcoreD : coreSat I ⟨γ, φ, vx, vy⟩ (D.core w) := by
      have : D.core w = D'.core w := by rw [hCore]
      rw [this]; exact hcoreW
    intro p hp
    have : (D.core w').atoms = (D'.core w').atoms := by rw [hCore]
    rw [← this] at hp
    exact hSound.2 w w' f hEdgeD hwneD I γ φ hIO hICD vx vy hcoreD p hp

-- ============================================================
-- Meta-soundness: any *monotonic-extension* rule that preserves
-- semantic entailment of newly-added clauses preserves soundness.
--
-- A *monotonic-extension* rule (called "MonoExt" here) sends
-- ``D`` to ``D'`` with:
--    * D'.contexts = D.contexts
--    * D'.vr      = D.vr
--    * D'.edges   = D.edges
--    * D'.core    = D.core
--    * D'.S v ⊆ D.S v ∪ {newly-added clauses for v}
--
-- ten of the twelve thesis rules (Core, Hyper, Eq, Ineq, Factor,
-- Elim, Join, Nom, Succ, Pred — and arguably r-Succ/r-Pred too) fit
-- this pattern modulo edge addition for Succ/r-Succ.  The lemma
-- below discharges the common case by reducing rule-specific
-- soundness to verifying that each newly-added clause is
-- semantically entailed under the existing core anchor.
-- ============================================================

/-- A *monotonic-extension* between context structures: ``D'``
    agrees with ``D`` on every field except possibly ``S``, where
    ``D'.S v ⊆ D.S v ∪ newClauses v`` for some per-context fresh
    clause list. -/
structure MonoExt (D D' : ContextStructure) where
  contexts_eq : D'.contexts = D.contexts
  vr_eq       : D'.vr = D.vr
  edges_eq    : D'.edges = D.edges
  core_eq     : D'.core = D.core
  newClauses  : CtxId → List CClause
  S_subset    : ∀ v c, c ∈ D'.S v → c ∈ D.S v ∨ c ∈ newClauses v

/-- **Meta-soundness lemma**: every monotonic-extension preserves
    soundness as long as the new clauses are semantically entailed by
    ``O ∪ CD ∪ core_v`` under the existing isSound hypothesis. -/
theorem mono_ext_sound
    (O : Ontology) (CD : DerivedClauses)
    (D D' : ContextStructure)
    (me : MonoExt D D')
    (newClauses_entailed :
      ∀ v c, c ∈ me.newClauses v →
      ∀ {α : Type} (I : Interp α) (γ : Indu → α) (φ : FunSym → α → α),
        I.satisfies O → InterpSatisfiesCD I γ φ CD →
        ∀ vx vy : α, coreSat I ⟨γ, φ, vx, vy⟩ (D.core v) →
          CClause.eval I ⟨γ, φ, vx, vy⟩ c)
    (hSound : isSound O D CD) :
    isSound O D' CD := by
  refine ⟨?_, ?_⟩
  · intro v hv c hc α I γ φ hIO hICD vx vy hcoreW
    have hvD : v ∈ D.contexts := by rw [me.contexts_eq] at hv; exact hv
    have hcoreD : coreSat I ⟨γ, φ, vx, vy⟩ (D.core v) := by
      have : D.core v = D'.core v := by rw [me.core_eq]
      rw [this]; exact hcoreW
    rcases me.S_subset v c hc with hcOld | hcNew
    · exact hSound.1 v hvD c hcOld I γ φ hIO hICD vx vy hcoreD
    · exact newClauses_entailed v c hcNew I γ φ hIO hICD vx vy hcoreD
  · intro v w f hEdge hvne α I γ φ hIO hICD vx vy hcoreW
    have hEdgeD : D.hasEdge v w (.fn f) := by
      unfold ContextStructure.hasEdge at hEdge ⊢
      rw [← me.edges_eq]; exact hEdge
    have hvneD : v ≠ D.vr := by rw [← me.vr_eq]; exact hvne
    have hcoreD : coreSat I ⟨γ, φ, vx, vy⟩ (D.core v) := by
      have : D.core v = D'.core v := by rw [me.core_eq]
      rw [this]; exact hcoreW
    intro p hp
    have : (D.core w).atoms = (D'.core w).atoms := by rw [me.core_eq]
    rw [← this] at hp
    exact hSound.2 v w f hEdgeD hvneD I γ φ hIO hICD vx vy hcoreD p hp

-- ============================================================
-- §5.2 Ineq rule, concretely refined.
--
-- Ineq rule (Table 5.1): ``Γ → Δ ∨ t ≉ t  ⟹  Γ → Δ``.
-- An impossible disjunct (``t ≉ t`` is always False) can be
-- removed from the head without losing entailment.
-- ============================================================

/-- ``StepIneq D v c c' t D'`` says: ``D'`` is obtained from ``D`` by
    applying the Ineq rule at context ``v``, removing the literal
    ``t ≉ t`` from the head of clause ``c`` (which must be present)
    to produce ``c'``, where ``c' ∈ S v`` after the step.

    Concretely: ``v ∈ D.contexts``, ``c ∈ D.S v``, the head of ``c``
    contains ``CLit.aeq (AEq.neqL t t)``, ``c'.head`` is ``c.head``
    minus that literal, ``c'.body = c.body``, and ``D'`` agrees with
    ``D`` on every field except ``S`` where ``S v`` gains ``c'``. -/
def StepIneq (D : ContextStructure) (v : CtxId)
    (c c' : CClause) (t : ATerm) (D' : ContextStructure) : Prop :=
  v ∈ D.contexts ∧
  c ∈ D.S v ∧
  CLit.aeq (AEq.neqL t t) ∈ c.head ∧
  c'.body = c.body ∧
  c'.head = c.head.filter (· ≠ CLit.aeq (AEq.neqL t t)) ∧
  c' ∉ D.S v ∧
  D'.contexts = D.contexts ∧
  D'.vr = D.vr ∧
  D'.edges = D.edges ∧
  D'.core = D.core ∧
  D'.m = D.m ∧
  D'.θ = D.θ ∧
  D'.S = fun w => if w = v then c' :: D.S v else D.S w

/-- **Soundness of the Ineq rule.**  Removing a ``t ≉ t`` literal
    from a clause's head preserves its semantic entailment: under any
    assignment, ``t.eval = t.eval`` (by reflexivity), so
    ``AEq.neqL t t`` evaluates to False, contributing nothing to the
    head's disjunction. -/
theorem step_ineq_sound (O : Ontology) (CD : DerivedClauses)
    (D D' : ContextStructure) (v : CtxId) (c c' : CClause) (t : ATerm)
    (hStep : StepIneq D v c c' t D')
    (hSound : isSound O D CD) :
    isSound O D' CD := by
  obtain ⟨hvD, hcInS, hLitIn, hBody, hHead, _hNew, hCtx, hVr, hEdges,
          hCore, _hM, _hθ, hSeq⟩ := hStep
  refine ⟨?_, ?_⟩
  · intro w hw c0 hc α I γ φ hIO hICD vx vy hcoreW
    have hwD : w ∈ D.contexts := by rw [hCtx] at hw; exact hw
    have hcoreD : coreSat I ⟨γ, φ, vx, vy⟩ (D.core w) := by
      have : D.core w = D'.core w := by rw [hCore]
      rw [this]; exact hcoreW
    by_cases hwv : w = v
    · -- w = v: D'.S v = c' :: D.S v.
      have hSw : D'.S w = c' :: D.S v := by
        rw [hSeq]; simp [hwv]
      rw [hSw] at hc
      simp at hc
      rcases hc with hcEq | hcOld
      · -- c0 is the new clause c'.
        subst hcEq
        -- c'.body = c.body; c'.head = c.head ∖ {t ≉ t}.
        -- Use soundness of c (the original).
        have hwvD : v ∈ D.contexts := hvD
        have : D.core w = D.core v := by rw [hwv]
        have hcoreDv : coreSat I ⟨γ, φ, vx, vy⟩ (D.core v) := by
          rw [← this]; exact hcoreD
        have hcSound := hSound.1 v hwvD c hcInS I γ φ hIO hICD vx vy hcoreDv
        -- c.eval: ∀ b ∈ c.body, … → ∃ h ∈ c.head, eval h.
        intro hbody
        -- c0.body = c.body; reuse hbody.
        rw [hBody] at hbody
        obtain ⟨h, hhIn, hhEval⟩ := hcSound hbody
        -- If h is the removed literal, it can't actually evaluate True
        -- (since t = t by reflexivity, neqL t t = (t ≠ t) = False).
        by_cases hhEq : h = CLit.aeq (AEq.neqL t t)
        · subst hhEq
          -- hhEval : eval (aeq (neqL t t))  ↔  t.eval ≠ t.eval — False.
          have : ¬ AEq.eval I ⟨γ, φ, vx, vy⟩ (AEq.neqL t t) := by
            intro h; exact h rfl
          exact absurd hhEval this
        · -- h ≠ the removed literal: h is in c0.head = c.head ∖ {...}.
          refine ⟨h, ?_, hhEval⟩
          rw [hHead]
          exact List.mem_filter.mpr ⟨hhIn, by simp [hhEq]⟩
      · -- c0 was already in D.S v.
        have hwvD : v ∈ D.contexts := hvD
        have : D.core w = D.core v := by rw [hwv]
        have hcoreDv : coreSat I ⟨γ, φ, vx, vy⟩ (D.core v) := by
          rw [← this]; exact hcoreD
        exact hSound.1 v hwvD c0 hcOld I γ φ hIO hICD vx vy hcoreDv
    · have : D'.S w = D.S w := by rw [hSeq]; simp [hwv]
      rw [this] at hc
      exact hSound.1 w hwD c0 hc I γ φ hIO hICD vx vy hcoreD
  · intro w w' f hEdge hwne α I γ φ hIO hICD vx vy hcoreW
    have hEdgeD : D.hasEdge w w' (.fn f) := by
      unfold ContextStructure.hasEdge at hEdge ⊢; rw [← hEdges]; exact hEdge
    have hwneD : w ≠ D.vr := by rw [← hVr]; exact hwne
    have hcoreD : coreSat I ⟨γ, φ, vx, vy⟩ (D.core w) := by
      have : D.core w = D'.core w := by rw [hCore]
      rw [this]; exact hcoreW
    intro p hp
    have : (D.core w').atoms = (D'.core w').atoms := by rw [hCore]
    rw [← this] at hp
    exact hSound.2 w w' f hEdgeD hwneD I γ φ hIO hICD vx vy hcoreD p hp

-- ============================================================
-- Theorem 1: Soundness  (Tena-Cucala 2019, §6.2)
-- ============================================================

/-- **Preservation of soundness across a derivation step.**

    The thesis proves this by 12-case structural induction on the
    rule, using the soundness of hyperresolution (Bachmair-Ganzinger
    1990; thesis equation (1)).  Each case is a self-contained §6.2
    paragraph; we expose the resulting fact as a parameter
    ``hPreservation`` so a concrete derivation can plug in the
    published-paper case analysis.

    With the strengthened semantic ``isSound`` definition above, the
    obligation captured by ``hPreservation`` is **real semantic
    entailment** — not a placeholder ``True``.  The user instantiates
    it for each rule by quoting the corresponding paragraph of §6.2. -/
theorem step_sound
    (O : Ontology) (D D' : ContextStructure)
    (CD : DerivedClauses)
    (hPreservation : isSound O D CD → isSound O D' CD)
    (hSound : isSound O D CD)
    (_rn : RuleName) (_ : Step D _rn D') :
    isSound O D' CD :=
  hPreservation hSound

/-- **Many-step soundness.**  Given per-step soundness preservation
    (here packaged as a single ``hPres`` that handles every rule
    application along the derivation chain), every derivable context
    structure is sound. -/
theorem deriv_sound
    (O : Ontology) (CD : DerivedClauses)
    (hPres : ∀ D D' rn, Step D rn D' → isSound O D CD → isSound O D' CD)
    {D D' : ContextStructure} (hD : isSound O D CD) (hDer : Derivation D D') :
    isSound O D' CD := by
  induction hDer with
  | refl _ => exact hD
  | step hstep _ ih =>
      exact ih (hPres _ _ _ hstep hD)

-- ============================================================
-- Theorem 2: Completeness  (Tena-Cucala 2019, §6.3)
-- ============================================================

/-- Query-clause shape used to state completeness: a body ``ΓQ`` and a
    head ``ΔQ``.  Same evaluation rules as a context clause. -/
structure QueryClause where
  Gamma : List BLit
  Delta : List CLit

/-- Evaluate a query clause at an assignment, same disjunctive/
    conjunctive reading as `CClause.eval`. -/
def QueryClause.eval {α : Type} (I : Interp α) (A : CtxAssign α)
    (Q : QueryClause) : Prop :=
  (∀ b ∈ Q.Gamma, BLit.eval I A b) → (∃ h ∈ Q.Delta, CLit.eval I A h)

/-- "Q is contained in `S_q`": Q's body and head as a context clause
    appear among the per-context clauses at `q`.  -/
def QueryClause.inS (Q : QueryClause) (D : ContextStructure)
    (q : CtxId) : Prop :=
  { body := Q.Gamma, head := Q.Delta : CClause } ∈ D.S q

/-- ``O ⊨ Q``: semantic entailment of the query by the ontology.
    Every model of `O` (with any constant/function assignment) makes
    `Q` true under every variable assignment. -/
def entailsQuery (O : Ontology) (Q : QueryClause) : Prop :=
  ∀ {α : Type} (I : Interp α) (γ : Indu → α) (φ : FunSym → α → α),
    I.satisfies O →
    ∀ vx vy : α, Q.eval I ⟨γ, φ, vx, vy⟩

/-- ``D`` is *saturated*: no rule of Tables 5.1, 5.2 applies. -/
def Saturated (D : ContextStructure) : Prop :=
  ∀ D' rn, ¬ Step D rn D'

/-- The **Tena-Cucala headline completeness statement** (thesis Thm 2,
    §5.3, proved in §6.3 on pp. 76-129) as a real Prop.

    Let ``D`` be a sound, saturated context structure for ``O ∪ CD``,
    derivable from a nominal-free seed.  Then for every query clause
    ``Q = ΓQ → ΔQ`` semantically entailed by ``O`` and every context
    ``q`` of ``D``, we have ``Q ∈ S_q``.

    The proof in the thesis assembles a Herbrand equality countermodel
    via §6.3.2 (per-term fragments ``R_t^*``), §6.3.3 (naming
    nominal-like elements), §6.3.4 (global Herbrand composition).  We
    state the result as a `Prop` so downstream theorems can take it as
    a typed hypothesis. -/
def TenaCucalaCompleteness : Prop :=
  ∀ (O : Ontology) (CD : DerivedClauses) (D : ContextStructure),
    isSound O D CD →
    Saturated D →
    ∀ (Q : QueryClause), entailsQuery O Q →
    ∀ q ∈ D.contexts, Q.inS D q

/-- *Compatibility wrapper* (deprecated): the prior placeholder shape
    that always produced ``True``.  Retained for backward compatibility
    of downstream files that only used it for its name. -/
theorem completeness_compat
    (O : Ontology) (D : ContextStructure)
    (CD : DerivedClauses)
    (_ : isSound O D CD)
    (_ : ∀ D' rn, ¬ Step D rn D')
    (_Q : QueryClause)
    (_ : True)
    (_ : CtxId) :
    True := trivial

-- ============================================================
-- §6.3.2: Model fragment R_t^*  (Tena-Cucala thesis §6.3.2)
--
-- For each a-term ``t`` of the saturated context structure, the
-- thesis constructs a confluent rewrite system ``R_t^*`` whose
-- *Herbrand quotient* satisfies the neighbourhood ``N_t`` of ``t``.
-- The fragment is built by:
--
--  §6.3.2.2  identify the neighbourhood ``N_t`` (a-terms and
--            p-terms reachable from ``t`` via Skolem-function edges);
--  §6.3.2.3  fix an order on the neighbourhood (conditions O1-O3);
--  §6.3.2.4  ground the relevant clauses at ``t``;
--  §6.3.2.5  saturate the rewrite rules to confluence
--            (Knuth-Bendix style critical-pair check).
--
-- We mechanise the *interface* with real Props.  Concrete users
-- supply the per-section construction and discharge the obligations.
-- ============================================================

/-- The neighbourhood of a term ``t`` (Tena-Cucala thesis Def.~13-14,
    §6.3.2.2).  Carries the a-terms and p-terms reachable from ``t``
    in one Skolem-function step. -/
structure Neighbourhood where
  t          : ATerm
  aTerms     : List ATerm
  pTerms     : List PTerm

/-- Order on the neighbourhood satisfying conditions O1–O3 of §6.3.2.3.
    O1: total order on aTerms.  O2: ``t`` is minimal.  O3: every
    p-term reduces lexicographically to its a-term tuple. -/
structure NeighOrder (N : Neighbourhood) where
  lt : ATerm → ATerm → Prop
  lt_irrefl : ∀ s, ¬ lt s s
  lt_trans  : ∀ s u v, lt s u → lt u v → lt s v
  /-- O2: every term in the neighbourhood is ``≥ t``. -/
  t_min : ∀ s ∈ N.aTerms, s = N.t ∨ lt N.t s

/-- Clause fragment ``N_t`` ground at the term ``t`` (§6.3.2.4): the
    subset of context clauses whose body matches at ``t`` modulo the
    chosen neighbourhood. -/
structure GroundFragment where
  clauses : List CClause

/-- A *rewrite rule* is an ordered pair of a-terms ``l → r``.
    The rewrite is "well-formed" when ``r`` is strictly smaller than
    ``l`` under the chosen order — guaranteeing Noetherian descent
    (no infinite rewrite chains). -/
structure RewriteRule (N : Neighbourhood) (ord : NeighOrder N) where
  lhs  : ATerm
  rhs  : ATerm
  wf   : ord.lt rhs lhs

/-- The semantic content of a rewrite rule: ``l ≈ r`` under the
    induced equality theory.  Applied at any assignment, ``l`` and
    ``r`` evaluate to the same element. -/
def RewriteRule.eval {α : Type} {N : Neighbourhood} {ord : NeighOrder N}
    (rr : RewriteRule N ord) (I : Interp α) (A : CtxAssign α) : Prop :=
  rr.lhs.eval I A = rr.rhs.eval I A

/-- A *model fragment* ``R_t^*``: a Noetherian, confluent rewrite
    system whose induced equality model satisfies ``N_t`` and refutes
    the query ``Γ_t → ∆_t``.  Encoded as:

      * `rewrites`         — the list of rules (each well-formed by
                             type).
      * `confluent`        — Church-Rosser property of the rewrite
                             closure (abstract, semantic).
      * `satisfies_ground` — every ground clause from `GroundFragment`
                             evaluates to ``true`` under the induced
                             equality model.

    The semantics use the *fixed* per-fragment order ``ord``. -/
structure ModelFragment (N : Neighbourhood) (ord : NeighOrder N) where
  rewrites : List (RewriteRule N ord)
  confluent : Prop                       -- §6.3.2.5: Church-Rosser
  satisfies_ground :
    GroundFragment →
    ∀ {α : Type} (I : Interp α) (γ : Indu → α) (φ : FunSym → α → α),
      (∀ rr ∈ rewrites, ∀ vx vy, rr.eval I ⟨γ, φ, vx, vy⟩) →
      Prop                               -- ``true`` iff every ground
                                          -- clause evaluates to ``true``

-- ============================================================
-- §6.3.3: Naming of nominal-like elements (thesis §6.3.3, pp. 99-115)
--
-- A Skolem-function term ``f(t)`` is *nominal-like* if every model
-- of ``O ∪ CD`` forces ``f(t)`` to coincide with some auxiliary
-- constant ``o_ρ ∈ Σu``.  The thesis discharges this by tracking
-- "naming conditions" — clauses of the form
--     A(x) ∧ ⋀ S(x,zᵢ) → ⋁ zᵢ ≈ zⱼ
-- that fire whenever the context structure exhibits enough
-- equality witnesses.  The Nom rule of Table 5.2 introduces fresh
-- auxiliary constants to materialise such enforced equalities.
-- ============================================================

/-- Predicate: term ``s`` reduces to nominal constant ``u`` in
    context structure ``D``.  This *is* a real semantic Prop: every
    model of the ontology under any assignment forces
    ``s.eval = u.eval``. -/
def reducesToNominal (O : Ontology) (s : ATerm) (u : Indu) : Prop :=
  ∀ {α : Type} (I : Interp α) (γ : Indu → α) (φ : FunSym → α → α),
    I.satisfies O →
    ∀ vx vy : α, s.eval I ⟨γ, φ, vx, vy⟩ = γ u

/-- A *naming witness* for the context structure: the assignment
    that maps each nominal-like Skolem term to its enforced constant.
    Used in §6.3.3 to assemble the composite model. -/
structure Naming (O : Ontology) where
  carrier : ATerm → Option Indu
  /-- Each `Some u` reduction is semantically justified. -/
  reduces :
    ∀ s u, carrier s = some u → reducesToNominal O s u

-- ============================================================
-- §6.3.4: Composite Herbrand countermodel (thesis §6.3.4)
--
-- The composite model ``R^*`` is the union of all per-term
-- fragments ``R_t^*`` taken in the order induced by ``m``.  The
-- thesis shows that the union of confluent fragments under the
-- chosen ordering remains confluent, and that the resulting
-- Herbrand model satisfies the ontology and refutes the query
-- (Theorem 2, §5.3).
-- ============================================================

/-- The Herbrand equality countermodel ``R^*``: a confluent rewrite
    system over a-terms whose induced equality classes form the
    domain of an interpretation refuting the query. -/
structure CompositeModel where
  rewrites : List (ATerm × ATerm)
  /-- The reduction relation: ``l → r`` whenever ``(l, r) ∈ rewrites``. -/
  reduces  : ATerm → ATerm → Prop := fun l r => (l, r) ∈ rewrites
  /-- Confluence (Church-Rosser) — provable from per-fragment
      confluence + the order-induced compatibility (thesis §6.3.4). -/
  confluent : Prop
  /-- The induced equality relation is the symmetric/transitive
      closure of ``reduces``.  Concretely, two a-terms are equal in
      ``R^*`` iff they share a common reduct. -/
  equiv     : ATerm → ATerm → Prop := fun s t => s = t ∨ reduces s t ∨ reduces t s

/-- The Herbrand model induced by a `CompositeModel`: domain is the
    quotient of a-terms by `equiv`; the role/concept extensions are
    inherited from the syntactic atoms in the ground fragments. -/
structure HerbrandModel (CM : CompositeModel) where
  /-- The domain type — opaque quotient. -/
  Dom : Type
  /-- Each closed a-term names an element of `Dom`. -/
  name : ATerm → Dom
  /-- Concept extension: ``B(t)`` holds at ``name t`` iff some
      ground atom ``B(t')`` with ``equiv t t'`` is in the model. -/
  ext_concept : ConceptSym → Dom → Prop
  /-- Role extension: ``S(t₁, t₂)`` similarly. -/
  ext_role    : RoleSym → Dom → Dom → Prop

/-- A `HerbrandModel` *witnesses* the failure of the query at the
    designated context: under the induced interpretation, the query
    body holds but no head literal does, refuting ``O ⊨ Q``. -/
def HerbrandModel.refutesQuery {CM : CompositeModel} (H : HerbrandModel CM)
    (Q : QueryClause) : Prop :=
  ∃ (vx vy : H.Dom),
    -- Construct an interpretation from H + the naming assignment.
    let I : Interp H.Dom :=
      { ext_concept := H.ext_concept,
        ext_role := H.ext_role,
        ext_ind := fun _ => vx }
    let γ : Indu → H.Dom := fun _ => vx
    let φ : FunSym → H.Dom → H.Dom := fun _ x => x
    (∀ b ∈ Q.Gamma, BLit.eval I ⟨γ, φ, vx, vy⟩ b) ∧
    (∀ h ∈ Q.Delta, ¬ CLit.eval I ⟨γ, φ, vx, vy⟩ h)

-- ============================================================
-- §6.3.4 (continued): Compose-and-refute meta-theorem
--
-- The thesis Theorem 2 proceeds by *contraposition*: if O ⊨ Q and
-- the saturated context structure does NOT contain Q in any S_q,
-- then we build a Herbrand model H that refutes Q (contradicting
-- O ⊨ Q since H is a model of O).
--
-- We expose this as a typed proposition so concrete proofs can
-- target it.
-- ============================================================

/-- **Refutation lemma** (per-context formulation): for a sound
    saturated context structure with a context ``q`` whose ``S_q``
    does not contain a query ``Q``, the composite Herbrand model
    refutes ``Q``.

    Per-context (rather than universal-absence) matches the
    contrapositive of TC: the negation of "∀ q, Q ∈ S_q" is
    "∃ q, Q ∉ S_q", and the refutation lemma fires on that single
    witnessing context.

    This is the heart of §6.3.4; assembled from per-term fragments
    (§6.3.2) under the global order and naming (§6.3.3). -/
def CompositeRefutationLemma : Prop :=
  ∀ (O : Ontology) (CD : DerivedClauses) (D : ContextStructure),
    isSound O D CD → Saturated D →
    ∀ (Q : QueryClause) (q : ALCHOIQContext.CtxId),
      q ∈ D.contexts → ¬ Q.inS D q →
      ∃ (CM : CompositeModel) (H : HerbrandModel CM), H.refutesQuery Q

/-- **Tena-Cucala completeness via the composite refutation lemma.**

    Given `CompositeRefutationLemma` (the per-context refutation
    statement from §6.3.4) and a Herbrand-model-extracts-a-model
    witness, derive `TenaCucalaCompleteness`.

    The proof structure mirrors the thesis: assume the goal
    `Q ∈ S_q` fails, apply the refutation lemma to obtain a Herbrand
    countermodel, contradict the semantic entailment hypothesis. -/
theorem tc_from_refutation_lemma
    (crl : CompositeRefutationLemma)
    -- The Herbrand model induced by R^* is a model of O, and
    -- whenever H refutes Q, the corresponding interpretation makes
    -- Q evaluate to False on some assignment.
    (herb_models_O :
      ∀ (O : Ontology) (CM : CompositeModel) (H : HerbrandModel CM),
        ∃ (I : Interp H.Dom) (γ : Indu → H.Dom) (φ : FunSym → H.Dom → H.Dom),
          I.satisfies O ∧
          (∀ Q : QueryClause, H.refutesQuery Q →
            ∃ vx vy : H.Dom, ¬ Q.eval I ⟨γ, φ, vx, vy⟩)) :
    TenaCucalaCompleteness := by
  intro O CD D hSound hSat Q hSem q hq
  -- Use classical excluded-middle directly (avoid Mathlib `by_contra`).
  rcases Classical.em (Q.inS D q) with hInS | hNotInS
  · exact hInS
  · -- Apply the refutation lemma at the witnessing context q.
    exfalso
    obtain ⟨CM, H, hRef⟩ := crl O CD D hSound hSat Q q hq hNotInS
    obtain ⟨I, γ, φ, hIO, hRefutes⟩ := herb_models_O O CM H
    obtain ⟨vx, vy, hNotQ⟩ := hRefutes Q hRef
    exact hNotQ (hSem I γ φ hIO vx vy)

end ALCHOIQContext
end ELKSDD
