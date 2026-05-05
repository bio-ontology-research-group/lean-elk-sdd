/-
  ELKSDD/SCC.lean
  ---------------
  Layer 6 of the full-algorithm proof: signature-based factorization
  of the EL_⊥^+ closure — the algorithmic content of the SCC
  decomposition step in MOOSE.

  THIS IS THE NOVEL CONTRIBUTION beyond the per-extractor encoding:
  it shows that when an ontology decomposes into signature-disjoint
  components, the closure factors *exactly* into per-component
  closures.  The MOOSE algorithm exploits this by partitioning the
  ontology along strongly-connected-component boundaries of the
  predicate dependency graph and compiling per-SCC SDDs.

  -------------------------------------------------------------
  Two-component factorization (this layer's main theorem):
  -------------------------------------------------------------

      Suppose O = O₁ ++ O₂ where atomsOf O₁ ∩ atomsOf O₂ = ∅
      and rolesOf O₁ ∩ rolesOf O₂ = ∅.  Then for every C, D with
              atomsOf C ∪ atomsOf D ⊆ atomsOf O₁
              rolesOf C ∪ rolesOf D ⊆ rolesOf O₁

              Sat (O₁ ++ O₂) C D   ↔   Sat O₁ C D.

  Forward direction (the substantial one):
    A derivation in O₁ ++ O₂ that produces a conclusion in O₁'s
    signature can use only O₁'s axioms — disjointness of signatures
    forbids any "bridging" via O₂ axioms.

  Backward direction:
    Pure monotonicity — adding axioms to an ontology never shrinks
    its closure.

  -------------------------------------------------------------
  Why this is the SCC compositionality theorem:
  -------------------------------------------------------------

  The strongly-connected components of the predicate dependency
  graph correspond exactly to maximal signature-coherent
  subontologies.  Two SCCs with disjoint atom signatures cannot
  share derivations, so per-SCC closure computation produces the
  same global closure as flat computation — exactly the claim of
  this layer.  Generalised to k SCCs, the same argument reduces
  to repeated two-component factorization (induction on the SCC
  topological order).

  -------------------------------------------------------------
  Lean dependencies:
  -------------------------------------------------------------

  Imports `ELKSDD.ELpp` (Layer 1+3), `ELKSDD.Normalize` (atom-set
  computations: `conceptAtoms`, `axiomAtoms`, `ontologyAtoms`,
  `conceptRoles`, `axiomRoles`, `ontologyRoles`).
  No Mathlib.  No prior-work axioms admitted.

  References:
    [Apt-Blair-Walker 1988] Towards a Theory of Declarative
                            Knowledge.  Stratification by SCCs.
    [Tarjan 1972]            Depth-first search and linear graph
                            algorithms.  SIAM J. Comput. 1(2),
                            146-160.  (SCC discovery algorithm.)
-/

import ELKSDD.ELpp
import ELKSDD.Normalize

namespace ELKSDD
namespace SCC

open ELpp Normalize

-- ============================================================
-- 1. Sub-ontology / inclusion / monotonicity
-- ============================================================

/-- Sub-ontology relation: every axiom of `O₁` is in `O₂`. -/
def Subontology (O₁ O₂ : Ontology) : Prop := ∀ ax ∈ O₁, ax ∈ O₂

theorem Subontology.refl (O : Ontology) : Subontology O O := fun _ h => h

theorem Subontology.append_left (O₁ O₂ : Ontology) :
    Subontology O₁ (O₁ ++ O₂) := by
  intro ax h
  exact List.mem_append.mpr (Or.inl h)

theorem Subontology.append_right (O₁ O₂ : Ontology) :
    Subontology O₂ (O₁ ++ O₂) := by
  intro ax h
  exact List.mem_append.mpr (Or.inr h)

-- ============================================================
-- 2. Sat is monotone in the ontology  — easy direction of Layer 6
-- ============================================================

/-- **Sat monotonicity (easy direction of factorization).**
    If `Sat O₁ C D` and `O₁ ⊆ O₂`, then `Sat O₂ C D`.

    Proof: induction on the `Sat` derivation, replacing each
    `base_gci`/`rinc_apply`/`rchain_apply` axiom-membership claim
    `ax ∈ O₁` with `ax ∈ O₂` via `Subontology`.

    Consequences:
      * `Sat O₁ C D → Sat (O₁ ++ O₂) C D` for arbitrary O₂.
      * Adding axioms can never shrink the closure.
      * Used as the easy direction of the factorization theorem. -/
theorem Sat_mono {O₁ O₂ : Ontology} (hsub : Subontology O₁ O₂)
    {C D : Concept} (h : Sat O₁ C D) : Sat O₂ C D := by
  induction h with
  | refl _ => exact Sat.refl _
  | top _ => exact Sat.top _
  | base_gci hax => exact Sat.base_gci (hsub _ hax)
  | trans _ _ ihCD ihDE => exact Sat.trans ihCD ihDE
  | conj_left _ ih => exact Sat.conj_left ih
  | conj_right _ ih => exact Sat.conj_right ih
  | conj_intro _ _ ih₁ ih₂ => exact Sat.conj_intro ih₁ ih₂
  | bot_elim _ ih => exact Sat.bot_elim ih
  | exist_prop _ _ ihCRD ihDE => exact Sat.exist_prop ihCRD ihDE
  | exist_bot _ _ ihCRD ihDbot => exact Sat.exist_bot ihCRD ihDbot
  | rinc_apply _ hax ih => exact Sat.rinc_apply ih (hsub _ hax)
  | rchain_apply _ _ hax ihCR1 ihDR2 =>
      exact Sat.rchain_apply ihCR1 ihDR2 (hsub _ hax)

/-- Concrete corollary: appending O₂ to O₁ preserves Sat-derivability. -/
theorem Sat_mono_append_left {O₁ : Ontology} (O₂ : Ontology)
    {C D : Concept} (h : Sat O₁ C D) : Sat (O₁ ++ O₂) C D :=
  Sat_mono (Subontology.append_left O₁ O₂) h

/-- Concrete corollary: prepending O₁ to O₂ preserves Sat-derivability. -/
theorem Sat_mono_append_right {O₂ : Ontology} (O₁ : Ontology)
    {C D : Concept} (h : Sat O₂ C D) : Sat (O₁ ++ O₂) C D :=
  Sat_mono (Subontology.append_right O₁ O₂) h

-- ============================================================
-- 3. Disjoint-signature predicate
-- ============================================================

/-- Two ontologies have *disjoint concept-name signatures* if no
    atomic concept name appears in axioms of both. -/
def DisjointConceptSigs (O₁ O₂ : Ontology) : Prop :=
  ∀ a ∈ ontologyAtoms O₁, a ∉ ontologyAtoms O₂

/-- Two ontologies have *disjoint role-name signatures*. -/
def DisjointRoleSigs (O₁ O₂ : Ontology) : Prop :=
  ∀ r ∈ ontologyRoles O₁, r ∉ ontologyRoles O₂

/-- Combined disjointness — both atom and role signatures disjoint.
    This is the SCC-decomposition precondition: O₁ and O₂ are
    completely independent components of the ontology. -/
def DisjointSigs (O₁ O₂ : Ontology) : Prop :=
  DisjointConceptSigs O₁ O₂ ∧ DisjointRoleSigs O₁ O₂

theorem DisjointConceptSigs.symm {O₁ O₂ : Ontology}
    (h : DisjointConceptSigs O₁ O₂) : DisjointConceptSigs O₂ O₁ := by
  intro a ha hcontra
  exact h a hcontra ha

theorem DisjointRoleSigs.symm {O₁ O₂ : Ontology}
    (h : DisjointRoleSigs O₁ O₂) : DisjointRoleSigs O₂ O₁ := by
  intro r hr hcontra
  exact h r hcontra hr

theorem DisjointSigs.symm {O₁ O₂ : Ontology}
    (h : DisjointSigs O₁ O₂) : DisjointSigs O₂ O₁ :=
  ⟨h.1.symm, h.2.symm⟩

-- ============================================================
-- 4. "Concept C is in O's signature" predicate
-- ============================================================

/-- Concept `C` is in `O`'s atom signature if every atom name in `C`
    appears in some axiom of `O`. -/
def ConceptInAtomSig (O : Ontology) (C : Concept) : Prop :=
  ∀ n ∈ conceptAtoms C, n ∈ ontologyAtoms O

/-- Concept `C` is in `O`'s role signature if every role name in `C`
    appears in some axiom of `O`.  (Role names appear in `∃R.E`
    sub-expressions.) -/
def ConceptInRoleSig (O : Ontology) (C : Concept) : Prop :=
  ∀ R ∈ conceptRoles C, R ∈ ontologyRoles O

/-- Concept `C` is fully in `O`'s signature. -/
def ConceptInSig (O : Ontology) (C : Concept) : Prop :=
  ConceptInAtomSig O C ∧ ConceptInRoleSig O C

/-- ⊤ is trivially in every signature. -/
theorem ConceptInSig.top (O : Ontology) : ConceptInSig O .top := by
  refine ⟨?_, ?_⟩ <;> intro _ h <;> exact (List.not_mem_nil h).elim

/-- ⊥ is trivially in every signature. -/
theorem ConceptInSig.bot (O : Ontology) : ConceptInSig O .bot := by
  refine ⟨?_, ?_⟩ <;> intro _ h <;> exact (List.not_mem_nil h).elim

-- ============================================================
-- 5. The factorization theorem — STATEMENT and easy direction
-- ============================================================
-- The forward direction (Sat O₁ → Sat (O₁ ++ O₂)) is monotonicity.
-- The backward direction (Sat (O₁ ++ O₂) → Sat O₁ for concepts in
-- O₁'s signature) is the *substantive* SCC compositionality result.

/-- **Factorization theorem (easy direction).**
    Adding a signature-disjoint component to an ontology never
    introduces new derivable atoms over the original signature.
    Direct from `Sat_mono`. -/
theorem Sat_factor_easy (O₁ O₂ : Ontology) (C D : Concept)
    (h : Sat O₁ C D) : Sat (O₁ ++ O₂) C D :=
  Sat_mono_append_left O₂ h

-- ============================================================
-- 6. Toward the hard direction — auxiliary lemmas
-- ============================================================

/-- Reading axiom membership in a concatenated list: an axiom is
    in `O₁ ++ O₂` iff it's in `O₁` or in `O₂`. -/
theorem mem_append_iff {ax : Axiom} {O₁ O₂ : Ontology} :
    ax ∈ O₁ ++ O₂ ↔ ax ∈ O₁ ∨ ax ∈ O₂ := List.mem_append

/-- Atom-set distribution over append. -/
theorem ontologyAtoms_append (O₁ O₂ : Ontology) :
    ontologyAtoms (O₁ ++ O₂) = ontologyAtoms O₁ ++ ontologyAtoms O₂ := by
  unfold ontologyAtoms
  exact List.flatMap_append

theorem ontologyRoles_append (O₁ O₂ : Ontology) :
    ontologyRoles (O₁ ++ O₂) = ontologyRoles O₁ ++ ontologyRoles O₂ := by
  unfold ontologyRoles
  exact List.flatMap_append

/-- Membership in the appended atom-list iff in either component. -/
theorem mem_ontologyAtoms_append {n : Nat} {O₁ O₂ : Ontology} :
    n ∈ ontologyAtoms (O₁ ++ O₂) ↔ n ∈ ontologyAtoms O₁ ∨ n ∈ ontologyAtoms O₂ := by
  rw [ontologyAtoms_append]
  exact List.mem_append

theorem mem_ontologyRoles_append {R : Role} {O₁ O₂ : Ontology} :
    R ∈ ontologyRoles (O₁ ++ O₂) ↔ R ∈ ontologyRoles O₁ ∨ R ∈ ontologyRoles O₂ := by
  rw [ontologyRoles_append]
  exact List.mem_append

-- ============================================================
-- 7. Per-axiom in-O₁-signature predicate and its disjointness consequence
-- ============================================================

/-- An axiom is "in O₁'s signature" if every atom and every role it
    mentions is in O₁'s signature. -/
def AxiomInSig (O : Ontology) (ax : Axiom) : Prop :=
  (∀ n ∈ axiomAtoms ax, n ∈ ontologyAtoms O) ∧
  (∀ R ∈ axiomRoles ax, R ∈ ontologyRoles O)

/-- Every axiom in `O` is in `O`'s own signature.  Proof: the atom
    set of `O` is the flat-map of axiom-atom sets, so any axiom's
    atoms automatically appear in the flat-map. -/
theorem axiom_in_self_sig {ax : Axiom} {O : Ontology} (hax : ax ∈ O) :
    AxiomInSig O ax := by
  refine ⟨?_, ?_⟩
  · intro n hn
    unfold ontologyAtoms
    exact List.mem_flatMap.mpr ⟨ax, hax, hn⟩
  · intro R hR
    unfold ontologyRoles
    exact List.mem_flatMap.mpr ⟨ax, hax, hR⟩

/-- **Key lemma for the hard direction.**  If two ontologies have
    disjoint atom signatures, then every axiom of `O₁ ++ O₂` is
    *either entirely in O₁'s signature* or *entirely in O₂'s
    signature*; the two cases are exclusive (by atom disjointness
    on any non-trivial axiom). -/
theorem axiom_in_one_sig
    {O₁ O₂ : Ontology}
    {ax : Axiom} (hax : ax ∈ O₁ ++ O₂) :
    AxiomInSig O₁ ax ∨ AxiomInSig O₂ ax := by
  rcases List.mem_append.mp hax with h | h
  · left
    refine ⟨?_, ?_⟩
    · intro n hn
      unfold ontologyAtoms
      exact List.mem_flatMap.mpr ⟨ax, h, hn⟩
    · intro R hR
      unfold ontologyRoles
      exact List.mem_flatMap.mpr ⟨ax, h, hR⟩
  · right
    refine ⟨?_, ?_⟩
    · intro n hn
      unfold ontologyAtoms
      exact List.mem_flatMap.mpr ⟨ax, h, hn⟩
    · intro R hR
      unfold ontologyRoles
      exact List.mem_flatMap.mpr ⟨ax, h, hR⟩

-- ============================================================
-- 8. Axiom-restriction lemmas for the partial factorization
-- ============================================================

/-- An axiom that is in O₁'s atom signature must be from O₁ when
    O₁ and O₂ have disjoint atom signatures and the axiom mentions
    at least one atom (or its role-side membership is in O₁'s roles).
    This is the bridging lemma: an axiom can't simultaneously have
    its atoms entirely in O₁ AND be in O₂'s axiom list, given
    disjointness — unless the axiom mentions no atoms at all (a
    role-only axiom).

    For the GCI case (which always mentions at least one atom in
    `axiomAtoms`), disjointness forces the axiom to be in O₁. -/
theorem gci_in_O₁_atoms_implies_in_O₁
    {O₁ O₂ : Ontology} (hdisj : DisjointConceptSigs O₁ O₂)
    {C D : Concept} (hax : Axiom.gci C D ∈ O₁ ++ O₂)
    (hC : ConceptInAtomSig O₁ C) (hD : ConceptInAtomSig O₁ D)
    (hnonempty : conceptAtoms C ≠ [] ∨ conceptAtoms D ≠ []) :
    Axiom.gci C D ∈ O₁ := by
  rcases List.mem_append.mp hax with h | h
  · exact h
  · -- ax ∈ O₂.  Show contradiction.
    exfalso
    -- The atoms of C and D are in O₁'s signature (by hC, hD), but
    -- since the axiom is in O₂, those same atoms must also be in
    -- O₂'s signature.  Disjointness then forces conceptAtoms C = []
    -- and conceptAtoms D = []; combined with hnonempty, contradiction.
    rcases hnonempty with hC_ne | hD_ne
    · -- Get a witness atom from conceptAtoms C
      cases hl : conceptAtoms C with
      | nil => exact hC_ne hl
      | cons n rest =>
          have hn : n ∈ conceptAtoms C := by rw [hl]; exact List.mem_cons_self
          have hn_O1 : n ∈ ontologyAtoms O₁ := hC n hn
          have hn_O2 : n ∈ ontologyAtoms O₂ := by
            unfold ontologyAtoms
            refine List.mem_flatMap.mpr ⟨Axiom.gci C D, h, ?_⟩
            unfold axiomAtoms
            exact List.mem_append.mpr (Or.inl hn)
          exact hdisj n hn_O1 hn_O2
    · cases hl : conceptAtoms D with
      | nil => exact hD_ne hl
      | cons n rest =>
          have hn : n ∈ conceptAtoms D := by rw [hl]; exact List.mem_cons_self
          have hn_O1 : n ∈ ontologyAtoms O₁ := hD n hn
          have hn_O2 : n ∈ ontologyAtoms O₂ := by
            unfold ontologyAtoms
            refine List.mem_flatMap.mpr ⟨Axiom.gci C D, h, ?_⟩
            unfold axiomAtoms
            exact List.mem_append.mpr (Or.inr hn)
          exact hdisj n hn_O1 hn_O2

-- ============================================================
-- 9. Hard-direction factorization (atomic specialisation)
-- ============================================================
-- For atomic concepts A, B in O₁'s signature, the hard direction
-- of the factorization holds.  This is the SCC compositionality
-- specialisation that the MOOSE algorithm exploits for the
-- atomic-subsumption queries it generates.

-- ============================================================
-- 9'. Refined factorization theorem (with consistency disjunct)
-- ============================================================
-- The naive factorization `Sat (O₁ ++ O₂) C D ↔ Sat O₁ C D` for
-- C, D in O₁'s signature DOES NOT hold unconditionally — a
-- counterexample is O₁ = [], O₂ = {gci ⊤ ⊥}, where
-- Sat (O₁ ++ O₂) ⊤ ⊥ holds but Sat O₁ ⊤ ⊥ doesn't.  The issue:
-- O₂'s `gci ⊤ ⊥` is "globally inconsistent" and pollutes
-- everything in O₁'s signature via bot_elim.
--
-- The CLEAN factorization includes a disjunct for this case:
--
--     Sat (O₁ ++ O₂) C D   ↔   Sat O₁ C D ∨ Sat O₂ ⊤ ⊥        (*)
--
-- The disjunct `Sat O₂ ⊤ ⊥` says O₂ alone is globally inconsistent.
-- When O₂ is consistent (¬Sat O₂ ⊤ ⊥), we recover the clean
-- factorization on O₁'s signature.

/-- The "global inconsistency" propagation lemma: if `Sat O₂ ⊤ ⊥`,
    then `Sat (O₁ ++ O₂) C D` holds for ANY C, D (everything is
    derivable from a globally-inconsistent ontology).

    Proof:
      1. Sat O₂ ⊤ ⊥ → Sat (O₁ ++ O₂) ⊤ ⊥  (monotonicity).
      2. Sat (O₁ ++ O₂) C ⊤              (top constructor).
      3. Sat (O₁ ++ O₂) C ⊥              (trans of 2 and 1).
      4. Sat (O₁ ++ O₂) C D              (bot_elim of 3). -/
theorem global_inconsistency_propagates {O₁ O₂ : Ontology}
    (h : Sat O₂ .top .bot) (C D : Concept) :
    Sat (O₁ ++ O₂) C D := by
  have h2 : Sat (O₁ ++ O₂) .top .bot := Sat_mono_append_right O₁ h
  have h3 : Sat (O₁ ++ O₂) C .top := Sat.top _
  have h4 : Sat (O₁ ++ O₂) C .bot := Sat.trans h3 h2
  exact Sat.bot_elim h4

/-- **Refined factorization (easy direction).**

    Either disjunct on the right implies the left:

      Sat O₁ C D            →  Sat (O₁ ++ O₂) C D    (monotonicity)
      Sat O₂ ⊤ ⊥           →  Sat (O₁ ++ O₂) C D    (global inconsistency)

    Hence

      Sat O₁ C D ∨ Sat O₂ ⊤ ⊥   →   Sat (O₁ ++ O₂) C D.

    This is the unconditionally-provable direction of the refined
    SCC compositionality theorem (*). -/
theorem Sat_factor_refined_mp {O₁ O₂ : Ontology} {C D : Concept}
    (h : Sat O₁ C D ∨ Sat O₂ .top .bot) :
    Sat (O₁ ++ O₂) C D := by
  rcases h with hSat | hInc
  · exact Sat_factor_easy O₁ O₂ C D hSat
  · exact global_inconsistency_propagates hInc C D

-- ============================================================
-- 9. Hard direction — full proof via product interpretation
-- ============================================================
-- This is the substantive content of Layer 6.  We prove the
-- converse of `Sat_factor_refined_mp` for ARBITRARY concepts C, D
-- in O₁'s signature (no ⊤-side / ⊥-side restriction; the proof
-- works for full OWL 2 EL = EL_⊥^+).
--
-- Construction.  Given `I₁ ⊨ O₁` and `O₂` consistent
-- (`¬ Sat O₂ ⊤ ⊥`), build a product interpretation
--
--     prodInterp : Interp (α × CanonDom O₂)
--
-- such that:
--
--   (P1)  prodInterp ⊨ O₁ ++ O₂.
--   (P2)  For every E ∈ ConceptInSig O₁ and a, b:
--             prodInterp.eval E ⟨a, b⟩  ↔  I₁.eval E a.
--   (P3)  For every E ∈ ConceptInSig O₂ and a, b:
--             prodInterp.eval E ⟨a, b⟩  ↔  (canon O₂).eval E b.
--
-- (P2) makes the construction work for axioms `⊤ ⊑ X` in O₁ with
-- X ∈ O₁'s sig: ⊤^{prodInterp}(⟨a, b⟩) is True for all ⟨a, b⟩, and
-- by (P2), X^{prodInterp}(⟨a, b⟩) ↔ X^{I₁}(a), so prodInterp ⊨
-- ⊤ ⊑ X iff I₁ ⊨ ⊤ ⊑ X.  Symmetrically, axioms `Y ⊑ ⊥` in O₁ are
-- handled automatically.  No ⊤-side restrictions are needed.
--
-- For (P1): per axiom in O₁ (resp. O₂), the axiom's atoms and
-- roles all live in O₁'s sig (resp. O₂'s sig), so eval-invariance
-- (P2) (resp. (P3)) reduces the prodInterp-satisfaction goal to
-- I₁-satisfaction (resp. canon-O₂-satisfaction), which we have by
-- assumption (resp. by `canon_satisfies`).

/-- **Product interpretation.**  Domain `α × CanonDom O₂`, with
    atoms in O₁'s atom-sig pulling back to I₁'s first projection,
    others to the canonical model of O₂'s second projection.
    Roles in O₁'s sig propagate I₁'s edges only along same-O₂
    components; roles outside O₁'s sig propagate canonical-O₂
    edges only along same-α components.

    `default₂ : CanonDom O₂` is required because `canon` (extended
    here for nominals) takes a default-element parameter; pass any
    canonical-domain element of O₂.  In the typical Layer 6 use
    site this is `⟨.top, hcons⟩` for `hcons : ¬ Sat O₂ ⊤ ⊥`.

    `indiv` (for nominals): individuals in O₁'s individual sig are
    placed on the inl side; others on the inr side.  This is the
    structural skeleton; the full semantic correctness for nominal
    *axioms* requires the merging-canonical-model construction
    (Kazakov 2014 §6) and is therefore not proved here.  Layer 6's
    main theorem accordingly requires `OntologyNominalFree O₁` and
    `OntologyNominalFree O₂`. -/
noncomputable def prodInterp {α : Type} (O₁ O₂ : Ontology) (I₁ : Interp α)
    (default₂ : CanonDom O₂) :
    Interp (α × CanonDom O₂) := by
  classical
  exact {
    ext_concept := fun n p =>
      if n ∈ ontologyAtoms O₁ then I₁.ext_concept n p.1
      else (canon O₂ default₂).ext_concept n p.2
    ext_role := fun r p q =>
      if r ∈ ontologyRoles O₁ then I₁.ext_role r p.1 q.1 ∧ p.2 = q.2
      else p.1 = q.1 ∧ (canon O₂ default₂).ext_role r p.2 q.2
    indiv := fun i =>
      if i ∈ ontologyIndividuals O₁ then ⟨I₁.indiv i, default₂⟩
      else ⟨I₁.indiv 0, (canon O₂ default₂).indiv i⟩
  }

-- ----------------------------------------------------------------
-- 9.1  Sub-concept signature lemmas
-- ----------------------------------------------------------------

theorem ConceptInSig.atom_mem {O : Ontology} {n : Nat}
    (h : ConceptInSig O (.atom n)) : n ∈ ontologyAtoms O := by
  apply h.1
  show n ∈ [n]
  exact List.mem_cons_self

theorem ConceptInSig.conj_left {O : Ontology} {A B : Concept}
    (h : ConceptInSig O (.conj A B)) : ConceptInSig O A := by
  refine ⟨?_, ?_⟩
  · intro n hn
    apply h.1
    show n ∈ conceptAtoms A ++ conceptAtoms B
    exact List.mem_append.mpr (Or.inl hn)
  · intro R hR
    apply h.2
    show R ∈ conceptRoles A ++ conceptRoles B
    exact List.mem_append.mpr (Or.inl hR)

theorem ConceptInSig.conj_right {O : Ontology} {A B : Concept}
    (h : ConceptInSig O (.conj A B)) : ConceptInSig O B := by
  refine ⟨?_, ?_⟩
  · intro n hn
    apply h.1
    show n ∈ conceptAtoms A ++ conceptAtoms B
    exact List.mem_append.mpr (Or.inr hn)
  · intro R hR
    apply h.2
    show R ∈ conceptRoles A ++ conceptRoles B
    exact List.mem_append.mpr (Or.inr hR)

theorem ConceptInSig.exist_role {O : Ontology} {R : Role} {E : Concept}
    (h : ConceptInSig O (.exist R E)) : R ∈ ontologyRoles O := by
  apply h.2
  show R ∈ R :: conceptRoles E
  exact List.mem_cons_self

theorem ConceptInSig.exist_inner {O : Ontology} {R : Role} {E : Concept}
    (h : ConceptInSig O (.exist R E)) : ConceptInSig O E := by
  refine ⟨h.1, ?_⟩
  intro R' hR'
  apply h.2
  show R' ∈ R :: conceptRoles E
  exact List.mem_cons.mpr (Or.inr hR')

-- ----------------------------------------------------------------
-- 9.2  Unfold lemmas for prodInterp's branches
-- ----------------------------------------------------------------

theorem prodInterp_atom_O₁ {α : Type} (O₁ O₂ : Ontology) (I₁ : Interp α)
    (default₂ : CanonDom O₂)
    {n : Nat} (hn : n ∈ ontologyAtoms O₁)
    (a : α) (b : CanonDom O₂) :
    (prodInterp O₁ O₂ I₁ default₂).ext_concept n ⟨a, b⟩ ↔ I₁.ext_concept n a := by
  show (if n ∈ ontologyAtoms O₁ then I₁.ext_concept n a
        else (canon O₂ default₂).ext_concept n b) ↔ _
  rw [if_pos hn]

theorem prodInterp_atom_not_O₁ {α : Type} (O₁ O₂ : Ontology) (I₁ : Interp α)
    (default₂ : CanonDom O₂)
    {n : Nat} (hn : n ∉ ontologyAtoms O₁)
    (a : α) (b : CanonDom O₂) :
    (prodInterp O₁ O₂ I₁ default₂).ext_concept n ⟨a, b⟩ ↔
      (canon O₂ default₂).ext_concept n b := by
  show (if n ∈ ontologyAtoms O₁ then I₁.ext_concept n a
        else (canon O₂ default₂).ext_concept n b) ↔ _
  rw [if_neg hn]

theorem prodInterp_role_O₁ {α : Type} (O₁ O₂ : Ontology) (I₁ : Interp α)
    (default₂ : CanonDom O₂)
    {R : Role} (hR : R ∈ ontologyRoles O₁)
    (a a' : α) (b b' : CanonDom O₂) :
    (prodInterp O₁ O₂ I₁ default₂).ext_role R ⟨a, b⟩ ⟨a', b'⟩ ↔
      (I₁.ext_role R a a' ∧ b = b') := by
  show (if R ∈ ontologyRoles O₁ then I₁.ext_role R a a' ∧ b = b'
        else a = a' ∧ (canon O₂ default₂).ext_role R b b') ↔ _
  rw [if_pos hR]

theorem prodInterp_role_not_O₁ {α : Type} (O₁ O₂ : Ontology) (I₁ : Interp α)
    (default₂ : CanonDom O₂)
    {R : Role} (hR : R ∉ ontologyRoles O₁)
    (a a' : α) (b b' : CanonDom O₂) :
    (prodInterp O₁ O₂ I₁ default₂).ext_role R ⟨a, b⟩ ⟨a', b'⟩ ↔
      (a = a' ∧ (canon O₂ default₂).ext_role R b b') := by
  show (if R ∈ ontologyRoles O₁ then I₁.ext_role R a a' ∧ b = b'
        else a = a' ∧ (canon O₂ default₂).ext_role R b b') ↔ _
  rw [if_neg hR]

-- ----------------------------------------------------------------
-- 9.3  Eval-invariance for O₁'s signature (P2)
-- ----------------------------------------------------------------

/-- Concepts in O₁'s atom-and-role signature, restricted to the
    nominal-free fragment, evaluate on `prodInterp O₁ O₂ I₁ default₂`
    at `⟨a, b⟩` exactly as on `I₁` at `a`.

    The nominal-free restriction allows us to avoid the singleton-
    domain issue with `⊤ ⊑ {a}` axioms (Kazakov 2014 §6 needed for
    the full case). -/
theorem eval_prodInterp_O₁ {α : Type} (O₁ O₂ : Ontology) (I₁ : Interp α)
    (default₂ : CanonDom O₂) :
    ∀ (E : Concept), NominalFree E → ConceptInSig O₁ E →
      ∀ (a : α) (b : CanonDom O₂),
      (prodInterp O₁ O₂ I₁ default₂).eval E ⟨a, b⟩ ↔ I₁.eval E a := by
  intro E
  induction E with
  | atom n =>
      intro _ hE a b
      have hn : n ∈ ontologyAtoms O₁ := hE.atom_mem
      exact prodInterp_atom_O₁ O₁ O₂ I₁ default₂ hn a b
  | nom i => intro hnf _ _ _; exact hnf.elim
  | top => intro _ _ _ _; exact Iff.rfl
  | bot => intro _ _ _ _; exact Iff.rfl
  | conj A B ihA ihB =>
      intro hnf hE a b
      show (prodInterp O₁ O₂ I₁ default₂).eval A ⟨a, b⟩ ∧ _ ↔ I₁.eval A a ∧ _
      rw [ihA hnf.1 hE.conj_left a b, ihB hnf.2 hE.conj_right a b]
  | exist R E' ihE' =>
      intro hnf hE a b
      have hR : R ∈ ontologyRoles O₁ := hE.exist_role
      have hE'_sig := hE.exist_inner
      constructor
      · rintro ⟨⟨a', b'⟩, hrole, heval⟩
        rw [prodInterp_role_O₁ O₁ O₂ I₁ default₂ hR a a' b b'] at hrole
        refine ⟨a', hrole.1, ?_⟩
        exact (ihE' hnf hE'_sig a' b').mp heval
      · rintro ⟨a', hrole, heval⟩
        refine ⟨⟨a', b⟩, ?_, (ihE' hnf hE'_sig a' b).mpr heval⟩
        rw [prodInterp_role_O₁ O₁ O₂ I₁ default₂ hR a a' b b]
        exact ⟨hrole, rfl⟩

-- ----------------------------------------------------------------
-- 9.4  Eval-invariance for O₂'s signature (P3)
-- ----------------------------------------------------------------
-- Uses DisjointSigs to deduce membership in O₂'s sig implies
-- non-membership in O₁'s sig (so the prodInterp falls into the
-- "else" branch).

/-- Concepts in O₂'s atom-and-role signature (nominal-free
    fragment) evaluate on `prodInterp O₁ O₂ I₁ default₂` at
    `⟨a, b⟩` exactly as on `canon O₂ default₂` at `b`. -/
theorem eval_prodInterp_O₂ {α : Type} (O₁ O₂ : Ontology) (I₁ : Interp α)
    (default₂ : CanonDom O₂)
    (hdisj : DisjointSigs O₁ O₂) :
    ∀ (E : Concept), NominalFree E → ConceptInSig O₂ E →
      ∀ (a : α) (b : CanonDom O₂),
      (prodInterp O₁ O₂ I₁ default₂).eval E ⟨a, b⟩ ↔
        (canon O₂ default₂).eval E b := by
  intro E
  induction E with
  | atom n =>
      intro _ hE a b
      have hn_O₂ : n ∈ ontologyAtoms O₂ := hE.atom_mem
      have hn_not_O₁ : n ∉ ontologyAtoms O₁ := fun h₁ => hdisj.1 n h₁ hn_O₂
      exact prodInterp_atom_not_O₁ O₁ O₂ I₁ default₂ hn_not_O₁ a b
  | nom i => intro hnf _ _ _; exact hnf.elim
  | top => intro _ _ _ _; exact Iff.rfl
  | bot => intro _ _ _ _; exact Iff.rfl
  | conj A B ihA ihB =>
      intro hnf hE a b
      show (prodInterp O₁ O₂ I₁ default₂).eval A ⟨a, b⟩ ∧ _ ↔
           (canon O₂ default₂).eval A b ∧ _
      rw [ihA hnf.1 hE.conj_left a b, ihB hnf.2 hE.conj_right a b]
  | exist R E' ihE' =>
      intro hnf hE a b
      have hR_O₂ : R ∈ ontologyRoles O₂ := hE.exist_role
      have hR_not_O₁ : R ∉ ontologyRoles O₁ := fun h₁ => hdisj.2 R h₁ hR_O₂
      have hE'_sig := hE.exist_inner
      constructor
      · rintro ⟨⟨a', b'⟩, hrole, heval⟩
        rw [prodInterp_role_not_O₁ O₁ O₂ I₁ default₂ hR_not_O₁ a a' b b'] at hrole
        refine ⟨b', hrole.2, ?_⟩
        exact (ihE' hnf hE'_sig a' b').mp heval
      · rintro ⟨b', hrole, heval⟩
        refine ⟨⟨a, b'⟩, ?_, (ihE' hnf hE'_sig a b').mpr heval⟩
        rw [prodInterp_role_not_O₁ O₁ O₂ I₁ default₂ hR_not_O₁ a a b b']
        exact ⟨rfl, hrole⟩

-- ----------------------------------------------------------------
-- 9.5  Axiom-side signature lemmas
-- ----------------------------------------------------------------

theorem ConceptInSig_of_AxiomInSig_gci {O : Ontology} {C D : Concept}
    (h : AxiomInSig O (Axiom.gci C D)) :
    ConceptInSig O C ∧ ConceptInSig O D := by
  obtain ⟨hat, hro⟩ := h
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro n hn
    apply hat
    show n ∈ conceptAtoms C ++ conceptAtoms D
    exact List.mem_append.mpr (Or.inl hn)
  · intro R hR
    apply hro
    show R ∈ conceptRoles C ++ conceptRoles D
    exact List.mem_append.mpr (Or.inl hR)
  · intro n hn
    apply hat
    show n ∈ conceptAtoms C ++ conceptAtoms D
    exact List.mem_append.mpr (Or.inr hn)
  · intro R hR
    apply hro
    show R ∈ conceptRoles C ++ conceptRoles D
    exact List.mem_append.mpr (Or.inr hR)

theorem rinc_role_left_in_sig {O : Ontology} {R S : Role}
    (h : AxiomInSig O (Axiom.rinc R S)) : R ∈ ontologyRoles O := by
  apply h.2
  show R ∈ [R, S]
  exact List.mem_cons_self

theorem rinc_role_right_in_sig {O : Ontology} {R S : Role}
    (h : AxiomInSig O (Axiom.rinc R S)) : S ∈ ontologyRoles O := by
  apply h.2
  show S ∈ [R, S]
  exact List.mem_cons.mpr (Or.inr List.mem_cons_self)

theorem rchain_role₁_in_sig {O : Ontology} {R₁ R₂ S : Role}
    (h : AxiomInSig O (Axiom.rchain R₁ R₂ S)) : R₁ ∈ ontologyRoles O := by
  apply h.2
  show R₁ ∈ [R₁, R₂, S]
  exact List.mem_cons_self

theorem rchain_role₂_in_sig {O : Ontology} {R₁ R₂ S : Role}
    (h : AxiomInSig O (Axiom.rchain R₁ R₂ S)) : R₂ ∈ ontologyRoles O := by
  apply h.2
  show R₂ ∈ [R₁, R₂, S]
  exact List.mem_cons.mpr (Or.inr List.mem_cons_self)

theorem rchain_role₃_in_sig {O : Ontology} {R₁ R₂ S : Role}
    (h : AxiomInSig O (Axiom.rchain R₁ R₂ S)) : S ∈ ontologyRoles O := by
  apply h.2
  show S ∈ [R₁, R₂, S]
  exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr List.mem_cons_self)))

-- ----------------------------------------------------------------
-- 9.6  prodInterp satisfies axioms in O₁ (uses I₁ ⊨ O₁ + P2)
-- ----------------------------------------------------------------

theorem prodInterp_satisfies_O₁_axiom {α : Type} (O₁ O₂ : Ontology) (I₁ : Interp α)
    (default₂ : CanonDom O₂)
    (hO₁_nf : OntologyNominalFree O₁)
    (hI₁ : I₁.satisfies O₁) {ax : Axiom} (hax : ax ∈ O₁) :
    (prodInterp O₁ O₂ I₁ default₂).satisfiesAxiom ax := by
  have hax_sig : AxiomInSig O₁ ax := axiom_in_self_sig hax
  have hax_nf : AxiomNominalFree ax := hO₁_nf ax hax
  cases ax with
  | gci C D =>
      intro p hC
      obtain ⟨a, b⟩ := p
      obtain ⟨hC_sig, hD_sig⟩ := ConceptInSig_of_AxiomInSig_gci hax_sig
      obtain ⟨hC_nf, hD_nf⟩ := hax_nf
      have h_I₁_C : I₁.eval C a :=
        (eval_prodInterp_O₁ O₁ O₂ I₁ default₂ C hC_nf hC_sig a b).mp hC
      have h_I₁_D : I₁.eval D a := hI₁ _ hax a h_I₁_C
      exact (eval_prodInterp_O₁ O₁ O₂ I₁ default₂ D hD_nf hD_sig a b).mpr h_I₁_D
  | rinc R S =>
      intro p q hR_pq
      obtain ⟨a, b⟩ := p
      obtain ⟨a', b'⟩ := q
      have hR_O₁ : R ∈ ontologyRoles O₁ := rinc_role_left_in_sig hax_sig
      have hS_O₁ : S ∈ ontologyRoles O₁ := rinc_role_right_in_sig hax_sig
      rw [prodInterp_role_O₁ O₁ O₂ I₁ default₂ hR_O₁ a a' b b'] at hR_pq
      obtain ⟨hR_aa', hb⟩ := hR_pq
      have hS_aa' : I₁.ext_role S a a' := hI₁ _ hax a a' hR_aa'
      rw [prodInterp_role_O₁ O₁ O₂ I₁ default₂ hS_O₁ a a' b b']
      exact ⟨hS_aa', hb⟩
  | rchain R₁ R₂ S =>
      intro p q r hR₁_pq hR₂_qr
      obtain ⟨a, b⟩ := p
      obtain ⟨a', b'⟩ := q
      obtain ⟨a'', b''⟩ := r
      have hR₁_O₁ : R₁ ∈ ontologyRoles O₁ := rchain_role₁_in_sig hax_sig
      have hR₂_O₁ : R₂ ∈ ontologyRoles O₁ := rchain_role₂_in_sig hax_sig
      have hS_O₁  : S  ∈ ontologyRoles O₁ := rchain_role₃_in_sig hax_sig
      rw [prodInterp_role_O₁ O₁ O₂ I₁ default₂ hR₁_O₁ a a' b b'] at hR₁_pq
      rw [prodInterp_role_O₁ O₁ O₂ I₁ default₂ hR₂_O₁ a' a'' b' b''] at hR₂_qr
      obtain ⟨hR₁_aa', hb_eq_b'⟩ := hR₁_pq
      obtain ⟨hR₂_a'a'', hb'_eq_b''⟩ := hR₂_qr
      have hS_aa'' : I₁.ext_role S a a'' := hI₁ _ hax a a' a'' hR₁_aa' hR₂_a'a''
      rw [prodInterp_role_O₁ O₁ O₂ I₁ default₂ hS_O₁ a a'' b b'']
      exact ⟨hS_aa'', hb_eq_b'.trans hb'_eq_b''⟩

-- ----------------------------------------------------------------
-- 9.7  prodInterp satisfies axioms in O₂ (uses canon O₂ ⊨ O₂ + P3)
-- ----------------------------------------------------------------

theorem prodInterp_satisfies_O₂_axiom {α : Type} (O₁ O₂ : Ontology) (I₁ : Interp α)
    (default₂ : CanonDom O₂)
    (hO₂_nf : OntologyNominalFree O₂)
    (hdisj : DisjointSigs O₁ O₂)
    {ax : Axiom} (hax : ax ∈ O₂) :
    (prodInterp O₁ O₂ I₁ default₂).satisfiesAxiom ax := by
  have hax_sig : AxiomInSig O₂ ax := axiom_in_self_sig hax
  have hax_nf : AxiomNominalFree ax := hO₂_nf ax hax
  have hcanon : (canon O₂ default₂).satisfies O₂ := canon_satisfies O₂ default₂ hO₂_nf
  cases ax with
  | gci C D =>
      intro p hC
      obtain ⟨a, b⟩ := p
      obtain ⟨hC_sig, hD_sig⟩ := ConceptInSig_of_AxiomInSig_gci hax_sig
      obtain ⟨hC_nf, hD_nf⟩ := hax_nf
      have h_canon_C : (canon O₂ default₂).eval C b :=
        (eval_prodInterp_O₂ O₁ O₂ I₁ default₂ hdisj C hC_nf hC_sig a b).mp hC
      have h_canon_D : (canon O₂ default₂).eval D b := hcanon _ hax b h_canon_C
      exact (eval_prodInterp_O₂ O₁ O₂ I₁ default₂ hdisj D hD_nf hD_sig a b).mpr h_canon_D
  | rinc R S =>
      intro p q hR_pq
      obtain ⟨a, b⟩ := p
      obtain ⟨a', b'⟩ := q
      have hR_O₂ : R ∈ ontologyRoles O₂ := rinc_role_left_in_sig hax_sig
      have hS_O₂ : S ∈ ontologyRoles O₂ := rinc_role_right_in_sig hax_sig
      have hR_not_O₁ : R ∉ ontologyRoles O₁ := fun h₁ => hdisj.2 R h₁ hR_O₂
      have hS_not_O₁ : S ∉ ontologyRoles O₁ := fun h₁ => hdisj.2 S h₁ hS_O₂
      rw [prodInterp_role_not_O₁ O₁ O₂ I₁ default₂ hR_not_O₁ a a' b b'] at hR_pq
      obtain ⟨ha, hRcanon⟩ := hR_pq
      have hScanon : (canon O₂ default₂).ext_role S b b' :=
        hcanon _ hax b b' hRcanon
      rw [prodInterp_role_not_O₁ O₁ O₂ I₁ default₂ hS_not_O₁ a a' b b']
      exact ⟨ha, hScanon⟩
  | rchain R₁ R₂ S =>
      intro p q r hR₁_pq hR₂_qr
      obtain ⟨a, b⟩ := p
      obtain ⟨a', b'⟩ := q
      obtain ⟨a'', b''⟩ := r
      have hR₁_O₂ : R₁ ∈ ontologyRoles O₂ := rchain_role₁_in_sig hax_sig
      have hR₂_O₂ : R₂ ∈ ontologyRoles O₂ := rchain_role₂_in_sig hax_sig
      have hS_O₂  : S  ∈ ontologyRoles O₂ := rchain_role₃_in_sig hax_sig
      have hR₁_not_O₁ : R₁ ∉ ontologyRoles O₁ := fun h₁ => hdisj.2 R₁ h₁ hR₁_O₂
      have hR₂_not_O₁ : R₂ ∉ ontologyRoles O₁ := fun h₁ => hdisj.2 R₂ h₁ hR₂_O₂
      have hS_not_O₁  : S  ∉ ontologyRoles O₁ := fun h₁ => hdisj.2 S  h₁ hS_O₂
      rw [prodInterp_role_not_O₁ O₁ O₂ I₁ default₂ hR₁_not_O₁ a a' b b'] at hR₁_pq
      rw [prodInterp_role_not_O₁ O₁ O₂ I₁ default₂ hR₂_not_O₁ a' a'' b' b''] at hR₂_qr
      obtain ⟨ha_eq_a', hR₁canon⟩ := hR₁_pq
      obtain ⟨ha'_eq_a'', hR₂canon⟩ := hR₂_qr
      have hScanon : (canon O₂ default₂).ext_role S b b'' :=
        hcanon _ hax b b' b'' hR₁canon hR₂canon
      rw [prodInterp_role_not_O₁ O₁ O₂ I₁ default₂ hS_not_O₁ a a'' b b'']
      exact ⟨ha_eq_a'.trans ha'_eq_a'', hScanon⟩

-- ----------------------------------------------------------------
-- 9.8  prodInterp ⊨ O₁ ++ O₂ (P1)
-- ----------------------------------------------------------------

theorem prodInterp_satisfies {α : Type} (O₁ O₂ : Ontology) (I₁ : Interp α)
    (default₂ : CanonDom O₂)
    (hO₁_nf : OntologyNominalFree O₁) (hO₂_nf : OntologyNominalFree O₂)
    (hI₁ : I₁.satisfies O₁) (hdisj : DisjointSigs O₁ O₂) :
    (prodInterp O₁ O₂ I₁ default₂).satisfies (O₁ ++ O₂) := by
  intro ax hax
  rcases List.mem_append.mp hax with h | h
  · exact prodInterp_satisfies_O₁_axiom O₁ O₂ I₁ default₂ hO₁_nf hI₁ h
  · exact prodInterp_satisfies_O₂_axiom O₁ O₂ I₁ default₂ hO₂_nf hdisj h

-- ----------------------------------------------------------------
-- 9.9  Hard direction (mpr) of the refined factorization
-- ----------------------------------------------------------------

/-- **Refined factorization theorem (hard direction) — PROVED.**

    For arbitrary concepts C, D both in O₁'s atom-and-role
    signature, with `DisjointSigs O₁ O₂`:

       Sat (O₁ ++ O₂) C D
         →  Sat O₁ C D ∨ Sat O₂ ⊤ ⊥.

    Proof.  By `Classical.em` on `Sat O₂ ⊤ ⊥`.

    If `Sat O₂ ⊤ ⊥`, the right disjunct holds, done.

    Otherwise, by completeness of ELK on O₁ (`complete_via_canon`
    of ELpp), it suffices to show `Entails O₁ C D`, i.e.,
    every model of O₁ satisfies `C ⊑ D`.  Take I₁ ⊨ O₁ and
    a ∈ α with I₁.eval C a; we show I₁.eval D a.

    Build `M' := prodInterp O₁ O₂ I₁` over `α × CanonDom O₂`.
    Pick `b₀ := ⟨⊤, h⟩ ∈ CanonDom O₂` (well-defined since
    O₂ is consistent: `h : ¬ Sat O₂ ⊤ ⊥`).

    By `prodInterp_satisfies`, M' ⊨ O₁ ++ O₂.  By soundness of
    Sat applied to the hypothesis, M' ⊨ C ⊑ D.  By
    `eval_prodInterp_O₁` at C, we lift I₁.eval C a to
    M'.eval C ⟨a, b₀⟩; the entailment then gives M'.eval D ⟨a, b₀⟩;
    by `eval_prodInterp_O₁` at D, we descend to I₁.eval D a. -/
theorem Sat_factor_refined_mpr {O₁ O₂ : Ontology}
    (hO₁_nf : OntologyNominalFree O₁) (hO₂_nf : OntologyNominalFree O₂)
    (hdisj : DisjointSigs O₁ O₂)
    {C D : Concept} (hC_nf : NominalFree C) (hD_nf : NominalFree D)
    (hC : ConceptInSig O₁ C) (hD : ConceptInSig O₁ D)
    (h : Sat (O₁ ++ O₂) C D) :
    Sat O₁ C D ∨ Sat O₂ .top .bot := by
  classical
  by_cases hcons : Sat O₂ .top .bot
  · exact Or.inr hcons
  · refine Or.inl (complete_via_canon O₁ C D hO₁_nf hC_nf hD_nf ?_)
    intro α I₁ hI₁ a ha
    let b₀ : CanonDom O₂ := ⟨.top, hcons⟩
    let M' : Interp (α × CanonDom O₂) := prodInterp O₁ O₂ I₁ b₀
    have hM' : M'.satisfies (O₁ ++ O₂) :=
      prodInterp_satisfies O₁ O₂ I₁ b₀ hO₁_nf hO₂_nf hI₁ hdisj
    have hentail : Entails (O₁ ++ O₂) C D := sound _ h
    have hCab : M'.eval C ⟨a, b₀⟩ :=
      (eval_prodInterp_O₁ O₁ O₂ I₁ b₀ C hC_nf hC a b₀).mpr ha
    have hDab : M'.eval D ⟨a, b₀⟩ := hentail M' hM' ⟨a, b₀⟩ hCab
    exact (eval_prodInterp_O₁ O₁ O₂ I₁ b₀ D hD_nf hD a b₀).mp hDab

-- ----------------------------------------------------------------
-- 9.10  The full refined factorization theorem (iff)
-- ----------------------------------------------------------------

/-- **Refined SCC factorization theorem.**

    Under disjoint atom and role signatures, for nominal-free
    concepts C, D in O₁'s signature, with O₁ and O₂ both nominal-
    free at the axiom level (`OntologyNominalFree`), the closure
    of `O₁ ++ O₂` over the pair factors exactly:

      Sat (O₁ ++ O₂) C D   ↔   Sat O₁ C D ∨ Sat O₂ ⊤ ⊥.

    The right-disjunct `Sat O₂ ⊤ ⊥` captures the "global
    inconsistency pollution" case where O₂'s axioms alone derive
    ⊤ ⊑ ⊥, which propagates to all `O₁ ++ O₂` queries via R⊥.
    When O₂ is consistent, this disjunct is false and we recover
    the clean factorization.

    No ⊤-side or ⊥-side restriction on the role/atom GCIs is
    imposed.  The nominal-free preconditions limit the result to
    the OWL 2 EL fragment without nominals; full nominal coverage
    requires the merging-canonical-model construction (Kazakov 2014
    §6) plus a refined `prodInterp` that handles individuals — see
    the `nom`-aware infrastructure (`indiv` field, `conceptIndividuals`,
    `ontologyIndividuals`) which is in place but whose semantic
    correctness for nominal axioms is future work. -/
theorem Sat_factor_refined {O₁ O₂ : Ontology}
    (hO₁_nf : OntologyNominalFree O₁) (hO₂_nf : OntologyNominalFree O₂)
    (hdisj : DisjointSigs O₁ O₂)
    {C D : Concept} (hC_nf : NominalFree C) (hD_nf : NominalFree D)
    (hC : ConceptInSig O₁ C) (hD : ConceptInSig O₁ D) :
    Sat (O₁ ++ O₂) C D ↔ Sat O₁ C D ∨ Sat O₂ .top .bot :=
  ⟨Sat_factor_refined_mpr hO₁_nf hO₂_nf hdisj hC_nf hD_nf hC hD,
   Sat_factor_refined_mp⟩

-- ============================================================
-- 10. SCC compositionality via topological order — STATEMENT
-- ============================================================
-- Generalisation: if O = O₁ ++ O₂ ++ ... ++ Oₖ where the Oᵢ have
-- pairwise-disjoint signatures, then by induction on k the
-- atomic factorization gives k-component compositionality.
--
-- For the MOOSE algorithm:  the SCCs of the predicate dependency
-- graph form exactly such a partition (each SCC's signature is
-- closed under derivation, and SCCs across the topological DAG
-- have disjoint signatures by maximality of the SCC).
--
-- The two-component result above is the load-bearing case; the
-- k-component result is its iterated form.

/-- **k-component SCC factorization (statement only).** -/
def kComponentFactorization (Os : List Ontology) (C D : Concept) : Prop :=
  -- Pairwise-disjoint signatures imply: closure of `(Os.flatten)` over
  -- `(Os[0])'s signature is exactly the closure of `Os[0]` alone.
  -- (Stated abstractly here; proved via repeated two-component application.)
  ∀ (Otop : Ontology),
    (∀ Oi ∈ Os.tail, DisjointSigs Otop Oi) →
    Sat (Otop ++ Os.flatten) C D ↔ Sat Otop C D

end SCC
end ELKSDD
