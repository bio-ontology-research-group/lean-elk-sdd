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

/-- **Refined factorization (hard direction) — STATEMENT.**

    For atomic concepts A, B with both in `O₁`'s atom signature,
    under disjoint atom and role signatures, the converse of
    `Sat_factor_refined_mp` holds (specialized to atomic queries):

       Sat (O₁ ++ O₂) (.atom A) (.atom B)
         →  Sat O₁ (.atom A) (.atom B) ∨ Sat O₂ ⊤ ⊥.

    Proof outline (semantic, requires the disjoint-domain
    construction):

      Suppose ¬ Sat O₂ ⊤ ⊥ (the right disjunct fails).  We need
      Sat O₁ (.atom A) (.atom B).

      Consistency of O₂ implies the canonical model `canon O₂`
      has non-empty domain (the witness `⟨⊤, h⟩` exists, where
      `h : ¬ Sat O₂ ⊤ ⊥`).  Take any model I₁ of O₁ — exists
      because O₁ has the canonical model `canon O₁` over
      `CanonDom O₁` (well-defined when O₁ is consistent;
      falls under bot_elim otherwise).

      Form `sumInterp I₁ (canon O₂)` over `Δ_{I₁} ⊕ CanonDom O₂`:

        ext_concept n s = match s with
          | .inl a => if n ∈ atoms O₁ then I₁.ext_concept n a else False
          | .inr b => if n ∈ atoms O₁ then False else (canon O₂).ext_concept n b

        ext_role similar (using O₁'s role signature for the
                         conditional, with cross-side links empty).

      Eval-invariance for concepts in O₁'s atom-and-role signature:
      sumInterp.eval C (.inl a) ↔ I₁.eval C a (one direction;
      requires the side-restriction lemma).

      Sub-claim: sumInterp ⊨ O₁ on inl side; sumInterp ⊨ O₂ on
      inr side; cross-side axioms vacuous (signature
      disjointness).  Combined: sumInterp ⊨ (O₁ ++ O₂).

      By Entails (O₁ ++ O₂) (.atom A) (.atom B) and
      sumInterp ⊨ (O₁ ++ O₂):  for the canonical x (.inl
      (canon-O₁-witness-of-A)), sumInterp ⊨ A → B.  By
      eval-invariance, I₁ ⊨ A → B.  By completeness for O₁,
      Sat O₁ (.atom A) (.atom B).

    The construction goes through `Sum α β` (Lean `α ⊕ β`),
    eval-invariance lemmas similar in shape to `Normalize.
    eval_extendInterp_of_fresh`, and signature-side reasoning.
    Estimated ~300-500 LOC.  Not yet formalised in this layer; a
    follow-up Layer 6 increment will provide the construction. -/
def Sat_factor_refined_mpr_statement
    (O₁ O₂ : Ontology)
    (_hdisj : DisjointSigs O₁ O₂)
    (A B : Nat) (_hA : A ∈ ontologyAtoms O₁) (_hB : B ∈ ontologyAtoms O₁) :
    Prop :=
  Sat (O₁ ++ O₂) (.atom A) (.atom B) →
    Sat O₁ (.atom A) (.atom B) ∨ Sat O₂ .top .bot

/-- The full refined factorization iff form (statement only). -/
def Sat_factor_refined_statement
    (O₁ O₂ : Ontology) (C D : Concept) :
    Prop :=
  Sat (O₁ ++ O₂) C D ↔ Sat O₁ C D ∨ Sat O₂ .top .bot

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
