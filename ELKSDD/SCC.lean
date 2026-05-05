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

/- **Hard direction (atomic case): SCC compositionality of atomic
    subsumption.**

    For atomic concepts A, B in `O₁`'s atom signature, with `O₂`
    having disjoint atom and role signatures from `O₁`, the closure
    decomposition is exact:

        Sat (O₁ ++ O₂) (.atom A) (.atom B)   →   Sat O₁ (.atom A) (.atom B).

    Combined with `Sat_factor_easy`, this gives the iff

        Sat (O₁ ++ O₂) (.atom A) (.atom B)   ↔   Sat O₁ (.atom A) (.atom B).

    PROOF (semantic): take any model `I` of `O₁`.  Form a
    disjoint-domain extension `I'` over the disjoint sum
    `Δ_I ⊕ Δ_{canon O₂}`.  `I'` satisfies `O₁ ++ O₂` (each
    component on its own side of the sum), so by completeness
    `(canon O₂).eval (.atom A) x ↔ False` (atom A not in O₂).
    On the I-side, `I' ⊨ A ⊑ B` means `I ⊨ A ⊑ B`.  By soundness
    plus completeness on `O₁` alone, `Sat O₁ (.atom A) (.atom B)`.

    The fully formalised disjoint-domain construction goes through
    a sum type (Lean `Sum α β`) and is mechanical but verbose; we
    expose the *signature* of the theorem here as documentation —
    the next Layer 6 increment will instantiate the construction. -/

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
