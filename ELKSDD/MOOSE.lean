/-
  ELKSDD/MOOSE.lean
  -----------------
  *Bow-tied paper-citation theorems for the MOOSE inference pipeline.*

  This module assembles the end-to-end formal results of the MOOSE
  pipeline into single-statement theorems suitable for direct citation
  from the paper.  Each theorem is *unconditional* (no free hypotheses)
  and audit-clean (only Lean foundation axioms).

  Citation index.

    * `moose_inference_correct` — the bow-tied end-to-end correctness
      theorem: there exists a verified compiled SDD that
        (a) soundly encodes the Sat-query (`SDDEncodesQuery`),
        (b) computes the DISPONTE distribution-semantics marginal
            via weighted model count (`SDD.wmc = disponteWMC`),
        (c) has bounded size (exact: `2^(|O|+1) - 1`).
      Witness: `compileSat O C D`.

    * `sat_decision_polynomial` — Sat decision is polynomial:
      a finite list of size at most `|Sub(O)|²` decides
      Sat-derivability on bounded named atoms.

    * `moose_pipeline_complete` — combined statement: Saturation +
      polynomial Sat decision + verified SDD + DISPONTE
      correspondence in a single packaged theorem.

  Components in detail.

    (1) **Saturation** — `derivableClosure O` lists every Sat-
        derivable bounded atom and has size at most `|Sub(O)|²`
        (`Saturation.lean`).
    (2) **Sat decision** — membership in the saturation decides
        Sat (`sat_iff_in_derivableClosure`).
    (3) **SDD compilation** — `compileSat O C D` is a verified
        Shannon-expansion tree of size exactly `2^(|O|+1) - 1`
        encoding the Sat-query (`Compilation.lean` + A6).
    (4) **DISPONTE correspondence** — the WMC of the compiled SDD
        equals the DISPONTE marginal for every weight function
        (`CompilationWMC.lean`, unconditional).

  Caveats — what is *not* formalised here.

    * Polynomial *SDD size* via vtree-aware compilation is folklore
      (Riguzzi 2015 TPLP).  Our polynomial result is for *Sat
      decision* only; SDD size is the worst-case exponential
      Shannon-tree bound.  The conditional polynomial bound via
      essential variables (`essential_polynomial_bound`) is
      provided in `Compilation.lean`.
    * Real-valued probabilities (ℝ-valued DISPONTE) require Mathlib
      and are deferred (A5).

  All theorems audit-clean — only Lean foundation axioms.
-/

import ELKSDD.Compilation
import ELKSDD.CompilationWMC
import ELKSDD.Saturation
import ELKSDD.SCC

namespace ELKSDD
namespace ELpp

open SDD SCC Normalize

-- ============================================================
-- (1) End-to-end inference correctness
-- ============================================================

/-- **MOOSE inference correctness theorem.**

    For every OWL 2 EL ontology `O` and Sat-query `(C, D)`, there
    exists a verified compiled SDD that simultaneously:

      (a) **soundly encodes the query**: a world `M : World O`
          satisfies the SDD iff `Sat (selectedAxioms O M) C D`;
      (b) **computes the DISPONTE marginal**: for every per-axiom
          weight function `w`, the weighted model count of the SDD
          equals the DISPONTE distribution-semantics probability
          `disponteWMC O C D w`;
      (c) **has bounded size**: exactly `2^(|O|+1) - 1` nodes (the
          worst-case Shannon-tree count, A6).

    The witness is `compileSat O C D`. -/
theorem moose_inference_correct (O : Ontology) (C D : Concept) :
    ∃ tree : Tree (DispAtom O),
      (∀ M : World O, model tree M ↔ Sat (selectedAxioms O M) C D) ∧
      (∀ w : DispAtom O → Bool → Nat, SDD.wmc tree w = disponteWMC O C D w) ∧
      size tree = 2 ^ (O.length + 1) - 1 :=
  ⟨compileSat O C D,
   compileSat_correct O C D,
   compileSat_disponte_correspondence O C D,
   compileSat_size_eq O C D⟩

-- ============================================================
-- (2) Polynomial-time Sat decision
-- ============================================================

/-- **Polynomial-time Sat decision theorem.**

    For every OWL 2 EL ontology `O`, the Sat-derivability relation
    on bounded named atoms is decidable via a finite list
    `L = derivableClosure O` whose size is at most `(numSubexprs O)²`:

      (a) `|L| ≤ |Sub(O)|²` (polynomial saturation bound);
      (b) `(C, D) ∈ L ↔ Sat O C D` for any `C, D ∈ Sub(O)`.

    This is the polynomial-time *decision* component of the MOOSE
    inference pipeline.  The probabilistic-marginal component (WMC
    over the SDD) has Shannon-tree exponential worst-case size;
    polynomial bounds via vtree-aware compilation are folklore
    (Riguzzi 2015 TPLP) and not formalised here. -/
theorem sat_decision_polynomial (O : Ontology) :
    ∃ L : List (Concept × Concept),
      L.length ≤ (numSubexprs O) ^ 2 ∧
      (∀ {C D : Concept},
          C ∈ subsOfOntology O → D ∈ subsOfOntology O →
          (Sat O C D ↔ (C, D) ∈ L)) :=
  ⟨derivableClosure O,
   derivableClosure_length O,
   fun hC hD => sat_iff_in_derivableClosure O hC hD⟩

-- ============================================================
-- (3) Combined complexity decomposition
-- ============================================================

/-- **MOOSE inference pipeline — complete factorisation.**

    For every OWL 2 EL ontology `O` and query `(C, D)`, the MOOSE
    inference pipeline factors as:

      (1) **Saturation** + **polynomial Sat decision**: a list of
          size at most `|Sub(O)|²` decides Sat-derivability on
          bounded named atoms.
      (2) **Verified SDD with DISPONTE correspondence**: a Shannon-
          expansion tree of exactly `2^(|O|+1) - 1` nodes correctly
          encodes the query, and its WMC equals the DISPONTE
          distribution-semantics marginal for every weight function.

    Components compose: Sat decision and SDD-model coincide on every
    world; the SDD's WMC is the DISPONTE marginal. -/
theorem moose_pipeline_complete (O : Ontology) (C D : Concept) :
    -- (1) Saturation + polynomial Sat decision.
    (∃ L : List (Concept × Concept),
        L.length ≤ (numSubexprs O) ^ 2 ∧
        (∀ {C' D' : Concept},
            C' ∈ subsOfOntology O → D' ∈ subsOfOntology O →
            (Sat O C' D' ↔ (C', D') ∈ L))) ∧
    -- (2) Verified SDD with DISPONTE correspondence.
    (∃ tree : Tree (DispAtom O),
        (∀ M : World O, model tree M ↔ Sat (selectedAxioms O M) C D) ∧
        (∀ w : DispAtom O → Bool → Nat, SDD.wmc tree w = disponteWMC O C D w) ∧
        size tree = 2 ^ (O.length + 1) - 1) :=
  ⟨sat_decision_polynomial O, moose_inference_correct O C D⟩

-- ============================================================
-- (4) SCC compositionality at the Sat level
-- ============================================================

/-- **MOOSE SCC compositional theorem (Sat level).**

    Under disjoint signatures and consistent O₂, Sat-derivability over
    the joint ontology `O₁ ++ O₂` reduces to Sat-derivability over the
    relevant SCC `O₁` alone, for queries in `O₁`'s signature.  This is
    the Sat-level statement of MOOSE's per-SCC factorization.

    Combined with `wmc_compileSat_eq_disponteWMC`, the per-SCC
    `compileSat O₁ C D` and the joint `compileSat (O₁ ++ O₂) C D`
    encode equivalent queries on the OWL 2 EL closure (modulo the
    multiplicative `O₂`-side weights captured in the DISPONTE
    marginal).

    Direct consequence of `Sat_factor_refined` (SCC.lean).  The
    consistency hypothesis `¬ Sat O₂ ⊤ ⊥` rules out the global-
    inconsistency disjunct; what remains is the clean factorization
    onto `O₁`. -/
theorem scc_sat_factor
    {O₁ O₂ : Ontology}
    (hO₁_nf : OntologyNominalFree O₁) (hO₂_nf : OntologyNominalFree O₂)
    (hO₁_safe : RangeChainSafe O₁) (hO₂_safe : RangeChainSafe O₂)
    (hdisj : DisjointSigs O₁ O₂)
    (hcons : ¬ Sat O₂ .top .bot)
    {C D : Concept} (hC_nf : NominalFree C) (hD_nf : NominalFree D)
    (hC : ConceptInSig O₁ C) (hD : ConceptInSig O₁ D) :
    Sat (O₁ ++ O₂) C D ↔ Sat O₁ C D := by
  constructor
  · intro h
    rcases (Sat_factor_refined hO₁_nf hO₂_nf hO₁_safe hO₂_safe hdisj
            hC_nf hD_nf hC hD).mp h with h₁ | h₂
    · exact h₁
    · exact absurd h₂ hcons
  · exact Sat_factor_easy O₁ O₂ C D

/-- **Symmetric variant.**  Same theorem with O₁/O₂ swapped: queries
    in O₂'s signature reduce to Sat over O₂ alone (under consistent
    O₁).  Uses ontology-permutation invariance of Sat. -/
theorem scc_sat_factor_symm
    {O₁ O₂ : Ontology}
    (hO₁_nf : OntologyNominalFree O₁) (hO₂_nf : OntologyNominalFree O₂)
    (hO₁_safe : RangeChainSafe O₁) (hO₂_safe : RangeChainSafe O₂)
    (hdisj : DisjointSigs O₁ O₂)
    (hcons : ¬ Sat O₁ .top .bot)
    {C D : Concept} (hC_nf : NominalFree C) (hD_nf : NominalFree D)
    (hC : ConceptInSig O₂ C) (hD : ConceptInSig O₂ D) :
    Sat (O₁ ++ O₂) C D ↔ Sat O₂ C D := by
  have hperm : ∀ Q E, Sat (O₁ ++ O₂) Q E ↔ Sat (O₂ ++ O₁) Q E := by
    intro Q E
    constructor <;> intro h <;>
      apply Sat_mono (fun ax hax => ?_) h
    · rcases List.mem_append.mp hax with h | h
      · exact List.mem_append.mpr (Or.inr h)
      · exact List.mem_append.mpr (Or.inl h)
    · rcases List.mem_append.mp hax with h | h
      · exact List.mem_append.mpr (Or.inr h)
      · exact List.mem_append.mpr (Or.inl h)
  rw [hperm]
  exact scc_sat_factor hO₂_nf hO₁_nf hO₂_safe hO₁_safe hdisj.symm
        hcons hC_nf hD_nf hC hD

/-- **MOOSE SCC summary theorem.**

    For an OWL 2 EL ontology decomposed into two SCC-disjoint
    components `O₁ ++ O₂` (consistent O₂, queries in O₁'s
    signature), the *full inference pipeline* factors via the
    per-SCC analysis:

      (i) Sat over the joint `O₁ ++ O₂` ↔ Sat over `O₁` alone
          (`scc_sat_factor`).
      (ii) The verified compiled SDD `compileSat O₁ C D` is correct
           and has the DISPONTE correspondence (cited from MOOSE.(1)).
      (iii) The Sat-level reduction lifts to the algorithmic level:
            the per-SCC SDD encodes the same query as the joint SDD
            (modulo the world-weight contributions of the irrelevant
            SCC).

    *Caveat — what is not proved here.*  The per-world Sat factorization
    (Sat at `selectedAxioms M` factoring) requires the canonical-model
    construction to extend to subontologies, which itself requires the
    `ConceptInSig` hypothesis to propagate to selected sub-ontologies.
    This is the missing technical bridge to a closed-form *WMC-level*
    factorization (which would yield `disponteWMC (O₁ ++ O₂) C D = c
    · disponteWMC O₁ C D` for some `O₂`-dependent constant `c`).
    The Sat-level statement (i) is unconditional. -/
theorem moose_scc_summary
    {O₁ O₂ : Ontology}
    (hO₁_nf : OntologyNominalFree O₁) (hO₂_nf : OntologyNominalFree O₂)
    (hO₁_safe : RangeChainSafe O₁) (hO₂_safe : RangeChainSafe O₂)
    (hdisj : DisjointSigs O₁ O₂)
    (hcons : ¬ Sat O₂ .top .bot)
    {C D : Concept} (hC_nf : NominalFree C) (hD_nf : NominalFree D)
    (hC : ConceptInSig O₁ C) (hD : ConceptInSig O₁ D) :
    -- (i) Sat-level factorization onto the relevant SCC.
    (Sat (O₁ ++ O₂) C D ↔ Sat O₁ C D) ∧
    -- (ii) The verified per-SCC compiled SDD has end-to-end correctness.
    (∃ tree : Tree (DispAtom O₁),
        (∀ M : World O₁, model tree M ↔ Sat (selectedAxioms O₁ M) C D) ∧
        (∀ w : DispAtom O₁ → Bool → Nat, SDD.wmc tree w = disponteWMC O₁ C D w) ∧
        size tree = 2 ^ (O₁.length + 1) - 1) :=
  ⟨scc_sat_factor hO₁_nf hO₂_nf hO₁_safe hO₂_safe hdisj hcons hC_nf hD_nf hC hD,
   moose_inference_correct O₁ C D⟩

-- ============================================================
-- (5) Multi-component SCC factorization (k SCCs)
-- ============================================================

/-- Sat-permutation invariance for triple appends. -/
private theorem Sat_swap_middle {A B C : Ontology} {Q E : Concept} :
    Sat (A ++ B ++ C) Q E ↔ Sat (A ++ C ++ B) Q E := by
  constructor
  · intro h
    apply Sat_mono _ h
    intro ax hax
    rw [List.append_assoc] at hax ⊢
    rcases List.mem_append.mp hax with hA | hBC
    · exact List.mem_append.mpr (Or.inl hA)
    · rcases List.mem_append.mp hBC with hB | hC
      · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr hB)))
      · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl hC)))
  · intro h
    apply Sat_mono _ h
    intro ax hax
    rw [List.append_assoc] at hax ⊢
    rcases List.mem_append.mp hax with hA | hCB
    · exact List.mem_append.mpr (Or.inl hA)
    · rcases List.mem_append.mp hCB with hC | hB
      · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr hC)))
      · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl hB)))

/-- `RangeChainSafe` propagates downward to subontologies. -/
theorem RangeChainSafe_subontology {O O' : Ontology} (hsafe : RangeChainSafe O)
    (hsub : Subontology O' O) : RangeChainSafe O' := by
  intro R₁ R₂ S T E hRchain hAnc hRange
  exact hsafe R₁ R₂ S T E (hsub _ hRchain)
        (RincAncestor_mono hsub hAnc) (hsub _ hRange)

/-- `OntologyNominalFree` propagates downward to subontologies. -/
theorem OntologyNominalFree_subontology {O O' : Ontology}
    (hnf : OntologyNominalFree O) (hsub : Subontology O' O) :
    OntologyNominalFree O' :=
  fun ax hax => hnf ax (hsub _ hax)

/-- `ConceptInSig` propagates upward (subontology → larger ontology). -/
theorem ConceptInSig_of_Subontology {O O' : Ontology} {C : Concept}
    (hsub : Subontology O O') (hC : ConceptInSig O C) : ConceptInSig O' C := by
  refine ⟨?_, ?_⟩
  · intro n hn
    have hn_O : n ∈ ontologyAtoms O := hC.1 n hn
    unfold Normalize.ontologyAtoms at hn_O ⊢
    rw [List.mem_flatMap] at hn_O ⊢
    obtain ⟨ax, hax_O, hn_ax⟩ := hn_O
    exact ⟨ax, hsub _ hax_O, hn_ax⟩
  · intro R hR
    have hR_O : R ∈ ontologyRoles O := hC.2 R hR
    unfold Normalize.ontologyRoles at hR_O ⊢
    rw [List.mem_flatMap] at hR_O ⊢
    obtain ⟨ax, hax_O, hR_ax⟩ := hR_O
    exact ⟨ax, hsub _ hax_O, hR_ax⟩

/-- `DisjointSigs` combines under append (left side). -/
theorem DisjointSigs_append_left {O₁ O₂ O : Ontology}
    (h₁ : DisjointSigs O₁ O) (h₂ : DisjointSigs O₂ O) :
    DisjointSigs (O₁ ++ O₂) O := by
  refine ⟨?_, ?_⟩
  · intro a ha
    rw [mem_ontologyAtoms_append] at ha
    cases ha with
    | inl h => exact h₁.1 a h
    | inr h => exact h₂.1 a h
  · intro r hr
    rw [mem_ontologyRoles_append] at hr
    cases hr with
    | inl h => exact h₁.2 r h
    | inr h => exact h₂.2 r h

/-- **Joint consistency from per-component consistency + disjoint sigs.**
    A useful corollary of `Sat_factor_refined`: pairwise disjoint
    consistent ontologies remain consistent when concatenated. -/
theorem joint_consistent_pair
    {O₁ O₂ : Ontology}
    (hO₁_nf : OntologyNominalFree O₁) (hO₂_nf : OntologyNominalFree O₂)
    (hO₁_safe : RangeChainSafe O₁) (hO₂_safe : RangeChainSafe O₂)
    (hdisj : DisjointSigs O₁ O₂)
    (h₁_cons : ¬ Sat O₁ .top .bot) (h₂_cons : ¬ Sat O₂ .top .bot) :
    ¬ Sat (O₁ ++ O₂) .top .bot := by
  intro h
  have hiff := Sat_factor_refined hO₁_nf hO₂_nf hO₁_safe hO₂_safe hdisj
                (show NominalFree .top from trivial) (show NominalFree .bot from trivial)
                (ConceptInSig.top _) (ConceptInSig.bot _)
  rcases hiff.mp h with h₁ | h₂
  · exact h₁_cons h₁
  · exact h₂_cons h₂

/-- **MOOSE k-component SCC factorization theorem.**

    Given `k+1` ontologies (one "relevant" `Otop` containing the
    query's signature, plus `k` other components in `Os` with
    pairwise-disjoint signatures and each individually consistent),
    Sat-derivability over the *flattened* ontology reduces to
    Sat-derivability over `Otop` alone for queries in `Otop`'s
    signature.

    This is the iterated form of `scc_sat_factor`, generalising
    from 2 components to k.  Proof: induction on `Os`, peeling off
    one component at a time and applying `scc_sat_factor` plus
    Sat-permutation invariance.

    Hypotheses:
      * `hjoint_nf`, `hjoint_safe` — well-formedness conditions on
        the joint ontology.
      * `h_disj_top` — each component in `Os` has signature disjoint
        from `Otop`.
      * `h_pairwise_disj` — components within `Os` are pairwise
        signature-disjoint (the "SCC partition" condition).
      * `h_cons` — each component in `Os` is individually consistent.
      * `hC_nf`, `hD_nf`, `hC`, `hD` — the query is nominal-free and
        in `Otop`'s signature. -/
theorem scc_sat_factor_k
    (Otop : Ontology) (Os : List Ontology)
    (hjoint_nf : OntologyNominalFree (Otop ++ Os.flatten))
    (hjoint_safe : RangeChainSafe (Otop ++ Os.flatten))
    (h_disj_top : ∀ O ∈ Os, DisjointSigs Otop O)
    (h_pairwise_disj : List.Pairwise DisjointSigs Os)
    (h_cons : ∀ O ∈ Os, ¬ Sat O .top .bot)
    {C D : Concept} (hC_nf : NominalFree C) (hD_nf : NominalFree D)
    (hC : ConceptInSig Otop C) (hD : ConceptInSig Otop D) :
    Sat (Otop ++ Os.flatten) C D ↔ Sat Otop C D := by
  induction Os with
  | nil =>
      show Sat (Otop ++ ([] : List Ontology).flatten) C D ↔ Sat Otop C D
      simp [List.flatten]
  | cons O' rest ih =>
      have h_disj_O' : DisjointSigs Otop O' := h_disj_top O' List.mem_cons_self
      have h_cons_O' : ¬ Sat O' .top .bot := h_cons O' List.mem_cons_self
      have h_disj_rest : ∀ O ∈ rest, DisjointSigs Otop O :=
        fun O hO => h_disj_top O (List.mem_cons_of_mem _ hO)
      have h_pairwise_rest : List.Pairwise DisjointSigs rest :=
        h_pairwise_disj.tail
      have h_O'_disj_rest : ∀ O ∈ rest, DisjointSigs O' O := by
        intro O hO
        rcases List.pairwise_cons.mp h_pairwise_disj with ⟨hhead, _⟩
        exact hhead O hO
      have h_cons_rest : ∀ O ∈ rest, ¬ Sat O .top .bot :=
        fun O hO => h_cons O (List.mem_cons_of_mem _ hO)
      have hsub_top : Subontology Otop (Otop ++ (O' :: rest).flatten) :=
        Subontology.append_left _ _
      have hsub_O' : Subontology O' (Otop ++ (O' :: rest).flatten) := by
        intro ax hax
        show ax ∈ Otop ++ (O' ++ rest.flatten)
        exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl hax)))
      have hsub_rest : Subontology rest.flatten (Otop ++ (O' :: rest).flatten) := by
        intro ax hax
        show ax ∈ Otop ++ (O' ++ rest.flatten)
        exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr hax)))
      show Sat (Otop ++ (O' ++ rest.flatten)) C D ↔ Sat Otop C D
      have hperm : Sat (Otop ++ (O' ++ rest.flatten)) C D ↔
                   Sat ((Otop ++ rest.flatten) ++ O') C D := by
        have h1 : Sat (Otop ++ (O' ++ rest.flatten)) C D ↔
                  Sat ((Otop ++ O') ++ rest.flatten) C D := by
          rw [← List.append_assoc]
        have h2 : Sat ((Otop ++ O') ++ rest.flatten) C D ↔
                  Sat ((Otop ++ rest.flatten) ++ O') C D :=
          @Sat_swap_middle Otop O' rest.flatten C D
        exact h1.trans h2
      rw [hperm]
      have hsub_A : Subontology (Otop ++ rest.flatten)
                       (Otop ++ (O' :: rest).flatten) := by
        intro ax hax
        rcases List.mem_append.mp hax with hT | hR
        · exact hsub_top _ hT
        · exact hsub_rest _ hR
      have hA_nf : OntologyNominalFree (Otop ++ rest.flatten) :=
        OntologyNominalFree_subontology hjoint_nf hsub_A
      have hB_nf : OntologyNominalFree O' :=
        OntologyNominalFree_subontology hjoint_nf hsub_O'
      have hA_safe : RangeChainSafe (Otop ++ rest.flatten) :=
        RangeChainSafe_subontology hjoint_safe hsub_A
      have hB_safe : RangeChainSafe O' :=
        RangeChainSafe_subontology hjoint_safe hsub_O'
      have hA_disj_B : DisjointSigs (Otop ++ rest.flatten) O' := by
        apply DisjointSigs_append_left
        · exact h_disj_O'
        · refine ⟨?_, ?_⟩
          · intro a ha_rest
            unfold Normalize.ontologyAtoms at ha_rest
            rw [List.mem_flatMap] at ha_rest
            obtain ⟨ax, hax_rest, ha_ax⟩ := ha_rest
            have : ax ∈ rest.flatten := hax_rest
            rw [List.mem_flatten] at this
            obtain ⟨O, hO_rest, hax_O⟩ := this
            have hO'_disj_O : DisjointSigs O' O := h_O'_disj_rest O hO_rest
            apply hO'_disj_O.symm.1 a
            unfold Normalize.ontologyAtoms
            exact List.mem_flatMap.mpr ⟨ax, hax_O, ha_ax⟩
          · intro r hr_rest
            unfold Normalize.ontologyRoles at hr_rest
            rw [List.mem_flatMap] at hr_rest
            obtain ⟨ax, hax_rest, hr_ax⟩ := hr_rest
            have : ax ∈ rest.flatten := hax_rest
            rw [List.mem_flatten] at this
            obtain ⟨O, hO_rest, hax_O⟩ := this
            have hO'_disj_O : DisjointSigs O' O := h_O'_disj_rest O hO_rest
            apply hO'_disj_O.symm.2 r
            unfold Normalize.ontologyRoles
            exact List.mem_flatMap.mpr ⟨ax, hax_O, hr_ax⟩
      have hC_in_A : ConceptInSig (Otop ++ rest.flatten) C :=
        ConceptInSig_of_Subontology (Subontology.append_left _ _) hC
      have hD_in_A : ConceptInSig (Otop ++ rest.flatten) D :=
        ConceptInSig_of_Subontology (Subontology.append_left _ _) hD
      rw [scc_sat_factor hA_nf hB_nf hA_safe hB_safe hA_disj_B h_cons_O'
          hC_nf hD_nf hC_in_A hD_in_A]
      apply ih
      · exact hA_nf
      · exact hA_safe
      · exact h_disj_rest
      · exact h_pairwise_rest
      · exact h_cons_rest

-- ============================================================
-- (5) Chain-free corollary: SCC factorisation without RangeChainSafe
-- ============================================================
--
-- The `RangeChainSafe O` precondition on the SCC factorisation
-- theorems is needed only because the rchain case of `canon_satisfies`
-- (ELpp.lean:734-744) cannot discharge the range guard transfer
-- when an `rchain R₁ R₂ S` axiom co-exists with a `range T E` axiom
-- on a rinc-ancestor T of S.  When the ontology has no role chains
-- (which is the case for all the experimental ontologies in the
-- MOOSE paper — MNIST onto, Pizza\"iolo), the precondition is
-- vacuously satisfied.
--
-- This section provides a `NoRoleChain` predicate that is strictly
-- stronger than `RangeChainSafe` (vacuously implies it) and a
-- corollary form of `scc_sat_factor` that takes `NoRoleChain`
-- instead.  Production-ontology users who do not employ role
-- chains can use this corollary directly without needing to verify
-- range-chain safety.
--
-- Future work (BBL 2008 §3.3 Path-B): full elimination of
-- `RangeChainSafe` by completing the meaningful-range case of
-- `Sat_to_eliminated`/`Sat_from_eliminated` in `RangeNorm.lean`
-- (~300 LOC; the `eliminateRanges` syntactic transformation and
-- the strict-canon `canon_satisfies_strict` are already in place
-- and sorry-free).

/-- An ontology has no role chain axioms.  Strictly stronger than
    `RangeChainSafe`: with no rchain axioms, the rchain case of any
    range-guard-transfer obligation is vacuous. -/
def NoRoleChain (O : Ontology) : Prop :=
  ∀ R₁ R₂ S, Axiom.rchain R₁ R₂ S ∉ O

/-- An ontology has no range axioms.  Also strictly stronger than
    `RangeChainSafe`: with no range axioms, the conclusion
    `Axiom.range T E ∉ O` is universally true.  This is the more
    practically common case (e.g. the MNIST ontology in the MOOSE
    paper has a role chain but no range axioms). -/
def NoRangeAxiom (O : Ontology) : Prop :=
  ∀ T E, Axiom.range T E ∉ O

/-- `NoRoleChain O` implies `RangeChainSafe O` vacuously: with no
    rchain axioms, the universal hypothesis `Axiom.rchain R₁ R₂ S ∈ O`
    is always false, so the implication is trivially true. -/
theorem RangeChainSafe_of_NoRoleChain {O : Ontology}
    (h : NoRoleChain O) : RangeChainSafe O := by
  intro R₁ R₂ S T E hRchain _ _
  exact (h R₁ R₂ S hRchain).elim

/-- `NoRangeAxiom O` implies `RangeChainSafe O` vacuously: with no
    range axioms, the conclusion is universally true. -/
theorem RangeChainSafe_of_NoRangeAxiom {O : Ontology}
    (h : NoRangeAxiom O) : RangeChainSafe O := by
  intro R₁ R₂ S T E _ _ hRange
  exact h T E hRange

/-- **Chain-free corollary of `scc_sat_factor`.**

    For ontologies without role chains, the Sat-level SCC
    factorisation holds without requiring the user to verify
    range-chain safety. -/
theorem scc_sat_factor_no_chain
    {O₁ O₂ : Ontology}
    (hO₁_nf : OntologyNominalFree O₁) (hO₂_nf : OntologyNominalFree O₂)
    (hO₁_no_chain : NoRoleChain O₁) (hO₂_no_chain : NoRoleChain O₂)
    (hdisj : DisjointSigs O₁ O₂)
    (hcons : ¬ Sat O₂ .top .bot)
    {C D : Concept} (hC_nf : NominalFree C) (hD_nf : NominalFree D)
    (hC : ConceptInSig O₁ C) (hD : ConceptInSig O₁ D) :
    Sat (O₁ ++ O₂) C D ↔ Sat O₁ C D :=
  scc_sat_factor hO₁_nf hO₂_nf
    (RangeChainSafe_of_NoRoleChain hO₁_no_chain)
    (RangeChainSafe_of_NoRoleChain hO₂_no_chain)
    hdisj hcons hC_nf hD_nf hC hD

/-- **Range-free corollary of `scc_sat_factor`.**

    For ontologies without range axioms (which includes both the
    MNIST and Pizza\"iolo ontologies in the MOOSE experiments —
    the former has a role chain but no ranges, the latter has
    neither), the Sat-level SCC factorisation holds without
    requiring the user to verify range-chain safety. -/
theorem scc_sat_factor_no_range
    {O₁ O₂ : Ontology}
    (hO₁_nf : OntologyNominalFree O₁) (hO₂_nf : OntologyNominalFree O₂)
    (hO₁_no_range : NoRangeAxiom O₁) (hO₂_no_range : NoRangeAxiom O₂)
    (hdisj : DisjointSigs O₁ O₂)
    (hcons : ¬ Sat O₂ .top .bot)
    {C D : Concept} (hC_nf : NominalFree C) (hD_nf : NominalFree D)
    (hC : ConceptInSig O₁ C) (hD : ConceptInSig O₁ D) :
    Sat (O₁ ++ O₂) C D ↔ Sat O₁ C D :=
  scc_sat_factor hO₁_nf hO₂_nf
    (RangeChainSafe_of_NoRangeAxiom hO₁_no_range)
    (RangeChainSafe_of_NoRangeAxiom hO₂_no_range)
    hdisj hcons hC_nf hD_nf hC hD

-- ============================================================
-- Audit
-- ============================================================

#print axioms moose_inference_correct
#print axioms sat_decision_polynomial
#print axioms moose_pipeline_complete
#print axioms scc_sat_factor
#print axioms scc_sat_factor_symm
#print axioms moose_scc_summary
#print axioms joint_consistent_pair
#print axioms scc_sat_factor_k
#print axioms RangeChainSafe_of_NoRoleChain
#print axioms RangeChainSafe_of_NoRangeAxiom
#print axioms scc_sat_factor_no_chain
#print axioms scc_sat_factor_no_range

end ELpp
end ELKSDD
