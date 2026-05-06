/-
  ELKSDD/SCCNomLHS.lean
  ---------------------
  *Nominal-aware SCC factorization (LHS-nominal extension).*

  Lifts the SCC factorization from the strict
  `OntologyNominalFree O₁` requirement to the more permissive
  `OntologyNomLHS O₁`, allowing ABox-style ClassAssertion axioms
  `{a} ⊑ D` (with `D` nominal-free) on the analyzed side O₁.

  *Key insight.*  An LHS-nominal `{a}` (with `a ∈
  ontologyIndividuals O₁`) pins the prodInterp evaluation to a
  specific point `⟨I₁.indiv a, default₂⟩`, so no general nominal
  evaluation is needed — just evaluate at the specific second
  coordinate `default₂`.  This is the "ABox pinning" trick that
  bridges SCC factorization to ABox patterns without the merging
  canonical model.

  *Headline theorem.*

    `Sat_factor_nomLHS` — SCC factorization where O₁ may have
    LHS-nominal GCIs (other axiom positions remain nominal-free):

      Sat (O₁ ++ O₂) C D ↔ Sat O₁ C D ∨ Sat O₂ ⊤ ⊥

    under `OntologyNomLHS O₁`, `OntologyNominalFree O₂`, and
    standard SCC conditions plus `AllNomInhabited O₁` (every
    nominal in O₁ is consistent — automatic for globally consistent
    ontologies).

  *What is not covered.*

    Shape 2 (RHS nominal `gci C (.nom i)`), shape 4 (`gci (.nom i)
    (.nom j)`), and HasKey axioms.  These require the merging
    canonical model (Kazakov 2014 §6).

  All theorems audit-clean — only Lean foundation axioms.  No
  Mathlib.
-/

import ELKSDD.MOOSE

namespace ELKSDD
namespace ELpp
open SDD SCC Normalize

-- ============================================================
-- 1.  prodInterp.indiv reduction lemma for O₁'s individuals.
-- ============================================================

/-- For individuals in O₁'s individual signature, `prodInterp.indiv`
    reduces to the canonical first-projection form. -/
theorem prodInterp_indiv_O₁ {α : Type} (O₁ O₂ : Ontology) (I₁ : Interp α)
    (default₂ : CanonDom O₂)
    {i : Nat} (hi : i ∈ ontologyIndividuals O₁) :
    (prodInterp O₁ O₂ I₁ default₂).indiv i = (I₁.indiv i, default₂) := by
  show (if i ∈ ontologyIndividuals O₁ then ((I₁.indiv i, default₂) : α × CanonDom O₂)
        else (I₁.indiv 0, (canon O₂ default₂).indiv i)) = _
  rw [if_pos hi]

-- ============================================================
-- 2.  LHS-nominal axiom helper: extract i ∈ ontologyIndividuals.
-- ============================================================

/-- If `.gci (.nom i) D ∈ O`, then `i ∈ ontologyIndividuals O`.
    Direct from the definitions of `axiomIndividuals` and
    `ontologyIndividuals`. -/
theorem nomLHS_indiv_in_sig (O : Ontology) (i : Nat) (D : Concept)
    (hax : Axiom.gci (.nom i) D ∈ O) :
    i ∈ ontologyIndividuals O := by
  unfold ontologyIndividuals
  apply List.mem_flatMap.mpr
  refine ⟨_, hax, ?_⟩
  show i ∈ axiomIndividuals (.gci (.nom i) D)
  show i ∈ conceptIndividuals (.nom i) ++ conceptIndividuals D
  apply List.mem_append.mpr
  left
  show i ∈ [i]
  exact List.mem_cons_self

-- ============================================================
-- 3.  Per-axiom satisfaction with LHS-nominal allowed (O₁'s side).
-- ============================================================

/-- prodInterp satisfies axioms in O₁ where the LHS may be a
    nominal `{a}` with `a` in O₁'s individual signature. -/
theorem prodInterp_satisfies_O₁_axiom_nomLHS {α : Type}
    (O₁ O₂ : Ontology) (I₁ : Interp α) (default₂ : CanonDom O₂)
    (hO₁_nl : OntologyNomLHS O₁)
    (hI₁ : I₁.satisfies O₁) {ax : Axiom} (hax : ax ∈ O₁) :
    (prodInterp O₁ O₂ I₁ default₂).satisfiesAxiom ax := by
  have hax_sig : AxiomInSig O₁ ax := axiom_in_self_sig hax
  have hax_nl : AxiomNomLHS ax := hO₁_nl ax hax
  cases ax with
  | gci C D =>
      obtain ⟨hC_or, hD_nf⟩ := hax_nl
      obtain ⟨_hC_sig, hD_sig⟩ := ConceptInSig_of_AxiomInSig_gci hax_sig
      rcases hC_or with hC_nf | ⟨i, hCi⟩
      · -- C is nominal-free: identical to existing prodInterp_satisfies_O₁_axiom proof.
        intro p hC
        obtain ⟨a, b⟩ := p
        have h_I₁_C : I₁.eval C a :=
          (eval_prodInterp_O₁ O₁ O₂ I₁ default₂ C hC_nf _hC_sig a b).mp hC
        have h_I₁_D : I₁.eval D a := hI₁ _ hax a h_I₁_C
        exact (eval_prodInterp_O₁ O₁ O₂ I₁ default₂ D hD_nf hD_sig a b).mpr h_I₁_D
      · -- C = .nom i: the LHS-nominal case.
        subst hCi
        intro p hC
        -- hC : prodInterp.eval (.nom i) p = (p = prodInterp.indiv i).
        have hp_eq : p = (prodInterp O₁ O₂ I₁ default₂).indiv i := hC
        have hi_in : i ∈ ontologyIndividuals O₁ := nomLHS_indiv_in_sig O₁ i D hax
        rw [prodInterp_indiv_O₁ O₁ O₂ I₁ default₂ hi_in] at hp_eq
        subst hp_eq
        -- Goal: prodInterp.eval D ⟨I₁.indiv i, default₂⟩.
        have h_refl : I₁.eval (.nom i) (I₁.indiv i) := rfl
        have h_I₁_D : I₁.eval D (I₁.indiv i) := hI₁ _ hax (I₁.indiv i) h_refl
        exact (eval_prodInterp_O₁ O₁ O₂ I₁ default₂ D hD_nf hD_sig
                (I₁.indiv i) default₂).mpr h_I₁_D
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
  | range R C =>
      have hC_nf : NominalFree C := hax_nl
      intro p q hR_pq
      obtain ⟨a, b⟩ := p
      obtain ⟨a', b'⟩ := q
      have hR_O₁ : R ∈ ontologyRoles O₁ := range_role_in_sig hax_sig
      have hC_sig : ConceptInSig O₁ C := range_concept_in_sig hax_sig
      rw [prodInterp_role_O₁ O₁ O₂ I₁ default₂ hR_O₁ a a' b b'] at hR_pq
      obtain ⟨hR_aa', _hb⟩ := hR_pq
      have hI₁_C : I₁.eval C a' := hI₁ _ hax a a' hR_aa'
      exact (eval_prodInterp_O₁ O₁ O₂ I₁ default₂ C hC_nf hC_sig a' b').mpr hI₁_C
  | reflexive R =>
      intro p
      obtain ⟨a, b⟩ := p
      have hR_O₁ : R ∈ ontologyRoles O₁ := reflexive_role_in_sig hax_sig
      rw [prodInterp_role_O₁ O₁ O₂ I₁ default₂ hR_O₁ a a b b]
      exact ⟨hI₁ _ hax a, rfl⟩
  | hasKey _ _ => exact hax_nl.elim

-- ============================================================
-- 4.  prodInterp ⊨ O₁ ++ O₂ under nomLHS O₁.
-- ============================================================

/-- prodInterp satisfies the joint ontology when O₁ has the
    LHS-nominal-permissive structure and O₂ is nominal-free. -/
theorem prodInterp_satisfies_nomLHS {α : Type}
    (O₁ O₂ : Ontology) (I₁ : Interp α) (default₂ : CanonDom O₂)
    (hO₁_nl : OntologyNomLHS O₁) (hO₂_nf : OntologyNominalFree O₂)
    (hO₂_safe : RangeChainSafe O₂)
    (hI₁ : I₁.satisfies O₁) (hdisj : DisjointSigs O₁ O₂) :
    (prodInterp O₁ O₂ I₁ default₂).satisfies (O₁ ++ O₂) := by
  intro ax hax
  rcases List.mem_append.mp hax with h | h
  · exact prodInterp_satisfies_O₁_axiom_nomLHS O₁ O₂ I₁ default₂ hO₁_nl hI₁ h
  · exact prodInterp_satisfies_O₂_axiom O₁ O₂ I₁ default₂ hO₂_nf hO₂_safe hdisj h

-- ============================================================
-- 5.  Sat factor under nomLHS O₁.
-- ============================================================

/-- **Sat factorization with LHS-nominal O₁.**

    SCC factorization where O₁ may contain ABox-style ClassAssertion
    axioms `{a} ⊑ D` (D nominal-free).  All other axiom positions
    in O₁ remain nominal-free, and O₂ is fully nominal-free. -/
theorem Sat_factor_nomLHS
    {O₁ O₂ : Ontology}
    (hO₁_nl : OntologyNomLHS O₁) (hO₂_nf : OntologyNominalFree O₂)
    (hO₁_safe : RangeChainSafe O₁) (hO₂_safe : RangeChainSafe O₂)
    (hO₁_inhab : AllNomInhabited O₁)
    (hdisj : DisjointSigs O₁ O₂)
    (hO₂_cons : ¬ Sat O₂ .top .bot)
    {C D : Concept} (hC_nf : NominalFree C) (hD_nf : NominalFree D)
    (hC : ConceptInSig O₁ C) (hD : ConceptInSig O₁ D) :
    Sat (O₁ ++ O₂) C D ↔ Sat O₁ C D ∨ Sat O₂ .top .bot := by
  classical
  refine ⟨?_, ?_⟩
  · intro h
    by_cases hcons : Sat O₂ .top .bot
    · exact Or.inr hcons
    · refine Or.inl
        (complete_via_canon_nomLHS O₁ C D hO₁_nl hO₁_safe hO₁_inhab hC_nf hD_nf ?_)
      intro α I₁ hI₁ a ha
      let b₀ : CanonDom O₂ := ⟨.top, hO₂_cons⟩
      let M' : Interp (α × CanonDom O₂) := prodInterp O₁ O₂ I₁ b₀
      have hM' : M'.satisfies (O₁ ++ O₂) :=
        prodInterp_satisfies_nomLHS O₁ O₂ I₁ b₀
          hO₁_nl hO₂_nf hO₂_safe hI₁ hdisj
      have hentail : Entails (O₁ ++ O₂) C D := sound _ h
      have hCab : M'.eval C ⟨a, b₀⟩ :=
        (eval_prodInterp_O₁ O₁ O₂ I₁ b₀ C hC_nf hC a b₀).mpr ha
      have hDab : M'.eval D ⟨a, b₀⟩ := hentail M' hM' ⟨a, b₀⟩ hCab
      exact (eval_prodInterp_O₁ O₁ O₂ I₁ b₀ D hD_nf hD a b₀).mp hDab
  · intro h
    rcases h with hSat | hInc
    · exact Sat_factor_easy O₁ O₂ C D hSat
    · exact global_inconsistency_propagates hInc C D

-- ============================================================
-- 6.  Closed Sat factor (rules out global inconsistency disjunct).
-- ============================================================

/-- **Closed-form SCC factor under LHS-nominal O₁.**  Combines
    `Sat_factor_nomLHS` with consistency of O₂ to drop the
    global-inconsistency disjunct. -/
theorem scc_sat_factor_nomLHS
    {O₁ O₂ : Ontology}
    (hO₁_nl : OntologyNomLHS O₁) (hO₂_nf : OntologyNominalFree O₂)
    (hO₁_safe : RangeChainSafe O₁) (hO₂_safe : RangeChainSafe O₂)
    (hO₁_inhab : AllNomInhabited O₁)
    (hdisj : DisjointSigs O₁ O₂)
    (hcons : ¬ Sat O₂ .top .bot)
    {C D : Concept} (hC_nf : NominalFree C) (hD_nf : NominalFree D)
    (hC : ConceptInSig O₁ C) (hD : ConceptInSig O₁ D) :
    Sat (O₁ ++ O₂) C D ↔ Sat O₁ C D := by
  constructor
  · intro h
    rcases (Sat_factor_nomLHS hO₁_nl hO₂_nf hO₁_safe hO₂_safe hO₁_inhab
            hdisj hcons hC_nf hD_nf hC hD).mp h with h₁ | h₂
    · exact h₁
    · exact absurd h₂ hcons
  · exact Sat_factor_easy O₁ O₂ C D

-- ============================================================
-- Audit
-- ============================================================

#print axioms prodInterp_indiv_O₁
#print axioms nomLHS_indiv_in_sig
#print axioms prodInterp_satisfies_O₁_axiom_nomLHS
#print axioms prodInterp_satisfies_nomLHS
#print axioms Sat_factor_nomLHS
#print axioms scc_sat_factor_nomLHS

end ELpp
end ELKSDD
