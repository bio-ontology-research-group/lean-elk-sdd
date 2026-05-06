/-
  ELKSDD/SatFactorGeneral.lean
  ----------------------------
  *Generalized Sat-factor theorem*: SCC factorization for sub-ontologies.

  The existing `Sat_factor_refined` (SCC.lean) requires the analyzed
  ontology to be exactly `O₁ ++ O₂` with `ConceptInSig O₁ C/D` at the
  *analyzed* level.  This module generalizes to:

    * An ambient *signature-defining* ontology pair `(O₁_sig, O₂_sig)`
      with disjoint signatures.
    * An *analyzed* ontology pair `(O₁_actual, O₂_actual)` where
      `O₁_actual ⊆ O₁_sig` and `O₂_actual ⊆ O₂_sig`.
    * The query `(C, D)` is in `O₁_sig`'s signature (the *full* sig).

  *Why this matters.*

    The original `Sat_factor_refined`'s `ConceptInSig` requirement at
    the analyzed-ontology level is the key technical obstacle to
    proving a *per-world* Sat factorization
        `Sat (selectedAxioms M) C D ↔ Sat (selectedFromO₁ M) C D ∨ ...`
    where `selectedFromO₁ M ⊆ O₁` is the M-selected sub-ontology.
    For arbitrary M, `ConceptInSig (selectedFromO₁ M) C` can fail —
    M might exclude axioms mentioning C's atoms.

    `Sat_factor_refined_general` removes this obstacle: only the
    *signature-level* `ConceptInSig O₁_sig C` is required, which is
    a property of the full SCC, not the sub-ontology.

  *Headline theorem.*

    `Sat_factor_refined_general` —
        Sat (O₁_actual ++ O₂_actual) C D ↔
        Sat O₁_actual C D ∨ Sat O₂_actual ⊤ ⊥.

    Specialised to `O₁_actual = O₁_sig`, `O₂_actual = O₂_sig`, this
    recovers the existing `Sat_factor_refined`.

    Specialised to `O₁_actual = selectedFromO₁ M`,
    `O₂_actual = selectedFromO₂ M` (sub-ontologies via world
    selection), this yields the per-world Sat factor used in the
    WMC-level SCC factorization.

  *Proof strategy.*

    The proof structure mirrors `Sat_factor_refined_mpr` from
    SCC.lean, but builds `prodInterp` using `O₁_sig`/`O₂_sig` for
    atom dispatch (so `eval_prodInterp_O₁` works for `C ∈
    ConceptInSig O₁_sig`) while satisfying `O₁_actual ++ O₂_actual`
    (so the analyzed satisfaction works with `I₁ ⊨ O₁_actual`).
    The supporting `prodInterp_satisfies_actual_O₁_axiom` inlines
    the case analysis from `prodInterp_satisfies_O₁_axiom` with
    relaxed hypotheses.

  All theorems audit-clean — only Lean foundation axioms.
-/

import ELKSDD.MOOSE

namespace ELKSDD
namespace ELpp
open SDD SCC Normalize

-- ============================================================
-- Generalized prodInterp_satisfies for sub-ontologies.
-- Inlines the case analysis from `prodInterp_satisfies_O₁_axiom`
-- with relaxed hypotheses (build with O₁_sig, satisfy O₁_actual).
-- ============================================================

theorem prodInterp_satisfies_actual_O₁_axiom {α : Type}
    (O₁_sig O₂_sig : Ontology) (O₁_actual : Ontology)
    (I₁ : Interp α) (default₂ : CanonDom O₂_sig)
    (hO₁_sig_nf : OntologyNominalFree O₁_sig)
    (hO₁_sub : Subontology O₁_actual O₁_sig)
    (hI₁ : I₁.satisfies O₁_actual)
    {ax : Axiom} (hax : ax ∈ O₁_actual) :
    (prodInterp O₁_sig O₂_sig I₁ default₂).satisfiesAxiom ax := by
  have hax_sig : ax ∈ O₁_sig := hO₁_sub _ hax
  have hax_axsig : AxiomInSig O₁_sig ax := axiom_in_self_sig hax_sig
  have hax_nf : AxiomNominalFree ax := hO₁_sig_nf ax hax_sig
  cases ax with
  | gci C D =>
      intro p hC
      obtain ⟨a, b⟩ := p
      obtain ⟨hC_sig, hD_sig⟩ := ConceptInSig_of_AxiomInSig_gci hax_axsig
      obtain ⟨hC_nf, hD_nf⟩ := hax_nf
      have h_I₁_C : I₁.eval C a :=
        (eval_prodInterp_O₁ O₁_sig O₂_sig I₁ default₂ C hC_nf hC_sig a b).mp hC
      have h_I₁_D : I₁.eval D a := hI₁ _ hax a h_I₁_C
      exact (eval_prodInterp_O₁ O₁_sig O₂_sig I₁ default₂ D hD_nf hD_sig a b).mpr h_I₁_D
  | rinc R S =>
      intro p q hR_pq
      obtain ⟨a, b⟩ := p
      obtain ⟨a', b'⟩ := q
      have hR_sig : R ∈ ontologyRoles O₁_sig := rinc_role_left_in_sig hax_axsig
      have hS_sig : S ∈ ontologyRoles O₁_sig := rinc_role_right_in_sig hax_axsig
      rw [prodInterp_role_O₁ O₁_sig O₂_sig I₁ default₂ hR_sig a a' b b'] at hR_pq
      obtain ⟨hR_aa', hb⟩ := hR_pq
      have hS_aa' : I₁.ext_role S a a' := hI₁ _ hax a a' hR_aa'
      rw [prodInterp_role_O₁ O₁_sig O₂_sig I₁ default₂ hS_sig a a' b b']
      exact ⟨hS_aa', hb⟩
  | rchain R₁ R₂ S =>
      intro p q r hR₁_pq hR₂_qr
      obtain ⟨a, b⟩ := p
      obtain ⟨a', b'⟩ := q
      obtain ⟨a'', b''⟩ := r
      have hR₁_sig : R₁ ∈ ontologyRoles O₁_sig := rchain_role₁_in_sig hax_axsig
      have hR₂_sig : R₂ ∈ ontologyRoles O₁_sig := rchain_role₂_in_sig hax_axsig
      have hS_sig  : S  ∈ ontologyRoles O₁_sig := rchain_role₃_in_sig hax_axsig
      rw [prodInterp_role_O₁ O₁_sig O₂_sig I₁ default₂ hR₁_sig a a' b b'] at hR₁_pq
      rw [prodInterp_role_O₁ O₁_sig O₂_sig I₁ default₂ hR₂_sig a' a'' b' b''] at hR₂_qr
      obtain ⟨hR₁_aa', hb_eq_b'⟩ := hR₁_pq
      obtain ⟨hR₂_a'a'', hb'_eq_b''⟩ := hR₂_qr
      have hS_aa'' : I₁.ext_role S a a'' := hI₁ _ hax a a' a'' hR₁_aa' hR₂_a'a''
      rw [prodInterp_role_O₁ O₁_sig O₂_sig I₁ default₂ hS_sig a a'' b b'']
      exact ⟨hS_aa'', hb_eq_b'.trans hb'_eq_b''⟩
  | range R C =>
      have hC_nf : NominalFree C := hax_nf
      intro p q hR_pq
      obtain ⟨a, b⟩ := p
      obtain ⟨a', b'⟩ := q
      have hR_sig : R ∈ ontologyRoles O₁_sig := range_role_in_sig hax_axsig
      have hC_sig : ConceptInSig O₁_sig C := range_concept_in_sig hax_axsig
      rw [prodInterp_role_O₁ O₁_sig O₂_sig I₁ default₂ hR_sig a a' b b'] at hR_pq
      obtain ⟨hR_aa', _hb⟩ := hR_pq
      have hI₁_C : I₁.eval C a' := hI₁ _ hax a a' hR_aa'
      exact (eval_prodInterp_O₁ O₁_sig O₂_sig I₁ default₂ C hC_nf hC_sig a' b').mpr hI₁_C
  | reflexive R =>
      intro p
      obtain ⟨a, b⟩ := p
      have hR_sig : R ∈ ontologyRoles O₁_sig := reflexive_role_in_sig hax_axsig
      rw [prodInterp_role_O₁ O₁_sig O₂_sig I₁ default₂ hR_sig a a b b]
      exact ⟨hI₁ _ hax a, rfl⟩
  | hasKey _ _ => exact hax_nf.elim

theorem prodInterp_satisfies_actual_O₂_axiom {α : Type}
    (O₁_sig O₂_sig : Ontology) (O₂_actual : Ontology)
    (I₁ : Interp α) (default₂ : CanonDom O₂_sig)
    (hO₂_sig_nf : OntologyNominalFree O₂_sig) (hO₂_sig_safe : RangeChainSafe O₂_sig)
    (hO₂_sub : Subontology O₂_actual O₂_sig)
    (hdisj : DisjointSigs O₁_sig O₂_sig)
    {ax : Axiom} (hax : ax ∈ O₂_actual) :
    (prodInterp O₁_sig O₂_sig I₁ default₂).satisfiesAxiom ax :=
  prodInterp_satisfies_O₂_axiom O₁_sig O₂_sig I₁ default₂
    hO₂_sig_nf hO₂_sig_safe hdisj (hO₂_sub _ hax)

theorem prodInterp_satisfies_actual {α : Type}
    (O₁_sig O₂_sig : Ontology) (O₁_actual O₂_actual : Ontology)
    (I₁ : Interp α) (default₂ : CanonDom O₂_sig)
    (hO₁_sig_nf : OntologyNominalFree O₁_sig)
    (hO₂_sig_nf : OntologyNominalFree O₂_sig)
    (hO₂_sig_safe : RangeChainSafe O₂_sig)
    (hO₁_sub : Subontology O₁_actual O₁_sig)
    (hO₂_sub : Subontology O₂_actual O₂_sig)
    (hI₁ : I₁.satisfies O₁_actual)
    (hdisj : DisjointSigs O₁_sig O₂_sig) :
    (prodInterp O₁_sig O₂_sig I₁ default₂).satisfies (O₁_actual ++ O₂_actual) := by
  intro ax hax
  rcases List.mem_append.mp hax with h | h
  · exact prodInterp_satisfies_actual_O₁_axiom O₁_sig O₂_sig O₁_actual I₁ default₂
          hO₁_sig_nf hO₁_sub hI₁ h
  · exact prodInterp_satisfies_actual_O₂_axiom O₁_sig O₂_sig O₂_actual I₁ default₂
          hO₂_sig_nf hO₂_sig_safe hO₂_sub hdisj h

-- ============================================================
-- The headline theorem: generalized Sat_factor_refined.
-- ============================================================

/-- **Generalized Sat-factor theorem.**

    For arbitrary sub-ontologies `O₁_actual ⊆ O₁_sig`, `O₂_actual ⊆
    O₂_sig` with `O₁_sig`/`O₂_sig` having disjoint signatures and
    `O₂_sig` consistent, queries in `O₁_sig`'s signature factor:

      Sat (O₁_actual ++ O₂_actual) C D ↔
      Sat O₁_actual C D ∨ Sat O₂_actual ⊤ ⊥.

    The key advance over `Sat_factor_refined` (SCC.lean): the
    `ConceptInSig` hypothesis is on the *signature-level* `O₁_sig`,
    not the analyzed-level `O₁_actual`.  This unblocks per-world
    factorization where M-selected sub-ontologies might lack atoms
    in their signature.

    Specialised to `O₁_actual = O₁_sig`, `O₂_actual = O₂_sig` (full
    ontologies), this recovers `Sat_factor_refined`. -/
theorem Sat_factor_refined_general
    {O₁_sig O₂_sig : Ontology}
    {O₁_actual O₂_actual : Ontology}
    (hO₁_sig_nf : OntologyNominalFree O₁_sig)
    (hO₂_sig_nf : OntologyNominalFree O₂_sig)
    (hO₂_sig_safe : RangeChainSafe O₂_sig)
    (hO₂_sig_cons : ¬ Sat O₂_sig .top .bot)
    (hO₁_actual_nf : OntologyNominalFree O₁_actual)
    (hO₁_actual_safe : RangeChainSafe O₁_actual)
    (hO₁_sub : Subontology O₁_actual O₁_sig)
    (hO₂_sub : Subontology O₂_actual O₂_sig)
    (hdisj_sig : DisjointSigs O₁_sig O₂_sig)
    {C D : Concept} (hC_nf : NominalFree C) (hD_nf : NominalFree D)
    (hC : ConceptInSig O₁_sig C) (hD : ConceptInSig O₁_sig D) :
    Sat (O₁_actual ++ O₂_actual) C D ↔
    Sat O₁_actual C D ∨ Sat O₂_actual .top .bot := by
  classical
  refine ⟨?_, ?_⟩
  · intro h
    by_cases hcons : Sat O₂_actual .top .bot
    · exact Or.inr hcons
    · refine Or.inl
        (complete_via_canon O₁_actual C D hO₁_actual_nf hO₁_actual_safe hC_nf hD_nf ?_)
      intro α I₁ hI₁ a ha
      let b₀ : CanonDom O₂_sig := ⟨.top, hO₂_sig_cons⟩
      let M' : Interp (α × CanonDom O₂_sig) := prodInterp O₁_sig O₂_sig I₁ b₀
      have hM' : M'.satisfies (O₁_actual ++ O₂_actual) :=
        prodInterp_satisfies_actual O₁_sig O₂_sig O₁_actual O₂_actual I₁ b₀
          hO₁_sig_nf hO₂_sig_nf hO₂_sig_safe hO₁_sub hO₂_sub hI₁ hdisj_sig
      have hentail : Entails (O₁_actual ++ O₂_actual) C D := sound _ h
      have hCab : M'.eval C ⟨a, b₀⟩ :=
        (eval_prodInterp_O₁ O₁_sig O₂_sig I₁ b₀ C hC_nf hC a b₀).mpr ha
      have hDab : M'.eval D ⟨a, b₀⟩ := hentail M' hM' ⟨a, b₀⟩ hCab
      exact (eval_prodInterp_O₁ O₁_sig O₂_sig I₁ b₀ D hD_nf hD a b₀).mp hDab
  · intro h
    rcases h with hSat | hInc
    · exact Sat_factor_easy O₁_actual O₂_actual C D hSat
    · exact global_inconsistency_propagates hInc C D

-- ============================================================
-- Audit
-- ============================================================

#print axioms prodInterp_satisfies_actual_O₁_axiom
#print axioms prodInterp_satisfies_actual_O₂_axiom
#print axioms prodInterp_satisfies_actual
#print axioms Sat_factor_refined_general

end ELpp
end ELKSDD
