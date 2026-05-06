import ELKSDD.SatFactorGeneral

namespace ELKSDD
namespace ELpp
open SDD SCC Normalize

noncomputable def restrictWorld₁ {O₁ O₂ : Ontology} (M : World (O₁ ++ O₂)) :
    World O₁ :=
  fun i => M ⟨i.val, by
    have h : (O₁ ++ O₂).length = O₁.length + O₂.length := List.length_append
    rw [h]; omega⟩

noncomputable def restrictWorld₂ {O₁ O₂ : Ontology} (M : World (O₁ ++ O₂)) :
    World O₂ :=
  fun i => M ⟨O₁.length + i.val, by
    have h : (O₁ ++ O₂).length = O₁.length + O₂.length := List.length_append
    rw [h]; omega⟩

noncomputable def selectedFromO₁ (O₁ O₂ : Ontology) (M : World (O₁ ++ O₂)) : Ontology :=
  selectedAxioms O₁ (restrictWorld₁ M)

noncomputable def selectedFromO₂ (O₁ O₂ : Ontology) (M : World (O₁ ++ O₂)) : Ontology :=
  selectedAxioms O₂ (restrictWorld₂ M)

theorem selectedFromO₁_sub (O₁ O₂ : Ontology) (M : World (O₁ ++ O₂)) :
    Subontology (selectedFromO₁ O₁ O₂ M) O₁ :=
  selectedAxioms_subset O₁ (restrictWorld₁ M)

theorem selectedFromO₂_sub (O₁ O₂ : Ontology) (M : World (O₁ ++ O₂)) :
    Subontology (selectedFromO₂ O₁ O₂ M) O₂ :=
  selectedAxioms_subset O₂ (restrictWorld₂ M)

-- Helper: the i-th elt of selectedAxioms is determined by a Fin position.
-- Membership in selectedAxioms = ∃ i with M i = true and ax = O.get i.

theorem mem_selectedAxioms_iff (O : Ontology) (M : World O) (ax : Axiom) :
    ax ∈ selectedAxioms O M ↔ ∃ i : Fin O.length, M i = true ∧ ax = O.get i := by
  unfold selectedAxioms
  rw [List.mem_filterMap]
  refine ⟨?_, ?_⟩
  · rintro ⟨i, _hin, hi⟩
    by_cases hMi : M i = true
    · simp only [if_pos hMi] at hi
      exact ⟨i, hMi, (Option.some_inj.mp hi).symm⟩
    · simp only [if_neg hMi] at hi
      cases hi
  · rintro ⟨i, hMi, hax⟩
    refine ⟨i, List.mem_finRange _, ?_⟩
    simp only [if_pos hMi]
    exact congrArg some hax.symm

-- The two subontology directions:

theorem selectedAxioms_sub_decompose (O₁ O₂ : Ontology) (M : World (O₁ ++ O₂)) :
    Subontology (selectedAxioms (O₁ ++ O₂) M)
                (selectedFromO₁ O₁ O₂ M ++ selectedFromO₂ O₁ O₂ M) := by
  intro ax hax
  obtain ⟨i, hMi, hax_eq⟩ := (mem_selectedAxioms_iff _ _ _).mp hax
  by_cases hi_lt : i.val < O₁.length
  · apply List.mem_append.mpr; left
    apply (mem_selectedAxioms_iff _ _ _).mpr
    refine ⟨⟨i.val, hi_lt⟩, ?_, ?_⟩
    · -- restrictWorld₁ M ⟨i.val, hi_lt⟩ = M i = true.
      unfold restrictWorld₁
      show M ⟨i.val, _⟩ = true
      have hfeq : (⟨i.val, i.isLt⟩ : Fin (O₁ ++ O₂).length) = i := Fin.ext rfl
      rw [hfeq]; exact hMi
    · -- ax = O₁.get ⟨i.val, hi_lt⟩.
      show ax = O₁[i.val]'hi_lt
      rw [hax_eq]
      show (O₁ ++ O₂)[i.val]'i.isLt = O₁[i.val]'hi_lt
      rw [List.getElem_append (i := i.val) i.isLt, dif_pos hi_lt]
  · apply List.mem_append.mpr; right
    have h_len : (O₁ ++ O₂).length = O₁.length + O₂.length := List.length_append
    have hi_diff : i.val - O₁.length < O₂.length := by have := i.isLt; omega
    apply (mem_selectedAxioms_iff _ _ _).mpr
    refine ⟨⟨i.val - O₁.length, hi_diff⟩, ?_, ?_⟩
    · unfold restrictWorld₂
      show M ⟨O₁.length + (i.val - O₁.length), _⟩ = true
      have heq : O₁.length + (i.val - O₁.length) = i.val := by omega
      have hbd : O₁.length + (i.val - O₁.length) < (O₁ ++ O₂).length := by
        rw [heq]; exact i.isLt
      have hfeq : (⟨O₁.length + (i.val - O₁.length), hbd⟩ : Fin _) = i := Fin.ext heq
      rw [hfeq]; exact hMi
    · show ax = O₂[i.val - O₁.length]'hi_diff
      rw [hax_eq]
      show (O₁ ++ O₂)[i.val]'i.isLt = O₂[i.val - O₁.length]'hi_diff
      rw [List.getElem_append (i := i.val) i.isLt, dif_neg hi_lt]

theorem decompose_sub_selectedAxioms (O₁ O₂ : Ontology) (M : World (O₁ ++ O₂)) :
    Subontology (selectedFromO₁ O₁ O₂ M ++ selectedFromO₂ O₁ O₂ M)
                (selectedAxioms (O₁ ++ O₂) M) := by
  intro ax hax
  rcases List.mem_append.mp hax with h | h
  · -- ax ∈ selectedFromO₁ → ax = O₁.get j with restrictWorld₁ M j = true.
    obtain ⟨j, hMj, hax_eq⟩ := (mem_selectedAxioms_iff _ _ _).mp h
    apply (mem_selectedAxioms_iff _ _ _).mpr
    refine ⟨⟨j.val, by rw [List.length_append]; have := j.isLt; omega⟩, ?_, ?_⟩
    · -- M (lifted j) = true.  By definition of restrictWorld₁.
      unfold restrictWorld₁ at hMj
      exact hMj
    · -- ax = (O₁ ++ O₂).get (lifted j) = O₁.get j.
      show ax = (O₁ ++ O₂)[j.val]'(by rw [List.length_append]; have := j.isLt; omega)
      rw [hax_eq]
      show O₁[j.val]'j.isLt = (O₁ ++ O₂)[j.val]'_
      rw [List.getElem_append (i := j.val)]
      rw [dif_pos j.isLt]
  · -- ax ∈ selectedFromO₂ → ax = O₂.get j with restrictWorld₂ M j = true.
    obtain ⟨j, hMj, hax_eq⟩ := (mem_selectedAxioms_iff _ _ _).mp h
    have hi_lt : O₁.length + j.val < (O₁ ++ O₂).length := by
      rw [List.length_append]; have := j.isLt; omega
    have hi_ge : ¬ O₁.length + j.val < O₁.length := by omega
    apply (mem_selectedAxioms_iff _ _ _).mpr
    refine ⟨⟨O₁.length + j.val, hi_lt⟩, ?_, ?_⟩
    · unfold restrictWorld₂ at hMj
      show M ⟨O₁.length + j.val, _⟩ = true
      exact hMj
    · show ax = (O₁ ++ O₂)[O₁.length + j.val]'hi_lt
      rw [hax_eq]
      show O₂[j.val]'j.isLt = (O₁ ++ O₂)[O₁.length + j.val]'hi_lt
      rw [List.getElem_append (i := O₁.length + j.val) hi_lt, dif_neg hi_ge]
      have heq : O₁.length + j.val - O₁.length = j.val := by omega
      simp only [heq]

#print axioms selectedAxioms_sub_decompose
#print axioms decompose_sub_selectedAxioms

end ELpp
end ELKSDD

namespace ELKSDD.ELpp
open SDD SCC Normalize

-- ============================================================
-- Sat-equivalence: selectedAxioms M ↔ selectedFromO₁ ++ selectedFromO₂
-- ============================================================

theorem sat_selectedAxioms_decompose_iff (O₁ O₂ : Ontology)
    (M : World (O₁ ++ O₂)) (C D : Concept) :
    Sat (selectedAxioms (O₁ ++ O₂) M) C D ↔
    Sat (selectedFromO₁ O₁ O₂ M ++ selectedFromO₂ O₁ O₂ M) C D := by
  refine ⟨?_, ?_⟩
  · exact Sat_mono (selectedAxioms_sub_decompose O₁ O₂ M)
  · exact Sat_mono (decompose_sub_selectedAxioms O₁ O₂ M)

-- ============================================================
-- Per-world Sat factor (the main consequence of Sat_factor_refined_general)
-- ============================================================

theorem per_world_sat_factor
    {O₁ O₂ : Ontology}
    (hO₁_nf : OntologyNominalFree O₁) (hO₂_nf : OntologyNominalFree O₂)
    (hO₁_safe : RangeChainSafe O₁) (hO₂_safe : RangeChainSafe O₂)
    (hO₂_cons : ¬ Sat O₂ .top .bot)
    (hdisj : DisjointSigs O₁ O₂)
    {C D : Concept} (hC_nf : NominalFree C) (hD_nf : NominalFree D)
    (hC : ConceptInSig O₁ C) (hD : ConceptInSig O₁ D)
    (M : World (O₁ ++ O₂)) :
    Sat (selectedAxioms (O₁ ++ O₂) M) C D ↔
    Sat (selectedFromO₁ O₁ O₂ M) C D ∨ Sat (selectedFromO₂ O₁ O₂ M) .top .bot := by
  rw [sat_selectedAxioms_decompose_iff]
  apply Sat_factor_refined_general hO₁_nf hO₂_nf hO₂_safe hO₂_cons
  · exact OntologyNominalFree_subontology hO₁_nf (selectedFromO₁_sub _ _ _)
  · exact RangeChainSafe_subontology hO₁_safe (selectedFromO₁_sub _ _ _)
  · exact selectedFromO₁_sub _ _ _
  · exact selectedFromO₂_sub _ _ _
  · exact hdisj
  · exact hC_nf
  · exact hD_nf
  · exact hC
  · exact hD

-- ============================================================
-- Under consistent O₂, the right disjunct vanishes (Sat_mono).
-- ============================================================

theorem per_world_sat_factor_consistent
    {O₁ O₂ : Ontology}
    (hO₁_nf : OntologyNominalFree O₁) (hO₂_nf : OntologyNominalFree O₂)
    (hO₁_safe : RangeChainSafe O₁) (hO₂_safe : RangeChainSafe O₂)
    (hO₂_cons : ¬ Sat O₂ .top .bot)
    (hdisj : DisjointSigs O₁ O₂)
    {C D : Concept} (hC_nf : NominalFree C) (hD_nf : NominalFree D)
    (hC : ConceptInSig O₁ C) (hD : ConceptInSig O₁ D)
    (M : World (O₁ ++ O₂)) :
    Sat (selectedAxioms (O₁ ++ O₂) M) C D ↔
    Sat (selectedFromO₁ O₁ O₂ M) C D := by
  have h := per_world_sat_factor hO₁_nf hO₂_nf hO₁_safe hO₂_safe hO₂_cons hdisj
            hC_nf hD_nf hC hD M
  rw [h]
  -- Eliminate the Sat O₂' ⊤ ⊥ disjunct using consistency.
  have h_sub₂ : Sat (selectedFromO₂ O₁ O₂ M) .top .bot → Sat O₂ .top .bot :=
    fun h => Sat_mono (selectedFromO₂_sub _ _ _) h
  constructor
  · rintro (h₁ | h₂)
    · exact h₁
    · exact absurd (h_sub₂ h₂) hO₂_cons
  · intro h₁; exact Or.inl h₁

#print axioms per_world_sat_factor
#print axioms per_world_sat_factor_consistent

end ELKSDD.ELpp
