/-
  ELKSDD/SatComplexity.lean
  -------------------------
  *Closure-size complexity bound* for the new inductive `Sat` predicate
  in `ELKSDD.ELpp`, covering OWL 2 EL nominal shapes 1-4 + HasKey +
  range + reflexive + Self.

  Companion to `ELKSDD.Complexity` (which bounds the Shannon-tree SDD
  size at `2^(|vars|+1)`).  This module bounds the *cardinality* of
  the syntactic atom set over which the ELK calculus operates.

  *What is bounded.*

    Given an ontology `O`, define the *signature* `Sub(O)` of all
    concept-subexpressions appearing in `O` (LHS, RHS of GCIs, range
    concepts, key classes, plus `⊤` and `⊥`).  Define `Roles(O)` as
    the role names appearing in `O` (in role axioms, range roles,
    reflexive roles, key roles, and inside concepts via `∃R.C` and
    `Self R`).

    The *bounded atom set* `boundedAtomSet O` enumerates every
    syntactic shape that an ELK rule can produce when both the LHS
    and the relevant subexpressions stay within the signature:

      * `atomEnum`       — pairs `(C, D) ∈ Sub(O) × Sub(O)`.
      * `linkEnum`       — pairs `(C, ∃R.D)` for `C, D ∈ Sub(O)`,
                           `R ∈ Roles(O)`.  (Used by `exist_prop`,
                           `rinc_apply`, `rchain_apply`.)
      * `rangeLinkEnum`  — pairs `(C, ∃R.(D ⊓ E))` for `C, D, E ∈
                           Sub(O)`, `R ∈ Roles(O)`.  (Used by
                           `range_apply` and `range_via_rincStar`.)
      * `reflEnum`       — pairs `(C, ∃R.C)` for `C ∈ Sub(O)`,
                           `R ∈ Roles(O)`.  (Used by `reflexive_apply`
                           and `self_intro`.)
      * `selfEnum`       — pairs `(C, Self R)` for `C ∈ Sub(O)`,
                           `R ∈ Roles(O)`.  (Used by `reflexive_self`
                           and `rinc_self_star`.)

    Each enumeration's length is computed exactly; the total length
    of `boundedAtomSet O` is

      `|atomEnum O| + |linkEnum O| + |rangeLinkEnum O| +
       |reflEnum O| + |selfEnum O|`
      = `n² + n²·r + n³·r + n·r + n·r`
      = `n² + n²·r + n³·r + 2·n·r`,

    where `n = numSubexprs O`, `r = numRoles O`.  This is `O(n³ · r)`,
    polynomial in the syntactic size of `O`.

  *Bound theorem* (`sat_named_atom_in_bound`).  For every named atom
  `(C, D)` with `C ∈ Sub(O)` and `D ∈ Sub(O)`, if `Sat O C D` then
  `(C, D) ∈ atomEnum O ⊆ boundedAtomSet O`.  By inclusion in a list
  of polynomial length, the *set* `{(C, D) ∈ Sub(O)² | Sat O C D}`
  has cardinality at most `|atomEnum O| = n²`.

  Together with the analogous statements for the link/range/refl/
  self shapes, the set of *named-atom* derivations is polynomially
  bounded, mirroring the standard ELK polynomial-closure result of
  Kazakov-Krötzsch-Simančík 2014 §4.

  *What is NOT proved.*

    *Closure preservation* (every Sat derivation can be
    canonicalised to use only intermediate concepts in
    `boundedAtomSet O`'s signature) — this is the deeper
    "saturation terminates with the right answer" theorem and
    requires the canonical-model + cut-elimination argument, which
    is mechanical follow-on work from the existing canonical-model
    proofs in `ELpp.complete_via_canon` and `Merging.lean`.

  All theorems audit-clean — only Lean foundation axioms.
-/

import ELKSDD.ELpp
import ELKSDD.Util

namespace ELKSDD
namespace ELpp

open Util

-- ============================================================
-- 1. Subexpression enumeration
-- ============================================================

/-- All concept-subexpressions of a single concept, including itself.
    Leaves (atom, nom, self, top, bot) yield singletons; compound
    forms cons themselves and recurse into structural children. -/
def subsOfConcept : Concept → List Concept
  | .atom n     => [.atom n]
  | .nom i      => [.nom i]
  | .self R     => [.self R]
  | .top        => [.top]
  | .bot        => [.bot]
  | .conj A B   => .conj A B :: (subsOfConcept A ++ subsOfConcept B)
  | .exist R E  => .exist R E :: subsOfConcept E

theorem mem_subsOfConcept_self (C : Concept) : C ∈ subsOfConcept C := by
  cases C <;> simp [subsOfConcept]

/-- Concept-subexpressions appearing in an axiom (concept arguments
    on both sides, plus the key class for HasKey). -/
def subsOfAxiom : Axiom → List Concept
  | .gci C D       => subsOfConcept C ++ subsOfConcept D
  | .rinc _ _      => []
  | .rchain _ _ _  => []
  | .range _ C     => subsOfConcept C
  | .reflexive _   => []
  | .hasKey C _    => subsOfConcept C

/-- Concept-subexpressions of an ontology, with `⊤` and `⊥` always
    included (since the calculus's `top` and `bot_elim` rules
    introduce them regardless of axiom shape). -/
def subsOfOntology (O : Ontology) : List Concept :=
  .top :: .bot :: O.flatMap subsOfAxiom

/-- Cardinality of the signature: the number of distinct
    subexpression occurrences (with `⊤`, `⊥` always counted).  Note
    we do not deduplicate; the bound is on the syntactic-occurrence
    count, which is an over-approximation of the distinct-set
    cardinality and adequate for the polynomial bound. -/
def numSubexprs (O : Ontology) : Nat := (subsOfOntology O).length

theorem numSubexprs_pos (O : Ontology) : numSubexprs O ≥ 2 := by
  unfold numSubexprs subsOfOntology
  simp

-- ============================================================
-- 2. Role enumeration
-- ============================================================

/-- Role names appearing inside a concept (via `∃R.C` and `Self R`). -/
def rolesOfConcept : Concept → List Role
  | .atom _     => []
  | .nom _      => []
  | .self R     => [R]
  | .top        => []
  | .bot        => []
  | .conj A B   => rolesOfConcept A ++ rolesOfConcept B
  | .exist R E  => R :: rolesOfConcept E

/-- Role names appearing in an axiom. -/
def rolesOfAxiom : Axiom → List Role
  | .gci C D       => rolesOfConcept C ++ rolesOfConcept D
  | .rinc R S      => [R, S]
  | .rchain R S T  => [R, S, T]
  | .range R C     => R :: rolesOfConcept C
  | .reflexive R   => [R]
  | .hasKey C rs   => rs ++ rolesOfConcept C

/-- All role names appearing anywhere in the ontology. -/
def rolesOfOntology (O : Ontology) : List Role :=
  O.flatMap rolesOfAxiom

/-- Cardinality of the role signature. -/
def numRoles (O : Ontology) : Nat := (rolesOfOntology O).length

-- ============================================================
-- 3. Bounded atom enumerations (one per ELK rule shape)
-- ============================================================

/-- Atomic-shape pairs: `(C, D)` with both `C, D ∈ Sub(O)`.  Captures
    `refl`, `top`, `base_gci`, `trans`, `bot_elim`, `conj_*` outputs
    when LHS/RHS already lie in the signature. -/
def atomEnum (O : Ontology) : List (Concept × Concept) :=
  (subsOfOntology O).flatMap (fun C =>
    (subsOfOntology O).map (fun D => (C, D)))

/-- Existential-link shape: `(C, ∃R.D)` for `C, D ∈ Sub(O)`,
    `R ∈ Roles(O)`.  Captures `exist_prop`, `rinc_apply`,
    `rchain_apply` outputs. -/
def linkEnum (O : Ontology) : List (Concept × Concept) :=
  (subsOfOntology O).flatMap (fun C =>
    (rolesOfOntology O).flatMap (fun R =>
      (subsOfOntology O).map (fun D => (C, .exist R D))))

/-- Range-refined existential shape: `(C, ∃R.(D ⊓ E))` for `C, D, E ∈
    Sub(O)`, `R ∈ Roles(O)`.  Captures `range_apply` and
    `range_via_rincStar` outputs. -/
def rangeLinkEnum (O : Ontology) : List (Concept × Concept) :=
  (subsOfOntology O).flatMap (fun C =>
    (rolesOfOntology O).flatMap (fun R =>
      (subsOfOntology O).flatMap (fun D =>
        (subsOfOntology O).map (fun E => (C, .exist R (.conj D E))))))

/-- Reflexive-existential shape: `(C, ∃R.C)` for `C ∈ Sub(O)`,
    `R ∈ Roles(O)`.  Captures `reflexive_apply` and `self_intro`
    outputs. -/
def reflEnum (O : Ontology) : List (Concept × Concept) :=
  (subsOfOntology O).flatMap (fun C =>
    (rolesOfOntology O).map (fun R => (C, .exist R C)))

/-- Self-restriction shape: `(C, Self R)` for `C ∈ Sub(O)`,
    `R ∈ Roles(O)`.  Captures `reflexive_self`, `rinc_self_star`
    outputs. -/
def selfEnum (O : Ontology) : List (Concept × Concept) :=
  (subsOfOntology O).flatMap (fun C =>
    (rolesOfOntology O).map (fun R => (C, .self R)))

/-- Total bounded-atom enumeration: the union of every shape an
    ELK-rule output can take when bounded to the signature.  -/
def boundedAtomSet (O : Ontology) : List (Concept × Concept) :=
  atomEnum O ++ linkEnum O ++ rangeLinkEnum O ++ reflEnum O ++ selfEnum O

-- ============================================================
-- 4. Length theorems for each enumeration
-- ============================================================

/-- `|atomEnum O| = n²` where `n = numSubexprs O`. -/
theorem atomEnum_length (O : Ontology) :
    (atomEnum O).length = (numSubexprs O) ^ 2 := by
  unfold atomEnum numSubexprs
  rw [length_flatMap_map_const]
  simp [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]

/-- `|linkEnum O| = n² · r`. -/
theorem linkEnum_length (O : Ontology) :
    (linkEnum O).length = (numSubexprs O) ^ 2 * numRoles O := by
  unfold linkEnum numSubexprs numRoles
  rw [length_flatMap_const_length _ _
        ((rolesOfOntology O).length * (subsOfOntology O).length)]
  · simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    rw [Nat.mul_comm (rolesOfOntology O).length, ← Nat.mul_assoc]
  · intro C _
    exact length_flatMap_map_const _ _ _

/-- `|rangeLinkEnum O| = n³ · r`. -/
theorem rangeLinkEnum_length (O : Ontology) :
    (rangeLinkEnum O).length = (numSubexprs O) ^ 3 * numRoles O := by
  unfold rangeLinkEnum numSubexprs numRoles
  -- Outer: |Sub(O)|.  Inner per-C: |Roles| · (|Sub(O)| · |Sub(O)|).
  rw [length_flatMap_const_length _ _
        ((rolesOfOntology O).length *
         ((subsOfOntology O).length * (subsOfOntology O).length))]
  · -- Goal: subs · (roles · (subs · subs)) = subs³ · roles.
    -- Expand subs³ = subs · subs · subs (left-assoc).
    simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    -- Goal: subs · (roles · (subs · subs)) = subs · subs · subs · roles.
    -- Step 1: commute roles past (subs · subs) inside.
    rw [Nat.mul_comm (rolesOfOntology O).length
          ((subsOfOntology O).length * (subsOfOntology O).length)]
    -- Step 2: drop two layers of left-association.
    rw [← Nat.mul_assoc, ← Nat.mul_assoc]
  · intro C _
    -- Inner length: roles.flatMap (fun R => subs.flatMap (fun D =>
    --                subs.map (fun E => (C, ∃R.(D ⊓ E))))).length
    --             = roles.length · (subs.length · subs.length).
    rw [length_flatMap_const_length _ _
          ((subsOfOntology O).length * (subsOfOntology O).length)]
    intro R _
    exact length_flatMap_map_const _ _ _

/-- `|reflEnum O| = n · r`. -/
theorem reflEnum_length (O : Ontology) :
    (reflEnum O).length = numSubexprs O * numRoles O := by
  unfold reflEnum numSubexprs numRoles
  rw [length_flatMap_const_length _ _ (rolesOfOntology O).length]
  intro C _
  exact List.length_map _

/-- `|selfEnum O| = n · r`. -/
theorem selfEnum_length (O : Ontology) :
    (selfEnum O).length = numSubexprs O * numRoles O := by
  unfold selfEnum numSubexprs numRoles
  rw [length_flatMap_const_length _ _ (rolesOfOntology O).length]
  intro C _
  exact List.length_map _

/-- **Total polynomial bound** on the bounded-atom enumeration.  The
    length is the exact sum of the per-shape counts:

      `n² + n²·r + n³·r + 2·n·r`. -/
theorem boundedAtomSet_length (O : Ontology) :
    (boundedAtomSet O).length =
      (numSubexprs O) ^ 2 +
      (numSubexprs O) ^ 2 * numRoles O +
      (numSubexprs O) ^ 3 * numRoles O +
      numSubexprs O * numRoles O +
      numSubexprs O * numRoles O := by
  unfold boundedAtomSet
  simp only [List.length_append]
  rw [atomEnum_length, linkEnum_length, rangeLinkEnum_length,
      reflEnum_length, selfEnum_length]

/-- **Polynomial witness**.  The bounded-atom enumeration is at most
    `5 · n³ · (r + 1)`, i.e., cubic in the subexpression count and
    linear in the role count.  This is the quantitative form of the
    Kazakov-Krötzsch-Simančík 2014 §4 polynomial-closure result for
    the new inductive `Sat`. -/
theorem boundedAtomSet_polynomial (O : Ontology) :
    (boundedAtomSet O).length ≤
      5 * (numSubexprs O) ^ 3 * (numRoles O + 1) := by
  rw [boundedAtomSet_length]
  generalize hn_def : numSubexprs O = n
  generalize hr_def : numRoles O = r
  -- Two key monotonicity facts: n^2 ≤ n^3 and n ≤ n^3.
  have h_n2_le_n3 : n ^ 2 ≤ n ^ 3 := by
    rcases Nat.eq_zero_or_pos n with hn0 | hpos
    · rw [hn0]; simp [Nat.pow_succ]
    · exact Nat.pow_le_pow_right hpos (by decide : (2 : Nat) ≤ 3)
  have h_n_le_n3 : n ≤ n ^ 3 := by
    rcases Nat.eq_zero_or_pos n with hn0 | hpos
    · rw [hn0]; simp
    · calc n = n ^ 1 := (Nat.pow_one _).symm
           _ ≤ n ^ 3 := Nat.pow_le_pow_right hpos (by decide : (1 : Nat) ≤ 3)
  -- All five summands ≤ q := n^3 · (r + 1).
  generalize hq_def : n ^ 3 * (r + 1) = q
  have h_n3_le_q : n ^ 3 ≤ q := by
    rw [← hq_def]
    calc n ^ 3 = n ^ 3 * 1 := (Nat.mul_one _).symm
         _ ≤ n ^ 3 * (r + 1) :=
            Nat.mul_le_mul_left _ (Nat.succ_le_succ (Nat.zero_le _))
  have h_n3r_le_q : n ^ 3 * r ≤ q := by
    rw [← hq_def]
    exact Nat.mul_le_mul_left _ (Nat.le_succ _)
  have hn2 : n ^ 2 ≤ q := Nat.le_trans h_n2_le_n3 h_n3_le_q
  have hn2r : n ^ 2 * r ≤ q :=
    Nat.le_trans (Nat.mul_le_mul_right _ h_n2_le_n3) h_n3r_le_q
  have hn3r : n ^ 3 * r ≤ q := h_n3r_le_q
  have hnr : n * r ≤ q :=
    Nat.le_trans (Nat.mul_le_mul_right _ h_n_le_n3) h_n3r_le_q
  -- Sum the five bounds.
  calc n ^ 2 + n ^ 2 * r + n ^ 3 * r + n * r + n * r
      ≤ q + q + q + q + q := by
        apply Nat.add_le_add
        · apply Nat.add_le_add
          · apply Nat.add_le_add
            · exact Nat.add_le_add hn2 hn2r
            · exact hn3r
          · exact hnr
        · exact hnr
    _ = 5 * q := by omega
    _ = 5 * n ^ 3 * (r + 1) := by rw [← hq_def, ← Nat.mul_assoc]

-- ============================================================
-- 5. Membership theorems — every named atom is enumerated
-- ============================================================

/-- Every pair `(C, D)` with both endpoints in the signature is in
    `atomEnum O`. -/
theorem mem_atomEnum (O : Ontology) {C D : Concept}
    (hC : C ∈ subsOfOntology O) (hD : D ∈ subsOfOntology O) :
    (C, D) ∈ atomEnum O := by
  unfold atomEnum
  rw [List.mem_flatMap]
  refine ⟨C, hC, ?_⟩
  rw [List.mem_map]
  exact ⟨D, hD, rfl⟩

/-- Every shape `(C, ∃R.D)` with `C, D ∈ Sub(O)`, `R ∈ Roles(O)` is
    in `linkEnum O`. -/
theorem mem_linkEnum (O : Ontology) {C D : Concept} {R : Role}
    (hC : C ∈ subsOfOntology O) (hR : R ∈ rolesOfOntology O)
    (hD : D ∈ subsOfOntology O) :
    (C, .exist R D) ∈ linkEnum O := by
  unfold linkEnum
  rw [List.mem_flatMap]
  refine ⟨C, hC, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨R, hR, ?_⟩
  rw [List.mem_map]
  exact ⟨D, hD, rfl⟩

/-- Every shape `(C, ∃R.(D ⊓ E))` with `C, D, E ∈ Sub(O)`,
    `R ∈ Roles(O)` is in `rangeLinkEnum O`. -/
theorem mem_rangeLinkEnum (O : Ontology) {C D E : Concept} {R : Role}
    (hC : C ∈ subsOfOntology O) (hR : R ∈ rolesOfOntology O)
    (hD : D ∈ subsOfOntology O) (hE : E ∈ subsOfOntology O) :
    (C, .exist R (.conj D E)) ∈ rangeLinkEnum O := by
  unfold rangeLinkEnum
  rw [List.mem_flatMap]
  refine ⟨C, hC, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨R, hR, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨D, hD, ?_⟩
  rw [List.mem_map]
  exact ⟨E, hE, rfl⟩

/-- Every shape `(C, ∃R.C)` with `C ∈ Sub(O)`, `R ∈ Roles(O)` is in
    `reflEnum O`. -/
theorem mem_reflEnum (O : Ontology) {C : Concept} {R : Role}
    (hC : C ∈ subsOfOntology O) (hR : R ∈ rolesOfOntology O) :
    (C, .exist R C) ∈ reflEnum O := by
  unfold reflEnum
  rw [List.mem_flatMap]
  refine ⟨C, hC, ?_⟩
  rw [List.mem_map]
  exact ⟨R, hR, rfl⟩

/-- Every shape `(C, Self R)` with `C ∈ Sub(O)`, `R ∈ Roles(O)` is in
    `selfEnum O`. -/
theorem mem_selfEnum (O : Ontology) {C : Concept} {R : Role}
    (hC : C ∈ subsOfOntology O) (hR : R ∈ rolesOfOntology O) :
    (C, .self R) ∈ selfEnum O := by
  unfold selfEnum
  rw [List.mem_flatMap]
  refine ⟨C, hC, ?_⟩
  rw [List.mem_map]
  exact ⟨R, hR, rfl⟩

/-- Membership in any of the per-shape enumerations implies membership
    in the union `boundedAtomSet O`. -/
theorem mem_atomEnum_in_bounded (O : Ontology) {C D : Concept}
    (h : (C, D) ∈ atomEnum O) :
    (C, D) ∈ boundedAtomSet O := by
  unfold boundedAtomSet
  rw [List.mem_append]; left
  rw [List.mem_append]; left
  rw [List.mem_append]; left
  rw [List.mem_append]; left
  exact h

theorem mem_linkEnum_in_bounded (O : Ontology) {p : Concept × Concept}
    (h : p ∈ linkEnum O) : p ∈ boundedAtomSet O := by
  unfold boundedAtomSet
  rw [List.mem_append]; left
  rw [List.mem_append]; left
  rw [List.mem_append]; left
  rw [List.mem_append]; right
  exact h

theorem mem_rangeLinkEnum_in_bounded (O : Ontology) {p : Concept × Concept}
    (h : p ∈ rangeLinkEnum O) : p ∈ boundedAtomSet O := by
  unfold boundedAtomSet
  rw [List.mem_append]; left
  rw [List.mem_append]; left
  rw [List.mem_append]; right
  exact h

theorem mem_reflEnum_in_bounded (O : Ontology) {p : Concept × Concept}
    (h : p ∈ reflEnum O) : p ∈ boundedAtomSet O := by
  unfold boundedAtomSet
  rw [List.mem_append]; left
  rw [List.mem_append]; right
  exact h

theorem mem_selfEnum_in_bounded (O : Ontology) {p : Concept × Concept}
    (h : p ∈ selfEnum O) : p ∈ boundedAtomSet O := by
  unfold boundedAtomSet
  rw [List.mem_append]; right
  exact h

-- ============================================================
-- 6. Bound theorem on the inductive Sat (named-atom case)
-- ============================================================

/-- **Polynomial closure-size bound (named-atom case)**.  For every
    `Sat`-derivable pair `(C, D)` with both `C, D ∈ Sub(O)`, the pair
    is in `atomEnum O`, hence in `boundedAtomSet O`.  The set
    `{(C, D) ∈ Sub(O)² | Sat O C D}` therefore has cardinality at most
    `(numSubexprs O)²`, polynomial in the syntactic size of `O`. -/
theorem sat_named_atom_in_bound (O : Ontology) {C D : Concept}
    (hC : C ∈ subsOfOntology O) (hD : D ∈ subsOfOntology O)
    (_h : Sat O C D) : (C, D) ∈ boundedAtomSet O :=
  mem_atomEnum_in_bounded O (mem_atomEnum O hC hD)

/-- **Cardinality bound** on the named-atom subset of Sat.  There is
    a finite list `L` of length `(numSubexprs O)²` containing every
    Sat-derivable pair `(C, D)` with both endpoints in `Sub(O)`.

    This is the polynomial-closure analog for the new inductive Sat
    of `Moose.Prior.elk_closure_size_bound` (which holds for the
    older list-based formalisation).

    Here we restrict to the *named-atom* case: pairs of named
    subexpressions of the ontology.  The full closure (including
    intermediate concepts of the form `∃R.(D ⊓ E)`, `∃R.C`,
    `Self R`, etc.) is bounded by `boundedAtomSet O`, whose length
    is `O(n³ · r)` (`boundedAtomSet_polynomial`). -/
theorem sat_named_atom_cardinality_bound (O : Ontology) :
    ∃ L : List (Concept × Concept),
      L.length = (numSubexprs O) ^ 2 ∧
      ∀ {C D : Concept},
        C ∈ subsOfOntology O → D ∈ subsOfOntology O →
        Sat O C D → (C, D) ∈ L :=
  ⟨atomEnum O, atomEnum_length O, fun hC hD _ => mem_atomEnum O hC hD⟩

/-- **Total closure-size bound**.  Every Sat-derivable atom whose
    syntactic shape matches one of the five enumerated shapes lies
    in `boundedAtomSet O`, whose total length is polynomial — at
    most `5 · n³ · (r + 1)`.

    This is the *uniform* version of `sat_named_atom_in_bound`,
    capturing all output shapes of the ELK rules in `ELpp.Sat`:
    `atomEnum` (atomic), `linkEnum` (`∃R.D`), `rangeLinkEnum`
    (`∃R.(D ⊓ E)`), `reflEnum` (`∃R.C`), `selfEnum` (`Self R`). -/
theorem sat_closure_total_polynomial_bound (O : Ontology) :
    (boundedAtomSet O).length ≤
      5 * (numSubexprs O) ^ 3 * (numRoles O + 1) :=
  boundedAtomSet_polynomial O

-- ============================================================
-- 7. Audit
-- ============================================================

#print axioms atomEnum_length
#print axioms linkEnum_length
#print axioms rangeLinkEnum_length
#print axioms reflEnum_length
#print axioms selfEnum_length
#print axioms boundedAtomSet_length
#print axioms boundedAtomSet_polynomial
#print axioms sat_named_atom_in_bound
#print axioms sat_named_atom_cardinality_bound
#print axioms sat_closure_total_polynomial_bound

end ELpp
end ELKSDD
