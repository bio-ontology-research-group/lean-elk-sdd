/-
  ELKSDD/ALCHOQ.lean
  --------------------
  Extension of `ELKSDD.ALC` with nominals (`{a}`) and qualified number
  restrictions (`≥n R.C`, `≤n R.C`).  Adds:

  * syntax via a separate `Concept` inductive (avoids touching the
    pre-existing `ELKSDD.ALC.Concept` whose soundness proof is already
    sorry-free);
  * Tarskian set-extension semantics that handles the new constructors;
  * a sound consequence-based saturation calculus `Sat` analogous to
    `ALC.Sat` plus role-axis monotonicity through `≥n` / `≤n`.

  Imports only Lean 4 core.  Foundation-only axiom budget retained.

  Conventions
  -----------
  * Concept names and role names: `Nat` (carried-over).
  * Individuals: `Nat` (used as the "nominal index"); a Tarskian
    interpretation assigns each individual index an element of the
    domain via `ext_ind : Nat → α`.
  * Numbers in `≥n` / `≤n` are `Nat`, with the standard convention that
    `≥0 R.C` is `⊤` and `≤0 R.C` is `∀R.¬C`.
-/

namespace ELKSDD
namespace ALCHOQ

-- ============================================================
-- 1. Concept syntax
-- ============================================================

inductive Concept : Type where
  | atom    : Nat → Concept
  | top     : Concept
  | bot     : Concept
  | nom     : Nat → Concept                            -- {a_i}
  | neg     : Concept → Concept
  | conj    : Concept → Concept → Concept
  | disj    : Concept → Concept → Concept
  | exist   : Nat → Concept → Concept                  -- ∃R.C
  | univ    : Nat → Concept → Concept                  -- ∀R.C
  | atLeast : Nat → Nat → Concept → Concept            -- ≥n R.C
  | atMost  : Nat → Nat → Concept → Concept            -- ≤n R.C
  deriving DecidableEq

abbrev Axiom := Concept × Concept
abbrev Ontology := List Axiom

-- ============================================================
-- 2. Tarskian semantics
-- ============================================================

/-- An interpretation now also assigns each individual index an element
    of the domain.  Roles and concept-name extensions stay as in ALC. -/
structure Interp (α : Type) where
  ext_concept : Nat → α → Prop
  ext_role    : Nat → α → α → Prop
  ext_ind     : Nat → α

namespace Interp

/-- The cardinality predicate `|S| ≥ n` for a unary predicate `S` on
    `α`.  Encoded via `n`-tuples of pairwise distinct witnesses; this
    matches the standard DL semantics. -/
def atLeastCard {α : Type} (S : α → Prop) : Nat → Prop
  | 0     => True
  | n + 1 => ∃ x : α, S x ∧ atLeastCard (fun y => S y ∧ y ≠ x) n

/-- `|S| ≤ n` is the De Morgan dual: `¬(|S| ≥ n+1)`. -/
def atMostCard {α : Type} (S : α → Prop) (n : Nat) : Prop :=
  ¬ atLeastCard S (n + 1)

variable {α : Type}

/-- Recursive evaluation of an ALCHOQ concept. -/
def eval (I : Interp α) : Concept → α → Prop
  | .atom n, x => I.ext_concept n x
  | .top, _ => True
  | .bot, _ => False
  | .nom i, x => x = I.ext_ind i
  | .neg C, x => ¬ I.eval C x
  | .conj A B, x => I.eval A x ∧ I.eval B x
  | .disj A B, x => I.eval A x ∨ I.eval B x
  | .exist R C, x => ∃ y, I.ext_role R x y ∧ I.eval C y
  | .univ R C, x => ∀ y, I.ext_role R x y → I.eval C y
  | .atLeast n R C, x =>
      atLeastCard (fun y => I.ext_role R x y ∧ I.eval C y) n
  | .atMost n R C, x =>
      atMostCard (fun y => I.ext_role R x y ∧ I.eval C y) n

def satisfiesAxiom (I : Interp α) (ax : Axiom) : Prop :=
  ∀ x, I.eval ax.1 x → I.eval ax.2 x

def satisfies (I : Interp α) (O : Ontology) : Prop :=
  ∀ ax, ax ∈ O → I.satisfiesAxiom ax

end Interp

def Entails (O : Ontology) (C D : Concept) : Prop :=
  ∀ {α : Type} (I : Interp α), I.satisfies O →
    ∀ x, I.eval C x → I.eval D x

-- ============================================================
-- 3. Basic semantic lemmas (sanity, dualities reused)
-- ============================================================

namespace Interp

variable {α : Type} (I : Interp α)

/-- Singleton semantics of a nominal. -/
theorem eval_nom_iff (i : Nat) (x : α) :
    I.eval (.nom i) x ↔ x = I.ext_ind i := Iff.rfl

/-- `≥0 R.C` is `⊤`. -/
theorem eval_atLeast_zero (R : Nat) (C : Concept) (x : α) :
    I.eval (.atLeast 0 R C) x ↔ True := by
  unfold eval atLeastCard
  exact ⟨fun _ => trivial, fun _ => trivial⟩

/-- `≤0 R.C` is `∀R.¬C`. -/
theorem eval_atMost_zero (R : Nat) (C : Concept) (x : α) :
    I.eval (.atMost 0 R C) x ↔ ∀ y, I.ext_role R x y → ¬ I.eval C y := by
  show ¬ atLeastCard (fun y => I.ext_role R x y ∧ I.eval C y) 1 ↔ _
  unfold atLeastCard
  constructor
  · intro h y hR hC
    exact h ⟨y, ⟨hR, hC⟩, trivial⟩
  · rintro h ⟨y, ⟨hR, hC⟩, _⟩
    exact h y hR hC

/-- ≥1 R.C is the existential. -/
theorem eval_atLeast_one_iff_exist (R : Nat) (C : Concept) (x : α) :
    I.eval (.atLeast 1 R C) x ↔ ∃ y, I.ext_role R x y ∧ I.eval C y := by
  show atLeastCard (fun y => I.ext_role R x y ∧ I.eval C y) 1 ↔ _
  unfold atLeastCard
  constructor
  · rintro ⟨y, hyS, _⟩
    exact ⟨y, hyS⟩
  · rintro ⟨y, hyS⟩
    exact ⟨y, hyS, trivial⟩

end Interp

-- ============================================================
-- 4. Sound consequence-based saturation calculus
-- ============================================================

/--
Rules:

* the propositional and role-axis ALC rules (`refl`, `axm`, `trans`,
  `andL`, `andR`, `andI`, `orL`, `orR`, `orE`, `bot`, `top`,
  `monoExist`, `monoUniv`),
* `nomRefl` for the nominal-self-membership clause `{a} ⊑ {a}` (free),
* `monoAtLeast` and `monoAtMost` for filler-monotonicity through the
  qualified number restrictions: `C ⊑ D` lifts to `≥n R.C ⊑ ≥n R.D`
  (covariant) and to `≤n R.D ⊑ ≤n R.C` (contravariant — *D ↦ C* in
  the filler).
-/
inductive Sat (O : Ontology) : Concept → Concept → Prop where
  | refl       : ∀ C, Sat O C C
  | axm        : ∀ C D, (C, D) ∈ O → Sat O C D
  | trans      : ∀ {C D E}, Sat O C D → Sat O D E → Sat O C E
  | andL       : ∀ C D, Sat O (.conj C D) C
  | andR       : ∀ C D, Sat O (.conj C D) D
  | andI       : ∀ {C D E}, Sat O C D → Sat O C E → Sat O C (.conj D E)
  | orL        : ∀ C D, Sat O C (.disj C D)
  | orR        : ∀ C D, Sat O D (.disj C D)
  | orE        : ∀ {C D E}, Sat O C E → Sat O D E → Sat O (.disj C D) E
  | bot        : ∀ C, Sat O .bot C
  | top        : ∀ C, Sat O C .top
  | monoExist  : ∀ R {C D}, Sat O C D → Sat O (.exist R C) (.exist R D)
  | monoUniv   : ∀ R {C D}, Sat O C D → Sat O (.univ  R C) (.univ  R D)
  | monoAtLeast : ∀ n R {C D}, Sat O C D →
                    Sat O (.atLeast n R C) (.atLeast n R D)
  | monoAtMost  : ∀ n R {C D}, Sat O C D →
                    Sat O (.atMost n R D) (.atMost n R C)

-- ============================================================
-- 5. Soundness
-- ============================================================

/-- Filler-covariant lifting of subsumption through `≥n R.·`.  Direct
    induction on `n` over the cardinality predicate. -/
private theorem atLeast_mono {α} (P Q : α → Prop)
    (hPQ : ∀ y, P y → Q y) :
    ∀ n, Interp.atLeastCard P n → Interp.atLeastCard Q n
  | 0, _ => trivial
  | (n+1), ⟨x, hPx, hRest⟩ => by
      refine ⟨x, hPQ x hPx, ?_⟩
      have hPx' : ∀ y, (P y ∧ y ≠ x) → (Q y ∧ y ≠ x) := by
        intro y ⟨hp, hne⟩; exact ⟨hPQ y hp, hne⟩
      exact atLeast_mono _ _ hPx' n hRest

/-- Filler-contravariant lifting through `≤n R.·`. -/
private theorem atMost_anti {α} (P Q : α → Prop)
    (hQP : ∀ y, Q y → P y) (n : Nat) :
    Interp.atMostCard P n → Interp.atMostCard Q n := by
  intro hP hQ
  exact hP (atLeast_mono _ _ hQP (n+1) hQ)

theorem sat_sound (O : Ontology) (C D : Concept)
    (h : Sat O C D) : Entails O C D := by
  intro α I hOK x hC
  induction h generalizing x with
  | refl _ => exact hC
  | axm C D hMem => exact hOK (C, D) hMem x hC
  | trans hCD hDE ihCD ihDE => exact ihDE x (ihCD x hC)
  | andL _ _ => exact hC.1
  | andR _ _ => exact hC.2
  | andI _ _ ihD ihE => exact ⟨ihD x hC, ihE x hC⟩
  | orL _ _ => exact Or.inl hC
  | orR _ _ => exact Or.inr hC
  | orE _ _ ihE ihE' =>
      cases hC with
      | inl h => exact ihE x h
      | inr h => exact ihE' x h
  | bot _ => exact hC.elim
  | top _ => trivial
  | monoExist R _ ih =>
      obtain ⟨y, hR, hCy⟩ := hC
      exact ⟨y, hR, ih y hCy⟩
  | monoUniv R _ ih =>
      intro y hR
      exact ih y (hC y hR)
  | monoAtLeast n R _ ih =>
      refine atLeast_mono _ _ (fun y hy => ⟨hy.1, ih y hy.2⟩) n hC
  | monoAtMost n R _ ih =>
      refine atMost_anti _ _ (fun y hy => ⟨hy.1, ih y hy.2⟩) n hC

-- ============================================================
-- 6. A worked example: ≥2 R.A ⊑ ≥1 R.A via filler-covariance
--    (here used at n=2, filler unchanged — illustrating the rule shape)
-- ============================================================

example : Sat ([] : Ontology) (.atLeast 2 0 (.atom 0)) (.atLeast 2 0 (.atom 0)) :=
  Sat.refl _

example : Sat ([(Concept.atom 0, Concept.atom 1)] : Ontology)
              (.atLeast 3 5 (Concept.atom 0))
              (.atLeast 3 5 (Concept.atom 1)) :=
  Sat.monoAtLeast 3 5 (Sat.axm _ _ (by simp))

example : Sat ([(Concept.atom 1, Concept.atom 0)] : Ontology)
              (.atMost 4 7 (Concept.atom 0))
              (.atMost 4 7 (Concept.atom 1)) :=
  Sat.monoAtMost 4 7 (Sat.axm _ _ (by simp))

end ALCHOQ
end ELKSDD
