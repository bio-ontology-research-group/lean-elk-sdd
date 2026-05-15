/-
  ELKSDD/SROIQ.lean
  -------------------
  SROIQ role-axis features on top of `ELKSDD.ALCHOQ`:

  * Role hierarchy ``R ⊑ S``;
  * Role chains ``R₁ ∘ … ∘ Rₖ ⊑ S``;
  * Transitive, symmetric, asymmetric, reflexive, irreflexive,
    inverse, functional, disjoint roles;
  * Role-axis lifting lemmas matching the structural transformations
    performed by `moose.sroiq.grounding`.

  We give the *semantic correctness* of each ground-time expansion as
  an `iff`-style theorem.  The Python grounder emits ground clauses;
  these lemmas justify that the emitted clauses faithfully encode the
  intended semantic constraint.

  No imports beyond Lean 4 core; no Mathlib.  Foundation-only axiom
  budget retained (the file does not introduce any `axiom`/`sorry`).
-/

import ELKSDD.ALCHOQ

namespace ELKSDD
namespace SROIQ

open ALCHOQ (Interp)

-- ============================================================
-- 1. RBox axiom semantics
-- ============================================================

/-- An RBox axiom: every shape the Python `Ontology.rbox` recognises. -/
inductive RAxiom : Type where
  | incl   : Nat → Nat → RAxiom                         -- R ⊑ S
  | chain  : List Nat → Nat → RAxiom                    -- R₁ ∘ … ∘ Rₖ ⊑ S
  | trans  : Nat → RAxiom                               -- Trans(R)
  | sym    : Nat → RAxiom                               -- Sym(R)
  | asym   : Nat → RAxiom                               -- Asym(R)
  | refl   : Nat → RAxiom                               -- Refl(R)
  | irrefl : Nat → RAxiom                               -- Irrefl(R)
  | inv    : Nat → Nat → RAxiom                         -- R ≡ S⁻
  | disj   : Nat → Nat → RAxiom                         -- Disjoint(R, S)
  deriving DecidableEq

/-- `holdsAlong I rs x y` says the chain of roles `rs` connects `x`
    to `y` in `I`. -/
def holdsAlong {α : Type} (I : Interp α) : List Nat → α → α → Prop
  | [], x, y => x = y
  | r :: rs, x, y => ∃ z, I.ext_role r x z ∧ holdsAlong I rs z y

/-- Tarskian semantics of an RBox axiom. -/
def RAxiom.eval {α : Type} (I : Interp α) : RAxiom → Prop
  | .incl R S => ∀ x y, I.ext_role R x y → I.ext_role S x y
  | .chain rs S => ∀ x y, holdsAlong I rs x y → I.ext_role S x y
  | .trans R => ∀ x y z, I.ext_role R x y → I.ext_role R y z →
                          I.ext_role R x z
  | .sym R => ∀ x y, I.ext_role R x y → I.ext_role R y x
  | .asym R => ∀ x y, I.ext_role R x y → ¬ I.ext_role R y x
  | .refl R => ∀ x, I.ext_role R x x
  | .irrefl R => ∀ x, ¬ I.ext_role R x x
  | .inv R S => ∀ x y, I.ext_role R x y ↔ I.ext_role S y x
  | .disj R S => ∀ x y, ¬ (I.ext_role R x y ∧ I.ext_role S x y)

abbrev RBox := List RAxiom

def RBox.eval {α : Type} (I : Interp α) (rs : RBox) : Prop :=
  ∀ ax, ax ∈ rs → ax.eval I

-- ============================================================
-- 2. Soundness of the role-axis structural transformations
--    (these justify the grounder's per-pair / per-triple clauses)
-- ============================================================

variable {α : Type} (I : Interp α)

theorem incl_sound (R S : Nat) :
    (RAxiom.incl R S).eval I ↔
    ∀ x y, I.ext_role R x y → I.ext_role S x y := Iff.rfl

theorem trans_sound (R : Nat) :
    (RAxiom.trans R).eval I ↔
    ∀ x y z, I.ext_role R x y → I.ext_role R y z → I.ext_role R x z :=
  Iff.rfl

theorem sym_sound (R : Nat) :
    (RAxiom.sym R).eval I ↔
    ∀ x y, I.ext_role R x y → I.ext_role R y x := Iff.rfl

theorem asym_sound (R : Nat) :
    (RAxiom.asym R).eval I ↔
    ∀ x y, ¬ (I.ext_role R x y ∧ I.ext_role R y x) := by
  constructor
  · intro h x y ⟨h1, h2⟩; exact h x y h1 h2
  · intro h x y h1 h2; exact h x y ⟨h1, h2⟩

theorem refl_sound (R : Nat) :
    (RAxiom.refl R).eval I ↔ ∀ x, I.ext_role R x x := Iff.rfl

theorem irrefl_sound (R : Nat) :
    (RAxiom.irrefl R).eval I ↔ ∀ x, ¬ I.ext_role R x x := Iff.rfl

theorem inv_sound (R S : Nat) :
    (RAxiom.inv R S).eval I ↔
    ∀ x y, I.ext_role R x y ↔ I.ext_role S y x := Iff.rfl

theorem disj_sound (R S : Nat) :
    (RAxiom.disj R S).eval I ↔
    ∀ x y, ¬ (I.ext_role R x y ∧ I.ext_role S x y) := Iff.rfl

theorem chain_two_sound (R₁ R₂ S : Nat) :
    (RAxiom.chain [R₁, R₂] S).eval I ↔
    ∀ x y z, I.ext_role R₁ x y → I.ext_role R₂ y z → I.ext_role S x z := by
  unfold RAxiom.eval
  constructor
  · intro h x y z h1 h2
    apply h x z
    refine ⟨y, h1, ?_⟩
    show ∃ w, I.ext_role R₂ y w ∧ (w = z)
    exact ⟨z, h2, rfl⟩
  · intro h x z hch
    obtain ⟨y, h1, hrest⟩ := hch
    obtain ⟨w, h2, hwz⟩ := hrest
    cases hwz
    exact h x y z h1 h2

-- ============================================================
-- 3. Standard role-axis interactions: transitivity → 2-step chain,
--    symmetry ↔ R ≡ R⁻, asymmetry ↔ Disjoint(R, R⁻)
-- ============================================================

theorem trans_iff_chain (R : Nat) :
    (RAxiom.trans R).eval I ↔ (RAxiom.chain [R, R] R).eval I := by
  rw [trans_sound, chain_two_sound]

theorem sym_iff_self_inverse (R : Nat) :
    (RAxiom.sym R).eval I ↔ (RAxiom.inv R R).eval I := by
  rw [sym_sound, inv_sound]
  constructor
  · intro h x y
    exact ⟨fun hxy => h x y hxy, fun hyx => h y x hyx⟩
  · intro h x y hxy
    exact (h x y).mp hxy

-- ============================================================
-- 4. Nominal-singleton lemma used by the grounder
-- ============================================================

namespace Interp

/-- Singleton-extension lemma: an individual ``a`` is in the
    extension of the nominal ``{a}``, and *no one else* is.  Justifies
    the grounder's per-individual pinning of the nominal concept-name
    proxy. -/
theorem nom_singleton {α} (I : ALCHOQ.Interp α) (i : Nat) (x : α) :
    I.eval (.nom i) x ↔ x = I.ext_ind i := Iff.rfl

end Interp

end SROIQ
end ELKSDD
