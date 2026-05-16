/-
  ELKSDD/MathlibSmoke.lean
  ------------------------
  Sanity check that Mathlib is available to the ELKSDD library.
  Nothing here is depended on by the main development.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Card
import Mathlib.Logic.Basic

namespace ELKSDD
namespace Smoke

example : (3 + 4 : Nat) = 7 := by decide

example (s : Finset Nat) : s.card = s.card := rfl

end Smoke
end ELKSDD
