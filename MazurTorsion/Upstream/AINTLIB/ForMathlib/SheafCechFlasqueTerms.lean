/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SheafCohomologyCompat
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SheafCohomologyFiniteProducts

/-!
# Flasque terms in the sheaf-level Cech resolution

Restriction to an open and pushforward along its inclusion both preserve flasqueness.
Consequently every factor of a Cech term of a flasque sheaf is flasque. For a finite
cover, finite-product compatibility of genuine sheaf cohomology then makes the whole
Cech term acyclic in positive degrees.
-/

open CategoryTheory TopologicalSpace

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}
variable (F : Sheaf AddCommGrpCat.{u} X) {ι : Type u} (U : ι → Opens X)

/-- Every positive cohomology group of a finite Cech term of a flasque sheaf vanishes. -/
theorem cechTerm_subsingleton_H_of_isFlasque [Finite ι] [IsFlasque F]
    (n q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H (cechTerm F U n) (q + 1)) := by
  apply cechTerm_subsingleton_H_of_factors F U n (q + 1)
  intro i
  let V := ∏ᶜ fun k : Fin (n + 1) => U (i k)
  letI : IsFlasque ((restrict AddCommGrpCat V.isOpenEmbedding).obj F) :=
    IsFlasque.of_restrict AddCommGrpCat F V.isOpenEmbedding
  letI : IsFlasque ((pushforward AddCommGrpCat V.inclusion').obj
      ((restrict AddCommGrpCat V.isOpenEmbedding).obj F)) :=
    IsFlasque.pushforward_isFlasque _ V.inclusion'
  change Subsingleton (CategoryTheory.Sheaf.H
    ((pushforward AddCommGrpCat V.inclusion').obj
      ((restrict AddCommGrpCat V.isOpenEmbedding).obj F)) (q + 1))
  exact IsFlasque.subsingleton_H q

end TopCat.Sheaf
