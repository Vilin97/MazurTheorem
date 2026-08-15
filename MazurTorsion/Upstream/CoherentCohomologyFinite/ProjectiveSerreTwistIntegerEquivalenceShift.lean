/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveModuleSerreTwistEquivalence
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistIntegerDescentShift

/-!
# The projective scalar-twist equivalence shifts integer twists

Conjugating the glued scalar twist across the canonical glued-cover
isomorphism sends `𝒪(m)` to `𝒪(m+n)`.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

variable (k : Type) [CommRing k] (d : ℕ)

/-- The pullback definition of `OInt` identifies it with the inverse
projective-to-glued equivalence applied to the glued integer module. -/
noncomputable def integerModuleToInverseGluedIso
    (m : ℤ) :
    OInt k d m ≅
      (projectiveToGluedModules k d).inverse.obj
        (gluedIntegerModule k d m) :=
  ((gluedToProjectiveModulesFunctorIso k d).app
    (gluedIntegerModule k d m)).symm

/-- Sending `OInt m` to the glued standard cover recovers the glued
degree-`m` integer module. -/
noncomputable def projectiveToGluedIntegerModuleIso
    (m : ℤ) :
    (projectiveToGluedModules k d).functor.obj
        (OInt k d m) ≅
      gluedIntegerModule k d m :=
  (projectiveToGluedModules k d).functor.mapIso
      (integerModuleToInverseGluedIso k d m) ≪≫
    (projectiveToGluedModules k d).counitIso.app
      (gluedIntegerModule k d m)

/-- The glued scalar-twist functor carries the comparison from projective
`OInt m` to the corresponding glued integer module. -/
noncomputable def gluedScalarTwistMapProjectiveIntegerIso
    (m n : ℤ) :
    (gluedIntegerScalarTwistEquivalence k d n).functor.obj
        ((projectiveToGluedModules k d).functor.obj
          (OInt k d m)) ≅
      (gluedIntegerScalarTwistEquivalence k d n).functor.obj
        (gluedIntegerModule k d m) :=
  (gluedIntegerScalarTwistEquivalence k d n).functor.mapIso
    (projectiveToGluedIntegerModuleIso k d m)

/-- On the glued model, the image of projective `OInt m` under the scalar
twist is the degree-`m+n` glued integer module. -/
noncomputable def gluedScalarTwistProjectiveIntegerShiftIso
    (m n : ℤ) :
    (gluedIntegerScalarTwistEquivalence k d n).functor.obj
        ((projectiveToGluedModules k d).functor.obj
          (OInt k d m)) ≅
      gluedIntegerModule k d (m + n) :=
  gluedScalarTwistMapProjectiveIntegerIso k d m n ≪≫
    gluedIntegerScalarTwistShiftIso k d m n

/-- Transport the glued degree-shift comparison back to projective space. -/
noncomputable def inverseGluedMapIntegerShiftIso
    (m n : ℤ) :
    (projectiveToGluedModules k d).inverse.obj
        ((gluedIntegerScalarTwistEquivalence k d n).functor.obj
          ((projectiveToGluedModules k d).functor.obj
            (OInt k d m))) ≅
      (projectiveToGluedModules k d).inverse.obj
        (gluedIntegerModule k d (m + n)) :=
  (projectiveToGluedModules k d).inverse.mapIso
    (gluedScalarTwistProjectiveIntegerShiftIso
      k d m n)

/-- The projective scalar-twist autoequivalence of degree `n` sends
`OInt m` to `OInt (m+n)`. -/
noncomputable def projectiveIntegerScalarTwistShiftIso
    (m n : ℤ) :
    (projectiveIntegerScalarTwistEquivalence
        k d n).functor.obj (OInt k d m) ≅
      OInt k d (m + n) :=
  inverseGluedMapIntegerShiftIso k d m n ≪≫
    (gluedToProjectiveModulesFunctorIso k d).app
      (gluedIntegerModule k d (m + n))

/-- Existence form of the integer degree-shift comparison. -/
theorem nonempty_projectiveIntegerScalarTwistShiftIso
    (m n : ℤ) :
    Nonempty
      ((projectiveIntegerScalarTwistEquivalence
          k d n).functor.obj (OInt k d m) ≅
        OInt k d (m + n)) :=
  ⟨projectiveIntegerScalarTwistShiftIso k d m n⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
