/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverScalarTwistChartRestriction
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistBaseChangeCoverUnits

/-!
# Relative projective scalar-twist equivalences

The integer Serre cocycle on the standard cover of projective space pulls
back along every morphism `f : T ⟶ ℙ^d_k`.  Transporting scalar-twisted
effective descent across the pulled-back open cover gives an
autoequivalence of module sheaves on `T`.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.CoverDescentData

variable (k : Type) [CommRing k] (d : ℕ)
  {T : Scheme.{0}} (f : T ⟶ scheme k d)

/--
Scalar twisting by the pullback of the integer Serre cocycle along
`f : T ⟶ ℙ^d_k`.
-/
noncomputable def relativeProjectiveSerreTwistEquivalence
    (m : ℤ) :
    T.Modules ≌ T.Modules :=
  openCoverScalarTwistEquivalence
    ((cover k d).pullback₁ f)
    (baseChangedIntegerCoverUnit k d f m)
    (baseChangedIntegerCoverUnit_self k d f m)
    (baseChangedIntegerCoverUnit_cocycle k d f m)

/-- Expansion of the relative twist through the pulled-back glued cover. -/
@[simp]
theorem relativeProjectiveSerreTwistEquivalence_functor
    (m : ℤ) :
    (relativeProjectiveSerreTwistEquivalence k d f m).functor =
      (modulesToGluedEquivalence
          ((cover k d).pullback₁ f)).functor ⋙
        (scalarTwistGluedEquivalence
          (baseChangedIntegerCoverUnit k d f m)
          (baseChangedIntegerCoverUnit_self k d f m)
          (baseChangedIntegerCoverUnit_cocycle k d f m)).functor ⋙
        (modulesToGluedEquivalence
          ((cover k d).pullback₁ f)).inverse :=
  rfl

/--
Object-level expansion into restriction, scalar twisting of the descent
transitions, and gluing.
-/
@[simp]
theorem relativeProjectiveSerreTwistEquivalence_functor_obj
    (m : ℤ) (M : T.Modules) :
    (relativeProjectiveSerreTwistEquivalence
        k d f m).functor.obj M =
      (modulesToGluedEquivalence
          ((cover k d).pullback₁ f)).inverse.obj
        ((glueFunctor
          (D := Scheme.Cover.gluedCover
            ((cover k d).pullback₁ f))).obj
          ((scalarTwistFunctor
            (baseChangedIntegerCoverUnit k d f m)
            (baseChangedIntegerCoverUnit_self k d f m)
            (baseChangedIntegerCoverUnit_cocycle k d f m)).obj
              ((restrictionFunctor
                (D := Scheme.Cover.gluedCover
                  ((cover k d).pullback₁ f))).obj
                ((modulesToGluedEquivalence
                  ((cover k d).pullback₁ f)).functor.obj M)))) :=
  rfl

/--
The first leg of the relative scalar twist may be written geometrically
as pullback along the canonical map from the glued pulled-back cover.
-/
noncomputable def relativeProjectiveSerreTwistFunctorIso
    (m : ℤ) :
    (relativeProjectiveSerreTwistEquivalence
        k d f m).functor ≅
      (Scheme.Modules.pullback
          (Scheme.Cover.fromGlued
            ((cover k d).pullback₁ f)) ⋙
        (scalarTwistGluedEquivalence
          (baseChangedIntegerCoverUnit k d f m)
          (baseChangedIntegerCoverUnit_self k d f m)
          (baseChangedIntegerCoverUnit_cocycle k d f m)).functor) ⋙
        (modulesToGluedEquivalence
          ((cover k d).pullback₁ f)).inverse :=
  openCoverScalarTwistFunctorIso
    ((cover k d).pullback₁ f)
    (baseChangedIntegerCoverUnit k d f m)
    (baseChangedIntegerCoverUnit_self k d f m)
    (baseChangedIntegerCoverUnit_cocycle k d f m)

/-- Objectwise form of `relativeProjectiveSerreTwistFunctorIso`. -/
noncomputable def relativeProjectiveSerreTwistObjectIso
    (m : ℤ) (M : T.Modules) :
    (relativeProjectiveSerreTwistEquivalence
        k d f m).functor.obj M ≅
      (modulesToGluedEquivalence
        ((cover k d).pullback₁ f)).inverse.obj
        ((scalarTwistGluedEquivalence
          (baseChangedIntegerCoverUnit k d f m)
          (baseChangedIntegerCoverUnit_self k d f m)
          (baseChangedIntegerCoverUnit_cocycle k d f m)).functor.obj
            ((Scheme.Modules.pullback
              (Scheme.Cover.fromGlued
                ((cover k d).pullback₁ f))).obj M)) :=
  openCoverScalarTwistObjectIso
    ((cover k d).pullback₁ f)
    (baseChangedIntegerCoverUnit k d f m)
    (baseChangedIntegerCoverUnit_self k d f m)
    (baseChangedIntegerCoverUnit_cocycle k d f m)
    M

/--
The relative scalar twist is unchanged after restriction to each chart
of the pulled-back standard projective cover.
-/
noncomputable def relativeProjectiveSerreTwistChartRestrictionIso
    (m : ℤ) (M : T.Modules) (i : Fin (d + 1)) :
    (Scheme.Modules.pullback
      (((cover k d).pullback₁ f).f i)).obj
        ((relativeProjectiveSerreTwistEquivalence
          k d f m).functor.obj M) ≅
      (Scheme.Modules.pullback
        (((cover k d).pullback₁ f).f i)).obj M :=
  openCoverScalarTwistChartRestrictionIso
    ((cover k d).pullback₁ f)
    (baseChangedIntegerCoverUnit k d f m)
    (baseChangedIntegerCoverUnit_self k d f m)
    (baseChangedIntegerCoverUnit_cocycle k d f m)
    M i

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
