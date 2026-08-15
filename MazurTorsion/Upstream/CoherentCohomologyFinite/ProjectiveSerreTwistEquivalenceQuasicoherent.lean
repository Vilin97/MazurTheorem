/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineQuasicoherentPresentation
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistEquivalenceCharts
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeModulePullbackQuasicoherent
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafOverEquivalence

/-!
# Quasicoherence under the projective scalar-twist equivalence

On every standard affine chart the scalar-twist functor is isomorphic to
the identity.  An affine presentation of the original chart restriction
therefore gives a presentation of the twisted restriction.  Binding these
presentations over the standard cover proves quasicoherence.
-/


open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open AlgebraicGeometry.Scheme.Modules

variable (k : Type) [CommRing k] (d : ℕ)

/-- A global affine presentation for the restriction of the scalar-twisted
module to one standard projective chart. -/
noncomputable def projectiveIntegerScalarTwistChartPresentation
    (E : (scheme k d).Modules) [E.IsQuasicoherent]
    (n : ℤ) (i : Fin (d + 1)) :
    ((pullback ((standardChart k i).ι)).obj
      ((projectiveIntegerScalarTwistEquivalence
        k d n).functor.obj E)).Presentation := by
  letI :
      ((pullback ((standardChart k i).ι)).obj E).IsQuasicoherent :=
    isQuasicoherent_pullback (standardChart k i).ι E
  letI : IsAffine (standardChart k i) :=
    isAffineOpen_standardChart k i
  let P :
      ((pullback ((standardChart k i).ι)).obj E).Presentation :=
    quasicoherentPresentation
      ((pullback ((standardChart k i).ι)).obj E)
  let e := projectiveIntegerScalarTwistChartIso k d E n i
  exact @SheafOfModules.Presentation.ofIsIso
    _ _ _ _ _ _ _ _ e.inv e.isIso_inv P

/-- A presentation on the slice site over one standard chart. -/
noncomputable def projectiveIntegerScalarTwistOverChartPresentation
    (E : (scheme k d).Modules) [E.IsQuasicoherent]
    (n : ℤ) (i : Fin (d + 1)) :
    (((projectiveIntegerScalarTwistEquivalence
      k d n).functor.obj E).over
        (standardChart k i)).Presentation := by
  let T :=
    (projectiveIntegerScalarTwistEquivalence
      k d n).functor.obj E
  let P :
      ((pullback ((standardChart k i).ι)).obj T).Presentation :=
    projectiveIntegerScalarTwistChartPresentation
      k d E n i
  let Pover :
      ((Scheme.Modules.overEquivalence
        (standardChart k i)).functor.obj
          ((pullback
            ((standardChart k i).ι)).obj T)).Presentation :=
    P.map
      (Scheme.Modules.overEquivalence
        (standardChart k i)).functor
      (Scheme.Modules.unitOverIso
        (standardChart k i)).symm
  let e :
      T.over (standardChart k i) ≅
        (Scheme.Modules.overEquivalence
          (standardChart k i)).functor.obj
            ((pullback
              ((standardChart k i).ι)).obj T) :=
    (Scheme.Modules.restrictOverIso
      (standardChart k i) T).symm ≪≫
      (Scheme.Modules.overEquivalence
        (standardChart k i)).functor.mapIso
          ((Scheme.Modules.restrictFunctorIsoPullback
            (standardChart k i).ι).app T)
  exact @SheafOfModules.Presentation.ofIsIso
    _ _ _ _ _ _ _ _ e.inv e.isIso_inv Pover

/-- Quasicoherent data for a scalar-twisted module, assembled from its
standard-chart presentations. -/
noncomputable def projectiveIntegerScalarTwistQuasicoherentData
    (E : (scheme k d).Modules) [E.IsQuasicoherent]
    (n : ℤ) :
    ((projectiveIntegerScalarTwistEquivalence
      k d n).functor.obj E).QuasicoherentData where
  I := Fin (d + 1)
  X := standardChart k
  coversTop :=
    TopologicalSpace.Opens.coversTop_of_iSup_eq_top
      (standardChart k) (iSup_standardChart k d)
  presentation i :=
    projectiveIntegerScalarTwistOverChartPresentation
      k d E n i

/-- The projective integer scalar-twist functor preserves
quasicoherence. -/
theorem projectiveIntegerScalarTwist_isQuasicoherent
    (E : (scheme k d).Modules) (n : ℤ)
    (hE : E.IsQuasicoherent) :
    ((projectiveIntegerScalarTwistEquivalence
      k d n).functor.obj E).IsQuasicoherent := by
  letI : E.IsQuasicoherent := hE
  exact
    (projectiveIntegerScalarTwistQuasicoherentData
      k d E n).isQuasicoherent

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
