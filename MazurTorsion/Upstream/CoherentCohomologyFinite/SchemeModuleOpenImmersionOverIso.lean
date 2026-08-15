/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafAffineQuasicoherent
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafOverFiniteness

/-!
# Slice-site comparison along an open immersion

An isomorphism after pullback along an open immersion induces an
isomorphism between ordinary slice-site restrictions over its open
range.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{0}} (f : X ⟶ Y)
  [IsOpenImmersion f]

/--
Restricting to the range of an open immersion and then pulling back along
the canonical range isomorphism recovers pullback along the original
open immersion.
-/
noncomputable def rangeRestrictionPullbackIso
    (M : Y.Modules) :
    (pullback f.isoOpensRange.hom).obj
        (M.restrict f.opensRange.ι) ≅
      (pullback f).obj M :=
  (pullback f.isoOpensRange.hom).mapIso
      ((restrictFunctorIsoPullback
        f.opensRange.ι).app M) ≪≫
    (pullbackComp
      f.isoOpensRange.hom
      f.opensRange.ι).app M ≪≫
    (pullbackCongr
      f.isoOpensRange_hom_ι).app M

/--
An isomorphism after pullback along an open immersion descends to an
isomorphism between restrictions to its open range.
-/
noncomputable def rangeRestrictionIsoOfPullbackIso
    {M N : Y.Modules}
    (e : (pullback f).obj M ≅
      (pullback f).obj N) :
    M.restrict f.opensRange.ι ≅
      N.restrict f.opensRange.ι := by
  let F := pullback f.isoOpensRange.hom
  letI :
      (restrictFunctor
        f.isoOpensRange.hom).IsEquivalence :=
    inferInstance
  letI : F.IsEquivalence :=
    Functor.isEquivalence_of_iso
      (restrictFunctorIsoPullback
        f.isoOpensRange.hom)
  exact
    F.preimageIso
      (rangeRestrictionPullbackIso f M ≪≫
        e ≪≫
        (rangeRestrictionPullbackIso f N).symm)

/--
Slice-site form of `rangeRestrictionIsoOfPullbackIso`.
-/
noncomputable def overRangeIsoOfPullbackIso
    {M N : Y.Modules}
    (e : (pullback f).obj M ≅
      (pullback f).obj N) :
    M.over f.opensRange ≅
      N.over f.opensRange :=
  (restrictOverIso f.opensRange M).symm ≪≫
    (overEquivalence f.opensRange).functor.mapIso
      (rangeRestrictionIsoOfPullbackIso f e) ≪≫
    restrictOverIso f.opensRange N

end AlgebraicGeometry.Scheme.Modules
