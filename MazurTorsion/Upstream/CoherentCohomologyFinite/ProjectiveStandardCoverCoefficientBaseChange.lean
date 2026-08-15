/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistTransition
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSpaceCoefficientBaseChange

/-!
# Coefficient base change for the standard projective cover

The inverse image of a standard projective chart under coefficient
extension is the corresponding standard chart over the larger coefficient
ring.  Consequently, after pulling back along a morphism to projective
space, the standard covers over the two coefficient rings are canonically
isomorphic component by component.
-/


open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R]
variable (d : ℕ) {Y : Scheme} (g : Y ⟶ scheme R d)

local instance coefficientBaseChangeStandardCoverComponentIsOpenImmersion
    {A : Type} [CommRing A] (i : Fin (d + 1)) :
    IsOpenImmersion ((cover A d).f i) :=
  (cover A d).map_prop i

local instance pulledBackStandardCoverComponentIsOpenImmersion
    {A : Type} [CommRing A] {Z : Scheme}
    (f : Z ⟶ scheme A d) (i : Fin (d + 1)) :
    IsOpenImmersion (((cover A d).pullback₁ f).f i) :=
  Scheme.Cover.map_prop ((cover A d).pullback₁ f) i

/-- The range of a component of the standard cover is its standard chart. -/
lemma standardCoverComponent_opensRange
    {A : Type} [CommRing A] (i : Fin (d + 1)) :
    ((cover A d).f i).opensRange = standardChart A i := by
  unfold cover
  apply TopologicalSpace.Opens.ext
  exact Scheme.Opens.range_ι (standardChart A i)

/--
The corresponding components of the two pulled-back standard covers have
the same open range in the common base scheme.
-/
lemma coefficientBaseChangeStandardChart_opensRange
    (i : Fin (d + 1)) :
    (((cover k d).pullback₁
      (g ≫ coefficientMap (algebraMap k R) d)).f i).opensRange =
      (((cover R d).pullback₁ g).f i).opensRange := by
  change
    (pullback.fst
      (g ≫ coefficientMap (algebraMap k R) d)
      ((cover k d).f i)).opensRange =
      (pullback.fst g ((cover R d).f i)).opensRange
  rw [Scheme.Hom.opensRange_pullbackFst,
    Scheme.Hom.opensRange_pullbackFst,
    standardCoverComponent_opensRange,
    standardCoverComponent_opensRange,
    Scheme.Hom.comp_preimage,
    coefficientMap_preimage_standardChart]

/--
The componentwise chart isomorphism between the pulled-back standard cover
over `k` and the pulled-back standard cover over `R`.
-/
def coefficientBaseChangeStandardChartIso
    (i : Fin (d + 1)) :
    ((cover k d).pullback₁
      (g ≫ coefficientMap (algebraMap k R) d)).X i ≅
      ((cover R d).pullback₁ g).X i :=
  ((((cover k d).pullback₁
      (g ≫ coefficientMap (algebraMap k R) d)).f i).isoOpensRange) ≪≫
    Y.isoOfEq
      (coefficientBaseChangeStandardChart_opensRange d g i) ≪≫
    ((((cover R d).pullback₁ g).f i).isoOpensRange).symm

/--
The componentwise chart isomorphism commutes with the two maps to the common
base scheme.
-/
@[reassoc]
lemma coefficientBaseChangeStandardChartIso_hom_coverMap
    (i : Fin (d + 1)) :
    (coefficientBaseChangeStandardChartIso d g i).hom ≫
      ((cover R d).pullback₁ g).f i =
        ((cover k d).pullback₁
          (g ≫ coefficientMap (algebraMap k R) d)).f i := by
  simp [coefficientBaseChangeStandardChartIso]

/--
The underlying pre-zero-hypercovers of the two pulled-back standard covers
are isomorphic without changing the chart index.
-/
def coefficientBaseChangeStandardCoverPreIso :
    ((cover k d).pullback₁
      (g ≫ coefficientMap (algebraMap k R) d)).toPreZeroHypercover ≅
      ((cover R d).pullback₁ g).toPreZeroHypercover :=
  PreZeroHypercover.isoMk
    (Equiv.refl (Fin (d + 1)))
    (coefficientBaseChangeStandardChartIso d g)
    (coefficientBaseChangeStandardChartIso_hom_coverMap d g)

/--
Coefficient extension identifies the two same-index pulled-back standard
open covers.
-/
def coefficientBaseChangeStandardCoverIso :
    (cover k d).pullback₁
        (g ≫ coefficientMap (algebraMap k R) d) ≅
      (cover R d).pullback₁ g :=
  Precoverage.ZeroHypercover.isoMk
    (coefficientBaseChangeStandardCoverPreIso d g)

/-- The coefficient-change cover isomorphism does not change chart indices. -/
@[simp]
theorem coefficientBaseChangeStandardCoverIso_hom_s₀
    (i : Fin (d + 1)) :
    (coefficientBaseChangeStandardCoverIso
      (k := k) (R := R) d g).hom.s₀ i = i :=
  rfl

/--
The forward chart component of the coefficient-change cover isomorphism is
the canonical coefficient base-change chart isomorphism.
-/
@[simp]
theorem coefficientBaseChangeStandardCoverIso_hom_h₀
    (i : Fin (d + 1)) :
    (coefficientBaseChangeStandardCoverIso
      (k := k) (R := R) d g).hom.h₀ i =
      (coefficientBaseChangeStandardChartIso
        (k := k) (R := R) d g i).hom :=
  rfl

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
