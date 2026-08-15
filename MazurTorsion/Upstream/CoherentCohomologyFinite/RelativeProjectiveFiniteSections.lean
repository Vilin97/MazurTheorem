/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineOpenProjectiveFactorization
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenRestrictionFiniteSections
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveFactorizationBaseExt
import MazurTorsion.Upstream.CoherentCohomologyFinite.RationalAlgebraFlat
import MazurTorsion.Upstream.CoherentCohomologyFinite.TopologicalSheafBaseLinearDegreeZero

/-!
# Finite sections of a relative-projective direct image

On an affine open of a locally Noetherian rational base, a relative
projective factorization becomes an ordinary projective factorization
over the ring of functions on that open.  Degree-zero projective Ext is
the module of sections, so the projective Ext finiteness theorem gives
finite generation of the corresponding direct-image sections.
-/


open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.TopCat
open SerreTwist

/--
Sections of a coherent module over the inverse image of an affine open
are finite over the ring of functions on the open when the morphism is
relative projective.
-/
theorem finiteSections_preimage_of_relativeProjectiveFactorization
    {Y X : Scheme.{0}}
    {s : X ⟶ Spec (CommRingCat.of ℚ)}
    {f : Y ⟶ X}
    [IsLocallyNoetherian X]
    (hprojective : IsRelativeProjectiveFactorization s f)
    (M : Y.Modules) [M.IsFiniteType] [M.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U)
    (hchart :
      ∀ (d : ℕ) (m : ℤ),
        BaseStandardCoverCoordinatesNatural Γ(X, U) d m)
    (hcoordinate :
      ∀ (d N : ℕ),
        IntegerOverChartCoordinateTransition Γ(X, U) d N) :
    letI : Algebra ℚ Γ(X, U) :=
      (affineOpenCoefficientMap s U hU).hom.toAlgebra
    letI :
        (f ⁻¹ᵁ U).toScheme.Over
          (Spec (CommRingCat.of Γ(X, U))) :=
      ⟨morphismRestrict f U ≫ hU.isoSpec.hom⟩
    Module.Finite Γ(X, U)
      ((moduleSheaf
        (k := Γ(X, U))
        (M.restrict (f ⁻¹ᵁ U).ι)).obj.obj
          (op (⊤ :
            Opens ((f ⁻¹ᵁ U).toScheme : TopCat)))) := by
  letI : Algebra ℚ Γ(X, U) :=
    (affineOpenCoefficientMap s U hU).hom.toAlgebra
  letI : Module.Flat ℤ Γ(X, U) :=
    moduleFlat_int_of_algebra_rat Γ(X, U)
  letI : IsNoetherianRing Γ(X, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  letI :
      (f ⁻¹ᵁ U).toScheme.Over
        (Spec (CommRingCat.of Γ(X, U))) :=
    ⟨morphismRestrict f U ≫ hU.isoSpec.hom⟩
  let N : (f ⁻¹ᵁ U).toScheme.Modules :=
    M.restrict (f ⁻¹ᵁ U).ι
  letI : N.IsFiniteType := inferInstance
  letI : N.IsQuasicoherent := inferInstance
  letI :
      AddCommGroup
        (Abelian.Ext
          (constantRankOneSheaf
            (R := Γ(X, U)) ((f ⁻¹ᵁ U).toScheme : TopCat))
          (moduleSheaf (k := Γ(X, U)) N) 0) :=
    CategoryTheory.Abelian.Ext.instAddCommGroup
  letI :
      Module Γ(X, U)
        (Abelian.Ext
          (constantRankOneSheaf
            (R := Γ(X, U)) ((f ⁻¹ᵁ U).toScheme : TopCat))
          (moduleSheaf (k := Γ(X, U)) N) 0) :=
    CategoryTheory.Abelian.Ext.instModule
  have hExt :
      Module.Finite Γ(X, U)
        (Abelian.Ext
          (constantRankOneSheaf
            (R := Γ(X, U)) ((f ⁻¹ᵁ U).toScheme : TopCat))
          (moduleSheaf (k := Γ(X, U)) N) 0) :=
    coherentModuleSheafExt_finite_of_projectiveFactorization
      (hprojective.isProjectiveFactorization_affineOpen U hU)
      hchart hcoordinate N 0
  have htop :
      Module.Finite Γ(X, U)
        ((moduleSheaf (k := Γ(X, U)) N).obj.obj
          (op (⊤ : Opens ((f ⁻¹ᵁ U).toScheme : TopCat)))) :=
    (constantRankOneExtZero_finite_iff_sections
      (moduleSheaf (k := Γ(X, U)) N)).mp hExt
  exact htop

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
