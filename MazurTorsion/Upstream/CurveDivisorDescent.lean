/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveAffineChart
import MazurTorsion.Upstream.AffineDivisorLocalization
import MazurTorsion.Upstream.CurveLineBundleLocality
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Chartwise divisor line bundles and their descent boundary

This file restricts a global Weil divisor to compatible Dedekind affine charts and constructs
the actual Tau Ceti invertible sheaf `O(D)` on every coordinate spectrum. Restriction preserves
addition, and a global principal divisor gives the affine principal divisor and hence the
trivial local line bundle.

For a covering family of affine opens, `DivisorCocycle` is the exact remaining overlap input:
pairwise isomorphisms between these specific local line bundles, diagonal normalization, and
the triple-overlap cocycle. On a single chart, equality of the ambient divisor coefficients on a
principal open constructs the actual pairwise restriction isomorphism. Across two charts, every
compatible common Dedekind affine-overlap presentation now constructs the actual restriction
isomorphism for an arbitrary ambient divisor. Open-immersion prime extension supplies equality of
the extended inverse ideals, affine tilde base change supplies both restriction comparisons, and
equality of the two maps to the ambient curve proves the required coefficient equality
automatically. Moreover, a chosen common Dedekind affine subopen canonically supplies every
algebra map, open immersion, scalar tower, and map compatibility used by that theorem. Principal
divisors retain a direct rational-function shortcut. On a separated integral scheme, the full
intersection of two nonempty affine charts is affine and nonempty; a final checked consumer gives
the arbitrary-divisor isomorphism there once its coordinate ring is Dedekind. Properness over a
field supplies the required absolute separatedness automatically. Transporting these intersection
isomorphisms to the chosen descent pullbacks, normalizing them, and proving cover-wide cocycle
coherence remain. Given
object-specific effective invertible descent, the checked
consumer `globalLineBundle` constructs a global line bundle and identifies every chart
restriction with the affine `O(D)`. Proven locality of invertibility now upgrades ordinary
module effectivity to this input. Coherent triviality of a principal cocycle, together with
essential injectivity on objects for module descent, makes that global line bundle trivial;
fully faithful descent is a checked sufficient source of this exact input. No cover-wide divisor
cocycle, module-effectivity theorem, or object-separation theorem is asserted here.
-/

namespace MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

universe u v

open CategoryTheory MonoidalCategory
open CategoryTheory.Limits
open TopologicalSpace
open _root_.AlgebraicGeometry
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open IsDedekindDomain
open AffineDivisorLocalization
open scoped AlgebraicGeometry

/-- The standard monoidal structure on sheaves of modules over a scheme. -/
noncomputable local instance schemeModulesMonoidal (Y : Scheme.{u}) :
    MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y

/-- Restrict a Weil divisor to the codimension-one points in an open subset. -/
noncomputable def restrictDivisor
    (X : Scheme.{u}) (U : X.Opens) :
    WeilDivisor (CodimensionOnePoint X) →+
      WeilDivisor {x : CodimensionOnePoint X // x.1 ∈ U} :=
  Finsupp.subtypeDomainAddMonoidHom
    (p := fun x : CodimensionOnePoint X ↦ x.1 ∈ U)

@[simp]
lemma restrictDivisor_apply
    (X : Scheme.{u}) (U : X.Opens)
    (D : WeilDivisor (CodimensionOnePoint X))
    (x : {x : CodimensionOnePoint X // x.1 ∈ U}) :
    restrictDivisor X U D x = D x.1 := by
  exact Finsupp.subtypeDomain_apply

/-- Restriction of a principal divisor for the geometric order system is the ambient principal
divisor on the chart. -/
lemma restrictDivisor_principalDivisor
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
    (h : AffineChart.DedekindOrderCompatibility X U hU)
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (hord : S.ord = SchemeWeilDivisor.orderAt)
    (g : Additive X.functionFieldˣ) :
    restrictDivisor X U (S.principalDivisor g) =
      (h.ambientOrderSystem X U hU).principalDivisor g := by
  ext x
  change restrictDivisor X U (S.principalDivisor g) x =
    (h.ambientOrderSystem X U hU).principalDivisor g x
  change WeilDivisor.coeff (S.principalDivisor g) x.1 =
    WeilDivisor.coeff ((h.ambientOrderSystem X U hU).principalDivisor g) x
  rw [OrderSystem.coeff_principalDivisor,
    OrderSystem.coeff_principalDivisor]
  change S.ord x.1 g = SchemeWeilDivisor.orderAt x.1 g
  rw [hord]

/-- The restriction of a global divisor, expressed on height-one primes of a compatible
Dedekind affine chart. -/
noncomputable def localDivisor
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
    (h : AffineChart.DedekindOrderCompatibility X U hU)
    (D : WeilDivisor (CodimensionOnePoint X)) :
    WeilDivisor (HeightOneSpectrum Γ(X, U)) :=
  (h.divisorEquiv X U hU).symm (restrictDivisor X U D)

/-- A coordinate divisor has at a chart prime the coefficient of the original global divisor
at the corresponding ambient codimension-one point. -/
lemma localDivisor_coeff
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
    (h : AffineChart.DedekindOrderCompatibility X U hU)
    (D : WeilDivisor (CodimensionOnePoint X))
    (v : HeightOneSpectrum Γ(X, U)) :
    coeff (localDivisor X U hU h D) v =
      coeff D (h.pointEquiv X U hU v).1 := by
  let e := h.divisorEquiv X U hU
  have he := e.apply_symm_apply (restrictDivisor X U D)
  have hev := DFunLike.congr_fun he (h.pointEquiv X U hU v)
  change (e.symm (restrictDivisor X U D)) v =
    D (h.pointEquiv X U hU v).1
  calc
    (e.symm (restrictDivisor X U D)) v =
        e (e.symm (restrictDivisor X U D))
          (h.pointEquiv X U hU v) := by
      change _ = Finsupp.domCongr (h.pointEquiv X U hU)
        (e.symm (restrictDivisor X U D)) (h.pointEquiv X U hU v)
      rw [Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain,
        Finsupp.mapDomain_equiv_apply, Equiv.symm_apply_apply]
    _ = restrictDivisor X U D (h.pointEquiv X U hU v) := hev
    _ = D (h.pointEquiv X U hU v).1 := restrictDivisor_apply X U D _

/-- Restriction and chart reindexing preserve divisor addition. -/
lemma localDivisor_add
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
    (h : AffineChart.DedekindOrderCompatibility X U hU)
    (D E : WeilDivisor (CodimensionOnePoint X)) :
    localDivisor X U hU h (D + E) =
      localDivisor X U hU h D + localDivisor X U hU h E := by
  simp [localDivisor]

/-- The coordinate divisor obtained from a global principal divisor is the affine Dedekind
principal divisor. -/
lemma localDivisor_principalDivisor
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
    (h : AffineChart.DedekindOrderCompatibility X U hU)
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (hord : S.ord = SchemeWeilDivisor.orderAt)
    (g : Additive X.functionFieldˣ) :
    localDivisor X U hU h (S.principalDivisor g) =
      (h.affineOrderSystem X U hU).principalDivisor g := by
  apply (h.divisorEquiv X U hU).injective
  change
    h.divisorEquiv X U hU
        ((h.divisorEquiv X U hU).symm
          (restrictDivisor X U (S.principalDivisor g))) =
      h.divisorEquiv X U hU
        ((h.affineOrderSystem X U hU).principalDivisor g)
  rw [AddEquiv.apply_symm_apply,
    h.principalDivisor_reindex_eq_ambientPrincipalDivisor X U hU]
  exact restrictDivisor_principalDivisor X U hU h S hord g

/-- The actual affine line bundle associated to the restriction of a global divisor. -/
noncomputable def localLineBundle
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
    (h : AffineChart.DedekindOrderCompatibility X U hU)
    (D : WeilDivisor (CodimensionOnePoint X)) :
    InvertibleSheaf (Spec (.of Γ(X, U))) := by
  letI := h.isDedekindDomain
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  exact AffineDedekind.lineBundle Γ(X, U) X.functionField
    (localDivisor X U hU h D)

/-- If the two affine-coordinate maps from a common overlap induce the same map to the ambient
curve, contraction of an overlap height-one prime through either coordinate ring gives the same
ambient codimension-one point. -/
lemma contractedPoint_eq_of_commonMap
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (U₁ U₂ : X.Opens) [Nonempty U₁] [Nonempty U₂]
    (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂)
    (h₁ : AffineChart.DedekindOrderCompatibility X U₁ hU₁)
    (h₂ : AffineChart.DedekindOrderCompatibility X U₂ hU₂)
    [IsDedekindDomain Γ(X, U₁)] [IsDedekindDomain Γ(X, U₂)]
    (B : Type u) [CommRing B] [IsDedekindDomain B]
    [Algebra Γ(X, U₁) B] [Algebra Γ(X, U₂) B]
    [IsOpenImmersion
      (AffineDivisorLocalization.CommonExtension.extensionMap Γ(X, U₁) B)]
    [IsOpenImmersion
      (AffineDivisorLocalization.CommonExtension.extensionMap Γ(X, U₂) B)]
    (j : Spec (.of B) ⟶ X)
    (hj₁ : AffineDivisorLocalization.CommonExtension.extensionMap Γ(X, U₁) B ≫
      hU₁.fromSpec = j)
    (hj₂ : AffineDivisorLocalization.CommonExtension.extensionMap Γ(X, U₂) B ≫
      hU₂.fromSpec = j)
    (q : HeightOneSpectrum B) :
    (h₁.pointEquiv X U₁ hU₁
      (AffineDivisorLocalization.Boundary.underHeightOneOpenImmersion
        Γ(X, U₁) B q)).1.1 =
      (h₂.pointEquiv X U₂ hU₂
        (AffineDivisorLocalization.Boundary.underHeightOneOpenImmersion
          Γ(X, U₂) B q)).1.1 := by
  let y : Spec (.of B) := ⟨q.asIdeal, q.isPrime⟩
  calc
    (h₁.pointEquiv X U₁ hU₁
        (AffineDivisorLocalization.Boundary.underHeightOneOpenImmersion
          Γ(X, U₁) B q)).1.1 =
        hU₁.fromSpec
          ⟨(AffineDivisorLocalization.Boundary.underHeightOneOpenImmersion
              Γ(X, U₁) B q).asIdeal,
            (AffineDivisorLocalization.Boundary.underHeightOneOpenImmersion
              Γ(X, U₁) B q).isPrime⟩ := by
      change (AffineChart.affineOpenHeightOneSpectrumEquiv X U₁ hU₁
        (AffineDivisorLocalization.Boundary.underHeightOneOpenImmersion
          Γ(X, U₁) B q)).1.1 = _
      rw [AffineChart.affineOpenHeightOneSpectrumEquiv_apply_val]
    _ = (AffineDivisorLocalization.CommonExtension.extensionMap Γ(X, U₁) B ≫
          hU₁.fromSpec) y := by
      rfl
    _ = j y := by rw [hj₁]
    _ = (AffineDivisorLocalization.CommonExtension.extensionMap Γ(X, U₂) B ≫
          hU₂.fromSpec) y := by
      rw [hj₂]
    _ = hU₂.fromSpec
          ⟨(AffineDivisorLocalization.Boundary.underHeightOneOpenImmersion
              Γ(X, U₂) B q).asIdeal,
            (AffineDivisorLocalization.Boundary.underHeightOneOpenImmersion
              Γ(X, U₂) B q).isPrime⟩ := by
      rfl
    _ = (h₂.pointEquiv X U₂ hU₂
        (AffineDivisorLocalization.Boundary.underHeightOneOpenImmersion
          Γ(X, U₂) B q)).1.1 := by
      change _ = (AffineChart.affineOpenHeightOneSpectrumEquiv X U₂ hU₂
        (AffineDivisorLocalization.Boundary.underHeightOneOpenImmersion
          Γ(X, U₂) B q)).1.1
      rw [AffineChart.affineOpenHeightOneSpectrumEquiv_apply_val]

/-- For restrictions of one ambient divisor, compatibility of the two common-overlap maps
automatically supplies the contracted coefficient equality required by the algebraic theorem. -/
lemma openImmersionCoefficientEq_localDivisor_of_commonMap
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (U₁ U₂ : X.Opens) [Nonempty U₁] [Nonempty U₂]
    (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂)
    (h₁ : AffineChart.DedekindOrderCompatibility X U₁ hU₁)
    (h₂ : AffineChart.DedekindOrderCompatibility X U₂ hU₂)
    [IsDedekindDomain Γ(X, U₁)] [IsDedekindDomain Γ(X, U₂)]
    (B : Type u) [CommRing B] [IsDedekindDomain B]
    [Algebra Γ(X, U₁) B] [Algebra Γ(X, U₂) B]
    [IsOpenImmersion
      (AffineDivisorLocalization.CommonExtension.extensionMap Γ(X, U₁) B)]
    [IsOpenImmersion
      (AffineDivisorLocalization.CommonExtension.extensionMap Γ(X, U₂) B)]
    (j : Spec (.of B) ⟶ X)
    (hj₁ : AffineDivisorLocalization.CommonExtension.extensionMap Γ(X, U₁) B ≫
      hU₁.fromSpec = j)
    (hj₂ : AffineDivisorLocalization.CommonExtension.extensionMap Γ(X, U₂) B ≫
      hU₂.fromSpec = j)
    (D : WeilDivisor (CodimensionOnePoint X)) :
    AffineDivisorLocalization.Boundary.OpenImmersionCoefficientEq
      Γ(X, U₁) Γ(X, U₂) B
      (localDivisor X U₁ hU₁ h₁ D)
      (localDivisor X U₂ hU₂ h₂ D) := by
  intro q
  rw [localDivisor_coeff X U₁ hU₁ h₁ D,
    localDivisor_coeff X U₂ hU₂ h₂ D]
  congr 1
  ext
  exact contractedPoint_eq_of_commonMap X U₁ U₂ hU₁ hU₂ h₁ h₂ B
    j hj₁ hj₂ q

/-- A compatible common affine-overlap presentation makes the two inverse ideals attached to
the chart restrictions of one ambient divisor equal after extension to the overlap ring. -/
lemma overlapInverseIdealExtensionEq_localDivisor_of_commonMap
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (U₁ U₂ : X.Opens) [Nonempty U₁] [Nonempty U₂]
    (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂)
    (h₁ : AffineChart.DedekindOrderCompatibility X U₁ hU₁)
    (h₂ : AffineChart.DedekindOrderCompatibility X U₂ hU₂)
    [IsDedekindDomain Γ(X, U₁)] [IsDedekindDomain Γ(X, U₂)]
    [IsFractionRing Γ(X, U₁) X.functionField]
    [IsFractionRing Γ(X, U₂) X.functionField]
    (B : Type u) [CommRing B] [IsDedekindDomain B]
    [Algebra Γ(X, U₁) B] [Module.IsTorsionFree Γ(X, U₁) B]
    [Algebra Γ(X, U₂) B] [Module.IsTorsionFree Γ(X, U₂) B]
    [Algebra B X.functionField] [IsFractionRing B X.functionField]
    [IsOpenImmersion
      (AffineDivisorLocalization.CommonExtension.extensionMap Γ(X, U₁) B)]
    [IsOpenImmersion
      (AffineDivisorLocalization.CommonExtension.extensionMap Γ(X, U₂) B)]
    (htower₁ : IsScalarTower Γ(X, U₁) B X.functionField)
    (htower₂ : IsScalarTower Γ(X, U₂) B X.functionField)
    (j : Spec (.of B) ⟶ X)
    (hj₁ : AffineDivisorLocalization.CommonExtension.extensionMap Γ(X, U₁) B ≫
      hU₁.fromSpec = j)
    (hj₂ : AffineDivisorLocalization.CommonExtension.extensionMap Γ(X, U₂) B ≫
      hU₂.fromSpec = j)
    (D : WeilDivisor (CodimensionOnePoint X)) :
    AffineDivisorLocalization.Boundary.OverlapInverseIdealExtensionEq
      Γ(X, U₁) Γ(X, U₂) B X.functionField
      (localDivisor X U₁ hU₁ h₁ D)
      (localDivisor X U₂ hU₂ h₂ D) :=
  AffineDivisorLocalization.Boundary.overlapInverseIdealExtensionEq_of_openImmersion_coeff_eq
      Γ(X, U₁) Γ(X, U₂) B X.functionField htower₁ htower₂ _ _
      (openImmersionCoefficientEq_localDivisor_of_commonMap
        X U₁ U₂ hU₁ hU₂ h₁ h₂ B j hj₁ hj₂ D)

/-- A compatible common affine-overlap presentation constructs the actual pairwise isomorphism
between the two chartwise divisor line-bundle restrictions for every ambient divisor. -/
noncomputable def localLineBundleRestrictionIsoOfCommonMap
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (U₁ U₂ : X.Opens) [Nonempty U₁] [Nonempty U₂]
    (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂)
    (h₁ : AffineChart.DedekindOrderCompatibility X U₁ hU₁)
    (h₂ : AffineChart.DedekindOrderCompatibility X U₂ hU₂)
    [IsDedekindDomain Γ(X, U₁)] [IsDedekindDomain Γ(X, U₂)]
    (B : Type u) [CommRing B] [IsDedekindDomain B]
    [Algebra Γ(X, U₁) B] [Module.IsTorsionFree Γ(X, U₁) B]
    [Algebra Γ(X, U₂) B] [Module.IsTorsionFree Γ(X, U₂) B]
    [Algebra B X.functionField] [IsFractionRing B X.functionField]
    [IsOpenImmersion
      (AffineDivisorLocalization.CommonExtension.extensionMap Γ(X, U₁) B)]
    [IsOpenImmersion
      (AffineDivisorLocalization.CommonExtension.extensionMap Γ(X, U₂) B)]
    (htower₁ : IsScalarTower Γ(X, U₁) B X.functionField)
    (htower₂ : IsScalarTower Γ(X, U₂) B X.functionField)
    (j : Spec (.of B) ⟶ X)
    (hj₁ : AffineDivisorLocalization.CommonExtension.extensionMap Γ(X, U₁) B ≫
      hU₁.fromSpec = j)
    (hj₂ : AffineDivisorLocalization.CommonExtension.extensionMap Γ(X, U₂) B ≫
      hU₂.fromSpec = j)
    (D : WeilDivisor (CodimensionOnePoint X)) :
    (localLineBundle X U₁ hU₁ h₁ D).obj.restrict
        (AffineDivisorLocalization.CommonExtension.extensionMap Γ(X, U₁) B) ≅
      (localLineBundle X U₂ hU₂ h₂ D).obj.restrict
        (AffineDivisorLocalization.CommonExtension.extensionMap Γ(X, U₂) B) := by
  letI : IsFractionRing Γ(X, U₁) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U₁ hU₁
  letI : IsFractionRing Γ(X, U₂) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U₂ hU₂
  change
    (AffineDedekind.lineBundle Γ(X, U₁) X.functionField
        (localDivisor X U₁ hU₁ h₁ D)).obj.restrict
        (AffineDivisorLocalization.CommonExtension.extensionMap Γ(X, U₁) B) ≅
      (AffineDedekind.lineBundle Γ(X, U₂) X.functionField
        (localDivisor X U₂ hU₂ h₂ D)).obj.restrict
        (AffineDivisorLocalization.CommonExtension.extensionMap Γ(X, U₂) B)
  exact AffineDivisorLocalization.CommonExtension.chosenLineBundleRestrictionIsoOfOverlapExtensionEq
      Γ(X, U₁) Γ(X, U₂) B X.functionField _ _
      (overlapInverseIdealExtensionEq_localDivisor_of_commonMap
        X U₁ U₂ hU₁ hU₂ h₁ h₂ B htower₁ htower₂ j hj₁ hj₂ D)

/-- The coordinate-ring algebra induced by restriction from an affine open to a smaller one. -/
noncomputable abbrev restrictionAlgebra
    (X : Scheme.{u}) (U W : X.Opens) (hWU : W ≤ U) :
    Algebra Γ(X, U) Γ(X, W) :=
  (X.presheaf.map (homOfLE hWU).op).hom.toAlgebra

/-- The spectrum map induced by section restriction, followed by the larger affine chart map,
is the canonical map from the smaller affine open to the ambient scheme. -/
lemma restrictionExtensionMap_comp_fromSpec
    (X : Scheme.{u}) (U W : X.Opens)
    (hU : IsAffineOpen U) (hW : IsAffineOpen W) (hWU : W ≤ U) :
    letI := restrictionAlgebra X U W hWU
    CommonExtension.extensionMap Γ(X, U) Γ(X, W) ≫ hU.fromSpec = hW.fromSpec := by
  change Spec.map (X.presheaf.map (homOfLE hWU).op) ≫ hU.fromSpec = hW.fromSpec
  exact hU.map_fromSpec hW (homOfLE hWU).op

/-- Restriction from an affine open to an affine subopen induces an affine open immersion on
coordinate spectra. -/
lemma restrictionExtensionMapIsOpenImmersion
    (X : Scheme.{u}) (U W : X.Opens)
    (hU : IsAffineOpen U) (hW : IsAffineOpen W) (hWU : W ≤ U) :
    letI := restrictionAlgebra X U W hWU
    IsOpenImmersion (CommonExtension.extensionMap Γ(X, U) Γ(X, W)) := by
  letI := restrictionAlgebra X U W hWU
  letI : IsOpenImmersion
      (CommonExtension.extensionMap Γ(X, U) Γ(X, W) ≫ hU.fromSpec) := by
    rw [restrictionExtensionMap_comp_fromSpec X U W hU hW hWU]
    infer_instance
  exact IsOpenImmersion.of_comp
    (CommonExtension.extensionMap Γ(X, U) Γ(X, W)) hU.fromSpec

private lemma restrictionFunctionFieldTower
    (X : Scheme.{u}) [IsIntegral X]
    (U W : X.Opens) [Nonempty U] [Nonempty W] (hWU : W ≤ U) :
    letI := restrictionAlgebra X U W hWU
    IsScalarTower Γ(X, U) Γ(X, W) X.functionField := by
  letI := restrictionAlgebra X U W hWU
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro s
  change (X.germToFunctionField U).hom s =
    (X.germToFunctionField W).hom ((X.presheaf.map (homOfLE hWU).op).hom s)
  have h := DFunLike.congr_fun
    (CommRingCat.hom_ext_iff.mp
      (X.presheaf.germ_res (homOfLE hWU) (genericPoint X)
        (((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr
          (by simpa using (inferInstance : Nonempty W))))) s
  exact h.symm

private lemma restrictionTorsionFree
    (X : Scheme.{u}) [IsIntegral X]
    (U W : X.Opens) [Nonempty W] [IsDomain Γ(X, U)] (hWU : W ≤ U) :
    letI := restrictionAlgebra X U W hWU
    Module.IsTorsionFree Γ(X, U) Γ(X, W) := by
  letI := restrictionAlgebra X U W hWU
  apply Module.isTorsionFree_iff_algebraMap_injective.mpr
  change Function.Injective (X.presheaf.map (homOfLE hWU).op)
  exact map_injective_of_isIntegral X (homOfLE hWU)

/-- Every chosen common Dedekind affine subopen of two compatible charts canonically constructs
the actual arbitrary-divisor restriction isomorphism on that subopen. All algebra maps, open
immersions, common-function-field towers, and ambient-map compatibilities are derived from
presheaf restriction. -/
noncomputable def localLineBundleRestrictionIsoOnCommonAffineOpen
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (U₁ U₂ W : X.Opens) [Nonempty U₁] [Nonempty U₂] [Nonempty W]
    (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂) (hW : IsAffineOpen W)
    (hWU₁ : W ≤ U₁) (hWU₂ : W ≤ U₂)
    (h₁ : AffineChart.DedekindOrderCompatibility X U₁ hU₁)
    (h₂ : AffineChart.DedekindOrderCompatibility X U₂ hU₂)
    [IsDedekindDomain Γ(X, U₁)] [IsDedekindDomain Γ(X, U₂)]
    [IsDedekindDomain Γ(X, W)]
    (D : WeilDivisor (CodimensionOnePoint X)) :
    letI := restrictionAlgebra X U₁ W hWU₁
    letI := restrictionAlgebra X U₂ W hWU₂
    letI : IsOpenImmersion
        (CommonExtension.extensionMap Γ(X, U₁) Γ(X, W)) :=
      restrictionExtensionMapIsOpenImmersion X U₁ W hU₁ hW hWU₁
    letI : IsOpenImmersion
        (CommonExtension.extensionMap Γ(X, U₂) Γ(X, W)) :=
      restrictionExtensionMapIsOpenImmersion X U₂ W hU₂ hW hWU₂
    (localLineBundle X U₁ hU₁ h₁ D).obj.restrict
        (CommonExtension.extensionMap Γ(X, U₁) Γ(X, W)) ≅
      (localLineBundle X U₂ hU₂ h₂ D).obj.restrict
        (CommonExtension.extensionMap Γ(X, U₂) Γ(X, W)) := by
  letI := restrictionAlgebra X U₁ W hWU₁
  letI := restrictionAlgebra X U₂ W hWU₂
  letI : Module.IsTorsionFree Γ(X, U₁) Γ(X, W) :=
    restrictionTorsionFree X U₁ W hWU₁
  letI : Module.IsTorsionFree Γ(X, U₂) Γ(X, W) :=
    restrictionTorsionFree X U₂ W hWU₂
  letI : IsOpenImmersion
      (CommonExtension.extensionMap Γ(X, U₁) Γ(X, W)) := by
    exact restrictionExtensionMapIsOpenImmersion X U₁ W hU₁ hW hWU₁
  letI : IsOpenImmersion
      (CommonExtension.extensionMap Γ(X, U₂) Γ(X, W)) := by
    exact restrictionExtensionMapIsOpenImmersion X U₂ W hU₂ hW hWU₂
  letI : IsFractionRing Γ(X, W) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X W hW
  exact localLineBundleRestrictionIsoOfCommonMap X U₁ U₂ hU₁ hU₂ h₁ h₂
    Γ(X, W) (restrictionFunctionFieldTower X U₁ W hWU₁)
      (restrictionFunctionFieldTower X U₂ W hWU₂) hW.fromSpec
      (restrictionExtensionMap_comp_fromSpec X U₁ W hU₁ hW hWU₁)
      (restrictionExtensionMap_comp_fromSpec X U₂ W hU₂ hW hWU₂) D

private lemma nonempty_inf_of_isIntegral
    (X : Scheme.{u}) [IsIntegral X]
    (U V : X.Opens) [Nonempty U] [Nonempty V] :
    Nonempty ↑(U ⊓ V : X.Opens) := by
  have hU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
      (by simpa using (inferInstance : Nonempty U))
  have hV : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr
      (by simpa using (inferInstance : Nonempty V))
  exact ⟨⟨genericPoint X, hU, hV⟩⟩

/-- On an absolutely separated integral scheme, the full intersection of two nonempty affine
charts is a nonempty affine open. Once its coordinate ring is Dedekind, the arbitrary-divisor
restriction isomorphism is therefore constructed on the full pairwise intersection. -/
noncomputable def localLineBundleRestrictionIsoOnIntersection
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    [IsSeparated (terminal.from X)]
    (U₁ U₂ : X.Opens) [Nonempty U₁] [Nonempty U₂]
    (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂)
    (h₁ : AffineChart.DedekindOrderCompatibility X U₁ hU₁)
    (h₂ : AffineChart.DedekindOrderCompatibility X U₂ hU₂)
    [IsDedekindDomain Γ(X, U₁)] [IsDedekindDomain Γ(X, U₂)]
    [IsDedekindDomain Γ(X, U₁ ⊓ U₂)]
    (D : WeilDivisor (CodimensionOnePoint X)) :
    letI := restrictionAlgebra X U₁ (U₁ ⊓ U₂) inf_le_left
    letI := restrictionAlgebra X U₂ (U₁ ⊓ U₂) inf_le_right
    letI : IsOpenImmersion
        (CommonExtension.extensionMap Γ(X, U₁) Γ(X, U₁ ⊓ U₂)) :=
      restrictionExtensionMapIsOpenImmersion X U₁ (U₁ ⊓ U₂)
        hU₁ (hU₁.inf hU₂) inf_le_left
    letI : IsOpenImmersion
        (CommonExtension.extensionMap Γ(X, U₂) Γ(X, U₁ ⊓ U₂)) :=
      restrictionExtensionMapIsOpenImmersion X U₂ (U₁ ⊓ U₂)
        hU₂ (hU₁.inf hU₂) inf_le_right
    (localLineBundle X U₁ hU₁ h₁ D).obj.restrict
        (CommonExtension.extensionMap Γ(X, U₁) Γ(X, U₁ ⊓ U₂)) ≅
      (localLineBundle X U₂ hU₂ h₂ D).obj.restrict
        (CommonExtension.extensionMap Γ(X, U₂) Γ(X, U₁ ⊓ U₂)) := by
  letI : Nonempty ↑(U₁ ⊓ U₂ : X.Opens) := nonempty_inf_of_isIntegral X U₁ U₂
  exact localLineBundleRestrictionIsoOnCommonAffineOpen X U₁ U₂ (U₁ ⊓ U₂)
    hU₁ hU₂ (hU₁.inf hU₂) inf_le_left inf_le_right h₁ h₂ D

/-- Relative properness over a field supplies the absolute separatedness needed to compare the
chosen divisor line bundles on the full intersection of two affine charts. -/
noncomputable def localLineBundleRestrictionIsoOnProperCurveIntersection
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f]
    (U₁ U₂ : X.Opens) [Nonempty U₁] [Nonempty U₂]
    (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂)
    (h₁ : AffineChart.DedekindOrderCompatibility X U₁ hU₁)
    (h₂ : AffineChart.DedekindOrderCompatibility X U₂ hU₂)
    [IsDedekindDomain Γ(X, U₁)] [IsDedekindDomain Γ(X, U₂)]
    [IsDedekindDomain Γ(X, U₁ ⊓ U₂)]
    (D : WeilDivisor (CodimensionOnePoint X)) :
    letI : IsSeparated (terminal.from X) := by
      rw [← terminal.comp_from f]
      infer_instance
    letI := restrictionAlgebra X U₁ (U₁ ⊓ U₂) inf_le_left
    letI := restrictionAlgebra X U₂ (U₁ ⊓ U₂) inf_le_right
    letI : IsOpenImmersion
        (CommonExtension.extensionMap Γ(X, U₁) Γ(X, U₁ ⊓ U₂)) :=
      restrictionExtensionMapIsOpenImmersion X U₁ (U₁ ⊓ U₂)
        hU₁ (hU₁.inf hU₂) inf_le_left
    letI : IsOpenImmersion
        (CommonExtension.extensionMap Γ(X, U₂) Γ(X, U₁ ⊓ U₂)) :=
      restrictionExtensionMapIsOpenImmersion X U₂ (U₁ ⊓ U₂)
        hU₂ (hU₁.inf hU₂) inf_le_right
    (localLineBundle X U₁ hU₁ h₁ D).obj.restrict
        (CommonExtension.extensionMap Γ(X, U₁) Γ(X, U₁ ⊓ U₂)) ≅
      (localLineBundle X U₂ hU₂ h₂ D).obj.restrict
        (CommonExtension.extensionMap Γ(X, U₂) Γ(X, U₁ ⊓ U₂)) := by
  letI : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  exact localLineBundleRestrictionIsoOnIntersection X U₁ U₂ hU₁ hU₂ h₁ h₂ D

/-- For a proper smooth relative curve, the mapwise normality input on the full affine
intersection supplies its Dedekind-domain instance and hence the actual overlap isomorphism. -/
noncomputable def localLineBundleRestrictionIsoOnProperSmoothCurveIntersectionOfNormality
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (U₁ U₂ : X.Opens) [Nonempty U₁] [Nonempty U₂]
    (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂)
    (h₁ : AffineChart.DedekindOrderCompatibility X U₁ hU₁)
    (h₂ : AffineChart.DedekindOrderCompatibility X U₂ hU₂)
    [IsDedekindDomain Γ(X, U₁)] [IsDedekindDomain Γ(X, U₂)]
    (hnormal : RingHom.Locally
      (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (f.appLE ⊤ (U₁ ⊓ U₂) le_top).hom →
        IsIntegrallyClosed Γ(X, U₁ ⊓ U₂))
    (D : WeilDivisor (CodimensionOnePoint X)) :
    letI : IsSeparated (terminal.from X) := by
      rw [← terminal.comp_from f]
      infer_instance
    letI := restrictionAlgebra X U₁ (U₁ ⊓ U₂) inf_le_left
    letI := restrictionAlgebra X U₂ (U₁ ⊓ U₂) inf_le_right
    letI : IsOpenImmersion
        (CommonExtension.extensionMap Γ(X, U₁) Γ(X, U₁ ⊓ U₂)) :=
      restrictionExtensionMapIsOpenImmersion X U₁ (U₁ ⊓ U₂)
        hU₁ (hU₁.inf hU₂) inf_le_left
    letI : IsOpenImmersion
        (CommonExtension.extensionMap Γ(X, U₂) Γ(X, U₁ ⊓ U₂)) :=
      restrictionExtensionMapIsOpenImmersion X U₂ (U₁ ⊓ U₂)
        hU₂ (hU₁.inf hU₂) inf_le_right
    (localLineBundle X U₁ hU₁ h₁ D).obj.restrict
        (CommonExtension.extensionMap Γ(X, U₁) Γ(X, U₁ ⊓ U₂)) ≅
      (localLineBundle X U₂ hU₂ h₂ D).obj.restrict
        (CommonExtension.extensionMap Γ(X, U₂) Γ(X, U₁ ⊓ U₂)) := by
  letI : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  letI : Nonempty ↑(U₁ ⊓ U₂ : X.Opens) :=
    nonempty_inf_of_isIntegral X U₁ U₂
  let hW : IsAffineOpen (U₁ ⊓ U₂) := hU₁.inf hU₂
  let hcompat := AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurveNormality
    K X f (U₁ ⊓ U₂) hW hnormal
  letI : IsDedekindDomain Γ(X, U₁ ⊓ U₂) := hcompat.isDedekindDomain
  exact localLineBundleRestrictionIsoOnProperCurveIntersection
    K X f U₁ U₂ hU₁ hU₂ h₁ h₂ D

/-- On one affine chart, equality of the ambient divisor coefficients at every point of
`D(f)` supplies the pairwise restriction isomorphism of the chartwise divisor line bundles.
This is a concrete same-chart input toward `DivisorCocycle`; comparisons between two different
coordinate rings and triple-overlap coherence remain separate requirements. -/
noncomputable def localLineBundleRestrictIsoOfCoeffEq
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
    (h : AffineChart.DedekindOrderCompatibility X U hU)
    (D E : WeilDivisor (CodimensionOnePoint X)) (f : Γ(X, U))
    (hcoeff : ∀ v : HeightOneSpectrum Γ(X, U),
      f ∉ v.asIdeal →
        coeff D (h.pointEquiv X U hU v).1 =
          coeff E (h.pointEquiv X U hU v).1) :
    (localLineBundle X U hU h D).obj.restrict
        (_root_.AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom
            (algebraMap Γ(X, U) (Localization.Away f)))) ≅
      (localLineBundle X U hU h E).obj.restrict
        (_root_.AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom
            (algebraMap Γ(X, U) (Localization.Away f)))) := by
  letI := h.isDedekindDomain
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  apply AffineDivisorLocalization.Chain.chosenTildeRestrictIsoOfCoeffEq
  intro v hfv
  rw [localDivisor_coeff X U hU h D v,
    localDivisor_coeff X U hU h E v]
  exact hcoeff v hfv

/-- The chartwise construction carries addition of global divisors to tensor product of the
actual affine line bundles. -/
lemma localLineBundle_add_iso
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
    (h : AffineChart.DedekindOrderCompatibility X U hU)
    (D E : WeilDivisor (CodimensionOnePoint X)) :
    Nonempty
      ((localLineBundle X U hU h (D + E)).obj ≅
        (localLineBundle X U hU h D).obj ⊗
          (localLineBundle X U hU h E).obj) := by
  letI := h.isDedekindDomain
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  rw [localLineBundle, localDivisor_add X U hU h D E]
  exact AffineDedekind.nonempty_lineBundle_add_iso
    Γ(X, U) X.functionField _ _

/-- On every compatible affine chart, the line bundle of a global principal divisor is
isomorphic to the trivial line bundle. -/
lemma localLineBundle_principal_iso_trivial
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
    (h : AffineChart.DedekindOrderCompatibility X U hU)
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (hord : S.ord = SchemeWeilDivisor.orderAt)
    (g : Additive X.functionFieldˣ) :
    Nonempty
      ((localLineBundle X U hU h (S.principalDivisor g)).obj ≅
        (InvertibleSheaf.trivial (Spec (.of Γ(X, U)))).obj) := by
  letI := h.isDedekindDomain
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  rw [localLineBundle, localDivisor_principalDivisor X U hU h S hord g]
  exact AffineDedekind.nonempty_lineBundle_principal_iso_trivial
    Γ(X, U) X.functionField g

/-- The canonical open cover whose members are the coordinate spectra of a covering family of
affine opens. -/
noncomputable def coordinateCover
    {X : Scheme.{u}} {I : Type v} (U : I → X.Opens)
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i)) : X.OpenCover :=
  (Scheme.AffineOpenCover.ofIsOpenCover U hcover hU).openCover

/-- The family of actual affine divisor line bundles on the canonical coordinate cover. -/
noncomputable def localLineBundles
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i : (coordinateCover U hcover hU).I₀) :
    InvertibleSheaf ((coordinateCover U hcover hU).X i) := by
  change InvertibleSheaf (Spec (.of Γ(X, U i)))
  letI := hnonempty i
  exact localLineBundle X (U i) (hU i) (h i) D

/-- The exact overlap-cocycle input for the chartwise divisor line bundles. -/
abbrev DivisorCocycle
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) :=
  LineBundleDescent.LineBundleCocycle
    (coordinateCover U hcover hU)
    (LineBundleDescent.overlap (coordinateCover U hcover hU))
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU))
    (localLineBundles X U hnonempty hcover hU h D)

/-- A coherent divisor cocycle gives locally invertible descent data. -/
noncomputable def invertibleDescentData
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (C : DivisorCocycle X U hnonempty hcover hU h D) :
    LineBundleDescent.InvertibleDescentData (coordinateCover U hcover hU) :=
  C.toInvertibleDescentData

/-- Object-specific effectivity of a divisor cocycle produces a global line bundle. -/
noncomputable def globalLineBundle
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (C : DivisorCocycle X U hnonempty hcover hU h D)
    (heffective : LineBundleDescent.EffectiveInvertible
      (coordinateCover U hcover hU) C.toDescentData) : InvertibleSheaf X :=
  heffective.lineBundle

/-- Cover-wide effective descent supplies the object-specific input for any divisor cocycle. -/
noncomputable def globalLineBundleOfEffectiveDescentFor
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (C : DivisorCocycle X U hnonempty hcover hU h D)
    (heffective : LineBundleDescent.InvertibleEffectiveDescentFor
      (coordinateCover U hcover hU)) : InvertibleSheaf X :=
  globalLineBundle X U hnonempty hcover hU h D C
    (heffective (invertibleDescentData X U hnonempty hcover hU h D C))

/-- Ordinary module effectivity on the coordinate cover is enough to globalize a divisor
cocycle: locality of invertibility is now proved for every scheme open cover. -/
noncomputable def globalLineBundleOfModuleEffectivity
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (C : DivisorCocycle X U hnonempty hcover hU h D)
    (heffective : LineBundleDescent.ModuleEffectiveDescentFor
      (coordinateCover U hcover hU)) : InvertibleSheaf X :=
  globalLineBundleOfEffectiveDescentFor X U hnonempty hcover hU h D C
    (LineBundleDescent.invertibleEffectiveDescentFor_of_moduleEffectivity heffective)

/-- The constructed global line bundle restricts to the actual affine divisor line bundle on
every chart. -/
noncomputable def globalLineBundleRestrictionIso
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (C : DivisorCocycle X U hnonempty hcover hU h D)
    (heffective : LineBundleDescent.EffectiveInvertible
      (coordinateCover U hcover hU) C.toDescentData)
    (i : (coordinateCover U hcover hU).I₀) :
    (Scheme.Modules.pullback ((coordinateCover U hcover hU).f i)).obj
        (globalLineBundle X U hnonempty hcover hU h D C heffective).obj ≅
      (localLineBundles X U hnonempty hcover hU h D i).obj :=
  C.effectiveRestrictionIso heffective i

/-- Coherent triviality of the entire descent cocycle attached to a principal divisor. The
chartwise trivializations above do not by themselves supply this compatibility. -/
noncomputable def PrincipalCocycleTrivial
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (g : Additive X.functionFieldˣ)
    (C : DivisorCocycle X U hnonempty hcover hU h (S.principalDivisor g)) : Prop :=
  Nonempty
    (C.toDescentData ≅
      (LineBundleDescent.modulesPseudofunctor.toDescentData
        (coordinateCover U hcover hU).f).obj (InvertibleSheaf.trivial X).obj)

/-- A coherently trivial principal cocycle descends to the trivial global line bundle as soon as
module descent reflects the trivial object. This is the narrower separation property used here;
comparison of two arbitrary global modules is unnecessary. -/
lemma globalLineBundle_principal_iso_trivial_of_reflectsTriviality
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (g : Additive X.functionFieldˣ)
    (C : DivisorCocycle X U hnonempty hcover hU h (S.principalDivisor g))
    (heffective : LineBundleDescent.EffectiveInvertible
      (coordinateCover U hcover hU) C.toDescentData)
    (hreflect : LineBundleDescent.ModuleDescentReflectsTrivialityFor
      (coordinateCover U hcover hU))
    (htrivial : PrincipalCocycleTrivial X U hnonempty hcover hU h S g C) :
    Nonempty
      ((globalLineBundle X U hnonempty hcover hU h (S.principalDivisor g)
        C heffective).obj ≅ (InvertibleSheaf.trivial X).obj) := by
  change Nonempty (heffective.lineBundle.obj ≅ (InvertibleSheaf.trivial X).obj)
  exact hreflect _ ⟨heffective.descentIso ≪≫ htrivial.some⟩

/-- Full object separation remains a sufficient source of the sharper trivial-object reflection
theorem. -/
lemma globalLineBundle_principal_iso_trivial
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (g : Additive X.functionFieldˣ)
    (C : DivisorCocycle X U hnonempty hcover hU h (S.principalDivisor g))
    (heffective : LineBundleDescent.EffectiveInvertible
      (coordinateCover U hcover hU) C.toDescentData)
    (hinjective : LineBundleDescent.ModuleDescentEssentiallyInjectiveFor
      (coordinateCover U hcover hU))
    (htrivial : PrincipalCocycleTrivial X U hnonempty hcover hU h S g C) :
    Nonempty
      ((globalLineBundle X U hnonempty hcover hU h (S.principalDivisor g)
        C heffective).obj ≅ (InvertibleSheaf.trivial X).obj) :=
  globalLineBundle_principal_iso_trivial_of_reflectsTriviality
    X U hnonempty hcover hU h S g C heffective
    (LineBundleDescent.moduleDescentReflectsTrivialityFor_of_essentiallyInjective hinjective)
    htrivial

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent
