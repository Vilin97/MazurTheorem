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
automatically. Moreover, a chosen common Dedekind affine subopen supplies every
algebra map, open immersion, scalar tower, and map compatibility used by that theorem. Principal
divisors retain a direct rational-function shortcut. The resulting actual isomorphism uses the
chosen affine line-bundle comparisons; no coherence or choice-independence is asserted. On a
separated integral scheme, the full
intersection of two nonempty affine charts is affine and nonempty; a final checked consumer gives
the arbitrary-divisor isomorphism there once its coordinate ring is Dedekind. Properness over a
field supplies the required absolute separatedness automatically, and smooth relative dimension
one supplies the Dedekind condition without a separate normality hypothesis. Transporting these
intersection isomorphisms to the chosen descent pullbacks is now implemented, including a
coordinate-cover consumer whose target is the exact pairwise field of `DivisorCocycle`. The exact
diagonal normalization is proved; base-change compatibility and cover-wide triple-cocycle
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

/-- The two restriction-induced spectrum maps from the coordinate ring of a full affine
intersection exhibit that spectrum as the categorical pullback of the two chart maps. -/
theorem restrictionExtensionMapsIsPullback
    (X : Scheme.{u}) [IsSeparated (terminal.from X)]
    (U₁ U₂ : X.Opens) (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂) :
    letI := restrictionAlgebra X U₁ (U₁ ⊓ U₂) inf_le_left
    letI := restrictionAlgebra X U₂ (U₁ ⊓ U₂) inf_le_right
    IsPullback
      (CommonExtension.extensionMap Γ(X, U₁) Γ(X, U₁ ⊓ U₂))
      (CommonExtension.extensionMap Γ(X, U₂) Γ(X, U₁ ⊓ U₂))
      hU₁.fromSpec hU₂.fromSpec := by
  letI := restrictionAlgebra X U₁ (U₁ ⊓ U₂) inf_le_left
  letI := restrictionAlgebra X U₂ (U₁ ⊓ U₂) inf_le_right
  let hW : IsAffineOpen (U₁ ⊓ U₂) := hU₁.inf hU₂
  refine (isPullback_opens_inf U₁ U₂).of_iso
    hW.isoSpec hU₁.isoSpec hU₂.isoSpec (Iso.refl X) ?_ ?_ ?_ ?_
  · rw [← cancel_mono hU₁.fromSpec]
    simp [restrictionExtensionMap_comp_fromSpec X U₁ (U₁ ⊓ U₂)
      hU₁ hW inf_le_left]
  · rw [← cancel_mono hU₂.fromSpec]
    simp [restrictionExtensionMap_comp_fromSpec X U₂ (U₁ ⊓ U₂)
      hU₂ hW inf_le_right]
  · simp
  · simp

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

/-- Every chosen common Dedekind affine subopen of two compatible charts supplies the actual
arbitrary-divisor restriction isomorphism on that subopen. All algebra maps, open
immersions, common-function-field towers, and ambient-map compatibilities are derived from
presheaf restriction; coherence of the resulting chosen isomorphisms is not asserted. -/
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

/-- The chosen common-affine comparison of a chart with itself is the identity when both
occurrences use the same restriction map and the same affine line-bundle comparison. -/
lemma localLineBundleRestrictionIsoOnCommonAffineOpen_self
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (U W : X.Opens) [Nonempty U] [Nonempty W]
    (hU : IsAffineOpen U) (hW : IsAffineOpen W) (hWU : W ≤ U)
    (h : AffineChart.DedekindOrderCompatibility X U hU)
    [IsDedekindDomain Γ(X, U)] [IsDedekindDomain Γ(X, W)]
    (D : WeilDivisor (CodimensionOnePoint X)) :
    letI := restrictionAlgebra X U W hWU
    letI : IsOpenImmersion
        (CommonExtension.extensionMap Γ(X, U) Γ(X, W)) :=
      restrictionExtensionMapIsOpenImmersion X U W hU hW hWU
    localLineBundleRestrictionIsoOnCommonAffineOpen
      X U U W hU hU hW hWU hWU h h D = Iso.refl _ := by
  letI := restrictionAlgebra X U W hWU
  letI : Module.IsTorsionFree Γ(X, U) Γ(X, W) :=
    restrictionTorsionFree X U W hWU
  letI : IsOpenImmersion
      (CommonExtension.extensionMap Γ(X, U) Γ(X, W)) :=
    restrictionExtensionMapIsOpenImmersion X U W hU hW hWU
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  letI : IsFractionRing Γ(X, W) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X W hW
  letI : IsScalarTower Γ(X, U) Γ(X, W) X.functionField :=
    restrictionFunctionFieldTower X U W hWU
  unfold localLineBundleRestrictionIsoOnCommonAffineOpen
  unfold localLineBundleRestrictionIsoOfCommonMap
  apply CommonExtension.chosenLineBundleRestrictionIso_diagonal_of_same_comparison
  exact CommonExtension.restrictionIdentifiesExtendedInverseIdeal_of_isOpenImmersion
    Γ(X, U) Γ(X, W) X.functionField (localDivisor X U hU h D)

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

/-- On the full self-intersection of one affine chart, the untransported restriction
comparison is the identity. -/
lemma localLineBundleRestrictionIsoOnIntersection_self
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    [IsSeparated (terminal.from X)]
    (U : X.Opens) [Nonempty U]
    (hU : IsAffineOpen U)
    (h : AffineChart.DedekindOrderCompatibility X U hU)
    [IsDedekindDomain Γ(X, U)] [IsDedekindDomain Γ(X, U ⊓ U)]
    (D : WeilDivisor (CodimensionOnePoint X)) :
    letI := restrictionAlgebra X U (U ⊓ U) inf_le_left
    letI := restrictionAlgebra X U (U ⊓ U) inf_le_right
    letI : IsOpenImmersion
        (CommonExtension.extensionMap Γ(X, U) Γ(X, U ⊓ U)) :=
      restrictionExtensionMapIsOpenImmersion X U (U ⊓ U)
        hU (hU.inf hU) inf_le_left
    localLineBundleRestrictionIsoOnIntersection X U U hU hU h h D = Iso.refl _ := by
  letI : Nonempty ↑(U ⊓ U : X.Opens) := nonempty_inf_of_isIntegral X U U
  unfold localLineBundleRestrictionIsoOnIntersection
  apply localLineBundleRestrictionIsoOnCommonAffineOpen_self

/-- Transport the full-intersection comparison to the standard categorical pullback used by
module descent. This constructs the exact pairwise overlap isomorphism field of a divisor
cocycle; normalization and the triple cocycle remain separate. -/
noncomputable def localLineBundlePullbackIsoOnIntersection
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    [IsSeparated (terminal.from X)]
    (U₁ U₂ : X.Opens) [Nonempty U₁] [Nonempty U₂]
    (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂)
    (h₁ : AffineChart.DedekindOrderCompatibility X U₁ hU₁)
    (h₂ : AffineChart.DedekindOrderCompatibility X U₂ hU₂)
    [IsDedekindDomain Γ(X, U₁)] [IsDedekindDomain Γ(X, U₂)]
    [IsDedekindDomain Γ(X, U₁ ⊓ U₂)]
    (D : WeilDivisor (CodimensionOnePoint X)) :
    (Scheme.Modules.pullback (pullback.fst hU₁.fromSpec hU₂.fromSpec)).obj
        (localLineBundle X U₁ hU₁ h₁ D).obj ≅
      (Scheme.Modules.pullback (pullback.snd hU₁.fromSpec hU₂.fromSpec)).obj
        (localLineBundle X U₂ hU₂ h₂ D).obj := by
  letI : Nonempty ↑(U₁ ⊓ U₂ : X.Opens) := nonempty_inf_of_isIntegral X U₁ U₂
  letI := restrictionAlgebra X U₁ (U₁ ⊓ U₂) inf_le_left
  letI := restrictionAlgebra X U₂ (U₁ ⊓ U₂) inf_le_right
  let j₁ := CommonExtension.extensionMap Γ(X, U₁) Γ(X, U₁ ⊓ U₂)
  let j₂ := CommonExtension.extensionMap Γ(X, U₂) Γ(X, U₁ ⊓ U₂)
  letI : IsOpenImmersion j₁ :=
    restrictionExtensionMapIsOpenImmersion X U₁ (U₁ ⊓ U₂)
      hU₁ (hU₁.inf hU₂) inf_le_left
  letI : IsOpenImmersion j₂ :=
    restrictionExtensionMapIsOpenImmersion X U₂ (U₁ ⊓ U₂)
      hU₂ (hU₁.inf hU₂) inf_le_right
  let H : IsPullback j₁ j₂ hU₁.fromSpec hU₂.fromSpec :=
    restrictionExtensionMapsIsPullback X U₁ U₂ hU₁ hU₂
  let e := H.isoPullback
  let α := localLineBundleRestrictionIsoOnIntersection
    X U₁ U₂ hU₁ hU₂ h₁ h₂ D
  let β :
      (Scheme.Modules.pullback j₁).obj (localLineBundle X U₁ hU₁ h₁ D).obj ≅
        (Scheme.Modules.pullback j₂).obj (localLineBundle X U₂ hU₂ h₂ D).obj :=
    ((Scheme.Modules.restrictFunctorIsoPullback j₁).app
        (localLineBundle X U₁ hU₁ h₁ D).obj).symm ≪≫
      α ≪≫
        ((Scheme.Modules.restrictFunctorIsoPullback j₂).app
          (localLineBundle X U₂ hU₂ h₂ D).obj)
  exact
    (((Scheme.Modules.pullbackComp e.inv j₁).app
          (localLineBundle X U₁ hU₁ h₁ D).obj ≪≫
        (Scheme.Modules.pullbackCongr H.isoPullback_inv_fst).app
          (localLineBundle X U₁ hU₁ h₁ D).obj).symm) ≪≫
      (Scheme.Modules.pullback e.inv).mapIso β ≪≫
      ((Scheme.Modules.pullbackComp e.inv j₂).app
          (localLineBundle X U₂ hU₂ h₂ D).obj ≪≫
        (Scheme.Modules.pullbackCongr H.isoPullback_inv_snd).app
          (localLineBundle X U₂ hU₂ h₂ D).obj)

private lemma pullHom_eqToHom_of_eq
    {C : Type u} [Category C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat)
    {P Y : C} (a b : P ⟶ Y) (hab : a = b) (d : Y ⟶ P)
    (ha : d ≫ a = 𝟙 Y) (hb : d ≫ b = 𝟙 Y)
    (M : F.obj (.mk (Opposite.op Y))) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := F) (M₁ := M) (M₂ := M)
      (eqToHom (by subst b; rfl)) d (𝟙 Y) (𝟙 Y) ha hb = 𝟙 _ := by
  subst b
  unfold Pseudofunctor.LocallyDiscreteOpToCat.pullHom
  simp

private lemma pullHom_pullbackCongr_of_eq
    {P Y : Scheme.{u}} (a b : P ⟶ Y) (hab : a = b) (d : Y ⟶ P)
    (ha : d ≫ a = 𝟙 Y) (hb : d ≫ b = 𝟙 Y) (M : Y.Modules) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := LineBundleDescent.modulesPseudofunctor) (M₁ := M) (M₂ := M)
      ((Scheme.Modules.pullbackCongr hab).app M).hom d (𝟙 Y) (𝟙 Y) ha hb = 𝟙 _ := by
  have hφ : ((Scheme.Modules.pullbackCongr hab).app M).hom =
      (eqToHom (by subst b; rfl) :
        (Scheme.Modules.pullback a).obj M ⟶
          (Scheme.Modules.pullback b).obj M) := by
    subst b
    rfl
  rw [hφ]
  exact pullHom_eqToHom_of_eq
    LineBundleDescent.modulesPseudofunctor a b hab d ha hb M

private lemma pullHom'_pullbackCongr_diagonal
    {Y S : Scheme.{u}} (f : Y ⟶ S) [Mono f] (M : Y.Modules) :
    let sq := LineBundleDescent.ChosenOverlaps.chosenPullback f f
    let hp : sq.p₁ = sq.p₂ := by
      rw [← cancel_mono f]
      exact sq.condition
    Pseudofunctor.DescentData'.pullHom'
        (F := LineBundleDescent.modulesPseudofunctor)
        (f := fun _ : Unit ↦ f)
        (sq := fun _ _ : Unit ↦ sq)
        (i₁ := ()) (i₂ := ())
        (fun _ _ ↦ ((Scheme.Modules.pullbackCongr hp).app M).hom)
        f (𝟙 _) (𝟙 _) = 𝟙 _ := by
  dsimp only
  unfold Pseudofunctor.DescentData'.pullHom'
  unfold LineBundleDescent.ChosenOverlaps.chosenPullback
  unfold Pseudofunctor.LocallyDiscreteOpToCat.pullHom
  apply pullHom_pullbackCongr_of_eq
  <;> simp

/-- On a self-intersection, the transported divisor comparison is the canonical comparison
between pullbacks along the two equal projections. -/
lemma localLineBundlePullbackIsoOnIntersection_self
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    [IsSeparated (terminal.from X)]
    (U : X.Opens) [Nonempty U]
    (hU : IsAffineOpen U)
    (h : AffineChart.DedekindOrderCompatibility X U hU)
    [IsDedekindDomain Γ(X, U)] [IsDedekindDomain Γ(X, U ⊓ U)]
    (D : WeilDivisor (CodimensionOnePoint X)) :
    let hp : pullback.fst hU.fromSpec hU.fromSpec =
        pullback.snd hU.fromSpec hU.fromSpec := by
      rw [← cancel_mono hU.fromSpec]
      exact pullback.condition
    localLineBundlePullbackIsoOnIntersection X U U hU hU h h D =
      (Scheme.Modules.pullbackCongr hp).app (localLineBundle X U hU h D).obj := by
  dsimp only
  unfold localLineBundlePullbackIsoOnIntersection
  rw [localLineBundleRestrictionIsoOnIntersection_self]
  simp only [Functor.comp_obj, Iso.trans_symm, Iso.refl_trans, Iso.symm_self_id,
    Functor.mapIso_refl, Iso.trans_assoc, Iso.symm_self_id_assoc]
  apply Iso.ext
  simp [Scheme.Modules.pullbackCongr, eqToHom_trans]

/-- Pulling the transported self-overlap comparison back along the diagonal gives the
identity. This is the single-chart form of divisor-cocycle normalization. -/
lemma localLineBundlePullbackIsoOnIntersection_normalization
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    [IsSeparated (terminal.from X)]
    (U : X.Opens) [Nonempty U]
    (hU : IsAffineOpen U)
    (h : AffineChart.DedekindOrderCompatibility X U hU)
    [IsDedekindDomain Γ(X, U)] [IsDedekindDomain Γ(X, U ⊓ U)]
    (D : WeilDivisor (CodimensionOnePoint X)) :
    Pseudofunctor.DescentData'.pullHom'
        (F := LineBundleDescent.modulesPseudofunctor)
        (f := fun _ : Unit ↦ hU.fromSpec)
        (sq := fun _ _ : Unit ↦
          LineBundleDescent.ChosenOverlaps.chosenPullback hU.fromSpec hU.fromSpec)
        (i₁ := ()) (i₂ := ())
        (fun _ _ ↦
          (localLineBundlePullbackIsoOnIntersection X U U hU hU h h D).hom)
        hU.fromSpec (𝟙 _) (𝟙 _) = 𝟙 _ := by
  rw [localLineBundlePullbackIsoOnIntersection_self]
  apply pullHom'_pullbackCongr_diagonal

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

/-- On a proper smooth relative curve, smoothness supplies the Dedekind-domain instance on the
full affine intersection and hence the actual overlap isomorphism, with no extra normality
hypothesis. -/
noncomputable def localLineBundleRestrictionIsoOnProperSmoothCurveIntersection
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (U₁ U₂ : X.Opens) [Nonempty U₁] [Nonempty U₂]
    (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂)
    (h₁ : AffineChart.DedekindOrderCompatibility X U₁ hU₁)
    (h₂ : AffineChart.DedekindOrderCompatibility X U₂ hU₂)
    [IsDedekindDomain Γ(X, U₁)] [IsDedekindDomain Γ(X, U₂)]
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
  let hcompat := AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve
    K X f (U₁ ⊓ U₂) hW
  letI : IsDedekindDomain Γ(X, U₁ ⊓ U₂) := hcompat.isDedekindDomain
  exact localLineBundleRestrictionIsoOnProperCurveIntersection
    K X f U₁ U₂ hU₁ hU₂ h₁ h₂ D

/-- Compatibility wrapper for the former mapwise-normality entry point. Smoothness now proves
that hypothesis internally; new code should use
`localLineBundleRestrictionIsoOnProperSmoothCurveIntersection`. -/
noncomputable def localLineBundleRestrictionIsoOnProperSmoothCurveIntersectionOfNormality
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (U₁ U₂ : X.Opens) [Nonempty U₁] [Nonempty U₂]
    (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂)
    (h₁ : AffineChart.DedekindOrderCompatibility X U₁ hU₁)
    (h₂ : AffineChart.DedekindOrderCompatibility X U₂ hU₂)
    [IsDedekindDomain Γ(X, U₁)] [IsDedekindDomain Γ(X, U₂)]
    (_hnormal : RingHom.Locally
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
        (CommonExtension.extensionMap Γ(X, U₂) Γ(X, U₁ ⊓ U₂)) :=
  localLineBundleRestrictionIsoOnProperSmoothCurveIntersection
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

/-- The full-intersection comparison, transported to the exact standard chosen pullback used by
the coordinate-cover descent package. This discharges the pairwise isomorphism field of
`DivisorCocycle` under Dedekind hypotheses on all pairwise intersections. -/
noncomputable def coordinateDivisorOverlapIso
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    [IsSeparated (terminal.from X)]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (hinter : ∀ i j, IsDedekindDomain Γ(X, U i ⊓ U j))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i j : (coordinateCover U hcover hU).I₀) :
    (Scheme.Modules.pullback
        (LineBundleDescent.overlap (coordinateCover U hcover hU) i j).p₁).obj
        (localLineBundles X U hnonempty hcover hU h D i).obj ≅
      (Scheme.Modules.pullback
        (LineBundleDescent.overlap (coordinateCover U hcover hU) i j).p₂).obj
        (localLineBundles X U hnonempty hcover hU h D j).obj := by
  letI := hnonempty i
  letI := hnonempty j
  letI : IsDedekindDomain Γ(X, U i) := (h i).isDedekindDomain
  letI : IsDedekindDomain Γ(X, U j) := (h j).isDedekindDomain
  letI : IsDedekindDomain Γ(X, U i ⊓ U j) := hinter i j
  change
    (Scheme.Modules.pullback (pullback.fst (hU i).fromSpec (hU j).fromSpec)).obj
        (localLineBundle X (U i) (hU i) (h i) D).obj ≅
      (Scheme.Modules.pullback (pullback.snd (hU i).fromSpec (hU j).fromSpec)).obj
        (localLineBundle X (U j) (hU j) (h j) D).obj
  exact localLineBundlePullbackIsoOnIntersection
    X (U i) (U j) (hU i) (hU j) (h i) (h j) D

/-- The coordinate-cover self-overlap comparison is the canonical comparison between the two
equal pullback projections. -/
lemma coordinateDivisorOverlapIso_self
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    [IsSeparated (terminal.from X)]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (hinter : ∀ i j, IsDedekindDomain Γ(X, U i ⊓ U j))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i : (coordinateCover U hcover hU).I₀) :
    let sq := LineBundleDescent.overlap (coordinateCover U hcover hU) i i
    let hp : sq.p₁ = sq.p₂ := by
      rw [← cancel_mono ((coordinateCover U hcover hU).f i)]
      exact sq.condition
    coordinateDivisorOverlapIso
        X U hnonempty hcover hU h hinter D i i =
      (Scheme.Modules.pullbackCongr hp).app
        (localLineBundles X U hnonempty hcover hU h D i).obj := by
  letI := hnonempty i
  letI : IsDedekindDomain Γ(X, U i) := (h i).isDedekindDomain
  letI : IsDedekindDomain Γ(X, U i ⊓ U i) := hinter i i
  dsimp only
  unfold coordinateDivisorOverlapIso
  exact localLineBundlePullbackIsoOnIntersection_self
    X (U i) (hU i) (h i) D

/-- The transported divisor overlap isomorphisms satisfy the diagonal normalization required
by `LineBundleCocycle`. -/
lemma coordinateDivisorOverlapIso_normalization
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    [IsSeparated (terminal.from X)]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (hinter : ∀ i j, IsDedekindDomain Γ(X, U i ⊓ U j))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i : (coordinateCover U hcover hU).I₀) :
    Pseudofunctor.DescentData'.pullHom'
        (F := LineBundleDescent.modulesPseudofunctor)
        (sq := LineBundleDescent.overlap (coordinateCover U hcover hU))
        (fun i j ↦
          (coordinateDivisorOverlapIso
            X U hnonempty hcover hU h hinter D i j).hom)
        ((coordinateCover U hcover hU).f i) (𝟙 _) (𝟙 _) = 𝟙 _ := by
  letI := hnonempty i
  letI : IsDedekindDomain Γ(X, U i) := (h i).isDedekindDomain
  letI : IsDedekindDomain Γ(X, U i ⊓ U i) := hinter i i
  unfold Pseudofunctor.DescentData'.pullHom'
  dsimp only
  rw [coordinateDivisorOverlapIso_self]
  unfold Pseudofunctor.LocallyDiscreteOpToCat.pullHom
  apply pullHom_pullbackCongr_of_eq
  <;> simp

/-- On a proper smooth relative curve, smoothness supplies the exact chosen-pullback overlap
isomorphisms for every pair of charts in the coordinate cover, with no extra normality
hypothesis. -/
noncomputable def coordinateDivisorOverlapIsoOnProperSmoothCurve
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i j : (coordinateCover U hcover hU).I₀) :
    (Scheme.Modules.pullback
        (LineBundleDescent.overlap (coordinateCover U hcover hU) i j).p₁).obj
        (localLineBundles X U hnonempty hcover hU h D i).obj ≅
      (Scheme.Modules.pullback
        (LineBundleDescent.overlap (coordinateCover U hcover hU) i j).p₂).obj
        (localLineBundles X U hnonempty hcover hU h D j).obj := by
  letI : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  let hinter : ∀ i j, IsDedekindDomain Γ(X, U i ⊓ U j) := fun i j ↦ by
    letI := hnonempty i
    letI := hnonempty j
    letI : Nonempty ↑(U i ⊓ U j : X.Opens) :=
      nonempty_inf_of_isIntegral X (U i) (U j)
    let hW : IsAffineOpen (U i ⊓ U j) := (hU i).inf (hU j)
    exact (AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve
      K X f (U i ⊓ U j) hW).isDedekindDomain
  exact coordinateDivisorOverlapIso X U hnonempty hcover hU h hinter D i j

/-- Compatibility wrapper for the former cover-wide mapwise-normality entry point. -/
noncomputable def coordinateDivisorOverlapIsoOnProperSmoothCurveOfNormality
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (_hnormal : ∀ i j, RingHom.Locally
      (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (f.appLE ⊤ (U i ⊓ U j) le_top).hom →
        IsIntegrallyClosed Γ(X, U i ⊓ U j))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i j : (coordinateCover U hcover hU).I₀) :
    (Scheme.Modules.pullback
        (LineBundleDescent.overlap (coordinateCover U hcover hU) i j).p₁).obj
        (localLineBundles X U hnonempty hcover hU h D i).obj ≅
      (Scheme.Modules.pullback
        (LineBundleDescent.overlap (coordinateCover U hcover hU) i j).p₂).obj
        (localLineBundles X U hnonempty hcover hU h D j).obj :=
  coordinateDivisorOverlapIsoOnProperSmoothCurve
    K X f U hnonempty hcover hU h D i j

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

/-- A coherently trivial principal cocycle descends to the trivial global line bundle when
module descent is fully faithful on the cover. -/
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
        C heffective).obj ≅ (InvertibleSheaf.trivial X).obj) := by
  change Nonempty (heffective.lineBundle.obj ≅ (InvertibleSheaf.trivial X).obj)
  exact hinjective _ _ ⟨heffective.descentIso ≪≫ htrivial.some⟩

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent
