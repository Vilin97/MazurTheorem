/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveAffineChart
import MazurTorsion.Upstream.CurveLineBundleLocality

/-!
# Chartwise divisor line bundles and their descent boundary

This file restricts a global Weil divisor to compatible Dedekind affine charts and constructs
the actual Tau Ceti invertible sheaf `O(D)` on every coordinate spectrum. Restriction preserves
addition, and a global principal divisor gives the affine principal divisor and hence the
trivial local line bundle.

For a covering family of affine opens, `DivisorCocycle` is the exact remaining overlap input:
pairwise isomorphisms between these specific local line bundles, diagonal normalization, and
the triple-overlap cocycle. Given object-specific effective invertible descent, the checked
consumer `globalLineBundle` constructs a global line bundle and identifies every chart
restriction with the affine `O(D)`. Proven locality of invertibility now upgrades ordinary
module effectivity to this input. Coherent triviality of a principal cocycle, together with
essential injectivity on objects for module descent, makes that global line bundle trivial;
fully faithful descent is a checked sufficient source of this exact input. No overlap
isomorphism, module-effectivity theorem, or object-separation theorem is asserted here.
-/

namespace MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

universe u v

open CategoryTheory MonoidalCategory
open TopologicalSpace
open _root_.AlgebraicGeometry
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open IsDedekindDomain

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
