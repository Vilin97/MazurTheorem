/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveDivisorDescent

/-!
# Divisor-indexed descent into the Picard group

This file packages the exact coherence needed to turn the chartwise divisor line bundles from
`CurveDivisorDescent` into a divisor-to-Picard homomorphism. A cocycle is chosen for every Weil
divisor, every cocycle is effectively descended, and the resulting global line bundles are
tensor-additive up to isomorphism. The actual normalized cocycle reconstructed for a principal
divisor is unconditionally effective, with the trivial global line bundle as its witness;
arbitrary-divisor effectivity remains an input. Given the forward `TensorInverseComparison X`,
these bundles define elements of the scheme Picard group. More sharply, the `ExplicitInverse`
namespace avoids that global comparison: once the zero-divisor bundle is trivial, tensor
additivity makes the bundle of `-D` an explicit inverse to the bundle of `D`. Since Picard
classes live in the skeleton, no higher tensor coherence is needed.

If every principal cocycle is coherently trivial and module descent separates global objects,
the homomorphism kills principal divisors and therefore descends to divisor classes. With the
additional geometric assertion that only principal divisors have globally trivial descended line
bundle, the principal kernel is exact; checked code also proves the converse. This exactness and
surjectivity supply the full divisor-class/Picard equivalence without comparing unrelated
invertible sheaves. The more structured `DivisorPicard.Dictionary` still records the global
forward comparison and remains conditional on it. This file does not assert existence of the
arbitrary-divisor cocycle family, its effectivity, tensor-additivity, zero or principal coherence
for that family, object separation,
principal detection, exactness, surjectivity, or the global forward comparison. A global
trivialization is proved to make the divisor principal on each chart. Under equality of the
chosen global and scheme orders, the witness-level statement that one rational function gives
all chart restrictions is proved equivalent to principal detection; it is not a separate gluing
input. Constructing compatible rational data from the explicit line-bundle cocycle remains
absent.
-/

namespace MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

universe u v

open CategoryTheory MonoidalCategory
open TopologicalSpace
open _root_.AlgebraicGeometry
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor

/-- The standard monoidal structure on sheaves of modules over a scheme. -/
noncomputable local instance schemeModulesMonoidalForPicardDescent (Y : Scheme.{u}) :
    MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y

/-- The standard symmetry on tensor products of sheaves of modules over a scheme. -/
noncomputable local instance schemeModulesSymmetricForPicardDescent (Y : Scheme.{u}) :
    SymmetricCategory Y.Modules :=
  Scheme.Modules.symmetricCategory Y

/-- The coherent principal-divisor datum delivered to the divisor-to-Picard boundary. It is the
actual full descent datum reconstructed from the normalized principal-divisor cocycle. -/
noncomputable def principalPicardBoundaryDatum
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (hord : S.ord = SchemeWeilDivisor.orderAt)
    (g : Additive X.functionFieldˣ) :
    LineBundleDescent.InvertibleDescentData (coordinateCover U hcover hU) :=
  principalDivisorInvertibleDescentData
    X U hnonempty hcover hU h S hord g

@[simp]
lemma principalPicardBoundaryDatum_toDescentData
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (hord : S.ord = SchemeWeilDivisor.orderAt)
    (g : Additive X.functionFieldˣ) :
    (principalPicardBoundaryDatum
      X U hnonempty hcover hU h S hord g).toDescentData =
      principalDivisorDescentData X U hnonempty hcover hU h S hord g :=
  rfl

/-- The Picard-boundary principal datum is effectively represented by the global trivial line
bundle. This is the checked downstream consumer of the chosen-overlap/full-descent comparison
for the actual normalized divisor cocycle. -/
theorem principalPicardBoundaryDatum_effective
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (hord : S.ord = SchemeWeilDivisor.orderAt)
    (g : Additive X.functionFieldˣ) :
    LineBundleDescent.EffectiveInvertible (coordinateCover U hcover hU)
      (principalPicardBoundaryDatum
        X U hnonempty hcover hU h S hord g).toDescentData :=
  principalDivisorCocycleEffectiveInvertible
    X U hnonempty hcover hU h S hord g

/-- A chosen coherent chart cocycle for every Weil divisor. This family does not by itself
assert compatibility with divisor addition or principal divisors. -/
abbrev DivisorCocycleSystem
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i)) :=
  ∀ D : WeilDivisor (CodimensionOnePoint X),
    DivisorCocycle X U hnonempty hcover hU h D

/-- Objectwise effectivity of a divisor-indexed cocycle system. This is weaker than effective
descent for every locally invertible module datum on the cover. -/
def EffectiveDivisorCocycleSystem
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h) : Prop :=
  ∀ D, LineBundleDescent.EffectiveInvertible
    (coordinateCover U hcover hU) (C D).toDescentData

/-- The global line bundle attached to a divisor by an effective divisor cocycle system. -/
noncomputable def descendedLineBundle
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (D : WeilDivisor (CodimensionOnePoint X)) : InvertibleSheaf X :=
  globalLineBundle X U hnonempty hcover hU h D (C D) (heffective D)

/-- Every descended line bundle restricts to the specified affine divisor line bundle on each
member of the coordinate cover. -/
noncomputable def descendedLineBundleRestrictionIso
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (D : WeilDivisor (CodimensionOnePoint X))
    (i : (coordinateCover U hcover hU).I₀) :
    (Scheme.Modules.pullback ((coordinateCover U hcover hU).f i)).obj
        (descendedLineBundle X U hnonempty hcover hU h C heffective D).obj ≅
      (localLineBundles X U hnonempty hcover hU h D i).obj :=
  globalLineBundleRestrictionIso X U hnonempty hcover hU h D
    (C D) (heffective D) i

/-- The descended line bundle of the zero divisor is globally trivial. This is the minimal
unit input needed, together with tensor additivity, to construct Picard classes for all
divisor-generated bundles: the bundle of `-D` then gives an explicit tensor inverse to the
bundle of `D`. -/
def DescendedZeroTrivial
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C) : Prop :=
  Nonempty
    ((descendedLineBundle X U hnonempty hcover hU h C heffective 0).obj ≅
      (InvertibleSheaf.trivial X).obj)

/-- The exact additive compatibility needed after descent: the line bundle of `D + E` is
isomorphic to the tensor product of the line bundles of `D` and `E`. No chosen associativity or
unit coherence is needed after passing to Picard classes. -/
def DescendedTensorAdditive
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C) : Prop :=
  ∀ D E, Nonempty
    ((descendedLineBundle X U hnonempty hcover hU h C heffective (D + E)).obj ≅
      (descendedLineBundle X U hnonempty hcover hU h C heffective D).obj ⊗
        (descendedLineBundle X U hnonempty hcover hU h C heffective E).obj)

/-- Coherent triviality, as descent data, of every principal member of a divisor cocycle
system. Chartwise triviality alone does not supply these compatible isomorphisms. -/
def PrincipalCocycleSystemTrivial
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h) : Prop :=
  ∀ g, PrincipalCocycleTrivial X U hnonempty hcover hU h S g
    (C (S.principalDivisor g))

/-- The global consequence of coherent principal cocycles that the Picard construction actually
uses: every descended principal-divisor line bundle is trivial. This boundary deliberately omits
descent-data coherence and separation for unrelated global modules. -/
def DescendedPrincipalTrivial
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C) : Prop :=
  ∀ g, Nonempty
    ((descendedLineBundle X U hnonempty hcover hU h C heffective
      (S.principalDivisor g)).obj ≅ (InvertibleSheaf.trivial X).obj)

namespace DivisorCocycleSystem

/-- Coherent principal cocycles plus reflection of the trivial descent object imply exactly the
global principal triviality needed by the Picard map. -/
theorem descendedPrincipalTrivial_of_principalCocycleSystem
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hreflect : LineBundleDescent.ModuleDescentReflectsTrivialityFor
      (coordinateCover U hcover hU))
    (hprincipal : PrincipalCocycleSystemTrivial X U hnonempty hcover hU h S C) :
    DescendedPrincipalTrivial X U hnonempty hcover hU h S C heffective :=
  fun g ↦ globalLineBundle_principal_iso_trivial_of_reflectsTriviality
    X U hnonempty hcover hU h S g (C (S.principalDivisor g))
    (heffective (S.principalDivisor g)) hreflect (hprincipal g)

/-- Coherent triviality of the principal cocycles and object separation for module descent make
every descended principal-divisor line bundle globally trivial. -/
lemma descendedLineBundle_principal_iso_trivial
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hinjective : LineBundleDescent.ModuleDescentEssentiallyInjectiveFor
      (coordinateCover U hcover hU))
    (hprincipal : PrincipalCocycleSystemTrivial X U hnonempty hcover hU h S C)
    (g : Additive X.functionFieldˣ) :
    Nonempty
      ((descendedLineBundle X U hnonempty hcover hU h C heffective
        (S.principalDivisor g)).obj ≅ (InvertibleSheaf.trivial X).obj) :=
  globalLineBundle_principal_iso_trivial X U hnonempty hcover hU h S g
    (C (S.principalDivisor g)) (heffective (S.principalDivisor g))
    hinjective (hprincipal g)

/-- Coherent principal triviality supplies the minimal zero-bundle trivialization used by the
explicit-inverse Picard construction. It is enough to specialize the principal cocycle at the
unit rational function. -/
theorem descendedZeroTrivial_of_principalCocycleSystem
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hinjective : LineBundleDescent.ModuleDescentEssentiallyInjectiveFor
      (coordinateCover U hcover hU))
    (hprincipal : PrincipalCocycleSystemTrivial X U hnonempty hcover hU h S C) :
    DescendedZeroTrivial X U hnonempty hcover hU h C heffective := by
  change Nonempty
    ((descendedLineBundle X U hnonempty hcover hU h C heffective 0).obj ≅
      (InvertibleSheaf.trivial X).obj)
  simpa using descendedLineBundle_principal_iso_trivial X U hnonempty hcover hU h S C
    heffective hinjective hprincipal (Additive.ofMul (1 : X.functionFieldˣ))

/-- Global triviality of principal-divisor bundles already includes the zero-bundle
trivialization. Thus `DescendedZeroTrivial` is not an independent hypothesis in the exact
principal-boundary API. -/
theorem descendedZeroTrivial_of_descendedPrincipalTrivial
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hprincipal : DescendedPrincipalTrivial
      X U hnonempty hcover hU h S C heffective) :
    DescendedZeroTrivial X U hnonempty hcover hU h C heffective := by
  change Nonempty
    ((descendedLineBundle X U hnonempty hcover hU h C heffective 0).obj ≅
      (InvertibleSheaf.trivial X).obj)
  have hp := hprincipal (Additive.ofMul (1 : X.functionFieldˣ))
  rw [show Additive.ofMul (1 : X.functionFieldˣ) = 0 by rfl,
    S.principalDivisor_zero] at hp
  exact hp

namespace ExplicitInverse

/-- Tensor additivity and triviality at zero exhibit the bundle of `-D` as a tensor inverse to
the descended bundle of `D`. This construction is divisor-specific and therefore requires no
global `TensorInverseComparison X` for arbitrary invertible sheaves. -/
noncomputable def descendedTensorInverseIso
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hadd : DescendedTensorAdditive X U hnonempty hcover hU h C heffective)
    (hzero : DescendedZeroTrivial X U hnonempty hcover hU h C heffective)
    (D : WeilDivisor (CodimensionOnePoint X)) :
    (descendedLineBundle X U hnonempty hcover hU h C heffective D).obj ⊗
        (descendedLineBundle X U hnonempty hcover hU h C heffective (-D)).obj ≅
      𝟙_ X.Modules :=
  (hadd D (-D)).some.symm ≪≫ (by simpa using hzero.some) ≪≫
    TensorInverseComparison.trivialIsoTensorUnit

/-- The Picard unit represented by the descended divisor line bundle, using the line bundle of
the negative divisor as an explicit inverse. -/
noncomputable def divisorPicClass
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hadd : DescendedTensorAdditive X U hnonempty hcover hU h C heffective)
    (hzero : DescendedZeroTrivial X U hnonempty hcover hU h C heffective)
    (D : WeilDivisor (CodimensionOnePoint X)) : Scheme.Pic X := by
  let L := (descendedLineBundle X U hnonempty hcover hU h C heffective D).obj
  let N := (descendedLineBundle X U hnonempty hcover hU h C heffective (-D)).obj
  let e : L ⊗ N ≅ 𝟙_ X.Modules :=
    descendedTensorInverseIso X U hnonempty hcover hU h C heffective hadd hzero D
  exact (isUnit_of_dvd_one ⟨toSkeleton N, by
    rw [← Skeleton.toSkeleton_tensorObj, Skeleton.one_eq]
    exact Quotient.sound ⟨e.symm⟩⟩).unit

/-- The explicit divisor Picard class has the descended line bundle as its underlying skeleton
object. -/
@[simp]
lemma divisorPicClass_val
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hadd : DescendedTensorAdditive X U hnonempty hcover hU h C heffective)
    (hzero : DescendedZeroTrivial X U hnonempty hcover hU h C heffective)
    (D : WeilDivisor (CodimensionOnePoint X)) :
    (divisorPicClass X U hnonempty hcover hU h C heffective hadd hzero D).val =
      toSkeleton (descendedLineBundle X U hnonempty hcover hU h C heffective D).obj :=
  IsUnit.unit_spec _

/-- Tensor-additive descended bundles whose zero member is trivial define an additive map from
Weil divisors to the scheme Picard group. The inverse of the class of `D` is represented
explicitly by the descended bundle of `-D`; no comparison for arbitrary invertible sheaves is
needed. -/
noncomputable def divisorToPic
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hadd : DescendedTensorAdditive X U hnonempty hcover hU h C heffective)
    (hzero : DescendedZeroTrivial X U hnonempty hcover hU h C heffective) :
    WeilDivisor (CodimensionOnePoint X) →+ PicardGroup X where
  toFun D := Additive.ofMul
    (divisorPicClass X U hnonempty hcover hU h C heffective hadd hzero D)
  map_zero' := by
    change divisorPicClass X U hnonempty hcover hU h C heffective hadd hzero 0 = 1
    apply Units.ext
    rw [divisorPicClass_val]
    change toSkeleton
        (descendedLineBundle X U hnonempty hcover hU h C heffective 0).obj =
      toSkeleton (𝟙_ X.Modules)
    exact Quotient.sound ⟨hzero.some ≪≫ TensorInverseComparison.trivialIsoTensorUnit⟩
  map_add' D E := by
    change divisorPicClass X U hnonempty hcover hU h C heffective hadd hzero (D + E) =
      divisorPicClass X U hnonempty hcover hU h C heffective hadd hzero D *
        divisorPicClass X U hnonempty hcover hU h C heffective hadd hzero E
    apply Units.ext
    change
      (divisorPicClass X U hnonempty hcover hU h C heffective hadd hzero (D + E)).val =
        (divisorPicClass X U hnonempty hcover hU h C heffective hadd hzero D).val *
          (divisorPicClass X U hnonempty hcover hU h C heffective hadd hzero E).val
    rw [divisorPicClass_val, divisorPicClass_val, divisorPicClass_val,
      ← Skeleton.toSkeleton_tensorObj]
    exact Quotient.sound ⟨(hadd D E).some⟩

/-- Whenever a comparison for every invertible sheaf is available, the explicit
divisor-generated Picard class agrees with it. The comparison is compatibility data here, not
an input to the construction. -/
lemma divisorPicClass_eq_toPic
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hadd : DescendedTensorAdditive X U hnonempty hcover hU h C heffective)
    (hzero : DescendedZeroTrivial X U hnonempty hcover hU h C heffective)
    (hX : TensorInverseComparison X)
    (D : WeilDivisor (CodimensionOnePoint X)) :
    divisorPicClass X U hnonempty hcover hU h C heffective hadd hzero D =
      hX.toPic (descendedLineBundle X U hnonempty hcover hU h C heffective D) := by
  apply Units.ext
  rw [divisorPicClass_val, hX.toPic_val]

/-- The geometric injectivity boundary for descended divisor line bundles: if the line bundle
of `D` is globally trivial, then `D` belongs to the principal subgroup. Together with coherent
principal triviality and object separation, this is exactly the principal-kernel condition for
the resulting explicit Picard map. -/
def TrivialLineBundleDetectsPrincipal
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C) : Prop :=
  ∀ D, Nonempty
      ((descendedLineBundle X U hnonempty hcover hU h C heffective D).obj ≅
        (InvertibleSheaf.trivial X).obj) →
    D ∈ S.principalSubgroup

/-- The exact global principal boundary for the descended divisor bundles. The forward field says
that principal divisors give trivial bundles; the reverse field says that a trivial bundle comes
only from a principal divisor. This is a logically narrower interface than the earlier cone of
coherent principal cocycles, arbitrary-object separation, separate zero triviality, and principal
detection. Establishing either field from rational sections remains genuine A3 mathematics. -/
structure GlobalPrincipalBoundary
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C) : Prop where
  /-- Every principal divisor has a globally trivial descended line bundle. -/
  trivial_of_principal :
    DescendedPrincipalTrivial X U hnonempty hcover hU h S C heffective
  /-- A globally trivial descended divisor line bundle detects a principal divisor. -/
  principal_of_trivial :
    TrivialLineBundleDetectsPrincipal X U hnonempty hcover hU h S C heffective

namespace GlobalPrincipalBoundary

/-- The two fields of the global boundary are equivalent to the standard geometric
classification of trivial divisor line bundles. -/
theorem trivial_iff_mem_principalSubgroup
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} {U : I → X.Opens} {hnonempty : ∀ i, Nonempty (U i)}
    {hcover : IsOpenCover U} {hU : ∀ i, IsAffineOpen (U i)}
    {h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i)}
    {S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ)}
    {C : DivisorCocycleSystem X U hnonempty hcover hU h}
    {heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C}
    (b : GlobalPrincipalBoundary X U hnonempty hcover hU h S C heffective)
    (D : WeilDivisor (CodimensionOnePoint X)) :
    Nonempty
        ((descendedLineBundle X U hnonempty hcover hU h C heffective D).obj ≅
          (InvertibleSheaf.trivial X).obj) ↔
      D ∈ S.principalSubgroup := by
  constructor
  · exact b.principal_of_trivial D
  · intro hD
    obtain ⟨g, rfl⟩ := S.mem_principalSubgroup.mp hD
    exact b.trivial_of_principal g

/-- The older coherent-cocycle and object-separation cone constructs the sharper global
principal boundary. Only reflection of the trivial object is needed. -/
theorem of_principalCocycleSystem
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hreflect : LineBundleDescent.ModuleDescentReflectsTrivialityFor
      (coordinateCover U hcover hU))
    (hprincipal : PrincipalCocycleSystemTrivial X U hnonempty hcover hU h S C)
    (hdetect : TrivialLineBundleDetectsPrincipal
      X U hnonempty hcover hU h S C heffective) :
    GlobalPrincipalBoundary X U hnonempty hcover hU h S C heffective where
  trivial_of_principal := descendedPrincipalTrivial_of_principalCocycleSystem
    X U hnonempty hcover hU h S C heffective hreflect hprincipal
  principal_of_trivial := hdetect

/-- The zero-divisor bundle is trivial without a separate zero-coherence hypothesis. -/
theorem zeroTrivial
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} {U : I → X.Opens} {hnonempty : ∀ i, Nonempty (U i)}
    {hcover : IsOpenCover U} {hU : ∀ i, IsAffineOpen (U i)}
    {h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i)}
    {S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ)}
    {C : DivisorCocycleSystem X U hnonempty hcover hU h}
    {heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C}
    (b : GlobalPrincipalBoundary X U hnonempty hcover hU h S C heffective) :
    DescendedZeroTrivial X U hnonempty hcover hU h C heffective :=
  descendedZeroTrivial_of_descendedPrincipalTrivial
    X U hnonempty hcover hU h S C heffective b.trivial_of_principal

end GlobalPrincipalBoundary

/-- The divisor-to-Picard map attached to the exact global principal boundary. Its zero-bundle
trivialization is derived from the principal divisor of the unit rational function and is not a
separate argument. -/
noncomputable def divisorToPicOfGlobalPrincipalBoundary
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hadd : DescendedTensorAdditive X U hnonempty hcover hU h C heffective)
    (b : GlobalPrincipalBoundary X U hnonempty hcover hU h S C heffective) :
    WeilDivisor (CodimensionOnePoint X) →+ PicardGroup X :=
  divisorToPic X U hnonempty hcover hU h C heffective hadd b.zeroTrivial

noncomputable section

/-- A global trivialization of the descended divisor line bundle makes the divisor principal on
every coordinate chart. The unresolved global step is compatibility of these chartwise rational
functions, not affine principal detection. -/
theorem restrictDivisor_mem_principal_of_descendedLineBundle_iso_trivial
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (D : WeilDivisor (CodimensionOnePoint X))
    (htrivial : Nonempty
      ((descendedLineBundle X U hnonempty hcover hU h C heffective D).obj ≅
        (InvertibleSheaf.trivial X).obj))
    (i : I) :
    restrictDivisor X (U i) D ∈
      ((h i).ambientOrderSystem X (U i) (hU i)).principalSubgroup := by
  letI := hnonempty i
  let cov := coordinateCover U hcover hU
  let f := cov.f i
  letI : IsOpenImmersion f := cov.map_prop i
  have epull :
      (Scheme.Modules.pullback f).obj (InvertibleSheaf.trivial X).obj ≅
        (InvertibleSheaf.trivial (Spec (.of Γ(X, U i)))).obj := by
    let efreeX : (InvertibleSheaf.trivial X).obj ≅
        SheafOfModules.unit X.ringCatSheaf :=
      Limits.coproductUniqueIso (fun _ : PUnit =>
        SheafOfModules.unit X.ringCatSheaf)
    let Y := Spec (.of Γ(X, U i))
    let efreeY : (InvertibleSheaf.trivial Y).obj ≅
        SheafOfModules.unit Y.ringCatSheaf :=
      Limits.coproductUniqueIso (fun _ : PUnit =>
        SheafOfModules.unit Y.ringCatSheaf)
    exact ((Scheme.Modules.restrictFunctorIsoPullback f).app
      (InvertibleSheaf.trivial X).obj).symm ≪≫
        (Scheme.Modules.restrictFunctor f).mapIso efreeX ≪≫
        Scheme.Modules.restrictUnitIso f ≪≫ efreeY.symm
  have elocal : Nonempty
      ((localLineBundle X (U i) (hU i) (h i) D).obj ≅
        (InvertibleSheaf.trivial (Spec (.of Γ(X, U i)))).obj) := by
    refine ⟨(descendedLineBundleRestrictionIso X U hnonempty hcover hU h C
      heffective D i).symm ≪≫
      (Scheme.Modules.pullback f).mapIso htrivial.some ≪≫ epull⟩
  have ezero : Nonempty
      ((localLineBundle X (U i) (hU i) (h i) 0).obj ≅
        (InvertibleSheaf.trivial (Spec (.of Γ(X, U i)))).obj) := by
    letI := (h i).isDedekindDomain
    letI : IsFractionRing Γ(X, U i) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X (U i) (hU i)
    change Nonempty
      ((AffineDedekind.lineBundle Γ(X, U i) X.functionField
        (localDivisor X (U i) (hU i) (h i) 0)).obj ≅
          (InvertibleSheaf.trivial (Spec (.of Γ(X, U i)))).obj)
    simpa [localDivisor] using
      (AffineDedekind.nonempty_lineBundle_principal_iso_trivial
        Γ(X, U i) X.functionField
        (Additive.ofMul (1 : X.functionFieldˣ)))
  have hlinear :
      (h i).affineOrderSystem X (U i) (hU i) |>.LinearlyEquivalent
        (localDivisor X (U i) (hU i) (h i) D)
        (localDivisor X (U i) (hU i) (h i) 0) := by
    letI := (h i).isDedekindDomain
    letI : IsFractionRing Γ(X, U i) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X (U i) (hU i)
    apply (AffineDedekind.nonempty_lineBundle_iso_iff_linearlyEquivalent
      Γ(X, U i) X.functionField _ _).mp
    exact ⟨elocal.some ≪≫ ezero.some.symm⟩
  have hlocal : localDivisor X (U i) (hU i) (h i) D ∈
      ((h i).affineOrderSystem X (U i) (hU i)).principalSubgroup := by
    simpa [OrderSystem.LinearlyEquivalent, localDivisor] using hlinear
  obtain ⟨g, hg⟩ :=
    ((h i).affineOrderSystem X (U i) (hU i)).mem_principalSubgroup.mp hlocal
  apply ((h i).ambientOrderSystem X (U i) (hU i)).mem_principalSubgroup.mpr
  refine ⟨g, ?_⟩
  rw [← (h i).principalDivisor_reindex_eq_ambientPrincipalDivisor
    X (U i) (hU i) g]
  simpa [localDivisor] using
    congrArg ((h i).divisorEquiv X (U i) (hU i)) hg

/-- Witness-level form of principal detection: every trivial descended divisor bundle admits
one rational function whose principal divisor gives every chart restriction. Once the chosen
global order agrees with the scheme order, this condition is equivalent to
`TrivialLineBundleDetectsPrincipal`; it does not itself construct the witness from overlap data. -/
def TrivialDescendedLineBundleHasGlobalPrincipalWitness
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C) : Prop :=
  ∀ D, Nonempty
      ((descendedLineBundle X U hnonempty hcover hU h C heffective D).obj ≅
        (InvertibleSheaf.trivial X).obj) →
    ∃ g : Additive X.functionFieldˣ, ∀ i,
      restrictDivisor X (U i) D =
        ((h i).ambientOrderSystem X (U i) (hU i)).principalDivisor g

/-- A single global principal witness on every affine chart proves geometric principal
detection. -/
theorem trivialLineBundleDetectsPrincipal_of_globalPrincipalWitness
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (hord : S.ord = SchemeWeilDivisor.orderAt)
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hwitness : TrivialDescendedLineBundleHasGlobalPrincipalWitness
      X U hnonempty hcover hU h C heffective) :
    TrivialLineBundleDetectsPrincipal X U hnonempty hcover hU h S C heffective := by
  intro D htrivial
  obtain ⟨g, hg⟩ := hwitness D htrivial
  apply S.mem_principalSubgroup.mpr
  refine ⟨g, ?_⟩
  ext x
  obtain ⟨i, hxi⟩ := hcover.exists_mem x.1
  let xi : {x : CodimensionOnePoint X // x.1 ∈ U i} := ⟨x, hxi⟩
  have heq := congrArg (fun E => E xi)
    ((restrictDivisor_principalDivisor X (U i) (hU i) (h i) S hord g).trans
      (hg i).symm)
  change (S.principalDivisor g) x = D x
  simpa only [restrictDivisor_apply, xi] using heq

/-- Geometric principal detection supplies the corresponding single rational witness on every
chart. This is the converse of
`trivialLineBundleDetectsPrincipal_of_globalPrincipalWitness`. -/
theorem globalPrincipalWitness_of_trivialLineBundleDetectsPrincipal
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (hord : S.ord = SchemeWeilDivisor.orderAt)
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hdetect : TrivialLineBundleDetectsPrincipal
      X U hnonempty hcover hU h S C heffective) :
    TrivialDescendedLineBundleHasGlobalPrincipalWitness
      X U hnonempty hcover hU h C heffective := by
  intro D htrivial
  obtain ⟨g, hg⟩ := S.mem_principalSubgroup.mp (hdetect D htrivial)
  refine ⟨g, fun i => ?_⟩
  rw [← hg]
  exact restrictDivisor_principalDivisor X (U i) (hU i) (h i) S hord g

/-- Under compatibility of the chosen global order with the scheme order, the global-witness
formulation is exactly geometric principal detection. In particular it is not an additional
localization or cocycle theorem. -/
theorem globalPrincipalWitness_iff_trivialLineBundleDetectsPrincipal
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (hord : S.ord = SchemeWeilDivisor.orderAt)
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C) :
    TrivialDescendedLineBundleHasGlobalPrincipalWitness
        X U hnonempty hcover hU h C heffective ↔
      TrivialLineBundleDetectsPrincipal
        X U hnonempty hcover hU h S C heffective := by
  constructor
  · exact trivialLineBundleDetectsPrincipal_of_globalPrincipalWitness
      X U hnonempty hcover hU h S hord C heffective
  · exact globalPrincipalWitness_of_trivialLineBundleDetectsPrincipal
      X U hnonempty hcover hU h S hord C heffective

end

namespace GlobalPrincipalBoundary

/-- A single rational function compatible on all charts supplies the reverse direction of the
global principal boundary. Together with coherent principal cocycles, only reflection of the
trivial descent object is needed for the forward direction. This is the reduced consumer aimed
at a future rational-section construction. -/
theorem of_globalPrincipalWitness
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (hord : S.ord = SchemeWeilDivisor.orderAt)
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hreflect : LineBundleDescent.ModuleDescentReflectsTrivialityFor
      (coordinateCover U hcover hU))
    (hprincipal : PrincipalCocycleSystemTrivial X U hnonempty hcover hU h S C)
    (hwitness : TrivialDescendedLineBundleHasGlobalPrincipalWitness
      X U hnonempty hcover hU h C heffective) :
    GlobalPrincipalBoundary X U hnonempty hcover hU h S C heffective :=
  of_principalCocycleSystem X U hnonempty hcover hU h S C heffective
    hreflect hprincipal
    (trivialLineBundleDetectsPrincipal_of_globalPrincipalWitness
      X U hnonempty hcover hU h S hord C heffective hwitness)

end GlobalPrincipalBoundary

/-- The map built from the global principal boundary kills principal divisors. No descent
object-separation or separate zero-bundle input appears in this theorem. -/
theorem divisorToPicOfGlobalPrincipalBoundary_principalTrivial
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hadd : DescendedTensorAdditive X U hnonempty hcover hU h C heffective)
    (b : GlobalPrincipalBoundary X U hnonempty hcover hU h S C heffective) :
    DivisorPicard.PrincipalTrivial S
      (divisorToPicOfGlobalPrincipalBoundary
        X U hnonempty hcover hU h S C heffective hadd b) := by
  intro g
  change divisorPicClass X U hnonempty hcover hU h C heffective hadd b.zeroTrivial
    (S.principalDivisor g) = 1
  apply Units.ext
  rw [divisorPicClass_val]
  change toSkeleton
      (descendedLineBundle X U hnonempty hcover hU h C heffective
        (S.principalDivisor g)).obj =
    toSkeleton (𝟙_ X.Modules)
  exact Quotient.sound ⟨(b.trivial_of_principal g).some ≪≫
    TensorInverseComparison.trivialIsoTensorUnit⟩

/-- The global principal boundary gives the exact principal kernel of the derived Picard map.
This is a checked consumer of the two directions of the classical statement
`𝒪(D) ≅ 𝒪 ⇔ D` is principal; constructing the boundary itself remains open. -/
theorem divisorToPicOfGlobalPrincipalBoundary_hasPrincipalKernel
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hadd : DescendedTensorAdditive X U hnonempty hcover hU h C heffective)
    (b : GlobalPrincipalBoundary X U hnonempty hcover hU h S C heffective) :
    DivisorPicard.HasPrincipalKernel S
      (divisorToPicOfGlobalPrincipalBoundary
        X U hnonempty hcover hU h S C heffective hadd b) := by
  apply AddSubgroup.ext
  intro D
  rw [AddMonoidHom.mem_ker]
  constructor
  · intro hD
    apply b.principal_of_trivial D
    change divisorPicClass X U hnonempty hcover hU h C heffective hadd b.zeroTrivial D = 1
      at hD
    have hskel := congrArg Units.val hD
    rw [divisorPicClass_val] at hskel
    change toSkeleton
        (descendedLineBundle X U hnonempty hcover hU h C heffective D).obj =
      toSkeleton (𝟙_ X.Modules) at hskel
    exact ⟨(toSkeleton_eq_toSkeleton_iff.mp hskel).some ≪≫
      TensorInverseComparison.trivialIsoTensorUnit.symm⟩
  · intro hD
    obtain ⟨g, rfl⟩ := S.mem_principalSubgroup.mp hD
    exact divisorToPicOfGlobalPrincipalBoundary_principalTrivial
      X U hnonempty hcover hU h S C heffective hadd b g

/-- Coherent principal triviality makes the explicit divisor homomorphism kill principal
divisors. -/
theorem divisorToPic_principalTrivial
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hadd : DescendedTensorAdditive X U hnonempty hcover hU h C heffective)
    (hzero : DescendedZeroTrivial X U hnonempty hcover hU h C heffective)
    (hinjective : LineBundleDescent.ModuleDescentEssentiallyInjectiveFor
      (coordinateCover U hcover hU))
    (hprincipal : PrincipalCocycleSystemTrivial X U hnonempty hcover hU h S C) :
    DivisorPicard.PrincipalTrivial S
      (divisorToPic X U hnonempty hcover hU h C heffective hadd hzero) := by
  intro g
  change divisorPicClass X U hnonempty hcover hU h C heffective hadd hzero
    (S.principalDivisor g) = 1
  apply Units.ext
  rw [divisorPicClass_val]
  change toSkeleton
      (descendedLineBundle X U hnonempty hcover hU h C heffective
        (S.principalDivisor g)).obj =
    toSkeleton (𝟙_ X.Modules)
  exact Quotient.sound ⟨
    (descendedLineBundle_principal_iso_trivial X U hnonempty hcover hU h S C
      heffective hinjective hprincipal g).some ≪≫
      TensorInverseComparison.trivialIsoTensorUnit⟩

/-- Under object separation, geometric detection of principal divisors upgrades coherent
principal triviality to the exact principal kernel required for divisor-class injectivity. -/
theorem hasPrincipalKernel_of_trivialLineBundleDetectsPrincipal
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hadd : DescendedTensorAdditive X U hnonempty hcover hU h C heffective)
    (hzero : DescendedZeroTrivial X U hnonempty hcover hU h C heffective)
    (hinjective : LineBundleDescent.ModuleDescentEssentiallyInjectiveFor
      (coordinateCover U hcover hU))
    (hprincipal : PrincipalCocycleSystemTrivial X U hnonempty hcover hU h S C)
    (hdetect : TrivialLineBundleDetectsPrincipal
      X U hnonempty hcover hU h S C heffective) :
    DivisorPicard.HasPrincipalKernel S
      (divisorToPic X U hnonempty hcover hU h C heffective hadd hzero) := by
  apply AddSubgroup.ext
  intro D
  rw [AddMonoidHom.mem_ker]
  constructor
  · intro hD
    apply hdetect D
    change divisorPicClass X U hnonempty hcover hU h C heffective hadd hzero D = 1 at hD
    have hskel := congrArg Units.val hD
    rw [divisorPicClass_val] at hskel
    change toSkeleton
        (descendedLineBundle X U hnonempty hcover hU h C heffective D).obj =
      toSkeleton (𝟙_ X.Modules) at hskel
    exact ⟨(toSkeleton_eq_toSkeleton_iff.mp hskel).some ≪≫
      TensorInverseComparison.trivialIsoTensorUnit.symm⟩
  · intro hD
    obtain ⟨g, rfl⟩ := S.mem_principalSubgroup.mp hD
    exact divisorToPic_principalTrivial X U hnonempty hcover hU h S C heffective hadd
      hzero hinjective hprincipal g

/-- Exact principal kernel conversely forces global triviality of a descended divisor line
bundle to detect a principal divisor. -/
theorem trivialLineBundleDetectsPrincipal_of_hasPrincipalKernel
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hadd : DescendedTensorAdditive X U hnonempty hcover hU h C heffective)
    (hzero : DescendedZeroTrivial X U hnonempty hcover hU h C heffective)
    (hker : DivisorPicard.HasPrincipalKernel S
      (divisorToPic X U hnonempty hcover hU h C heffective hadd hzero)) :
    TrivialLineBundleDetectsPrincipal X U hnonempty hcover hU h S C heffective := by
  intro D htrivial
  rw [← hker, AddMonoidHom.mem_ker]
  change divisorPicClass X U hnonempty hcover hU h C heffective hadd hzero D = 1
  apply Units.ext
  rw [divisorPicClass_val]
  change toSkeleton
      (descendedLineBundle X U hnonempty hcover hU h C heffective D).obj =
    toSkeleton (𝟙_ X.Modules)
  exact toSkeleton_eq_toSkeleton_iff.mpr
    ⟨htrivial.some ≪≫ TensorInverseComparison.trivialIsoTensorUnit⟩

/-- Under coherent principal triviality and object separation, exactness of the divisor Picard
map is equivalent to the geometric assertion that only principal divisors have trivial
descended line bundle. -/
theorem hasPrincipalKernel_iff_trivialLineBundleDetectsPrincipal
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hadd : DescendedTensorAdditive X U hnonempty hcover hU h C heffective)
    (hzero : DescendedZeroTrivial X U hnonempty hcover hU h C heffective)
    (hinjective : LineBundleDescent.ModuleDescentEssentiallyInjectiveFor
      (coordinateCover U hcover hU))
    (hprincipal : PrincipalCocycleSystemTrivial X U hnonempty hcover hU h S C) :
    DivisorPicard.HasPrincipalKernel S
        (divisorToPic X U hnonempty hcover hU h C heffective hadd hzero) ↔
      TrivialLineBundleDetectsPrincipal X U hnonempty hcover hU h S C heffective :=
  ⟨trivialLineBundleDetectsPrincipal_of_hasPrincipalKernel
      X U hnonempty hcover hU h S C heffective hadd hzero,
    hasPrincipalKernel_of_trivialLineBundleDetectsPrincipal
      X U hnonempty hcover hU h S C heffective hadd hzero hinjective hprincipal⟩

/-- Descend the explicit divisor homomorphism to divisor classes, still without any ambient
invertible-sheaf/Picard comparison. -/
noncomputable def classToPic
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hadd : DescendedTensorAdditive X U hnonempty hcover hU h C heffective)
    (hzero : DescendedZeroTrivial X U hnonempty hcover hU h C heffective)
    (hinjective : LineBundleDescent.ModuleDescentEssentiallyInjectiveFor
      (coordinateCover U hcover hU))
    (hprincipal : PrincipalCocycleSystemTrivial X U hnonempty hcover hU h S C) :
    S.ClassGroup →+ PicardGroup X :=
  DivisorPicard.classToPic S
    (divisorToPic X U hnonempty hcover hU h C heffective hadd hzero)
    (divisorToPic_principalTrivial X U hnonempty hcover hU h S C heffective hadd
      hzero hinjective hprincipal)

/-- The explicit class map agrees with the divisor construction on representatives. -/
@[simp]
lemma classToPic_divisorClass
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hadd : DescendedTensorAdditive X U hnonempty hcover hU h C heffective)
    (hzero : DescendedZeroTrivial X U hnonempty hcover hU h C heffective)
    (hinjective : LineBundleDescent.ModuleDescentEssentiallyInjectiveFor
      (coordinateCover U hcover hU))
    (hprincipal : PrincipalCocycleSystemTrivial X U hnonempty hcover hU h S C)
    (D : WeilDivisor (CodimensionOnePoint X)) :
    classToPic X U hnonempty hcover hU h S C heffective hadd hzero
        hinjective hprincipal (S.divisorClass D) =
      divisorToPic X U hnonempty hcover hU h C heffective hadd hzero D :=
  DivisorPicard.classToPic_divisorClass S
    (divisorToPic X U hnonempty hcover hU h C heffective hadd hzero)
    (divisorToPic_principalTrivial X U hnonempty hcover hU h S C heffective hadd
      hzero hinjective hprincipal) D

/-- Exact principal kernel identifies divisor classes with the actual range of the explicit
Picard map. This is the unconditional-on-surjectivity equivalence and uses no global
invertible-sheaf comparison. -/
noncomputable def classEquivPicardRange
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hadd : DescendedTensorAdditive X U hnonempty hcover hU h C heffective)
    (hzero : DescendedZeroTrivial X U hnonempty hcover hU h C heffective)
    (hker : DivisorPicard.HasPrincipalKernel S
      (divisorToPic X U hnonempty hcover hU h C heffective hadd hzero)) :
    S.ClassGroup ≃+
      (DivisorPicard.classToPic S
        (divisorToPic X U hnonempty hcover hU h C heffective hadd hzero)
        (DivisorPicard.principalTrivial_of_principalKernel S
          (divisorToPic X U hnonempty hcover hU h C heffective hadd hzero) hker)).range :=
  DivisorPicard.classEquivPicardRange S
    (divisorToPic X U hnonempty hcover hU h C heffective hadd hzero) hker

/-- The explicit range equivalence agrees with the coherently descended class map. -/
@[simp]
lemma classEquivPicardRange_apply_val
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hadd : DescendedTensorAdditive X U hnonempty hcover hU h C heffective)
    (hzero : DescendedZeroTrivial X U hnonempty hcover hU h C heffective)
    (hinjective : LineBundleDescent.ModuleDescentEssentiallyInjectiveFor
      (coordinateCover U hcover hU))
    (hprincipal : PrincipalCocycleSystemTrivial X U hnonempty hcover hU h S C)
    (hker : DivisorPicard.HasPrincipalKernel S
      (divisorToPic X U hnonempty hcover hU h C heffective hadd hzero))
    (c : S.ClassGroup) :
    (classEquivPicardRange X U hnonempty hcover hU h S C heffective hadd hzero hker c).1 =
      classToPic X U hnonempty hcover hU h S C heffective hadd hzero
        hinjective hprincipal c := by
  rw [classEquivPicardRange, DivisorPicard.classEquivPicardRange_apply_val]
  rfl

/-- Exact principal kernel and surjectivity give the full divisor-class/scheme-Picard
equivalence for divisor-generated bundles, without a comparison for unrelated invertible
sheaves. -/
noncomputable def classEquivPicard
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hadd : DescendedTensorAdditive X U hnonempty hcover hU h C heffective)
    (hzero : DescendedZeroTrivial X U hnonempty hcover hU h C heffective)
    (hker : DivisorPicard.HasPrincipalKernel S
      (divisorToPic X U hnonempty hcover hU h C heffective hadd hzero))
    (hsurjective : Function.Surjective
      (divisorToPic X U hnonempty hcover hU h C heffective hadd hzero)) :
    DivisorPicard.ClassEquivalence S X :=
  DivisorPicard.classEquivPicard S
    (divisorToPic X U hnonempty hcover hU h C heffective hadd hzero) hker hsurjective

/-- The exact global principal boundary and surjectivity construct the full divisor-class/Picard
equivalence. Compared with the earlier descent cone, separate zero trivialization,
arbitrary-object separation, and descent-level principal cocycle hypotheses are not parameters of
this consumer. -/
noncomputable def classEquivPicardOfGlobalPrincipalBoundary
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hadd : DescendedTensorAdditive X U hnonempty hcover hU h C heffective)
    (b : GlobalPrincipalBoundary X U hnonempty hcover hU h S C heffective)
    (hsurjective : Function.Surjective
      (divisorToPicOfGlobalPrincipalBoundary
        X U hnonempty hcover hU h S C heffective hadd b)) :
    DivisorPicard.ClassEquivalence S X :=
  DivisorPicard.classEquivPicard S
    (divisorToPicOfGlobalPrincipalBoundary
      X U hnonempty hcover hU h S C heffective hadd b)
    (divisorToPicOfGlobalPrincipalBoundary_hasPrincipalKernel
      X U hnonempty hcover hU h S C heffective hadd b)
    hsurjective

/-- Under coherent principal triviality and object separation, the geometric principal-detection
condition and Picard surjectivity give the full divisor-class/Picard equivalence. This consumer
replaces the abstract kernel equality by its equivalent line-bundle formulation. -/
noncomputable def classEquivPicardOfTrivialLineBundleDetection
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hadd : DescendedTensorAdditive X U hnonempty hcover hU h C heffective)
    (hzero : DescendedZeroTrivial X U hnonempty hcover hU h C heffective)
    (hinjective : LineBundleDescent.ModuleDescentEssentiallyInjectiveFor
      (coordinateCover U hcover hU))
    (hprincipal : PrincipalCocycleSystemTrivial X U hnonempty hcover hU h S C)
    (hdetect : TrivialLineBundleDetectsPrincipal
      X U hnonempty hcover hU h S C heffective)
    (hsurjective : Function.Surjective
      (divisorToPic X U hnonempty hcover hU h C heffective hadd hzero)) :
    DivisorPicard.ClassEquivalence S X :=
  classEquivPicard X U hnonempty hcover hU h S C heffective hadd hzero
    (hasPrincipalKernel_of_trivialLineBundleDetectsPrincipal
      X U hnonempty hcover hU h S C heffective hadd hzero hinjective hprincipal hdetect)
    hsurjective

/-- The witness-level form of principal detection can replace the abstract exact-kernel input in
the full divisor-class/Picard equivalence. Coherent principal triviality, object separation, and
Picard surjectivity remain separate hypotheses. -/
noncomputable def classEquivPicardOfGlobalPrincipalWitness
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (hord : S.ord = SchemeWeilDivisor.orderAt)
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hadd : DescendedTensorAdditive X U hnonempty hcover hU h C heffective)
    (hzero : DescendedZeroTrivial X U hnonempty hcover hU h C heffective)
    (hinjective : LineBundleDescent.ModuleDescentEssentiallyInjectiveFor
      (coordinateCover U hcover hU))
    (hprincipal : PrincipalCocycleSystemTrivial X U hnonempty hcover hU h S C)
    (hwitness : TrivialDescendedLineBundleHasGlobalPrincipalWitness
      X U hnonempty hcover hU h C heffective)
    (hsurjective : Function.Surjective
      (divisorToPic X U hnonempty hcover hU h C heffective hadd hzero)) :
    DivisorPicard.ClassEquivalence S X :=
  classEquivPicardOfTrivialLineBundleDetection
    X U hnonempty hcover hU h S C heffective hadd hzero hinjective hprincipal
    (trivialLineBundleDetectsPrincipal_of_globalPrincipalWitness
      X U hnonempty hcover hU h S hord C heffective hwitness)
    hsurjective

/-- Adding the global comparison for arbitrary invertible sheaves packages the same explicit
divisor-generated map and its chosen descended representatives into the stronger exact
dictionary. The comparison is used only for the dictionary field relating arbitrary sheaves to
Picard units, not to construct the divisor-class equivalence itself. -/
noncomputable def dictionary
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hadd : DescendedTensorAdditive X U hnonempty hcover hU h C heffective)
    (hzero : DescendedZeroTrivial X U hnonempty hcover hU h C heffective)
    (hX : TensorInverseComparison X)
    (hker : DivisorPicard.HasPrincipalKernel S
      (divisorToPic X U hnonempty hcover hU h C heffective hadd hzero))
    (hsurjective : Function.Surjective
      (divisorToPic X U hnonempty hcover hU h C heffective hadd hzero)) :
    DivisorPicard.Dictionary S X where
  comparison := hX
  divisorToPic := divisorToPic X U hnonempty hcover hU h C heffective hadd hzero
  lineBundle := descendedLineBundle X U hnonempty hcover hU h C heffective
  lineBundle_toPic D := by
    change Additive.ofMul
        (hX.toPic (descendedLineBundle X U hnonempty hcover hU h C heffective D)) =
      Additive.ofMul
        (divisorPicClass X U hnonempty hcover hU h C heffective hadd hzero D)
    exact congrArg Additive.ofMul
      (divisorPicClass_eq_toPic X U hnonempty hcover hU h C heffective hadd
        hzero hX D).symm
  principalKernel := hker
  surjective := hsurjective

/-- A forward tensor-inverse comparison upgrades the exact global principal boundary to the
full divisor-line-bundle dictionary. The earlier descent and zero conditions are replaced here by
their global principal-boundary consequence, not proved automatically. -/
noncomputable def dictionaryOfGlobalPrincipalBoundary
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hadd : DescendedTensorAdditive X U hnonempty hcover hU h C heffective)
    (b : GlobalPrincipalBoundary X U hnonempty hcover hU h S C heffective)
    (hX : TensorInverseComparison X)
    (hsurjective : Function.Surjective
      (divisorToPicOfGlobalPrincipalBoundary
        X U hnonempty hcover hU h S C heffective hadd b)) :
    DivisorPicard.Dictionary S X :=
  dictionary X U hnonempty hcover hU h S C heffective hadd b.zeroTrivial hX
    (divisorToPicOfGlobalPrincipalBoundary_hasPrincipalKernel
      X U hnonempty hcover hU h S C heffective hadd b)
    hsurjective

/-- The full explicit-inverse equivalence computes to the divisor Picard map on
representatives. -/
@[simp]
lemma classEquivPicard_divisorClass
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hadd : DescendedTensorAdditive X U hnonempty hcover hU h C heffective)
    (hzero : DescendedZeroTrivial X U hnonempty hcover hU h C heffective)
    (hker : DivisorPicard.HasPrincipalKernel S
      (divisorToPic X U hnonempty hcover hU h C heffective hadd hzero))
    (hsurjective : Function.Surjective
      (divisorToPic X U hnonempty hcover hU h C heffective hadd hzero))
    (D : WeilDivisor (CodimensionOnePoint X)) :
    classEquivPicard X U hnonempty hcover hU h S C heffective hadd hzero hker hsurjective
        (S.divisorClass D) =
      divisorToPic X U hnonempty hcover hU h C heffective hadd hzero D :=
  DivisorPicard.classEquivPicard_divisorClass S
    (divisorToPic X U hnonempty hcover hU h C heffective hadd hzero)
    hker hsurjective D

end ExplicitInverse

/-- Tensor-additive descended line bundles and the forward tensor-inverse comparison define an
additive homomorphism from Weil divisors to the scheme Picard group. The zero law follows by
cancellation from the isomorphism for `0 + 0`; it is not an extra assumption. -/
noncomputable def divisorToPic
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hadd : DescendedTensorAdditive X U hnonempty hcover hU h C heffective)
    (hX : TensorInverseComparison X) :
    WeilDivisor (CodimensionOnePoint X) →+ PicardGroup X where
  toFun D := Additive.ofMul (hX.toPic
    (descendedLineBundle X U hnonempty hcover hU h C heffective D))
  map_zero' := by
    change hX.toPic
      (descendedLineBundle X U hnonempty hcover hU h C heffective 0) = 1
    have hz : hX.toPic
        (descendedLineBundle X U hnonempty hcover hU h C heffective 0) =
      hX.toPic (descendedLineBundle X U hnonempty hcover hU h C heffective 0) *
        hX.toPic (descendedLineBundle X U hnonempty hcover hU h C heffective 0) := by
      apply Units.ext
      change toSkeleton
          (descendedLineBundle X U hnonempty hcover hU h C heffective 0).obj =
        toSkeleton
            (descendedLineBundle X U hnonempty hcover hU h C heffective 0).obj *
          toSkeleton
            (descendedLineBundle X U hnonempty hcover hU h C heffective 0).obj
      rw [← Skeleton.toSkeleton_tensorObj]
      exact Quotient.sound ⟨(hadd 0 0).some⟩
    exact (mul_left_cancel (show
      hX.toPic (descendedLineBundle X U hnonempty hcover hU h C heffective 0) * 1 =
        hX.toPic (descendedLineBundle X U hnonempty hcover hU h C heffective 0) *
          hX.toPic (descendedLineBundle X U hnonempty hcover hU h C heffective 0) by
      simpa only [mul_one] using hz)).symm
  map_add' D E := by
    change hX.toPic
        (descendedLineBundle X U hnonempty hcover hU h C heffective (D + E)) =
      hX.toPic (descendedLineBundle X U hnonempty hcover hU h C heffective D) *
        hX.toPic (descendedLineBundle X U hnonempty hcover hU h C heffective E)
    apply Units.ext
    change toSkeleton
        (descendedLineBundle X U hnonempty hcover hU h C heffective (D + E)).obj =
      toSkeleton (descendedLineBundle X U hnonempty hcover hU h C heffective D).obj *
        toSkeleton (descendedLineBundle X U hnonempty hcover hU h C heffective E).obj
    rw [← Skeleton.toSkeleton_tensorObj]
    exact Quotient.sound ⟨(hadd D E).some⟩

/-- When the global tensor-inverse comparison exists, the explicit divisor-generated
homomorphism is exactly the earlier comparison-based homomorphism. -/
theorem explicitDivisorToPic_eq_divisorToPic_of_tensorInverseComparison
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hadd : DescendedTensorAdditive X U hnonempty hcover hU h C heffective)
    (hzero : DescendedZeroTrivial X U hnonempty hcover hU h C heffective)
    (hX : TensorInverseComparison X) :
    ExplicitInverse.divisorToPic X U hnonempty hcover hU h C heffective hadd hzero =
      divisorToPic X U hnonempty hcover hU h C heffective hadd hX := by
  apply AddMonoidHom.ext
  intro D
  exact congrArg Additive.ofMul
    (ExplicitInverse.divisorPicClass_eq_toPic X U hnonempty hcover hU h C heffective
      hadd hzero hX D)

/-- Coherently trivial principal cocycles give a principal-trivial divisor-to-Picard
homomorphism after object separation. -/
theorem divisorToPic_principalTrivial
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hadd : DescendedTensorAdditive X U hnonempty hcover hU h C heffective)
    (hX : TensorInverseComparison X)
    (hinjective : LineBundleDescent.ModuleDescentEssentiallyInjectiveFor
      (coordinateCover U hcover hU))
    (hprincipal : PrincipalCocycleSystemTrivial X U hnonempty hcover hU h S C) :
    DivisorPicard.PrincipalTrivial S
      (divisorToPic X U hnonempty hcover hU h C heffective hadd hX) := by
  intro g
  change hX.toPic
      (descendedLineBundle X U hnonempty hcover hU h C heffective
        (S.principalDivisor g)) = 1
  have hpic : hX.toPic
      (descendedLineBundle X U hnonempty hcover hU h C heffective
        (S.principalDivisor g)) =
      hX.toPic (InvertibleSheaf.trivial X) := by
    apply Units.ext
    rw [hX.toPic_val, hX.toPic_val]
    exact Quotient.sound ⟨(descendedLineBundle_principal_iso_trivial X U hnonempty
      hcover hU h S C heffective hinjective hprincipal g).some⟩
  exact hpic.trans hX.toPic_trivial

/-- Coherent principal triviality and object separation descend the Picard homomorphism of an
effective tensor-additive divisor cocycle system, constructed using the forward tensor-inverse
comparison, to Weil divisor classes. -/
noncomputable def classToPic
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hadd : DescendedTensorAdditive X U hnonempty hcover hU h C heffective)
    (hX : TensorInverseComparison X)
    (hinjective : LineBundleDescent.ModuleDescentEssentiallyInjectiveFor
      (coordinateCover U hcover hU))
    (hprincipal : PrincipalCocycleSystemTrivial X U hnonempty hcover hU h S C) :
    S.ClassGroup →+ PicardGroup X :=
  DivisorPicard.classToPic S
    (divisorToPic X U hnonempty hcover hU h C heffective hadd hX)
    (divisorToPic_principalTrivial X U hnonempty hcover hU h S C heffective
      hadd hX hinjective hprincipal)

/-- The descended class map agrees with the divisor-to-Picard construction on every
representative. -/
@[simp]
lemma classToPic_divisorClass
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hadd : DescendedTensorAdditive X U hnonempty hcover hU h C heffective)
    (hX : TensorInverseComparison X)
    (hinjective : LineBundleDescent.ModuleDescentEssentiallyInjectiveFor
      (coordinateCover U hcover hU))
    (hprincipal : PrincipalCocycleSystemTrivial X U hnonempty hcover hU h S C)
    (D : WeilDivisor (CodimensionOnePoint X)) :
    classToPic X U hnonempty hcover hU h S C heffective hadd hX hinjective hprincipal
        (S.divisorClass D) =
      divisorToPic X U hnonempty hcover hU h C heffective hadd hX D :=
  DivisorPicard.classToPic_divisorClass S
    (divisorToPic X U hnonempty hcover hU h C heffective hadd hX)
    (divisorToPic_principalTrivial X U hnonempty hcover hU h S C heffective
      hadd hX hinjective hprincipal) D

/-- If the descended divisor map constructed using the forward tensor-inverse comparison has
exactly the principal divisors as its kernel, divisor classes are equivalent to its actual range
in the scheme Picard group. No Picard-surjectivity hypothesis is used. -/
noncomputable def classEquivPicardRange
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hadd : DescendedTensorAdditive X U hnonempty hcover hU h C heffective)
    (hX : TensorInverseComparison X)
    (hker : DivisorPicard.HasPrincipalKernel S
      (divisorToPic X U hnonempty hcover hU h C heffective hadd hX)) :
    S.ClassGroup ≃+
      (DivisorPicard.classToPic S
        (divisorToPic X U hnonempty hcover hU h C heffective hadd hX)
        (DivisorPicard.principalTrivial_of_principalKernel S
          (divisorToPic X U hnonempty hcover hU h C heffective hadd hX)
          hker)).range :=
  DivisorPicard.classEquivPicardRange S
    (divisorToPic X U hnonempty hcover hU h C heffective hadd hX) hker

/-- The range equivalence agrees with the cocycle-built class map whenever coherent principal
triviality and object separation supply that map. -/
@[simp]
lemma classEquivPicardRange_apply_val
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hadd : DescendedTensorAdditive X U hnonempty hcover hU h C heffective)
    (hX : TensorInverseComparison X)
    (hinjective : LineBundleDescent.ModuleDescentEssentiallyInjectiveFor
      (coordinateCover U hcover hU))
    (hprincipal : PrincipalCocycleSystemTrivial X U hnonempty hcover hU h S C)
    (hker : DivisorPicard.HasPrincipalKernel S
      (divisorToPic X U hnonempty hcover hU h C heffective hadd hX))
    (c : S.ClassGroup) :
    (classEquivPicardRange X U hnonempty hcover hU h S C heffective hadd hX hker c).1 =
      classToPic X U hnonempty hcover hU h S C heffective hadd hX
        hinjective hprincipal c := by
  rw [classEquivPicardRange, DivisorPicard.classEquivPicardRange_apply_val]
  rfl

/-- The forward tensor-inverse comparison together with exact kernel and surjectivity hypotheses
upgrades the descended construction to the complete scheme-level divisor-line-bundle dictionary.
The dictionary's checked consumer gives the full divisor-class/Picard equivalence. -/
noncomputable def dictionary
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hadd : DescendedTensorAdditive X U hnonempty hcover hU h C heffective)
    (hX : TensorInverseComparison X)
    (hker : DivisorPicard.HasPrincipalKernel S
      (divisorToPic X U hnonempty hcover hU h C heffective hadd hX))
    (hsurjective : Function.Surjective
      (divisorToPic X U hnonempty hcover hU h C heffective hadd hX)) :
    DivisorPicard.Dictionary S X where
  comparison := hX
  divisorToPic := divisorToPic X U hnonempty hcover hU h C heffective hadd hX
  lineBundle := descendedLineBundle X U hnonempty hcover hU h C heffective
  lineBundle_toPic _ := rfl
  principalKernel := hker
  surjective := hsurjective

/-- Under the forward tensor-inverse comparison, exact kernel, and surjectivity, the cocycle
construction yields the full additive equivalence from Weil divisor classes to the scheme
Picard group. -/
noncomputable def classEquivalence
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hadd : DescendedTensorAdditive X U hnonempty hcover hU h C heffective)
    (hX : TensorInverseComparison X)
    (hker : DivisorPicard.HasPrincipalKernel S
      (divisorToPic X U hnonempty hcover hU h C heffective hadd hX))
    (hsurjective : Function.Surjective
      (divisorToPic X U hnonempty hcover hU h C heffective hadd hX)) :
    DivisorPicard.ClassEquivalence S X :=
  (dictionary X U hnonempty hcover hU h S C heffective hadd hX
    hker hsurjective).classEquivalence

/-- The full equivalence induced by the cocycle construction agrees with its divisor-to-Picard
homomorphism on representatives. -/
@[simp]
lemma classEquivalence_divisorClass
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hadd : DescendedTensorAdditive X U hnonempty hcover hU h C heffective)
    (hX : TensorInverseComparison X)
    (hker : DivisorPicard.HasPrincipalKernel S
      (divisorToPic X U hnonempty hcover hU h C heffective hadd hX))
    (hsurjective : Function.Surjective
      (divisorToPic X U hnonempty hcover hU h C heffective hadd hX))
    (D : WeilDivisor (CodimensionOnePoint X)) :
    classEquivalence X U hnonempty hcover hU h S C heffective hadd hX hker hsurjective
        (S.divisorClass D) =
      divisorToPic X U hnonempty hcover hU h C heffective hadd hX D :=
  DivisorPicard.Dictionary.classEquivalence_divisorClass
    (dictionary X U hnonempty hcover hU h S C heffective hadd hX
      hker hsurjective) D

end DivisorCocycleSystem

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent
