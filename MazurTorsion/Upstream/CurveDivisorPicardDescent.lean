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
tensor-additive up to isomorphism. Given the forward `TensorInverseComparison X`, these bundles
define elements of the scheme Picard group. Since Picard classes live in the skeleton, no higher
tensor coherence is needed: the isomorphism for `0 + 0` already proves the zero law by
cancellation.

If every principal cocycle is coherently trivial and module descent separates global objects,
the homomorphism kills principal divisors and therefore descends to divisor classes. With the
additional exact-kernel and surjectivity inputs, the construction supplies the full checked
divisor-line-bundle dictionary and hence the divisor-class/Picard equivalence. This file does not
assert existence of the cocycle family, effectivity, tensor-additivity, the forward
tensor-inverse comparison, principal coherence, object separation, exactness, or surjectivity.
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

namespace DivisorCocycleSystem

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
