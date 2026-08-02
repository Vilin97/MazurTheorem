/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.AINTLIB.Picard.Pic
import TauCeti.AlgebraicGeometry.LineBundle.Basic
import TauCeti.AlgebraicGeometry.WeilDivisor.Dedekind.ClassGroup
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.RingTheory.PicardGroup

/-!
# Divisor classes and line bundles

This file provides checked interfaces between three existing notions:

* Tau Ceti's locally free rank-one `InvertibleSheaf`;
* AINTLIB's tensor-unit definition of the Picard group of a scheme;
* Tau Ceti's Weil-divisor class group.

The scheme-level bridge is stated relative to the exact comparison between local rank-one
freeness and tensor-invertibility that it needs. Given a principal-trivial divisor-to-Picard
homomorphism, the universal property of the divisor class group then supplies the descent. If
the kernel is exactly the principal divisors and the map is surjective, the descent is an
equivalence.

Unconditionally, the current dependency graph supports the class-level dictionary between the
divisor class group of an affine Dedekind curve and Mathlib's module Picard group. The resulting
equivalence has the standard sign: the checked representative formula below sends the divisor
of a fractional ideal to the inverse of that ideal's Picard class. An explicit localization
hypothesis packages the chosen invertible module as an invertible sheaf on `Spec R`; the further
comparison with AINTLIB's scheme Picard group remains visible in `PicardComparison` rather than
being hidden behind a stronger claim than the current library proves.
-/

open CategoryTheory
open scoped nonZeroDivisors

namespace MazurTorsion.AlgebraicGeometry

universe u v

open _root_.AlgebraicGeometry
open TauCeti.AlgebraicGeometry

/-- The AINTLIB monoidal structure used locally to inspect representatives of `Scheme.Pic`. -/
noncomputable local instance schemeModulesMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- The AINTLIB symmetric structure used locally for the commutative Picard group. -/
noncomputable local instance schemeModulesSymmetric (X : Scheme.{u}) :
    SymmetricCategory X.Modules :=
  Scheme.Modules.symmetricCategory X

/-- The additive form of the scheme Picard group, used by divisor homomorphisms. -/
abbrev PicardGroup (X : Scheme.{u}) := Additive (Scheme.Pic X)

/-- Categorical tensor-invertibility of a sheaf of modules. -/
def IsTensorInvertible (X : Scheme.{u}) (M : X.Modules) : Prop :=
  letI := Scheme.Modules.monoidalCategory X
  IsUnit (toSkeleton M)

/-- The comparison between locally free rank-one sheaves and tensor units. -/
def PicardComparison (X : Scheme.{u}) : Prop :=
  ∀ M : X.Modules,
    SheafOfModules.isInvertible X M ↔ IsTensorInvertible X M

/-- The affine localization input saying that the sheaf associated to an invertible module is
locally free of rank one. -/
def TildeInvertibility (R : Type u) [CommRing R] : Prop :=
  ∀ M : ModuleCat.{u} R, [Module.Invertible R M] →
    SheafOfModules.isInvertible (_root_.AlgebraicGeometry.Spec (.of R))
      (_root_.AlgebraicGeometry.tilde M)

/-- The tilde-localization comparison, uniformly for commutative rings in one universe. -/
def UniversalTildeInvertibility : Prop :=
  ∀ (R : CommRingCat.{u}) (M : ModuleCat.{u} R), [Module.Invertible R M] →
    SheafOfModules.isInvertible (_root_.AlgebraicGeometry.Spec R)
      (_root_.AlgebraicGeometry.tilde M)

namespace PicardComparison

variable {X : Scheme.{u}} (hX : PicardComparison X)

/-- The Picard class represented by an invertible sheaf. -/
noncomputable def toPic (L : InvertibleSheaf X) : Scheme.Pic X := by
  exact (hX L.obj).mp L.property |>.unit

@[simp]
lemma toPic_val (L : InvertibleSheaf X) :
    (hX.toPic L).val = toSkeleton L.obj := by
  exact IsUnit.unit_spec _

/-- A chosen invertible-sheaf representative of a Picard class. -/
noncomputable def representative (p : Scheme.Pic X) : InvertibleSheaf X := by
  refine ⟨(fromSkeleton X.Modules).obj p.val, (hX _).mpr ?_⟩
  rw [IsTensorInvertible, toSkeleton_fromSkeleton_obj]
  exact p.isUnit

@[simp]
lemma toPic_representative (p : Scheme.Pic X) :
    hX.toPic (hX.representative p) = p := by
  apply Units.ext
  exact toPic_val hX _ |>.trans (toSkeleton_fromSkeleton_obj _)

/-- Recovering a representative from the Picard class of a line bundle changes it only by
isomorphism. -/
lemma nonempty_representative_toPic_iso (L : InvertibleSheaf X) :
    Nonempty ((hX.representative (hX.toPic L)).obj ≅ L.obj) := by
  change Nonempty ((fromSkeleton X.Modules).obj (hX.toPic L).val ≅ L.obj)
  apply toSkeleton_eq_toSkeleton_iff.mp
  rw [toSkeleton_fromSkeleton_obj, toPic_val]

end PicardComparison

namespace DivisorPicard

variable {Y : Type*} {X : Scheme.{u}} {G : Type v} [AddCommGroup G]

/-- The type of additive identifications between divisor classes and scheme Picard classes. -/
abbrev ClassEquivalence (S : WeilDivisor.OrderSystem Y G) (X : Scheme.{u}) :=
  S.ClassGroup ≃+ PicardGroup X

/-- A divisor-to-Picard homomorphism sends every principal divisor to the identity. -/
def PrincipalTrivial
    (S : WeilDivisor.OrderSystem Y G)
    (toPic : WeilDivisor Y →+ PicardGroup X) : Prop :=
  ∀ g, toPic (S.principalDivisor g) = 0

/-- Descend a principal-trivial divisor-to-Picard construction to divisor classes. -/
noncomputable def classToPic
    (S : WeilDivisor.OrderSystem Y G)
    (toPic : WeilDivisor Y →+ PicardGroup X)
    (hprincipal : PrincipalTrivial S toPic) :
    S.ClassGroup →+ PicardGroup X :=
  WeilDivisor.OrderSystem.ClassGroup.lift S toPic hprincipal

@[simp]
lemma classToPic_divisorClass
    (S : WeilDivisor.OrderSystem Y G)
    (toPic : WeilDivisor Y →+ PicardGroup X)
    (hprincipal : PrincipalTrivial S toPic) (D : WeilDivisor Y) :
    classToPic S toPic hprincipal (S.divisorClass D) = toPic D :=
  WeilDivisor.OrderSystem.ClassGroup.lift_divisorClass S toPic hprincipal D

/-- Exactness at divisors: the only divisors with trivial Picard class are principal. -/
def HasPrincipalKernel
    (S : WeilDivisor.OrderSystem Y G)
    (toPic : WeilDivisor Y →+ PicardGroup X) : Prop :=
  toPic.ker = S.principalSubgroup

lemma classToPic_injective
    (S : WeilDivisor.OrderSystem Y G)
    (toPic : WeilDivisor Y →+ PicardGroup X)
    (hprincipal : PrincipalTrivial S toPic)
    (hker : HasPrincipalKernel S toPic) :
    Function.Injective (classToPic S toPic hprincipal) := by
  intro c d hcd
  apply sub_eq_zero.mp
  obtain ⟨D, hD⟩ := S.divisorClass_surjective (c - d)
  have hzero : classToPic S toPic hprincipal (c - d) = 0 := by
    rw [map_sub, hcd, sub_self]
  rw [← hD] at hzero ⊢
  rw [classToPic_divisorClass] at hzero
  rw [S.divisorClass_eq_zero_iff]
  rw [← hker]
  exact hzero

lemma classToPic_surjective
    (S : WeilDivisor.OrderSystem Y G)
    (toPic : WeilDivisor Y →+ PicardGroup X)
    (hprincipal : PrincipalTrivial S toPic)
    (hsurjective : Function.Surjective toPic) :
    Function.Surjective (classToPic S toPic hprincipal) := by
  intro p
  obtain ⟨D, rfl⟩ := hsurjective p
  exact ⟨S.divisorClass D, classToPic_divisorClass S toPic hprincipal D⟩

/-- The strongest general divisor-class/Picard equivalence: a principal-trivial construction
with exactly principal kernel and hitting every Picard class descends to an equivalence. -/
noncomputable def classEquivPicard
    (S : WeilDivisor.OrderSystem Y G)
    (toPic : WeilDivisor Y →+ PicardGroup X)
    (hprincipal : PrincipalTrivial S toPic)
    (hker : HasPrincipalKernel S toPic)
    (hsurjective : Function.Surjective toPic) :
    ClassEquivalence S X :=
  AddEquiv.ofBijective (classToPic S toPic hprincipal)
    ⟨classToPic_injective S toPic hprincipal hker,
      classToPic_surjective S toPic hprincipal hsurjective⟩

@[simp]
lemma classEquivPicard_divisorClass
    (S : WeilDivisor.OrderSystem Y G)
    (toPic : WeilDivisor Y →+ PicardGroup X)
    (hprincipal : PrincipalTrivial S toPic)
    (hker : HasPrincipalKernel S toPic)
    (hsurjective : Function.Surjective toPic) (D : WeilDivisor Y) :
    classEquivPicard S toPic hprincipal hker hsurjective (S.divisorClass D) = toPic D :=
  classToPic_divisorClass S toPic hprincipal D

/-- An exact scheme-level divisor-class/Picard dictionary for an order system. Besides the class
map and its exactness, it records chosen invertible-sheaf representatives and the comparison
between Tau Ceti's local rank-one predicate and AINTLIB's tensor-unit Picard group. The data does
not assert a particular affine-chart normalization of the chosen correspondence. -/
structure Dictionary (S : WeilDivisor.OrderSystem Y G) (X : Scheme.{u}) where
  /-- Locally free rank-one sheaves are exactly tensor-invertible sheaves. -/
  comparison : PicardComparison X
  /-- The additive Picard class associated to a Weil divisor. -/
  divisorToPic : WeilDivisor Y →+ PicardGroup X
  /-- An invertible-sheaf representative of the line bundle associated to a divisor. -/
  lineBundle : WeilDivisor Y → InvertibleSheaf X
  /-- The chosen line bundle represents the specified divisor Picard class. -/
  lineBundle_toPic (D : WeilDivisor Y) :
    Additive.ofMul (comparison.toPic (lineBundle D)) = divisorToPic D
  /-- Principal divisors have trivial Picard class. -/
  principalTrivial : PrincipalTrivial S divisorToPic
  /-- The line bundle of a principal divisor is isomorphic to the trivial line bundle. -/
  lineBundle_principal_iso_trivial (g : G) :
    Nonempty ((lineBundle (S.principalDivisor g)).obj ≅ (InvertibleSheaf.trivial X).obj)
  /-- Only principal divisors have trivial Picard class. -/
  principalKernel : HasPrincipalKernel S divisorToPic
  /-- Every scheme Picard class is represented by a divisor. -/
  surjective : Function.Surjective divisorToPic

namespace Dictionary

variable {S : WeilDivisor.OrderSystem Y G}
variable (d : Dictionary S X)

/-- The divisor-class/Picard equivalence supplied by an exact dictionary. -/
noncomputable def classEquivalence : ClassEquivalence S X :=
  classEquivPicard S d.divisorToPic d.principalTrivial d.principalKernel d.surjective

@[simp]
lemma classEquivalence_divisorClass (D : WeilDivisor Y) :
    d.classEquivalence (S.divisorClass D) = d.divisorToPic D :=
  classEquivPicard_divisorClass S d.divisorToPic d.principalTrivial d.principalKernel
    d.surjective D

end Dictionary

end DivisorPicard

namespace AffineDedekind

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open TauCeti.AlgebraicGeometry.WeilDivisor

variable (R : Type u) [CommRing R] [IsDedekindDomain R]
variable (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The standard-sign affine Dedekind divisor-class/Picard equivalence. Tau Ceti's fractional
ideal divisor sends an ideal to its positive valuation divisor, while `O(D)` is represented by
the inverse ideal, hence the final negation. -/
noncomputable def classEquivPicard :
    (WeilDivisor.OrderSystem.ofDedekindDomain R K).ClassGroup ≃+
      Additive (CommRing.Pic R) :=
  (WeilDivisor.classGroupAddEquiv R K).trans
    ((MulEquiv.toAdditive (ClassGroup.equivPic R)).trans
      (AddEquiv.neg (Additive (CommRing.Pic R))))

/-- The Picard class of the invertible module `O(D)` associated to an affine Dedekind divisor. -/
noncomputable def divisorToPic :
    WeilDivisor (HeightOneSpectrum R) →+ Additive (CommRing.Pic R) :=
  classEquivPicard R K |>.toAddMonoidHom.comp
    (WeilDivisor.OrderSystem.ofDedekindDomain R K).divisorClass

@[simp]
lemma divisorToPic_principalDivisor (g : Additive Kˣ) :
    divisorToPic R K
      ((WeilDivisor.OrderSystem.ofDedekindDomain R K).principalDivisor g) = 0 := by
  rw [divisorToPic, AddMonoidHom.comp_apply,
    WeilDivisor.OrderSystem.divisorClass_principalDivisor, map_zero]

/-- The multiplicative Picard class underlying `divisorToPic`. -/
noncomputable def lineBundleClass (D : WeilDivisor (HeightOneSpectrum R)) :
    CommRing.Pic R :=
  Additive.toMul (divisorToPic R K D)

/-- On the divisor of an invertible fractional ideal `I`, the standard line-bundle class is the
inverse of the Picard class represented by `I`. -/
@[simp]
lemma lineBundleClass_fractionalIdealDivisor (I : (FractionalIdeal R⁰ K)ˣ) :
    lineBundleClass R K (WeilDivisor.fractionalIdealDivisor R K (Additive.ofMul I)) =
      ((ClassGroup.equivPic R) (ClassGroup.mk K I))⁻¹ := by
  rw [lineBundleClass, divisorToPic, AddMonoidHom.comp_apply]
  change Additive.toMul
      (classEquivPicard R K
        ((WeilDivisor.OrderSystem.ofDedekindDomain R K).divisorClass
          (WeilDivisor.fractionalIdealDivisor R K (Additive.ofMul I)))) = _
  rw [classEquivPicard, AddEquiv.trans_apply,
    WeilDivisor.classGroupAddEquiv_divisorClass_fractionalIdealDivisor]
  rfl

@[simp]
lemma classEquivPicard_divisorClass (D : WeilDivisor (HeightOneSpectrum R)) :
    classEquivPicard R K
        ((WeilDivisor.OrderSystem.ofDedekindDomain R K).divisorClass D) =
      Additive.ofMul (lineBundleClass R K D) := by
  rw [lineBundleClass, ofMul_toMul]
  rfl

@[simp]
lemma lineBundleClass_principalDivisor (g : Additive Kˣ) :
    lineBundleClass R K
      ((WeilDivisor.OrderSystem.ofDedekindDomain R K).principalDivisor g) = 1 := by
  rw [lineBundleClass, divisorToPic_principalDivisor]
  rfl

/-- A chosen invertible-module representative of the affine line-bundle class `O(D)`. -/
abbrev lineBundleModule (D : WeilDivisor (HeightOneSpectrum R)) : Type u :=
  (lineBundleClass R K D : Type u)

@[simp]
lemma lineBundleModule_picClass (D : WeilDivisor (HeightOneSpectrum R)) :
    CommRing.Pic.mk R (lineBundleModule R K D) = lineBundleClass R K D :=
  CommRing.Pic.mk_eq_self

/-- A principal divisor has a trivial affine line-bundle module. -/
lemma nonempty_lineBundleModule_principal_equiv (g : Additive Kˣ) :
    Nonempty
      (lineBundleModule R K
          ((WeilDivisor.OrderSystem.ofDedekindDomain R K).principalDivisor g) ≃ₗ[R] R) := by
  rw [← CommRing.Pic.mk_eq_one_iff, lineBundleModule_picClass,
    lineBundleClass_principalDivisor]

/-- The line bundle `O(D)` on the affine Dedekind scheme, assuming the precise localization
comparison asserting that tilde of an invertible module is locally free of rank one. -/
noncomputable def lineBundle
    (hlocal : TildeInvertibility R) (D : WeilDivisor (HeightOneSpectrum R)) :
    InvertibleSheaf (_root_.AlgebraicGeometry.Spec (.of R)) :=
  ⟨_root_.AlgebraicGeometry.tilde (ModuleCat.of R (lineBundleModule R K D)),
    hlocal (ModuleCat.of R (lineBundleModule R K D))⟩

/-- The line bundle of a principal divisor is isomorphic to the trivial line bundle. -/
lemma nonempty_lineBundle_principal_iso_trivial
    (hlocal : TildeInvertibility R) (g : Additive Kˣ) :
    Nonempty
      ((lineBundle R K hlocal
          ((WeilDivisor.OrderSystem.ofDedekindDomain R K).principalDivisor g)).obj ≅
        (InvertibleSheaf.trivial (_root_.AlgebraicGeometry.Spec (.of R))).obj) := by
  let e : lineBundleModule R K
      ((WeilDivisor.OrderSystem.ofDedekindDomain R K).principalDivisor g) ≃ₗ[R] R :=
    (nonempty_lineBundleModule_principal_equiv R K g).some
  let e' := e.trans (Finsupp.uniqueLinearEquiv R R PUnit.unit).symm
  exact ⟨(_root_.AlgebraicGeometry.tilde.functor (.of R)).mapIso e'.toModuleIso ≪≫
    _root_.AlgebraicGeometry.tildeFinsupp PUnit⟩

end AffineDedekind

end MazurTorsion.AlgebraicGeometry
