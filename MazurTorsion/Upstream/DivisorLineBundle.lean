/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.AINTLIB.Picard.Pic
import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.LocalTriviality
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

At the scheme level, a full invertible-sheaf/Picard comparison together with a divisor-class
equivalence constructs the entire dictionary: chosen line bundles come from skeleton
representatives, their tensor-additivity holds up to isomorphism, and exactness supplies
principal triviality. Conversely, every exact dictionary forces precisely those two global
outputs. Thus the remaining global Challenge has a checked irreducible characterization rather
than hiding additional localization assumptions.

Unconditionally, the current dependency graph supports the standard-sign class-level dictionary
for an affine Dedekind curve, tensor-additive chosen invertible-module representatives, and tilde
line bundles whose isomorphism classes detect linear equivalence exactly. The checked
representative formula below sends the divisor of a fractional ideal to the inverse of that
ideal's Picard class. The affine localization bridge is also unconditional: restriction of tilde
to a principal open is identified through localized global sections, and a finite basic-open
cover proves that tilde of every invertible module is an invertible sheaf. The further comparison
with AINTLIB's scheme Picard group is now canonical in the forward direction: the localized
tensor comparison assembles to a tilde tensor-product isomorphism, hence an injective homomorphism
from the module Picard group to the scheme Picard group. Consequently the affine divisor map has
exactly the principal divisors as its kernel, and divisor classes are unconditionally equivalent
to their canonical image in scheme Picard. Surjectivity of that canonical map and the full
comparison for arbitrary sheaves remain open rather than being hidden behind a stronger claim
than the current library proves. A final affine existence theorem characterizes the remaining
full-dictionary boundary.
-/

open CategoryTheory
open MonoidalCategory
open TopologicalSpace
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

/-- The exact forward comparison needed to attach a Picard class to a locally free rank-one
sheaf: such a sheaf admits a tensor inverse. -/
def TensorInverseComparison (X : Scheme.{u}) : Prop :=
  ∀ M : X.Modules,
    SheafOfModules.isInvertible X M →
      letI := Scheme.Modules.monoidalCategory X
      ∃ N : X.Modules, Nonempty (M ⊗ N ≅ 𝟙_ X.Modules)

/-- The reverse comparison: every tensor-unit class has a locally free rank-one
representative. -/
def TensorUnitLocalTriviality (X : Scheme.{u}) : Prop :=
  ∀ M : X.Modules, IsTensorInvertible X M → SheafOfModules.isInvertible X M

/-- The comparison between locally free rank-one sheaves and tensor units. -/
def PicardComparison (X : Scheme.{u}) : Prop :=
  ∀ M : X.Modules,
    SheafOfModules.isInvertible X M ↔ IsTensorInvertible X M

namespace TensorInverseComparison

variable {X : Scheme.{u}} (hX : TensorInverseComparison X)

include hX

/-- A chosen tensor inverse makes the skeleton class of a locally free rank-one sheaf a
unit. -/
theorem isTensorInvertible {M : X.Modules} (hM : SheafOfModules.isInvertible X M) :
    IsTensorInvertible X M := by
  rw [IsTensorInvertible]
  letI := Scheme.Modules.monoidalCategory X
  letI := Scheme.Modules.symmetricCategory X
  obtain ⟨N, ⟨e⟩⟩ := hX M hM
  refine isUnit_of_dvd_one ⟨toSkeleton N, ?_⟩
  rw [← Skeleton.toSkeleton_tensorObj, Skeleton.one_eq]
  exact Quotient.sound ⟨e.symm⟩

/-- The Picard class represented by an invertible sheaf, using only the forward tensor-inverse
comparison. -/
noncomputable def toPic (L : InvertibleSheaf X) : Scheme.Pic X := by
  exact (hX.isTensorInvertible L.property).unit

@[simp]
lemma toPic_val (L : InvertibleSheaf X) :
    (hX.toPic L).val = toSkeleton L.obj := by
  exact IsUnit.unit_spec _

/-- The globally free rank-one sheaf is the tensor unit for AINTLIB's localized monoidal
structure on sheaves of modules. The first isomorphism identifies the singleton coproduct with
Mathlib's ordinary unit sheaf; the adjunction counit then identifies that sheaf with the
sheafified monoidal unit. -/
noncomputable def trivialIsoTensorUnit :
    (InvertibleSheaf.trivial X).obj ≅ (𝟙_ X.Modules) :=
  Limits.coproductUniqueIso (fun _ : PUnit ↦
    _root_.SheafOfModules.unit X.ringCatSheaf) ≪≫
      (asIso ((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).counit.app
          (_root_.SheafOfModules.unit X.ringCatSheaf))).symm

/-- The globally trivial invertible sheaf represents the identity of the scheme Picard group. -/
@[simp]
lemma toPic_trivial : hX.toPic (InvertibleSheaf.trivial X) = 1 := by
  apply Units.ext
  rw [toPic_val]
  change toSkeleton (InvertibleSheaf.trivial X).obj = toSkeleton (𝟙_ X.Modules)
  exact Quotient.sound ⟨trivialIsoTensorUnit (X := X)⟩

end TensorInverseComparison

namespace IsTensorInvertible

/-- A tensor-unit class has a chosen sheaf representative of its inverse. -/
theorem exists_tensorInverse {X : Scheme.{u}} {M : X.Modules}
    (hM : IsTensorInvertible X M) :
    letI := Scheme.Modules.monoidalCategory X
    ∃ N : X.Modules, Nonempty (M ⊗ N ≅ 𝟙_ X.Modules) := by
  rw [IsTensorInvertible] at hM
  letI := Scheme.Modules.monoidalCategory X
  obtain ⟨v, hv, -⟩ := isUnit_iff_exists.mp hM
  refine ⟨(fromSkeleton X.Modules).obj v, ?_⟩
  rw [← toSkeleton_fromSkeleton_obj (C := X.Modules) v,
    ← Skeleton.toSkeleton_tensorObj, Skeleton.one_eq] at hv
  exact toSkeleton_eq_toSkeleton_iff.mp hv

end IsTensorInvertible

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

namespace AffineTilde

section TensorLocalization

open scoped TensorProduct

variable (R : Type u) [CommRing R]
variable (M N : Type u) [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable (S : Submonoid R)
variable (A : Type u) [CommRing A] [Algebra R A] [IsLocalization S A]

private noncomputable local instance localizedModuleM : Module A (LocalizedModule S M) :=
  @LocalizedModule.moduleOfIsLocalization R _ S M _ _ A _ _ _

private noncomputable local instance localizedModuleN : Module A (LocalizedModule S N) :=
  @LocalizedModule.moduleOfIsLocalization R _ S N _ _ A _ _ _

private noncomputable local instance localizedModuleTensor :
    Module A (LocalizedModule S (M ⊗[R] N)) :=
  @LocalizedModule.moduleOfIsLocalization R _ S (M ⊗[R] N) _ _ A _ _ _

/-- Tensor product commutes with localization of both modules, for an arbitrary chosen
localization ring. -/
noncomputable def localizedTensorEquivOfIsLocalization :
    LocalizedModule S M ⊗[A] LocalizedModule S N ≃ₗ[A]
      LocalizedModule S (M ⊗[R] N) :=
  IsLocalization.moduleTensorEquiv S A
      (LocalizedModule S M) (LocalizedModule S N) ≪≫ₗ
    (IsLocalizedModule.linearEquiv S
      (TensorProduct.map
        (LocalizedModule.mkLinearMap S M)
        (LocalizedModule.mkLinearMap S N))
      (LocalizedModule.mkLinearMap S (M ⊗[R] N))).extendScalarsOfIsLocalization S A

/-- The tensor-localization equivalence sends the tensor of two denominator-one fractions to
the denominator-one fraction of their tensor. -/
lemma localizedTensorEquivOfIsLocalization_mk_one (m : M) (n : N) :
    localizedTensorEquivOfIsLocalization R M N S A
      (LocalizedModule.mk m 1 ⊗ₜ[A] LocalizedModule.mk n 1) =
        LocalizedModule.mk (m ⊗ₜ[R] n) 1 := by
  change (IsLocalizedModule.linearEquiv S
      (TensorProduct.map
        (LocalizedModule.mkLinearMap S M)
        (LocalizedModule.mkLinearMap S N))
      (LocalizedModule.mkLinearMap S (M ⊗[R] N)))
        ((TensorProduct.map
          (LocalizedModule.mkLinearMap S M)
          (LocalizedModule.mkLinearMap S N)) (m ⊗ₜ[R] n)) =
      (LocalizedModule.mkLinearMap S (M ⊗[R] N)) (m ⊗ₜ[R] n)
  exact IsLocalizedModule.linearEquiv_apply S _ _ _

/-- The tensor-localization equivalence multiplies denominators on arbitrary pure fractions. -/
lemma localizedTensorEquivOfIsLocalization_mk (m : M) (n : N) (s t : S) :
    localizedTensorEquivOfIsLocalization R M N S A
      (LocalizedModule.mk m s ⊗ₜ[A] LocalizedModule.mk n t) =
        LocalizedModule.mk (m ⊗ₜ[R] n) (s * t) := by
  have hm : LocalizedModule.mk m s =
      IsLocalization.mk' A 1 s • LocalizedModule.mk m 1 := by
    simpa using (LocalizedModule.mk'_smul_mk (T := A) 1 m s 1).symm
  have hn : LocalizedModule.mk n t =
      IsLocalization.mk' A 1 t • LocalizedModule.mk n 1 := by
    simpa using (LocalizedModule.mk'_smul_mk (T := A) 1 n t 1).symm
  rw [hm, hn]
  simp only [TensorProduct.smul_tmul_smul, LinearEquiv.map_smul]
  rw [localizedTensorEquivOfIsLocalization_mk_one]
  have hmn : LocalizedModule.mk (m ⊗ₜ[R] n) (s * t) =
      IsLocalization.mk' A 1 (s * t) • LocalizedModule.mk (m ⊗ₜ[R] n) 1 := by
    simpa using
      (LocalizedModule.mk'_smul_mk (T := A) 1 (m ⊗ₜ[R] n) (s * t) 1).symm
  rw [hmn]
  congr 1
  rw [← IsLocalization.mk'_mul]
  simp

end TensorLocalization

section TildeTensor

open scoped TensorProduct

variable (R : Type u) [CommRing R]
variable (M N : Type u) [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

/-- Tensor product commutes with localization, using Mathlib's canonical module structures on
`LocalizedModule`. This specialization can therefore be applied directly to stalk elements. -/
noncomputable def localizedTensorEquiv (S : Submonoid R) :
    LocalizedModule S M ⊗[Localization S] LocalizedModule S N ≃ₗ[Localization S]
      LocalizedModule S (M ⊗[R] N) :=
  IsLocalization.moduleTensorEquiv S (Localization S)
      (LocalizedModule S M) (LocalizedModule S N) ≪≫ₗ
    (IsLocalizedModule.linearEquiv S
      (TensorProduct.map
        (LocalizedModule.mkLinearMap S M)
        (LocalizedModule.mkLinearMap S N))
      (LocalizedModule.mkLinearMap S (M ⊗[R] N))).extendScalarsOfIsLocalization
        S (Localization S)

/-- The canonical localization tensor equivalence multiplies the denominators of pure
fractions. -/
lemma localizedTensorEquiv_mk (S : Submonoid R) (m : M) (n : N) (s t : S) :
    localizedTensorEquiv R M N S
      (LocalizedModule.mk m s ⊗ₜ[Localization S] LocalizedModule.mk n t) =
        LocalizedModule.mk (m ⊗ₜ[R] n) (s * t) := by
  exact localizedTensorEquivOfIsLocalization_mk R M N S (Localization S) m n s t

/-- Pointwise tensor multiplication of locally fractional sections. The local-fraction proof
intersects the two witnessing neighborhoods and multiplies their denominators. -/
noncomputable def sectionsTensorPure (U : Opens (PrimeSpectrum.Top R))
    (a : (structureSheafInType R M).obj.obj (.op U))
    (b : (structureSheafInType R N).obj.obj (.op U)) :
      (structureSheafInType R (M ⊗[R] N)).obj.obj (.op U) :=
  ⟨fun x => letI := x.1.isPrime
    localizedTensorEquiv R M N x.1.asIdeal.primeCompl
        (a.1 x ⊗ₜ[StructureSheaf.Localizations R x.1] b.1 x), by
    intro x
    obtain ⟨Va, hxa, ia, ra, sa, wa⟩ := a.2 x
    obtain ⟨Vb, hxb, ib, rb, sb, wb⟩ := b.2 x
    refine ⟨Va ⊓ Vb, ⟨hxa, hxb⟩, Opens.infLELeft _ _ ≫ ia,
      ra ⊗ₜ[R] rb, sa * sb, fun y => ?_⟩
    obtain ⟨hsay, hay⟩ := wa ⟨y.1, y.2.1⟩
    obtain ⟨hsby, hby⟩ := wb ⟨y.1, y.2.2⟩
    letI := y.1.isPrime
    refine ⟨y.1.asIdeal.primeCompl.mul_mem hsay hsby, ?_⟩
    convert localizedTensorEquiv_mk R M N y.1.asIdeal.primeCompl
      ra rb ⟨sa, hsay⟩ ⟨sb, hsby⟩ using 1
    · apply congrArg (localizedTensorEquiv R M N y.1.asIdeal.primeCompl)
      congr 1
    · rfl⟩

/-- The sectionwise bilinear pairing from the pointwise tensor of tilde presheaves to the tilde
presheaf of the module tensor product. -/
noncomputable def sectionsTensorMap (U : Opens (PrimeSpectrum.Top R)) :
    (moduleStructurePresheaf R M ⊗ moduleStructurePresheaf R N).obj (.op U) ⟶
      (moduleStructurePresheaf R (M ⊗[R] N)).obj (.op U) :=
  ModuleCat.MonoidalCategory.tensorLift (sectionsTensorPure R M N U)
    (by
      intro a a' b
      apply Subtype.ext
      funext x
      letI := x.1.isPrime
      change localizedTensorEquiv R M N x.1.asIdeal.primeCompl
        ((a.1 x + a'.1 x) ⊗ₜ[StructureSheaf.Localizations R x.1] b.1 x) = _
      rw [TensorProduct.add_tmul, map_add]
      rfl)
    (by
      intro r a b
      apply Subtype.ext
      funext x
      letI := x.1.isPrime
      change localizedTensorEquiv R M N x.1.asIdeal.primeCompl
        ((r.1 x • a.1 x) ⊗ₜ[StructureSheaf.Localizations R x.1] b.1 x) = _
      rw [← TensorProduct.smul_tmul', map_smul]
      rfl)
    (by
      intro a b b'
      apply Subtype.ext
      funext x
      letI := x.1.isPrime
      change localizedTensorEquiv R M N x.1.asIdeal.primeCompl
        (a.1 x ⊗ₜ[StructureSheaf.Localizations R x.1] (b.1 x + b'.1 x)) = _
      rw [TensorProduct.tmul_add, map_add]
      rfl)
    (by
      intro r a b
      apply Subtype.ext
      funext x
      letI := x.1.isPrime
      change localizedTensorEquiv R M N x.1.asIdeal.primeCompl
        (a.1 x ⊗ₜ[StructureSheaf.Localizations R x.1] (r.1 x • b.1 x)) = _
      rw [TensorProduct.tmul_smul]
      change localizedTensorEquiv R M N x.1.asIdeal.primeCompl
        (r.1 x • (a.1 x ⊗ₜ[StructureSheaf.Localizations R x.1] b.1 x)) = _
      rw [map_smul]
      rfl)

/-- The natural presheaf morphism underlying the tensor-product comparison for tilde. -/
noncomputable def tensorToTildePresheaf :
    moduleStructurePresheaf R M ⊗ moduleStructurePresheaf R N ⟶
      moduleStructurePresheaf R (M ⊗[R] N) where
  app U := sectionsTensorMap R M N U.unop
  naturality {U V} i := ModuleCat.MonoidalCategory.tensor_ext (by
    intro a b
    apply Subtype.ext
    funext x
    rfl)

/-- On a principal open, the sectionwise tensor pairing is the standard equivalence between
the tensor of two localized modules and the localization of their tensor. -/
noncomputable def basicOpenTensorEquiv (f : R) :
    (structureSheafInType R M).obj.obj (.op (PrimeSpectrum.basicOpen f))
        ⊗[(structureSheafInType R R).obj.obj (.op (PrimeSpectrum.basicOpen f))]
      (structureSheafInType R N).obj.obj (.op (PrimeSpectrum.basicOpen f)) ≃ₗ[
        (structureSheafInType R R).obj.obj (.op (PrimeSpectrum.basicOpen f))]
      (structureSheafInType R (M ⊗[R] N)).obj.obj
        (.op (PrimeSpectrum.basicOpen f)) :=
  IsLocalization.moduleTensorEquiv (.powers f)
      ((structureSheafInType R R).obj.obj (.op (PrimeSpectrum.basicOpen f)))
      ((structureSheafInType R M).obj.obj (.op (PrimeSpectrum.basicOpen f)))
      ((structureSheafInType R N).obj.obj (.op (PrimeSpectrum.basicOpen f))) ≪≫ₗ
    (IsLocalizedModule.linearEquiv (.powers f)
      (TensorProduct.map
        (StructureSheaf.toOpenₗ R M (PrimeSpectrum.basicOpen f))
        (StructureSheaf.toOpenₗ R N (PrimeSpectrum.basicOpen f)))
      (StructureSheaf.toOpenₗ R (M ⊗[R] N)
        (PrimeSpectrum.basicOpen f))).extendScalarsOfIsLocalization
          (.powers f)
          ((structureSheafInType R R).obj.obj (.op (PrimeSpectrum.basicOpen f)))

/-- The principal-open equivalence sends a tensor of denominator-one sections to the
denominator-one section of the tensor. -/
lemma basicOpenTensorEquiv_tmul_toOpen (f : R) (m : M) (n : N) :
    basicOpenTensorEquiv R M N f
      (StructureSheaf.toOpenₗ R M (PrimeSpectrum.basicOpen f) m ⊗ₜ[
        (structureSheafInType R R).obj.obj (.op (PrimeSpectrum.basicOpen f))]
        StructureSheaf.toOpenₗ R N (PrimeSpectrum.basicOpen f) n) =
      StructureSheaf.toOpenₗ R (M ⊗[R] N)
        (PrimeSpectrum.basicOpen f) (m ⊗ₜ[R] n) := by
  change (IsLocalizedModule.linearEquiv (.powers f)
      (TensorProduct.map
        (StructureSheaf.toOpenₗ R M (PrimeSpectrum.basicOpen f))
        (StructureSheaf.toOpenₗ R N (PrimeSpectrum.basicOpen f)))
      (StructureSheaf.toOpenₗ R (M ⊗[R] N) (PrimeSpectrum.basicOpen f)))
        ((TensorProduct.map
          (StructureSheaf.toOpenₗ R M (PrimeSpectrum.basicOpen f))
          (StructureSheaf.toOpenₗ R N (PrimeSpectrum.basicOpen f))) (m ⊗ₜ[R] n)) = _
  exact IsLocalizedModule.linearEquiv_apply (.powers f) _ _ _

/-- On denominator-one sections, the section pairing has the expected pure-tensor formula. -/
lemma sectionsTensorMap_tmul_toOpen (f : R) (m : M) (n : N) :
    sectionsTensorPure R M N (PrimeSpectrum.basicOpen f)
      (StructureSheaf.toOpenₗ R M (PrimeSpectrum.basicOpen f) m)
      (StructureSheaf.toOpenₗ R N (PrimeSpectrum.basicOpen f) n) =
      StructureSheaf.toOpenₗ R (M ⊗[R] N)
        (PrimeSpectrum.basicOpen f) (m ⊗ₜ[R] n) := by
  apply Subtype.ext
  funext x
  letI := x.1.isPrime
  change localizedTensorEquiv R M N x.1.asIdeal.primeCompl
      (LocalizedModule.mk m 1 ⊗ₜ[StructureSheaf.Localizations R x.1]
        LocalizedModule.mk n 1) =
    LocalizedModule.mk (m ⊗ₜ[R] n) 1
  simpa using localizedTensorEquiv_mk R M N x.1.asIdeal.primeCompl m n
    (1 : x.1.asIdeal.primeCompl) (1 : x.1.asIdeal.primeCompl)

/-- The section pairing on a principal open agrees with the localization equivalence after
reducing arbitrary fractions to scalar multiples of denominator-one sections. -/
lemma sectionsTensorMap_basicOpen (f : R) :
    sectionsTensorMap R M N (PrimeSpectrum.basicOpen f) =
      ModuleCat.ofHom (basicOpenTensorEquiv R M N f).toLinearMap := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro a b
  let A := (structureSheafInType R R).obj.obj (.op (PrimeSpectrum.basicOpen f))
  let fM := StructureSheaf.toOpenₗ R M (PrimeSpectrum.basicOpen f)
  let fN := StructureSheaf.toOpenₗ R N (PrimeSpectrum.basicOpen f)
  obtain ⟨⟨m, s⟩, hm⟩ := IsLocalizedModule.mk'_surjective (.powers f) fM a
  obtain ⟨⟨n, t⟩, hn⟩ := IsLocalizedModule.mk'_surjective (.powers f) fN b
  have hm' : IsLocalizedModule.mk' fM m s =
      IsLocalization.mk' A 1 s • fM m := by
    rw [← IsLocalizedModule.mk'_one (.powers f) fM m]
    symm
    simpa using IsLocalizedModule.mk'_smul_mk' A fM 1 m s 1
  have hn' : IsLocalizedModule.mk' fN n t =
      IsLocalization.mk' A 1 t • fN n := by
    rw [← IsLocalizedModule.mk'_one (.powers f) fN n]
    symm
    simpa using IsLocalizedModule.mk'_smul_mk' A fN 1 n t 1
  let AS := ↑((structurePresheafInCommRingCat R ⋙ forget₂ CommRingCat RingCat).obj
    (.op (PrimeSpectrum.basicOpen f)))
  let fm : ↑((moduleStructurePresheaf R M).obj (.op (PrimeSpectrum.basicOpen f))) := fM m
  let fn : ↑((moduleStructurePresheaf R N).obj (.op (PrimeSpectrum.basicOpen f))) := fN n
  let rs : AS := IsLocalization.mk' A 1 s
  let rt : AS := IsLocalization.mk' A 1 t
  have hm'' : Function.uncurry (IsLocalizedModule.mk' fM) (m, s) = rs • fm := hm'
  have hn'' : Function.uncurry (IsLocalizedModule.mk' fN) (n, t) = rt • fn := hn'
  rw [← hm, ← hn, hm'', hn'']
  have hTensor : (rs • fm) ⊗ₜ[AS] (rt • fn) =
      (rs * rt) • (fm ⊗ₜ[AS] fn) := by
    exact TensorProduct.smul_tmul_smul _ _ _ _
  rw [hTensor, map_smul, map_smul]
  have hbase :
      (sectionsTensorMap R M N (PrimeSpectrum.basicOpen f)).hom (fm ⊗ₜ[AS] fn) =
        basicOpenTensorEquiv R M N f (fM m ⊗ₜ[A] fN n) := by
    change sectionsTensorPure R M N (PrimeSpectrum.basicOpen f) (fM m) (fN n) =
      basicOpenTensorEquiv R M N f (fM m ⊗ₜ[A] fN n)
    rw [sectionsTensorMap_tmul_toOpen, basicOpenTensorEquiv_tmul_toOpen]
  exact congrArg ((rs * rt) • ·) hbase

/-- Every principal-open component of the tilde tensor presheaf morphism is bijective. -/
lemma sectionsTensorMap_basicOpen_bijective (f : R) :
    Function.Bijective
      (sectionsTensorMap R M N (PrimeSpectrum.basicOpen f)).hom := by
  rw [sectionsTensorMap_basicOpen]
  exact (basicOpenTensorEquiv R M N f).bijective

private noncomputable abbrev tensorToTildeUnderlying :=
  (PresheafOfModules.toPresheaf
    (structurePresheafInCommRingCat R ⋙ forget₂ CommRingCat RingCat)).map
      (tensorToTildePresheaf R M N)

private instance tensorToTildeUnderlying_isLocallyInjective :
    Presheaf.IsLocallyInjective
      (Opens.grothendieckTopology (PrimeSpectrum.Top R))
      (tensorToTildeUnderlying R M N) where
  equalizerSieve_mem {X} a b h x hx := by
    obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hxf, hfX⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hx X.unop.2
    refine ⟨PrimeSpectrum.basicOpen f, homOfLE hfX, ?_, hxf⟩
    apply (sectionsTensorMap_basicOpen_bijective R M N f).1
    change (tensorToTildePresheaf R M N).app (.op (PrimeSpectrum.basicOpen f))
        ((moduleStructurePresheaf R M ⊗ moduleStructurePresheaf R N).map
          (homOfLE hfX).op a) =
      (tensorToTildePresheaf R M N).app (.op (PrimeSpectrum.basicOpen f))
        ((moduleStructurePresheaf R M ⊗ moduleStructurePresheaf R N).map
          (homOfLE hfX).op b)
    have ha := CategoryTheory.congr_fun
      ((tensorToTildePresheaf R M N).naturality (homOfLE hfX).op) a
    have hb := CategoryTheory.congr_fun
      ((tensorToTildePresheaf R M N).naturality (homOfLE hfX).op) b
    exact ha.trans ((congrArg
      (fun z => (moduleStructurePresheaf R (M ⊗[R] N)).map (homOfLE hfX).op z) h).trans
        hb.symm)

private instance tensorToTildeUnderlying_isLocallySurjective :
    Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology (PrimeSpectrum.Top R))
      (tensorToTildeUnderlying R M N) where
  imageSieve_mem {U} s x hx := by
    obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hxf, hfU⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hx U.2
    refine ⟨PrimeSpectrum.basicOpen f, homOfLE hfU, ?_, hxf⟩
    obtain ⟨t, ht⟩ := (sectionsTensorMap_basicOpen_bijective R M N f).2
      ((moduleStructurePresheaf R (M ⊗[R] N)).map (homOfLE hfU).op s)
    exact ⟨t, ht⟩

private noncomputable abbrev affineRingSheafId :=
  𝟙 (⟨(_root_.AlgebraicGeometry.Spec (CommRingCat.of R)).sheaf.obj ⋙
    forget₂ CommRingCat RingCat,
      (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)).ringCatSheaf.property⟩ :
        Sheaf _ RingCat).obj

private noncomputable abbrev affineSheafification :=
  PresheafOfModules.sheafification (affineRingSheafId R)

private noncomputable abbrev affineSheafificationW :=
  PresheafOfModules.sheafificationW (affineRingSheafId R)

private noncomputable abbrev underlyingAffineModule
    (P : (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)).Modules) :=
  P.val

private noncomputable local instance affinePresheafModulesMonoidalStruct :
    MonoidalCategoryStruct
      (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)).PresheafOfModules :=
  inferInstanceAs (MonoidalCategoryStruct
    (PresheafOfModules
      ((_root_.AlgebraicGeometry.Spec (CommRingCat.of R)).sheaf.obj ⋙
        forget₂ CommRingCat RingCat)))

private noncomputable local instance affinePresheafModulesMonoidal :
    MonoidalCategory
      (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)).PresheafOfModules :=
  inferInstanceAs (MonoidalCategory
    (PresheafOfModules
      ((_root_.AlgebraicGeometry.Spec (CommRingCat.of R)).sheaf.obj ⋙
        forget₂ CommRingCat RingCat)))

private noncomputable local instance affineSheafificationIsLocalization :
    (PresheafOfModules.sheafification (affineRingSheafId R)).IsLocalization
      (PresheafOfModules.sheafificationW (affineRingSheafId R)) :=
  PresheafOfModules.sheafificationW_isLocalization _

/-- Sheafifying the underlying presheaf of a sheaf of modules returns that sheaf. This is the
reflective sheafification counit, specialized to an affine scheme. -/
noncomputable def sheafifyValIso
    (P : (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)).Modules) :
    (affineSheafification R).obj P.val ≅ P :=
  (asIso (PresheafOfModules.sheafificationAdjunction
    (𝟙 (_root_.AlgebraicGeometry.Spec
      (CommRingCat.of R)).ringCatSheaf.obj)).counit).app P

/-- The localized monoidal structure identifies the tensor of two tilde sheaves with the
sheafification of the pointwise tensor of their underlying presheaves. -/
noncomputable def tensorAsSheafification :
    _root_.AlgebraicGeometry.tilde (ModuleCat.of R M) ⊗
        _root_.AlgebraicGeometry.tilde (ModuleCat.of R N) ≅
      (affineSheafification R).obj
        (underlyingAffineModule R (_root_.AlgebraicGeometry.tilde (ModuleCat.of R M)) ⊗
          underlyingAffineModule R (_root_.AlgebraicGeometry.tilde (ModuleCat.of R N))) :=
  ((sheafifyValIso R
      (_root_.AlgebraicGeometry.tilde (ModuleCat.of R M))).symm ⊗ᵢ
    (sheafifyValIso R
      (_root_.AlgebraicGeometry.tilde (ModuleCat.of R N))).symm) ≪≫
      CategoryTheory.Localization.Monoidal.μ
        (affineSheafification R) (affineSheafificationW R) (Iso.refl _) _ _

/-- The locally bijective presheaf morphism used to compare the sheaf tensor with tilde of the
module tensor product. -/
noncomputable def tildeTensorUnderlyingHom :
    underlyingAffineModule R (_root_.AlgebraicGeometry.tilde (ModuleCat.of R M)) ⊗
        underlyingAffineModule R (_root_.AlgebraicGeometry.tilde (ModuleCat.of R N)) ⟶
      underlyingAffineModule R
        (_root_.AlgebraicGeometry.tilde (ModuleCat.of R (M ⊗[R] N))) :=
  tensorToTildePresheaf R M N

/-- The presheaf tensor comparison is inverted by sheafification because its components are
bijective on the basis of principal opens. -/
lemma tildeTensorUnderlyingHom_memW :
    affineSheafificationW R (tildeTensorUnderlyingHom R M N) := by
  apply (PresheafOfModules.sheafificationW_iff_isLocallyBijective
    (affineRingSheafId R) _).2
  constructor
  · change Presheaf.IsLocallyInjective
      (Opens.grothendieckTopology (PrimeSpectrum.Top R))
      (tensorToTildeUnderlying R M N)
    infer_instance
  · change Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology (PrimeSpectrum.Top R))
      (tensorToTildeUnderlying R M N)
    infer_instance

/-- On an affine scheme, the sheaf tensor product of two tilde objects agrees with tilde of the
module tensor product. -/
noncomputable def tildeTensorIso :
    _root_.AlgebraicGeometry.tilde (ModuleCat.of R M) ⊗
        _root_.AlgebraicGeometry.tilde (ModuleCat.of R N) ≅
      _root_.AlgebraicGeometry.tilde (R := CommRingCat.of R)
        (ModuleCat.of R (M ⊗[R] N)) := by
  let h := (affineSheafification R).map (tildeTensorUnderlyingHom R M N)
  let hi : IsIso h :=
    (PresheafOfModules.sheafificationW_iff
      (affineRingSheafId R) (tildeTensorUnderlyingHom R M N)).1
        (tildeTensorUnderlyingHom_memW R M N)
  exact tensorAsSheafification R M N ≪≫
    (@asIso _ _ _ _ h hi) ≪≫
      sheafifyValIso R
        (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of R)
          (ModuleCat.of R (M ⊗[R] N)))

end TildeTensor

/-- The tilde sheaf of an invertible module has the tilde sheaf of its dual as an explicit
tensor inverse. -/
noncomputable def tildeTensorInverseIso
    (R : Type u) [CommRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Invertible R M] :
    _root_.AlgebraicGeometry.tilde (ModuleCat.of R M) ⊗
        _root_.AlgebraicGeometry.tilde (ModuleCat.of R (Module.Dual R M)) ≅
      𝟙_ (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)).Modules :=
  tildeTensorIso R M (Module.Dual R M) ≪≫
    (_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of R)).mapIso
      ((TensorProduct.comm R M (Module.Dual R M) ≪≫ₗ
        Module.Invertible.linearEquiv R M).toModuleIso) ≪≫
    (_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of R)).mapIso
      (Finsupp.uniqueLinearEquiv R R PUnit.unit).symm.toModuleIso ≪≫
    _root_.AlgebraicGeometry.tildeFinsupp PUnit ≪≫
    TensorInverseComparison.trivialIsoTensorUnit

/-- Tilde sends every invertible module to a tensor-invertible sheaf. This proves the forward
Picard comparison for the affine tilde representatives used below, without assuming a global
comparison for arbitrary sheaves. -/
theorem tilde_isTensorInvertible
    (R : Type u) [CommRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Invertible R M] :
    IsTensorInvertible (_root_.AlgebraicGeometry.Spec (CommRingCat.of R))
      (_root_.AlgebraicGeometry.tilde (ModuleCat.of R M)) := by
  rw [IsTensorInvertible]
  refine isUnit_of_dvd_one ⟨toSkeleton
    (_root_.AlgebraicGeometry.tilde (ModuleCat.of R (Module.Dual R M))), ?_⟩
  rw [← Skeleton.toSkeleton_tensorObj, Skeleton.one_eq]
  exact Quotient.sound ⟨(tildeTensorInverseIso R M).symm⟩

open scoped TensorProduct

/-- The scheme Picard class represented by the tilde sheaf of a module Picard-class
representative. -/
noncomputable def modulePicToSchemePicClass
    (R : Type u) [CommRing R] (I : CommRing.Pic R) :
    Scheme.Pic (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)) :=
  (tilde_isTensorInvertible R I).unit

@[simp]
lemma modulePicToSchemePicClass_val
    (R : Type u) [CommRing R] (I : CommRing.Pic R) :
    (modulePicToSchemePicClass R I).val =
      toSkeleton (_root_.AlgebraicGeometry.tilde (ModuleCat.of R I)) :=
  IsUnit.unit_spec _

/-- Tilde of the identity module-Picard representative is the scheme tensor unit. -/
private noncomputable def tildePicOneIso
    (R : Type u) [CommRing R] :
    _root_.AlgebraicGeometry.tilde (ModuleCat.of R (1 : CommRing.Pic R)) ≅
      𝟙_ (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)).Modules := by
  let e : (1 : CommRing.Pic R) ≃ₗ[R] R :=
    (CommRing.Pic.mk_eq_one_iff.mp CommRing.Pic.mk_eq_self).some
  exact (_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of R)).mapIso e.toModuleIso ≪≫
    (_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of R)).mapIso
      (Finsupp.uniqueLinearEquiv R R PUnit.unit).symm.toModuleIso ≪≫
    _root_.AlgebraicGeometry.tildeFinsupp PUnit ≪≫
    TensorInverseComparison.trivialIsoTensorUnit

/-- Tilde carries multiplication of module Picard classes to the sheaf tensor product. -/
private noncomputable def tildePicMulIso
    (R : Type u) [CommRing R] (I J : CommRing.Pic R) :
    _root_.AlgebraicGeometry.tilde (R := CommRingCat.of R)
        (ModuleCat.of R (I * J : CommRing.Pic R)) ≅
      _root_.AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R I) ⊗
        _root_.AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R J) := by
  have h : CommRing.Pic.mk R (I ⊗[R] J) = I * J := by
    rw [CommRing.Pic.mk_tensor, CommRing.Pic.mk_eq_self, CommRing.Pic.mk_eq_self]
  let e : (I * J : CommRing.Pic R) ≃ₗ[R] (I ⊗[R] J) :=
    (CommRing.Pic.mk_eq_iff.mp h).some.symm
  exact (_root_.AlgebraicGeometry.tilde.functor
      (CommRingCat.of R)).mapIso e.toModuleIso ≪≫
    (tildeTensorIso R I J).symm

@[simp]
lemma modulePicToSchemePicClass_one
    (R : Type u) [CommRing R] :
    modulePicToSchemePicClass R 1 = 1 := by
  apply Units.ext
  rw [modulePicToSchemePicClass_val]
  change toSkeleton
      (_root_.AlgebraicGeometry.tilde (ModuleCat.of R (1 : CommRing.Pic R))) =
    toSkeleton (𝟙_ (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)).Modules)
  exact Quotient.sound ⟨tildePicOneIso R⟩

@[simp]
lemma modulePicToSchemePicClass_mul
    (R : Type u) [CommRing R] (I J : CommRing.Pic R) :
    modulePicToSchemePicClass R (I * J) =
      modulePicToSchemePicClass R I * modulePicToSchemePicClass R J := by
  apply Units.ext
  rw [modulePicToSchemePicClass_val]
  change toSkeleton
      (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of R)
        (ModuleCat.of R (I * J : CommRing.Pic R))) =
    toSkeleton (_root_.AlgebraicGeometry.tilde
      (R := CommRingCat.of R) (ModuleCat.of R I)) *
      toSkeleton (_root_.AlgebraicGeometry.tilde
        (R := CommRingCat.of R) (ModuleCat.of R J))
  rw [← Skeleton.toSkeleton_tensorObj]
  exact Quotient.sound ⟨tildePicMulIso R I J⟩

/-- The canonical comparison from the module Picard group of a ring to the scheme Picard group
of its spectrum, induced by tilde. -/
noncomputable def modulePicToSchemePic
    (R : Type u) [CommRing R] :
    CommRing.Pic R →* Scheme.Pic
      (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)) where
  toFun := modulePicToSchemePicClass R
  map_one' := modulePicToSchemePicClass_one R
  map_mul' := modulePicToSchemePicClass_mul R

/-- The tilde comparison from module Picard classes to scheme Picard classes is injective.
Equality in the scheme skeleton gives an isomorphism of tilde sheaves, and full faithfulness of
tilde recovers a linear equivalence of the module representatives. -/
theorem modulePicToSchemePic_injective
    (R : Type u) [CommRing R] :
    Function.Injective (modulePicToSchemePic R) := by
  intro I J h
  have hs : toSkeleton
      (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R I)) =
      toSkeleton
        (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R J)) := by
    have hval := congrArg Units.val h
    change (modulePicToSchemePicClass R I).val =
      (modulePicToSchemePicClass R J).val at hval
    rw [modulePicToSchemePicClass_val, modulePicToSchemePicClass_val] at hval
    exact hval
  obtain ⟨e⟩ := toSkeleton_eq_toSkeleton_iff.mp hs
  let e' := _root_.AlgebraicGeometry.tilde.fullyFaithfulFunctor.preimageIso e
  exact CommRing.Pic.ext_iff.mpr ⟨e'.toLinearEquiv⟩

/-- The additive form of the canonical comparison from module Picard classes to scheme Picard
classes. -/
noncomputable def modulePicToSchemePicAdd
    (R : Type u) [CommRing R] :
    Additive (CommRing.Pic R) →+
      PicardGroup (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)) :=
  (modulePicToSchemePic R).toAdditive

/-- The additive tilde comparison is injective. -/
theorem modulePicToSchemePicAdd_injective
    (R : Type u) [CommRing R] :
    Function.Injective (modulePicToSchemePicAdd R) :=
  modulePicToSchemePic_injective R

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (f : R)

private noncomputable abbrev awayRing := Localization.Away f

private noncomputable abbrev awayMap : R ⟶ CommRingCat.of (awayRing f) :=
  CommRingCat.ofHom (algebraMap R (awayRing f))

private noncomputable abbrev awaySpecMap :
    _root_.AlgebraicGeometry.Spec (CommRingCat.of (awayRing f)) ⟶
      _root_.AlgebraicGeometry.Spec R :=
  _root_.AlgebraicGeometry.Spec.map (awayMap f)

private noncomputable abbrev specSectionsModule (S : CommRingCat.{u})
    (N : (_root_.AlgebraicGeometry.Spec S).Modules)
    (U : (_root_.AlgebraicGeometry.Spec S).Opens) : Module S Γ(N, U) :=
  inferInstance

private noncomputable local instance instModuleAwayRestrictTop :
    Module (awayRing f) Γ((_root_.AlgebraicGeometry.tilde M).restrict (awaySpecMap f),
      (⊤ : (_root_.AlgebraicGeometry.Spec (CommRingCat.of (awayRing f))).Opens)) :=
  specSectionsModule (CommRingCat.of (awayRing f))
    ((_root_.AlgebraicGeometry.tilde M).restrict (awaySpecMap f)) ⊤

private noncomputable local instance instModuleRRestrictTop :
    Module R Γ((_root_.AlgebraicGeometry.tilde M).restrict (awaySpecMap f),
      (⊤ : (_root_.AlgebraicGeometry.Spec (CommRingCat.of (awayRing f))).Opens)) :=
  Module.compHom _ (algebraMap R (awayRing f))

private noncomputable local instance instIsScalarTowerRestrictTop :
    IsScalarTower R (awayRing f)
      Γ((_root_.AlgebraicGeometry.tilde M).restrict (awaySpecMap f),
        (⊤ : (_root_.AlgebraicGeometry.Spec (CommRingCat.of (awayRing f))).Opens)) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

private noncomputable def restrictAppLinearEquivR :
    Γ((_root_.AlgebraicGeometry.tilde M).restrict (awaySpecMap f), ⊤) ≃ₗ[R]
      Γ(_root_.AlgebraicGeometry.tilde M, awaySpecMap f ''ᵁ ⊤) where
  toFun := (Scheme.Modules.restrictAppIso
    (awaySpecMap f) (_root_.AlgebraicGeometry.tilde M) ⊤).hom
  invFun := (Scheme.Modules.restrictAppIso
    (awaySpecMap f) (_root_.AlgebraicGeometry.tilde M) ⊤).inv
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := (Scheme.Modules.restrictAppIso
    (awaySpecMap f) (_root_.AlgebraicGeometry.tilde M) ⊤).hom.hom.map_add x y
  map_smul' r x := Scheme.Modules.restrictAppIso_smul_Spec (awayMap f) r x

private noncomputable def toRestrictTop :
    ModuleCat.of R M ⟶
      ModuleCat.of R
        Γ((_root_.AlgebraicGeometry.tilde M).restrict (awaySpecMap f), ⊤) :=
  ModuleCat.ofHom <|
    (restrictAppLinearEquivR M f).symm.toLinearMap.comp
      (_root_.AlgebraicGeometry.tilde.toOpen M (awaySpecMap f ''ᵁ ⊤)).hom

private noncomputable local instance instIsLocalizedModuleToRestrictTop :
    IsLocalizedModule.Away f (toRestrictTop M f).hom := by
  dsimp [toRestrictTop]
  have : IsLocalizedModule.Away f
      (_root_.AlgebraicGeometry.tilde.toOpen M (awaySpecMap f ''ᵁ ⊤)).hom := by
    rw [show awaySpecMap f ''ᵁ
      (⊤ : (_root_.AlgebraicGeometry.Spec (CommRingCat.of (awayRing f))).Opens) =
        PrimeSpectrum.basicOpen f by
      simp [awaySpecMap, awayMap, awayRing]
      rfl]
    infer_instance
  exact IsLocalizedModule.of_linearEquiv (.powers f)
    (_root_.AlgebraicGeometry.tilde.toOpen M (awaySpecMap f ''ᵁ ⊤)).hom
    (restrictAppLinearEquivR M f).symm

private noncomputable def localizedEquivRestrictTop :
    LocalizedModule.Away f M ≃ₗ[awayRing f]
      Γ((_root_.AlgebraicGeometry.tilde M).restrict (awaySpecMap f), ⊤) :=
  (IsLocalizedModule.linearEquiv (.powers f)
    (LocalizedModule.mkLinearMap (.powers f) M)
    (toRestrictTop M f).hom).extendScalarsOfIsLocalization (.powers f) (awayRing f)

private noncomputable local instance instQuasicoherentRestrict :
    ((_root_.AlgebraicGeometry.tilde M).restrict (awaySpecMap f)).IsQuasicoherent :=
  Scheme.Modules.isQuasicoherent_restrictFunctor
    (awaySpecMap f) (_root_.AlgebraicGeometry.tilde M)

private noncomputable local instance instIsIsoFromTildeRestrict :
    IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of (awayRing f))
      ((_root_.AlgebraicGeometry.tilde M).restrict (awaySpecMap f))) :=
  Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent
    ((_root_.AlgebraicGeometry.tilde M).restrict (awaySpecMap f))

/-- Tilde commutes with localization to a principal open: the tilde of the localized module is
isomorphic to the restriction of the original tilde sheaf along `Spec R[1/f] ⟶ Spec R`. -/
noncomputable def localizedTildeRestrictIso :
    _root_.AlgebraicGeometry.tilde (R := CommRingCat.of (awayRing f))
        (ModuleCat.of (awayRing f) (LocalizedModule.Away f M)) ≅
      (_root_.AlgebraicGeometry.tilde M).restrict (awaySpecMap f) :=
  (_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of (awayRing f))).mapIso
      (localizedEquivRestrictTop M f).toModuleIso ≪≫
    @asIso _ _ _ _
      (Scheme.Modules.fromTildeΓ (R := CommRingCat.of (awayRing f))
        ((_root_.AlgebraicGeometry.tilde M).restrict (awaySpecMap f)))
      (instIsIsoFromTildeRestrict M f)

end AffineTilde

/-- The basic open of `Spec R` associated to `r`, expressed in the scheme's own type of opens.
This avoids hiding the comparison between the scheme topology and the raw prime spectrum. -/
noncomputable abbrev specBasicOpen (R : CommRingCat.{u}) (r : R) :
    (_root_.AlgebraicGeometry.Spec R).Opens :=
  PrimeSpectrum.basicOpen r

/-- The precise affine localization input: whenever `Mₙ` is free on `D(r)`, the restriction
of `tilde M` to that basic open is the free rank-one sheaf. -/
def BasicOpenTildeTriviality
    (R : CommRingCat.{u}) (M : ModuleCat.{u} R) : Prop :=
  Module.Invertible R M →
  ∀ r : R, [Module.Free (Localization.Away r) (LocalizedModule.Away r M)] →
    Nonempty
      (_root_.SheafOfModules.free.{u, u, u}
          (R := (_root_.AlgebraicGeometry.Spec R).ringCatSheaf.over (specBasicOpen R r))
          PUnit.{u + 1} ≅
        (_root_.AlgebraicGeometry.tilde M).over (specBasicOpen R r))

/-- The basic-open tilde comparison, uniformly for rings and modules in one universe. -/
def UniversalBasicOpenTildeTriviality : Prop :=
  ∀ (R : CommRingCat.{u}) (M : ModuleCat.{u} R), BasicOpenTildeTriviality R M

namespace AffineTilde

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (f : R)

/-- If the localization of an invertible module at `f` is free, its tilde sheaf on
`Spec R[1/f]` is the free rank-one sheaf and hence trivializes the restricted original
sheaf. -/
noncomputable def localizedTildeFreeIso [Module.Invertible R M]
    [Module.Free (Localization.Away f) (LocalizedModule.Away f M)] :
    _root_.SheafOfModules.free
        (R := (_root_.AlgebraicGeometry.Spec
          (CommRingCat.of (Localization.Away f))).ringCatSheaf) PUnit.{u + 1} ≅
      (_root_.AlgebraicGeometry.tilde M).restrict
        (_root_.AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap R (Localization.Away f)))) := by
  let e : LocalizedModule.Away f M ≃ₗ[Localization.Away f] Localization.Away f :=
    (Module.Invertible.free_iff_linearEquiv.mp inferInstance).some
  let e' := e.trans (Finsupp.uniqueLinearEquiv
    (Localization.Away f) (Localization.Away f)
      (PUnit.unit : PUnit.{u + 1})).symm
  exact (_root_.AlgebraicGeometry.tildeFinsupp PUnit).symm ≪≫
    (_root_.AlgebraicGeometry.tilde.functor
      (CommRingCat.of (Localization.Away f))).mapIso e'.symm.toModuleIso ≪≫
    localizedTildeRestrictIso M f

private noncomputable def freePUnitIso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {S : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    _root_.SheafOfModules.free (R := S) PUnit.{u + 1} ≅
      _root_.SheafOfModules.unit S :=
  Limits.coproductUniqueIso (fun _ : PUnit.{u + 1} ↦
    _root_.SheafOfModules.unit S)

/-- The checked basic-open trivialization required by Tau Ceti's local definition of an
invertible sheaf. -/
noncomputable def basicOpenTrivialization [Module.Invertible R M]
    [Module.Free (Localization.Away f) (LocalizedModule.Away f M)] :
    _root_.SheafOfModules.free
        (R := (_root_.AlgebraicGeometry.Spec R).ringCatSheaf.over (specBasicOpen R f))
        PUnit.{u + 1} ≅
      (_root_.AlgebraicGeometry.tilde M).over (specBasicOpen R f) := by
  let U : (_root_.AlgebraicGeometry.Spec R).Opens := PrimeSpectrum.basicOpen f
  let A : CommRingCat.{u} := .of (Localization.Away f)
  let j : _root_.AlgebraicGeometry.Spec A ⟶ _root_.AlgebraicGeometry.Spec R :=
    _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R A))
  let b : U.toScheme ≅ _root_.AlgebraicGeometry.Spec A :=
    _root_.AlgebraicGeometry.basicOpenIsoSpecAway f
  letI : IsOpenImmersion U.ι := inferInstance
  let eU : _root_.SheafOfModules.free
      (R := U.toScheme.ringCatSheaf) PUnit.{u + 1} ≅
      (_root_.AlgebraicGeometry.tilde M).restrict U.ι :=
    freePUnitIso ≪≫
      (Scheme.Modules.restrictUnitIso b.hom).symm ≪≫
      (Scheme.Modules.restrictFunctor b.hom).mapIso freePUnitIso.symm ≪≫
      (Scheme.Modules.restrictFunctor b.hom).mapIso (localizedTildeFreeIso M f) ≪≫
      ((Scheme.Modules.restrictFunctorComp b.hom j).app
        (_root_.AlgebraicGeometry.tilde M)).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr (by
        dsimp only [b, j, U, A]
        simp)).app (_root_.AlgebraicGeometry.tilde M)
  let eMapped : (Scheme.Modules.overEquiv U).functor.obj
      (_root_.SheafOfModules.free
        (R := (_root_.AlgebraicGeometry.Spec R).ringCatSheaf.over U) PUnit.{u + 1}) ≅
      (Scheme.Modules.overEquiv U).functor.obj
        ((_root_.AlgebraicGeometry.tilde M).over U) :=
    (Scheme.Modules.overEquiv U).functor.mapIso freePUnitIso ≪≫
      U.sheafOfModulesEquivOverUnit
        (_root_.AlgebraicGeometry.Spec R).ringCatSheaf ≪≫
      freePUnitIso.symm ≪≫ eU ≪≫
      ((Scheme.Modules.overFunctorEquiv U).app
        (_root_.AlgebraicGeometry.tilde M)).symm
  exact (Scheme.Modules.overEquiv U).functor.preimageIso eMapped

end AffineTilde

/-- The pinned Mathlib and Tau Ceti APIs prove the universal basic-open tilde comparison. -/
theorem universalBasicOpenTildeTriviality : UniversalBasicOpenTildeTriviality.{u} :=
  fun _ M hM r _ ↦ by
    letI := hM
    exact ⟨AffineTilde.basicOpenTrivialization M r⟩

/-- Finite basic-open freeness of an invertible module and the exact local restriction
comparison imply that its tilde sheaf is invertible. -/
theorem tilde_isInvertible_of_basicOpenTriviality
    (R : CommRingCat.{u}) (M : ModuleCat.{u} R)
    [Module.Invertible R M] (h : BasicOpenTildeTriviality R M) :
    TauCeti.SheafOfModules.IsInvertible
      (R := (_root_.AlgebraicGeometry.Spec R).ringCatSheaf)
      (_root_.AlgebraicGeometry.tilde M) := by
  obtain ⟨s, hs, hfree⟩ :=
    Module.Invertible.exists_finset_free_localization (R := R) (M := M)
  apply TauCeti.SheafOfModules.LocalTrivializations.isInvertible
  let t : TauCeti.SheafOfModules.LocalTrivializations.{u, u, u}
      (_root_.AlgebraicGeometry.tilde M) :=
    { I := s
      X := fun r ↦ specBasicOpen R r.1
      coversTop := by
        rw [Opens.coversTop_iff]
        apply IsOpenCover.mk
        change (⨆ r : s, PrimeSpectrum.basicOpen r.1 :
          TopologicalSpace.Opens (PrimeSpectrum R)) = ⊤
        rw [PrimeSpectrum.iSup_basicOpen_eq_top_iff]
        simpa only [Subtype.range_coe_subtype, Finset.setOf_mem] using hs
      iso := fun r ↦ by
        letI := hfree r.1 r.2
        exact (h inferInstance r.1).some }
  exact t

/-- The exact basic-open localization theorem entails the formerly bundled global tilde
invertibility statement. -/
theorem UniversalBasicOpenTildeTriviality.toUniversalTildeInvertibility
    (h : UniversalBasicOpenTildeTriviality.{u}) : UniversalTildeInvertibility.{u} :=
  fun R M _ ↦ tilde_isInvertible_of_basicOpenTriviality R M (h R M)

/-- Tilde of every invertible module is an invertible sheaf. This is now unconditional in the
pinned dependency graph. -/
theorem universalTildeInvertibility : UniversalTildeInvertibility.{u} :=
  universalBasicOpenTildeTriviality.toUniversalTildeInvertibility

/-- The universe-local form of unconditional tilde invertibility. -/
theorem tildeInvertibility (R : Type u) [CommRing R] : TildeInvertibility R :=
  fun M _ ↦ universalTildeInvertibility (CommRingCat.of R) M

namespace PicardComparison

variable {X : Scheme.{u}} (hX : PicardComparison X)

include hX

/-- The full comparison contains the exact forward tensor-inverse comparison. -/
theorem tensorInverseComparison : TensorInverseComparison X :=
  fun M hM ↦ IsTensorInvertible.exists_tensorInverse ((hX M).mp hM)

/-- The full comparison contains the reverse local-triviality comparison. -/
theorem tensorUnitLocalTriviality : TensorUnitLocalTriviality X :=
  fun M hM ↦ (hX M).mpr hM

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

/-- The full Picard comparison is exactly its forward tensor-inverse component together with
the reverse local-triviality component. -/
theorem picardComparison_of_components {X : Scheme.{u}}
    (hforward : TensorInverseComparison X)
    (hreverse : TensorUnitLocalTriviality X) : PicardComparison X :=
  fun M ↦ ⟨fun hM ↦ hforward.isTensorInvertible hM, hreverse M⟩

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

/-- Exactness at divisors already proves that every principal divisor has trivial Picard class. -/
lemma principalTrivial_of_principalKernel
    (S : WeilDivisor.OrderSystem Y G)
    (toPic : WeilDivisor Y →+ PicardGroup X)
    (hker : HasPrincipalKernel S toPic) :
    PrincipalTrivial S toPic := by
  intro g
  rw [← AddMonoidHom.mem_ker, hker]
  exact S.principalDivisor_mem_principalSubgroup g

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

/-- The strongest general divisor-class/Picard equivalence: a homomorphism with exactly
principal kernel and hitting every Picard class descends to an equivalence. Principal
triviality is a consequence of the kernel equality, not an additional assumption. -/
noncomputable def classEquivPicard
    (S : WeilDivisor.OrderSystem Y G)
    (toPic : WeilDivisor Y →+ PicardGroup X)
    (hker : HasPrincipalKernel S toPic)
    (hsurjective : Function.Surjective toPic) :
    ClassEquivalence S X :=
  let hprincipal := principalTrivial_of_principalKernel S toPic hker
  AddEquiv.ofBijective (classToPic S toPic hprincipal)
    ⟨classToPic_injective S toPic hprincipal hker,
      classToPic_surjective S toPic hprincipal hsurjective⟩

@[simp]
lemma classEquivPicard_divisorClass
    (S : WeilDivisor.OrderSystem Y G)
    (toPic : WeilDivisor Y →+ PicardGroup X)
    (hker : HasPrincipalKernel S toPic)
    (hsurjective : Function.Surjective toPic) (D : WeilDivisor Y) :
    classEquivPicard S toPic hker hsurjective (S.divisorClass D) = toPic D :=
  classToPic_divisorClass S toPic (principalTrivial_of_principalKernel S toPic hker) D

/-- An exact scheme-level divisor-class/Picard dictionary for an order system. Besides the class
map and its exactness, it records chosen invertible-sheaf representatives and the comparison
between Tau Ceti's local rank-one predicate and AINTLIB's tensor-unit Picard group. The data does
not assert a particular affine-chart normalization of the chosen correspondence. -/
structure Dictionary (S : WeilDivisor.OrderSystem Y G) (X : Scheme.{u}) where
  /-- Every locally free rank-one sheaf has a tensor inverse and hence a Picard class. -/
  comparison : TensorInverseComparison X
  /-- The additive Picard class associated to a Weil divisor. -/
  divisorToPic : WeilDivisor Y →+ PicardGroup X
  /-- An invertible-sheaf representative of the line bundle associated to a divisor. -/
  lineBundle : WeilDivisor Y → InvertibleSheaf X
  /-- The chosen line bundle represents the specified divisor Picard class. -/
  lineBundle_toPic (D : WeilDivisor Y) :
    Additive.ofMul (comparison.toPic (lineBundle D)) = divisorToPic D
  /-- Only principal divisors have trivial Picard class. -/
  principalKernel : HasPrincipalKernel S divisorToPic
  /-- Every scheme Picard class is represented by a divisor. -/
  surjective : Function.Surjective divisorToPic

namespace Dictionary

variable {S : WeilDivisor.OrderSystem Y G}
variable (d : Dictionary S X)

/-- A full Picard comparison and a divisor-class/Picard equivalence canonically supply all data
of an exact dictionary. The line bundle of `D` is the chosen invertible-sheaf representative of
the image of `[D]`; exactness and surjectivity are inherited from the quotient equivalence. -/
noncomputable def ofClassEquivalence
    (hX : PicardComparison X) (e : ClassEquivalence S X) :
    Dictionary S X where
  comparison := hX.tensorInverseComparison
  divisorToPic := e.toAddMonoidHom.comp S.divisorClass
  lineBundle D := hX.representative (Additive.toMul (e (S.divisorClass D)))
  lineBundle_toPic D := by
    change hX.tensorInverseComparison.toPic
        (hX.representative (Additive.toMul (e (S.divisorClass D)))) =
      Additive.toMul (e (S.divisorClass D))
    apply Units.ext
    rw [TensorInverseComparison.toPic_val]
    exact toSkeleton_fromSkeleton_obj _
  principalKernel := by
    apply AddSubgroup.ext
    intro D
    rw [AddMonoidHom.mem_ker]
    change e (S.divisorClass D) = 0 ↔ D ∈ S.principalSubgroup
    constructor
    · intro h
      rw [← S.divisorClass_eq_zero_iff]
      exact e.injective (by simpa using h)
    · intro h
      rw [← S.divisorClass_eq_zero_iff] at h
      simp [h]
  surjective := by
    intro p
    obtain ⟨c, rfl⟩ := e.surjective p
    obtain ⟨D, rfl⟩ := S.divisorClass_surjective c
    exact ⟨D, rfl⟩

/-- Principal divisors have trivial Picard class, as a checked consequence of exactness at the
divisor term. -/
lemma principalTrivial : PrincipalTrivial S d.divisorToPic :=
  principalTrivial_of_principalKernel S d.divisorToPic d.principalKernel

/-- The line bundle attached by an exact dictionary to a principal divisor is isomorphic to the
globally trivial line bundle. This follows from exactness, compatibility with the Picard class,
and the fact that equality in the skeleton is precisely existence of an isomorphism. -/
lemma lineBundle_principal_iso_trivial (g : G) :
    Nonempty ((d.lineBundle (S.principalDivisor g)).obj ≅
      (InvertibleSheaf.trivial X).obj) := by
  apply toSkeleton_eq_toSkeleton_iff.mp
  have hclass := d.lineBundle_toPic (S.principalDivisor g)
  rw [d.principalTrivial g] at hclass
  change d.comparison.toPic (d.lineBundle (S.principalDivisor g)) = 1 at hclass
  have hpic :
      d.comparison.toPic (d.lineBundle (S.principalDivisor g)) =
        d.comparison.toPic (InvertibleSheaf.trivial X) :=
    hclass.trans d.comparison.toPic_trivial.symm
  exact congrArg Units.val hpic

/-- Divisor addition is represented by tensor product of the chosen line bundles, up to the
isomorphism appropriate for chosen representatives. -/
lemma lineBundle_add_iso (D E : WeilDivisor Y) :
    Nonempty ((d.lineBundle (D + E)).obj ≅
      (d.lineBundle D).obj ⊗ (d.lineBundle E).obj) := by
  apply toSkeleton_eq_toSkeleton_iff.mp
  rw [Skeleton.toSkeleton_tensorObj]
  have hp :
      d.comparison.toPic (d.lineBundle (D + E)) =
        d.comparison.toPic (d.lineBundle D) *
          d.comparison.toPic (d.lineBundle E) := by
    apply Additive.ofMul.injective
    change Additive.ofMul (d.comparison.toPic (d.lineBundle (D + E))) =
      Additive.ofMul (d.comparison.toPic (d.lineBundle D)) +
        Additive.ofMul (d.comparison.toPic (d.lineBundle E))
    rw [d.lineBundle_toPic, d.lineBundle_toPic, d.lineBundle_toPic, map_add]
  calc
    toSkeleton (d.lineBundle (D + E)).obj =
        (d.comparison.toPic (d.lineBundle (D + E))).val :=
      d.comparison.toPic_val _ |>.symm
    _ = (d.comparison.toPic (d.lineBundle D) *
          d.comparison.toPic (d.lineBundle E)).val := congrArg Units.val hp
    _ = (d.comparison.toPic (d.lineBundle D)).val *
          (d.comparison.toPic (d.lineBundle E)).val := Units.val_mul _ _
    _ = toSkeleton (d.lineBundle D).obj * toSkeleton (d.lineBundle E).obj := by
      rw [d.comparison.toPic_val, d.comparison.toPic_val]

/-- The chosen line bundles of linearly equivalent divisors are isomorphic. -/
lemma lineBundle_iso_of_linearlyEquivalent {D E : WeilDivisor Y}
    (h : S.LinearlyEquivalent D E) :
    Nonempty ((d.lineBundle D).obj ≅ (d.lineBundle E).obj) := by
  apply toSkeleton_eq_toSkeleton_iff.mp
  have hker : D - E ∈ d.divisorToPic.ker := by
    rw [d.principalKernel]
    exact h
  have hp : d.divisorToPic D = d.divisorToPic E := by
    apply sub_eq_zero.mp
    simpa only [map_sub] using (AddMonoidHom.mem_ker.mp hker)
  have hpUnits :
      d.comparison.toPic (d.lineBundle D) =
        d.comparison.toPic (d.lineBundle E) := by
    apply Additive.ofMul.injective
    rw [d.lineBundle_toPic, d.lineBundle_toPic, hp]
  exact congrArg Units.val hpUnits

/-- The exact dictionary detects linear equivalence on the chosen divisor line bundles: two
such bundles are isomorphic precisely when their divisors differ by a principal divisor. -/
theorem nonempty_lineBundle_iso_iff_linearlyEquivalent (D E : WeilDivisor Y) :
    Nonempty ((d.lineBundle D).obj ≅ (d.lineBundle E).obj) ↔
      S.LinearlyEquivalent D E := by
  constructor
  · intro h
    have hs : toSkeleton (d.lineBundle D).obj = toSkeleton (d.lineBundle E).obj :=
      toSkeleton_eq_toSkeleton_iff.mpr h
    have hpUnits :
        d.comparison.toPic (d.lineBundle D) =
          d.comparison.toPic (d.lineBundle E) := by
      apply Units.ext
      simpa only [d.comparison.toPic_val] using hs
    have hp : d.divisorToPic D = d.divisorToPic E := by
      rw [← d.lineBundle_toPic D, ← d.lineBundle_toPic E, hpUnits]
    rw [S.linearlyEquivalent_iff, ← d.principalKernel, AddMonoidHom.mem_ker, map_sub,
      hp, sub_self]
  · exact d.lineBundle_iso_of_linearlyEquivalent

include d

/-- Surjectivity of the divisor map and the chosen line-bundle representatives force the
reverse Picard comparison: every tensor-unit sheaf is locally free of rank one. Thus a global
dictionary need not store that comparison as an independent hypothesis. -/
theorem tensorUnitLocalTriviality : TensorUnitLocalTriviality X := by
  intro M hM
  let p : Scheme.Pic X := by
    rw [IsTensorInvertible] at hM
    exact hM.unit
  obtain ⟨D, hD⟩ := d.surjective (Additive.ofMul p)
  have hp : d.comparison.toPic (d.lineBundle D) = p := by
    apply Additive.ofMul.injective
    rw [d.lineBundle_toPic, hD]
  have hs : toSkeleton (d.lineBundle D).obj = toSkeleton M := by
    rw [← d.comparison.toPic_val, hp]
    exact IsUnit.unit_spec hM
  obtain ⟨e⟩ := toSkeleton_eq_toSkeleton_iff.mp hs
  exact (SheafOfModules.isInvertible X).prop_of_iso e (d.lineBundle D).property

/-- An exact divisor-line-bundle dictionary supplies the full equivalence between Tau Ceti's
local rank-one predicate and AINTLIB's tensor-unit predicate. -/
theorem picardComparison : PicardComparison X :=
  picardComparison_of_components d.comparison d.tensorUnitLocalTriviality

/-- The divisor-class/Picard equivalence supplied by an exact dictionary. -/
noncomputable def classEquivalence : ClassEquivalence S X :=
  classEquivPicard S d.divisorToPic d.principalKernel d.surjective

@[simp]
lemma classEquivalence_divisorClass (D : WeilDivisor Y) :
    d.classEquivalence (S.divisorClass D) = d.divisorToPic D :=
  classEquivPicard_divisorClass S d.divisorToPic d.principalKernel d.surjective D

omit d in
/-- The divisor-class equivalence recovered from the dictionary constructed by
`ofClassEquivalence` is the original equivalence. -/
@[simp]
theorem classEquivalence_ofClassEquivalence
    (hX : PicardComparison X) (e : ClassEquivalence S X) :
    (ofClassEquivalence hX e).classEquivalence = e := by
  apply AddEquiv.ext
  intro c
  obtain ⟨D, rfl⟩ := S.divisorClass_surjective c
  rw [classEquivalence_divisorClass]
  rfl

omit d in
/-- Existence of an exact dictionary is equivalent to precisely its two irreducible global
outputs: the full invertible-sheaf/Picard comparison and an equivalence from divisor classes to
the scheme Picard group. All chosen divisor line bundles and their compatibility are then
constructed by `ofClassEquivalence`. -/
theorem nonempty_iff_picardComparison_and_classEquivalence :
    Nonempty (Dictionary S X) ↔
      PicardComparison X ∧ Nonempty (ClassEquivalence S X) := by
  constructor
  · rintro ⟨d⟩
    exact ⟨d.picardComparison, ⟨d.classEquivalence⟩⟩
  · rintro ⟨hX, ⟨e⟩⟩
    exact ⟨ofClassEquivalence hX e⟩

end Dictionary

end DivisorPicard

namespace AffineDedekind

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open TauCeti.AlgebraicGeometry.WeilDivisor
open scoped TensorProduct

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

/-- The canonical tilde-induced homomorphism from affine Dedekind divisor classes to AINTLIB's
scheme Picard group. -/
noncomputable def classToSchemePic :
    (WeilDivisor.OrderSystem.ofDedekindDomain R K).ClassGroup →+
      PicardGroup (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)) :=
  (AffineTilde.modulePicToSchemePicAdd R).comp
    (classEquivPicard R K).toAddMonoidHom

/-- Affine Dedekind divisor classes inject canonically into the scheme Picard group. -/
theorem classToSchemePic_injective :
    Function.Injective (classToSchemePic R K) :=
  (AffineTilde.modulePicToSchemePicAdd_injective R).comp
    (classEquivPicard R K).injective

/-- The strongest unconditional affine divisor-class/scheme-Picard equivalence currently
available: divisor classes are equivalent to the range of their canonical tilde realization. -/
noncomputable def classEquivSchemePicRange :
    (WeilDivisor.OrderSystem.ofDedekindDomain R K).ClassGroup ≃+
      (classToSchemePic R K).range :=
  AddEquiv.ofBijective (classToSchemePic R K).rangeRestrict
    ⟨fun _ _ h ↦ classToSchemePic_injective R K (congrArg Subtype.val h), by
      rintro ⟨_, ⟨x, rfl⟩⟩
      exact ⟨x, rfl⟩⟩

/-- The Picard class of the invertible module `O(D)` associated to an affine Dedekind divisor. -/
noncomputable def divisorToPic :
    WeilDivisor (HeightOneSpectrum R) →+ Additive (CommRing.Pic R) :=
  classEquivPicard R K |>.toAddMonoidHom.comp
    (WeilDivisor.OrderSystem.ofDedekindDomain R K).divisorClass

/-- The canonical affine Dedekind divisor-to-scheme-Picard homomorphism. It is the descent-ready
scheme-level realization of the module line-bundle class. -/
noncomputable def divisorToSchemePic :
    WeilDivisor (HeightOneSpectrum R) →+
      PicardGroup (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)) :=
  (classToSchemePic R K).comp
    (WeilDivisor.OrderSystem.ofDedekindDomain R K).divisorClass

@[simp]
lemma divisorToSchemePic_apply (D : WeilDivisor (HeightOneSpectrum R)) :
    divisorToSchemePic R K D =
      AffineTilde.modulePicToSchemePicAdd R (divisorToPic R K D) :=
  rfl

@[simp]
lemma divisorToPic_principalDivisor (g : Additive Kˣ) :
    divisorToPic R K
      ((WeilDivisor.OrderSystem.ofDedekindDomain R K).principalDivisor g) = 0 := by
  rw [divisorToPic, AddMonoidHom.comp_apply,
    WeilDivisor.OrderSystem.divisorClass_principalDivisor, map_zero]

/-- Principal divisors give the zero scheme-Picard class. -/
lemma divisorToSchemePic_principalDivisor (g : Additive Kˣ) :
    divisorToSchemePic R K
      ((WeilDivisor.OrderSystem.ofDedekindDomain R K).principalDivisor g) = 0 := by
  rw [divisorToSchemePic_apply, divisorToPic_principalDivisor, map_zero]

/-- The kernel of the canonical divisor-to-scheme-Picard map consists exactly of principal
divisors. Thus its factorization through `classToSchemePic` is an honest descent to divisor
classes, with no unproved surjectivity claim. -/
theorem divisorToSchemePic_kernel :
    (divisorToSchemePic R K).ker =
      (WeilDivisor.OrderSystem.ofDedekindDomain R K).principalSubgroup := by
  apply AddSubgroup.ext
  intro D
  rw [AddMonoidHom.mem_ker]
  constructor
  · intro h
    rw [divisorToSchemePic, AddMonoidHom.comp_apply] at h
    rw [← (WeilDivisor.OrderSystem.ofDedekindDomain R K).divisorClass_eq_zero_iff]
    apply classToSchemePic_injective R K
    simpa using h
  · intro h
    rw [← (WeilDivisor.OrderSystem.ofDedekindDomain R K).divisorClass_eq_zero_iff] at h
    simp [divisorToSchemePic, h]

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

/-- The chosen affine line-bundle module carries divisor addition to tensor product, up to
linear equivalence. -/
lemma nonempty_lineBundleModule_add_equiv (D E : WeilDivisor (HeightOneSpectrum R)) :
    Nonempty (lineBundleModule R K (D + E) ≃ₗ[R]
      (lineBundleModule R K D ⊗[R] lineBundleModule R K E)) := by
  rw [← CommRing.Pic.mk_eq_mk_iff, lineBundleModule_picClass,
    CommRing.Pic.mk_tensor, lineBundleModule_picClass, lineBundleModule_picClass]
  change Additive.toMul (divisorToPic R K (D + E)) =
    Additive.toMul (divisorToPic R K D) * Additive.toMul (divisorToPic R K E)
  rw [map_add]
  rfl

/-- Two chosen affine line-bundle modules are linearly equivalent exactly when the underlying
divisors are linearly equivalent. -/
lemma nonempty_lineBundleModule_equiv_iff_linearlyEquivalent
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    Nonempty (lineBundleModule R K D ≃ₗ[R] lineBundleModule R K E) ↔
      (WeilDivisor.OrderSystem.ofDedekindDomain R K).LinearlyEquivalent D E := by
  rw [← CommRing.Pic.mk_eq_mk_iff, lineBundleModule_picClass,
    lineBundleModule_picClass]
  change divisorToPic R K D = divisorToPic R K E ↔ _
  constructor
  · intro h
    rw [divisorToPic, AddMonoidHom.comp_apply] at h
    exact (WeilDivisor.OrderSystem.ofDedekindDomain R K).divisorClass_eq_iff.mp
      ((classEquivPicard R K).injective h)
  · intro h
    rw [divisorToPic, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply]
    exact congrArg (classEquivPicard R K)
      ((WeilDivisor.OrderSystem.ofDedekindDomain R K).divisorClass_eq_iff.mpr h)

/-- A principal divisor has a trivial affine line-bundle module. -/
lemma nonempty_lineBundleModule_principal_equiv (g : Additive Kˣ) :
    Nonempty
      (lineBundleModule R K
          ((WeilDivisor.OrderSystem.ofDedekindDomain R K).principalDivisor g) ≃ₗ[R] R) := by
  rw [← CommRing.Pic.mk_eq_one_iff, lineBundleModule_picClass,
    lineBundleClass_principalDivisor]

/-- The line bundle `O(D)` on the affine Dedekind scheme. -/
noncomputable def lineBundle (D : WeilDivisor (HeightOneSpectrum R)) :
    InvertibleSheaf (_root_.AlgebraicGeometry.Spec (.of R)) :=
  ⟨_root_.AlgebraicGeometry.tilde (ModuleCat.of R (lineBundleModule R K D)),
    tildeInvertibility R (ModuleCat.of R (lineBundleModule R K D))⟩

/-- The canonical scheme-Picard class of `O(D)` is represented by the actual tilde line bundle
constructed above. -/
lemma divisorToSchemePic_val (D : WeilDivisor (HeightOneSpectrum R)) :
    (Additive.toMul (divisorToSchemePic R K D)).val =
      toSkeleton (lineBundle R K D).obj := by
  rw [divisorToSchemePic_apply]
  change (AffineTilde.modulePicToSchemePicClass R (lineBundleClass R K D)).val = _
  rw [AffineTilde.modulePicToSchemePicClass_val]
  rfl

/-- Divisor addition is carried to the actual sheaf tensor product by the chosen affine line
bundles. This strengthens the module-level formula to a checked line-bundle isomorphism. -/
lemma nonempty_lineBundle_add_iso (D E : WeilDivisor (HeightOneSpectrum R)) :
    Nonempty
      ((lineBundle R K (D + E)).obj ≅
        (lineBundle R K D).obj ⊗ (lineBundle R K E).obj) := by
  let e : lineBundleModule R K (D + E) ≃ₗ[R]
      (lineBundleModule R K D ⊗[R] lineBundleModule R K E) :=
    (nonempty_lineBundleModule_add_equiv R K D E).some
  exact ⟨(_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of R)).mapIso e.toModuleIso ≪≫
    (AffineTilde.tildeTensorIso R
      (lineBundleModule R K D) (lineBundleModule R K E)).symm⟩

/-- The line bundle of a principal divisor is isomorphic to the trivial line bundle. -/
lemma nonempty_lineBundle_principal_iso_trivial
    (g : Additive Kˣ) :
    Nonempty
      ((lineBundle R K
          ((WeilDivisor.OrderSystem.ofDedekindDomain R K).principalDivisor g)).obj ≅
        (InvertibleSheaf.trivial (_root_.AlgebraicGeometry.Spec (.of R))).obj) := by
  let e : lineBundleModule R K
      ((WeilDivisor.OrderSystem.ofDedekindDomain R K).principalDivisor g) ≃ₗ[R] R :=
    (nonempty_lineBundleModule_principal_equiv R K g).some
  let e' := e.trans (Finsupp.uniqueLinearEquiv R R PUnit.unit).symm
  exact ⟨(_root_.AlgebraicGeometry.tilde.functor (.of R)).mapIso e'.toModuleIso ≪≫
    _root_.AlgebraicGeometry.tildeFinsupp PUnit⟩

/-- Isomorphism of the chosen affine tilde line bundles detects linear equivalence exactly. The
reverse implication uses full faithfulness of Mathlib's tilde functor. -/
theorem nonempty_lineBundle_iso_iff_linearlyEquivalent
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    Nonempty ((lineBundle R K D).obj ≅ (lineBundle R K E).obj) ↔
      (WeilDivisor.OrderSystem.ofDedekindDomain R K).LinearlyEquivalent D E := by
  constructor
  · rintro ⟨e⟩
    let e' := _root_.AlgebraicGeometry.tilde.fullyFaithfulFunctor.preimageIso e
    exact (nonempty_lineBundleModule_equiv_iff_linearlyEquivalent R K D E).mp
      ⟨e'.toLinearEquiv⟩
  · intro h
    obtain ⟨e⟩ :=
      (nonempty_lineBundleModule_equiv_iff_linearlyEquivalent R K D E).mpr h
    exact ⟨(_root_.AlgebraicGeometry.tilde.functor (.of R)).mapIso e.toModuleIso⟩

/-- Because affine Dedekind divisor classes are already identified with Mathlib's module Picard
group, an exact scheme-level dictionary exists precisely when the full local-rank-one/tensor-unit
comparison and an additive module-Picard/scheme-Picard equivalence do. The canonical tilde map
above supplies an injection; this existence characterization does not assert that particular map
is surjective. -/
theorem nonempty_dictionary_iff_picardComparison_and_modulePicardEquivalence :
    Nonempty (DivisorPicard.Dictionary
      (WeilDivisor.OrderSystem.ofDedekindDomain R K)
      (_root_.AlgebraicGeometry.Spec (.of R))) ↔
      PicardComparison (_root_.AlgebraicGeometry.Spec (.of R)) ∧
        Nonempty (Additive (CommRing.Pic R) ≃+
          PicardGroup (_root_.AlgebraicGeometry.Spec (.of R))) := by
  rw [DivisorPicard.Dictionary.nonempty_iff_picardComparison_and_classEquivalence]
  constructor
  · rintro ⟨hX, ⟨e⟩⟩
    exact ⟨hX, ⟨(classEquivPicard R K).symm.trans e⟩⟩
  · rintro ⟨hX, ⟨e⟩⟩
    exact ⟨hX, ⟨(classEquivPicard R K).trans e⟩⟩

end AffineDedekind

end MazurTorsion.AlgebraicGeometry
