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
with AINTLIB's scheme Picard group remains factored into its exact forward and reverse components
rather than hidden behind a stronger claim than the current library proves. A final affine
existence theorem characterizes that boundary exactly by the full Picard comparison and an
additive equivalence between the module and scheme Picard groups. The local algebra identifying
the tensor of two localized modules with the localization of their tensor is also checked; a
strong monoidal tilde comparison still requires assembling those maps at the presheaf level.
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

end TensorLocalization

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
group, an exact scheme-level dictionary exists precisely when the two remaining comparisons do:
local rank-one sheaves versus tensor units, and the module Picard group versus AINTLIB's scheme
Picard group. The latter is only an abstract additive equivalence here; no canonical tilde
compatibility is claimed. -/
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
