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

Unconditionally, the current dependency graph supports the class-level dictionary between the
divisor class group of an affine Dedekind curve and Mathlib's module Picard group. The resulting
equivalence has the standard sign: the checked representative formula below sends the divisor
of a fractional ideal to the inverse of that ideal's Picard class. The affine localization
bridge is also unconditional: restriction of tilde to a principal open is identified through
localized global sections, and a finite basic-open cover proves that tilde of every invertible
module is an invertible sheaf. The further comparison with AINTLIB's scheme Picard group remains
factored into its exact forward and reverse components rather than hidden behind a stronger
claim than the current library proves.
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
  /-- Every locally free rank-one sheaf has a tensor inverse and hence a Picard class. -/
  comparison : TensorInverseComparison X
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

end AffineDedekind

end MazurTorsion.AlgebraicGeometry
