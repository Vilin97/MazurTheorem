/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafQuasicoherentRestriction
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Quasicoherent modules on affine schemes

This file isolates the consequences of the affine tilde-counit theorem:
closure under colimits and finite products, surjectivity of global
sections along epimorphisms, and preservation by pushforward between
affine schemes.

The local class `HasQuasicoherentTildeCounit` makes the dependency on the
affine patching theorem explicit.  The patching file supplies this class
for every commutative ring.
-/

open CategoryTheory Limits TopologicalSpace Opposite

universe u v w

namespace AlgebraicGeometry.Scheme

open Modules

variable {X : Scheme.{u}} {R : CommRingCat.{u}}

/--
A reducible quasicoherence wrapper for categorical object-property arguments.
Public theorem signatures use Mathlib's canonical `SheafOfModules.IsQuasicoherent`
predicate directly.
-/
abbrev Modules.Quasicoherent (M : X.Modules) :=
  SheafOfModules.IsQuasicoherent.{u, u, u} M

/-- The object property of being quasicoherent. -/
abbrev Modules.isQuasicoherentCohomology (X : Scheme.{u}) :
    ObjectProperty X.Modules :=
  SheafOfModules.IsQuasicoherent.{u, u, u}

namespace Modules

/-- The affine patching input: every quasicoherent module on `Spec R`
has invertible tilde counit. -/
class HasQuasicoherentTildeCounit (R : CommRingCat.{u}) : Prop where
  isIso (M : (Spec R).Modules) [M.IsQuasicoherent] :
    IsIso M.fromTildeΓ

/-- Extract the tilde-counit isomorphism from the affine patching input. -/
instance isIso_fromTildeΓ_of_hasQuasicoherentTildeCounit
    [HasQuasicoherentTildeCounit R]
    (M : (Spec R).Modules) [M.IsQuasicoherent] :
    IsIso M.fromTildeΓ :=
  HasQuasicoherentTildeCounit.isIso M

end Modules

@[simp]
lemma isQuasicoherent_def {M : X.Modules} :
    isQuasicoherentCohomology X M ↔ M.IsQuasicoherent :=
  Iff.rfl

/-- Quasicoherence is invariant under isomorphism. -/
theorem isQuasicoherent_of_iso {M N : X.Modules}
    (e : M ≅ N) [M.IsQuasicoherent] :
    N.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e
    inferInstance

instance isQuasicoherentCohomology_closedUnderIsomorphisms :
    (isQuasicoherentCohomology X).IsClosedUnderIsomorphisms :=
  ObjectProperty.IsClosedUnderIsomorphisms.mk
    (fun e _ => isQuasicoherent_of_iso e)

section Spec

variable [Modules.HasQuasicoherentTildeCounit R]

/-- On an affine spectrum, quasicoherence is equivalent to invertibility
of the tilde counit. -/
theorem isIso_fromTildeΓ_iff_isQuasicoherent
    (M : (Spec R).Modules) :
    IsIso M.fromTildeΓ ↔ M.IsQuasicoherent := by
  constructor
  · intro h
    letI : IsIso M.fromTildeΓ := h
    exact isQuasicoherent_of_iso (asIso M.fromTildeΓ)
  · intro
    infer_instance

/-- The essential image of tilde is exactly the quasicoherent modules. -/
theorem isQuasicoherent_iff_tilde_essImage :
    (tilde.functor R).essImage =
      isQuasicoherentCohomology (Spec R) := by
  ext M
  rw [← isIso_fromTildeΓ_iff]
  exact isIso_fromTildeΓ_iff_isQuasicoherent M

variable {J : Type w} [Category.{v} J]
  [HasColimitsOfShape J AddCommGrpCat]

/-- Quasicoherent modules on a spectrum are closed under colimits. -/
instance isQuasicoherentCohomology_spec_closedUnderColimits :
    (isQuasicoherentCohomology (Spec R)).IsClosedUnderColimitsOfShape J := by
  letI : (tilde.functor R).Full :=
    tilde.fullyFaithfulFunctor.full
  letI : (tilde.functor R).Faithful :=
    tilde.fullyFaithfulFunctor.faithful
  rw [← isQuasicoherent_iff_tilde_essImage]
  apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
  rintro _ ⟨G, hG⟩
  exact
    ⟨colimit (Functor.essImage.liftFunctor G (tilde.functor R) hG),
      ⟨IsColimit.coconePointsIsoOfNatIso
        (isColimitOfPreserves (tilde.functor R) (colimit.isColimit _))
        (colimit.isColimit _)
        (Functor.essImage.liftFunctorCompIso G (tilde.functor R) hG)⟩⟩

/-- Quasicoherent modules on a spectrum are closed under finite products. -/
instance isQuasicoherentCohomology_spec_closedUnderFiniteLimits [Finite J] :
    (isQuasicoherentCohomology (Spec R)).IsClosedUnderLimitsOfShape
      (Discrete J) := by
  letI : (tilde.functor R).Full :=
    tilde.fullyFaithfulFunctor.full
  letI : (tilde.functor R).Faithful :=
    tilde.fullyFaithfulFunctor.faithful
  rw [← isQuasicoherent_iff_tilde_essImage]
  apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
  rintro _ ⟨G, hG⟩
  exact
    ⟨limit (Functor.essImage.liftFunctor G (tilde.functor R) hG),
      ⟨IsLimit.conePointsIsoOfNatIso
        (isLimitOfPreserves (tilde.functor R) (limit.isLimit _))
        (limit.isLimit _)
        (Functor.essImage.liftFunctorCompIso G (tilde.functor R) hG)⟩⟩

/-- An epimorphism of quasicoherent modules on a spectrum is surjective
on global sections. -/
instance epi_moduleSpecΓFunctor_map_of_epi
    {M N : (Spec R).Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [Epi f] :
    Epi (moduleSpecΓFunctor.map f) := by
  apply (tilde.functor R).epi_of_epi_map
  haveI : IsIso (tilde.adjunction.counit.app N) :=
    isIso_fromTildeΓ_of_hasQuasicoherentTildeCounit N
  rw [← epi_comp_iff_of_isIso _
      (tilde.adjunction.counit.app N),
    tilde.adjunction.counit_naturality f]
  haveI : Epi (tilde.adjunction.counit.app M) :=
    (isIso_fromTildeΓ_of_hasQuasicoherentTildeCounit M).epi_of_iso
  infer_instance

/-- An epimorphism of quasicoherent modules on a spectrum is
surjective on sections over the top open. -/
theorem isQuasicoherent_spec_surjective_of_epi
    {M N : (Spec R).Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [Epi f] :
    Function.Surjective (f.val.app (op ⊤)).hom :=
  ModuleCat.epi_iff_surjective (moduleSpecΓFunctor.map f) |>.mp
    (epi_moduleSpecΓFunctor_map_of_epi f)

end Spec

noncomputable section RestrictEquivalence

variable {Y : Scheme.{u}} (e : X ≅ Y)

namespace Modules

/-- Restricting successively along an isomorphism and its inverse is
naturally isomorphic to the identity. -/
def restrictFunctor_inv_restrictFunctor_hom_id_coherentCohomology :
    restrictFunctor e.inv ⋙ restrictFunctor e.hom ≅ 𝟭 X.Modules :=
  (restrictFunctorComp e.hom e.inv).symm ≪≫
    restrictFunctorCongr e.hom_inv_id ≪≫
    restrictFunctorId

instance restrictFunctor_isEquivalence_coherentCohomology :
    (restrictFunctor e.hom).IsEquivalence :=
  Functor.IsEquivalence.mk' _
    (restrictFunctor_inv_restrictFunctor_hom_id_coherentCohomology e.symm).symm
    (restrictFunctor_inv_restrictFunctor_hom_id_coherentCohomology e)

/-- Quasicoherence is invariant under restriction along a scheme
isomorphism. -/
theorem isQuasicoherent_restrictFunctor_iff_coherentCohomology
    {M : Y.Modules} :
    (M.restrict e.hom).IsQuasicoherent ↔
      M.IsQuasicoherent := by
  refine ⟨fun _ => ?_, fun _ => inferInstance⟩
  apply ObjectProperty.prop_of_iso _
    ((restrictFunctor_inv_restrictFunctor_hom_id_coherentCohomology e.symm).app M)
  simp only [Iso.symm_inv, Iso.symm_hom, Functor.comp_obj]
  infer_instance

/-- Pulling the quasicoherent object property back along a scheme
isomorphism gives the same property. -/
theorem isQuasicoherent_inverseImage_iso_coherentCohomology :
    (isQuasicoherentCohomology X).inverseImage (restrictFunctor e.hom) =
      isQuasicoherentCohomology Y := by
  ext M
  simp [isQuasicoherent_restrictFunctor_iff_coherentCohomology]

/-- Pushforward along a scheme isomorphism preserves quasicoherence. -/
instance isQuasicoherent_pushforward_of_iso_coherentCohomology
    {e : X ⟶ Y} [IsIso e] {M : X.Modules}
    [M.IsQuasicoherent] :
    ((pushforward e).obj M).IsQuasicoherent :=
  (isQuasicoherent_restrictFunctor_iff_coherentCohomology (asIso e)).mp
    ((isQuasicoherentCohomology X).prop_of_iso
      ((restrictFunctorAdjCounitIso e).app M).symm
      (by simpa only [Functor.id_obj] using
        (inferInstance : M.IsQuasicoherent)))

end Modules

end RestrictEquivalence

noncomputable section Affine

variable [∀ R : CommRingCat.{u},
  Modules.HasQuasicoherentTildeCounit R]

namespace Modules

/-- On an affine scheme, an epimorphism of quasicoherent modules is
surjective on global sections. -/
theorem isQuasicoherent_surjective_of_epi_coherentCohomology
    {M N : X.Modules} [IsAffine X] (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [Epi f] :
    Function.Surjective (f.val.app (op ⊤)).hom := by
  rw [← (isoSpec X).inv.opensRange_of_isIso,
    ← (isoSpec X).inv.image_top_eq_opensRange]
  change Function.Surjective
    (((restrictFunctor (isoSpec X).inv).map f).val.app (op ⊤))
  exact isQuasicoherent_spec_surjective_of_epi
    ((restrictFunctor (isoSpec X).inv).map f)

/-- Pushforward along a morphism of affine spectra preserves
quasicoherence. -/
instance isQuasicoherent_pushforward_specMap
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    {M : (Spec S).Modules} [M.IsQuasicoherent] :
    ((pushforward (Spec.map φ)).obj M).IsQuasicoherent := by
  rw [← isIso_fromTildeΓ_iff_isQuasicoherent] at ⊢
  exact isIso_fromTildeΓ_pushforward φ M

/-- Pushforward along a morphism between affine schemes preserves
quasicoherence. -/
instance isQuasicoherent_pushforward_affine
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (M : X.Modules) [M.IsQuasicoherent] :
    ((pushforward f).obj M).IsQuasicoherent := by
  rw [show f =
      (X.isoSpec.hom ≫ Spec.map (Hom.appTop f)) ≫
        Y.isoSpec.inv by
    simp [isoSpec_hom_naturality f]]
  let e :=
    (pushforward X.isoSpec.hom).isoWhiskerLeft
      (pushforwardComp (Spec.map (Hom.appTop f))
        Y.isoSpec.inv) ≪≫
    pushforwardComp X.isoSpec.hom
      (Spec.map (Hom.appTop f) ≫ Y.isoSpec.inv)
  have h :
      ((pushforward X.isoSpec.hom ⋙
        pushforward (Spec.map (Hom.appTop f)) ⋙
        pushforward Y.isoSpec.inv).obj M).IsQuasicoherent := by
    simp only [Functor.comp_obj]
    infer_instance
  exact isQuasicoherent_of_iso (e.app M)

variable {J : Type w} [Category.{v} J]
  [HasColimitsOfShape J AddCommGrpCat]

/-- Quasicoherent modules on an affine scheme are closed under
colimits. -/
instance isQuasicoherentCohomology_affine_closedUnderColimits [IsAffine X] :
    (isQuasicoherentCohomology X).IsClosedUnderColimitsOfShape J := by
  rw [← isQuasicoherent_inverseImage_iso_coherentCohomology (isoSpec X).symm]
  exact ObjectProperty.IsClosedUnderColimitsOfShape.inverseImage ..

/-- Quasicoherent modules on an affine scheme are closed under finite
products. -/
instance isQuasicoherentCohomology_affine_closedUnderFiniteLimits
    [IsAffine X] [Finite J] :
    (isQuasicoherentCohomology X).IsClosedUnderLimitsOfShape
      (Discrete J) := by
  rw [← isQuasicoherent_inverseImage_iso_coherentCohomology (isoSpec X).symm]
  exact ObjectProperty.IsClosedUnderLimitsOfShape.inverseImage ..

end Modules

end Affine

end AlgebraicGeometry.Scheme
