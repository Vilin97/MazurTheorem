/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
import Mathlib.CategoryTheory.Sites.Equivalence
import MazurTorsion.Upstream.SchemeModuleCohomologyAffineHOne

/-!
# Degree-two affine local killing

This file removes the affine-section-surjectivity premise from degree-two
local killing.  First, degree-one quasicoherent affine vanishing is transported
from a spectrum across the canonical affine scheme isomorphism.  Pulling the
injective-cokernel sequence back to an affine open is exact, so its long exact
cohomology sequence makes the cokernel projection surjective on sections over
that open.  This supplies the premise of the conditional degree-two theorem.

The construction is a clean-room derivation against this repository's pinned
Mathlib.  The unlicensed AINTLIB files `KempfLocalKilling.lean` and
`AffineVanishing.lean`, the prior implementation branch, and commit `77901d2`
were not consulted.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

private abbrev AbSheaf (X : Scheme.{u}) :=
  CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}

private noncomputable def openSheafPullback
    {X : Scheme.{u}} (U : X.Opens) :
    AbSheaf X ⥤ AbSheaf U :=
  U.ι.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}

private noncomputable instance openSheafPullback_preservesFiniteLimits
    {X : Scheme.{u}} (U : X.Opens) :
    PreservesFiniteLimits (openSheafPullback U) := by
  letI := U.ι.isOpenEmbedding.functor_isContinuous
  let E₁ := openSheafPullback U ⋙
    sheafToPresheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u}
  let E₂ := sheafToPresheaf
      (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj
      U.ι.isOpenEmbedding.functor.op
  let e : E₁ ≅ E₂ :=
    U.ι.isOpenEmbedding.functor.sheafPushforwardContinuousCompSheafToPresheafIso
      AddCommGrpCat.{u} (Opens.grothendieckTopology U)
        (Opens.grothendieckTopology X)
  haveI : PreservesFiniteLimits
      (sheafToPresheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{u}) := by infer_instance
  haveI : PreservesFiniteLimits
      ((Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj
        U.ι.isOpenEmbedding.functor.op) := by infer_instance
  haveI : PreservesFiniteLimits E₂ := by infer_instance
  haveI : PreservesFiniteLimits E₁ :=
    preservesFiniteLimits_of_natIso e.symm
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (sheafToPresheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u})

private noncomputable instance openSheafPullback_preservesFiniteColimits
    {X : Scheme.{u}} (U : X.Opens) :
    PreservesFiniteColimits (openSheafPullback U) := by
  change PreservesFiniteColimits
    (U.ι.isOpenEmbedding.sheafPullback AddCommGrpCat.{u})
  letI : PreservesColimits
      (TopCat.Sheaf.pullback AddCommGrpCat.{u} U.ι.base) :=
    (TopCat.Sheaf.pullbackPushforwardAdjunction
      AddCommGrpCat.{u} U.ι.base).leftAdjoint_preservesColimits
  exact preservesFiniteColimits_of_natIso
    (U.ι.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u})

private noncomputable def sheafEquivOfSchemeIso
    {X Y : Scheme.{u}} (e : X ≅ Y) :
    AbSheaf X ≌ AbSheaf Y := by
  let eb : (X : TopCat) ≅ (Y : TopCat) := asIso e.hom.base
  let eo := Opens.mapMapIso eb
  letI : eo.functor.IsCocontinuous
      (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) :=
    (eo.toAdjunction.isCocontinuous_iff_coverPreserving _ _).2
      (coverPreserving_opens_map eb.inv)
  letI : eo.inverse.IsCocontinuous
      (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) :=
    (eo.symm.toAdjunction.isCocontinuous_iff_coverPreserving _ _).2
      (coverPreserving_opens_map eb.hom)
  letI : eo.functor.IsDenseSubsite
      (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) :=
    eo.isDenseSubsite_functor_of_isCocontinuous _ _
  exact (Functor.IsDenseSubsite.sheafEquiv
    (G := eo.functor)
    (K := Opens.grothendieckTopology X)
    (Opens.grothendieckTopology Y)
    AddCommGrpCat.{u}).symm

private noncomputable def pushforwardConstantIso
    {X Y : Scheme.{u}} (e : X ≅ Y) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom.base).obj
        ((CategoryTheory.constantSheaf
          (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
            (AddCommGrpCat.of (ULift ℤ))) ≅
      (CategoryTheory.constantSheaf
        (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift ℤ)) := by
  let eb : (X : TopCat) ≅ (Y : TopCat) := asIso e.hom.base
  let eo := Opens.mapMapIso eb
  letI : eo.functor.IsCocontinuous
      (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) :=
    (eo.toAdjunction.isCocontinuous_iff_coverPreserving _ _).2
      (coverPreserving_opens_map eb.inv)
  letI : eo.inverse.IsCocontinuous
      (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) :=
    (eo.symm.toAdjunction.isCocontinuous_iff_coverPreserving _ _).2
      (coverPreserving_opens_map eb.hom)
  letI : eo.functor.IsDenseSubsite
      (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) :=
    eo.isDenseSubsite_functor_of_isCocontinuous _ _
  exact (equivCommuteConstant'
    (Opens.grothendieckTopology Y)
    AddCommGrpCat.{u}
    (Opens.grothendieckTopology X)
    eo.functor
    (isTerminalTop : IsTerminal (⊤ : Opens Y))
    (isTerminalTop : IsTerminal (⊤ : Opens X))).symm.app
      (AddCommGrpCat.of (ULift ℤ))

/-- Cohomology subsingletonness transports back across a scheme isomorphism. -/
theorem sheafH_subsingleton_of_iso
    {X Y : Scheme.{u}} (e : X ≅ Y) (F : AbSheaf X) (n : ℕ)
    [Subsingleton (CategoryTheory.Sheaf.H
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom.base).obj F) n)] :
    Subsingleton (CategoryTheory.Sheaf.H F n) := by
  let P := TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom.base
  let E := sheafEquivOfSchemeIso e
  letI : P.IsEquivalence := by
    change E.functor.IsEquivalence
    infer_instance
  letI : PreservesFiniteLimits P := by infer_instance
  letI : PreservesFiniteColimits P := by infer_instance
  letI : P.PreservesZeroMorphisms := by infer_instance
  letI : P.Additive := P.additive_of_preserves_binary_products
  letI : P.PreservesInjectiveObjects := by infer_instance
  letI hH : Subsingleton (CategoryTheory.Sheaf.H (P.obj F) n) := by
    dsimp [P]
    infer_instance
  let Z := (CategoryTheory.constantSheaf
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ))
  let κ := pushforwardConstantIso e
  have htarget : Subsingleton (Abelian.Ext (P.obj Z) (P.obj F) n) := by
    refine ⟨fun a b ↦ ?_⟩
    have h := @Subsingleton.elim
      (CategoryTheory.Sheaf.H (P.obj F) n) hH
      ((Abelian.Ext.mk₀ κ.inv).comp a (zero_add n))
      ((Abelian.Ext.mk₀ κ.inv).comp b (zero_add n))
    calc
      a = (Abelian.Ext.mk₀ (𝟙 (P.obj Z))).comp a (zero_add n) :=
        (Abelian.Ext.mk₀_id_comp a).symm
      _ = (Abelian.Ext.mk₀ (κ.hom ≫ κ.inv)).comp a
          (zero_add n) := by rw [κ.hom_inv_id]
      _ = (Abelian.Ext.mk₀ κ.hom).comp
          ((Abelian.Ext.mk₀ κ.inv).comp a (zero_add n))
            (zero_add n) :=
        (Abelian.Ext.mk₀_comp_mk₀_assoc κ.hom κ.inv a).symm
      _ = (Abelian.Ext.mk₀ κ.hom).comp
          ((Abelian.Ext.mk₀ κ.inv).comp b (zero_add n))
            (zero_add n) := congrArg
        (fun z ↦ (Abelian.Ext.mk₀ κ.hom).comp z (zero_add n)) h
      _ = (Abelian.Ext.mk₀ (κ.hom ≫ κ.inv)).comp b
          (zero_add n) :=
        Abelian.Ext.mk₀_comp_mk₀_assoc κ.hom κ.inv b
      _ = (Abelian.Ext.mk₀ (𝟙 (P.obj Z))).comp b (zero_add n) := by
        rw [κ.hom_inv_id]
      _ = b := Abelian.Ext.mk₀_id_comp b
  refine ⟨fun a b ↦ ?_⟩
  apply (P.mapExt_bijective_of_preservesInjectiveObjects Z F n).injective
  exact @Subsingleton.elim _ htarget _ _

/-- Genuine degree-one cohomology of a quasicoherent module on any affine
scheme is subsingleton. -/
theorem moduleAffineHOne_subsingleton
    {X : Scheme.{u}} [IsAffine X] (M : X.Modules)
    [M.IsQuasicoherent] :
    Subsingleton (H M 1) := by
  let e := X.isoSpec
  let N := (Scheme.Modules.pushforward e.hom).obj M
  letI : N.IsQuasicoherent := isQuasicoherent_pushforward_iso
  have hN : Subsingleton (H N 1) :=
    moduleSpecHOne_subsingleton N
  letI : Subsingleton (H N 1) := hN
  letI : Subsingleton (CategoryTheory.Sheaf.H
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom.base).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) 1) := by
    change Subsingleton (H N 1)
    exact hN
  exact sheafH_subsingleton_of_iso e
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) 1

private noncomputable abbrev injectiveCokernelSequence
    {X : Scheme.{u}} (F : AbSheaf X) :
    ShortComplex (AbSheaf X) :=
  ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
    (cokernel.condition (Injective.ι F))

private theorem injectiveCokernelSequence_shortExact
    {X : Scheme.{u}} (F : AbSheaf X) :
    (injectiveCokernelSequence F).ShortExact := by
  letI : Mono (injectiveCokernelSequence F).f := by
    change Mono (Injective.ι F)
    infer_instance
  letI : Epi (injectiveCokernelSequence F).g := by
    change Epi (cokernel.π (Injective.ι F))
    infer_instance
  exact ShortComplex.ShortExact.mk
    (ShortComplex.exact_cokernel (Injective.ι F))

/-- For a quasicoherent module, the projection from an injective sheaf to
its cokernel is surjective on sections of every affine open. -/
theorem injectiveCokernel_app_surjective_of_isAffineOpen
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Surjective
      ((cokernel.π (Injective.ι
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M))).hom.app (op U)) := by
  let F := (SheafOfModules.toSheaf X.ringCatSheaf).obj M
  let L := openSheafPullback U
  let S := injectiveCokernelSequence F
  letI : PreservesFiniteLimits L := by
    dsimp [L]
    infer_instance
  letI : PreservesFiniteColimits L := by
    dsimp [L]
    infer_instance
  letI : L.PreservesZeroMorphisms := by infer_instance
  letI : L.Additive := L.additive_of_preserves_binary_products
  have hS : S.ShortExact := by
    dsimp [S]
    exact injectiveCokernelSequence_shortExact F
  have hSL : (S.map L).ShortExact :=
    ShortComplex.ShortExact.map_of_exact hS L
  letI : IsAffine (U : Scheme) := hU
  let N := (Scheme.Modules.restrictFunctor U.ι).obj M
  letI : N.IsQuasicoherent := by
    dsimp [N]
    infer_instance
  have hN : Subsingleton (H N 1) :=
    moduleAffineHOne_subsingleton N
  letI : Subsingleton ((S.map L).X₁.H 1) := by
    change Subsingleton (H N 1)
    exact hN
  have hsurjective :=
    CategoryTheory.Sheaf.H.longSequence_surjective_of_subsingleton_H
      hSL (isTerminalTop : IsTerminal (⊤ : Opens (U : Scheme)))
  change Function.Surjective
    ((L.map (cokernel.π (Injective.ι F))).hom.app
      (op (⊤ : Opens (U : Scheme)))) at hsurjective
  change Function.Surjective
    ((cokernel.π (Injective.ι F)).hom.app
      (op (U.ι.isOpenEmbedding.functor.obj
        (⊤ : Opens (U : Scheme))))) at hsurjective
  have htop : U.ι.isOpenEmbedding.functor.obj
      (⊤ : Opens (U : Scheme)) = U := by
    ext x
    simp
  rw [htop] at hsurjective
  simpa only [F] using hsurjective

namespace LocalKilling

/-- Every degree-two class of a quasicoherent module on an affine spectrum
is killed by restriction to a finite affine open cover. -/
theorem schemeHTwo_finiteAffineKillingCover
    {R : CommRingCat.{u}} (M : (Spec R).Modules) [M.IsQuasicoherent]
    (c : H M 2) :
    ∃ (I : Type u) (U : I → (Spec R).Opens),
      Finite I ∧
      IsOpenCover U ∧
      (∀ i, IsAffine (U i)) ∧
      (∀ i, (zariskiFunctor (Spec R) 2).map
        ((Scheme.Modules.restrictAdjunction (U i).ι).unit.app M) c = 0) ∧
      (zariskiFunctor (Spec R) 2).map
        (toAffineCoverModule M U) c = 0 := by
  exact schemeHTwo_finiteAffineKillingCover_of_affine_cokernel_app_surjective
    M c (injectiveCokernel_app_surjective_of_isAffineOpen M)

end LocalKilling

/-- Genuine Ext-based `H²` of a quasicoherent scheme module on an affine
spectrum is subsingleton. -/
theorem moduleSpecHTwo_subsingleton
    {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [M.IsQuasicoherent] : Subsingleton (H M 2) := by
  refine subsingleton_of_forall_eq 0 fun c ↦ ?_
  obtain ⟨I, U, hfinite, hcover, haffine, _, hkilled⟩ :=
    LocalKilling.schemeHTwo_finiteAffineKillingCover M c
  letI : Finite I := hfinite
  letI (i : I) : IsAffine (U i) := haffine i
  letI : (cokernel (toAffineCoverModule M U)).IsQuasicoherent :=
    affineCoverCokernel_isQuasicoherent M U
  letI : Subsingleton (H (cokernel (toAffineCoverModule M U)) 1) :=
    moduleSpecHOne_subsingleton _
  apply toAffineCoverModule_H_succ_injective_of_cokernel_subsingleton
    M U hcover 1
  rw [hkilled, map_zero]

/-- Every genuine Ext-based degree-two class of a quasicoherent scheme
module on an affine spectrum is zero. -/
theorem moduleSpecHTwo_eq_zero
    {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [M.IsQuasicoherent] (c : H M 2) : c = 0 := by
  letI : Subsingleton (H M 2) := moduleSpecHTwo_subsingleton M
  exact Subsingleton.elim _ _

/-- Genuine degree-two cohomology of a quasicoherent module on any affine
scheme is subsingleton. -/
theorem moduleAffineHTwo_subsingleton
    {X : Scheme.{u}} [IsAffine X] (M : X.Modules)
    [M.IsQuasicoherent] : Subsingleton (H M 2) := by
  let e := X.isoSpec
  let N := (Scheme.Modules.pushforward e.hom).obj M
  letI : N.IsQuasicoherent := isQuasicoherent_pushforward_iso
  have hN : Subsingleton (H N 2) := moduleSpecHTwo_subsingleton N
  letI : Subsingleton (H N 2) := hN
  letI : Subsingleton (CategoryTheory.Sheaf.H
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom.base).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) 2) := by
    change Subsingleton (H N 2)
    exact hN
  exact sheafH_subsingleton_of_iso e
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) 2

/-- Every genuine Ext-based degree-two class of a quasicoherent module on
an affine scheme is zero. -/
theorem moduleAffineHTwo_eq_zero
    {X : Scheme.{u}} [IsAffine X] (M : X.Modules)
    [M.IsQuasicoherent] (c : H M 2) : c = 0 := by
  letI : Subsingleton (H M 2) := moduleAffineHTwo_subsingleton M
  exact Subsingleton.elim _ _

end MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology
