/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.CategoryTheory.Generator.Sheaf
import Mathlib.Topology.Sheaves.Flasque
import MazurTorsion.Upstream.SchemeModuleCohomologyAffineHTwo

/-!
# Degree-three affine quasicoherent acyclicity

This file develops the flasque-sheaf input needed to iterate the affine
local-killing argument beyond degree two.  Injective abelian sheaves are
proved flasque from the free abelian sheaf represented by an open set, and
flasque sheaves are then proved acyclic in every positive degree by honest
dimension shifting through injective cokernels.

The degree-three consumer below uses this acyclicity after restriction to an
affine open.  Together with affine degree-two vanishing, it supplies the next
injective-cokernel section-surjectivity premise rather than assuming that
premise for an iterated syzygy.

The construction is a clean-room derivation against this repository's pinned
Mathlib.  The unlicensed AINTLIB files `KempfLocalKilling.lean` and
`AffineVanishing.lean`, the prior implementation branch, and commit
`77901d2` were not consulted.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

private abbrev AbSheaf (X : TopCat.{u}) :=
  CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}

private noncomputable abbrev freeAbelianRepresentable
    {X : TopCat.{u}} (U : Opens X) : AbSheaf X :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (yoneda.obj U ⋙ AddCommGrpCat.free)

private noncomputable def freeAbelianRepresentableMap
    {X : TopCat.{u}} {U V : Opens X} (i : U ⟶ V) :
    freeAbelianRepresentable U ⟶ freeAbelianRepresentable V :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
    (Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free)

private noncomputable def freeAbelianRepresentableHomEquiv
    {X : TopCat.{u}} {U : Opens X} {F : AbSheaf X} :
    (freeAbelianRepresentable U ⟶ F) ≃ F.obj.obj (op U) :=
  ((sheafificationAdjunction
      (Opens.grothendieckTopology X) AddCommGrpCat.{u}).homEquiv _ _).trans <|
    ((AddCommGrpCat.adj.whiskerRight (Opens X)ᵒᵖ).homEquiv _ _).trans
      yonedaEquiv

private theorem freeAbelianRepresentableMap_mono
    {X : TopCat.{u}} {U V : Opens X} (i : U ⟶ V) :
    Mono (freeAbelianRepresentableMap i) := by
  dsimp [freeAbelianRepresentableMap]
  apply Functor.map_mono

private theorem freeAbelianRepresentableHomEquiv_map
    {X : TopCat.{u}} {U V : Opens X} (i : U ⟶ V)
    {F : AbSheaf X} (f : freeAbelianRepresentable V ⟶ F) :
    freeAbelianRepresentableHomEquiv
        (freeAbelianRepresentableMap i ≫ f) =
      F.obj.map i.op (freeAbelianRepresentableHomEquiv f) := by
  let a₁ := sheafificationAdjunction
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let a₂ := AddCommGrpCat.adj.whiskerRight (Opens X)ᵒᵖ
  let α := Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free
  have h₁ := a₁.homEquiv_naturality_left α f
  have h₂ := a₂.homEquiv_naturality_left (yoneda.map i)
    (a₁.homEquiv _ _ f)
  dsimp [freeAbelianRepresentableHomEquiv,
    freeAbelianRepresentableMap, freeAbelianRepresentable, a₁, a₂, α] at h₁ h₂ ⊢
  rw [h₁, h₂]
  exact (yonedaEquiv_naturality _ _).symm

/-- An injective abelian sheaf is flasque.  This is the section-extension
property needed after restricting an injective resolution to an open set. -/
theorem injectiveSheaf_isFlasque
    {X : TopCat.{u}} (F : AbSheaf X) [Injective F] :
    TopCat.Sheaf.IsFlasque F := by
  constructor
  intro U V i
  rw [AddCommGrpCat.epi_iff_surjective]
  intro s
  let g : freeAbelianRepresentable V.unop ⟶ F :=
    freeAbelianRepresentableHomEquiv.symm s
  let m : freeAbelianRepresentable V.unop ⟶
      freeAbelianRepresentable U.unop :=
    freeAbelianRepresentableMap i.unop
  letI : Mono m := freeAbelianRepresentableMap_mono i.unop
  let h : freeAbelianRepresentable U.unop ⟶ F :=
    Injective.factorThru g m
  refine ⟨freeAbelianRepresentableHomEquiv h, ?_⟩
  have hnat : F.obj.map i (freeAbelianRepresentableHomEquiv h) =
      freeAbelianRepresentableHomEquiv (m ≫ h) := by
    simpa only [m, Quiver.Hom.op_unop, Opposite.op_unop] using
      (freeAbelianRepresentableHomEquiv_map i.unop h).symm
  rw [hnat, Injective.comp_factorThru]
  exact Equiv.apply_symm_apply _ _

private noncomputable abbrev injectiveCokernelSequence
    {X : TopCat.{u}} (F : AbSheaf X) : ShortComplex (AbSheaf X) :=
  ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
    (cokernel.condition (Injective.ι F))

private theorem injectiveCokernelSequence_shortExact
    {X : TopCat.{u}} (F : AbSheaf X) :
    (injectiveCokernelSequence F).ShortExact := by
  letI : Mono (injectiveCokernelSequence F).f := by
    change Mono (Injective.ι F)
    infer_instance
  exact ShortComplex.ShortExact.mk
    (ShortComplex.exact_cokernel (Injective.ι F))

private theorem exists_injectiveCokernel_class
    {X : TopCat.{u}} {Z F : AbSheaf X} {n : ℕ}
    (c : Abelian.Ext Z F (n + 1)) :
    ∃ q : Abelian.Ext Z (cokernel (Injective.ι F)) n,
      q.comp (injectiveCokernelSequence_shortExact F).extClass rfl = c := by
  have hc : c.comp (Abelian.Ext.mk₀ (Injective.ι F)) rfl = 0 :=
    Abelian.Ext.eq_zero_of_injective _
  exact Abelian.Ext.covariant_sequence_exact₁ Z
    (injectiveCokernelSequence_shortExact F) c hc rfl

/-- Every positive-degree cohomology group of a flasque abelian sheaf is
subsingleton.  The proof uses the actual injective-cokernel sequence: its
injective middle term is flasque, its cokernel remains flasque, and the base
case is the section-surjectivity theorem for a short exact sequence with
flasque kernel. -/
theorem flasqueSheaf_H_succ_subsingleton
    {X : TopCat.{u}} (F : AbSheaf X) [TopCat.Sheaf.IsFlasque F]
    (n : ℕ) : Subsingleton (CategoryTheory.Sheaf.H F (n + 1)) := by
  induction n generalizing F with
  | zero =>
      refine subsingleton_of_forall_eq 0 fun c ↦ ?_
      obtain ⟨q, hq⟩ := exists_injectiveCokernel_class c
      let S := injectiveCokernelSequence F
      have hS : S.ShortExact := injectiveCokernelSequence_shortExact F
      haveI : Epi (S.g.hom.app (op (⊤ : Opens X))) :=
        TopCat.Sheaf.IsFlasque.epi_of_shortExact hS
      obtain ⟨t, ht⟩ := (AddCommGrpCat.epi_iff_surjective _).mp
        (inferInstance : Epi (S.g.hom.app (op (⊤ : Opens X))))
        (CategoryTheory.Sheaf.H.equiv₀ S.X₃
          (isTerminalTop : IsTerminal (⊤ : Opens X)) q)
      let y := (CategoryTheory.Sheaf.H.equiv₀ S.X₂
        (isTerminalTop : IsTerminal (⊤ : Opens X))).symm t
      have hy : CategoryTheory.Sheaf.H.map S.g 0 y = q := by
        apply (CategoryTheory.Sheaf.H.equiv₀ S.X₃
          (isTerminalTop : IsTerminal (⊤ : Opens X))).injective
        rw [← CategoryTheory.Sheaf.H.equiv₀_naturality]
        simpa only [y, AddEquiv.apply_symm_apply] using ht
      rw [← hq, ← hy]
      change (y.comp (Abelian.Ext.mk₀ S.g) rfl).comp hS.extClass rfl = 0
      calc
        _ = y.comp ((Abelian.Ext.mk₀ S.g).comp hS.extClass
            (zero_add 1)) (zero_add 1) := by
          simpa only using (Abelian.Ext.comp_assoc y
            (Abelian.Ext.mk₀ S.g) hS.extClass rfl rfl rfl)
        _ = 0 := by rw [hS.comp_extClass, Abelian.Ext.comp_zero]
  | succ n ih =>
      refine subsingleton_of_forall_eq 0 fun c ↦ ?_
      obtain ⟨q, hq⟩ := exists_injectiveCokernel_class c
      let S := injectiveCokernelSequence F
      letI : TopCat.Sheaf.IsFlasque S.X₂ :=
        injectiveSheaf_isFlasque S.X₂
      letI : TopCat.Sheaf.IsFlasque S.X₃ :=
        TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂
          (injectiveCokernelSequence_shortExact F)
      have hqzero : q = 0 := by
        letI : Subsingleton (CategoryTheory.Sheaf.H S.X₃ (n + 1)) :=
          ih S.X₃
        exact Subsingleton.elim _ _
      rw [← hq, hqzero, Abelian.Ext.zero_comp]

private noncomputable def openSheafPullback
    {X : Scheme.{u}} (U : X.Opens) : AbSheaf X ⥤ AbSheaf U :=
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

private theorem openSheafPullback_isFlasque
    {X : Scheme.{u}} (U : X.Opens) (F : AbSheaf X)
    [TopCat.Sheaf.IsFlasque F] :
    TopCat.Sheaf.IsFlasque ((openSheafPullback U).obj F) := by
  constructor
  intro V W i
  change Epi (F.obj.map _)
  infer_instance

private theorem subsingleton_H_X₃_of_shortExact
    {X : Scheme.{u}} {S : ShortComplex (AbSheaf X)}
    (hS : S.ShortExact) (n : ℕ)
    (hmiddle : Subsingleton (CategoryTheory.Sheaf.H S.X₂ n))
    (hleft : Subsingleton (CategoryTheory.Sheaf.H S.X₁ (n + 1))) :
    Subsingleton (CategoryTheory.Sheaf.H S.X₃ n) := by
  letI : Subsingleton (CategoryTheory.Sheaf.H S.X₂ n) := hmiddle
  letI : Subsingleton (CategoryTheory.Sheaf.H S.X₁ (n + 1)) := hleft
  refine subsingleton_of_forall_eq 0 fun c ↦ ?_
  obtain ⟨y, hy⟩ := CategoryTheory.Sheaf.H.longSequence_exact₃
    hS n (n + 1) rfl c (Subsingleton.elim _ _)
  rw [Subsingleton.elim y 0, map_zero] at hy
  exact hy.symm

private theorem secondInjectiveCokernel_app_surjective_of_isAffineOpen
    {R : CommRingCat.{u}} (M : (Spec R).Modules) [M.IsQuasicoherent]
    (U : (Spec R).Opens) (hU : IsAffineOpen U) :
    let F := (SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj M
    let C := cokernel (Injective.ι F)
    Function.Surjective
      ((cokernel.π (Injective.ι C)).hom.app (op U)) := by
  let F := (SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj M
  let C := cokernel (Injective.ι F)
  let L := openSheafPullback U
  let S₀ := injectiveCokernelSequence F
  have hS₀ : S₀.ShortExact := injectiveCokernelSequence_shortExact F
  letI : PreservesFiniteLimits L := by
    dsimp [L]
    infer_instance
  letI : PreservesFiniteColimits L := by
    dsimp [L]
    infer_instance
  letI : L.PreservesZeroMorphisms := by infer_instance
  letI : L.Additive := L.additive_of_preserves_binary_products
  have hS₀L : (S₀.map L).ShortExact :=
    ShortComplex.ShortExact.map_of_exact hS₀ L
  have hI : TopCat.Sheaf.IsFlasque (Injective.under F) :=
    injectiveSheaf_isFlasque (Injective.under F)
  letI : TopCat.Sheaf.IsFlasque (Injective.under F) := hI
  letI : TopCat.Sheaf.IsFlasque (L.obj (Injective.under F)) :=
    @openSheafPullback_isFlasque _ U (Injective.under F) hI
  have hmiddle : Subsingleton
      (CategoryTheory.Sheaf.H (L.obj (Injective.under F)) 1) :=
    flasqueSheaf_H_succ_subsingleton _ 0
  letI : IsAffine (U : Scheme) := hU
  let N := (Scheme.Modules.restrictFunctor U.ι).obj M
  letI : N.IsQuasicoherent := by
    dsimp [N]
    infer_instance
  have hN : Subsingleton (H N 2) := moduleAffineHTwo_subsingleton N
  have hleft : Subsingleton
      (CategoryTheory.Sheaf.H (L.obj F) 2) := by
    change Subsingleton (H N 2)
    exact hN
  have hC : Subsingleton (CategoryTheory.Sheaf.H (L.obj C) 1) := by
    exact subsingleton_H_X₃_of_shortExact hS₀L 1 hmiddle hleft
  let S₁ := injectiveCokernelSequence C
  have hS₁ : S₁.ShortExact := injectiveCokernelSequence_shortExact C
  have hS₁L : (S₁.map L).ShortExact :=
    ShortComplex.ShortExact.map_of_exact hS₁ L
  letI : Subsingleton ((S₁.map L).X₁.H 1) := by
    change Subsingleton (CategoryTheory.Sheaf.H (L.obj C) 1)
    exact hC
  have hsurjective :=
    CategoryTheory.Sheaf.H.longSequence_surjective_of_subsingleton_H
      hS₁L (isTerminalTop : IsTerminal (⊤ : Opens (U : Scheme)))
  change Function.Surjective
    ((L.map (cokernel.π (Injective.ι C))).hom.app
      (op (⊤ : Opens (U : Scheme)))) at hsurjective
  change Function.Surjective
    ((cokernel.π (Injective.ι C)).hom.app
      (op (U.ι.isOpenEmbedding.functor.obj
        (⊤ : Opens (U : Scheme))))) at hsurjective
  have htop : U.ι.isOpenEmbedding.functor.obj
      (⊤ : Opens (U : Scheme)) = U := by
    ext x
    simp
  rw [htop] at hsurjective
  exact hsurjective

namespace LocalKilling

/-- Every degree-three class of a quasicoherent module on an affine spectrum
is killed by restriction to a finite affine open cover. -/
theorem schemeHThree_finiteAffineKillingCover
    {R : CommRingCat.{u}} (M : (Spec R).Modules) [M.IsQuasicoherent]
    (c : H M 3) :
    ∃ (I : Type u) (U : I → (Spec R).Opens),
      Finite I ∧
      IsOpenCover U ∧
      (∀ i, IsAffine (U i)) ∧
      (∀ i, (zariskiFunctor (Spec R) 3).map
        ((Scheme.Modules.restrictAdjunction (U i).ι).unit.app M) c = 0) ∧
      (zariskiFunctor (Spec R) 3).map
        (toAffineCoverModule M U) c = 0 := by
  exact schemeHThree_finiteAffineKillingCover_of_affine_cokernel_app_surjective
    M c (injectiveCokernel_app_surjective_of_isAffineOpen M)
      (secondInjectiveCokernel_app_surjective_of_isAffineOpen M)

end LocalKilling

/-- Genuine Ext-based `H³` of a quasicoherent scheme module on an affine
spectrum is subsingleton. -/
theorem moduleSpecHThree_subsingleton
    {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [M.IsQuasicoherent] : Subsingleton (H M 3) := by
  refine subsingleton_of_forall_eq 0 fun c ↦ ?_
  obtain ⟨I, U, hfinite, hcover, haffine, _, hkilled⟩ :=
    LocalKilling.schemeHThree_finiteAffineKillingCover M c
  letI : Finite I := hfinite
  letI (i : I) : IsAffine (U i) := haffine i
  letI : (cokernel (toAffineCoverModule M U)).IsQuasicoherent :=
    affineCoverCokernel_isQuasicoherent M U
  letI : Subsingleton (H (cokernel (toAffineCoverModule M U)) 2) :=
    moduleSpecHTwo_subsingleton _
  apply toAffineCoverModule_H_succ_injective_of_cokernel_subsingleton
    M U hcover 2
  rw [hkilled, map_zero]

/-- Every genuine Ext-based degree-three class of a quasicoherent scheme
module on an affine spectrum is zero. -/
theorem moduleSpecHThree_eq_zero
    {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [M.IsQuasicoherent] (c : H M 3) : c = 0 := by
  letI : Subsingleton (H M 3) := moduleSpecHThree_subsingleton M
  exact Subsingleton.elim _ _

/-- Genuine degree-three cohomology of a quasicoherent module on any affine
scheme is subsingleton. -/
theorem moduleAffineHThree_subsingleton
    {X : Scheme.{u}} [IsAffine X] (M : X.Modules)
    [M.IsQuasicoherent] : Subsingleton (H M 3) := by
  let e := X.isoSpec
  let N := (Scheme.Modules.pushforward e.hom).obj M
  letI : N.IsQuasicoherent := isQuasicoherent_pushforward_iso
  have hN : Subsingleton (H N 3) := moduleSpecHThree_subsingleton N
  letI : Subsingleton (H N 3) := hN
  letI : Subsingleton (CategoryTheory.Sheaf.H
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom.base).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) 3) := by
    change Subsingleton (H N 3)
    exact hN
  exact sheafH_subsingleton_of_iso e
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) 3

/-- Every genuine Ext-based degree-three class of a quasicoherent module on
an affine scheme is zero. -/
theorem moduleAffineHThree_eq_zero
    {X : Scheme.{u}} [IsAffine X] (M : X.Modules)
    [M.IsQuasicoherent] (c : H M 3) : c = 0 := by
  letI : Subsingleton (H M 3) := moduleAffineHThree_subsingleton M
  exact Subsingleton.elim _ _

end MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology
