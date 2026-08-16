/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.UniversalEffectiveDivisor

/-!
# Restricting ordered incidence to an open chart

This file proves directly that pullback of ideal sheaves preserves products
along an open immersion: on each affine open, the restriction formula
transports ideals through a ring equivalence.  Consequently the
scheme-theoretic union defining ordered incidence restricts to the product
of the pulled-back coordinate-graph ideals, with all multiplicities retained.
The extension to arbitrary scheme morphisms is proved affine-locally in
`IdealSheafPullbackProduct`.

The named downstream consumer is the finite étale split-chart comparison in
`PointedIncidenceDescent`.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.OrderedIncidenceOpenRestriction

open UniversalEffectiveDivisor

/-- Pullback of ideal sheaves along an open immersion preserves products. -/
theorem idealSheaf_comap_mul_of_isOpenImmersion
    {X Y : Scheme.{u}} (I J : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] :
    (I * J).comap f = I.comap f * J.comap f := by
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : X.affineOpens ↦ U) (iSup_affineOpens_eq_top X)
  intro U
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  simp only [Scheme.IdealSheafData.ideal_mul]
  change _ = (I.comap f).ideal U * (J.comap f).ideal U
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion I f U,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion J f U]
  let e := (f.appIso U).commRingCatIsoToRingEquiv
  let K := I.ideal ⟨f ''ᵁ U, U.2.image_of_isOpenImmersion f⟩
  let L := J.ideal ⟨f ''ᵁ U, U.2.image_of_isOpenImmersion f⟩
  change (K * L).comap e.symm.toRingHom =
    K.comap e.symm.toRingHom * L.comap e.symm.toRingHom
  calc
    _ = (K * L).map e.toRingHom :=
      (Ideal.map_comap_of_equiv e).symm
    _ = K.map e.toRingHom * L.map e.toRingHom :=
      Ideal.map_mul e.toRingHom K L
    _ = _ := congrArg₂ (fun A B ↦ A * B)
      (Ideal.map_comap_of_equiv e) (Ideal.map_comap_of_equiv e)

/-- Pullback along an open immersion preserves a finite product of ideal
sheaves. -/
theorem idealSheaf_comap_finsetProd_of_isOpenImmersion
    {X Y : Scheme.{u}} {I : Type*} (s : Finset I)
    (F : I → Y.IdealSheafData) (f : X ⟶ Y) [IsOpenImmersion f] :
    (s.prod F).comap f = s.prod (fun i ↦ (F i).comap f) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi,
        idealSheaf_comap_mul_of_isOpenImmersion, ih]

variable (S : Scheme.{u}) (d : ℕ) (X : Over S)

/-- The ordered-incidence ideal restricted to an open chart is the product
of the individually restricted coordinate-graph ideals. -/
theorem orderedIncidenceIdeal_comap_of_isOpenImmersion
    [IsSeparated X.hom] {Y : Scheme.{u}}
    (f : Y ⟶ (orderedAmbient S d X).left) [IsOpenImmersion f] :
    (orderedIncidenceIdeal S d X).comap f =
      Finset.univ.prod (fun i ↦ (coordinateGraphIdeal S d X i).comap f) := by
  classical
  exact idealSheaf_comap_finsetProd_of_isOpenImmersion
    Finset.univ (coordinateGraphIdeal S d X) f

/-- Restricting one coordinate graph to an open chart gives the kernel of
the corresponding pullback closed immersion. -/
theorem coordinateGraphIdeal_comap_eq_pullbackKernel
    [IsSeparated X.hom] {Y : Scheme.{u}}
    (f : Y ⟶ (orderedAmbient S d X).left) (i : Fin d) :
    (coordinateGraphIdeal S d X i).comap f =
      (pullback.fst f (coordinateGraphι S d X i).left).ker := by
  rw [coordinateGraphIdeal]
  exact (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion
    (coordinateGraphι S d X i).left f).symm

/-- Scheme-theoretic open restriction of ordered incidence, expressed as
the product of the kernels of the pulled-back coordinate graphs. -/
theorem orderedIncidenceIdeal_comap_eq_prod_pullbackKernels
    [IsSeparated X.hom] {Y : Scheme.{u}}
    (f : Y ⟶ (orderedAmbient S d X).left) [IsOpenImmersion f] :
    (orderedIncidenceIdeal S d X).comap f =
      Finset.univ.prod (fun i ↦
        (pullback.fst f (coordinateGraphι S d X i).left).ker) := by
  rw [orderedIncidenceIdeal_comap_of_isOpenImmersion]
  congr 1
  funext i
  exact coordinateGraphIdeal_comap_eq_pullbackKernel S d X f i

/-- The restricted ordered-incidence subscheme is canonically the pullback
of the global ordered-incidence closed immersion. -/
noncomputable def orderedIncidenceOpenRestrictionIso
    [IsSeparated X.hom] {Y : Scheme.{u}}
    (f : Y ⟶ (orderedAmbient S d X).left) :
    ((orderedIncidenceIdeal S d X).comap f).subscheme ≅
      pullback f (orderedIncidenceι S d X) :=
  (orderedIncidenceIdeal S d X).comapIso f

@[reassoc]
theorem orderedIncidenceOpenRestrictionIso_hom_fst
    [IsSeparated X.hom] {Y : Scheme.{u}}
    (f : Y ⟶ (orderedAmbient S d X).left) :
    (orderedIncidenceOpenRestrictionIso S d X f).hom ≫
        pullback.fst f (orderedIncidenceι S d X) =
      ((orderedIncidenceIdeal S d X).comap f).subschemeι :=
  Scheme.IdealSheafData.comapIso_hom_fst
    (orderedIncidenceIdeal S d X) f

end MazurTorsion.AlgebraicGeometry.Jacobian.OrderedIncidenceOpenRestriction
