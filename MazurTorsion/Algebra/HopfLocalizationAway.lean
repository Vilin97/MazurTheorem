/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Principal-open localization of a commutative Hopf algebra

Let `A` be a commutative Hopf algebra over `R`, and let `x : A`.  The principal open
`Spec A[1/x]` is stable under the group operations when the images of `x` under
comultiplication, counit, and antipode become units in the appropriate targets.  Under exactly
those hypotheses, this file descends the three Hopf structure maps to `Localization.Away x`.

The hypotheses are deliberately stated as unit conditions rather than by requiring `x` to be
group-like.  This is what is needed for open subgroup schemes whose special fibre loses some
connected components.  The constant-flat construction is the first downstream consumer.
-/

noncomputable section

open WithConv
open scoped TensorProduct

namespace HopfLocalizationAway

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A]
variable (x : A)

/-- The coordinate ring of the principal open cut out by `x`. -/
abbrev Ring := Localization.Away x

variable (hcomul : IsUnit
  ((Algebra.TensorProduct.map
      (Algebra.algHom R A (Ring x)) (Algebra.algHom R A (Ring x))).comp
    (Bialgebra.comulAlgHom R A) x))

/-- Comultiplication descended to the principal localization. -/
noncomputable def comul : Ring x →ₐ[R] Ring x ⊗[R] Ring x :=
  IsLocalization.Away.liftAlgHom x hcomul

variable (hcounit : IsUnit (Bialgebra.counitAlgHom R A x))

/-- Counit descended to the principal localization. -/
noncomputable def counit : Ring x →ₐ[R] R :=
  IsLocalization.Away.liftAlgHom x hcounit

@[simp]
theorem comul_algebraMap (a : A) :
    comul x hcomul (algebraMap A (Ring x) a) =
      Algebra.TensorProduct.map (Algebra.algHom R A (Ring x))
        (Algebra.algHom R A (Ring x)) (Bialgebra.comulAlgHom R A a) := by
  change IsLocalization.Away.liftAlgHom x hcomul (algebraMap A (Ring x) a) = _
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

@[simp]
theorem counit_algebraMap (a : A) :
    counit x hcounit (algebraMap A (Ring x) a) =
      Bialgebra.counitAlgHom R A a := by
  change IsLocalization.Away.liftAlgHom x hcounit (algebraMap A (Ring x) a) = _
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

private abbrev iota : A →ₐ[R] Ring x := Algebra.algHom R A (Ring x)

@[simp]
private theorem iota_apply (a : A) :
    iota (R := R) x a = algebraMap A (Ring x) a := rfl

@[simp]
private theorem comul_comp_iota :
    (comul x hcomul).comp (iota (R := R) x) =
      (Algebra.TensorProduct.map (iota (R := R) x) (iota (R := R) x)).comp
        (Bialgebra.comulAlgHom R A) := by
  apply AlgHom.ext
  intro a
  exact comul_algebraMap x hcomul a

@[simp]
private theorem counit_comp_iota :
    (counit x hcounit).comp (iota (R := R) x) =
      Bialgebra.counitAlgHom R A := by
  apply AlgHom.ext
  intro a
  exact counit_algebraMap x hcounit a

private theorem map_comul_iota_natural (t : A ⊗[R] A) :
    Algebra.TensorProduct.map (comul x hcomul) (AlgHom.id R (Ring x))
        (Algebra.TensorProduct.map (iota (R := R) x) (iota (R := R) x) t) =
      Algebra.TensorProduct.map
        (Algebra.TensorProduct.map (iota (R := R) x) (iota (R := R) x))
          (iota (R := R) x)
          (Algebra.TensorProduct.map (Bialgebra.comulAlgHom R A) (AlgHom.id R A) t) := by
  change ((Algebra.TensorProduct.map (comul x hcomul) (AlgHom.id R (Ring x))).comp
      (Algebra.TensorProduct.map (iota (R := R) x) (iota (R := R) x))) t = _
  rw [← Algebra.TensorProduct.map_comp]
  rw [comul_comp_iota]
  change Algebra.TensorProduct.map
      ((Algebra.TensorProduct.map (iota (R := R) x) (iota (R := R) x)).comp
        (Bialgebra.comulAlgHom R A)) (iota (R := R) x) t = _
  simpa only [AlgHom.comp_id, AlgHom.id_comp, AlgHom.comp_apply] using congrArg (fun q ↦ q t)
    (Algebra.TensorProduct.map_comp
      (Algebra.TensorProduct.map (iota (R := R) x) (iota (R := R) x))
      (Bialgebra.comulAlgHom R A) (iota (R := R) x) (AlgHom.id R A))

private theorem map_iota_comul_natural (t : A ⊗[R] A) :
    Algebra.TensorProduct.map (AlgHom.id R (Ring x)) (comul x hcomul)
        (Algebra.TensorProduct.map (iota (R := R) x) (iota (R := R) x) t) =
      Algebra.TensorProduct.map (iota (R := R) x)
        (Algebra.TensorProduct.map (iota (R := R) x) (iota (R := R) x))
          (Algebra.TensorProduct.map (AlgHom.id R A) (Bialgebra.comulAlgHom R A) t) := by
  change ((Algebra.TensorProduct.map (AlgHom.id R (Ring x)) (comul x hcomul)).comp
      (Algebra.TensorProduct.map (iota (R := R) x) (iota (R := R) x))) t = _
  rw [← Algebra.TensorProduct.map_comp]
  rw [comul_comp_iota]
  change Algebra.TensorProduct.map (iota (R := R) x)
      ((Algebra.TensorProduct.map (iota (R := R) x) (iota (R := R) x)).comp
        (Bialgebra.comulAlgHom R A)) t = _
  simpa only [AlgHom.comp_id, AlgHom.id_comp, AlgHom.comp_apply] using congrArg (fun q ↦ q t)
    (Algebra.TensorProduct.map_comp (iota (R := R) x) (AlgHom.id R A)
      (Algebra.TensorProduct.map (iota (R := R) x) (iota (R := R) x))
      (Bialgebra.comulAlgHom R A))

private theorem assoc_iota_natural (t : (A ⊗[R] A) ⊗[R] A) :
    Algebra.TensorProduct.assoc R R R (Ring x) (Ring x) (Ring x)
        (Algebra.TensorProduct.map
          (Algebra.TensorProduct.map (iota (R := R) x) (iota (R := R) x))
            (iota (R := R) x) t) =
      Algebra.TensorProduct.map (iota (R := R) x)
        (Algebra.TensorProduct.map (iota (R := R) x) (iota (R := R) x))
          (Algebra.TensorProduct.assoc R R R A A A t) := by
  exact (TensorProduct.map_map_assoc (iota (R := R) x).toLinearMap
    (iota (R := R) x).toLinearMap (iota (R := R) x).toLinearMap t).symm

private theorem map_counit_iota_natural (t : A ⊗[R] A) :
    Algebra.TensorProduct.map (counit x hcounit) (AlgHom.id R (Ring x))
        (Algebra.TensorProduct.map (iota (R := R) x) (iota (R := R) x) t) =
      Algebra.TensorProduct.map (AlgHom.id R R) (iota (R := R) x)
        (Algebra.TensorProduct.map (Bialgebra.counitAlgHom R A) (AlgHom.id R A) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
      change counit x hcounit (algebraMap A (Ring x) a) ⊗ₜ[R]
          algebraMap A (Ring x) b = _
      rw [counit_algebraMap]
      rfl
  | add a b ha hb => simp only [map_add, ha, hb]

private theorem map_iota_counit_natural (t : A ⊗[R] A) :
    Algebra.TensorProduct.map (AlgHom.id R (Ring x)) (counit x hcounit)
        (Algebra.TensorProduct.map (iota (R := R) x) (iota (R := R) x) t) =
      Algebra.TensorProduct.map (iota (R := R) x) (AlgHom.id R R)
        (Algebra.TensorProduct.map (AlgHom.id R A) (Bialgebra.counitAlgHom R A) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
      change algebraMap A (Ring x) a ⊗ₜ[R]
          counit x hcounit (algebraMap A (Ring x) b) = _
      rw [counit_algebraMap]
      rfl
  | add a b ha hb => simp only [map_add, ha, hb]

private theorem coassoc :
    ((Algebra.TensorProduct.assoc R R R (Ring x) (Ring x) (Ring x)).toAlgHom).comp
        ((Algebra.TensorProduct.map (comul x hcomul) (AlgHom.id R (Ring x))).comp
          (comul x hcomul)) =
      (Algebra.TensorProduct.map (AlgHom.id R (Ring x)) (comul x hcomul)).comp
        (comul x hcomul) := by
  apply IsLocalization.algHom_ext (Submonoid.powers x)
  apply AlgHom.ext
  intro a
  simp only [AlgHom.comp_apply]
  change (Algebra.TensorProduct.assoc R R R (Ring x) (Ring x) (Ring x))
      (Algebra.TensorProduct.map (comul x hcomul) (AlgHom.id R (Ring x))
        (comul x hcomul (algebraMap A (Ring x) a))) =
    Algebra.TensorProduct.map (AlgHom.id R (Ring x)) (comul x hcomul)
      (comul x hcomul (algebraMap A (Ring x) a))
  rw [comul_algebraMap]
  rw [map_comul_iota_natural, assoc_iota_natural, map_iota_comul_natural]
  congr 1
  exact Coalgebra.coassoc_apply a

private theorem rTensor_counit :
    (Algebra.TensorProduct.map (counit x hcounit) (AlgHom.id R (Ring x))).comp
        (comul x hcomul) =
      (Algebra.TensorProduct.lid R (Ring x)).symm.toAlgHom := by
  apply IsLocalization.algHom_ext (Submonoid.powers x)
  apply AlgHom.ext
  intro a
  simp only [AlgHom.comp_apply]
  change Algebra.TensorProduct.map (counit x hcounit) (AlgHom.id R (Ring x))
      (comul x hcomul (algebraMap A (Ring x) a)) =
    (Algebra.TensorProduct.lid R (Ring x)).symm (algebraMap A (Ring x) a)
  rw [comul_algebraMap, map_counit_iota_natural]
  change Algebra.TensorProduct.map (AlgHom.id R R) (iota (R := R) x)
      (Coalgebra.counit.rTensor A (Coalgebra.comul a)) = _
  rw [Coalgebra.rTensor_counit_comul]
  simp

private theorem lTensor_counit :
    (Algebra.TensorProduct.map (AlgHom.id R (Ring x)) (counit x hcounit)).comp
        (comul x hcomul) =
      (Algebra.TensorProduct.rid R R (Ring x)).symm.toAlgHom := by
  apply IsLocalization.algHom_ext (Submonoid.powers x)
  apply AlgHom.ext
  intro a
  simp only [AlgHom.comp_apply]
  change Algebra.TensorProduct.map (AlgHom.id R (Ring x)) (counit x hcounit)
      (comul x hcomul (algebraMap A (Ring x) a)) =
    (Algebra.TensorProduct.rid R R (Ring x)).symm (algebraMap A (Ring x) a)
  rw [comul_algebraMap, map_iota_counit_natural]
  change Algebra.TensorProduct.map (iota (R := R) x) (AlgHom.id R R)
      (Coalgebra.counit.lTensor A (Coalgebra.comul a)) = _
  rw [Coalgebra.lTensor_counit_comul]
  simp

/-- The bialgebra structure descended to the principal localization. -/
@[instance_reducible]
noncomputable def bialgebra : Bialgebra R (Ring x) :=
  Bialgebra.ofAlgHom (comul x hcomul) (counit x hcounit)
    (coassoc x hcomul) (rTensor_counit x hcomul hcounit)
      (lTensor_counit x hcomul hcounit)

variable (hantipode : IsUnit
  (((Algebra.algHom R A (Ring x)).comp (HopfAlgebra.antipodeAlgHom R A)) x))

/-- Antipode descended to the principal localization. -/
noncomputable def antipode : Ring x →ₐ[R] Ring x :=
  IsLocalization.Away.liftAlgHom x
    (f := (Algebra.algHom R A (Ring x)).comp (HopfAlgebra.antipodeAlgHom R A)) hantipode

@[simp]
theorem antipode_algebraMap (a : A) :
    antipode x hantipode (algebraMap A (Ring x) a) =
      algebraMap A (Ring x) (HopfAlgebra.antipodeAlgHom R A a) := by
  change IsLocalization.Away.liftAlgHom x hantipode (algebraMap A (Ring x) a) = _
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

private theorem lift_antipode_iota_natural (t : A ⊗[R] A) :
    Algebra.TensorProduct.lift (antipode x hantipode) (AlgHom.id R (Ring x))
        (fun _ _ ↦ Commute.all _ _)
        (Algebra.TensorProduct.map (iota (R := R) x) (iota (R := R) x) t) =
      iota (R := R) x
        (Algebra.TensorProduct.lift (HopfAlgebra.antipodeAlgHom R A) (AlgHom.id R A)
          (fun _ _ ↦ Commute.all _ _) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
      change antipode x hantipode (algebraMap A (Ring x) a) *
        algebraMap A (Ring x) b = _
      rw [antipode_algebraMap]
      simp [Algebra.TensorProduct.lift_tmul]
  | add a b ha hb => simp only [map_add, ha, hb]

private theorem lift_iota_antipode_natural (t : A ⊗[R] A) :
    Algebra.TensorProduct.lift (AlgHom.id R (Ring x)) (antipode x hantipode)
        (fun _ _ ↦ Commute.all _ _)
        (Algebra.TensorProduct.map (iota (R := R) x) (iota (R := R) x) t) =
      iota (R := R) x
        (Algebra.TensorProduct.lift (AlgHom.id R A) (HopfAlgebra.antipodeAlgHom R A)
          (fun _ _ ↦ Commute.all _ _) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
      change algebraMap A (Ring x) a *
        antipode x hantipode (algebraMap A (Ring x) b) = _
      rw [antipode_algebraMap]
      simp [Algebra.TensorProduct.lift_tmul]
  | add a b ha hb => simp only [map_add, ha, hb]

private theorem mul_antipode_rTensor_comul :
    (Algebra.TensorProduct.lift (antipode x hantipode) (AlgHom.id R (Ring x))
      (fun _ _ ↦ Commute.all _ _)).comp (comul x hcomul) =
        (Algebra.ofId R (Ring x)).comp (counit x hcounit) := by
  apply IsLocalization.algHom_ext (Submonoid.powers x)
  apply AlgHom.ext
  intro a
  change Algebra.TensorProduct.lift (antipode x hantipode) (AlgHom.id R (Ring x))
      (fun _ _ ↦ Commute.all _ _)
        (comul x hcomul (algebraMap A (Ring x) a)) =
    algebraMap R (Ring x) (counit x hcounit (algebraMap A (Ring x) a))
  rw [comul_algebraMap, lift_antipode_iota_natural, counit_algebraMap]
  have h :
      (Algebra.TensorProduct.lift (HopfAlgebra.antipodeAlgHom R A) (AlgHom.id R A)
        (fun _ _ ↦ Commute.all _ _)).comp (Bialgebra.comulAlgHom R A) =
          (Algebra.ofId R A).comp (Bialgebra.counitAlgHom R A) := by
    apply AlgHom.toLinearMap_injective
    simpa [← Algebra.TensorProduct.lmul'_comp_map] using!
      (HopfAlgebra.mul_antipode_rTensor_comul (R := R) (A := A))
  have ha := congrArg (fun q : A →ₐ[R] A ↦ q a) h
  have hai := congrArg (iota (R := R) x) ha
  calc
    _ = algebraMap A (Ring x)
        (algebraMap R A (Bialgebra.counitAlgHom R A a)) := by
      simpa only [AlgHom.comp_apply, Algebra.ofId_apply, iota_apply] using hai
    _ = algebraMap R (Ring x) (Bialgebra.counitAlgHom R A a) :=
      (IsScalarTower.algebraMap_apply R A (Ring x) _).symm

private theorem mul_antipode_lTensor_comul :
    (Algebra.TensorProduct.lift (AlgHom.id R (Ring x)) (antipode x hantipode)
      (fun _ _ ↦ Commute.all _ _)).comp (comul x hcomul) =
        (Algebra.ofId R (Ring x)).comp (counit x hcounit) := by
  apply IsLocalization.algHom_ext (Submonoid.powers x)
  apply AlgHom.ext
  intro a
  change Algebra.TensorProduct.lift (AlgHom.id R (Ring x)) (antipode x hantipode)
      (fun _ _ ↦ Commute.all _ _)
        (comul x hcomul (algebraMap A (Ring x) a)) =
    algebraMap R (Ring x) (counit x hcounit (algebraMap A (Ring x) a))
  rw [comul_algebraMap, lift_iota_antipode_natural, counit_algebraMap]
  have h :
      (Algebra.TensorProduct.lift (AlgHom.id R A) (HopfAlgebra.antipodeAlgHom R A)
        (fun _ _ ↦ Commute.all _ _)).comp (Bialgebra.comulAlgHom R A) =
          (Algebra.ofId R A).comp (Bialgebra.counitAlgHom R A) := by
    apply AlgHom.toLinearMap_injective
    simpa [← Algebra.TensorProduct.lmul'_comp_map] using!
      (HopfAlgebra.mul_antipode_lTensor_comul (R := R) (A := A))
  have ha := congrArg (fun q : A →ₐ[R] A ↦ q a) h
  have hai := congrArg (iota (R := R) x) ha
  calc
    _ = algebraMap A (Ring x)
        (algebraMap R A (Bialgebra.counitAlgHom R A a)) := by
      simpa only [AlgHom.comp_apply, Algebra.ofId_apply, iota_apply] using hai
    _ = algebraMap R (Ring x) (Bialgebra.counitAlgHom R A a) :=
      (IsScalarTower.algebraMap_apply R A (Ring x) _).symm

/-- The Hopf algebra structure descended to the principal localization.  Install `bialgebra`
as an instance before installing this structure. -/
@[instance_reducible]
noncomputable def hopfAlgebra : HopfAlgebra R (Ring x) := by
  letI := bialgebra x hcomul hcounit
  exact HopfAlgebra.ofAlgHom (antipode x hantipode)
    (mul_antipode_rTensor_comul x hcomul hcounit hantipode)
      (mul_antipode_lTensor_comul x hcomul hcounit hantipode)

end HopfLocalizationAway
