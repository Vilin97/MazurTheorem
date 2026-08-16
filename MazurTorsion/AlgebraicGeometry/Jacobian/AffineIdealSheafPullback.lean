/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Pulling back products of ideal sheaves between affine schemes

For a morphism between affine schemes, pullback of an ideal sheaf is the
extension of its global ideal along the induced map on global sections.
Extension of ideals preserves products, so affine pullback preserves finite
products of ideal sheaves along an arbitrary morphism.

The ring calculation is proved from the tensor-product presentation of a
pushout along a surjection.  The named downstream consumer is
`PointedIncidenceDescent`, where the affine fpqc split chart pulls back the
product defining the ordered incidence family.
-/

noncomputable section

universe u

open CategoryTheory Limits
open scoped TensorProduct
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.AffineIdealSheafPullback

private theorem includeLeft_ker_of_surjective
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (g : R →ₐ[R] T) (hg : Function.Surjective g) :
    RingHom.ker
        (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T) =
      Ideal.map (algebraMap R S) (RingHom.ker g) := by
  let e := Algebra.TensorProduct.rid R R S
  have hcomp :
      (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T).comp
          e.toAlgHom =
        Algebra.TensorProduct.map (AlgHom.id R S) g := by
    ext
    simp [e]
  calc
    RingHom.ker
          (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T) =
        Ideal.map e
          (Ideal.comap e
            (RingHom.ker
              (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T))) :=
      (Ideal.map_comap_eq_self_of_equiv e _).symm
    _ = Ideal.map e
        (RingHom.ker
          ((Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T).comp
            e.toAlgHom)) := by
      congr 1
    _ = Ideal.map e
        (RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R S) g)) := by
      rw [hcomp]
    _ = Ideal.map e
        (Ideal.map Algebra.TensorProduct.includeRight (RingHom.ker g)) := by
      rw [Algebra.TensorProduct.lTensor_ker g hg]
    _ = Ideal.map
        (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
        (RingHom.ker g) := by
      change Ideal.map e.toRingHom
        (Ideal.map Algebra.TensorProduct.includeRight.toRingHom
          (RingHom.ker g)) = _
      rw [Ideal.map_map]
    _ = Ideal.map (algebraMap R S) (RingHom.ker g) := by
      congr 2
      ext
      simp [e, Algebra.smul_def]

private theorem ker_eq_map_of_isPushout_of_surjective
    {R S T P : CommRingCat.{u}}
    (f : R ⟶ S) (g : R ⟶ T) (f' : S ⟶ P) (g' : T ⟶ P)
    (h : IsPushout f g f' g') (hg : Function.Surjective g.hom) :
    RingHom.ker f'.hom = Ideal.map f.hom (RingHom.ker g.hom) := by
  algebraize [f.hom, g.hom, f'.hom, g'.hom,
    f'.hom.comp f.hom]
  letI : IsScalarTower R S P :=
    .of_algebraMap_eq fun _ ↦ rfl
  letI : IsScalarTower R T P :=
    .of_algebraMap_eq fun x ↦ congr($(h.w).hom x)
  letI : Algebra.IsPushout R S T P :=
    CommRingCat.isPushout_iff_isPushout.mp h
  let e := Algebra.IsPushout.equiv R S T P
  have hf' :
      e.toRingHom.comp
          (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T) =
        f'.hom := by
    ext x
    exact e.commutes x
  calc
    RingHom.ker f'.hom = RingHom.ker
        (e.toRingHom.comp
          (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T)) := by
      rw [hf']
    _ = RingHom.ker
        (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T) :=
      RingHom.ker_equiv_comp _ e.toRingEquiv
    _ = Ideal.map (algebraMap R S)
        (RingHom.ker (Algebra.ofId R T)) :=
      includeLeft_ker_of_surjective (Algebra.ofId R T) hg
    _ = Ideal.map f.hom (RingHom.ker g.hom) := rfl

/-- On affine schemes, pulling back an ideal sheaf extends its global ideal
along the induced map on global sections. -/
theorem ideal_comap_top_eq_map_of_isAffine
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ =
      Ideal.map f.appTop.hom
        (I.ideal ⟨⊤, isAffineOpen_top Y⟩) := by
  letI : IsAffine I.subscheme :=
    isAffine_of_isAffineHom I.subschemeι
  have hker :
      RingHom.ker (pullback.fst f I.subschemeι).appTop.hom =
        Ideal.map f.appTop.hom
          (I.ideal ⟨⊤, isAffineOpen_top Y⟩) := by
    have hsurj : Function.Surjective I.subschemeι.appTop.hom := by
      change Function.Surjective
        (I.subschemeι.app (⊤ : Y.Opens)).hom
      exact I.subschemeι_app_surjective ⟨⊤, isAffineOpen_top Y⟩
    rw [ker_eq_map_of_isPushout_of_surjective
      f.appTop I.subschemeι.appTop
      (pullback.fst f I.subschemeι).appTop
      (pullback.snd f I.subschemeι).appTop
      (isPushout_appTop_of_isPullback
        (IsPullback.of_hasPullback f I.subschemeι)) hsurj]
    have hsub : RingHom.ker I.subschemeι.appTop.hom =
        I.ideal ⟨⊤, isAffineOpen_top Y⟩ := by
      change RingHom.ker
          (I.subschemeι.app (⊤ : Y.Opens)).hom = _
      exact I.ker_subschemeι_app ⟨⊤, isAffineOpen_top Y⟩
    rw [hsub]
  change (pullback.fst f I.subschemeι).ker.ideal
      ⟨⊤, isAffineOpen_top X⟩ = _
  rw [Scheme.ker_of_isAffine]
  simpa using hker

/-- Pullback along any morphism between affine schemes preserves products of
ideal sheaves. -/
theorem idealSheaf_comap_mul_of_isAffine
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (I J : Y.IdealSheafData) (f : X ⟶ Y) :
    (I * J).comap f = I.comap f * J.comap f := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  calc
    ((I * J).comap f).ideal ⟨⊤, isAffineOpen_top X⟩ =
        Ideal.map f.appTop.hom
          ((I * J).ideal ⟨⊤, isAffineOpen_top Y⟩) :=
      ideal_comap_top_eq_map_of_isAffine (I * J) f
    _ = Ideal.map f.appTop.hom
        (I.ideal ⟨⊤, isAffineOpen_top Y⟩ *
          J.ideal ⟨⊤, isAffineOpen_top Y⟩) := rfl
    _ = Ideal.map f.appTop.hom
          (I.ideal ⟨⊤, isAffineOpen_top Y⟩) *
        Ideal.map f.appTop.hom
          (J.ideal ⟨⊤, isAffineOpen_top Y⟩) :=
      Ideal.map_mul f.appTop.hom _ _
    _ = (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ *
        (J.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ := by
      rw [ideal_comap_top_eq_map_of_isAffine,
        ideal_comap_top_eq_map_of_isAffine]
    _ = (I.comap f * J.comap f).ideal
        ⟨⊤, isAffineOpen_top X⟩ := rfl

/-- Pullback along any morphism between affine schemes preserves finite
products of ideal sheaves. -/
theorem idealSheaf_comap_finsetProd_of_isAffine
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    {ι : Type*} (s : Finset ι) (F : ι → Y.IdealSheafData)
    (f : X ⟶ Y) :
    (s.prod F).comap f = s.prod (fun i ↦ (F i).comap f) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi,
        idealSheaf_comap_mul_of_isAffine, ih]

end MazurTorsion.AlgebraicGeometry.Jacobian.AffineIdealSheafPullback
