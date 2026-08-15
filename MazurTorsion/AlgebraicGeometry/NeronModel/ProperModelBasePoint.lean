/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.NeronModel.Basic
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# Rational points of proper group models

For a proper commutative group scheme over a valuation ring, the valuative criterion identifies
its integral points with the rational points of its generic fibre.  This is only the terminal-test
scheme consequence of properness; it does not assert the Neron mapping property for arbitrary
smooth test schemes.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj

namespace AlgebraicGeometry

universe u

namespace ProperModelBasePoint

variable {R K : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  {A : CommGroupScheme (Spec (.of K))}

private def underlyingGenericFiberIso (G : CommGroupScheme (Spec (.of R)))
    (e : genericFiber R K G ≅ A) :
    (Over.pullback (fractionSpecMap R K)).obj G.X ≅ A.X :=
  (CommGrp.forget (Over (Spec (.of K)))).mapIso e

private def pointMulEquivOfOverIso {S : Scheme.{u}} (G : CommGroupScheme S)
    {X Y : Over S} (e : X ≅ Y) : (X ⟶ G.X) ≃* (Y ⟶ G.X) where
  toFun x := e.inv ≫ x
  invFun y := e.hom ≫ y
  left_inv x := by simp
  right_inv y := by simp
  map_mul' x y := CategoryTheory.MonObj.comp_mul e.inv x y

/-- Restriction from integral points of `G` to rational points of its identified generic fibre. -/
def restriction (G : CommGroupScheme (Spec (.of R)))
    (e : genericFiber R K G ≅ A) :
    (Over.mk (𝟙 (Spec (.of R))) ⟶ G.X) →*
      (Over.mk (𝟙 (Spec (.of K))) ⟶ A.X) :=
  (pointMulEquivOfOverIso A (CartesianMonoidalCategory.preservesTerminalIso
      (Over.pullback (fractionSpecMap R K)))).toMonoidHom.comp
    (genericFiberRestriction R K G A e (Over.mk (𝟙 (Spec (.of R)))))

private def genericPoint (G : CommGroupScheme (Spec (.of R)))
    (e : genericFiber R K G ≅ A)
    (x : Over.mk (𝟙 (Spec (.of K))) ⟶ A.X) :
    Spec (.of K) ⟶ G.X.left :=
  (x ≫ (underlyingGenericFiberIso G e).inv).left ≫
    ((Over.mapPullbackAdj (fractionSpecMap R K)).counit.app G.X).left

private def valuativeSquare (G : CommGroupScheme (Spec (.of R)))
    (e : genericFiber R K G ≅ A)
    (x : Over.mk (𝟙 (Spec (.of K))) ⟶ A.X) :
    ValuativeCommSq G.X.hom where
  R := R
  K := K
  i₁ := genericPoint G e x
  i₂ := 𝟙 _
  commSq := ⟨by
    simp only [genericPoint]
    erw [Category.assoc,
      Over.w ((Over.mapPullbackAdj (fractionSpecMap R K)).counit.app G.X)]
    erw [← Category.assoc,
      Over.w (x ≫ (underlyingGenericFiberIso G e).inv)]
    rfl⟩

omit [IsDomain R] [ValuationRing R] in
private theorem valuativeCriterion (G : CommGroupScheme (Spec (.of R)))
    [IsProper G.X.hom] : ValuativeCriterion G.X.hom := by
  have h : IsProper G.X.hom := inferInstance
  rw [IsProper.eq_valuativeCriterion] at h
  exact h.1.1.1

private noncomputable def lift (G : CommGroupScheme (Spec (.of R)))
    [IsProper G.X.hom] (e : genericFiber R K G ≅ A)
    (x : Over.mk (𝟙 (Spec (.of K))) ⟶ A.X) :
    (valuativeSquare G e x).commSq.LiftStruct :=
  ((valuativeCriterion G (valuativeSquare G e x)).some).default

private noncomputable def extensionPoint (G : CommGroupScheme (Spec (.of R)))
    [IsProper G.X.hom] (e : genericFiber R K G ≅ A)
    (x : Over.mk (𝟙 (Spec (.of K))) ⟶ A.X) :
    Over.mk (𝟙 (Spec (.of R))) ⟶ G.X :=
  Over.homMk (lift G e x).l (lift G e x).fac_right

private theorem extensionPoint_left (G : CommGroupScheme (Spec (.of R)))
    [IsProper G.X.hom] (e : genericFiber R K G ≅ A)
    (x : Over.mk (𝟙 (Spec (.of K))) ⟶ A.X) :
    (extensionPoint G e x).left = (lift G e x).l :=
  rfl

private theorem lift_fac_left (G : CommGroupScheme (Spec (.of R)))
    [IsProper G.X.hom] (e : genericFiber R K G ≅ A)
    (x : Over.mk (𝟙 (Spec (.of K))) ⟶ A.X) :
    fractionSpecMap R K ≫ (lift G e x).l = genericPoint G e x := by
  exact (lift G e x).fac_left

private theorem terminalPullback_lift_fac_left
    (G : CommGroupScheme (Spec (.of R))) [IsProper G.X.hom]
    (e : genericFiber R K G ≅ A)
    (x : Over.mk (𝟙 (Spec (.of K))) ⟶ A.X) :
    (pullback.snd (𝟙 (Spec (.of R))) (fractionSpecMap R K) ≫
        fractionSpecMap R K) ≫ (lift G e x).l =
      pullback.snd (𝟙 (Spec (.of R))) (fractionSpecMap R K) ≫
        genericPoint G e x :=
  (Category.assoc _ _ _).trans
    (congrArg (pullback.snd (𝟙 (Spec (.of R))) (fractionSpecMap R K) ≫ ·)
      (lift_fac_left G e x))

omit [ValuationRing R] in
private theorem genericPoint_restriction (G : CommGroupScheme (Spec (.of R)))
    (e : genericFiber R K G ≅ A)
    (x : Over.mk (𝟙 (Spec (.of R))) ⟶ G.X) :
    genericPoint G e (restriction G e x) = fractionSpecMap R K ≫ x.left := by
  let f := fractionSpecMap R K
  let t := CartesianMonoidalCategory.preservesTerminalIso (Over.pullback f)
  let eu := underlyingGenericFiberIso G e
  change (t.inv ≫ (Over.pullback f).map x ≫ eu.hom ≫ eu.inv).left ≫
      ((Over.mapPullbackAdj f).counit.app G.X).left = f ≫ x.left
  have he : t.inv ≫ (Over.pullback f).map x ≫ eu.hom ≫ eu.inv =
      t.inv ≫ (Over.pullback f).map x := by simp
  rw [he]
  have hn := congrArg Over.Hom.left ((Over.mapPullbackAdj f).counit.naturality x)
  simp only [Functor.comp_map, Over.comp_left, Over.map_map_left, Functor.id_map] at hn
  simp only [Over.comp_left]
  rw [Category.assoc]
  rw [hn]
  rw [← Category.assoc]
  congr 1
  simp [t, f, Over.preservesTerminalIso_pullback, Over.mapPullbackAdj_counit_app]

private theorem restriction_extensionPoint (G : CommGroupScheme (Spec (.of R)))
    [IsProper G.X.hom] (e : genericFiber R K G ≅ A)
    (x : Over.mk (𝟙 (Spec (.of K))) ⟶ A.X) :
    restriction G e (extensionPoint G e x) = x := by
  let t := CartesianMonoidalCategory.preservesTerminalIso
    (Over.pullback (fractionSpecMap R K))
  let eu := underlyingGenericFiberIso G e
  change pointMulEquivOfOverIso A t
      (genericFiberRestriction R K G A e (Over.mk (𝟙 (Spec (.of R))))
        (extensionPoint G e x)) = x
  apply (pointMulEquivOfOverIso A t).symm.injective
  simp only [MulEquiv.symm_apply_apply]
  change genericFiberRestriction R K G A e (Over.mk (𝟙 (Spec (.of R))))
      (extensionPoint G e x) = t.hom ≫ x
  change (Over.pullback (fractionSpecMap R K)).map (extensionPoint G e x) ≫ eu.hom =
    t.hom ≫ x
  rw [← cancel_mono eu.inv]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  ext
  apply pullback.hom_ext
  · simp only [Over.pullback_map_left, pullback.lift_fst, extensionPoint_left]
    simp only [Over.mk_hom]
    rw [← Category.comp_id (pullback.fst (𝟙 (Spec (.of R)))
        (fractionSpecMap R K)), pullback.condition]
    rw [terminalPullback_lift_fac_left]
    simp [genericPoint, t, eu, Over.preservesTerminalIso_pullback,
      Over.mapPullbackAdj_counit_app]
  · simp only [Over.pullback_map_left, pullback.lift_snd]
    change pullback.snd (𝟙 (Spec (.of R))) (fractionSpecMap R K) =
      pullback.snd (𝟙 (Spec (.of R))) (fractionSpecMap R K) ≫
        (x ≫ eu.inv).left ≫ pullback.snd G.X.hom (fractionSpecMap R K)
    rw [← Over.pullback_obj_hom, Over.w (x ≫ eu.inv)]
    simp

private theorem restriction_bijective (G : CommGroupScheme (Spec (.of R)))
    [IsProper G.X.hom] (e : genericFiber R K G ≅ A) :
    Function.Bijective (restriction G e) := by
  constructor
  · intro x y hxy
    let sq := valuativeSquare G e (restriction G e x)
    let lx : sq.commSq.LiftStruct :=
      { l := x.left
        fac_left := (genericPoint_restriction G e x).symm
        fac_right := x.w }
    let ly : sq.commSq.LiftStruct :=
      { l := y.left
        fac_left := by
          change fractionSpecMap R K ≫ y.left = genericPoint G e (restriction G e x)
          rw [hxy]
          exact (genericPoint_restriction G e y).symm
        fac_right := y.w }
    let hUnique := (valuativeCriterion G sq).some
    have hl : lx = ly := (hUnique.uniq lx).trans (hUnique.uniq ly).symm
    apply Over.OverMorphism.ext
    exact congrArg (fun l ↦ l.l) hl
  · intro x
    exact ⟨extensionPoint G e x, restriction_extensionPoint G e x⟩

/-- Properness identifies integral points of a commutative group model with rational points of
its identified generic fibre. -/
noncomputable def mulEquiv (G : CommGroupScheme (Spec (.of R)))
    [IsProper G.X.hom] (e : genericFiber R K G ≅ A) :
    (Over.mk (𝟙 (Spec (.of R))) ⟶ G.X) ≃*
      (Over.mk (𝟙 (Spec (.of K))) ⟶ A.X) :=
  MulEquiv.ofBijective (restriction G e) (restriction_bijective G e)

/-- Extend a rational point uniquely to an integral point of its proper group model. -/
noncomputable def extension (G : CommGroupScheme (Spec (.of R)))
    [IsProper G.X.hom] (e : genericFiber R K G ≅ A) :
    (Over.mk (𝟙 (Spec (.of K))) ⟶ A.X) →*
      (Over.mk (𝟙 (Spec (.of R))) ⟶ G.X) :=
  (mulEquiv G e).symm.toMonoidHom

@[simp]
theorem restriction_extension (G : CommGroupScheme (Spec (.of R)))
    [IsProper G.X.hom] (e : genericFiber R K G ≅ A)
    (x : Over.mk (𝟙 (Spec (.of K))) ⟶ A.X) :
    restriction G e (extension G e x) = x :=
  (mulEquiv G e).apply_symm_apply x

@[simp]
theorem extension_restriction (G : CommGroupScheme (Spec (.of R)))
    [IsProper G.X.hom] (e : genericFiber R K G ≅ A)
    (x : Over.mk (𝟙 (Spec (.of R))) ⟶ G.X) :
    extension G e (restriction G e x) = x :=
  (mulEquiv G e).symm_apply_apply x

end ProperModelBasePoint

end AlgebraicGeometry
