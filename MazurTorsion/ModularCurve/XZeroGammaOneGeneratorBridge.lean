/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassGeometricIntegrality
import EllipticCurves.Mathlib.EllipticCurvePoint

/-!
# A rational cyclic generator as a geometric section

This file relates the generator chosen by a split rational `Gamma_0(N)` datum to its coordinate
base change and to the corresponding point of the concrete projective Weierstrass cubic.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped WeierstrassCurve.Affine
open scoped CategoryTheory.MonObj

namespace MazurTorsion.ModularCurve.XZeroModuli

open XZeroFiniteFlatModuli
open XZeroFiniteFlatModuli.WeierstrassProjectiveCubic

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [DecidableEq K] [DecidableEq L]
  {N : ℕ} [NeZero N]

local instance (x : RationalDatum K N) : (x.curve⁄L).IsElliptic :=
  inferInstanceAs ((x.curve.map (algebraMap K L)).IsElliptic)

/-- The chosen rational cyclic generator after extension to a field `L`. -/
noncomputable def RationalDatum.generatorPointMap (x : RationalDatum K N) :
    (x.curve⁄L).toAffine.Point :=
  x.curve.toAffine.pointMap L x.generator

/-- Injectivity of coordinate base change preserves the exact order of the chosen generator. -/
@[simp]
theorem RationalDatum.addOrderOf_generatorPointMap (x : RationalDatum K N) :
    addOrderOf (x.generatorPointMap (L := L)) = N := by
  exact (addOrderOf_injective (x.curve.toAffine.pointMap L)
    (WeierstrassCurve.Affine.pointMap_injective x.curve.toAffine L) x.generator).trans
      x.addOrderOf_generator

/-- The corresponding projective point of the coefficient-extended Weierstrass curve. -/
noncomputable def RationalDatum.generatorProjectivePointMap (x : RationalDatum K N) :
    (x.curve⁄L).toProjective.Point :=
  (WeierstrassCurve.Projective.Point.toAffineAddEquiv (x.curve⁄L)).symm
    (x.generatorPointMap (L := L))

/-- The projective marked point retains exact order `N`. -/
@[simp]
theorem RationalDatum.addOrderOf_generatorProjectivePointMap (x : RationalDatum K N) :
    addOrderOf (x.generatorProjectivePointMap (L := L)) = N := by
  let e := WeierstrassCurve.Projective.Point.toAffineAddEquiv (x.curve⁄L)
  calc
    addOrderOf (x.generatorProjectivePointMap (L := L)) =
        addOrderOf (e (x.generatorProjectivePointMap (L := L))) :=
      (e.addOrderOf_eq _).symm
    _ = addOrderOf (x.generatorPointMap (L := L)) :=
      congrArg addOrderOf (e.apply_symm_apply (x.generatorPointMap (L := L)))
    _ = N := x.addOrderOf_generatorPointMap (L := L)

/-- The chosen generator as an `L`-valued section of the concrete mapped cubic. -/
noncomputable def RationalDatum.generatorGeometricSection (x : RationalDatum K N) :
    AffineCommGroupScheme.testObject (R := L) L ⟶
      toOver (x.curve⁄L) :=
  projectivePointOverMorphism (x.curve⁄L)
    (x.generatorProjectivePointMap (L := L))

/-- The chosen generator as a projective point over the original field. -/
noncomputable def RationalDatum.generatorProjectivePoint (x : RationalDatum K N) :
    x.curve.toProjective.Point :=
  (WeierstrassCurve.Projective.Point.toAffineAddEquiv x.curve).symm x.generator

/-- The chosen generator as a section of the concrete cubic over the original field. -/
noncomputable def RationalDatum.generatorSection (x : RationalDatum K N) :
    AffineCommGroupScheme.testObject (R := K) K ⟶ toOver x.curve :=
  projectivePointOverMorphism x.curve x.generatorProjectivePoint

/-- Precomposition with `Spec L ⟶ Spec K` on points of the concrete cubic. -/
noncomputable def RationalDatum.fieldExtensionRestrictionHom
    (x : RationalDatum K N) [GrpObj (toOver x.curve)] :
    (AffineCommGroupScheme.testObject (R := K) K ⟶ toOver x.curve) →*
      (AffineCommGroupScheme.testObject (R := K) L ⟶ toOver x.curve) :=
  ((yonedaGrpObj (toOver x.curve)).map
    (AffineCommGroupScheme.testObjectMap (R := K) (Algebra.ofId K L)).op).hom

omit [DecidableEq L] in
@[simp]
theorem RationalDatum.fieldExtensionRestrictionHom_apply
    (x : RationalDatum K N) [GrpObj (toOver x.curve)]
    (s : AffineCommGroupScheme.testObject (R := K) K ⟶ toOver x.curve) :
    x.fieldExtensionRestrictionHom (L := L) s =
      AffineCommGroupScheme.testObjectMap (R := K) (Algebra.ofId K L) ≫ s :=
  rfl

/-- The chosen generator section pulled back to `Spec L`, still viewed as a point of the
original `K`-group scheme. -/
noncomputable def RationalDatum.generatorSectionPullback
    (x : RationalDatum K N) [GrpObj (toOver x.curve)] :
    AffineCommGroupScheme.testObject (R := K) L ⟶ toOver x.curve :=
  x.fieldExtensionRestrictionHom (L := L) x.generatorSection

omit [DecidableEq L] in
/-- Field extension is faithfully flat, so restriction of represented points is injective. -/
theorem RationalDatum.fieldExtensionRestrictionHom_injective
    (x : RationalDatum K N) [GrpObj (toOver x.curve)] :
    Function.Injective (x.fieldExtensionRestrictionHom (L := L)) := by
  let f := AffineCommGroupScheme.testObjectMap (R := K) (Algebra.ofId K L)
  letI : Epi f.left := by
    change Epi (Spec.map (CommRingCat.ofHom (algebraMap K L)))
    infer_instance
  letI : Epi f := Over.epi_of_epi_left f
  intro a b h
  apply (cancel_epi f).1
  exact h

/-- The marked section on the reconstructed coefficient-extended cubic has exact order `N`
whenever the concrete cubic carries its canonical geometric group law. -/
theorem RationalDatum.orderOf_generatorGeometricSection
    (x : RationalDatum K N) [GrpObj (toOver (x.curve⁄L))]
    [GeometricallyIntegral (toOver (x.curve⁄L)).hom]
    (hgroup : CanonicalPointGroupLawCompatibility (x.curve⁄L)) :
    orderOf (x.generatorGeometricSection (L := L)) = N := by
  let e := canonicalProjectivePointEquivOfGroupLaw (x.curve⁄L)
    hgroup.map_zero hgroup.map_add
  calc
    orderOf (x.generatorGeometricSection (L := L)) =
        orderOf (e (Multiplicative.ofAdd
          (x.generatorProjectivePointMap (L := L)))) := rfl
    _ = orderOf (Multiplicative.ofAdd
        (x.generatorProjectivePointMap (L := L))) := e.orderOf_eq _
    _ = addOrderOf (x.generatorProjectivePointMap (L := L)) := rfl
    _ = N := x.addOrderOf_generatorProjectivePointMap (L := L)

/-- The marked section has exact multiplicative order `N` over the ground field. -/
theorem RationalDatum.orderOf_generatorSection
    (x : RationalDatum K N) [GrpObj (toOver x.curve)]
    [GeometricallyIntegral (toOver x.curve).hom]
    (hgroup : CanonicalPointGroupLawCompatibility x.curve) :
    orderOf x.generatorSection = N := by
  let e := canonicalProjectivePointEquivOfGroupLaw x.curve
    hgroup.map_zero hgroup.map_add
  calc
    orderOf x.generatorSection =
        orderOf (e (Multiplicative.ofAdd x.generatorProjectivePoint)) := rfl
    _ = orderOf (Multiplicative.ofAdd x.generatorProjectivePoint) :=
      e.orderOf_eq _
    _ = addOrderOf x.generatorProjectivePoint := rfl
    _ = addOrderOf x.generator := by
      let a := WeierstrassCurve.Projective.Point.toAffineAddEquiv x.curve
      exact (a.addOrderOf_eq x.generatorProjectivePoint).symm.trans <| by
        change addOrderOf (a (a.symm x.generator)) = addOrderOf x.generator
        rw [a.apply_symm_apply]
    _ = N := x.addOrderOf_generator

omit [DecidableEq L] in
/-- Every field-extension pullback of the marked generator section has exact order `N`.
This is the fibrewise exact-order statement required by a naive `Gamma_1(N)` structure. -/
theorem RationalDatum.orderOf_generatorSectionPullback
    (x : RationalDatum K N) [GrpObj (toOver x.curve)]
    [GeometricallyIntegral (toOver x.curve).hom]
    (hgroup : CanonicalPointGroupLawCompatibility x.curve) :
    orderOf (x.generatorSectionPullback (L := L)) = N := by
  calc
    orderOf (x.generatorSectionPullback (L := L)) =
        orderOf x.generatorSection :=
      orderOf_injective (x.fieldExtensionRestrictionHom (L := L))
        (x.fieldExtensionRestrictionHom_injective (L := L)) x.generatorSection
    _ = N := x.orderOf_generatorSection hgroup

/-- The geometric section and coordinate base change have the same exact order.  This avoids
asserting an unproved equality between the reduced-cubic pullback and the reconstructed mapped
cubic while providing precisely the order comparison used by the level predicate. -/
theorem RationalDatum.orderOf_generatorSectionPullback_eq_addOrderOf_generatorPointMap
    (x : RationalDatum K N) [GrpObj (toOver x.curve)]
    [GeometricallyIntegral (toOver x.curve).hom]
    (hgroup : CanonicalPointGroupLawCompatibility x.curve) :
    orderOf (x.generatorSectionPullback (L := L)) =
      addOrderOf (x.generatorPointMap (L := L)) := by
  rw [x.orderOf_generatorSectionPullback hgroup,
    x.addOrderOf_generatorPointMap]

/-- Concrete order-49 consumer of the fibrewise marked-section theorem. -/
theorem RationalDatum.orderOf_generatorSectionPullback_fortyNine
    (x : RationalDatum ℚ 49) [GrpObj (toOver x.curve)]
    [GeometricallyIntegral (toOver x.curve).hom]
    (hgroup : CanonicalPointGroupLawCompatibility x.curve)
    (L : Type) [Field L] [Algebra ℚ L] :
    orderOf (x.generatorSectionPullback (L := L)) = 49 :=
  x.orderOf_generatorSectionPullback hgroup

end MazurTorsion.ModularCurve.XZeroModuli
