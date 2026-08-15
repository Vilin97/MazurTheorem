/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassInfinityCompatibility

/-!
# Cross compatibilities in the affine Weierstrass addition atlas

The four-chart affine atlas has two cross overlaps not covered by the
same-slope and infinity/infinity comparisons.  This file treats those exact
principal opens.  It first compares the `D(B₁₂)` product-neighbourhood
formula with the vertical infinity formula on `D(B₁₂ Y_vert)`.

All transition identities are proved in localization rings from polynomial
cross-products.  No pointwise addition law or supplied group object is used.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

/-! ## The product-neighbourhood/vertical overlap -/

/-- Coordinate ring of `D(B₁₂ Y_vert)`. -/
abbrev productVerticalIntersectionCoordinateRing
    (W : WeierstrassCurve K) :=
  Localization.Away (additionB12 W * verticalAddYNumerator W)

/-- Restriction from `D(B₁₂)` to `D(B₁₂ Y_vert)`. -/
noncomputable def productNeighborhoodToVerticalIntersectionRing
    (W : WeierstrassCurve K) :
    productNeighborhoodCoordinateRing W →+*
      productVerticalIntersectionCoordinateRing W :=
  IsLocalization.Away.awayToAwayRight
    (S := productNeighborhoodCoordinateRing W)
    (P := productVerticalIntersectionCoordinateRing W)
    (additionB12 W) (verticalAddYNumerator W)

/-- Restriction from the vertical infinity chart to
`D(B₁₂ Y_vert)`. -/
noncomputable def verticalChartToProductIntersectionRing
    (W : WeierstrassCurve K) :
    verticalChartCoordinateRing W →+*
      productVerticalIntersectionCoordinateRing W :=
  IsLocalization.Away.awayToAwayLeft
    (S := verticalChartCoordinateRing W)
    (P := productVerticalIntersectionCoordinateRing W)
    (verticalAddYNumerator W) (additionB12 W)

@[simp]
private theorem productNeighborhoodToVerticalIntersectionRing_algebraMap
    (W : WeierstrassCurve K) (a : secantPairCoordinateRing W) :
    productNeighborhoodToVerticalIntersectionRing W
        (algebraMap (secantPairCoordinateRing W)
          (productNeighborhoodCoordinateRing W) a) =
      algebraMap (secantPairCoordinateRing W)
        (productVerticalIntersectionCoordinateRing W) a := by
  exact IsLocalization.Away.awayToAwayRight_eq
    (S := productNeighborhoodCoordinateRing W)
    (P := productVerticalIntersectionCoordinateRing W)
    (additionB12 W) (verticalAddYNumerator W) a

@[simp]
private theorem verticalChartToProductIntersectionRing_algebraMap
    (W : WeierstrassCurve K) (a : secantPairCoordinateRing W) :
    verticalChartToProductIntersectionRing W
        (algebraMap (secantPairCoordinateRing W)
          (verticalChartCoordinateRing W) a) =
      algebraMap (secantPairCoordinateRing W)
        (productVerticalIntersectionCoordinateRing W) a := by
  exact IsLocalization.Away.awayToAwayLeft_eq
    (S := verticalChartCoordinateRing W)
    (P := productVerticalIntersectionCoordinateRing W)
    (verticalAddYNumerator W) (additionB12 W) a

private theorem productVertical_productX_cleared
    (W : WeierstrassCurve K) :
    productNeighborhoodToVerticalIntersectionRing W
          (productNeighborhoodAddX W) *
        algebraMap (secantPairCoordinateRing W)
          (productVerticalIntersectionCoordinateRing W)
            (additionB12 W) ^ 2 =
      algebraMap (secantPairCoordinateRing W)
        (productVerticalIntersectionCoordinateRing W)
          (antidiagonalAddXNumerator W) := by
  have h := congrArg (productNeighborhoodToVerticalIntersectionRing W)
    (productNeighborhoodAddX_mul_B12_sq W)
  simpa only [map_mul, map_pow, productNeighborhoodB12,
    productNeighborhoodToVerticalIntersectionRing_algebraMap] using h

private theorem productVertical_productY_cleared
    (W : WeierstrassCurve K) :
    productNeighborhoodToVerticalIntersectionRing W
          (productNeighborhoodAddY W) *
        algebraMap (secantPairCoordinateRing W)
          (productVerticalIntersectionCoordinateRing W)
            (additionB12 W) ^ 3 =
      algebraMap (secantPairCoordinateRing W)
        (productVerticalIntersectionCoordinateRing W)
          (antidiagonalAddYNumerator W) := by
  have h := congrArg (productNeighborhoodToVerticalIntersectionRing W)
    (productNeighborhoodAddY_mul_B12_cube W)
  simpa only [map_mul, map_pow, productNeighborhoodB12,
    productNeighborhoodToVerticalIntersectionRing_algebraMap] using h

private theorem productVertical_X_transition (W : WeierstrassCurve K) :
    verticalChartToProductIntersectionRing W (verticalChartXOverY W) *
        productNeighborhoodToVerticalIntersectionRing W
          (productNeighborhoodAddY W) =
      productNeighborhoodToVerticalIntersectionRing W
        (productNeighborhoodAddX W) := by
  let f := productNeighborhoodToVerticalIntersectionRing W
  let g := verticalChartToProductIntersectionRing W
  let b := algebraMap (secantPairCoordinateRing W)
    (productVerticalIntersectionCoordinateRing W) (additionB12 W)
  let ib := f (IsLocalization.Away.invSelf
    (S := productNeighborhoodCoordinateRing W) (additionB12 W))
  let xa := algebraMap (secantPairCoordinateRing W)
    (productVerticalIntersectionCoordinateRing W)
      (antidiagonalAddXNumerator W)
  let ya := algebraMap (secantPairCoordinateRing W)
    (productVerticalIntersectionCoordinateRing W)
      (antidiagonalAddYNumerator W)
  let xv := g (verticalChartHomogeneousX W)
  let yv := g (verticalChartHomogeneousY W)
  let iv := g (IsLocalization.Away.invSelf
    (S := verticalChartCoordinateRing W) (verticalAddYNumerator W))
  let xp := f (productNeighborhoodAddX W)
  let yp := f (productNeighborhoodAddY W)
  have hb : b * ib = 1 := by
    dsimp only [b, ib, f]
    simpa only [map_mul, map_one,
      productNeighborhoodToVerticalIntersectionRing_algebraMap] using
      congrArg (productNeighborhoodToVerticalIntersectionRing W)
        (IsLocalization.Away.mul_invSelf
          (S := productNeighborhoodCoordinateRing W) (additionB12 W))
  have hyv : yv * iv = 1 := by
    dsimp only [yv, iv, g]
    simpa only [verticalChartHomogeneousY, map_mul, map_one,
      verticalChartToProductIntersectionRing_algebraMap] using
      congrArg (verticalChartToProductIntersectionRing W)
        (IsLocalization.Away.mul_invSelf
          (S := verticalChartCoordinateRing W) (verticalAddYNumerator W))
  have hxp : xp * b ^ 2 = xa := by
    simpa only [xp, b, xa, f] using productVertical_productX_cleared W
  have hyp : yp * b ^ 3 = ya := by
    simpa only [yp, b, ya, f] using productVertical_productY_cleared W
  have hcross : b * xa * yv = xv * ya := by
    have h := congrArg
      (algebraMap (secantPairCoordinateRing W)
        (productVerticalIntersectionCoordinateRing W))
      (antidiagonalVertical_homogeneousX_mul_Y W)
    simpa only [b, xa, ya, xv, yv, g,
      verticalChartHomogeneousX, verticalChartHomogeneousY, map_mul,
      verticalChartToProductIntersectionRing_algebraMap] using h
  have hxprepr : xp = xa * ib ^ 2 := by
    calc
      xp = xp * (b * ib) ^ 2 := by rw [hb, one_pow, mul_one]
      _ = (xp * b ^ 2) * ib ^ 2 := by ring
      _ = xa * ib ^ 2 := by rw [hxp]
  have hyprepr : yp = ya * ib ^ 3 := by
    calc
      yp = yp * (b * ib) ^ 3 := by rw [hb, one_pow, mul_one]
      _ = (yp * b ^ 3) * ib ^ 3 := by ring
      _ = ya * ib ^ 3 := by rw [hyp]
  simp only [verticalChartXOverY, map_mul]
  change xv * iv * yp = xp
  rw [hxprepr, hyprepr]
  calc
    xv * iv * (ya * ib ^ 3) = (xv * ya) * iv * ib ^ 3 := by ring
    _ = (b * xa * yv) * iv * ib ^ 3 := by rw [← hcross]
    _ = xa * ib ^ 2 * (yv * iv) * (b * ib) := by ring
    _ = xa * ib ^ 2 := by rw [hyv, hb]; ring

private theorem productVertical_Z_transition (W : WeierstrassCurve K) :
    verticalChartToProductIntersectionRing W (verticalChartZOverY W) *
        productNeighborhoodToVerticalIntersectionRing W
          (productNeighborhoodAddY W) = 1 := by
  let f := productNeighborhoodToVerticalIntersectionRing W
  let g := verticalChartToProductIntersectionRing W
  let b := algebraMap (secantPairCoordinateRing W)
    (productVerticalIntersectionCoordinateRing W) (additionB12 W)
  let ib := f (IsLocalization.Away.invSelf
    (S := productNeighborhoodCoordinateRing W) (additionB12 W))
  let ya := algebraMap (secantPairCoordinateRing W)
    (productVerticalIntersectionCoordinateRing W)
      (antidiagonalAddYNumerator W)
  let zv := g (verticalChartHomogeneousZ W)
  let yv := g (verticalChartHomogeneousY W)
  let iv := g (IsLocalization.Away.invSelf
    (S := verticalChartCoordinateRing W) (verticalAddYNumerator W))
  let yp := f (productNeighborhoodAddY W)
  have hb : b * ib = 1 := by
    dsimp only [b, ib, f]
    simpa only [map_mul, map_one,
      productNeighborhoodToVerticalIntersectionRing_algebraMap] using
      congrArg (productNeighborhoodToVerticalIntersectionRing W)
        (IsLocalization.Away.mul_invSelf
          (S := productNeighborhoodCoordinateRing W) (additionB12 W))
  have hyv : yv * iv = 1 := by
    dsimp only [yv, iv, g]
    simpa only [verticalChartHomogeneousY, map_mul, map_one,
      verticalChartToProductIntersectionRing_algebraMap] using
      congrArg (verticalChartToProductIntersectionRing W)
        (IsLocalization.Away.mul_invSelf
          (S := verticalChartCoordinateRing W) (verticalAddYNumerator W))
  have hyp : yp * b ^ 3 = ya := by
    simpa only [yp, b, ya, f] using productVertical_productY_cleared W
  have hcross : b ^ 3 * yv = zv * ya := by
    have h := congrArg
      (algebraMap (secantPairCoordinateRing W)
        (productVerticalIntersectionCoordinateRing W))
      (antidiagonalVertical_homogeneousZ_mul_Y W)
    simpa only [b, ya, zv, yv, g, verticalChartHomogeneousZ,
      verticalChartHomogeneousY, map_mul, map_pow,
      verticalChartToProductIntersectionRing_algebraMap] using h
  have hyprepr : yp = ya * ib ^ 3 := by
    calc
      yp = yp * (b * ib) ^ 3 := by rw [hb, one_pow, mul_one]
      _ = (yp * b ^ 3) * ib ^ 3 := by ring
      _ = ya * ib ^ 3 := by rw [hyp]
  simp only [verticalChartZOverY, map_mul]
  change zv * iv * yp = 1
  rw [hyprepr]
  calc
    zv * iv * (ya * ib ^ 3) = (zv * ya) * iv * ib ^ 3 := by ring
    _ = b ^ 3 * yv * iv * ib ^ 3 := by rw [← hcross]
    _ = (b * ib) ^ 3 * (yv * iv) := by ring
    _ = 1 := by rw [hb, hyv, one_pow, one_mul]

private theorem productVertical_additionB12_isUnit
    (W : WeierstrassCurve K) :
    IsUnit (algebraMap (secantPairCoordinateRing W)
      (productVerticalIntersectionCoordinateRing W) (additionB12 W)) := by
  let f := productNeighborhoodToVerticalIntersectionRing W
  let b := algebraMap (secantPairCoordinateRing W)
    (productVerticalIntersectionCoordinateRing W) (additionB12 W)
  let ib := f (IsLocalization.Away.invSelf
    (S := productNeighborhoodCoordinateRing W) (additionB12 W))
  have hb : b * ib = 1 := by
    dsimp only [b, ib, f]
    simpa only [map_mul, map_one,
      productNeighborhoodToVerticalIntersectionRing_algebraMap] using
      congrArg (productNeighborhoodToVerticalIntersectionRing W)
        (IsLocalization.Away.mul_invSelf
          (S := productNeighborhoodCoordinateRing W) (additionB12 W))
  exact IsUnit.of_mul_eq_one ib hb

private theorem productVertical_verticalY_isUnit
    (W : WeierstrassCurve K) :
    IsUnit (algebraMap (secantPairCoordinateRing W)
      (productVerticalIntersectionCoordinateRing W)
        (verticalAddYNumerator W)) := by
  let g := verticalChartToProductIntersectionRing W
  let yv := algebraMap (secantPairCoordinateRing W)
    (productVerticalIntersectionCoordinateRing W)
      (verticalAddYNumerator W)
  let iv := g (IsLocalization.Away.invSelf
    (S := verticalChartCoordinateRing W) (verticalAddYNumerator W))
  have hyv : yv * iv = 1 := by
    dsimp only [yv, iv, g]
    simpa only [map_mul, map_one,
      verticalChartToProductIntersectionRing_algebraMap] using
      congrArg (verticalChartToProductIntersectionRing W)
        (IsLocalization.Away.mul_invSelf
          (S := verticalChartCoordinateRing W) (verticalAddYNumerator W))
  exact IsUnit.of_mul_eq_one iv hyv

private theorem productVertical_antidiagonalY_isUnit
    (W : WeierstrassCurve K) :
    IsUnit (algebraMap (secantPairCoordinateRing W)
      (productVerticalIntersectionCoordinateRing W)
        (antidiagonalAddYNumerator W)) := by
  let b := algebraMap (secantPairCoordinateRing W)
    (productVerticalIntersectionCoordinateRing W) (additionB12 W)
  let ya := algebraMap (secantPairCoordinateRing W)
    (productVerticalIntersectionCoordinateRing W)
      (antidiagonalAddYNumerator W)
  let yv := algebraMap (secantPairCoordinateRing W)
    (productVerticalIntersectionCoordinateRing W)
      (verticalAddYNumerator W)
  let zv := verticalChartToProductIntersectionRing W
    (verticalChartHomogeneousZ W)
  have hcross : b ^ 3 * yv = zv * ya := by
    have h := congrArg
      (algebraMap (secantPairCoordinateRing W)
        (productVerticalIntersectionCoordinateRing W))
      (antidiagonalVertical_homogeneousZ_mul_Y W)
    simpa only [b, ya, yv, zv, verticalChartHomogeneousZ, map_mul,
      map_pow, verticalChartToProductIntersectionRing_algebraMap] using h
  have hleft : IsUnit (b ^ 3 * yv) :=
    (productVertical_additionB12_isUnit W).pow 3 |>.mul
      (productVertical_verticalY_isUnit W)
  have hright : IsUnit (zv * ya) := hcross ▸ hleft
  exact IsUnit.mul_iff.mp hright |>.2

private noncomputable def productVerticalToProductAntidiagonalRing
    (W : WeierstrassCurve K) :
    productAntidiagonalIntersectionCoordinateRing W →+*
      productVerticalIntersectionCoordinateRing W :=
  IsLocalization.Away.lift
    (R := secantPairCoordinateRing W)
    (S := productAntidiagonalIntersectionCoordinateRing W)
    (P := productVerticalIntersectionCoordinateRing W)
    (g := algebraMap (secantPairCoordinateRing W)
      (productVerticalIntersectionCoordinateRing W))
    (additionB12 W * antidiagonalAddYNumerator W)
    (by
      simpa only [map_mul] using
        IsUnit.mul (productVertical_additionB12_isUnit W)
          (productVertical_antidiagonalY_isUnit W))

private noncomputable def productVerticalToInfinityIntersectionRing
    (W : WeierstrassCurve K) :
    infinityIntersectionCoordinateRing W →+*
      productVerticalIntersectionCoordinateRing W :=
  IsLocalization.Away.lift
    (R := secantPairCoordinateRing W)
    (S := infinityIntersectionCoordinateRing W)
    (P := productVerticalIntersectionCoordinateRing W)
    (g := algebraMap (secantPairCoordinateRing W)
      (productVerticalIntersectionCoordinateRing W))
    (antidiagonalAddYNumerator W * verticalAddYNumerator W)
    (by
      simpa only [map_mul] using
        IsUnit.mul (productVertical_antidiagonalY_isUnit W)
          (productVertical_verticalY_isUnit W))

@[simp]
private theorem productVerticalToProductAntidiagonalRing_algebraMap
    (W : WeierstrassCurve K) (a : secantPairCoordinateRing W) :
    productVerticalToProductAntidiagonalRing W
        (algebraMap (secantPairCoordinateRing W)
          (productAntidiagonalIntersectionCoordinateRing W) a) =
      algebraMap (secantPairCoordinateRing W)
        (productVerticalIntersectionCoordinateRing W) a := by
  exact IsLocalization.Away.lift_eq
    (R := secantPairCoordinateRing W)
    (S := productAntidiagonalIntersectionCoordinateRing W)
    (P := productVerticalIntersectionCoordinateRing W)
    (g := algebraMap (secantPairCoordinateRing W)
      (productVerticalIntersectionCoordinateRing W))
    (additionB12 W * antidiagonalAddYNumerator W) _ a

@[simp]
private theorem productVerticalToInfinityIntersectionRing_algebraMap
    (W : WeierstrassCurve K) (a : secantPairCoordinateRing W) :
    productVerticalToInfinityIntersectionRing W
        (algebraMap (secantPairCoordinateRing W)
          (infinityIntersectionCoordinateRing W) a) =
      algebraMap (secantPairCoordinateRing W)
        (productVerticalIntersectionCoordinateRing W) a := by
  exact IsLocalization.Away.lift_eq
    (R := secantPairCoordinateRing W)
    (S := infinityIntersectionCoordinateRing W)
    (P := productVerticalIntersectionCoordinateRing W)
    (g := algebraMap (secantPairCoordinateRing W)
      (productVerticalIntersectionCoordinateRing W))
    (antidiagonalAddYNumerator W * verticalAddYNumerator W) _ a

/-- Restriction from the exact cross overlap to the product-neighbourhood
chart. -/
def productVerticalIntersectionToProductNeighborhood
    (W : WeierstrassCurve K) :
    Spec (.of (productVerticalIntersectionCoordinateRing W)) ⟶
      Spec (.of (productNeighborhoodCoordinateRing W)) :=
  Spec.map (CommRingCat.ofHom
    (productNeighborhoodToVerticalIntersectionRing W))

/-- Restriction from the exact cross overlap to the vertical infinity
chart. -/
def productVerticalIntersectionToVerticalChart
    (W : WeierstrassCurve K) :
    Spec (.of (productVerticalIntersectionCoordinateRing W)) ⟶
      Spec (.of (verticalChartCoordinateRing W)) :=
  Spec.map (CommRingCat.ofHom (verticalChartToProductIntersectionRing W))

private def productVerticalIntersectionToProductAntidiagonalIntersection
    (W : WeierstrassCurve K) :
    Spec (.of (productVerticalIntersectionCoordinateRing W)) ⟶
      Spec (.of (productAntidiagonalIntersectionCoordinateRing W)) :=
  Spec.map (CommRingCat.ofHom
    (productVerticalToProductAntidiagonalRing W))

private def productVerticalIntersectionToInfinityIntersection
    (W : WeierstrassCurve K) :
    Spec (.of (productVerticalIntersectionCoordinateRing W)) ⟶
      Spec (.of (infinityIntersectionCoordinateRing W)) :=
  Spec.map (CommRingCat.ofHom
    (productVerticalToInfinityIntersectionRing W))

private theorem productVertical_to_productNeighborhood
    (W : WeierstrassCurve K) :
    productVerticalIntersectionToProductAntidiagonalIntersection W ≫
        productAntidiagonalIntersectionToProductNeighborhood W =
      productVerticalIntersectionToProductNeighborhood W := by
  have hring :
      (productVerticalToProductAntidiagonalRing W).comp
          (productNeighborhoodToAntidiagonalIntersectionRing W) =
        productNeighborhoodToVerticalIntersectionRing W := by
    apply IsLocalization.ringHom_ext (.powers (additionB12 W))
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply,
      productNeighborhoodToAntidiagonalIntersectionRing,
      IsLocalization.Away.awayToAwayRight_eq,
      productVerticalToProductAntidiagonalRing_algebraMap,
      productNeighborhoodToVerticalIntersectionRing_algebraMap]
  have hmap := congrArg
    (fun f : productNeighborhoodCoordinateRing W →+*
        productVerticalIntersectionCoordinateRing W =>
      Spec.map (CommRingCat.ofHom f)) hring
  rw [productVerticalIntersectionToProductAntidiagonalIntersection,
    productAntidiagonalIntersectionToProductNeighborhood,
    productVerticalIntersectionToProductNeighborhood, ← Spec.map_comp]
  exact hmap

private theorem productVertical_to_antidiagonal
    (W : WeierstrassCurve K) :
    productVerticalIntersectionToProductAntidiagonalIntersection W ≫
        productAntidiagonalIntersectionToAntidiagonalChart W =
      productVerticalIntersectionToInfinityIntersection W ≫
        infinityIntersectionToAntidiagonalChart W := by
  have hring :
      (productVerticalToProductAntidiagonalRing W).comp
          (antidiagonalChartToIntersectionRing W) =
        (productVerticalToInfinityIntersectionRing W).comp
          (antidiagonalToInfinityIntersectionRing W) := by
    apply IsLocalization.ringHom_ext
      (.powers (antidiagonalAddYNumerator W))
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply, antidiagonalChartToIntersectionRing,
      antidiagonalToInfinityIntersectionRing,
      IsLocalization.Away.awayToAwayLeft_eq,
      IsLocalization.Away.awayToAwayRight_eq,
      productVerticalToProductAntidiagonalRing_algebraMap,
      productVerticalToInfinityIntersectionRing_algebraMap]
  have hmap := congrArg
    (fun f : antidiagonalChartCoordinateRing W →+*
        productVerticalIntersectionCoordinateRing W =>
      Spec.map (CommRingCat.ofHom f)) hring
  rw [productVerticalIntersectionToProductAntidiagonalIntersection,
    productAntidiagonalIntersectionToAntidiagonalChart,
    productVerticalIntersectionToInfinityIntersection,
    infinityIntersectionToAntidiagonalChart, ← Spec.map_comp,
    ← Spec.map_comp]
  exact hmap

private theorem productVertical_to_vertical
    (W : WeierstrassCurve K) :
    productVerticalIntersectionToInfinityIntersection W ≫
        infinityIntersectionToVerticalChart W =
      productVerticalIntersectionToVerticalChart W := by
  have hring :
      (productVerticalToInfinityIntersectionRing W).comp
          (verticalToInfinityIntersectionRing W) =
        verticalChartToProductIntersectionRing W := by
    apply IsLocalization.ringHom_ext (.powers (verticalAddYNumerator W))
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply, verticalToInfinityIntersectionRing,
      IsLocalization.Away.awayToAwayLeft_eq,
      productVerticalToInfinityIntersectionRing_algebraMap,
      verticalChartToProductIntersectionRing_algebraMap]
  have hmap := congrArg
    (fun f : verticalChartCoordinateRing W →+*
        productVerticalIntersectionCoordinateRing W =>
      Spec.map (CommRingCat.ofHom f)) hring
  rw [productVerticalIntersectionToInfinityIntersection,
    infinityIntersectionToVerticalChart,
    productVerticalIntersectionToVerticalChart, ← Spec.map_comp]
  exact hmap

/-- Product-neighbourhood addition and the vertical infinity formula agree
as actual morphisms on `D(B₁₂ Y_vert)`. -/
theorem productVerticalIntersection_additionProjective_eq
    (W : WeierstrassCurve K) :
    productVerticalIntersectionToProductNeighborhood W ≫
        productNeighborhoodAdditionProjectiveMorphism W =
      productVerticalIntersectionToVerticalChart W ≫
        verticalAdditionProjectiveMorphism W := by
  have hproduct := congrArg
    (fun f => productVerticalIntersectionToProductAntidiagonalIntersection W ≫ f)
    (productAntidiagonalIntersection_additionProjective_eq W)
  have hinfinity := congrArg
    (fun f => productVerticalIntersectionToInfinityIntersection W ≫ f)
    (infinityIntersection_additionProjective_eq W)
  calc
    _ = (productVerticalIntersectionToProductAntidiagonalIntersection W ≫
          productAntidiagonalIntersectionToProductNeighborhood W) ≫
          productNeighborhoodAdditionProjectiveMorphism W :=
      congrArg (fun f => f ≫
        productNeighborhoodAdditionProjectiveMorphism W)
        (productVertical_to_productNeighborhood W).symm
    _ = productVerticalIntersectionToProductAntidiagonalIntersection W ≫
          (productAntidiagonalIntersectionToProductNeighborhood W ≫
            productNeighborhoodAdditionProjectiveMorphism W) :=
      Category.assoc _ _ _
    _ = productVerticalIntersectionToProductAntidiagonalIntersection W ≫
          (productAntidiagonalIntersectionToAntidiagonalChart W ≫
            antidiagonalAdditionProjectiveMorphism W) := hproduct
    _ = (productVerticalIntersectionToProductAntidiagonalIntersection W ≫
          productAntidiagonalIntersectionToAntidiagonalChart W) ≫
          antidiagonalAdditionProjectiveMorphism W :=
      (Category.assoc _ _ _).symm
    _ = (productVerticalIntersectionToInfinityIntersection W ≫
          infinityIntersectionToAntidiagonalChart W) ≫
          antidiagonalAdditionProjectiveMorphism W :=
      congrArg (fun f => f ≫ antidiagonalAdditionProjectiveMorphism W)
        (productVertical_to_antidiagonal W)
    _ = productVerticalIntersectionToInfinityIntersection W ≫
          (infinityIntersectionToAntidiagonalChart W ≫
            antidiagonalAdditionProjectiveMorphism W) :=
      Category.assoc _ _ _
    _ = productVerticalIntersectionToInfinityIntersection W ≫
          (infinityIntersectionToVerticalChart W ≫
            verticalAdditionProjectiveMorphism W) := hinfinity
    _ = (productVerticalIntersectionToInfinityIntersection W ≫
          infinityIntersectionToVerticalChart W) ≫
          verticalAdditionProjectiveMorphism W :=
      (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun f => f ≫ verticalAdditionProjectiveMorphism W)
      (productVertical_to_vertical W)

/-! ## The secant/antidiagonal overlap -/

/-- Coordinate ring of `D((x₁-x₂) Y_anti)`. -/
abbrev secantAntidiagonalIntersectionCoordinateRing
    (W : WeierstrassCurve K) :=
  Localization.Away
    (secantDenominator W * antidiagonalAddYNumerator W)

/-- Restriction from the ordinary secant chart to
`D((x₁-x₂) Y_anti)`. -/
noncomputable def secantToAntidiagonalIntersectionRing
    (W : WeierstrassCurve K) :
    secantChartCoordinateRing W →+*
      secantAntidiagonalIntersectionCoordinateRing W :=
  IsLocalization.Away.awayToAwayRight
    (S := secantChartCoordinateRing W)
    (P := secantAntidiagonalIntersectionCoordinateRing W)
    (secantDenominator W) (antidiagonalAddYNumerator W)

/-- Restriction from the antidiagonal infinity chart to
`D((x₁-x₂) Y_anti)`. -/
noncomputable def antidiagonalChartToSecantIntersectionRing
    (W : WeierstrassCurve K) :
    antidiagonalChartCoordinateRing W →+*
      secantAntidiagonalIntersectionCoordinateRing W :=
  IsLocalization.Away.awayToAwayLeft
    (S := antidiagonalChartCoordinateRing W)
    (P := secantAntidiagonalIntersectionCoordinateRing W)
    (antidiagonalAddYNumerator W) (secantDenominator W)

@[simp]
private theorem secantToAntidiagonalIntersectionRing_algebraMap
    (W : WeierstrassCurve K) (a : secantPairCoordinateRing W) :
    secantToAntidiagonalIntersectionRing W
        (algebraMap (secantPairCoordinateRing W)
          (secantChartCoordinateRing W) a) =
      algebraMap (secantPairCoordinateRing W)
        (secantAntidiagonalIntersectionCoordinateRing W) a := by
  exact IsLocalization.Away.awayToAwayRight_eq
    (S := secantChartCoordinateRing W)
    (P := secantAntidiagonalIntersectionCoordinateRing W)
    (secantDenominator W) (antidiagonalAddYNumerator W) a

@[simp]
private theorem antidiagonalChartToSecantIntersectionRing_algebraMap
    (W : WeierstrassCurve K) (a : secantPairCoordinateRing W) :
    antidiagonalChartToSecantIntersectionRing W
        (algebraMap (secantPairCoordinateRing W)
          (antidiagonalChartCoordinateRing W) a) =
      algebraMap (secantPairCoordinateRing W)
        (secantAntidiagonalIntersectionCoordinateRing W) a := by
  exact IsLocalization.Away.awayToAwayLeft_eq
    (S := antidiagonalChartCoordinateRing W)
    (P := secantAntidiagonalIntersectionCoordinateRing W)
    (antidiagonalAddYNumerator W) (secantDenominator W) a

private theorem secantAntidiagonal_denominator_isUnit
    (W : WeierstrassCurve K) :
    IsUnit (algebraMap (secantPairCoordinateRing W)
      (secantAntidiagonalIntersectionCoordinateRing W)
        (secantDenominator W)) := by
  have h : IsUnit (algebraMap (secantPairCoordinateRing W)
      (secantAntidiagonalIntersectionCoordinateRing W)
        (secantDenominator W * antidiagonalAddYNumerator W)) :=
    IsLocalization.Away.algebraMap_isUnit
      (secantDenominator W * antidiagonalAddYNumerator W)
  rw [map_mul] at h
  exact isUnit_of_mul_isUnit_left h

private theorem secantAntidiagonal_antidiagonalY_isUnit
    (W : WeierstrassCurve K) :
    IsUnit (algebraMap (secantPairCoordinateRing W)
      (secantAntidiagonalIntersectionCoordinateRing W)
        (antidiagonalAddYNumerator W)) := by
  have h : IsUnit (algebraMap (secantPairCoordinateRing W)
      (secantAntidiagonalIntersectionCoordinateRing W)
        (secantDenominator W * antidiagonalAddYNumerator W)) :=
    IsLocalization.Away.algebraMap_isUnit
      (secantDenominator W * antidiagonalAddYNumerator W)
  rw [map_mul] at h
  exact isUnit_of_mul_isUnit_right h

private theorem secantAntidiagonal_verticalY_isUnit
    (W : WeierstrassCurve K) :
    IsUnit (algebraMap (secantPairCoordinateRing W)
      (secantAntidiagonalIntersectionCoordinateRing W)
        (verticalAddYNumerator W)) := by
  let b := algebraMap (secantPairCoordinateRing W)
    (secantAntidiagonalIntersectionCoordinateRing W) (additionB12 W)
  let d := algebraMap (secantPairCoordinateRing W)
    (secantAntidiagonalIntersectionCoordinateRing W) (secantDenominator W)
  let ya := algebraMap (secantPairCoordinateRing W)
    (secantAntidiagonalIntersectionCoordinateRing W)
      (antidiagonalAddYNumerator W)
  let yv := algebraMap (secantPairCoordinateRing W)
    (secantAntidiagonalIntersectionCoordinateRing W)
      (verticalAddYNumerator W)
  have hcross : b ^ 3 * yv = d ^ 3 * ya := by
    have h := congrArg
      (algebraMap (secantPairCoordinateRing W)
        (secantAntidiagonalIntersectionCoordinateRing W))
      (antidiagonalVertical_homogeneousZ_mul_Y W)
    simpa only [b, d, ya, yv, verticalAdditionB, secantDenominator,
      map_mul, map_pow] using h
  have hright : IsUnit (d ^ 3 * ya) :=
    (secantAntidiagonal_denominator_isUnit W).pow 3 |>.mul
      (secantAntidiagonal_antidiagonalY_isUnit W)
  have hleft : IsUnit (b ^ 3 * yv) := hcross.symm ▸ hright
  exact IsUnit.mul_iff.mp hleft |>.2

private noncomputable def secantAntidiagonalToSecantVerticalRing
    (W : WeierstrassCurve K) :
    secantVerticalIntersectionCoordinateRing W →+*
      secantAntidiagonalIntersectionCoordinateRing W :=
  IsLocalization.Away.lift
    (R := secantPairCoordinateRing W)
    (S := secantVerticalIntersectionCoordinateRing W)
    (P := secantAntidiagonalIntersectionCoordinateRing W)
    (g := algebraMap (secantPairCoordinateRing W)
      (secantAntidiagonalIntersectionCoordinateRing W))
    (secantDenominator W * verticalAddYNumerator W)
    (by
      simpa only [map_mul] using
        IsUnit.mul (secantAntidiagonal_denominator_isUnit W)
          (secantAntidiagonal_verticalY_isUnit W))

private noncomputable def secantAntidiagonalToInfinityIntersectionRing
    (W : WeierstrassCurve K) :
    infinityIntersectionCoordinateRing W →+*
      secantAntidiagonalIntersectionCoordinateRing W :=
  IsLocalization.Away.lift
    (R := secantPairCoordinateRing W)
    (S := infinityIntersectionCoordinateRing W)
    (P := secantAntidiagonalIntersectionCoordinateRing W)
    (g := algebraMap (secantPairCoordinateRing W)
      (secantAntidiagonalIntersectionCoordinateRing W))
    (antidiagonalAddYNumerator W * verticalAddYNumerator W)
    (by
      simpa only [map_mul] using
        IsUnit.mul (secantAntidiagonal_antidiagonalY_isUnit W)
          (secantAntidiagonal_verticalY_isUnit W))

@[simp]
private theorem secantAntidiagonalToSecantVerticalRing_algebraMap
    (W : WeierstrassCurve K) (a : secantPairCoordinateRing W) :
    secantAntidiagonalToSecantVerticalRing W
        (algebraMap (secantPairCoordinateRing W)
          (secantVerticalIntersectionCoordinateRing W) a) =
      algebraMap (secantPairCoordinateRing W)
        (secantAntidiagonalIntersectionCoordinateRing W) a := by
  exact IsLocalization.Away.lift_eq
    (R := secantPairCoordinateRing W)
    (S := secantVerticalIntersectionCoordinateRing W)
    (P := secantAntidiagonalIntersectionCoordinateRing W)
    (g := algebraMap (secantPairCoordinateRing W)
      (secantAntidiagonalIntersectionCoordinateRing W))
    (secantDenominator W * verticalAddYNumerator W) _ a

@[simp]
private theorem secantAntidiagonalToInfinityIntersectionRing_algebraMap
    (W : WeierstrassCurve K) (a : secantPairCoordinateRing W) :
    secantAntidiagonalToInfinityIntersectionRing W
        (algebraMap (secantPairCoordinateRing W)
          (infinityIntersectionCoordinateRing W) a) =
      algebraMap (secantPairCoordinateRing W)
        (secantAntidiagonalIntersectionCoordinateRing W) a := by
  exact IsLocalization.Away.lift_eq
    (R := secantPairCoordinateRing W)
    (S := infinityIntersectionCoordinateRing W)
    (P := secantAntidiagonalIntersectionCoordinateRing W)
    (g := algebraMap (secantPairCoordinateRing W)
      (secantAntidiagonalIntersectionCoordinateRing W))
    (antidiagonalAddYNumerator W * verticalAddYNumerator W) _ a

/-- Restriction of the cross overlap to the existing secant/vertical
intersection. -/
private def secantAntidiagonalIntersectionToSecantVerticalIntersection
    (W : WeierstrassCurve K) :
    Spec (.of (secantAntidiagonalIntersectionCoordinateRing W)) ⟶
      Spec (.of (secantVerticalIntersectionCoordinateRing W)) :=
  Spec.map (CommRingCat.ofHom
    (secantAntidiagonalToSecantVerticalRing W))

/-- Restriction of the cross overlap to the existing common infinity
intersection. -/
private def secantAntidiagonalIntersectionToInfinityIntersection
    (W : WeierstrassCurve K) :
    Spec (.of (secantAntidiagonalIntersectionCoordinateRing W)) ⟶
      Spec (.of (infinityIntersectionCoordinateRing W)) :=
  Spec.map (CommRingCat.ofHom
    (secantAntidiagonalToInfinityIntersectionRing W))

/-- Restriction from the exact cross overlap to the ordinary secant chart. -/
def secantAntidiagonalIntersectionToSecantChart
    (W : WeierstrassCurve K) :
    Spec (.of (secantAntidiagonalIntersectionCoordinateRing W)) ⟶
      Spec (.of (secantChartCoordinateRing W)) :=
  Spec.map (CommRingCat.ofHom
    (secantToAntidiagonalIntersectionRing W))

/-- Restriction from the exact cross overlap to the antidiagonal infinity
chart. -/
def secantAntidiagonalIntersectionToAntidiagonalChart
    (W : WeierstrassCurve K) :
    Spec (.of (secantAntidiagonalIntersectionCoordinateRing W)) ⟶
      Spec (.of (antidiagonalChartCoordinateRing W)) :=
  Spec.map (CommRingCat.ofHom
    (antidiagonalChartToSecantIntersectionRing W))

private theorem secantAntidiagonal_to_secant
    (W : WeierstrassCurve K) :
    secantAntidiagonalIntersectionToSecantVerticalIntersection W ≫
        secantVerticalIntersectionToSecantChart W =
      secantAntidiagonalIntersectionToSecantChart W := by
  have hring :
      (secantAntidiagonalToSecantVerticalRing W).comp
          (secantToVerticalIntersectionRing W) =
        secantToAntidiagonalIntersectionRing W := by
    apply IsLocalization.ringHom_ext (.powers (secantDenominator W))
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply, secantToVerticalIntersectionRing,
      IsLocalization.Away.awayToAwayRight_eq,
      secantAntidiagonalToSecantVerticalRing_algebraMap,
      secantToAntidiagonalIntersectionRing_algebraMap]
  have hmap := congrArg
    (fun f : secantChartCoordinateRing W →+*
        secantAntidiagonalIntersectionCoordinateRing W =>
      Spec.map (CommRingCat.ofHom f)) hring
  rw [secantAntidiagonalIntersectionToSecantVerticalIntersection,
    secantVerticalIntersectionToSecantChart,
    secantAntidiagonalIntersectionToSecantChart, ← Spec.map_comp]
  exact hmap

private theorem secantAntidiagonal_to_vertical
    (W : WeierstrassCurve K) :
    secantAntidiagonalIntersectionToSecantVerticalIntersection W ≫
        secantVerticalIntersectionToVerticalChart W =
      secantAntidiagonalIntersectionToInfinityIntersection W ≫
        infinityIntersectionToVerticalChart W := by
  have hring :
      (secantAntidiagonalToSecantVerticalRing W).comp
          (verticalChartToIntersectionRing W) =
        (secantAntidiagonalToInfinityIntersectionRing W).comp
          (verticalToInfinityIntersectionRing W) := by
    apply IsLocalization.ringHom_ext (.powers (verticalAddYNumerator W))
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply, verticalChartToIntersectionRing,
      verticalToInfinityIntersectionRing,
      IsLocalization.Away.awayToAwayLeft_eq,
      secantAntidiagonalToSecantVerticalRing_algebraMap,
      secantAntidiagonalToInfinityIntersectionRing_algebraMap]
  have hmap := congrArg
    (fun f : verticalChartCoordinateRing W →+*
        secantAntidiagonalIntersectionCoordinateRing W =>
      Spec.map (CommRingCat.ofHom f)) hring
  rw [secantAntidiagonalIntersectionToSecantVerticalIntersection,
    secantVerticalIntersectionToVerticalChart,
    secantAntidiagonalIntersectionToInfinityIntersection,
    infinityIntersectionToVerticalChart, ← Spec.map_comp,
    ← Spec.map_comp]
  exact hmap

private theorem secantAntidiagonal_to_antidiagonal
    (W : WeierstrassCurve K) :
    secantAntidiagonalIntersectionToInfinityIntersection W ≫
        infinityIntersectionToAntidiagonalChart W =
      secantAntidiagonalIntersectionToAntidiagonalChart W := by
  have hring :
      (secantAntidiagonalToInfinityIntersectionRing W).comp
          (antidiagonalToInfinityIntersectionRing W) =
        antidiagonalChartToSecantIntersectionRing W := by
    apply IsLocalization.ringHom_ext
      (.powers (antidiagonalAddYNumerator W))
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply, antidiagonalToInfinityIntersectionRing,
      IsLocalization.Away.awayToAwayRight_eq,
      secantAntidiagonalToInfinityIntersectionRing_algebraMap,
      antidiagonalChartToSecantIntersectionRing_algebraMap]
  have hmap := congrArg
    (fun f : antidiagonalChartCoordinateRing W →+*
        secantAntidiagonalIntersectionCoordinateRing W =>
      Spec.map (CommRingCat.ofHom f)) hring
  rw [secantAntidiagonalIntersectionToInfinityIntersection,
    infinityIntersectionToAntidiagonalChart,
    secantAntidiagonalIntersectionToAntidiagonalChart, ← Spec.map_comp]
  exact hmap

/-- Ordinary secant addition and the antidiagonal infinity formula agree as
actual morphisms on `D((x₁-x₂) Y_anti)`. -/
theorem secantAntidiagonalIntersection_additionProjective_eq
    (W : WeierstrassCurve K) :
    secantAntidiagonalIntersectionToSecantChart W ≫
        secantAdditionProjectiveMorphism W =
      secantAntidiagonalIntersectionToAntidiagonalChart W ≫
        antidiagonalAdditionProjectiveMorphism W := by
  have hsecant := congrArg
    (fun f => secantAntidiagonalIntersectionToSecantVerticalIntersection W ≫ f)
    (secantVerticalIntersection_additionProjective_eq W)
  have hinfinity := congrArg
    (fun f => secantAntidiagonalIntersectionToInfinityIntersection W ≫ f)
    (infinityIntersection_additionProjective_eq W)
  calc
    _ = (secantAntidiagonalIntersectionToSecantVerticalIntersection W ≫
          secantVerticalIntersectionToSecantChart W) ≫
          secantAdditionProjectiveMorphism W :=
      congrArg (fun f => f ≫ secantAdditionProjectiveMorphism W)
        (secantAntidiagonal_to_secant W).symm
    _ = secantAntidiagonalIntersectionToSecantVerticalIntersection W ≫
          (secantVerticalIntersectionToSecantChart W ≫
            secantAdditionProjectiveMorphism W) := Category.assoc _ _ _
    _ = secantAntidiagonalIntersectionToSecantVerticalIntersection W ≫
          (secantVerticalIntersectionToVerticalChart W ≫
            verticalAdditionProjectiveMorphism W) := hsecant
    _ = (secantAntidiagonalIntersectionToSecantVerticalIntersection W ≫
          secantVerticalIntersectionToVerticalChart W) ≫
          verticalAdditionProjectiveMorphism W := (Category.assoc _ _ _).symm
    _ = (secantAntidiagonalIntersectionToInfinityIntersection W ≫
          infinityIntersectionToVerticalChart W) ≫
          verticalAdditionProjectiveMorphism W :=
      congrArg (fun f => f ≫ verticalAdditionProjectiveMorphism W)
        (secantAntidiagonal_to_vertical W)
    _ = secantAntidiagonalIntersectionToInfinityIntersection W ≫
          (infinityIntersectionToVerticalChart W ≫
            verticalAdditionProjectiveMorphism W) := Category.assoc _ _ _
    _ = secantAntidiagonalIntersectionToInfinityIntersection W ≫
          (infinityIntersectionToAntidiagonalChart W ≫
            antidiagonalAdditionProjectiveMorphism W) := hinfinity.symm
    _ = (secantAntidiagonalIntersectionToInfinityIntersection W ≫
          infinityIntersectionToAntidiagonalChart W) ≫
          antidiagonalAdditionProjectiveMorphism W :=
      (Category.assoc _ _ _).symm
    _ = _ := congrArg
      (fun f => f ≫ antidiagonalAdditionProjectiveMorphism W)
      (secantAntidiagonal_to_antidiagonal W)

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
