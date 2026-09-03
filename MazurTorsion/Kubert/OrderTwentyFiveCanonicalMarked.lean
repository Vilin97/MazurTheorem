/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveCanonicalOpen
import MazurTorsion.Kubert.OrderTwentyFiveNormalizedModel

/-!
# Marked order-twenty-five points on the canonical carrier

Three consecutive nonzero members `(a,b,c)` of a Lécacheux orbit reconstruct
canonical coordinates by

`[x:y:z:w] = [1+c+bc+abc : 1+bc+abc : -abc : bc]`.

The first three cyclic functions of this point are definitionally `a`, `b`,
and `c`.  The six orbit relations, away from the already excluded component
`a = 1`, force both canonical equations and identify the remaining two
cyclic functions with `d` and `e`.  Conversely, applying this reconstruction
to the five functions of a point in the common canonical chart recovers the
original coordinates up to the explicit projective scale
`1 / (y+z-w)`.

The actual Brunault orbit attached to a marked Tate point of exact order 25
therefore gives a noncuspidal rational point on the fixed canonical carrier,
with all five functions identified term by term.  The named endpoint
`rationalPoint_addOrderOf_ne_twentyFive_of_noCanonicalNoncuspidal` isolates
the remaining Diophantine boundary: a classification excluding noncuspidal
rational points on this one explicit canonical curve suffices for the actual
order-25 theorem.
-/

namespace MazurTorsion.Kubert

open scoped WeierstrassCurve.Affine

/-- The six polynomial relations defining a rational Lécacheux orbit. -/
structure OrderTwentyFiveOrbitRelations (a b c d e : ℚ) : Prop where
  relationZero : orderTwentyFiveOrbitRelationZero a b c d e = 0
  relationOne : orderTwentyFiveOrbitRelationOne a b c d e = 0
  relationTwo : orderTwentyFiveOrbitRelationTwo a b c d e = 0
  relationThree : orderTwentyFiveOrbitRelationThree a b c d e = 0
  relationFour : orderTwentyFiveOrbitRelationFour a b c d e = 0
  relationFive : orderTwentyFiveOrbitRelationFive a b c d e = 0

/-- Three consecutive cyclic units reconstruct homogeneous coordinates on
the canonical complete intersection. -/
def orderTwentyFiveCanonicalCoordinatesOfOrbit
    {R : Type*} [CommRing R] (a b c : R) :
    OrderTwentyFiveCanonicalCoordinates R where
  x := 1 + c + b * c + a * b * c
  y := 1 + b * c + a * b * c
  z := -(a * b * c)
  w := b * c

@[simp]
theorem orderTwentyFiveCanonicalCoordinatesOfOrbit_sub
    {R : Type*} [CommRing R] (a b c : R) :
    (orderTwentyFiveCanonicalCoordinatesOfOrbit a b c).x -
        (orderTwentyFiveCanonicalCoordinatesOfOrbit a b c).y = c := by
  simp only [orderTwentyFiveCanonicalCoordinatesOfOrbit]
  ring

@[simp]
theorem orderTwentyFiveCanonicalCoordinatesOfOrbit_linear
    {R : Type*} [CommRing R] (a b c : R) :
    (orderTwentyFiveCanonicalCoordinatesOfOrbit a b c).y +
        (orderTwentyFiveCanonicalCoordinatesOfOrbit a b c).z -
        (orderTwentyFiveCanonicalCoordinatesOfOrbit a b c).w = 1 := by
  simp only [orderTwentyFiveCanonicalCoordinatesOfOrbit]
  ring

/-- The reconstructed homogeneous coordinate vector is never zero. -/
theorem orderTwentyFiveCanonicalCoordinatesOfOrbit_nonzero
    (a b c : ℚ) :
    OrderTwentyFiveCanonicalCoordinatesNonzero
      (orderTwentyFiveCanonicalCoordinatesOfOrbit a b c).x
      (orderTwentyFiveCanonicalCoordinatesOfOrbit a b c).y
      (orderTwentyFiveCanonicalCoordinatesOfOrbit a b c).z
      (orderTwentyFiveCanonicalCoordinatesOfOrbit a b c).w := by
  by_contra hzero
  simp only [OrderTwentyFiveCanonicalCoordinatesNonzero, not_or, not_not] at hzero
  rcases hzero with ⟨hx, hy, hz, hw⟩
  have hlinear := orderTwentyFiveCanonicalCoordinatesOfOrbit_linear a b c
  rw [hy, hz, hw] at hlinear
  norm_num at hlinear

/-- Norm one forces every member of a rational Lécacheux orbit to be
nonzero. -/
theorem OrderTwentyFiveOrbitRelations.all_ne_zero
    {a b c d e : ℚ} (h : OrderTwentyFiveOrbitRelations a b c d e) :
    a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ d ≠ 0 ∧ e ≠ 0 := by
  have hproduct : a * b * c * d * e = 1 := by
    simpa only [orderTwentyFiveOrbitRelationFive, sub_eq_zero] using
      h.relationFive
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ha
    rw [ha] at hproduct
    norm_num at hproduct
  · intro hb
    rw [hb] at hproduct
    norm_num at hproduct
  · intro hc
    rw [hc] at hproduct
    norm_num at hproduct
  · intro hd
    rw [hd] at hproduct
    norm_num at hproduct
  · intro he
    rw [he] at hproduct
    norm_num at hproduct

/-- Away from the extraneous orbit component `a = 1`, the orbit equations
force the reconstructed point onto the canonical complete intersection and
identify the two remaining cyclic ratios by cleared polynomial identities. -/
theorem orderTwentyFiveCanonicalCoordinatesOfOrbit_certificates
    (a b c d e : ℚ) (ha : a ≠ 1)
    (h : OrderTwentyFiveOrbitRelations a b c d e) :
    let p := orderTwentyFiveCanonicalCoordinatesOfOrbit a b c
    orderTwentyFiveCanonicalQuadric p.x p.y p.z p.w = 0 ∧
      orderTwentyFiveCanonicalCubic p.x p.y p.z p.w = 0 ∧
      p.w - p.y - p.z = d * p.x ∧
      p.x = e * p.z := by
  dsimp only
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  have hfactor : a - 1 ≠ 0 := sub_ne_zero.mpr ha
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hmul :
        (a - 1) * orderTwentyFiveCanonicalQuadric
          (orderTwentyFiveCanonicalCoordinatesOfOrbit a b c).x
          (orderTwentyFiveCanonicalCoordinatesOfOrbit a b c).y
          (orderTwentyFiveCanonicalCoordinatesOfOrbit a b c).z
          (orderTwentyFiveCanonicalCoordinatesOfOrbit a b c).w = 0 := by
      clear ha hfactor
      simp only [orderTwentyFiveCanonicalCoordinatesOfOrbit,
        orderTwentyFiveCanonicalQuadric,
        orderTwentyFiveOrbitRelationZero,
        orderTwentyFiveOrbitRelationOne,
        orderTwentyFiveOrbitRelationTwo,
        orderTwentyFiveOrbitRelationThree,
        orderTwentyFiveOrbitRelationFour,
        orderTwentyFiveOrbitRelationFive] at h0 h1 h2 h3 h4 h5 ⊢
      grobner
    exact (mul_eq_zero.mp hmul).resolve_left hfactor
  · have hmul :
        (a - 1) * orderTwentyFiveCanonicalCubic
          (orderTwentyFiveCanonicalCoordinatesOfOrbit a b c).x
          (orderTwentyFiveCanonicalCoordinatesOfOrbit a b c).y
          (orderTwentyFiveCanonicalCoordinatesOfOrbit a b c).z
          (orderTwentyFiveCanonicalCoordinatesOfOrbit a b c).w = 0 := by
      clear ha hfactor
      simp only [orderTwentyFiveCanonicalCoordinatesOfOrbit,
        orderTwentyFiveCanonicalCubic,
        orderTwentyFiveOrbitRelationZero,
        orderTwentyFiveOrbitRelationOne,
        orderTwentyFiveOrbitRelationTwo,
        orderTwentyFiveOrbitRelationThree,
        orderTwentyFiveOrbitRelationFour,
        orderTwentyFiveOrbitRelationFive] at h0 h1 h2 h3 h4 h5 ⊢
      grobner
    exact (mul_eq_zero.mp hmul).resolve_left hfactor
  · apply sub_eq_zero.mp
    have hmul :
        (a - 1) *
          ((orderTwentyFiveCanonicalCoordinatesOfOrbit a b c).w -
              (orderTwentyFiveCanonicalCoordinatesOfOrbit a b c).y -
              (orderTwentyFiveCanonicalCoordinatesOfOrbit a b c).z -
            d * (orderTwentyFiveCanonicalCoordinatesOfOrbit a b c).x) = 0 := by
      clear ha hfactor
      simp only [orderTwentyFiveCanonicalCoordinatesOfOrbit,
        orderTwentyFiveOrbitRelationZero,
        orderTwentyFiveOrbitRelationOne,
        orderTwentyFiveOrbitRelationTwo,
        orderTwentyFiveOrbitRelationThree,
        orderTwentyFiveOrbitRelationFour,
        orderTwentyFiveOrbitRelationFive] at h0 h1 h2 h3 h4 h5 ⊢
      grobner
    exact (mul_eq_zero.mp hmul).resolve_left hfactor
  · apply sub_eq_zero.mp
    have hmul :
        (a - 1) *
          ((orderTwentyFiveCanonicalCoordinatesOfOrbit a b c).x -
            e * (orderTwentyFiveCanonicalCoordinatesOfOrbit a b c).z) = 0 := by
      clear ha hfactor
      simp only [orderTwentyFiveCanonicalCoordinatesOfOrbit,
        orderTwentyFiveOrbitRelationZero,
        orderTwentyFiveOrbitRelationOne,
        orderTwentyFiveOrbitRelationTwo,
        orderTwentyFiveOrbitRelationThree,
        orderTwentyFiveOrbitRelationFour,
        orderTwentyFiveOrbitRelationFive] at h0 h1 h2 h3 h4 h5 ⊢
      grobner
    exact (mul_eq_zero.mp hmul).resolve_left hfactor

/-- The reconstructed point lies on the canonical curve. -/
theorem orderTwentyFiveCanonicalCoordinatesOfOrbit_onCurve
    (a b c d e : ℚ) (ha : a ≠ 1)
    (h : OrderTwentyFiveOrbitRelations a b c d e) :
    (orderTwentyFiveCanonicalCoordinatesOfOrbit a b c).OnCurve := by
  obtain ⟨hQ, hC, -, -⟩ :=
    orderTwentyFiveCanonicalCoordinatesOfOrbit_certificates a b c d e ha h
  exact ⟨hQ, hC⟩

/-- The five cyclic denominator forms are nonzero on a reconstructed
nonexceptional orbit point. -/
theorem orderTwentyFiveCanonicalCoordinatesOfOrbit_denominators
    (a b c d e : ℚ) (ha : a ≠ 1)
    (h : OrderTwentyFiveOrbitRelations a b c d e) :
    let p := orderTwentyFiveCanonicalCoordinatesOfOrbit a b c
    p.w ≠ 0 ∧ p.x - p.y ≠ 0 ∧ p.y + p.z - p.w ≠ 0 ∧
      p.x ≠ 0 ∧ p.z ≠ 0 := by
  dsimp only
  obtain ⟨ha0, hb0, hc0, _hd0, he0⟩ := h.all_ne_zero
  obtain ⟨-, -, -, hxe⟩ :=
    orderTwentyFiveCanonicalCoordinatesOfOrbit_certificates a b c d e ha h
  have hw : (orderTwentyFiveCanonicalCoordinatesOfOrbit a b c).w ≠ 0 := by
    simp only [orderTwentyFiveCanonicalCoordinatesOfOrbit]
    exact mul_ne_zero hb0 hc0
  have hxy :
      (orderTwentyFiveCanonicalCoordinatesOfOrbit a b c).x -
          (orderTwentyFiveCanonicalCoordinatesOfOrbit a b c).y ≠ 0 := by
    simpa only [orderTwentyFiveCanonicalCoordinatesOfOrbit_sub] using hc0
  have hlinear :
      (orderTwentyFiveCanonicalCoordinatesOfOrbit a b c).y +
          (orderTwentyFiveCanonicalCoordinatesOfOrbit a b c).z -
          (orderTwentyFiveCanonicalCoordinatesOfOrbit a b c).w ≠ 0 := by
    rw [orderTwentyFiveCanonicalCoordinatesOfOrbit_linear]
    norm_num
  have hz : (orderTwentyFiveCanonicalCoordinatesOfOrbit a b c).z ≠ 0 := by
    simp only [orderTwentyFiveCanonicalCoordinatesOfOrbit]
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero ha0 hb0) hc0)
  have hx : (orderTwentyFiveCanonicalCoordinatesOfOrbit a b c).x ≠ 0 := by
    rw [hxe]
    exact mul_ne_zero he0 hz
  exact ⟨hw, hxy, hlinear, hx, hz⟩

/-- All five canonical rational functions recover the supplied orbit term by
term. -/
theorem orderTwentyFiveCanonicalCoordinatesOfOrbit_roots
    (a b c d e : ℚ) (ha : a ≠ 1)
    (h : OrderTwentyFiveOrbitRelations a b c d e) :
    let p := orderTwentyFiveCanonicalCoordinatesOfOrbit a b c
    orderTwentyFiveCanonicalRootZero p = a ∧
      orderTwentyFiveCanonicalRootOne p = b ∧
      orderTwentyFiveCanonicalRootTwo p = c ∧
      orderTwentyFiveCanonicalRootThree p = d ∧
      orderTwentyFiveCanonicalRootFour p = e := by
  dsimp only
  obtain ⟨hw, hxy, hlinear, hx, hz⟩ :=
    orderTwentyFiveCanonicalCoordinatesOfOrbit_denominators a b c d e ha h
  obtain ⟨-, -, hthree, hfour⟩ :=
    orderTwentyFiveCanonicalCoordinatesOfOrbit_certificates a b c d e ha h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [orderTwentyFiveCanonicalRootZero, div_eq_iff hw]
    simp only [orderTwentyFiveCanonicalCoordinatesOfOrbit]
    ring
  · rw [orderTwentyFiveCanonicalRootOne, div_eq_iff hxy]
    simp only [orderTwentyFiveCanonicalCoordinatesOfOrbit]
    ring
  · rw [orderTwentyFiveCanonicalRootTwo, div_eq_iff hlinear]
    simp only [orderTwentyFiveCanonicalCoordinatesOfOrbit]
    ring
  · rw [orderTwentyFiveCanonicalRootThree, div_eq_iff hx]
    exact hthree
  · rw [orderTwentyFiveCanonicalRootFour, div_eq_iff hz]
    exact hfour

/-- Nonvanishing of `w` and `x-y` excludes every displayed canonical cusp
ray. -/
theorem OrderTwentyFiveCanonicalCoordinates.not_isCusp_of_w_sub_ne_zero
    {p : OrderTwentyFiveCanonicalCoordinates ℚ}
    (hw : p.w ≠ 0) (hxy : p.x - p.y ≠ 0) :
    ¬p.IsCusp := by
  rintro ⟨i, s, hs, hx, hy, hz, hw'⟩
  fin_cases i
  · norm_num [orderTwentyFiveCanonicalCuspX,
      orderTwentyFiveCanonicalCuspY, orderTwentyFiveCanonicalCuspZ,
      orderTwentyFiveCanonicalCuspW, Matrix.cons_val_zero] at hx hy hz hw'
    apply hxy
    linear_combination hx - hy
  · norm_num [orderTwentyFiveCanonicalCuspX,
      orderTwentyFiveCanonicalCuspY, orderTwentyFiveCanonicalCuspZ,
      orderTwentyFiveCanonicalCuspW, Matrix.cons_val_zero] at hx hy hz hw'
    exact hw hw'
  · norm_num [orderTwentyFiveCanonicalCuspX,
      orderTwentyFiveCanonicalCuspY, orderTwentyFiveCanonicalCuspZ,
      orderTwentyFiveCanonicalCuspW, Matrix.cons_val_zero] at hx hy hz hw'
    apply hxy
    linear_combination hx - hy
  · norm_num [orderTwentyFiveCanonicalCuspX,
      orderTwentyFiveCanonicalCuspY, orderTwentyFiveCanonicalCuspZ,
      orderTwentyFiveCanonicalCuspW, Matrix.cons_val_zero] at hx hy hz hw'
    exact hw hw'
  · norm_num [orderTwentyFiveCanonicalCuspX,
      orderTwentyFiveCanonicalCuspY, orderTwentyFiveCanonicalCuspZ,
      orderTwentyFiveCanonicalCuspW, Matrix.cons_val_zero] at hx hy hz hw'
    exact hw hw'

/-- A rational nonexceptional Lécacheux orbit reconstructs a noncuspidal
rational point on the canonical carrier. -/
theorem orderTwentyFiveCanonicalCoordinatesOfOrbit_isNoncuspidal
    (a b c d e : ℚ) (ha : a ≠ 1)
    (h : OrderTwentyFiveOrbitRelations a b c d e) :
    (orderTwentyFiveCanonicalCoordinatesOfOrbit a b c).IsNoncuspidal := by
  obtain ⟨hw, hxy, -, -, -⟩ :=
    orderTwentyFiveCanonicalCoordinatesOfOrbit_denominators a b c d e ha h
  exact ⟨orderTwentyFiveCanonicalCoordinatesOfOrbit_nonzero a b c,
    orderTwentyFiveCanonicalCoordinatesOfOrbit_onCurve a b c d e ha h,
    OrderTwentyFiveCanonicalCoordinates.not_isCusp_of_w_sub_ne_zero hw hxy⟩

/-- Scalar multiplication of a canonical coordinate representative. -/
def orderTwentyFiveCanonicalCoordinatesScale
    {R : Type*} [CommRing R] (s : R)
    (p : OrderTwentyFiveCanonicalCoordinates R) :
    OrderTwentyFiveCanonicalCoordinates R where
  x := s * p.x
  y := s * p.y
  z := s * p.z
  w := s * p.w

/-- Conversely, the first three functions reconstruct every point in their
common chart up to the explicit projective scale `1/(y+z-w)`. -/
theorem orderTwentyFiveCanonicalCoordinatesOfOrbit_reconstruct
    (p : OrderTwentyFiveCanonicalCoordinates ℚ)
    (hw : p.w ≠ 0) (hxy : p.x - p.y ≠ 0)
    (hlinear : p.y + p.z - p.w ≠ 0) :
    orderTwentyFiveCanonicalCoordinatesOfOrbit
        (orderTwentyFiveCanonicalRootZero p)
        (orderTwentyFiveCanonicalRootOne p)
        (orderTwentyFiveCanonicalRootTwo p) =
      orderTwentyFiveCanonicalCoordinatesScale
        (1 / (p.y + p.z - p.w)) p := by
  ext <;>
    simp only [orderTwentyFiveCanonicalCoordinatesOfOrbit,
      orderTwentyFiveCanonicalCoordinatesScale,
      orderTwentyFiveCanonicalRootZero, orderTwentyFiveCanonicalRootOne,
      orderTwentyFiveCanonicalRootTwo] <;>
    field_simp [hw, hxy, hlinear] <;>
    ring

/-- The actual Brunault orbit of a marked Tate point, packaged in the
six-relation interface used by canonical reconstruction. -/
theorem orderTwentyFiveOrbitRelations_of_marked_order
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25) :
    OrderTwentyFiveOrbitRelations
      (orderTwentyFiveBrunaultXZero b c)
      (orderTwentyFiveBrunaultXOne b c)
      (orderTwentyFiveBrunaultXTwo b c)
      (orderTwentyFiveBrunaultXThree b c)
      (orderTwentyFiveBrunaultXFour b c) where
  relationZero :=
    orderTwentyFiveOrbitRelationZero_eq_zero_of_marked_order b c hb h00 horder
  relationOne :=
    orderTwentyFiveOrbitRelationOne_eq_zero_of_marked_order b c hb h00 horder
  relationTwo :=
    orderTwentyFiveOrbitRelationTwo_eq_zero_of_marked_order b c hb h00 horder
  relationThree :=
    orderTwentyFiveOrbitRelationThree_eq_zero_of_marked_order b c hb h00 horder
  relationFour :=
    orderTwentyFiveOrbitRelationFour_eq_zero_of_marked_order b c hb h00 horder
  relationFive :=
    orderTwentyFiveOrbitRelationFive_eq_zero_of_marked_order b c hb h00 horder

/-- The canonical point reconstructed from the first three actual Brunault
units of a marked Tate curve. -/
def orderTwentyFiveCanonicalCoordinatesOfMarkedOrder (b c : ℚ) :
    OrderTwentyFiveCanonicalCoordinates ℚ :=
  orderTwentyFiveCanonicalCoordinatesOfOrbit
    (orderTwentyFiveBrunaultXZero b c)
    (orderTwentyFiveBrunaultXOne b c)
    (orderTwentyFiveBrunaultXTwo b c)

/-- A marked Tate point of exact order 25 produces a noncuspidal rational
canonical point, and its five canonical functions are exactly the five
actual Brunault orbit units. -/
theorem orderTwentyFiveCanonicalPoint_of_marked_order
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25) :
    let p := orderTwentyFiveCanonicalCoordinatesOfMarkedOrder b c
    p.IsNoncuspidal ∧
      orderTwentyFiveCanonicalRootZero p =
        orderTwentyFiveBrunaultXZero b c ∧
      orderTwentyFiveCanonicalRootOne p =
        orderTwentyFiveBrunaultXOne b c ∧
      orderTwentyFiveCanonicalRootTwo p =
        orderTwentyFiveBrunaultXTwo b c ∧
      orderTwentyFiveCanonicalRootThree p =
        orderTwentyFiveBrunaultXThree b c ∧
      orderTwentyFiveCanonicalRootFour p =
        orderTwentyFiveBrunaultXFour b c ∧
      orderTwentyFiveCanonicalOrbitParameter p =
        orderTwentyFiveOrbitParameter
          (orderTwentyFiveBrunaultXZero b c)
          (orderTwentyFiveBrunaultXOne b c)
          (orderTwentyFiveBrunaultXTwo b c)
          (orderTwentyFiveBrunaultXThree b c)
          (orderTwentyFiveBrunaultXFour b c) := by
  dsimp only [orderTwentyFiveCanonicalCoordinatesOfMarkedOrder]
  let a := orderTwentyFiveBrunaultXZero b c
  let b1 := orderTwentyFiveBrunaultXOne b c
  let c1 := orderTwentyFiveBrunaultXTwo b c
  let d := orderTwentyFiveBrunaultXThree b c
  let e := orderTwentyFiveBrunaultXFour b c
  have ha : a ≠ 1 := by
    dsimp only [a]
    rw [orderTwentyFiveBrunaultXZero_eq_U]
    exact orderTwentyFiveBrunaultU_ne_one_of_marked_order b c hb h00 horder
  have hrelations : OrderTwentyFiveOrbitRelations a b1 c1 d e := by
    simpa only [a, b1, c1, d, e] using
      orderTwentyFiveOrbitRelations_of_marked_order b c hb h00 horder
  have hnoncusp :=
    orderTwentyFiveCanonicalCoordinatesOfOrbit_isNoncuspidal
      a b1 c1 d e ha hrelations
  obtain ⟨hr0, hr1, hr2, hr3, hr4⟩ :=
    orderTwentyFiveCanonicalCoordinatesOfOrbit_roots
      a b1 c1 d e ha hrelations
  refine ⟨hnoncusp, hr0, hr1, hr2, hr3, hr4, ?_⟩
  simp only [orderTwentyFiveCanonicalOrbitParameter]
  rw [hr0, hr1, hr2, hr3, hr4]

/-- A rational-point classification of the explicit canonical carrier rules
out a marked Tate point of exact order 25. -/
theorem no_orderTwentyFive_marked_order_of_noCanonicalNoncuspidal
    (hcanonical :
      ∀ p : OrderTwentyFiveCanonicalCoordinates ℚ, ¬p.IsNoncuspidal)
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25) :
    False :=
  hcanonical (orderTwentyFiveCanonicalCoordinatesOfMarkedOrder b c)
    (orderTwentyFiveCanonicalPoint_of_marked_order b c hb h00 horder).1

/-- Exact remaining endpoint boundary: excluding noncuspidal rational points
on the fixed canonical carrier implies that every rational elliptic-curve
point has additive order different from 25. -/
theorem rationalPoint_addOrderOf_ne_twentyFive_of_noCanonicalNoncuspidal
    (hcanonical :
      ∀ p : OrderTwentyFiveCanonicalCoordinates ℚ, ¬p.IsNoncuspidal)
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) :
    addOrderOf P ≠ 25 := by
  intro hP
  haveI : (E⁄ℚ).IsElliptic :=
    inferInstanceAs (E.map (algebraMap ℚ ℚ)).IsElliptic
  have hP2 : P + P ≠ 0 := by
    intro h
    have hdvd : addOrderOf P ∣ 2 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by
        rw [two_nsmul]
        exact h)
    rw [hP] at hdvd
    norm_num at hdvd
  have hP3 : P + P + P ≠ 0 := by
    intro h
    have hdvd : addOrderOf P ∣ 3 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by
        rw [show (3 : ℕ) • P = P + P + P by abel]
        exact h)
    rw [hP] at hdvd
    norm_num at hdvd
  obtain ⟨b, c, _u, _hu, hb, h00, e, heP, _hdisc, -, -⟩ :=
    exists_tateNormalCurve_scaled (E⁄ℚ) P hP2 hP3
  have hmarked :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25 := by
    rw [← heP, AddEquiv.addOrderOf_eq]
    exact hP
  exact no_orderTwentyFive_marked_order_of_noCanonicalNoncuspidal
    hcanonical b c hb h00 hmarked

end MazurTorsion.Kubert
