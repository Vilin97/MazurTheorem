/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveCanonicalExceptional

/-!
# The cyclic modular-unit orbit on the order-twenty-five canonical carrier

The canonical complete intersection admits the rational order-five linear
transformation

`(x,y,z,w) ↦ (z,w-y,-w,x-y)`.

This file checks that it preserves the canonical curve and that its fifth
iterate is the identity.  It then constructs the five rational functions

`-z/w`, `w/(x-y)`, `(x-y)/(y+z-w)`, `(w-y-z)/x`, `x/z`.

The transformation cyclically permutes these functions.  On the common open
chart where their denominators are nonzero, the canonical quadric and cubic
imply all five Lécacheux difference relations and the norm-one relation.
Consequently the already checked orbit machinery turns two of these explicit
canonical functions into roots of Lehmer's quintic.

`orderTwentyFiveCanonical_lehmerRoots` is the named downstream consumer.
This remains a model-side function-field boundary: identifying these rational
functions with the modular units constructed from a marked Tate point, and
checking their global principal divisors, are separate obligations.
-/

namespace MazurTorsion.Kubert

/-- Affine-cone coordinates for calculations on the canonical model. -/
@[ext]
structure OrderTwentyFiveCanonicalCoordinates (R : Type*) where
  x : R
  y : R
  z : R
  w : R

/-- The order-five linear transformation in canonical coordinates. -/
def orderTwentyFiveCanonicalDeckTransform
    {R : Type*} [Ring R]
    (p : OrderTwentyFiveCanonicalCoordinates R) :
    OrderTwentyFiveCanonicalCoordinates R where
  x := p.z
  y := p.w - p.y
  z := -p.w
  w := p.x - p.y

/-- Coordinate-structure membership in the canonical complete intersection. -/
def OrderTwentyFiveCanonicalCoordinates.OnCurve
    {R : Type*} [CommRing R]
    (p : OrderTwentyFiveCanonicalCoordinates R) : Prop :=
  OrderTwentyFiveCanonicalOnCurve p.x p.y p.z p.w

/-- The canonical quadric is fixed by the deck transformation. -/
theorem orderTwentyFiveCanonicalQuadric_deckTransform
    {R : Type*} [CommRing R]
    (p : OrderTwentyFiveCanonicalCoordinates R) :
    orderTwentyFiveCanonicalQuadric
        (orderTwentyFiveCanonicalDeckTransform p).x
        (orderTwentyFiveCanonicalDeckTransform p).y
        (orderTwentyFiveCanonicalDeckTransform p).z
        (orderTwentyFiveCanonicalDeckTransform p).w =
      orderTwentyFiveCanonicalQuadric p.x p.y p.z p.w := by
  simp only [orderTwentyFiveCanonicalDeckTransform,
    orderTwentyFiveCanonicalQuadric]
  ring

/-- The transformed cubic differs from the original cubic by `-z` times the
quadric, hence cuts out the same complete intersection. -/
theorem orderTwentyFiveCanonicalCubic_deckTransform
    {R : Type*} [CommRing R]
    (p : OrderTwentyFiveCanonicalCoordinates R) :
    orderTwentyFiveCanonicalCubic
        (orderTwentyFiveCanonicalDeckTransform p).x
        (orderTwentyFiveCanonicalDeckTransform p).y
        (orderTwentyFiveCanonicalDeckTransform p).z
        (orderTwentyFiveCanonicalDeckTransform p).w =
      orderTwentyFiveCanonicalCubic p.x p.y p.z p.w -
        p.z * orderTwentyFiveCanonicalQuadric p.x p.y p.z p.w := by
  simp only [orderTwentyFiveCanonicalDeckTransform,
    orderTwentyFiveCanonicalQuadric, orderTwentyFiveCanonicalCubic]
  ring

/-- The deck transformation preserves the canonical complete intersection. -/
theorem OrderTwentyFiveCanonicalCoordinates.OnCurve.deckTransform
    {R : Type*} [CommRing R]
    {p : OrderTwentyFiveCanonicalCoordinates R} (h : p.OnCurve) :
    (orderTwentyFiveCanonicalDeckTransform p).OnCurve := by
  constructor
  · rw [orderTwentyFiveCanonicalQuadric_deckTransform]
    exact h.1
  · rw [orderTwentyFiveCanonicalCubic_deckTransform, h.1, h.2]
    ring

/-- Five applications of the canonical deck transformation are the identity. -/
theorem orderTwentyFiveCanonicalDeckTransform_five
    {R : Type*} [CommRing R]
    (p : OrderTwentyFiveCanonicalCoordinates R) :
    orderTwentyFiveCanonicalDeckTransform
        (orderTwentyFiveCanonicalDeckTransform
          (orderTwentyFiveCanonicalDeckTransform
            (orderTwentyFiveCanonicalDeckTransform
              (orderTwentyFiveCanonicalDeckTransform p)))) = p := by
  ext <;> simp [orderTwentyFiveCanonicalDeckTransform] <;> ring

/-- The first canonical cyclic unit. -/
def orderTwentyFiveCanonicalRootZero
    {K : Type*} [Field K]
    (p : OrderTwentyFiveCanonicalCoordinates K) : K :=
  -p.z / p.w

/-- The second canonical cyclic unit. -/
def orderTwentyFiveCanonicalRootOne
    {K : Type*} [Field K]
    (p : OrderTwentyFiveCanonicalCoordinates K) : K :=
  p.w / (p.x - p.y)

/-- The third canonical cyclic unit. -/
def orderTwentyFiveCanonicalRootTwo
    {K : Type*} [Field K]
    (p : OrderTwentyFiveCanonicalCoordinates K) : K :=
  (p.x - p.y) / (p.y + p.z - p.w)

/-- The fourth canonical cyclic unit. -/
def orderTwentyFiveCanonicalRootThree
    {K : Type*} [Field K]
    (p : OrderTwentyFiveCanonicalCoordinates K) : K :=
  (p.w - p.y - p.z) / p.x

/-- The fifth canonical cyclic unit. -/
def orderTwentyFiveCanonicalRootFour
    {K : Type*} [Field K]
    (p : OrderTwentyFiveCanonicalCoordinates K) : K :=
  p.x / p.z

/-- Pullback by the deck transformation sends the first cyclic unit to the
second. -/
theorem orderTwentyFiveCanonicalRootZero_deckTransform
    {K : Type*} [Field K]
    (p : OrderTwentyFiveCanonicalCoordinates K) :
    orderTwentyFiveCanonicalRootZero
        (orderTwentyFiveCanonicalDeckTransform p) =
      orderTwentyFiveCanonicalRootOne p := by
  simp only [orderTwentyFiveCanonicalRootZero,
    orderTwentyFiveCanonicalRootOne, orderTwentyFiveCanonicalDeckTransform]
  ring

/-- Pullback by the deck transformation sends the second cyclic unit to the
third. -/
theorem orderTwentyFiveCanonicalRootOne_deckTransform
    {K : Type*} [Field K]
    (p : OrderTwentyFiveCanonicalCoordinates K) :
    orderTwentyFiveCanonicalRootOne
        (orderTwentyFiveCanonicalDeckTransform p) =
      orderTwentyFiveCanonicalRootTwo p := by
  simp only [orderTwentyFiveCanonicalRootOne,
    orderTwentyFiveCanonicalRootTwo, orderTwentyFiveCanonicalDeckTransform]
  ring

/-- Pullback by the deck transformation sends the third cyclic unit to the
fourth. -/
theorem orderTwentyFiveCanonicalRootTwo_deckTransform
    {K : Type*} [Field K]
    (p : OrderTwentyFiveCanonicalCoordinates K) :
    orderTwentyFiveCanonicalRootTwo
        (orderTwentyFiveCanonicalDeckTransform p) =
      orderTwentyFiveCanonicalRootThree p := by
  simp only [orderTwentyFiveCanonicalRootTwo,
    orderTwentyFiveCanonicalRootThree, orderTwentyFiveCanonicalDeckTransform]
  ring

/-- Pullback by the deck transformation sends the fourth cyclic unit to the
fifth. -/
theorem orderTwentyFiveCanonicalRootThree_deckTransform
    {K : Type*} [Field K]
    (p : OrderTwentyFiveCanonicalCoordinates K) :
    orderTwentyFiveCanonicalRootThree
        (orderTwentyFiveCanonicalDeckTransform p) =
      orderTwentyFiveCanonicalRootFour p := by
  simp only [orderTwentyFiveCanonicalRootThree,
    orderTwentyFiveCanonicalRootFour, orderTwentyFiveCanonicalDeckTransform]
  ring

/-- Pullback by the deck transformation returns the fifth cyclic unit to the
first. -/
theorem orderTwentyFiveCanonicalRootFour_deckTransform
    {K : Type*} [Field K]
    (p : OrderTwentyFiveCanonicalCoordinates K) :
    orderTwentyFiveCanonicalRootFour
        (orderTwentyFiveCanonicalDeckTransform p) =
      orderTwentyFiveCanonicalRootZero p := by
  simp only [orderTwentyFiveCanonicalRootFour,
    orderTwentyFiveCanonicalRootZero, orderTwentyFiveCanonicalDeckTransform]
  ring

private theorem orderTwentyFiveCanonical_orbitRelationZero
    {K : Type*} [Field K]
    (p : OrderTwentyFiveCanonicalCoordinates K) (hcurve : p.OnCurve)
    (hw : p.w ≠ 0) (hxy : p.x - p.y ≠ 0)
    (hlinear : p.y + p.z - p.w ≠ 0) (hx : p.x ≠ 0) :
    orderTwentyFiveOrbitRelationZero
      (orderTwentyFiveCanonicalRootZero p)
      (orderTwentyFiveCanonicalRootOne p)
      (orderTwentyFiveCanonicalRootTwo p)
      (orderTwentyFiveCanonicalRootThree p)
      (orderTwentyFiveCanonicalRootFour p) = 0 := by
  simp only [OrderTwentyFiveCanonicalCoordinates.OnCurve,
    OrderTwentyFiveCanonicalOnCurve, orderTwentyFiveCanonicalQuadric,
    orderTwentyFiveCanonicalCubic] at hcurve
  simp only [orderTwentyFiveOrbitRelationZero,
    orderTwentyFiveCanonicalRootZero, orderTwentyFiveCanonicalRootOne,
    orderTwentyFiveCanonicalRootTwo, orderTwentyFiveCanonicalRootThree]
  field_simp [hw, hxy, hlinear, hx]
  grobner

private theorem orderTwentyFiveCanonical_orbitRelationOne
    {K : Type*} [Field K]
    (p : OrderTwentyFiveCanonicalCoordinates K) (hcurve : p.OnCurve)
    (hxy : p.x - p.y ≠ 0) (hlinear : p.y + p.z - p.w ≠ 0)
    (hx : p.x ≠ 0) (hz : p.z ≠ 0) :
    orderTwentyFiveOrbitRelationOne
      (orderTwentyFiveCanonicalRootZero p)
      (orderTwentyFiveCanonicalRootOne p)
      (orderTwentyFiveCanonicalRootTwo p)
      (orderTwentyFiveCanonicalRootThree p)
      (orderTwentyFiveCanonicalRootFour p) = 0 := by
  simp only [OrderTwentyFiveCanonicalCoordinates.OnCurve,
    OrderTwentyFiveCanonicalOnCurve, orderTwentyFiveCanonicalQuadric,
    orderTwentyFiveCanonicalCubic] at hcurve
  simp only [orderTwentyFiveOrbitRelationOne,
    orderTwentyFiveCanonicalRootOne,
    orderTwentyFiveCanonicalRootTwo, orderTwentyFiveCanonicalRootThree,
    orderTwentyFiveCanonicalRootFour]
  field_simp [hxy, hlinear, hx, hz]
  grobner

private theorem orderTwentyFiveCanonical_orbitRelationTwo
    {K : Type*} [Field K]
    (p : OrderTwentyFiveCanonicalCoordinates K) (hcurve : p.OnCurve)
    (hw : p.w ≠ 0) (hlinear : p.y + p.z - p.w ≠ 0)
    (hx : p.x ≠ 0) (hz : p.z ≠ 0) :
    orderTwentyFiveOrbitRelationTwo
      (orderTwentyFiveCanonicalRootZero p)
      (orderTwentyFiveCanonicalRootOne p)
      (orderTwentyFiveCanonicalRootTwo p)
      (orderTwentyFiveCanonicalRootThree p)
      (orderTwentyFiveCanonicalRootFour p) = 0 := by
  simp only [OrderTwentyFiveCanonicalCoordinates.OnCurve,
    OrderTwentyFiveCanonicalOnCurve, orderTwentyFiveCanonicalQuadric,
    orderTwentyFiveCanonicalCubic] at hcurve
  simp only [orderTwentyFiveOrbitRelationTwo,
    orderTwentyFiveCanonicalRootZero,
    orderTwentyFiveCanonicalRootTwo, orderTwentyFiveCanonicalRootThree,
    orderTwentyFiveCanonicalRootFour]
  field_simp [hw, hlinear, hx, hz]
  grobner

private theorem orderTwentyFiveCanonical_orbitRelationThree
    {K : Type*} [Field K]
    (p : OrderTwentyFiveCanonicalCoordinates K) (hcurve : p.OnCurve)
    (hw : p.w ≠ 0) (hxy : p.x - p.y ≠ 0)
    (hx : p.x ≠ 0) (hz : p.z ≠ 0) :
    orderTwentyFiveOrbitRelationThree
      (orderTwentyFiveCanonicalRootZero p)
      (orderTwentyFiveCanonicalRootOne p)
      (orderTwentyFiveCanonicalRootTwo p)
      (orderTwentyFiveCanonicalRootThree p)
      (orderTwentyFiveCanonicalRootFour p) = 0 := by
  simp only [OrderTwentyFiveCanonicalCoordinates.OnCurve,
    OrderTwentyFiveCanonicalOnCurve, orderTwentyFiveCanonicalQuadric,
    orderTwentyFiveCanonicalCubic] at hcurve
  simp only [orderTwentyFiveOrbitRelationThree,
    orderTwentyFiveCanonicalRootZero, orderTwentyFiveCanonicalRootOne,
    orderTwentyFiveCanonicalRootThree,
    orderTwentyFiveCanonicalRootFour]
  field_simp [hw, hxy, hx, hz]
  grobner

private theorem orderTwentyFiveCanonical_orbitRelationFour
    {K : Type*} [Field K]
    (p : OrderTwentyFiveCanonicalCoordinates K) (hcurve : p.OnCurve)
    (hw : p.w ≠ 0) (hxy : p.x - p.y ≠ 0)
    (hlinear : p.y + p.z - p.w ≠ 0) (hz : p.z ≠ 0) :
    orderTwentyFiveOrbitRelationFour
      (orderTwentyFiveCanonicalRootZero p)
      (orderTwentyFiveCanonicalRootOne p)
      (orderTwentyFiveCanonicalRootTwo p)
      (orderTwentyFiveCanonicalRootThree p)
      (orderTwentyFiveCanonicalRootFour p) = 0 := by
  simp only [OrderTwentyFiveCanonicalCoordinates.OnCurve,
    OrderTwentyFiveCanonicalOnCurve, orderTwentyFiveCanonicalQuadric,
    orderTwentyFiveCanonicalCubic] at hcurve
  simp only [orderTwentyFiveOrbitRelationFour,
    orderTwentyFiveCanonicalRootZero, orderTwentyFiveCanonicalRootOne,
    orderTwentyFiveCanonicalRootTwo, orderTwentyFiveCanonicalRootFour]
  field_simp [hw, hxy, hlinear, hz]
  grobner

/-- The five canonical cyclic units telescope to one on their common domain. -/
theorem orderTwentyFiveCanonical_orbitRelationFive
    {K : Type*} [Field K]
    (p : OrderTwentyFiveCanonicalCoordinates K)
    (hw : p.w ≠ 0) (hxy : p.x - p.y ≠ 0)
    (hlinear : p.y + p.z - p.w ≠ 0)
    (hx : p.x ≠ 0) (hz : p.z ≠ 0) :
    orderTwentyFiveOrbitRelationFive
      (orderTwentyFiveCanonicalRootZero p)
      (orderTwentyFiveCanonicalRootOne p)
      (orderTwentyFiveCanonicalRootTwo p)
      (orderTwentyFiveCanonicalRootThree p)
      (orderTwentyFiveCanonicalRootFour p) = 0 := by
  simp only [orderTwentyFiveOrbitRelationFive,
    orderTwentyFiveCanonicalRootZero, orderTwentyFiveCanonicalRootOne,
    orderTwentyFiveCanonicalRootTwo, orderTwentyFiveCanonicalRootThree,
    orderTwentyFiveCanonicalRootFour]
  field_simp [hw, hxy, hlinear, hx, hz]
  ring

/-- All six Lécacheux relations hold for the explicit canonical cyclic units
on their common open chart. -/
theorem orderTwentyFiveCanonicalOrbitRelations
    {K : Type*} [Field K]
    (p : OrderTwentyFiveCanonicalCoordinates K) (hcurve : p.OnCurve)
    (hw : p.w ≠ 0) (hxy : p.x - p.y ≠ 0)
    (hlinear : p.y + p.z - p.w ≠ 0)
    (hx : p.x ≠ 0) (hz : p.z ≠ 0) :
    orderTwentyFiveOrbitRelationZero
        (orderTwentyFiveCanonicalRootZero p)
        (orderTwentyFiveCanonicalRootOne p)
        (orderTwentyFiveCanonicalRootTwo p)
        (orderTwentyFiveCanonicalRootThree p)
        (orderTwentyFiveCanonicalRootFour p) = 0 ∧
      orderTwentyFiveOrbitRelationOne
        (orderTwentyFiveCanonicalRootZero p)
        (orderTwentyFiveCanonicalRootOne p)
        (orderTwentyFiveCanonicalRootTwo p)
        (orderTwentyFiveCanonicalRootThree p)
        (orderTwentyFiveCanonicalRootFour p) = 0 ∧
      orderTwentyFiveOrbitRelationTwo
        (orderTwentyFiveCanonicalRootZero p)
        (orderTwentyFiveCanonicalRootOne p)
        (orderTwentyFiveCanonicalRootTwo p)
        (orderTwentyFiveCanonicalRootThree p)
        (orderTwentyFiveCanonicalRootFour p) = 0 ∧
      orderTwentyFiveOrbitRelationThree
        (orderTwentyFiveCanonicalRootZero p)
        (orderTwentyFiveCanonicalRootOne p)
        (orderTwentyFiveCanonicalRootTwo p)
        (orderTwentyFiveCanonicalRootThree p)
        (orderTwentyFiveCanonicalRootFour p) = 0 ∧
      orderTwentyFiveOrbitRelationFour
        (orderTwentyFiveCanonicalRootZero p)
        (orderTwentyFiveCanonicalRootOne p)
        (orderTwentyFiveCanonicalRootTwo p)
        (orderTwentyFiveCanonicalRootThree p)
        (orderTwentyFiveCanonicalRootFour p) = 0 ∧
      orderTwentyFiveOrbitRelationFive
        (orderTwentyFiveCanonicalRootZero p)
        (orderTwentyFiveCanonicalRootOne p)
        (orderTwentyFiveCanonicalRootTwo p)
        (orderTwentyFiveCanonicalRootThree p)
        (orderTwentyFiveCanonicalRootFour p) = 0 := by
  exact ⟨
    orderTwentyFiveCanonical_orbitRelationZero p hcurve hw hxy hlinear hx,
    orderTwentyFiveCanonical_orbitRelationOne p hcurve hxy hlinear hx hz,
    orderTwentyFiveCanonical_orbitRelationTwo p hcurve hw hlinear hx hz,
    orderTwentyFiveCanonical_orbitRelationThree p hcurve hw hxy hx hz,
    orderTwentyFiveCanonical_orbitRelationFour p hcurve hw hxy hlinear hz,
    orderTwentyFiveCanonical_orbitRelationFive p hw hxy hlinear hx hz⟩

/-- Two explicit functions on the canonical carrier are roots of the same
Lehmer quintic, with invariant recovered from the full cyclic orbit. -/
theorem orderTwentyFiveCanonical_lehmerRoots
    (p : OrderTwentyFiveCanonicalCoordinates ℚ) (hcurve : p.OnCurve)
    (hw : p.w ≠ 0) (hxy : p.x - p.y ≠ 0)
    (hlinear : p.y + p.z - p.w ≠ 0)
    (hx : p.x ≠ 0) (hz : p.z ≠ 0)
    (hroot : orderTwentyFiveCanonicalRootZero p ≠ 1) :
    orderTwentyFiveLehmerPolynomial
        (orderTwentyFiveOrbitParameter
          (orderTwentyFiveCanonicalRootZero p)
          (orderTwentyFiveCanonicalRootOne p)
          (orderTwentyFiveCanonicalRootTwo p)
          (orderTwentyFiveCanonicalRootThree p)
          (orderTwentyFiveCanonicalRootFour p))
        (orderTwentyFiveCanonicalRootZero p) = 0 ∧
      orderTwentyFiveLehmerPolynomial
        (orderTwentyFiveOrbitParameter
          (orderTwentyFiveCanonicalRootZero p)
          (orderTwentyFiveCanonicalRootOne p)
          (orderTwentyFiveCanonicalRootTwo p)
          (orderTwentyFiveCanonicalRootThree p)
          (orderTwentyFiveCanonicalRootFour p))
        (orderTwentyFiveCanonicalRootTwo p) = 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ :=
    orderTwentyFiveCanonicalOrbitRelations
      p hcurve hw hxy hlinear hx hz
  exact orderTwentyFiveLehmer_selectedRoots_of_orbit
    (orderTwentyFiveCanonicalRootZero p)
    (orderTwentyFiveCanonicalRootOne p)
    (orderTwentyFiveCanonicalRootTwo p)
    (orderTwentyFiveCanonicalRootThree p)
    (orderTwentyFiveCanonicalRootFour p)
    hroot h0 h1 h2 h3 h4 h5

end MazurTorsion.Kubert
