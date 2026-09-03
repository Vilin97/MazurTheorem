/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveCanonicalLocalOrder
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Two represented affine charts of the order-25 canonical curve

Two linear forms suffice to cover the canonical quadric-cubic complete
intersection in characteristic zero:

* the left chart normalizes `x + z = 1` and uses coordinates `(x,y,w)`;
* the right chart normalizes `x + w = 1` and uses coordinates `(x,y,z)`.

Each chart is represented by the quotient of a three-variable polynomial
ring by the normalized quadric and cubic.  Its algebra-valued points are
proved equivalent to solutions of the two canonical equations over every
commutative target algebra.  The cover proof is representative-level and
uses the exact obstruction `5x² = 0` on the common complement.

The named downstream packages `pointEquivalences` and `twoFormsCover`
supply the represented charts and covering calculation needed for their
scheme-theoretic gluing.  Constructing the overlap isomorphism remains the
next boundary.
-/

noncomputable section

open MvPolynomial
open _root_.AlgebraicGeometry

namespace MazurTorsion.Kubert
namespace OrderTwentyFiveCanonicalAffineCharts

universe u v

/-! ## Normalized equations and coordinate rings -/

/-- The canonical quadric after normalizing `x + z = 1`; the variables are
`(x,y,w)`. -/
def leftQuadric (K : Type u) [CommRing K] : MvPolynomial (Fin 3) K :=
  orderTwentyFiveCanonicalQuadric (X 0) (X 1) (1 - X 0) (X 2)

/-- The canonical cubic after normalizing `x + z = 1`; the variables are
`(x,y,w)`. -/
def leftCubic (K : Type u) [CommRing K] : MvPolynomial (Fin 3) K :=
  orderTwentyFiveCanonicalCubic (X 0) (X 1) (1 - X 0) (X 2)

/-- Evaluation of the normalized left-chart quadric recovers the canonical
quadric. -/
theorem eval_leftQuadric {K A : Type*} [CommRing K] [CommRing A]
    (g : K →+* A) (p : Fin 3 → A) :
    eval₂ g p (leftQuadric K) =
      orderTwentyFiveCanonicalQuadric (p 0) (p 1) (1 - p 0) (p 2) := by
  simp [leftQuadric, orderTwentyFiveCanonicalQuadric]

/-- Evaluation of the normalized left-chart cubic recovers the canonical
cubic. -/
theorem eval_leftCubic {K A : Type*} [CommRing K] [CommRing A]
    (g : K →+* A) (p : Fin 3 → A) :
    eval₂ g p (leftCubic K) =
      orderTwentyFiveCanonicalCubic (p 0) (p 1) (1 - p 0) (p 2) := by
  simp [leftCubic, orderTwentyFiveCanonicalCubic]

/-- The canonical quadric after normalizing `x + w = 1`; the variables are
`(x,y,z)`. -/
def rightQuadric (K : Type u) [CommRing K] : MvPolynomial (Fin 3) K :=
  orderTwentyFiveCanonicalQuadric (X 0) (X 1) (X 2) (1 - X 0)

/-- The canonical cubic after normalizing `x + w = 1`; the variables are
`(x,y,z)`. -/
def rightCubic (K : Type u) [CommRing K] : MvPolynomial (Fin 3) K :=
  orderTwentyFiveCanonicalCubic (X 0) (X 1) (X 2) (1 - X 0)

/-- Evaluation of the normalized right-chart quadric recovers the canonical
quadric. -/
theorem eval_rightQuadric {K A : Type*} [CommRing K] [CommRing A]
    (g : K →+* A) (p : Fin 3 → A) :
    eval₂ g p (rightQuadric K) =
      orderTwentyFiveCanonicalQuadric (p 0) (p 1) (p 2) (1 - p 0) := by
  simp [rightQuadric, orderTwentyFiveCanonicalQuadric]

/-- Evaluation of the normalized right-chart cubic recovers the canonical
cubic. -/
theorem eval_rightCubic {K A : Type*} [CommRing K] [CommRing A]
    (g : K →+* A) (p : Fin 3 → A) :
    eval₂ g p (rightCubic K) =
      orderTwentyFiveCanonicalCubic (p 0) (p 1) (p 2) (1 - p 0) := by
  simp [rightCubic, orderTwentyFiveCanonicalCubic]

/-- The two-equation ideal of the `x + z = 1` chart. -/
def leftIdeal (K : Type u) [CommRing K] :
    Ideal (MvPolynomial (Fin 3) K) :=
  Ideal.span {leftQuadric K, leftCubic K}

/-- Coordinate algebra of the `x + z = 1` chart. -/
abbrev LeftRing (K : Type u) [CommRing K] :=
  MvPolynomial (Fin 3) K ⧸ leftIdeal K

/-- The two-equation ideal of the `x + w = 1` chart. -/
def rightIdeal (K : Type u) [CommRing K] :
    Ideal (MvPolynomial (Fin 3) K) :=
  Ideal.span {rightQuadric K, rightCubic K}

/-- Coordinate algebra of the `x + w = 1` chart. -/
abbrev RightRing (K : Type u) [CommRing K] :=
  MvPolynomial (Fin 3) K ⧸ rightIdeal K

/-- The represented affine `x + z = 1` chart. -/
abbrev leftScheme (K : Type u) [CommRing K] : Scheme :=
  Spec (.of (LeftRing K))

/-- The represented affine `x + w = 1` chart. -/
abbrev rightScheme (K : Type u) [CommRing K] : Scheme :=
  Spec (.of (RightRing K))

/-! ## Algebra-valued points of the left chart -/

/-- A normalized canonical solution on the `x + z = 1` chart. -/
def LeftSolution (A : Type v) [CommRing A] :=
  {p : Fin 3 → A //
    OrderTwentyFiveCanonicalOnCurve (p 0) (p 1) (1 - p 0) (p 2)}

private theorem leftIdeal_le_ker_aeval
    {K : Type u} [CommRing K]
    (A : Type v) [CommRing A] [Algebra K A]
    (p : LeftSolution A) :
    leftIdeal K ≤ RingHom.ker (MvPolynomial.aeval p.1) := by
  rw [leftIdeal, Ideal.span_le]
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl
  · change (MvPolynomial.aeval p.1) (leftQuadric K) = 0
    rw [MvPolynomial.aeval_def, eval_leftQuadric]
    exact p.2.1
  · change (MvPolynomial.aeval p.1) (leftCubic K) = 0
    rw [MvPolynomial.aeval_def, eval_leftCubic]
    exact p.2.2

/-- Evaluation of the left coordinate algebra at a normalized solution. -/
def leftSolutionToAlgHom
    {K : Type u} [CommRing K]
    (A : Type v) [CommRing A] [Algebra K A]
    (p : LeftSolution A) : LeftRing K →ₐ[K] A :=
  Ideal.Quotient.liftₐ (leftIdeal K) (MvPolynomial.aeval p.1)
    (fun _ h ↦ leftIdeal_le_ker_aeval A p h)

/-- Evaluation at a left-chart solution sends each quotient coordinate to
the corresponding component. -/
@[simp]
theorem leftSolutionToAlgHom_X
    {K : Type u} [CommRing K]
    (A : Type v) [CommRing A] [Algebra K A]
    (p : LeftSolution A) (i : Fin 3) :
    leftSolutionToAlgHom A p
        (Ideal.Quotient.mk (leftIdeal K) (MvPolynomial.X i)) = p.1 i := by
  have hcomp :
      (leftSolutionToAlgHom A p).comp
          (Ideal.Quotient.mkₐ K (leftIdeal K)) =
        MvPolynomial.aeval p.1 :=
    Ideal.Quotient.liftₐ_comp (leftIdeal K)
      (MvPolynomial.aeval p.1)
      (fun _ h ↦ leftIdeal_le_ker_aeval A p h)
  calc
    _ = ((leftSolutionToAlgHom A p).comp
          (Ideal.Quotient.mkₐ K (leftIdeal K))) (MvPolynomial.X i) := rfl
    _ = (MvPolynomial.aeval p.1) (MvPolynomial.X i) :=
      DFunLike.congr_fun hcomp (MvPolynomial.X i)
    _ = p.1 i := MvPolynomial.aeval_X p.1 i

/-- An algebra-valued point of the left chart recovers its three normalized
coordinates. -/
def leftAlgHomToSolution
    {K : Type u} [CommRing K]
    (A : Type v) [CommRing A] [Algebra K A]
    (f : LeftRing K →ₐ[K] A) : LeftSolution A := by
  let p : Fin 3 → A := fun i ↦
    f (Ideal.Quotient.mk (leftIdeal K) (MvPolynomial.X i))
  have heval :
      f.comp (Ideal.Quotient.mkₐ K (leftIdeal K)) =
        MvPolynomial.aeval p := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [p]
  refine ⟨p, ?_, ?_⟩
  · rw [← eval_leftQuadric (algebraMap K A) p,
      ← MvPolynomial.aeval_def, ← heval]
    simp only [AlgHom.comp_apply]
    change f (Ideal.Quotient.mk (leftIdeal K) (leftQuadric K)) = 0
    have hq : Ideal.Quotient.mk (leftIdeal K) (leftQuadric K) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span
          (Set.mem_insert (leftQuadric K) {leftCubic K}))
    exact (congrArg f hq).trans (map_zero f)
  · rw [← eval_leftCubic (algebraMap K A) p,
      ← MvPolynomial.aeval_def, ← heval]
    simp only [AlgHom.comp_apply]
    change f (Ideal.Quotient.mk (leftIdeal K) (leftCubic K)) = 0
    have hc : Ideal.Quotient.mk (leftIdeal K) (leftCubic K) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_insert_iff.mpr (Or.inr rfl)))
    exact (congrArg f hc).trans (map_zero f)

/-- Normalized solutions on the left chart are exactly its algebra-valued
points. -/
def leftSolutionAlgHomEquiv
    {K : Type u} [CommRing K]
    (A : Type v) [CommRing A] [Algebra K A] :
    LeftSolution A ≃ (LeftRing K →ₐ[K] A) where
  toFun := leftSolutionToAlgHom A
  invFun := leftAlgHomToSolution A
  left_inv p := by
    apply Subtype.ext
    funext i
    have hcomp :
        (leftSolutionToAlgHom A p).comp
            (Ideal.Quotient.mkₐ K (leftIdeal K)) =
          MvPolynomial.aeval p.1 :=
      Ideal.Quotient.liftₐ_comp (leftIdeal K)
        (MvPolynomial.aeval p.1)
        (fun _ h ↦ leftIdeal_le_ker_aeval A p h)
    calc
      (leftAlgHomToSolution A (leftSolutionToAlgHom A p)).1 i =
          ((leftSolutionToAlgHom A p).comp
            (Ideal.Quotient.mkₐ K (leftIdeal K))) (MvPolynomial.X i) := rfl
      _ = (MvPolynomial.aeval p.1) (MvPolynomial.X i) :=
        DFunLike.congr_fun hcomp (MvPolynomial.X i)
      _ = p.1 i := MvPolynomial.aeval_X p.1 i
  right_inv f := by
    apply Ideal.Quotient.algHom_ext K
    apply MvPolynomial.algHom_ext
    intro i
    let p := leftAlgHomToSolution A f
    have hcomp :
        (leftSolutionToAlgHom A p).comp
            (Ideal.Quotient.mkₐ K (leftIdeal K)) =
          MvPolynomial.aeval p.1 :=
      Ideal.Quotient.liftₐ_comp (leftIdeal K)
        (MvPolynomial.aeval p.1)
        (fun _ h ↦ leftIdeal_le_ker_aeval A p h)
    calc
      ((leftSolutionToAlgHom A (leftAlgHomToSolution A f)).comp
          (Ideal.Quotient.mkₐ K (leftIdeal K))) (MvPolynomial.X i) =
          (MvPolynomial.aeval p.1) (MvPolynomial.X i) := by
        exact DFunLike.congr_fun hcomp (MvPolynomial.X i)
      _ = p.1 i := MvPolynomial.aeval_X p.1 i
      _ = (f.comp (Ideal.Quotient.mkₐ K (leftIdeal K)))
          (MvPolynomial.X i) := rfl

/-! ## Algebra-valued points of the right chart -/

/-- A normalized canonical solution on the `x + w = 1` chart. -/
def RightSolution (A : Type v) [CommRing A] :=
  {p : Fin 3 → A //
    OrderTwentyFiveCanonicalOnCurve (p 0) (p 1) (p 2) (1 - p 0)}

private theorem rightIdeal_le_ker_aeval
    {K : Type u} [CommRing K]
    (A : Type v) [CommRing A] [Algebra K A]
    (p : RightSolution A) :
    rightIdeal K ≤ RingHom.ker (MvPolynomial.aeval p.1) := by
  rw [rightIdeal, Ideal.span_le]
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl
  · change (MvPolynomial.aeval p.1) (rightQuadric K) = 0
    rw [MvPolynomial.aeval_def, eval_rightQuadric]
    exact p.2.1
  · change (MvPolynomial.aeval p.1) (rightCubic K) = 0
    rw [MvPolynomial.aeval_def, eval_rightCubic]
    exact p.2.2

/-- Evaluation of the right coordinate algebra at a normalized solution. -/
def rightSolutionToAlgHom
    {K : Type u} [CommRing K]
    (A : Type v) [CommRing A] [Algebra K A]
    (p : RightSolution A) : RightRing K →ₐ[K] A :=
  Ideal.Quotient.liftₐ (rightIdeal K) (MvPolynomial.aeval p.1)
    (fun _ h ↦ rightIdeal_le_ker_aeval A p h)

/-- Evaluation at a right-chart solution sends each quotient coordinate to
the corresponding component. -/
@[simp]
theorem rightSolutionToAlgHom_X
    {K : Type u} [CommRing K]
    (A : Type v) [CommRing A] [Algebra K A]
    (p : RightSolution A) (i : Fin 3) :
    rightSolutionToAlgHom A p
        (Ideal.Quotient.mk (rightIdeal K) (MvPolynomial.X i)) = p.1 i := by
  have hcomp :
      (rightSolutionToAlgHom A p).comp
          (Ideal.Quotient.mkₐ K (rightIdeal K)) =
        MvPolynomial.aeval p.1 :=
    Ideal.Quotient.liftₐ_comp (rightIdeal K)
      (MvPolynomial.aeval p.1)
      (fun _ h ↦ rightIdeal_le_ker_aeval A p h)
  calc
    _ = ((rightSolutionToAlgHom A p).comp
          (Ideal.Quotient.mkₐ K (rightIdeal K))) (MvPolynomial.X i) := rfl
    _ = (MvPolynomial.aeval p.1) (MvPolynomial.X i) :=
      DFunLike.congr_fun hcomp (MvPolynomial.X i)
    _ = p.1 i := MvPolynomial.aeval_X p.1 i

/-- An algebra-valued point of the right chart recovers its three normalized
coordinates. -/
def rightAlgHomToSolution
    {K : Type u} [CommRing K]
    (A : Type v) [CommRing A] [Algebra K A]
    (f : RightRing K →ₐ[K] A) : RightSolution A := by
  let p : Fin 3 → A := fun i ↦
    f (Ideal.Quotient.mk (rightIdeal K) (MvPolynomial.X i))
  have heval :
      f.comp (Ideal.Quotient.mkₐ K (rightIdeal K)) =
        MvPolynomial.aeval p := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [p]
  refine ⟨p, ?_, ?_⟩
  · rw [← eval_rightQuadric (algebraMap K A) p,
      ← MvPolynomial.aeval_def, ← heval]
    simp only [AlgHom.comp_apply]
    change f (Ideal.Quotient.mk (rightIdeal K) (rightQuadric K)) = 0
    have hq : Ideal.Quotient.mk (rightIdeal K) (rightQuadric K) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span
          (Set.mem_insert (rightQuadric K) {rightCubic K}))
    exact (congrArg f hq).trans (map_zero f)
  · rw [← eval_rightCubic (algebraMap K A) p,
      ← MvPolynomial.aeval_def, ← heval]
    simp only [AlgHom.comp_apply]
    change f (Ideal.Quotient.mk (rightIdeal K) (rightCubic K)) = 0
    have hc : Ideal.Quotient.mk (rightIdeal K) (rightCubic K) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_insert_iff.mpr (Or.inr rfl)))
    exact (congrArg f hc).trans (map_zero f)

/-- Normalized solutions on the right chart are exactly its algebra-valued
points. -/
def rightSolutionAlgHomEquiv
    {K : Type u} [CommRing K]
    (A : Type v) [CommRing A] [Algebra K A] :
    RightSolution A ≃ (RightRing K →ₐ[K] A) where
  toFun := rightSolutionToAlgHom A
  invFun := rightAlgHomToSolution A
  left_inv p := by
    apply Subtype.ext
    funext i
    have hcomp :
        (rightSolutionToAlgHom A p).comp
            (Ideal.Quotient.mkₐ K (rightIdeal K)) =
          MvPolynomial.aeval p.1 :=
      Ideal.Quotient.liftₐ_comp (rightIdeal K)
        (MvPolynomial.aeval p.1)
        (fun _ h ↦ rightIdeal_le_ker_aeval A p h)
    calc
      (rightAlgHomToSolution A (rightSolutionToAlgHom A p)).1 i =
          ((rightSolutionToAlgHom A p).comp
            (Ideal.Quotient.mkₐ K (rightIdeal K))) (MvPolynomial.X i) := rfl
      _ = (MvPolynomial.aeval p.1) (MvPolynomial.X i) :=
        DFunLike.congr_fun hcomp (MvPolynomial.X i)
      _ = p.1 i := MvPolynomial.aeval_X p.1 i
  right_inv f := by
    apply Ideal.Quotient.algHom_ext K
    apply MvPolynomial.algHom_ext
    intro i
    let p := rightAlgHomToSolution A f
    have hcomp :
        (rightSolutionToAlgHom A p).comp
            (Ideal.Quotient.mkₐ K (rightIdeal K)) =
          MvPolynomial.aeval p.1 :=
      Ideal.Quotient.liftₐ_comp (rightIdeal K)
        (MvPolynomial.aeval p.1)
        (fun _ h ↦ rightIdeal_le_ker_aeval A p h)
    calc
      ((rightSolutionToAlgHom A (rightAlgHomToSolution A f)).comp
          (Ideal.Quotient.mkₐ K (rightIdeal K))) (MvPolynomial.X i) =
          (MvPolynomial.aeval p.1) (MvPolynomial.X i) := by
        exact DFunLike.congr_fun hcomp (MvPolynomial.X i)
      _ = p.1 i := MvPolynomial.aeval_X p.1 i
      _ = (f.comp (Ideal.Quotient.mkₐ K (rightIdeal K)))
          (MvPolynomial.X i) := rfl

/-- Named representability package for both normalized affine charts. -/
theorem pointEquivalences
    {K : Type u} [CommRing K]
    (A : Type v) [CommRing A] [Algebra K A] :
    Function.Bijective (leftSolutionAlgHomEquiv (K := K) A) ∧
      Function.Bijective (rightSolutionAlgHomEquiv (K := K) A) := by
  exact ⟨Equiv.bijective _, Equiv.bijective _⟩

/-! ## Covering and normalization -/

/-- The linear forms `x + z` and `x + w` cannot vanish simultaneously on
a nonzero characteristic-zero canonical point.  Thus their two standard
affine opens cover the entire projective complete intersection. -/
theorem twoFormsCover
    {K : Type*} [Field K] [CharZero K]
    (x y z w : K)
    (hcurve : OrderTwentyFiveCanonicalOnCurve x y z w)
    (hne : (![x, y, z, w] : Fin 4 → K) ≠ 0) :
    x + z ≠ 0 ∨ x + w ≠ 0 := by
  by_contra hcover
  rw [not_or, not_ne_iff, not_ne_iff] at hcover
  have hz : z = -x := by linear_combination hcover.1
  have hw : w = -x := by linear_combination hcover.2
  have hq : 3 * x ^ 2 - x * y + y ^ 2 = 0 := by
    have hqraw := hcurve.1
    rw [hz, hw] at hqraw
    simp only [orderTwentyFiveCanonicalQuadric] at hqraw
    linear_combination hqraw
  have hc : x ^ 2 * (2 * x - y) = 0 := by
    have hcraw := hcurve.2
    rw [hz, hw] at hcraw
    simp only [orderTwentyFiveCanonicalCubic] at hcraw
    linear_combination -hcraw
  by_cases hx : x = 0
  · have hy : y = 0 := by
      rw [hx] at hq
      simpa using (sq_eq_zero_iff.mp (by simpa using hq))
    apply hne
    funext i
    fin_cases i <;> simp [hx, hy, hz, hw]
  · have hy : y = 2 * x := by
      have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
      have hxy := (mul_eq_zero.mp hc).resolve_left hx2
      linear_combination -hxy
    rw [hy] at hq
    have h5 : (5 : K) * x ^ 2 = 0 := by
      linear_combination hq
    exact hx
      (sq_eq_zero_iff.mp ((mul_eq_zero.mp h5).resolve_left (by norm_num)))

/-- Dividing by `x + z` sends a canonical representative to the normalized
left chart. -/
theorem leftNormalize
    {K : Type*} [Field K]
    (x y z w : K)
    (hcurve : OrderTwentyFiveCanonicalOnCurve x y z w)
    (hL : x + z ≠ 0) :
    OrderTwentyFiveCanonicalOnCurve
      (x / (x + z)) (y / (x + z))
      (1 - x / (x + z)) (w / (x + z)) := by
  have hz : 1 - x / (x + z) = z / (x + z) := by
    field_simp
    ring
  rw [hz]
  constructor
  · simp only [orderTwentyFiveCanonicalQuadric]
    have hq := hcurve.1
    simp only [orderTwentyFiveCanonicalQuadric] at hq
    field_simp
    linear_combination hq
  · simp only [orderTwentyFiveCanonicalCubic]
    have hc := hcurve.2
    simp only [orderTwentyFiveCanonicalCubic] at hc
    field_simp
    linear_combination hc

/-- Dividing by `x + w` sends a canonical representative to the normalized
right chart. -/
theorem rightNormalize
    {K : Type*} [Field K]
    (x y z w : K)
    (hcurve : OrderTwentyFiveCanonicalOnCurve x y z w)
    (hM : x + w ≠ 0) :
    OrderTwentyFiveCanonicalOnCurve
      (x / (x + w)) (y / (x + w)) (z / (x + w))
      (1 - x / (x + w)) := by
  have hw : 1 - x / (x + w) = w / (x + w) := by
    field_simp
    ring
  rw [hw]
  constructor
  · simp only [orderTwentyFiveCanonicalQuadric]
    have hq := hcurve.1
    simp only [orderTwentyFiveCanonicalQuadric] at hq
    field_simp
    linear_combination hq
  · simp only [orderTwentyFiveCanonicalCubic]
    have hc := hcurve.2
    simp only [orderTwentyFiveCanonicalCubic] at hc
    field_simp
    linear_combination hc

/-- Every point of the `w = 0` hyperplane section lies in the left affine
chart. -/
theorem leftForm_ne_zero_of_w_eq_zero
    {K : Type*} [Field K]
    (x y z w : K)
    (hcurve : OrderTwentyFiveCanonicalOnCurve x y z w)
    (hne : (![x, y, z, w] : Fin 4 → K) ≠ 0)
    (hw0 : w = 0) :
    x + z ≠ 0 := by
  intro hL
  have hz : z = -x := by linear_combination hL
  have hq : y ^ 2 + x ^ 2 - x * y = 0 := by
    have hqraw := hcurve.1
    rw [hz, hw0] at hqraw
    simp only [orderTwentyFiveCanonicalQuadric] at hqraw
    linear_combination hqraw
  have hc : x ^ 2 * y = 0 := by
    have hcraw := hcurve.2
    rw [hz, hw0] at hcraw
    simp only [orderTwentyFiveCanonicalCubic] at hcraw
    linear_combination -hcraw
  by_cases hx : x = 0
  · have hy : y = 0 := by
      rw [hx] at hq
      exact sq_eq_zero_iff.mp (by simpa using hq)
    apply hne
    funext i
    fin_cases i <;> simp [hx, hy, hz, hw0]
  · have hy : y = 0 :=
      (mul_eq_zero.mp hc).resolve_left (pow_ne_zero 2 hx)
    rw [hy] at hq
    exact hx (sq_eq_zero_iff.mp (by simpa using hq))

/-- Every point of the `z = 0` hyperplane section lies in the right affine
chart in characteristic zero. -/
theorem rightForm_ne_zero_of_z_eq_zero
    {K : Type*} [Field K] [CharZero K]
    (x y z w : K)
    (hcurve : OrderTwentyFiveCanonicalOnCurve x y z w)
    (hne : (![x, y, z, w] : Fin 4 → K) ≠ 0)
    (hz0 : z = 0) :
    x + w ≠ 0 := by
  intro hM
  have hw : w = -x := by linear_combination hM
  have hq : y ^ 2 + x ^ 2 = 0 := by
    have hqraw := hcurve.1
    rw [hz0, hw] at hqraw
    simp only [orderTwentyFiveCanonicalQuadric] at hqraw
    linear_combination hqraw
  have hc : x ^ 2 * (x - y) = 0 := by
    have hcraw := hcurve.2
    rw [hz0, hw] at hcraw
    simp only [orderTwentyFiveCanonicalCubic] at hcraw
    linear_combination -hcraw
  by_cases hx : x = 0
  · have hy : y = 0 := by
      rw [hx] at hq
      exact sq_eq_zero_iff.mp (by simpa using hq)
    apply hne
    funext i
    fin_cases i <;> simp [hx, hy, hz0, hw]
  · have hy : y = x := by
      have hxy :=
        (mul_eq_zero.mp hc).resolve_left (pow_ne_zero 2 hx)
      linear_combination -hxy
    rw [hy] at hq
    have h2 : (2 : K) * x ^ 2 = 0 := by
      linear_combination hq
    exact hx
      (sq_eq_zero_iff.mp
        ((mul_eq_zero.mp h2).resolve_left (by norm_num)))

end OrderTwentyFiveCanonicalAffineCharts
end MazurTorsion.Kubert
