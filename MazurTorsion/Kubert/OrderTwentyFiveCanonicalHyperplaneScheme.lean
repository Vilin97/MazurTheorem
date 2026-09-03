/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveCanonicalHyperplane
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.RingTheory.AdjoinRoot

/-!
# Affine schemes of the order-25 canonical hyperplane sections

The field-valued locus calculations for the coordinate sections `w = 0`
and `z = 0` discard the nilpotents which record intersection multiplicity.
This file retains them.  Over every commutative ring, the four normalized
chart intersections are equivalent to

* `x = y²+y`, `y²(y+1)=0` on `(z,w)=(1,0)`;
* `z = y²`, `y³=0` on `(x,w)=(1,0)`;
* `x = y²`, `y³(y-1)=0` on `(z,w)=(0,1)`;
* `w = y²`, `y²(y-1)=0` on `(x,z)=(1,0)`.

The four residual equations define actual affine schemes by `Spec` of their
`AdjoinRoot` algebras.  Their algebra-valued points are proved equivalent to
the corresponding pairs satisfying both canonical equations.  In
particular, this statement remains valid for nonreduced target rings and
therefore remembers the thickened cusp intersections.  The coordinate-ring
dimensions `3, 3, 4, 3` are also checked over every field.

`orderTwentyFiveCanonical_hyperplaneChartScheme_pointEquivalences` is the
named downstream consumer.  Gluing these charts into the represented
projective canonical curve and identifying the resulting zero-dimensional
closed subschemes with global Cartier divisors remain the geometric boundary.
-/

noncomputable section

open Polynomial
open _root_.AlgebraicGeometry

namespace MazurTorsion.Kubert

universe u v

/-! ## Ring-level elimination, retaining nilpotents -/

/-- Scheme-theoretic elimination on the `z = 1` chart of `w = 0`. -/
theorem orderTwentyFiveCanonical_w_zChart_schemeLocus
    {R : Type*} [CommRing R] (x y : R) :
    OrderTwentyFiveCanonicalOnCurve x y 1 0 ↔
      x = y ^ 2 + y ∧ y ^ 2 * (y + 1) = 0 := by
  constructor
  · rintro ⟨hQ, hC⟩
    constructor
    · simp only [orderTwentyFiveCanonicalQuadric] at hQ
      linear_combination -hQ
    · rw [← orderTwentyFiveCanonical_w_zChart_elimination x y, hQ, hC]
      ring
  · rintro ⟨hx, hp⟩
    constructor
    · simp only [orderTwentyFiveCanonicalQuadric]
      rw [hx]
      ring
    · simp only [orderTwentyFiveCanonicalCubic]
      rw [hx]
      linear_combination hp

/-- Scheme-theoretic elimination on the `x = 1` chart of `w = 0`. -/
theorem orderTwentyFiveCanonical_w_xChart_schemeLocus
    {R : Type*} [CommRing R] (y z : R) :
    OrderTwentyFiveCanonicalOnCurve 1 y z 0 ↔
      z = y ^ 2 ∧ y ^ 3 = 0 := by
  constructor
  · rintro ⟨hQ, hC⟩
    have hCsimple : y * z = 0 := by
      simpa [orderTwentyFiveCanonicalCubic] using hC
    have hz : z = y ^ 2 := by
      simp only [orderTwentyFiveCanonicalQuadric] at hQ
      linear_combination -hQ + hCsimple
    refine ⟨hz, ?_⟩
    rw [hz] at hCsimple
    linear_combination hCsimple
  · rintro ⟨hz, hp⟩
    constructor
    · simp only [orderTwentyFiveCanonicalQuadric]
      rw [hz]
      linear_combination hp
    · simp only [orderTwentyFiveCanonicalCubic]
      rw [hz]
      linear_combination hp

/-- Scheme-theoretic elimination on the `w = 1` chart of `z = 0`. -/
theorem orderTwentyFiveCanonical_z_wChart_schemeLocus
    {R : Type*} [CommRing R] (x y : R) :
    OrderTwentyFiveCanonicalOnCurve x y 0 1 ↔
      x = y ^ 2 ∧ y ^ 3 * (y - 1) = 0 := by
  constructor
  · rintro ⟨hQ, hC⟩
    have hx : x = y ^ 2 := by
      simp only [orderTwentyFiveCanonicalQuadric] at hQ
      linear_combination -hQ
    refine ⟨hx, ?_⟩
    rw [orderTwentyFiveCanonical_z_wChart_elimination x y, hQ] at hC
    simpa using hC
  · rintro ⟨hx, hp⟩
    constructor
    · simp only [orderTwentyFiveCanonicalQuadric]
      rw [hx]
      ring
    · simp only [orderTwentyFiveCanonicalCubic]
      rw [hx]
      linear_combination hp

/-- Scheme-theoretic elimination on the `x = 1` chart of `z = 0`. -/
theorem orderTwentyFiveCanonical_z_xChart_schemeLocus
    {R : Type*} [CommRing R] (y w : R) :
    OrderTwentyFiveCanonicalOnCurve 1 y 0 w ↔
      w = y ^ 2 ∧ y ^ 2 * (y - 1) = 0 := by
  constructor
  · rintro ⟨hQ, hC⟩
    have hw : w = y ^ 2 := by
      simp only [orderTwentyFiveCanonicalQuadric] at hQ
      linear_combination -hQ
    refine ⟨hw, ?_⟩
    have hid := orderTwentyFiveCanonical_z_xChart_elimination y w
    rw [hQ, hC] at hid
    simpa using hid
  · rintro ⟨hw, hp⟩
    constructor
    · simp only [orderTwentyFiveCanonicalQuadric]
      rw [hw]
      ring
    · simp only [orderTwentyFiveCanonicalCubic]
      rw [hw]
      linear_combination -hp

/-! ## The four represented residual schemes -/

variable (K : Type u) [CommRing K]

/-- Residual equation on the `z = 1`, `w = 0` chart. -/
def orderTwentyFiveCanonicalWZIntersectionEquation : Polynomial K :=
  X ^ 2 * (X + C 1)

/-- Residual equation on the `x = 1`, `w = 0` chart. -/
def orderTwentyFiveCanonicalWXIntersectionEquation : Polynomial K :=
  X ^ 3

/-- Residual equation on the `w = 1`, `z = 0` chart. -/
def orderTwentyFiveCanonicalZWIntersectionEquation : Polynomial K :=
  X ^ 3 * (X - C 1)

/-- Residual equation on the `x = 1`, `z = 0` chart. -/
def orderTwentyFiveCanonicalZXIntersectionEquation : Polynomial K :=
  X ^ 2 * (X - C 1)

/-- Coordinate algebra of the `z = 1`, `w = 0` intersection chart. -/
abbrev OrderTwentyFiveCanonicalWZIntersectionRing :=
  AdjoinRoot (orderTwentyFiveCanonicalWZIntersectionEquation K)

/-- Coordinate algebra of the `x = 1`, `w = 0` intersection chart. -/
abbrev OrderTwentyFiveCanonicalWXIntersectionRing :=
  AdjoinRoot (orderTwentyFiveCanonicalWXIntersectionEquation K)

/-- Coordinate algebra of the `w = 1`, `z = 0` intersection chart. -/
abbrev OrderTwentyFiveCanonicalZWIntersectionRing :=
  AdjoinRoot (orderTwentyFiveCanonicalZWIntersectionEquation K)

/-- Coordinate algebra of the `x = 1`, `z = 0` intersection chart. -/
abbrev OrderTwentyFiveCanonicalZXIntersectionRing :=
  AdjoinRoot (orderTwentyFiveCanonicalZXIntersectionEquation K)

/-- The `z = 1`, `w = 0` intersection as an actual affine scheme. -/
abbrev orderTwentyFiveCanonicalWZIntersectionScheme : Scheme :=
  Spec (.of (OrderTwentyFiveCanonicalWZIntersectionRing K))

/-- The `x = 1`, `w = 0` intersection as an actual affine scheme. -/
abbrev orderTwentyFiveCanonicalWXIntersectionScheme : Scheme :=
  Spec (.of (OrderTwentyFiveCanonicalWXIntersectionRing K))

/-- The `w = 1`, `z = 0` intersection as an actual affine scheme. -/
abbrev orderTwentyFiveCanonicalZWIntersectionScheme : Scheme :=
  Spec (.of (OrderTwentyFiveCanonicalZWIntersectionRing K))

/-- The `x = 1`, `z = 0` intersection as an actual affine scheme. -/
abbrev orderTwentyFiveCanonicalZXIntersectionScheme : Scheme :=
  Spec (.of (OrderTwentyFiveCanonicalZXIntersectionRing K))

/-! ## Algebra-valued points -/

/-- A root of a polynomial after extension to a `K`-algebra. -/
def OrderTwentyFiveCanonicalRootSolution (p : Polynomial K)
    (A : Type v) [CommRing A] [Algebra K A] :=
  {y : A // Polynomial.eval₂ (algebraMap K A) y p = 0}

variable {K}
variable (A : Type v) [CommRing A] [Algebra K A]

/-- A residual root evaluates its `AdjoinRoot` coordinate algebra. -/
def orderTwentyFiveCanonicalRootSolutionToAlgHom (p : Polynomial K)
    (y : OrderTwentyFiveCanonicalRootSolution K p A) :
    AdjoinRoot p →ₐ[K] A :=
  AdjoinRoot.liftAlgHom p (Algebra.ofId K A) y.1 (by
    change Polynomial.eval₂ (algebraMap K A) y.1 p = 0
    exact y.2)

/-- An algebra-valued point of an `AdjoinRoot` scheme recovers its residual
root. -/
def orderTwentyFiveCanonicalAlgHomToRootSolution (p : Polynomial K)
    (φ : AdjoinRoot p →ₐ[K] A) :
    OrderTwentyFiveCanonicalRootSolution K p A :=
  ⟨φ (AdjoinRoot.root p), by
    calc
      Polynomial.eval₂ (algebraMap K A) (φ (AdjoinRoot.root p)) p =
          Polynomial.eval₂
            (φ.toRingHom.comp (AdjoinRoot.of p))
            (φ (AdjoinRoot.root p)) p := by
        congr 2
        ext r
        change (algebraMap K A) r =
          φ ((algebraMap K (AdjoinRoot p)) r)
        exact (φ.commutes r).symm
      _ = φ (Polynomial.eval₂ (AdjoinRoot.of p)
          (AdjoinRoot.root p) p) := by
        exact (Polynomial.hom_eval₂ p (AdjoinRoot.of p)
          φ.toRingHom (AdjoinRoot.root p)).symm
      _ = φ 0 := congrArg φ (AdjoinRoot.eval₂_root p)
      _ = 0 := map_zero φ⟩

/-- Roots in a `K`-algebra are exactly the algebra-valued points of the
associated `AdjoinRoot` affine scheme. -/
def orderTwentyFiveCanonicalRootSolutionEquivAlgHom (p : Polynomial K) :
    OrderTwentyFiveCanonicalRootSolution K p A ≃
      (AdjoinRoot p →ₐ[K] A) where
  toFun := orderTwentyFiveCanonicalRootSolutionToAlgHom A p
  invFun := orderTwentyFiveCanonicalAlgHomToRootSolution A p
  left_inv y := by
    apply Subtype.ext
    simp [orderTwentyFiveCanonicalRootSolutionToAlgHom,
      orderTwentyFiveCanonicalAlgHomToRootSolution]
  right_inv φ := by
    apply AdjoinRoot.algHom_ext'
    · ext
    · simp [orderTwentyFiveCanonicalRootSolutionToAlgHom,
        orderTwentyFiveCanonicalAlgHomToRootSolution]

/-- Pairs on the normalized `z = 1`, `w = 0` chart. -/
def OrderTwentyFiveCanonicalWZIntersectionSolution
    (A : Type v) [CommRing A] :=
  {p : A × A // OrderTwentyFiveCanonicalOnCurve p.1 p.2 1 0}

/-- Pairs on the normalized `x = 1`, `w = 0` chart. -/
def OrderTwentyFiveCanonicalWXIntersectionSolution
    (A : Type v) [CommRing A] :=
  {p : A × A // OrderTwentyFiveCanonicalOnCurve 1 p.1 p.2 0}

/-- Pairs on the normalized `w = 1`, `z = 0` chart. -/
def OrderTwentyFiveCanonicalZWIntersectionSolution
    (A : Type v) [CommRing A] :=
  {p : A × A // OrderTwentyFiveCanonicalOnCurve p.1 p.2 0 1}

/-- Pairs on the normalized `x = 1`, `z = 0` chart. -/
def OrderTwentyFiveCanonicalZXIntersectionSolution
    (A : Type v) [CommRing A] :=
  {p : A × A // OrderTwentyFiveCanonicalOnCurve 1 p.1 0 p.2}

/-- Elimination identifies the `z = 1`, `w = 0` chart solutions with the
roots of `Y²(Y+1)`. -/
def orderTwentyFiveCanonicalWZSolutionEquivRoot :
    OrderTwentyFiveCanonicalWZIntersectionSolution A ≃
      OrderTwentyFiveCanonicalRootSolution K
        (orderTwentyFiveCanonicalWZIntersectionEquation K) A where
  toFun p := ⟨p.1.2, by
    have h := (orderTwentyFiveCanonical_w_zChart_schemeLocus
      p.1.1 p.1.2).mp p.2
    simpa [orderTwentyFiveCanonicalWZIntersectionEquation,
      Polynomial.eval₂_at_apply] using h.2⟩
  invFun y := ⟨(y.1 ^ 2 + y.1, y.1),
    (orderTwentyFiveCanonical_w_zChart_schemeLocus
      (y.1 ^ 2 + y.1) y.1).mpr ⟨rfl, by
        simpa [orderTwentyFiveCanonicalWZIntersectionEquation,
          Polynomial.eval₂_at_apply] using y.2⟩⟩
  left_inv p := by
    rcases p with ⟨⟨x, y⟩, hp⟩
    apply Subtype.ext
    apply Prod.ext
    · exact ((orderTwentyFiveCanonical_w_zChart_schemeLocus x y).mp hp).1.symm
    · rfl
  right_inv y := by
    apply Subtype.ext
    rfl

/-- Elimination identifies the `x = 1`, `w = 0` chart solutions with the
roots of `Y³`. -/
def orderTwentyFiveCanonicalWXSolutionEquivRoot :
    OrderTwentyFiveCanonicalWXIntersectionSolution A ≃
      OrderTwentyFiveCanonicalRootSolution K
        (orderTwentyFiveCanonicalWXIntersectionEquation K) A where
  toFun p := ⟨p.1.1, by
    have h := (orderTwentyFiveCanonical_w_xChart_schemeLocus
      p.1.1 p.1.2).mp p.2
    simpa [orderTwentyFiveCanonicalWXIntersectionEquation,
      Polynomial.eval₂_at_apply] using h.2⟩
  invFun y := ⟨(y.1, y.1 ^ 2),
    (orderTwentyFiveCanonical_w_xChart_schemeLocus
      y.1 (y.1 ^ 2)).mpr ⟨rfl, by
        simpa [orderTwentyFiveCanonicalWXIntersectionEquation,
          Polynomial.eval₂_at_apply] using y.2⟩⟩
  left_inv p := by
    rcases p with ⟨⟨y, z⟩, hp⟩
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact ((orderTwentyFiveCanonical_w_xChart_schemeLocus y z).mp hp).1.symm
  right_inv y := by
    apply Subtype.ext
    rfl

/-- Elimination identifies the `w = 1`, `z = 0` chart solutions with the
roots of `Y³(Y-1)`. -/
def orderTwentyFiveCanonicalZWSolutionEquivRoot :
    OrderTwentyFiveCanonicalZWIntersectionSolution A ≃
      OrderTwentyFiveCanonicalRootSolution K
        (orderTwentyFiveCanonicalZWIntersectionEquation K) A where
  toFun p := ⟨p.1.2, by
    have h := (orderTwentyFiveCanonical_z_wChart_schemeLocus
      p.1.1 p.1.2).mp p.2
    simpa [orderTwentyFiveCanonicalZWIntersectionEquation,
      Polynomial.eval₂_at_apply] using h.2⟩
  invFun y := ⟨(y.1 ^ 2, y.1),
    (orderTwentyFiveCanonical_z_wChart_schemeLocus
      (y.1 ^ 2) y.1).mpr ⟨rfl, by
        simpa [orderTwentyFiveCanonicalZWIntersectionEquation,
          Polynomial.eval₂_at_apply] using y.2⟩⟩
  left_inv p := by
    rcases p with ⟨⟨x, y⟩, hp⟩
    apply Subtype.ext
    apply Prod.ext
    · exact ((orderTwentyFiveCanonical_z_wChart_schemeLocus x y).mp hp).1.symm
    · rfl
  right_inv y := by
    apply Subtype.ext
    rfl

/-- Elimination identifies the `x = 1`, `z = 0` chart solutions with the
roots of `Y²(Y-1)`. -/
def orderTwentyFiveCanonicalZXSolutionEquivRoot :
    OrderTwentyFiveCanonicalZXIntersectionSolution A ≃
      OrderTwentyFiveCanonicalRootSolution K
        (orderTwentyFiveCanonicalZXIntersectionEquation K) A where
  toFun p := ⟨p.1.1, by
    have h := (orderTwentyFiveCanonical_z_xChart_schemeLocus
      p.1.1 p.1.2).mp p.2
    simpa [orderTwentyFiveCanonicalZXIntersectionEquation,
      Polynomial.eval₂_at_apply] using h.2⟩
  invFun y := ⟨(y.1, y.1 ^ 2),
    (orderTwentyFiveCanonical_z_xChart_schemeLocus
      y.1 (y.1 ^ 2)).mpr ⟨rfl, by
        simpa [orderTwentyFiveCanonicalZXIntersectionEquation,
          Polynomial.eval₂_at_apply] using y.2⟩⟩
  left_inv p := by
    rcases p with ⟨⟨y, w⟩, hp⟩
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact ((orderTwentyFiveCanonical_z_xChart_schemeLocus y w).mp hp).1.symm
  right_inv y := by
    apply Subtype.ext
    rfl

/-- The `z = 1`, `w = 0` canonical intersection solutions are precisely the
algebra-valued points of their residual affine scheme. -/
def orderTwentyFiveCanonicalWZSolutionEquivAlgHom :
    OrderTwentyFiveCanonicalWZIntersectionSolution A ≃
      (OrderTwentyFiveCanonicalWZIntersectionRing K →ₐ[K] A) :=
  (orderTwentyFiveCanonicalWZSolutionEquivRoot A).trans
    (orderTwentyFiveCanonicalRootSolutionEquivAlgHom A
      (orderTwentyFiveCanonicalWZIntersectionEquation K))

/-- The `x = 1`, `w = 0` canonical intersection solutions are precisely the
algebra-valued points of their residual affine scheme. -/
def orderTwentyFiveCanonicalWXSolutionEquivAlgHom :
    OrderTwentyFiveCanonicalWXIntersectionSolution A ≃
      (OrderTwentyFiveCanonicalWXIntersectionRing K →ₐ[K] A) :=
  (orderTwentyFiveCanonicalWXSolutionEquivRoot A).trans
    (orderTwentyFiveCanonicalRootSolutionEquivAlgHom A
      (orderTwentyFiveCanonicalWXIntersectionEquation K))

/-- The `w = 1`, `z = 0` canonical intersection solutions are precisely the
algebra-valued points of their residual affine scheme. -/
def orderTwentyFiveCanonicalZWSolutionEquivAlgHom :
    OrderTwentyFiveCanonicalZWIntersectionSolution A ≃
      (OrderTwentyFiveCanonicalZWIntersectionRing K →ₐ[K] A) :=
  (orderTwentyFiveCanonicalZWSolutionEquivRoot A).trans
    (orderTwentyFiveCanonicalRootSolutionEquivAlgHom A
      (orderTwentyFiveCanonicalZWIntersectionEquation K))

/-- The `x = 1`, `z = 0` canonical intersection solutions are precisely the
algebra-valued points of their residual affine scheme. -/
def orderTwentyFiveCanonicalZXSolutionEquivAlgHom :
    OrderTwentyFiveCanonicalZXIntersectionSolution A ≃
      (OrderTwentyFiveCanonicalZXIntersectionRing K →ₐ[K] A) :=
  (orderTwentyFiveCanonicalZXSolutionEquivRoot A).trans
    (orderTwentyFiveCanonicalRootSolutionEquivAlgHom A
      (orderTwentyFiveCanonicalZXIntersectionEquation K))

/-! ## Checked scheme lengths -/

private theorem adjoinRoot_finrank_eq_natDegree
    {K : Type*} [Field K] (p : Polynomial K) (hp : p ≠ 0) :
    Module.finrank K (AdjoinRoot p) = p.natDegree := by
  rw [(AdjoinRoot.powerBasis hp).finrank,
    AdjoinRoot.powerBasis_dim hp]

/-- The `z = 1`, `w = 0` residual scheme has total length three. -/
theorem orderTwentyFiveCanonicalWZIntersectionRing_finrank
    {K : Type*} [Field K] :
    Module.finrank K (OrderTwentyFiveCanonicalWZIntersectionRing K) = 3 := by
  have hmonic :
      (orderTwentyFiveCanonicalWZIntersectionEquation K).Monic := by
    rw [orderTwentyFiveCanonicalWZIntersectionEquation]
    exact (Polynomial.monic_X.pow 2).mul
      (Polynomial.monic_X_add_C 1)
  rw [adjoinRoot_finrank_eq_natDegree _ hmonic.ne_zero,
    orderTwentyFiveCanonicalWZIntersectionEquation,
    (Polynomial.monic_X.pow 2).natDegree_mul
      (Polynomial.monic_X_add_C 1),
    Polynomial.natDegree_pow, Polynomial.natDegree_X,
    Polynomial.natDegree_X_add_C]

/-- The `x = 1`, `w = 0` residual scheme has total length three. -/
theorem orderTwentyFiveCanonicalWXIntersectionRing_finrank
    {K : Type*} [Field K] :
    Module.finrank K (OrderTwentyFiveCanonicalWXIntersectionRing K) = 3 := by
  have hmonic :
      (orderTwentyFiveCanonicalWXIntersectionEquation K).Monic := by
    rw [orderTwentyFiveCanonicalWXIntersectionEquation]
    exact Polynomial.monic_X.pow 3
  rw [adjoinRoot_finrank_eq_natDegree _ hmonic.ne_zero,
    orderTwentyFiveCanonicalWXIntersectionEquation,
    Polynomial.natDegree_pow, Polynomial.natDegree_X]

/-- The `w = 1`, `z = 0` residual scheme has total length four. -/
theorem orderTwentyFiveCanonicalZWIntersectionRing_finrank
    {K : Type*} [Field K] :
    Module.finrank K (OrderTwentyFiveCanonicalZWIntersectionRing K) = 4 := by
  have hmonic :
      (orderTwentyFiveCanonicalZWIntersectionEquation K).Monic := by
    rw [orderTwentyFiveCanonicalZWIntersectionEquation]
    exact (Polynomial.monic_X.pow 3).mul
      (Polynomial.monic_X_sub_C 1)
  rw [adjoinRoot_finrank_eq_natDegree _ hmonic.ne_zero,
    orderTwentyFiveCanonicalZWIntersectionEquation,
    (Polynomial.monic_X.pow 3).natDegree_mul
      (Polynomial.monic_X_sub_C 1),
    Polynomial.natDegree_pow, Polynomial.natDegree_X,
    Polynomial.natDegree_X_sub_C]

/-- The `x = 1`, `z = 0` residual scheme has total length three. -/
theorem orderTwentyFiveCanonicalZXIntersectionRing_finrank
    {K : Type*} [Field K] :
    Module.finrank K (OrderTwentyFiveCanonicalZXIntersectionRing K) = 3 := by
  have hmonic :
      (orderTwentyFiveCanonicalZXIntersectionEquation K).Monic := by
    rw [orderTwentyFiveCanonicalZXIntersectionEquation]
    exact (Polynomial.monic_X.pow 2).mul
      (Polynomial.monic_X_sub_C 1)
  rw [adjoinRoot_finrank_eq_natDegree _ hmonic.ne_zero,
    orderTwentyFiveCanonicalZXIntersectionEquation,
    (Polynomial.monic_X.pow 2).natDegree_mul
      (Polynomial.monic_X_sub_C 1),
    Polynomial.natDegree_pow, Polynomial.natDegree_X,
    Polynomial.natDegree_X_sub_C]

/-- Named downstream package: all four chart solution functors are represented
by the displayed residual affine schemes over every commutative base and
target algebra. -/
theorem orderTwentyFiveCanonical_hyperplaneChartScheme_pointEquivalences :
    Function.Bijective
        (orderTwentyFiveCanonicalWZSolutionEquivAlgHom (K := K) A) ∧
      Function.Bijective
        (orderTwentyFiveCanonicalWXSolutionEquivAlgHom (K := K) A) ∧
      Function.Bijective
        (orderTwentyFiveCanonicalZWSolutionEquivAlgHom (K := K) A) ∧
      Function.Bijective
        (orderTwentyFiveCanonicalZXSolutionEquivAlgHom (K := K) A) := by
  exact ⟨Equiv.bijective _, Equiv.bijective _, Equiv.bijective _,
    Equiv.bijective _⟩

end MazurTorsion.Kubert
