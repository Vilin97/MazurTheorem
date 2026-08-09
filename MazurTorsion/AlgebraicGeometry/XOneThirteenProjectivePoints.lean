/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.XOneThirteenProjectiveCurve

/-!
# Rational points on the two-chart order-thirteen curve

This file realizes the six evident rational points of the hyperelliptic
model as literal morphisms into the glued scheme.  Four points lie in the
ordinary chart, at `x = 0, -1`; the remaining two are the normalized points
at infinity, `z = 0, w = ±1`, in the reciprocal chart.

The section identities are checked against the glued structure morphism.
Thus these are geometric basepoints on the actual scheme, not merely pairs
of rational coordinates.
-/

noncomputable section

namespace MazurTorsion.XOneThirteenProjectivePoints

open Polynomial
open _root_.AlgebraicGeometry
open CategoryTheory

universe u

/-! ## Points of the reciprocal chart -/

variable (K : Type u) [CommRing K]

/-- Elementary solutions of the reciprocal equation over a `K`-algebra. -/
def ReciprocalSolution (A : Type*) [CommRing A] [Algebra K A] :=
  {p : A × A //
    p.2 ^ 2 = aeval p.1
      (XOneThirteenProjectiveCurve.reciprocalPolynomial K)}

variable {K}
variable (A : Type*) [CommRing A] [Algebra K A]

/-- A reciprocal solution evaluates the reciprocal coordinate algebra. -/
noncomputable def reciprocalSolutionToAlgHom
    (p : ReciprocalSolution K A) :
    XOneThirteenProjectiveCurve.ReciprocalRing K →ₐ[K] A :=
  AdjoinRoot.liftAlgHom
    (XOneThirteenProjectiveCurve.reciprocalEquation K)
    (aeval p.1.1) p.1.2 (by
      simpa [XOneThirteenProjectiveCurve.reciprocalEquation,
        Polynomial.aeval_def] using
        sub_eq_zero.mpr p.property)

@[simp]
theorem reciprocalSolutionToAlgHom_z
    (p : ReciprocalSolution K A) :
    reciprocalSolutionToAlgHom A p
        (XOneThirteenProjectiveCurve.zCoordinate K) =
      p.1.1 := by
  simp [reciprocalSolutionToAlgHom,
    XOneThirteenProjectiveCurve.zCoordinate]

@[simp]
theorem reciprocalSolutionToAlgHom_w
    (p : ReciprocalSolution K A) :
    reciprocalSolutionToAlgHom A p
        (XOneThirteenProjectiveCurve.wCoordinate K) =
      p.1.2 := by
  simp [reciprocalSolutionToAlgHom,
    XOneThirteenProjectiveCurve.wCoordinate]

/-- An algebra point of the reciprocal chart recovers its two
coordinates. -/
noncomputable def algHomToReciprocalSolution
    (φ : XOneThirteenProjectiveCurve.ReciprocalRing K →ₐ[K] A) :
    ReciprocalSolution K A :=
  ⟨(φ (XOneThirteenProjectiveCurve.zCoordinate K),
      φ (XOneThirteenProjectiveCurve.wCoordinate K)), by
    rw [← map_pow, XOneThirteenProjectiveCurve.wCoordinate_sq]
    simp [XOneThirteenProjectiveCurve.zCoordinate,
      Polynomial.aeval_def]⟩

/-- The reciprocal equation and the reciprocal chart's algebra-valued
points are canonically equivalent. -/
noncomputable def reciprocalSolutionEquivAlgHom :
    ReciprocalSolution K A ≃
      (XOneThirteenProjectiveCurve.ReciprocalRing K →ₐ[K] A) where
  toFun := reciprocalSolutionToAlgHom A
  invFun := algHomToReciprocalSolution A
  left_inv p := by
    apply Subtype.ext
    ext <;> simp [algHomToReciprocalSolution]
  right_inv φ := by
    apply AdjoinRoot.algHom_ext'
    · apply Polynomial.algHom_ext
      simp [reciprocalSolutionToAlgHom,
        algHomToReciprocalSolution,
        XOneThirteenProjectiveCurve.zCoordinate]
    · simp [reciprocalSolutionToAlgHom,
        algHomToReciprocalSolution,
        XOneThirteenProjectiveCurve.wCoordinate]

variable (K : Type u) [CommRing K]

/-- A reciprocal-chart point over a ring with a unique endomorphism. -/
noncomputable def reciprocalSolutionToSchemePoint
    [Subsingleton (K →+* K)] (p : ReciprocalSolution K K) :
    Spec (.of K) ⟶ XOneThirteenProjectiveCurve.reciprocalScheme K :=
  Spec.map (CommRingCat.ofHom
    (reciprocalSolutionToAlgHom K p).toRingHom)

private noncomputable def reciprocalRingHomToAlgHom
    [Subsingleton (K →+* K)]
    (φ : XOneThirteenProjectiveCurve.ReciprocalRing K →+* K) :
    XOneThirteenProjectiveCurve.ReciprocalRing K →ₐ[K] K where
  __ := φ
  commutes' r := by
    change (φ.comp (algebraMap K
      (XOneThirteenProjectiveCurve.ReciprocalRing K))) r =
        (RingHom.id K) r
    exact DFunLike.congr_fun (Subsingleton.elim _ _) r

private noncomputable def reciprocalAlgHomEquivRingHom
    [Subsingleton (K →+* K)] :
    (XOneThirteenProjectiveCurve.ReciprocalRing K →ₐ[K] K) ≃
      (XOneThirteenProjectiveCurve.ReciprocalRing K →+* K) where
  toFun φ := φ.toRingHom
  invFun := reciprocalRingHomToAlgHom K
  left_inv φ := by
    apply AlgHom.coe_ringHom_injective
    rfl
  right_inv φ := rfl

private noncomputable def reciprocalRingHomEquivCommRingCatHom :
    (XOneThirteenProjectiveCurve.ReciprocalRing K →+* K) ≃
      (CommRingCat.of
          (XOneThirteenProjectiveCurve.ReciprocalRing K) ⟶
        CommRingCat.of K) where
  toFun := CommRingCat.ofHom
  invFun φ := φ.hom
  left_inv φ := rfl
  right_inv φ := by
    apply CommRingCat.hom_ext
    rfl

/-- Over a ring with a unique endomorphism, reciprocal solutions are
literal points of the reciprocal affine chart. -/
noncomputable def reciprocalSolutionEquivSchemePoint
    [Subsingleton (K →+* K)] :
    ReciprocalSolution K K ≃
      (Spec (.of K) ⟶
        XOneThirteenProjectiveCurve.reciprocalScheme K) :=
  (reciprocalSolutionEquivAlgHom K).trans <|
    (reciprocalAlgHomEquivRingHom K).trans <|
      (reciprocalRingHomEquivCommRingCatHom K).trans <|
        (Spec.homEquiv
          (R := .of (XOneThirteenProjectiveCurve.ReciprocalRing K))
          (S := .of K)).symm

@[simp, reassoc]
theorem reciprocalSolutionToSchemePoint_toBase
    [Subsingleton (K →+* K)] (p : ReciprocalSolution K K) :
    reciprocalSolutionToSchemePoint K p ≫
        XOneThirteenProjectiveCurve.reciprocalChartToBase K =
      𝟙 (Spec (.of K)) := by
  unfold reciprocalSolutionToSchemePoint
    XOneThirteenProjectiveCurve.reciprocalChartToBase
    XOneThirteenProjectiveCurve.reciprocalScheme
  rw [← Spec.map_comp, ← Spec.map_id, Spec.map_inj]
  apply CommRingCat.hom_ext
  exact Subsingleton.elim _ _

@[simp, reassoc]
theorem ordinarySolutionToSchemePoint_toBase
    [Subsingleton (K →+* K)]
    (p : XOneThirteenAffineCurve.Solution K K) :
    XOneThirteenAffineCurve.solutionEquivSchemePoint K p ≫
        XOneThirteenProjectiveCurve.ordinaryChartToBase K =
      𝟙 (Spec (.of K)) := by
  apply (Spec.homEquiv (R := .of K) (S := .of K)).injective
  apply CommRingCat.hom_ext
  exact Subsingleton.elim _ _

/-! ## The six rational points -/

/-- The first normalized point at infinity, `(z,w) = (0,1)`. -/
def infinityPlusSolution : ReciprocalSolution ℚ ℚ :=
  ⟨(0, 1), by
    norm_num [XOneThirteenProjectiveCurve.reciprocalPolynomial]⟩

/-- The second normalized point at infinity, `(z,w) = (0,-1)`. -/
def infinityMinusSolution : ReciprocalSolution ℚ ℚ :=
  ⟨(0, -1), by
    norm_num [XOneThirteenProjectiveCurve.reciprocalPolynomial]⟩

/-- The ordinary point `(x,y) = (0,1)`. -/
def zeroPlusSolution : XOneThirteenAffineCurve.Solution ℚ ℚ :=
  ⟨(0, 1), by
    norm_num [XOneThirteenAffineCurve.sexticPolynomial]⟩

/-- The ordinary point `(x,y) = (0,-1)`. -/
def zeroMinusSolution : XOneThirteenAffineCurve.Solution ℚ ℚ :=
  ⟨(0, -1), by
    norm_num [XOneThirteenAffineCurve.sexticPolynomial]⟩

/-- The ordinary point `(x,y) = (-1,1)`. -/
def negOnePlusSolution : XOneThirteenAffineCurve.Solution ℚ ℚ :=
  ⟨(-1, 1), by
    norm_num [XOneThirteenAffineCurve.sexticPolynomial]⟩

/-- The ordinary point `(x,y) = (-1,-1)`. -/
def negOneMinusSolution : XOneThirteenAffineCurve.Solution ℚ ℚ :=
  ⟨(-1, -1), by
    norm_num [XOneThirteenAffineCurve.sexticPolynomial]⟩

/-- A rational point of the actual glued curve. -/
abbrev RationalPoint :=
  Spec (.of ℚ) ⟶ XOneThirteenProjectiveCurve.curveScheme ℚ

/-- The point at infinity with reciprocal ordinate `1`. -/
noncomputable def infinityPlus : RationalPoint :=
  reciprocalSolutionToSchemePoint ℚ infinityPlusSolution ≫
    XOneThirteenProjectiveCurve.reciprocalChartMap ℚ

/-- The point at infinity with reciprocal ordinate `-1`. -/
noncomputable def infinityMinus : RationalPoint :=
  reciprocalSolutionToSchemePoint ℚ infinityMinusSolution ≫
    XOneThirteenProjectiveCurve.reciprocalChartMap ℚ

/-- The ordinary point `(0,1)` on the glued curve. -/
noncomputable def zeroPlus : RationalPoint :=
  XOneThirteenAffineCurve.solutionEquivSchemePoint ℚ zeroPlusSolution ≫
    XOneThirteenProjectiveCurve.ordinaryChartMap ℚ

/-- The ordinary point `(0,-1)` on the glued curve. -/
noncomputable def zeroMinus : RationalPoint :=
  XOneThirteenAffineCurve.solutionEquivSchemePoint ℚ zeroMinusSolution ≫
    XOneThirteenProjectiveCurve.ordinaryChartMap ℚ

/-- The ordinary point `(-1,1)` on the glued curve. -/
noncomputable def negOnePlus : RationalPoint :=
  XOneThirteenAffineCurve.solutionEquivSchemePoint ℚ negOnePlusSolution ≫
    XOneThirteenProjectiveCurve.ordinaryChartMap ℚ

/-- The ordinary point `(-1,-1)` on the glued curve. -/
noncomputable def negOneMinus : RationalPoint :=
  XOneThirteenAffineCurve.solutionEquivSchemePoint ℚ negOneMinusSolution ≫
    XOneThirteenProjectiveCurve.ordinaryChartMap ℚ

@[simp]
theorem infinityPlus_isSection :
    infinityPlus ≫ XOneThirteenProjectiveCurve.curveToBase ℚ =
      𝟙 (Spec (.of ℚ)) := by
  simp [infinityPlus, Category.assoc]

@[simp]
theorem infinityMinus_isSection :
    infinityMinus ≫ XOneThirteenProjectiveCurve.curveToBase ℚ =
      𝟙 (Spec (.of ℚ)) := by
  simp [infinityMinus, Category.assoc]

@[simp]
theorem zeroPlus_isSection :
    zeroPlus ≫ XOneThirteenProjectiveCurve.curveToBase ℚ =
      𝟙 (Spec (.of ℚ)) := by
  simp [zeroPlus, Category.assoc]

@[simp]
theorem zeroMinus_isSection :
    zeroMinus ≫ XOneThirteenProjectiveCurve.curveToBase ℚ =
      𝟙 (Spec (.of ℚ)) := by
  simp [zeroMinus, Category.assoc]

@[simp]
theorem negOnePlus_isSection :
    negOnePlus ≫ XOneThirteenProjectiveCurve.curveToBase ℚ =
      𝟙 (Spec (.of ℚ)) := by
  simp [negOnePlus, Category.assoc]

@[simp]
theorem negOneMinus_isSection :
    negOneMinus ≫ XOneThirteenProjectiveCurve.curveToBase ℚ =
      𝟙 (Spec (.of ℚ)) := by
  simp [negOneMinus, Category.assoc]

end MazurTorsion.XOneThirteenProjectivePoints
