/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedAffineChart
import MazurTorsion.AlgebraicGeometry.Jacobian.RelativeAffineLinePower
import MazurTorsion.AlgebraicGeometry.Jacobian.AssignedTupleMonicCoordinates

/-!
# Block-monic coordinates on a geometric divisor chart

The ordered affine-coordinate power at a geometric divisor is canonically
`Spec` of the root-coordinate polynomial ring.  This identification
intertwines its geometric-support stabilizer action with permutation of the
polynomial variables.  Comparing the categorical quotient constructed from
affine orbit neighbourhoods with the affine invariant-ring quotient gives a
canonical isomorphism from the geometric coordinate quotient to a polynomial
scheme of blockwise monic coefficients.

The final commutative squares attach these explicit coefficients to both the
affine occurrence-base quotient and the actual selected-component curve
quotient.  The named downstream consumer is `PointedIncidenceDescent`, where
the coefficient chart is compared with the universal monic incidence ideal.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.GeometricBlockMonicChart

open MazurTorsion.AlgebraicGeometry.Jacobian
open AssignedTupleMonicCoordinates
open FiniteSupportEtaleCoordinates
open GeometricAssignedAffineChart
open RelativeAffineLinePower
open SmoothCurveEtaleCoordinate

variable (K : Type u) [Field K]
variable (C : Over (Spec (.of K)))
variable [SmoothOfRelativeDimension 1 C.hom]
variable (d : ℕ)
variable (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)

abbrev baseRing := Γ(Spec (.of K), ⊤)

/-- Coefficient variables grouped by geometric support point and occurrence
inside that support block. -/
abbrev blockMonicIndex :=
  monicIndex d (geometricDistinctSupportCard K C d z)
    (geometricPointSupportIndex K C d z)

/-- The affine space of blockwise monic coefficients. -/
def blockMonicCoefficientSpace : Scheme.{u} :=
  Spec (.of (MvPolynomial (blockMonicIndex K C d z) (baseRing K)))

/-- Ordered affine coordinates are the spectrum of the root-coordinate
polynomial ring. -/
def coordinatePowerSchemeIsoPolynomial :
    coordinatePower K d ≅ Spec (.of (MvPolynomial (Fin d) (baseRing K))) := by
  change (linePower (baseRing K) (Fin d)).left ≅ _
  exact linePowerSchemeIsoPolynomial (baseRing K) (Fin d)

local instance : MulAction (Equiv.Perm (Fin d))
    (Fin d → Fin (geometricDistinctSupportCard K C d z)) :=
  SplitFiniteSymmetricQuotient.tuplePermutationAction d
    (Fin (geometricDistinctSupportCard K C d z))

/-- The geometric support stabilizer permutes the polynomial root
variables. -/
@[instance_reducible]
def polynomialRootAction :
    MulSemiringAction (geometricAssignedStabilizer K C d z)
      (MvPolynomial (Fin d) (baseRing K)) :=
  stabilizerRootAction (baseRing K) d
    (geometricDistinctSupportCard K C d z)
    (geometricPointSupportIndex K C d z)

/-- Scheme action induced contravariantly by permutation of the root
variables. -/
def polynomialAction :
    SchemeAction (geometricAssignedStabilizer K C d z)
      (Spec (.of (MvPolynomial (Fin d) (baseRing K)))) := by
  letI := polynomialRootAction K C d z
  exact SchemeAction.spec _ _

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- The ordered-coordinate polynomial presentation is equivariant. -/
theorem coordinatePowerSchemeIsoPolynomial_equivariant
    (g : geometricAssignedStabilizer K C d z) :
    (coordinateAction K C d z).hom g ≫
        (coordinatePowerSchemeIsoPolynomial K d).hom =
      (coordinatePowerSchemeIsoPolynomial K d).hom ≫
        (polynomialAction K C d z).hom g := by
  letI := polynomialRootAction K C d z
  change
    (PermutationPower.action (Spec (.of (baseRing K))) (Fin d)
        (lineOver (baseRing K))).hom g.1 ≫
      (linePowerSchemeIsoPolynomial (baseRing K) (Fin d)).hom =
    (linePowerSchemeIsoPolynomial (baseRing K) (Fin d)).hom ≫
      polynomialPermutationSpec (baseRing K) (Fin d) g.1
  exact linePowerSchemeIsoPolynomial_permutation (baseRing K) (Fin d) g.1

/-- The root-coordinate ring fixed by the geometric support stabilizer. -/
abbrev invariantRing :=
  letI := polynomialRootAction K C d z
  letI := stabilizerRootSMulCommClass (baseRing K) d
    (geometricDistinctSupportCard K C d z)
    (geometricPointSupportIndex K C d z)
  FixedPoints.subalgebra (baseRing K)
    (MvPolynomial (Fin d) (baseRing K))
    (geometricAssignedStabilizer K C d z)

/-- The explicit affine invariant-ring quotient. -/
def invariantQuotient : Scheme.{u} :=
  Spec (.of (invariantRing K C d z))

/-- Projection from ordered polynomial roots to the affine invariant-ring
quotient. -/
def polynomialInvariantπ :
    Spec (.of (MvPolynomial (Fin d) (baseRing K))) ⟶
      invariantQuotient K C d z := by
  letI := polynomialRootAction K C d z
  letI := stabilizerRootSMulCommClass (baseRing K) d
    (geometricDistinctSupportCard K C d z)
    (geometricPointSupportIndex K C d z)
  exact invariantsπ (geometricAssignedStabilizer K C d z)
    (MvPolynomial (Fin d) (baseRing K)) (baseRing K)

/-- Transport the affine invariant projection back to the geometric ordered
coordinate power. -/
def coordinatePowerToInvariantQuotient :
    coordinatePower K d ⟶ invariantQuotient K C d z :=
  (coordinatePowerSchemeIsoPolynomial K d).hom ≫
    polynomialInvariantπ K C d z

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- The transported affine invariant projection is constant on geometric
support-stabilizer orbits. -/
theorem coordinatePowerToInvariantQuotient_invariant
    (g : geometricAssignedStabilizer K C d z) :
    (coordinateAction K C d z).hom g ≫
        coordinatePowerToInvariantQuotient K C d z =
      coordinatePowerToInvariantQuotient K C d z := by
  letI := polynomialRootAction K C d z
  letI := stabilizerRootSMulCommClass (baseRing K) d
    (geometricDistinctSupportCard K C d z)
    (geometricPointSupportIndex K C d z)
  let E := coordinatePowerSchemeIsoPolynomial K d
  let π := polynomialInvariantπ K C d z
  calc
    (coordinateAction K C d z).hom g ≫
          coordinatePowerToInvariantQuotient K C d z =
        ((coordinateAction K C d z).hom g ≫ E.hom) ≫ π := by
      rfl
    _ = (E.hom ≫ (polynomialAction K C d z).hom g) ≫ π :=
      congrArg (fun q ↦ q ≫ π)
        (coordinatePowerSchemeIsoPolynomial_equivariant K C d z g)
    _ = E.hom ≫ ((polynomialAction K C d z).hom g ≫ π) :=
      Category.assoc _ _ _
    _ = E.hom ≫ π := by
      apply congrArg (fun q ↦ E.hom ≫ q)
      exact specSMul_invariantsπ
        (geometricAssignedStabilizer K C d z)
        (MvPolynomial (Fin d) (baseRing K)) (baseRing K) g
    _ = coordinatePowerToInvariantQuotient K C d z := rfl

/-- Descend the explicit invariant projection through Mazur's geometric
finite-group quotient. -/
def coordinateQuotientToInvariantQuotient :
    coordinateQuotient K C d z ⟶ invariantQuotient K C d z :=
  FiniteGroupQuotient.descendedMap (coordinateAction K C d z)
    (coordinateAction_hasAffineOrbit K C d z)
    (coordinatePowerToInvariantQuotient K C d z)
    (coordinatePowerToInvariantQuotient_invariant K C d z)

/- Defining square for the map from the geometric quotient to the explicit
affine invariant quotient. -/
omit [SmoothOfRelativeDimension 1 C.hom] in
@[reassoc]
theorem coordinateQuotientπ_comp_coordinateQuotientToInvariantQuotient :
    coordinateQuotientπ K C d z ≫
        coordinateQuotientToInvariantQuotient K C d z =
      coordinatePowerToInvariantQuotient K C d z :=
  FiniteGroupQuotient.quotientπ_comp_descendedMap
    (coordinateAction K C d z)
    (coordinateAction_hasAffineOrbit K C d z)
    (coordinatePowerToInvariantQuotient K C d z)
    (coordinatePowerToInvariantQuotient_invariant K C d z)

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- The inverse polynomial presentation is also equivariant. -/
theorem coordinatePowerSchemeIsoPolynomial_inv_equivariant
    (g : geometricAssignedStabilizer K C d z) :
    (polynomialAction K C d z).hom g ≫
        (coordinatePowerSchemeIsoPolynomial K d).inv =
      (coordinatePowerSchemeIsoPolynomial K d).inv ≫
        (coordinateAction K C d z).hom g := by
  apply (cancel_mono (coordinatePowerSchemeIsoPolynomial K d).hom).mp
  simp only [Category.assoc]
  rw [← Category.assoc,
    coordinatePowerSchemeIsoPolynomial_equivariant]
  simp

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- The geometric quotient projection, transported to polynomial roots, is
invariant. -/
theorem polynomialToCoordinateQuotient_invariant
    (g : geometricAssignedStabilizer K C d z) :
    (polynomialAction K C d z).hom g ≫
        ((coordinatePowerSchemeIsoPolynomial K d).inv ≫
          coordinateQuotientπ K C d z) =
      (coordinatePowerSchemeIsoPolynomial K d).inv ≫
        coordinateQuotientπ K C d z := by
  rw [← Category.assoc,
    coordinatePowerSchemeIsoPolynomial_inv_equivariant,
    Category.assoc]
  exact congrArg
    (fun q ↦ (coordinatePowerSchemeIsoPolynomial K d).inv ≫ q)
    (FiniteGroupQuotient.hom_quotientπ (coordinateAction K C d z)
      (coordinateAction_hasAffineOrbit K C d z) g)

/-- Descend the transported geometric quotient projection through the affine
invariant-ring quotient. -/
def invariantQuotientToCoordinateQuotient :
    invariantQuotient K C d z ⟶ coordinateQuotient K C d z := by
  letI := polynomialRootAction K C d z
  letI := stabilizerRootSMulCommClass (baseRing K) d
    (geometricDistinctSupportCard K C d z)
    (geometricPointSupportIndex K C d z)
  exact Classical.choose
    (existsUnique_invariantsπ_lift
      (geometricAssignedStabilizer K C d z)
      (MvPolynomial (Fin d) (baseRing K)) (baseRing K)
      ((coordinatePowerSchemeIsoPolynomial K d).inv ≫
        coordinateQuotientπ K C d z)
      (polynomialToCoordinateQuotient_invariant K C d z))

/- Defining square for the map from the affine invariant quotient back to
the geometric quotient. -/
omit [SmoothOfRelativeDimension 1 C.hom] in
@[reassoc]
theorem polynomialInvariantπ_comp_invariantQuotientToCoordinateQuotient :
    polynomialInvariantπ K C d z ≫
        invariantQuotientToCoordinateQuotient K C d z =
      (coordinatePowerSchemeIsoPolynomial K d).inv ≫
        coordinateQuotientπ K C d z := by
  letI := polynomialRootAction K C d z
  letI := stabilizerRootSMulCommClass (baseRing K) d
    (geometricDistinctSupportCard K C d z)
    (geometricPointSupportIndex K C d z)
  exact (Classical.choose_spec
    (existsUnique_invariantsπ_lift
      (geometricAssignedStabilizer K C d z)
      (MvPolynomial (Fin d) (baseRing K)) (baseRing K)
      ((coordinatePowerSchemeIsoPolynomial K d).inv ≫
        coordinateQuotientπ K C d z)
      (polynomialToCoordinateQuotient_invariant K C d z))).1

/-- Mazur's geometric coordinate quotient is canonically the spectrum of the
fixed root-coordinate ring. -/
def coordinateQuotientIsoInvariantQuotient :
    coordinateQuotient K C d z ≅ invariantQuotient K C d z where
  hom := coordinateQuotientToInvariantQuotient K C d z
  inv := invariantQuotientToCoordinateQuotient K C d z
  hom_inv_id := by
    letI : Epi (coordinateQuotientπ K C d z) :=
      FiniteGroupQuotient.epi_quotientπ (coordinateAction K C d z)
        (coordinateAction_hasAffineOrbit K C d z)
    apply (cancel_epi (coordinateQuotientπ K C d z)).mp
    calc
      coordinateQuotientπ K C d z ≫
            (coordinateQuotientToInvariantQuotient K C d z ≫
              invariantQuotientToCoordinateQuotient K C d z) =
          (coordinateQuotientπ K C d z ≫
            coordinateQuotientToInvariantQuotient K C d z) ≫
              invariantQuotientToCoordinateQuotient K C d z :=
        (Category.assoc _ _ _).symm
      _ = coordinatePowerToInvariantQuotient K C d z ≫
          invariantQuotientToCoordinateQuotient K C d z := by
        rw [coordinateQuotientπ_comp_coordinateQuotientToInvariantQuotient]
      _ = ((coordinatePowerSchemeIsoPolynomial K d).hom ≫
            polynomialInvariantπ K C d z) ≫
          invariantQuotientToCoordinateQuotient K C d z := rfl
      _ = (coordinatePowerSchemeIsoPolynomial K d).hom ≫
          (polynomialInvariantπ K C d z ≫
            invariantQuotientToCoordinateQuotient K C d z) :=
        Category.assoc _ _ _
      _ = (coordinatePowerSchemeIsoPolynomial K d).hom ≫
          ((coordinatePowerSchemeIsoPolynomial K d).inv ≫
            coordinateQuotientπ K C d z) := by
        rw [polynomialInvariantπ_comp_invariantQuotientToCoordinateQuotient]
      _ = coordinateQuotientπ K C d z := by simp
      _ = coordinateQuotientπ K C d z ≫
          𝟙 (coordinateQuotient K C d z) := by simp
  inv_hom_id := by
    letI := polynomialRootAction K C d z
    letI := stabilizerRootSMulCommClass (baseRing K) d
      (geometricDistinctSupportCard K C d z)
      (geometricPointSupportIndex K C d z)
    apply invariantsπ_hom_ext
      (geometricAssignedStabilizer K C d z)
      (MvPolynomial (Fin d) (baseRing K)) (baseRing K)
    change polynomialInvariantπ K C d z ≫
        (invariantQuotientToCoordinateQuotient K C d z ≫
          coordinateQuotientToInvariantQuotient K C d z) =
      polynomialInvariantπ K C d z ≫
        𝟙 (invariantQuotient K C d z)
    calc
      polynomialInvariantπ K C d z ≫
            (invariantQuotientToCoordinateQuotient K C d z ≫
              coordinateQuotientToInvariantQuotient K C d z) =
          (polynomialInvariantπ K C d z ≫
            invariantQuotientToCoordinateQuotient K C d z) ≫
              coordinateQuotientToInvariantQuotient K C d z :=
        (Category.assoc _ _ _).symm
      _ = ((coordinatePowerSchemeIsoPolynomial K d).inv ≫
            coordinateQuotientπ K C d z) ≫
          coordinateQuotientToInvariantQuotient K C d z := by
        rw [polynomialInvariantπ_comp_invariantQuotientToCoordinateQuotient]
      _ = (coordinatePowerSchemeIsoPolynomial K d).inv ≫
          (coordinateQuotientπ K C d z ≫
            coordinateQuotientToInvariantQuotient K C d z) :=
        Category.assoc _ _ _
      _ = (coordinatePowerSchemeIsoPolynomial K d).inv ≫
          coordinatePowerToInvariantQuotient K C d z := by
        rw [coordinateQuotientπ_comp_coordinateQuotientToInvariantQuotient]
      _ = (coordinatePowerSchemeIsoPolynomial K d).inv ≫
          ((coordinatePowerSchemeIsoPolynomial K d).hom ≫
            polynomialInvariantπ K C d z) := rfl
      _ = polynomialInvariantπ K C d z := by simp
      _ = polynomialInvariantπ K C d z ≫
          𝟙 (invariantQuotient K C d z) := by simp

/-- The geometric block quotient is canonically the affine space of monic
coefficients, one monic polynomial for every geometric support block. -/
def coordinateQuotientIsoMonicCoefficientSpace :
    coordinateQuotient K C d z ≅ blockMonicCoefficientSpace K C d z := by
  letI := polynomialRootAction K C d z
  letI := stabilizerRootSMulCommClass (baseRing K) d
    (geometricDistinctSupportCard K C d z)
    (geometricPointSupportIndex K C d z)
  exact coordinateQuotientIsoInvariantQuotient K C d z ≪≫
    monicCoefficientInvariantSchemeIso (baseRing K) d
      (geometricDistinctSupportCard K C d z)
      (geometricPointSupportIndex K C d z)

/-- The blockwise Vieta map from ordered affine roots to monic
coefficients. -/
def coordinatePowerToMonicCoefficientSpace :
    coordinatePower K d ⟶ blockMonicCoefficientSpace K C d z :=
  coordinatePowerToInvariantQuotient K C d z ≫
    (monicCoefficientInvariantSchemeIso (baseRing K) d
      (geometricDistinctSupportCard K C d z)
      (geometricPointSupportIndex K C d z)).hom

/- The coordinate quotient isomorphism identifies its projection with the
blockwise Vieta map. -/
omit [SmoothOfRelativeDimension 1 C.hom] in
@[reassoc]
theorem coordinateQuotientπ_comp_monicCoefficientIso :
    coordinateQuotientπ K C d z ≫
        (coordinateQuotientIsoMonicCoefficientSpace K C d z).hom =
      coordinatePowerToMonicCoefficientSpace K C d z := by
  change coordinateQuotientπ K C d z ≫
      (coordinateQuotientToInvariantQuotient K C d z ≫ _) = _
  rw [← Category.assoc,
    coordinateQuotientπ_comp_coordinateQuotientToInvariantQuotient]
  rfl

/-- Monic coefficient map on the affine occurrence-base quotient. -/
def baseQuotientToMonicCoefficientSpace :
    quotient K C d z ⟶ blockMonicCoefficientSpace K C d z :=
  quotientToCoordinateQuotient K C d z ≫
    (coordinateQuotientIsoMonicCoefficientSpace K C d z).hom

/-- Defining square for monic coefficients on the occurrence-base quotient. -/
@[reassoc]
theorem quotientπ_comp_baseQuotientToMonicCoefficientSpace :
    quotientπ K C d z ≫ baseQuotientToMonicCoefficientSpace K C d z =
      (toCoordinatePower K C d z).left ≫
        coordinatePowerToMonicCoefficientSpace K C d z := by
  rw [baseQuotientToMonicCoefficientSpace, ← Category.assoc,
    quotientπ_comp_quotientToCoordinateQuotient,
    Category.assoc, coordinateQuotientπ_comp_monicCoefficientIso]

/-- Monic coefficient map on the selected-component curve quotient. -/
def componentQuotientToMonicCoefficientSpace :
    componentQuotient K C d z ⟶ blockMonicCoefficientSpace K C d z :=
  componentQuotientToCoordinateQuotient K C d z ≫
    (coordinateQuotientIsoMonicCoefficientSpace K C d z).hom

/-- Defining square for monic coefficients on the selected-component curve
quotient. -/
@[reassoc]
theorem componentQuotientπ_comp_componentQuotientToMonicCoefficientSpace :
    componentQuotientπ K C d z ≫
        componentQuotientToMonicCoefficientSpace K C d z =
      (componentToCoordinatePower K C d z).left ≫
        coordinatePowerToMonicCoefficientSpace K C d z := by
  rw [componentQuotientToMonicCoefficientSpace, ← Category.assoc,
    componentQuotientπ_comp_componentQuotientToCoordinateQuotient,
    Category.assoc, coordinateQuotientπ_comp_monicCoefficientIso]

/-- The selected-component coefficient map factors through the affine-base
quotient. -/
@[reassoc]
theorem componentQuotientToBaseQuotient_comp_baseQuotientToMonicCoefficientSpace :
    componentQuotientToBaseQuotient K C d z ≫
        baseQuotientToMonicCoefficientSpace K C d z =
      componentQuotientToMonicCoefficientSpace K C d z := by
  rw [baseQuotientToMonicCoefficientSpace,
    componentQuotientToMonicCoefficientSpace, ← Category.assoc,
    componentQuotientToBaseQuotient_comp_quotientToCoordinateQuotient]

end MazurTorsion.AlgebraicGeometry.Jacobian.GeometricBlockMonicChart
