/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassAbelianVariety
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# The projective Weierstrass cubic as a scheme

This file constructs an actual scheme over `Spec K` from Mathlib's homogeneous
Weierstrass polynomial.  It is the reduced closed subscheme of `P²_K` supported
on the polynomial's projective zero locus.  The construction includes its
closed immersion, its proper structure morphism, and a bridge to Tau Ceti's
abelian-variety package once the remaining group law and geometric integrality
are supplied.

The final declarations are real consumers in the finite-flat `X₀(N)` path.
They isolate the remaining coordinate-to-scheme comparison without assuming an
unrelated abelian variety: the underlying scheme is definitionally the cubic
constructed here.

The degree-zero and finite-type arguments specialize the exact-pinned Tau Ceti
projective-line construction from two homogeneous coordinates to three.
-/

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry
open scoped CategoryTheory.MonObj DirectSum

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli

universe u

namespace WeierstrassProjectiveCubic

variable {K : Type u} [Field K]

/-- The standard grading of the homogeneous coordinate ring of `P²_K`. -/
abbrev homogeneousPieces (K : Type u) [Field K] :=
  MvPolynomial.homogeneousSubmodule (Fin 3) K

noncomputable instance (K : Type u) [Field K] : GradedAlgebra (homogeneousPieces K) :=
  MvPolynomial.gradedAlgebra

/-- The projective plane containing a projective Weierstrass cubic. -/
abbrev projectivePlane (K : Type u) [Field K] : Scheme.{u} :=
  Proj (homogeneousPieces K)

/-- Mathlib's projective Weierstrass polynomial is homogeneous of degree three. -/
theorem polynomial_isHomogeneous (W : WeierstrassCurve K) :
    W.toProjective.polynomial.IsHomogeneous 3 := by
  let X : MvPolynomial (Fin 3) K := MvPolynomial.X 0
  let Y : MvPolynomial (Fin 3) K := MvPolynomial.X 1
  let Z : MvPolynomial (Fin 3) K := MvPolynomial.X 2
  have hX : X.IsHomogeneous 1 := MvPolynomial.isHomogeneous_X K 0
  have hY : Y.IsHomogeneous 1 := MvPolynomial.isHomogeneous_X K 1
  have hZ : Z.IsHomogeneous 1 := MvPolynomial.isHomogeneous_X K 2
  have hY2Z : (Y ^ 2 * Z).IsHomogeneous 3 := by
    simpa only [one_mul, Nat.reduceMul, Nat.reduceAdd] using (hY.pow 2).mul hZ
  have ha1XYZ : (MvPolynomial.C W.a₁ * X * Y * Z).IsHomogeneous 3 := by
    simpa only [Nat.reduceAdd] using ((hX.C_mul W.a₁).mul hY).mul hZ
  have ha3YZ2 : (MvPolynomial.C W.a₃ * Y * Z ^ 2).IsHomogeneous 3 := by
    simpa only [one_mul, Nat.reduceMul, Nat.reduceAdd] using
      (hY.C_mul W.a₃).mul (hZ.pow 2)
  have hX3 : (X ^ 3).IsHomogeneous 3 := by
    simpa only [one_mul] using hX.pow 3
  have ha2X2Z : (MvPolynomial.C W.a₂ * X ^ 2 * Z).IsHomogeneous 3 := by
    simpa only [one_mul, Nat.reduceMul, Nat.reduceAdd] using
      (hX.pow 2).C_mul W.a₂ |>.mul hZ
  have ha4XZ2 : (MvPolynomial.C W.a₄ * X * Z ^ 2).IsHomogeneous 3 := by
    simpa only [one_mul, Nat.reduceMul, Nat.reduceAdd] using
      (hX.C_mul W.a₄).mul (hZ.pow 2)
  have ha6Z3 : (MvPolynomial.C W.a₆ * Z ^ 3).IsHomogeneous 3 := by
    simpa only [one_mul] using (hZ.pow 3).C_mul W.a₆
  change (Y ^ 2 * Z + MvPolynomial.C W.a₁ * X * Y * Z +
      MvPolynomial.C W.a₃ * Y * Z ^ 2 -
      (X ^ 3 + MvPolynomial.C W.a₂ * X ^ 2 * Z +
        MvPolynomial.C W.a₄ * X * Z ^ 2 + MvPolynomial.C W.a₆ * Z ^ 3)).IsHomogeneous 3
  exact ((hY2Z.add ha1XYZ).add ha3YZ2).sub
    (((hX3.add ha2X2Z).add ha4XZ2).add ha6Z3)

theorem polynomial_mem_degree_three (W : WeierstrassCurve K) :
    W.toProjective.polynomial ∈ homogeneousPieces K 3 :=
  polynomial_isHomogeneous W

/-- The closed subset of `P²_K` cut out by the homogeneous Weierstrass equation. -/
def carrier (W : WeierstrassCurve K) : Set (projectivePlane K) :=
  ProjectiveSpectrum.zeroLocus (homogeneousPieces K) {W.toProjective.polynomial}

theorem isClosed_carrier (W : WeierstrassCurve K) : IsClosed (carrier W) :=
  ProjectiveSpectrum.isClosed_zeroLocus _ _

/-- Membership in the projective zero locus is containment of the cubic polynomial in the
corresponding homogeneous prime ideal. -/
theorem mem_zeroLocus_iff (W : WeierstrassCurve K)
    (x : ProjectiveSpectrum (homogeneousPieces K)) :
    x ∈ ProjectiveSpectrum.zeroLocus (homogeneousPieces K) {W.toProjective.polynomial} ↔
      W.toProjective.polynomial ∈
        (x.asHomogeneousIdeal : Set (MvPolynomial (Fin 3) K)) := by
  simpa only [Set.singleton_subset_iff] using
    (ProjectiveSpectrum.mem_zeroLocus (homogeneousPieces K) x
      ({W.toProjective.polynomial} : Set (MvPolynomial (Fin 3) K)))

/-- The Weierstrass cubic as a closed subset of `P²_K`. -/
def closedCarrier (W : WeierstrassCurve K) : TopologicalSpace.Closeds (projectivePlane K) :=
  ⟨carrier W, isClosed_carrier W⟩

/-- The radical ideal sheaf defining the reduced projective Weierstrass cubic. -/
def idealSheaf (W : WeierstrassCurve K) : (projectivePlane K).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (closedCarrier W)

/-- The reduced closed subscheme of `P²_K` supported on the homogeneous Weierstrass cubic. -/
abbrev scheme (W : WeierstrassCurve K) : Scheme.{u} :=
  (idealSheaf W).subscheme

/-- The vanishing-ideal construction gives the cubic its reduced induced scheme structure. -/
instance scheme_isReduced (W : WeierstrassCurve K) : IsReduced (scheme W) := by
  rw [IsReduced.iff_of_openCover (scheme W) (idealSheaf W).subschemeCover.openCover]
  intro U
  letI : _root_.IsReduced
      (Γ(projectivePlane K, U.1) ⧸ (idealSheaf W).ideal U) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (by
      change (PrimeSpectrum.vanishingIdeal _).IsRadical
      exact PrimeSpectrum.isRadical_vanishingIdeal _)
  change IsReduced (Spec (.of
    (Γ(projectivePlane K, U.1) ⧸ (idealSheaf W).ideal U)))
  infer_instance

/-- The closed immersion of the reduced projective Weierstrass cubic into `P²_K`. -/
def inclusion (W : WeierstrassCurve K) : scheme W ⟶ projectivePlane K :=
  (idealSheaf W).subschemeι

instance inclusion_isClosedImmersion (W : WeierstrassCurve K) :
    IsClosedImmersion (inclusion W) := by
  change IsClosedImmersion (idealSheaf W).subschemeι
  infer_instance

theorem range_inclusion (W : WeierstrassCurve K) :
    Set.range (inclusion W) = carrier W := by
  rw [inclusion, Scheme.IdealSheafData.range_subschemeι]
  change ↑(Scheme.IdealSheafData.vanishingIdeal (closedCarrier W)).support = carrier W
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- Constants identify `K` with the degree-zero part of `K[X,Y,Z]`. -/
noncomputable def degreeZeroRingEquiv (K : Type u) [Field K] :
    K ≃+* homogeneousPieces K 0 :=
  RingEquiv.ofBijective (algebraMap K (homogeneousPieces K 0)) <| by
    constructor
    · intro r s hrs
      exact MvPolynomial.C_injective (Fin 3) K (congrArg Subtype.val hrs)
    · intro p
      have hp : (p : MvPolynomial (Fin 3) K) ∈
          (1 : Submodule K (MvPolynomial (Fin 3) K)) := by
        simpa [homogeneousPieces, MvPolynomial.homogeneousSubmodule_zero] using p.property
      obtain ⟨r, hr⟩ := Submodule.mem_one.mp hp
      refine ⟨r, Subtype.ext ?_⟩
      exact hr

noncomputable instance (K : Type u) [Field K] :
    Algebra.FiniteType (homogeneousPieces K 0) (MvPolynomial (Fin 3) K) := by
  letI : IsScalarTower K (homogeneousPieces K 0) (MvPolynomial (Fin 3) K) :=
    IsScalarTower.of_algebraMap_eq
      (R := K) (S := homogeneousPieces K 0) (A := MvPolynomial (Fin 3) K)
      (fun r ↦ by rfl)
  exact Algebra.FiniteType.of_restrictScalars_finiteType
    K (homogeneousPieces K 0) (MvPolynomial (Fin 3) K)

/-- The structure morphism of the ambient projective plane. -/
noncomputable def projectivePlaneStructureMap (K : Type u) [Field K] :
    projectivePlane K ⟶ Spec (.of K) :=
  Proj.toSpecZero (homogeneousPieces K) ≫
    Spec.map (degreeZeroRingEquiv K).toCommRingCatIso.hom

instance projectivePlaneStructureMap_isProper (K : Type u) [Field K] :
    IsProper (projectivePlaneStructureMap K) := by
  dsimp only [projectivePlaneStructureMap]
  infer_instance

/-- The structure morphism of the reduced projective Weierstrass cubic. -/
noncomputable def structureMap (W : WeierstrassCurve K) : scheme W ⟶ Spec (.of K) :=
  inclusion W ≫ projectivePlaneStructureMap K

instance structureMap_isProper (W : WeierstrassCurve K) : IsProper (structureMap W) := by
  dsimp only [structureMap]
  infer_instance

/-- The concrete Weierstrass cubic as an object over `Spec K`. -/
noncomputable def toOver (W : WeierstrassCurve K) : Over (Spec (.of K)) :=
  Over.mk (structureMap W)

instance toOver_hom_isProper (W : WeierstrassCurve K) : IsProper (toOver W).hom := by
  change IsProper (structureMap W)
  infer_instance

/-- Once the concrete cubic carries a group-object structure and is geometrically integral,
Tau Ceti packages it as an abelian variety; properness is already proved above. -/
noncomputable def toAbelianVariety (W : WeierstrassCurve K)
    [GrpObj (toOver W)] [GeometricallyIntegral (toOver W).hom] :
    TauCeti.AlgebraicGeometry.AbelianVariety K :=
  TauCeti.AlgebraicGeometry.AbelianVariety.ofGeometricallyIntegral (toOver W)

@[simp]
theorem toAbelianVariety_toOver (W : WeierstrassCurve K)
    [GrpObj (toOver W)] [GeometricallyIntegral (toOver W).hom] :
    (toAbelianVariety W).toOver = toOver W :=
  rfl

@[simp]
theorem toAbelianVariety_toScheme (W : WeierstrassCurve K)
    [GrpObj (toOver W)] [GeometricallyIntegral (toOver W).hom] :
    (toAbelianVariety W).toScheme = scheme W :=
  rfl

variable [DecidableEq K] {N : ℕ} [NeZero N]
  (W : WeierstrassCurve K) [W.IsElliptic]
  [GrpObj (toOver W)] [GeometricallyIntegral (toOver W).hom]

/-- A comparison of Mathlib's projective coordinate points with the rational points of the
concrete cubic supplies the existing abelian-variety bridge.  Unlike an arbitrary supplied
abelian variety, the underlying scheme here is definitionally the reduced homogeneous cubic
constructed above. -/
noncomputable def toAbelianVarietyComparison
    (e : Multiplicative W.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety W)) :
    WeierstrassAbelianVarietyComparison W :=
  WeierstrassAbelianVarietyComparison.ofProjectivePointEquiv W (toAbelianVariety W) e

/-- Real finite-flat downstream consumer of the concrete cubic: once its group law,
geometric integrality, and projective-coordinate point comparison are established, a point of
exact order `N` produces the split `Gamma₀(N)` subgroup datum. -/
noncomputable def splitGammaZeroDatumOfProjectiveCubic
    (e : Multiplicative W.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety W))
    (P : W.toAffine.Point) (hP : addOrderOf P = N) :
    WeierstrassGroupSchemeInterface.SplitGammaZeroDatum
      (N := N) W (toAbelianVarietyComparison W e).toGroupSchemeInterface :=
  WeierstrassAbelianVarietyComparison.splitGammaZeroDatumOfTorsion
    W (toAbelianVarietyComparison W e) P hP

omit [W.IsElliptic] in
/-- The finite-flat subgroup produced from the concrete projective cubic has constant order
`N`; this theorem checks that the bridge reaches the scheme-theoretic consumer. -/
theorem splitGammaZeroDatumOfProjectiveCubic_hasConstantOrder
    (e : Multiplicative W.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety W))
    (P : W.toAffine.Point) (hP : addOrderOf P = N) :
    (splitGammaZeroDatumOfProjectiveCubic W e P hP).subgroup.carrier.HasConstantOrder N :=
  WeierstrassAbelianVarietyComparison.splitGammaZeroDatumOfTorsion_hasConstantOrder
    W (toAbelianVarietyComparison W e) P hP

end WeierstrassProjectiveCubic

end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
