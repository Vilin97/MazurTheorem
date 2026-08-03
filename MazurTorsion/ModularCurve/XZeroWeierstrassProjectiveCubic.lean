/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.ReducedClosedSubscheme
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

The final declarations construct the canonical forward map from Mathlib's
coordinate points to scheme-valued points and consume it in the finite-flat
`X₀(N)` path.  They isolate the remaining group-law compatibility and
surjectivity proofs without assuming an unrelated abelian variety: the
underlying scheme is definitionally the cubic constructed here.

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

/-- Evaluation at a nonzero homogeneous coordinate triple, as a map into the global sections of
`Spec K`. -/
noncomputable def coordinateRingHom (P : Fin 3 → K) :
    MvPolynomial (Fin 3) K →+* Γ(Spec (.of K), ⊤) :=
  (Scheme.ΓSpecIso (.of K)).inv.hom.comp (MvPolynomial.eval P)

/-- A nonzero coordinate triple maps the irrelevant ideal to the unit ideal, as required to
construct its point of projective space. -/
theorem irrelevant_map_eq_top (P : Fin 3 → K) (hP : P ≠ 0) :
    Ideal.map (coordinateRingHom P)
      (HomogeneousIdeal.irrelevant (homogeneousPieces K)).toIdeal = ⊤ := by
  obtain ⟨i, hi⟩ : ∃ i, P i ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hP
    exact ⟨i, hi⟩
  have hXi : MvPolynomial.X i ∈
      (HomogeneousIdeal.irrelevant (homogeneousPieces K)).toIdeal :=
    HomogeneousIdeal.mem_irrelevant_of_mem (homogeneousPieces K) (by omega)
      (MvPolynomial.isHomogeneous_X K i)
  refine (Ideal.map (coordinateRingHom P)
    (HomogeneousIdeal.irrelevant (homogeneousPieces K)).toIdeal).eq_top_of_isUnit_mem
      (x := coordinateRingHom P (MvPolynomial.X i)) ?_ ?_
  · exact Ideal.mem_map_of_mem (coordinateRingHom P) hXi
  · simpa [coordinateRingHom, MvPolynomial.eval] using
      hi.isUnit.map (Scheme.ΓSpecIso (.of K)).inv.hom

/-- The point of projective two-space represented by a nonzero coordinate triple. -/
noncomputable def ambientPoint (P : Fin 3 → K) (hP : P ≠ 0) :
    Spec (.of K) ⟶ projectivePlane K :=
  Proj.fromOfGlobalSections (homogeneousPieces K) (coordinateRingHom P)
    (irrelevant_map_eq_top P hP)

/-- A homogeneous polynomial belongs to the projective prime at the closed point represented by
`P` exactly when it evaluates to zero at `P`. -/
theorem mem_ambientPoint_closedPoint_iff (P : Fin 3 → K) (hP : P ≠ 0)
    (q : MvPolynomial (Fin 3) K) {n : ℕ} (hn : 0 < n)
    (hq : q ∈ homogeneousPieces K n) :
    q ∈ (ambientPoint P hP (IsLocalRing.closedPoint K)).asHomogeneousIdeal ↔
      MvPolynomial.eval P q = 0 := by
  rw [← not_iff_not]
  change IsLocalRing.closedPoint K ∈ ambientPoint P hP ⁻¹ᵁ
      Proj.basicOpen (homogeneousPieces K) q ↔
    MvPolynomial.eval P q ≠ 0
  rw [ambientPoint, Proj.fromOfGlobalSections_preimage_basicOpen
    (homogeneousPieces K) (coordinateRingHom P)
    (irrelevant_map_eq_top P hP) hn hq]
  by_cases heq : MvPolynomial.eval P q = 0
  · have hf : coordinateRingHom P q = 0 := by
      simp [coordinateRingHom, heq]
    rw [hf, Scheme.basicOpen_zero]
    constructor
    · intro h
      exact (TopologicalSpace.Opens.mem_bot.mp h).elim
    · intro h
      exact (h heq).elim
  · have hf : IsUnit (coordinateRingHom P q) := by
      exact (isUnit_iff_ne_zero.mpr heq).map (Scheme.ΓSpecIso (.of K)).inv.hom
    rw [(Spec (.of K)).basicOpen_of_isUnit hf]
    constructor
    · intro
      exact heq
    · intro
      exact Set.mem_univ _

/-- Equal projective-space morphisms represented by nonzero triples have the same homogeneous
vanishing equations. -/
theorem eval_zero_iff_of_ambientPoint_eq
    (P Q : Fin 3 → K) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (heq : ambientPoint P hP = ambientPoint Q hQ)
    (q : MvPolynomial (Fin 3) K) {n : ℕ} (hn : 0 < n)
    (hq : q ∈ homogeneousPieces K n) :
    MvPolynomial.eval P q = 0 ↔ MvPolynomial.eval Q q = 0 := by
  rw [← mem_ambientPoint_closedPoint_iff P hP q hn hq,
    ← mem_ambientPoint_closedPoint_iff Q hQ q hn hq]
  rw [congrArg (fun f => f (IsLocalRing.closedPoint K)) heq]

/-- A nonsingular projective Weierstrass representative is not the zero triple. -/
theorem nonsingular_ne_zero (W : WeierstrassCurve K) (P : Fin 3 → K)
    (hP : W.toProjective.Nonsingular P) : P ≠ 0 := by
  intro h
  subst P
  simp [WeierstrassCurve.Projective.nonsingular_iff] at hP

/-- The projective-space point represented by a nonsingular Weierstrass triple belongs to the
cubic's projective zero locus. -/
theorem ambientPoint_mem_carrier (W : WeierstrassCurve K) (P : Fin 3 → K)
    (hP : W.toProjective.Nonsingular P) (s : Spec (.of K)) :
    ambientPoint P (nonsingular_ne_zero W P hP) s ∈ carrier W := by
  let x : ProjectiveSpectrum (homogeneousPieces K) :=
    ambientPoint P (nonsingular_ne_zero W P hP) s
  change x ∈ ProjectiveSpectrum.zeroLocus (homogeneousPieces K)
    {W.toProjective.polynomial}
  rw [ProjectiveSpectrum.mem_zeroLocus]
  simp only [Set.singleton_subset_iff, SetLike.mem_coe]
  by_contra hxq
  have hxbo : x ∈ Proj.basicOpen (homogeneousPieces K) W.toProjective.polynomial := hxq
  change ambientPoint P (nonsingular_ne_zero W P hP) s ∈
    Proj.basicOpen (homogeneousPieces K) W.toProjective.polynomial at hxbo
  have hs : s ∈ ambientPoint P (nonsingular_ne_zero W P hP) ⁻¹ᵁ
      Proj.basicOpen (homogeneousPieces K) W.toProjective.polynomial := hxbo
  rw [ambientPoint, Proj.fromOfGlobalSections_preimage_basicOpen
    (homogeneousPieces K) (coordinateRingHom P)
    (irrelevant_map_eq_top P (nonsingular_ne_zero W P hP))
    (by omega) (polynomial_mem_degree_three W)] at hs
  have hfq : coordinateRingHom P W.toProjective.polynomial = 0 := by
    change (Scheme.ΓSpecIso (.of K)).inv
      (MvPolynomial.eval P W.toProjective.polynomial) = 0
    rw [hP.1, map_zero]
  rw [hfq, Scheme.basicOpen_zero] at hs
  simp at hs

/-- The whole range of the point represented by a nonsingular Weierstrass triple lies in the
cubic's projective zero locus. -/
theorem ambientPoint_range_subset_carrier (W : WeierstrassCurve K)
    (P : Fin 3 → K) (hP : W.toProjective.Nonsingular P) :
    Set.range (ambientPoint P (nonsingular_ne_zero W P hP)) ⊆ carrier W := by
  rintro _ ⟨s, rfl⟩
  exact ambientPoint_mem_carrier W P hP s

/-- A nonsingular homogeneous coordinate representative defines a scheme-valued point of the
reduced Weierstrass cubic. -/
noncomputable def pointOfNonsingularRepresentative (W : WeierstrassCurve K)
    (P : Fin 3 → K) (hP : W.toProjective.Nonsingular P) :
    Spec (.of K) ⟶ scheme W :=
  MazurTorsion.AlgebraicGeometry.ReducedClosedSubscheme.lift
    (ambientPoint P (nonsingular_ne_zero W P hP)) (closedCarrier W)
    (ambientPoint_range_subset_carrier W P hP)

@[simp]
theorem pointOfNonsingularRepresentative_comp_inclusion (W : WeierstrassCurve K)
    (P : Fin 3 → K) (hP : W.toProjective.Nonsingular P) :
    pointOfNonsingularRepresentative W P hP ≫ inclusion W =
      ambientPoint P (nonsingular_ne_zero W P hP) :=
  MazurTorsion.AlgebraicGeometry.ReducedClosedSubscheme.lift_comp_subschemeι _ _ _

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

/-- A homogeneous coordinate point constructed by evaluation is a morphism over `Spec K`. -/
theorem ambientPoint_comp_projectivePlaneStructureMap
    (P : Fin 3 → K) (hP : P ≠ 0) :
    ambientPoint P hP ≫ projectivePlaneStructureMap K = 𝟙 _ := by
  rw [ambientPoint, projectivePlaneStructureMap, ← Category.assoc,
    Proj.fromOfGlobalSections_toSpecZero]
  rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, ← Spec.map_comp,
    ← Spec.map_id]
  congr 1
  ext r
  change (Scheme.ΓSpecIso (.of K)).hom
    (coordinateRingHom P ((algebraMap K (homogeneousPieces K 0)) r)) = r
  simp [coordinateRingHom]

/-- The structure morphism of the reduced projective Weierstrass cubic. -/
noncomputable def structureMap (W : WeierstrassCurve K) : scheme W ⟶ Spec (.of K) :=
  inclusion W ≫ projectivePlaneStructureMap K

instance structureMap_isProper (W : WeierstrassCurve K) : IsProper (structureMap W) := by
  dsimp only [structureMap]
  infer_instance

@[simp]
theorem pointOfNonsingularRepresentative_comp_structureMap
    (W : WeierstrassCurve K) (P : Fin 3 → K)
    (hP : W.toProjective.Nonsingular P) :
    pointOfNonsingularRepresentative W P hP ≫ structureMap W = 𝟙 _ := by
  rw [structureMap, ← Category.assoc,
    pointOfNonsingularRepresentative_comp_inclusion,
    ambientPoint_comp_projectivePlaneStructureMap]

/-- The concrete Weierstrass cubic as an object over `Spec K`. -/
noncomputable def toOver (W : WeierstrassCurve K) : Over (Spec (.of K)) :=
  Over.mk (structureMap W)

instance toOver_hom_isProper (W : WeierstrassCurve K) : IsProper (toOver W).hom := by
  change IsProper (structureMap W)
  infer_instance

/-- A nonsingular coordinate representative defines an honest `K`-point of the cubic as a
morphism in the slice over `Spec K`. -/
noncomputable def pointOverOfNonsingularRepresentative
    (W : WeierstrassCurve K) (P : Fin 3 → K)
    (hP : W.toProjective.Nonsingular P) :
    AffineCommGroupScheme.testObject (R := K) K ⟶ toOver W :=
  Over.homMk (pointOfNonsingularRepresentative W P hP) <| by
    change pointOfNonsingularRepresentative W P hP ≫ structureMap W =
      Spec.map (CommRingCat.ofHom (algebraMap K K))
    rw [pointOfNonsingularRepresentative_comp_structureMap]
    simp

/-- Canonical affine-coordinate points as morphisms from `Spec K` to the concrete cubic. -/
noncomputable def affinePointMorphism (W : WeierstrassCurve K) :
    W.toAffine.Point → (Spec (.of K) ⟶ scheme W)
  | .zero => pointOfNonsingularRepresentative W ![0, 1, 0]
      W.toProjective.nonsingular_zero
  | .some x y h => pointOfNonsingularRepresentative W ![x, y, 1]
      ((W.toProjective.nonsingular_some x y).mpr h)

@[simp]
theorem affinePointMorphism_zero (W : WeierstrassCurve K) :
    affinePointMorphism W .zero =
      pointOfNonsingularRepresentative W ![0, 1, 0]
        W.toProjective.nonsingular_zero :=
  rfl

@[simp]
theorem affinePointMorphism_some (W : WeierstrassCurve K) (x y : K)
    (h : W.toAffine.Nonsingular x y) :
    affinePointMorphism W (.some x y h) =
      pointOfNonsingularRepresentative W ![x, y, 1]
        ((W.toProjective.nonsingular_some x y).mpr h) :=
  rfl

/-- Equality of projective-space points represented in the affine chart `Z = 1` forces equality
of both affine coordinates. -/
theorem ambientPoint_some_coordinates_eq (W : WeierstrassCurve K)
    (x y x' y' : K)
    (h : W.toAffine.Nonsingular x y) (h' : W.toAffine.Nonsingular x' y')
    (heq : ambientPoint ![x, y, 1]
        (nonsingular_ne_zero W ![x, y, 1]
          ((W.toProjective.nonsingular_some x y).mpr h)) =
      ambientPoint ![x', y', 1]
        (nonsingular_ne_zero W ![x', y', 1]
          ((W.toProjective.nonsingular_some x' y').mpr h'))) :
    x = x' ∧ y = y' := by
  let qx : MvPolynomial (Fin 3) K :=
    MvPolynomial.X 0 - MvPolynomial.C x * MvPolynomial.X 2
  let qy : MvPolynomial (Fin 3) K :=
    MvPolynomial.X 1 - MvPolynomial.C y * MvPolynomial.X 2
  have hqx : qx ∈ homogeneousPieces K 1 :=
    (MvPolynomial.isHomogeneous_X K 0).sub
      ((MvPolynomial.isHomogeneous_X K 2).C_mul x)
  have hqy : qy ∈ homogeneousPieces K 1 :=
    (MvPolynomial.isHomogeneous_X K 1).sub
      ((MvPolynomial.isHomogeneous_X K 2).C_mul y)
  have hxzero : MvPolynomial.eval ![x, y, 1] qx = 0 := by
    simp [qx]
  have hyzero : MvPolynomial.eval ![x, y, 1] qy = 0 := by
    simp [qy]
  have hxzero' : MvPolynomial.eval ![x', y', 1] qx = 0 :=
    (eval_zero_iff_of_ambientPoint_eq _ _ _ _ heq qx (by omega) hqx).mp hxzero
  have hyzero' : MvPolynomial.eval ![x', y', 1] qy = 0 :=
    (eval_zero_iff_of_ambientPoint_eq _ _ _ _ heq qy (by omega) hqy).mp hyzero
  constructor
  · exact (sub_eq_zero.mp (by simpa [qx] using hxzero')).symm
  · exact (sub_eq_zero.mp (by simpa [qy] using hyzero')).symm

/-- The point at infinity and every point in the affine chart `Z = 1` define distinct
projective-space morphisms. -/
theorem ambientPoint_zero_ne_some (W : WeierstrassCurve K)
    (x y : K) (h : W.toAffine.Nonsingular x y) :
    ambientPoint ![0, 1, 0]
        (nonsingular_ne_zero W ![0, 1, 0] W.toProjective.nonsingular_zero) ≠
      ambientPoint ![x, y, 1]
        (nonsingular_ne_zero W ![x, y, 1]
          ((W.toProjective.nonsingular_some x y).mpr h)) := by
  intro heq
  let q : MvPolynomial (Fin 3) K := MvPolynomial.X 2
  have hq : q ∈ homogeneousPieces K 1 :=
    MvPolynomial.isHomogeneous_X K 2
  have hzero : MvPolynomial.eval ![0, 1, 0] q = 0 := by
    simp [q]
  have hone : MvPolynomial.eval ![x, y, 1] q = 0 :=
    (eval_zero_iff_of_ambientPoint_eq _ _ _ _ heq q (by omega) hq).mp hzero
  simp [q] at hone

/-- The canonical map from Mathlib's affine Weierstrass points to morphisms into the concrete
cubic is injective. -/
theorem affinePointMorphism_injective (W : WeierstrassCurve K) :
    Function.Injective (affinePointMorphism W) := by
  intro P Q heq
  cases P with
  | zero =>
      cases Q with
      | zero => rfl
      | some x' y' h' =>
          have hamb := congrArg (fun f => f ≫ inclusion W) heq
          simp only [affinePointMorphism_zero, affinePointMorphism_some,
            pointOfNonsingularRepresentative_comp_inclusion] at hamb
          exact (ambientPoint_zero_ne_some W x' y' h' hamb).elim
  | some x y h =>
      cases Q with
      | zero =>
          have hamb := congrArg (fun f => f ≫ inclusion W) heq
          simp only [affinePointMorphism_zero, affinePointMorphism_some,
            pointOfNonsingularRepresentative_comp_inclusion] at hamb
          exact (ambientPoint_zero_ne_some W x y h hamb.symm).elim
      | some x' y' h' =>
          have hamb := congrArg (fun f => f ≫ inclusion W) heq
          simp only [affinePointMorphism_some,
            pointOfNonsingularRepresentative_comp_inclusion] at hamb
          obtain ⟨rfl, rfl⟩ :=
            ambientPoint_some_coordinates_eq W x y x' y' h h' hamb
          rfl

/-- A Mathlib projective Weierstrass point as a morphism to the concrete cubic.  Passing through
the checked affine normal form avoids making a choice of homogeneous representative. -/
noncomputable def projectivePointMorphism (W : WeierstrassCurve K)
    (P : W.toProjective.Point) : Spec (.of K) ⟶ scheme W :=
  affinePointMorphism W P.toAffineLift

/-- The canonical map from Mathlib's projective Weierstrass points to morphisms into the concrete
cubic is injective. -/
theorem projectivePointMorphism_injective
    (W : WeierstrassCurve K) : Function.Injective (projectivePointMorphism W) := by
  classical
  intro P Q heq
  apply (WeierstrassCurve.Projective.Point.toAffineAddEquiv W).injective
  change P.toAffineLift = Q.toAffineLift
  apply affinePointMorphism_injective W
  simpa only [projectivePointMorphism] using heq

/-- Canonical affine-coordinate points as `K`-points in the slice category. -/
noncomputable def affinePointOverMorphism (W : WeierstrassCurve K) :
    W.toAffine.Point → (AffineCommGroupScheme.testObject (R := K) K ⟶ toOver W)
  | .zero => pointOverOfNonsingularRepresentative W ![0, 1, 0]
      W.toProjective.nonsingular_zero
  | .some x y h => pointOverOfNonsingularRepresentative W ![x, y, 1]
      ((W.toProjective.nonsingular_some x y).mpr h)

/-- A Mathlib projective Weierstrass point as an honest `K`-point of the concrete cubic. -/
noncomputable def projectivePointOverMorphism (W : WeierstrassCurve K)
    (P : W.toProjective.Point) :
    AffineCommGroupScheme.testObject (R := K) K ⟶ toOver W :=
  affinePointOverMorphism W P.toAffineLift

@[simp]
theorem projectivePointOverMorphism_left (W : WeierstrassCurve K)
    (P : W.toProjective.Point) :
    (projectivePointOverMorphism W P).left = projectivePointMorphism W P := by
  rw [projectivePointOverMorphism, projectivePointMorphism]
  cases P.toAffineLift <;> rfl

/-- The canonical map from Mathlib's projective points to `K`-points in the slice category is
injective. -/
theorem projectivePointOverMorphism_injective
    (W : WeierstrassCurve K) : Function.Injective (projectivePointOverMorphism W) := by
  intro P Q heq
  apply projectivePointMorphism_injective W
  have hleft := congrArg (fun f => f.left) heq
  rw [projectivePointOverMorphism_left,
    projectivePointOverMorphism_left] at hleft
  exact hleft

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

/-- The canonical forward map from Mathlib's projective coordinate points to the rational points
of the abelian variety carried by the concrete cubic.  Proving that this map preserves the group
law and is surjective remains the point-comparison obligation; injectivity is proved below. -/
noncomputable def projectivePointToAbelianVarietyRationalPoint
    (W : WeierstrassCurve K)
    [GrpObj (toOver W)] [GeometricallyIntegral (toOver W).hom]
    (P : W.toProjective.Point) :
    AbelianVarietyRationalPoint (toAbelianVariety W) :=
  projectivePointOverMorphism W P

/-- The canonical forward map to abelian-variety rational points is injective; this is already a
coordinate consequence and does not require compatibility with the scheme group law. -/
theorem projectivePointToAbelianVarietyRationalPoint_injective
    (W : WeierstrassCurve K)
    [GrpObj (toOver W)] [GeometricallyIntegral (toOver W).hom] :
    Function.Injective (projectivePointToAbelianVarietyRationalPoint W) :=
  projectivePointOverMorphism_injective W

variable [DecidableEq K] {N : ℕ} [NeZero N]
  (W : WeierstrassCurve K) [W.IsElliptic]
  [GrpObj (toOver W)] [GeometricallyIntegral (toOver W).hom]

/-- Package proofs that the canonical coordinate-to-scheme point map preserves zero and addition
as a monoid homomorphism from the multiplicative spelling of the coordinate group. -/
noncomputable def canonicalProjectivePointMonoidHom
    (hzero : projectivePointToAbelianVarietyRationalPoint W 0 = 1)
    (hadd : ∀ P Q : W.toProjective.Point,
      projectivePointToAbelianVarietyRationalPoint W (P + Q) =
        projectivePointToAbelianVarietyRationalPoint W P *
          projectivePointToAbelianVarietyRationalPoint W Q) :
    Multiplicative W.toProjective.Point →*
      AbelianVarietyRationalPoint (toAbelianVariety W) where
  toFun P := projectivePointToAbelianVarietyRationalPoint W P.toAdd
  map_one' := hzero
  map_mul' P Q := hadd P.toAdd Q.toAdd

/-- Once the canonical point map is known to preserve the group law and to be surjective, it is the
required multiplicative equivalence: injectivity was proved directly from coordinates above. -/
noncomputable def canonicalProjectivePointEquiv
    (hzero : projectivePointToAbelianVarietyRationalPoint W 0 = 1)
    (hadd : ∀ P Q : W.toProjective.Point,
      projectivePointToAbelianVarietyRationalPoint W (P + Q) =
        projectivePointToAbelianVarietyRationalPoint W P *
          projectivePointToAbelianVarietyRationalPoint W Q)
    (hsurj : Function.Surjective
      (fun P : Multiplicative W.toProjective.Point =>
        projectivePointToAbelianVarietyRationalPoint W P.toAdd)) :
    Multiplicative W.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety W) :=
  MulEquiv.ofBijective (canonicalProjectivePointMonoidHom W hzero hadd)
    ⟨projectivePointToAbelianVarietyRationalPoint_injective W, hsurj⟩

omit [DecidableEq K] [W.IsElliptic] in
@[simp]
theorem canonicalProjectivePointEquiv_apply
    (hzero : projectivePointToAbelianVarietyRationalPoint W 0 = 1)
    (hadd : ∀ P Q : W.toProjective.Point,
      projectivePointToAbelianVarietyRationalPoint W (P + Q) =
        projectivePointToAbelianVarietyRationalPoint W P *
          projectivePointToAbelianVarietyRationalPoint W Q)
    (hsurj : Function.Surjective
      (fun P : Multiplicative W.toProjective.Point =>
        projectivePointToAbelianVarietyRationalPoint W P.toAdd))
    (P : Multiplicative W.toProjective.Point) :
    canonicalProjectivePointEquiv W hzero hadd hsurj P =
      projectivePointToAbelianVarietyRationalPoint W P.toAdd :=
  rfl

/-- A comparison of Mathlib's projective coordinate points with the rational points of the
concrete cubic supplies the existing abelian-variety bridge.  Unlike an arbitrary supplied
abelian variety, the underlying scheme here is definitionally the reduced homogeneous cubic
constructed above. -/
noncomputable def toAbelianVarietyComparison
    (e : Multiplicative W.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety W)) :
    WeierstrassAbelianVarietyComparison W :=
  WeierstrassAbelianVarietyComparison.ofProjectivePointEquiv W (toAbelianVariety W) e

/-- Canonical comparison consumer: the remaining group-law and surjectivity proofs are attached to
the explicit coordinate-to-scheme point map constructed above. -/
noncomputable def toAbelianVarietyComparisonOfCanonicalPointMap
    (hzero : projectivePointToAbelianVarietyRationalPoint W 0 = 1)
    (hadd : ∀ P Q : W.toProjective.Point,
      projectivePointToAbelianVarietyRationalPoint W (P + Q) =
        projectivePointToAbelianVarietyRationalPoint W P *
          projectivePointToAbelianVarietyRationalPoint W Q)
    (hsurj : Function.Surjective
      (fun P : Multiplicative W.toProjective.Point =>
        projectivePointToAbelianVarietyRationalPoint W P.toAdd)) :
    WeierstrassAbelianVarietyComparison W :=
  toAbelianVarietyComparison W (canonicalProjectivePointEquiv W hzero hadd hsurj)

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

/-- Finite-flat consumer of the canonical coordinate-to-scheme point map: after its group-law and
surjectivity obligations are proved, exact coordinate torsion produces the split `Gamma₀(N)` datum
on this concrete cubic. -/
noncomputable def splitGammaZeroDatumOfCanonicalProjectiveCubic
    (hzero : projectivePointToAbelianVarietyRationalPoint W 0 = 1)
    (hadd : ∀ P Q : W.toProjective.Point,
      projectivePointToAbelianVarietyRationalPoint W (P + Q) =
        projectivePointToAbelianVarietyRationalPoint W P *
          projectivePointToAbelianVarietyRationalPoint W Q)
    (hsurj : Function.Surjective
      (fun Q : Multiplicative W.toProjective.Point =>
        projectivePointToAbelianVarietyRationalPoint W Q.toAdd))
    (P : W.toAffine.Point) (hP : addOrderOf P = N) :
    WeierstrassGroupSchemeInterface.SplitGammaZeroDatum
      (N := N) W
        (toAbelianVarietyComparisonOfCanonicalPointMap W hzero hadd hsurj).toGroupSchemeInterface :=
  splitGammaZeroDatumOfProjectiveCubic W
    (canonicalProjectivePointEquiv W hzero hadd hsurj) P hP

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

omit [W.IsElliptic] in
/-- The canonical-point-map finite-flat consumer produces a subgroup of constant order `N`. -/
theorem splitGammaZeroDatumOfCanonicalProjectiveCubic_hasConstantOrder
    (hzero : projectivePointToAbelianVarietyRationalPoint W 0 = 1)
    (hadd : ∀ P Q : W.toProjective.Point,
      projectivePointToAbelianVarietyRationalPoint W (P + Q) =
        projectivePointToAbelianVarietyRationalPoint W P *
          projectivePointToAbelianVarietyRationalPoint W Q)
    (hsurj : Function.Surjective
      (fun Q : Multiplicative W.toProjective.Point =>
        projectivePointToAbelianVarietyRationalPoint W Q.toAdd))
    (P : W.toAffine.Point) (hP : addOrderOf P = N) :
    _root_.AlgebraicGeometry.FiniteFlatCommGroupScheme.HasConstantOrder
      (splitGammaZeroDatumOfCanonicalProjectiveCubic W hzero hadd hsurj P hP).subgroup.carrier N :=
  splitGammaZeroDatumOfProjectiveCubic_hasConstantOrder W
    (canonicalProjectivePointEquiv W hzero hadd hsurj) P hP

end WeierstrassProjectiveCubic

end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
