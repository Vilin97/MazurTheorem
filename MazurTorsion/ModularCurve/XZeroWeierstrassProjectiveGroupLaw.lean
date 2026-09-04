/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassProjectiveProductGlobalAddition
import MazurTorsion.ModularCurve.XZeroWeierstrassProjectiveInfinity
import MazurTorsion.ModularCurve.XZeroWeierstrassCubicChartDensity

/-!
# The group law on the projective Weierstrass cubic

This file packages the globally glued projective addition morphism in the
slice over `Spec K` and proves its group-law equations.  The design boundary
is the concrete object `toOver W`: no pre-existing `MonObj` or `GrpObj`
structure is assumed while the equations are established.  The downstream
module `XZeroWeierstrassProjectiveAssociativity` proves the remaining
associativity equation and installs these checked morphisms as the canonical
group-object structure used by the modular-curve interfaces.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

/-! ## Operations in the slice -/

/-- The globally glued projective addition, regarded as a morphism over the
coefficient field.  This is the multiplication operation consumed by
`projectiveGrpObj` below. -/
noncomputable def projectiveAdditionOver
    (W : WeierstrassCurve K) [W.IsElliptic] :
    toOver W ⊗ toOver W ⟶ toOver W :=
  Over.homMk (projectiveAdditionMorphism W)
    (projectiveAdditionMorphism_comp_structureMap W)

@[simp]
theorem projectiveAdditionOver_left
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (projectiveAdditionOver W).left = projectiveAdditionMorphism W :=
  rfl

/-- The tensor-product structure map is the concrete projective-pair
structure map used during gluing. -/
@[simp]
theorem tensorProjectiveCubic_hom
    (W : WeierstrassCurve K) :
    (toOver W ⊗ toOver W).hom = projectivePairStructureMap W :=
  rfl

/-! ## The left unit on the dense standard chart -/

/-- Evaluate the first factor of the infinity-by-standard chart at the
origin and retain the second, universal standard-chart factor. -/
private noncomputable def leftUnitChartPairAlgHom
    (W : WeierstrassCurve K) :
    projectivePairChartCoordinateRing W (false, true) →ₐ[K]
      coveringChartCoordinateRing W true :=
  Algebra.TensorProduct.lift
    ((Algebra.ofId K (coveringChartCoordinateRing W true)).comp
      (coveringInfinityChartOriginAlgHom W))
    (AlgHom.id K (coveringChartCoordinateRing W true))
    (fun _ _ ↦ Commute.all _ _)

@[simp]
private theorem leftUnitChartPairAlgHom_firstUniversalPoint
    (W : WeierstrassCurve K) (j : Fin 3) :
    leftUnitChartPairAlgHom W
        (projectivePairChartFirstUniversalPoint W (false, true) j) =
      ![0, 1, 0] j := by
  fin_cases j <;>
    simp [leftUnitChartPairAlgHom, projectivePairChartFirstUniversalPoint,
      coveringInfinityChartOriginAlgHom_universalPoint]

@[simp]
private theorem leftUnitChartPairAlgHom_secondUniversalPoint
    (W : WeierstrassCurve K) (j : Fin 3) :
    leftUnitChartPairAlgHom W
        (projectivePairChartSecondUniversalPoint W (false, true) j) =
      coveringChartUniversalPoint W true j := by
  simp [leftUnitChartPairAlgHom, projectivePairChartSecondUniversalPoint]

private theorem leftUnitChartPairAlgHom_additionCoordinates
    (W : WeierstrassCurve K) (j : Fin 3) :
    leftUnitChartPairAlgHom W
        (projectivePairChartAdditionCoordinates W (false, true) j) =
      coveringChartUniversalPoint W true j := by
  let f := (leftUnitChartPairAlgHom W).toRingHom
  let P := projectivePairChartFirstUniversalPoint W (false, true)
  let Q := projectivePairChartSecondUniversalPoint W (false, true)
  have hmap := congrFun
    (WeierstrassCurve.Projective.map_addXYZ
      (W' := projectivePairChartMappedCurve W (false, true))
      (P := P) (Q := Q) f) j
  have hcurve :
      (projectivePairChartMappedCurve W (false, true)).map f =
        W.map (algebraMap K (coveringChartCoordinateRing W true)) := by
    rw [projectivePairChartMappedCurve, WeierstrassCurve.map_map]
    congr 1
    ext r
    exact (leftUnitChartPairAlgHom W).commutes r
  have hP : f ∘ P = (![0, 1, 0] : Fin 3 →
      coveringChartCoordinateRing W true) := by
    funext k
    exact leftUnitChartPairAlgHom_firstUniversalPoint W k
  have hQ : f ∘ Q = coveringChartUniversalPoint W true := by
    funext k
    exact leftUnitChartPairAlgHom_secondUniversalPoint W k
  change
    ((projectivePairChartMappedCurve W (false, true)).map f).toProjective.addXYZ
        (f ∘ P) (f ∘ Q) j =
      (f ∘ (projectivePairChartMappedCurve W (false, true)).toProjective.addXYZ
        P Q) j at hmap
  rw [hcurve, hP, hQ] at hmap
  have hformula :=
    WeierstrassCurve.Projective.addXYZ_of_Z_eq_zero_left
      (W' := (W.map
        (algebraMap K (coveringChartCoordinateRing W true))).toProjective)
      (P := (![0, 1, 0] : Fin 3 →
        coveringChartCoordinateRing W true))
      (Q := coveringChartUniversalPoint W true)
      (by simpa using
        (W.map (algebraMap K
          (coveringChartCoordinateRing W true))).toProjective.equation_zero)
      (by rfl)
  rw [hformula] at hmap
  have hQz : coveringChartUniversalPoint W true (2 : Fin 3) = 1 :=
    coveringChartUniversalPoint_normalized W true
  rw [Pi.smul_apply, hQz] at hmap
  simpa [P, Q, f, projectivePairChartAdditionCoordinates,
    Pi.smul_apply] using hmap.symm

private theorem leftUnitChartPairAlgHom_additionZ
    (W : WeierstrassCurve K) :
    leftUnitChartPairAlgHom W
        (projectivePairChartAdditionCoordinates W (false, true)
          (coveringCoordinate true)) = 1 := by
  rw [leftUnitChartPairAlgHom_additionCoordinates]
  exact coveringChartUniversalPoint_normalized W true

/-- The left-unit axis lands in the mixed chart's secant output-`Z` open,
because that output coordinate specializes to one. -/
private noncomputable def leftUnitChartOutputAlgHom
    (W : WeierstrassCurve K) :
    projectivePairChartAdditionOutputRing W (false, true) true →ₐ[K]
      coveringChartCoordinateRing W true :=
  IsLocalization.Away.liftAlgHom
    (projectivePairChartAdditionCoordinates W (false, true)
      (coveringCoordinate true))
    (f := leftUnitChartPairAlgHom W) (by
      rw [leftUnitChartPairAlgHom_additionZ]
      exact isUnit_one)

@[simp]
private theorem leftUnitChartOutputAlgHom_algebraMap
    (W : WeierstrassCurve K)
    (a : projectivePairChartCoordinateRing W (false, true)) :
    leftUnitChartOutputAlgHom W
        (algebraMap (projectivePairChartCoordinateRing W (false, true))
          (projectivePairChartAdditionOutputRing W (false, true) true) a) =
      leftUnitChartPairAlgHom W a := by
  simp [leftUnitChartOutputAlgHom, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]

private theorem leftUnitChartOutputAlgHom_outputPoint
    (W : WeierstrassCurve K) [W.IsElliptic] (j : Fin 3) :
    leftUnitChartOutputAlgHom W
        (projectivePairChartAdditionOutputPoint W (false, true) true j) =
      coveringChartUniversalPoint W true j := by
  rw [projectivePairChartAdditionOutputPoint, map_mul,
    leftUnitChartOutputAlgHom_algebraMap,
    leftUnitChartPairAlgHom_additionCoordinates]
  have hunit : leftUnitChartOutputAlgHom W
      (↑(projectivePairChartAdditionOutputUnit W (false, true) true) :
        projectivePairChartAdditionOutputRing W (false, true) true) = 1 := by
    unfold projectivePairChartAdditionOutputUnit
    rw [IsUnit.unit_spec]
    rw [leftUnitChartOutputAlgHom_algebraMap,
      leftUnitChartPairAlgHom_additionZ]
  have hinv : leftUnitChartOutputAlgHom W
      (↑(projectivePairChartAdditionOutputUnit W (false, true) true)⁻¹ :
        projectivePairChartAdditionOutputRing W (false, true) true) = 1 := by
    let u := projectivePairChartAdditionOutputUnit W (false, true) true
    have hu : Units.map (leftUnitChartOutputAlgHom W).toMonoidHom u = 1 := by
      apply Units.ext
      exact hunit
    have hi := congrArg Inv.inv hu
    have hiv := congrArg Units.val hi
    simpa [u] using hiv
  rw [hinv, one_mul]

private theorem leftUnitChartOutputAlgHom_comp_outputAlgHom
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (leftUnitChartOutputAlgHom W).comp
        (projectivePairChartAdditionOutputAlgHom W
          (false, true) true) =
      AlgHom.id K (coveringChartCoordinateRing W true) := by
  apply AlgHom.coe_ringHom_injective
  apply Ideal.Quotient.ringHom_ext
  apply chartRingHom_ext (K := K) (coveringCoordinate true)
  · ext a
    change leftUnitChartOutputAlgHom W
        (projectivePairChartAdditionOutputAlgHom W (false, true) true
          (coveringChartStructureRingHom W true a)) =
      coveringChartStructureRingHom W true a
    rw [← coveringChartCoordinateRing_algebraMap,
      (projectivePairChartAdditionOutputAlgHom W
        (false, true) true).commutes,
      (leftUnitChartOutputAlgHom W).commutes]
  · intro j
    change leftUnitChartOutputAlgHom W
        (projectivePairChartAdditionOutputAlgHom W (false, true) true
          (Ideal.Quotient.mk (coveringChartIdeal W true)
            (coordinateChartRatio (coveringCoordinate true) j))) = _
    rw [projectivePairChartAdditionOutputAlgHom_ratio,
      leftUnitChartOutputAlgHom_outputPoint]
    rfl

/-- The dense standard chart mapped into the infinity-by-standard pair chart
along the left-unit axis. -/
private noncomputable def leftUnitStandardChartToMixedPair
    (W : WeierstrassCurve K) :
    coveringChartScheme W true ⟶
      projectivePairChartScheme W (false, true) :=
  Spec.map (CommRingCat.ofHom (leftUnitChartPairAlgHom W).toRingHom) ≫
    (projectivePairChartIsoSpecTensor W (false, true)).inv

/-- The canonical factor of the left-unit axis through the output-`Z`
principal open. -/
private noncomputable def leftUnitStandardChartToOutputOpen
    (W : WeierstrassCurve K) :
    coveringChartScheme W true ⟶
      Spec (.of
        (projectivePairChartAdditionOutputRing W (false, true) true)) :=
  Spec.map (CommRingCat.ofHom (leftUnitChartOutputAlgHom W).toRingHom)

private theorem leftUnitStandardChartToOutputOpen_comp_open
    (W : WeierstrassCurve K) :
    leftUnitStandardChartToOutputOpen W ≫
        projectivePairChartAdditionOutputOpen W (false, true) true =
      leftUnitStandardChartToMixedPair W := by
  apply (cancel_mono
    (projectivePairChartIsoSpecTensor W (false, true)).hom).1
  rw [Category.assoc,
    projectivePairChartAdditionOutputOpen_comp_iso_hom]
  rw [leftUnitStandardChartToOutputOpen,
    leftUnitStandardChartToMixedPair, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, ← Spec.map_comp]
  have hring :
      (leftUnitChartOutputAlgHom W).toRingHom.comp
          (algebraMap (projectivePairChartCoordinateRing W (false, true))
            (projectivePairChartAdditionOutputRing W (false, true) true)) =
        (leftUnitChartPairAlgHom W).toRingHom := by
    apply RingHom.ext
    intro a
    exact leftUnitChartOutputAlgHom_algebraMap W a
  rw [Spec.map_inj]
  apply CommRingCat.hom_ext
  exact hring

private theorem leftUnitStandardChartToOutputOpen_comp_addition
    (W : WeierstrassCurve K) [W.IsElliptic] :
    leftUnitStandardChartToOutputOpen W ≫
        projectivePairChartAdditionOutputMorphism W (false, true) true =
      coveringChartMap W true := by
  rw [leftUnitStandardChartToOutputOpen,
    projectivePairChartAdditionOutputMorphism, ← Category.assoc,
    ← Spec.map_comp]
  have hring := leftUnitChartOutputAlgHom_comp_outputAlgHom W
  have hring' :
      (leftUnitChartOutputAlgHom W).toRingHom.comp
          (projectivePairChartAdditionOutputAlgHom W
            (false, true) true).toRingHom =
        RingHom.id (coveringChartCoordinateRing W true) := by
    exact congrArg AlgHom.toRingHom hring
  change Spec.map (CommRingCat.ofHom
      ((leftUnitChartOutputAlgHom W).toRingHom.comp
        (projectivePairChartAdditionOutputAlgHom W
          (false, true) true).toRingHom)) ≫
      coveringChartMap W true = coveringChartMap W true
  rw [hring']
  simp

/-! ## The chart origin is the projective infinity section -/

private theorem coordinateChartEvaluationRingHom_awayMk_eq_eval
    (i : Fin 3) (P : Fin 3 → K) (hPi : P i = 1)
    (p : MvPolynomial (Fin 3) K) {n : ℕ}
    (hp : p ∈ homogeneousPieces K n) :
    coordinateChartEvaluationRingHom i P
        (HomogeneousLocalization.Away.mk (homogeneousPieces K)
          (MvPolynomial.isHomogeneous_X K i) n p (by simpa using hp)) =
      MvPolynomial.eval P p := by
  rw [coordinateChartAwayMk_eq_eval₂Hom i p hp]
  simp only [MvPolynomial.map_eval₂Hom]
  have hconst :
      (coordinateChartEvaluationRingHom i P).comp
          (coordinateChartConstantHom i) = RingHom.id K := by
    ext a
    simp
  rw [hconst]
  have hratio :
      (fun j ↦ coordinateChartEvaluationRingHom (K := K) i P
        (coordinateChartRatio (K := K) i j)) = P := by
    funext j
    exact coordinateChartEvaluationRingHom_ratio (K := K) i P hPi j
  rw [hratio]
  rfl

/-- The explicit affine-chart evaluation at `[0 : 1 : 0]`. -/
private noncomputable def infinityChartOriginMorphism
    (W : WeierstrassCurve K) :
    Spec (.of K) ⟶ coveringChartScheme W false :=
  Spec.map (CommRingCat.ofHom
    (coveringInfinityChartOriginAlgHom W).toRingHom)

private theorem infinityChartOriginMorphism_ambient_closedPoint
    (W : WeierstrassCurve K) :
    (infinityChartOriginMorphism W ≫ coveringChartAmbientMap W false)
        (IsLocalRing.closedPoint K) =
      ambientPoint ![0, 1, 0]
        (nonsingular_ne_zero W ![0, 1, 0]
          W.toProjective.nonsingular_zero)
        (IsLocalRing.closedPoint K) := by
  let x : Spec (.of K) := IsLocalRing.closedPoint K
  let l : Spec (.of K) ⟶
      Spec (.of (coveringChartRing K false)) :=
    infinityChartOriginMorphism W ≫
      coveringChartQuotientInclusion W false
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro n p hp
  cases n with
  | zero =>
      rw [mem_projective_degree_zero_iff_eq_zero _ p hp,
        mem_projective_degree_zero_iff_eq_zero _ p hp]
  | succ n =>
      rw [mem_ambientPoint_closedPoint_iff ![0, 1, 0]
        (nonsingular_ne_zero W ![0, 1, 0]
          W.toProjective.nonsingular_zero)
        p (Nat.succ_pos n) hp]
      change p ∈
          ((coveringChartAway K false)
            (l x)).asHomogeneousIdeal ↔ _
      refine (polynomial_mem_awayι_iff_awayMk_mem
        (K := K) (coveringCoordinate false) (l x) p hp).trans ?_
      change coveringInfinityChartOriginAlgHom W
          (Ideal.Quotient.mk (coveringChartIdeal W false)
            (HomogeneousLocalization.Away.mk (homogeneousPieces K)
              (MvPolynomial.isHomogeneous_X K (coveringCoordinate false))
              (Nat.succ n) p (by simpa using hp))) ∈
            x.asIdeal ↔ _
      rw [show x.asIdeal = ⊥ from
        IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot]
      change coordinateChartEvaluationRingHom (K := K)
          (coveringCoordinate false) ![0, 1, 0]
            (HomogeneousLocalization.Away.mk (homogeneousPieces K)
              (MvPolynomial.isHomogeneous_X K (coveringCoordinate false))
              (Nat.succ n) p (by simpa using hp)) = 0 ↔ _
      rw [coordinateChartEvaluationRingHom_awayMk_eq_eval
        (coveringCoordinate false) ![0, 1, 0] (by rfl) p hp]

/-- The explicit infinity-chart origin as a point on the affine self-test
object. -/
private noncomputable def infinityChartOriginTestPoint
    (W : WeierstrassCurve K) :
    AffineCommGroupScheme.testObject (R := K) K ⟶ toOver W :=
  Over.homMk
    (infinityChartOriginMorphism W ≫ coveringChartMap W false) (by
      change (infinityChartOriginMorphism W ≫
          coveringChartMap W false) ≫ structureMap W =
        Spec.map (CommRingCat.ofHom (algebraMap K K))
      rw [Category.assoc, coveringChartMap_comp_structureMap,
        infinityChartOriginMorphism, ← Spec.map_comp,
        Spec.map_inj, ← CommRingCat.ofHom_comp]
      apply CommRingCat.hom_ext
      ext a
      exact (coveringInfinityChartOriginAlgHom W).commutes a)

private theorem infinityChartOriginTestPoint_eq_projectiveZero
    (W : WeierstrassCurve K) :
    infinityChartOriginTestPoint W = projectivePointOverMorphism W 0 := by
  apply overPoint_eq_of_ambientClosedPoint_eq W
  have hpoint :
      projectivePointMorphism W (0 : W.toProjective.Point) =
        pointOfNonsingularRepresentative W ![0, 1, 0]
          W.toProjective.nonsingular_zero := by
    rw [projectivePointMorphism,
      WeierstrassCurve.Projective.Point.toAffineLift_zero]
    change affinePointMorphism W (.zero) = _
    rfl
  have hoverpoint :
      projectivePointOverMorphism W (0 : W.toProjective.Point) =
        pointOverOfNonsingularRepresentative W ![0, 1, 0]
          W.toProjective.nonsingular_zero := by
    apply Over.OverMorphism.ext
    rw [projectivePointOverMorphism_left, hpoint]
    rfl
  rw [hoverpoint]
  rw [ambientClosedPointOfOverPoint, ambientClosedPointOfOverPoint,
    ambientMorphismOfOverPoint_pointOverOfNonsingularRepresentative]
  change
    ((infinityChartOriginMorphism W ≫ coveringChartMap W false) ≫
      inclusion W) (IsLocalRing.closedPoint K) = _
  rw [Category.assoc, coveringChartMap_comp_inclusion]
  exact infinityChartOriginMorphism_ambient_closedPoint W

/-- The explicit infinity-chart origin as a section in the slice. -/
private noncomputable def infinityChartOriginOver
    (W : WeierstrassCurve K) :
    𝟙_ (Over (Spec (.of K))) ⟶ toOver W :=
  Over.homMk
    (infinityChartOriginMorphism W ≫ coveringChartMap W false) (by
      change (infinityChartOriginMorphism W ≫
          coveringChartMap W false) ≫ structureMap W = 𝟙 _
      rw [Category.assoc, coveringChartMap_comp_structureMap,
        infinityChartOriginMorphism, ← Spec.map_comp, ← Spec.map_id,
        Spec.map_inj, ← CommRingCat.ofHom_comp]
      apply CommRingCat.hom_ext
      ext a
      exact (coveringInfinityChartOriginAlgHom W).commutes a)

private theorem infinityChartOriginOver_eq_testPoint
    (W : WeierstrassCurve K) :
    infinityChartOriginOver W =
      (tensorUnitIsoSelfTestObject (K := K)).hom ≫
        infinityChartOriginTestPoint W := by
  apply Over.OverMorphism.ext
  change infinityChartOriginMorphism W ≫ coveringChartMap W false =
    (tensorUnitIsoSelfTestObject (K := K)).hom.left ≫
      (infinityChartOriginMorphism W ≫ coveringChartMap W false)
  have he : (tensorUnitIsoSelfTestObject (K := K)).hom.left = 𝟙 _ := rfl
  rw [he]
  exact (Category.id_comp _).symm

private theorem infinityChartOriginOver_eq_infinitySectionOver
    (W : WeierstrassCurve K) :
    infinityChartOriginOver W = infinitySectionOver W := by
  rw [infinityChartOriginOver_eq_testPoint,
    infinityChartOriginTestPoint_eq_projectiveZero,
    tensorUnitIsoSelfTestObject_hom_comp_projectivePointOverMorphism_zero]

private theorem infinityChartOriginMorphism_comp_coveringChartMap
    (W : WeierstrassCurve K) :
    infinityChartOriginMorphism W ≫ coveringChartMap W false =
      (infinitySectionOver W).left := by
  have h := congrArg (fun f ↦ f.left)
    (infinityChartOriginOver_eq_infinitySectionOver W)
  exact h

private theorem leftUnitStandardChartToMixedPair_comp_secondInput
    (W : WeierstrassCurve K) :
    leftUnitStandardChartToMixedPair W ≫
        projectivePairChartSecondInput W (false, true) =
      coveringChartMap W true := by
  rw [leftUnitStandardChartToMixedPair,
    projectivePairChartSecondInput,
    projectivePairChartMorphismOfCoordinateRingHom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, ← Spec.map_comp]
  have hring :
      (leftUnitChartPairAlgHom W).toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := K)
            (A := coveringChartCoordinateRing W false)
            (B := coveringChartCoordinateRing W true)).toRingHom =
        RingHom.id (coveringChartCoordinateRing W true) := by
    apply RingHom.ext
    intro a
    simp [leftUnitChartPairAlgHom]
  have hcat :
      CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight
            (R := K)
            (A := coveringChartCoordinateRing W false)
            (B := coveringChartCoordinateRing W true)).toRingHom ≫
        CommRingCat.ofHom (leftUnitChartPairAlgHom W).toRingHom =
      𝟙 _ := by
    apply CommRingCat.hom_ext
    exact hring
  rw [hcat, Spec.map_id, Category.id_comp]

private theorem leftUnitStandardChartToMixedPair_comp_firstInput
    (W : WeierstrassCurve K) :
    leftUnitStandardChartToMixedPair W ≫
        projectivePairChartFirstInput W (false, true) =
      Spec.map (CommRingCat.ofHom
          (((Algebra.ofId K (coveringChartCoordinateRing W true)).comp
            (coveringInfinityChartOriginAlgHom W)).toRingHom)) ≫
        coveringChartMap W false := by
  rw [leftUnitStandardChartToMixedPair,
    projectivePairChartFirstInput,
    projectivePairChartMorphismOfCoordinateRingHom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  simp [leftUnitChartPairAlgHom]

private theorem leftUnitStandardChartToMixedPair_comp_firstInput_eq_infinity
    (W : WeierstrassCurve K) :
    leftUnitStandardChartToMixedPair W ≫
        projectivePairChartFirstInput W (false, true) =
      (coveringChartMap W true ≫ structureMap W) ≫
        (infinityChartOriginMorphism W ≫
          coveringChartMap W false) := by
  have hbase :
      Spec.map (CommRingCat.ofHom
          (((Algebra.ofId K (coveringChartCoordinateRing W true)).comp
            (coveringInfinityChartOriginAlgHom W)).toRingHom)) =
        Spec.map (CommRingCat.ofHom
            (coveringChartStructureRingHom W true)) ≫
          infinityChartOriginMorphism W := by
    rw [infinityChartOriginMorphism, ← Spec.map_comp, Spec.map_inj]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    rw [← coveringChartCoordinateRing_algebraMap]
    rfl
  calc
    _ = Spec.map (CommRingCat.ofHom
          (((Algebra.ofId K (coveringChartCoordinateRing W true)).comp
            (coveringInfinityChartOriginAlgHom W)).toRingHom)) ≫
        coveringChartMap W false :=
      leftUnitStandardChartToMixedPair_comp_firstInput W
    _ = (Spec.map (CommRingCat.ofHom
            (coveringChartStructureRingHom W true)) ≫
          infinityChartOriginMorphism W) ≫
        coveringChartMap W false := by rw [hbase]
    _ = Spec.map (CommRingCat.ofHom
          (coveringChartStructureRingHom W true)) ≫
        (infinityChartOriginMorphism W ≫
          coveringChartMap W false) := Category.assoc _ _ _
    _ = _ := by rw [coveringChartMap_comp_structureMap]

/-! ## The global left unit law -/

/-- Insert the projective infinity section in the first factor of the full
projective pair. -/
private theorem infinityChartOriginMorphism_comp_structureMap
    (W : WeierstrassCurve K) :
    (infinityChartOriginMorphism W ≫ coveringChartMap W false) ≫
      structureMap W = 𝟙 _ := by
  rw [Category.assoc, coveringChartMap_comp_structureMap,
    infinityChartOriginMorphism, ← Spec.map_comp, ← Spec.map_id,
    Spec.map_inj, ← CommRingCat.ofHom_comp]
  apply CommRingCat.hom_ext
  ext a
  exact (coveringInfinityChartOriginAlgHom W).commutes a

private noncomputable def projectiveLeftUnitInsertion
    (W : WeierstrassCurve K) :
    scheme W ⟶ projectivePair W :=
  pullback.lift
    (structureMap W ≫
      (infinityChartOriginMorphism W ≫ coveringChartMap W false))
    (𝟙 (scheme W)) (by
      calc
        (structureMap W ≫
            (infinityChartOriginMorphism W ≫ coveringChartMap W false)) ≫
            structureMap W =
          structureMap W ≫
            ((infinityChartOriginMorphism W ≫
              coveringChartMap W false) ≫ structureMap W) :=
              Category.assoc _ _ _
        _ = structureMap W ≫ 𝟙 (Spec (.of K)) := by
          rw [infinityChartOriginMorphism_comp_structureMap]
        _ = (𝟙 (scheme W)) ≫ structureMap W := by simp)

@[reassoc]
private theorem projectiveLeftUnitInsertion_fst
    (W : WeierstrassCurve K) :
    projectiveLeftUnitInsertion W ≫
        pullback.fst (structureMap W) (structureMap W) =
      structureMap W ≫
        (infinityChartOriginMorphism W ≫ coveringChartMap W false) := by
  exact pullback.lift_fst _ _ _

@[reassoc]
private theorem projectiveLeftUnitInsertion_snd
    (W : WeierstrassCurve K) :
    projectiveLeftUnitInsertion W ≫
        pullback.snd (structureMap W) (structureMap W) =
      𝟙 (scheme W) := by
  exact pullback.lift_snd _ _ _

private theorem leftUnitStandardChartToMixedPair_comp_globalChart
    (W : WeierstrassCurve K) :
    leftUnitStandardChartToMixedPair W ≫
        projectivePairChartMap W (false, true) =
      coveringChartMap W true ≫ projectiveLeftUnitInsertion W := by
  apply pullback.hom_ext
  · calc
      _ = leftUnitStandardChartToMixedPair W ≫
          projectivePairChartFirstInput W (false, true) := by
            rw [Category.assoc, projectivePairChartMap_comp_fst,
              ← projectivePairChartFirstInput_eq]
      _ = (coveringChartMap W true ≫ structureMap W) ≫
          (infinityChartOriginMorphism W ≫
            coveringChartMap W false) :=
        leftUnitStandardChartToMixedPair_comp_firstInput_eq_infinity W
      _ = coveringChartMap W true ≫
          (structureMap W ≫
            (infinityChartOriginMorphism W ≫
              coveringChartMap W false)) := Category.assoc _ _ _
      _ = coveringChartMap W true ≫
          (projectiveLeftUnitInsertion W ≫
            pullback.fst (structureMap W) (structureMap W)) := by
              rw [projectiveLeftUnitInsertion_fst]
      _ = (coveringChartMap W true ≫ projectiveLeftUnitInsertion W) ≫
          pullback.fst (structureMap W) (structureMap W) :=
            (Category.assoc _ _ _).symm
  · calc
      _ = leftUnitStandardChartToMixedPair W ≫
          projectivePairChartSecondInput W (false, true) := by
            rw [Category.assoc, projectivePairChartMap_comp_snd,
              ← projectivePairChartSecondInput_eq]
      _ = coveringChartMap W true :=
        leftUnitStandardChartToMixedPair_comp_secondInput W
      _ = coveringChartMap W true ≫ 𝟙 (scheme W) :=
        (Category.comp_id _).symm
      _ = coveringChartMap W true ≫
          (projectiveLeftUnitInsertion W ≫
            pullback.snd (structureMap W) (structureMap W)) := by
              rw [projectiveLeftUnitInsertion_snd]
      _ = (coveringChartMap W true ≫ projectiveLeftUnitInsertion W) ≫
          pullback.snd (structureMap W) (structureMap W) :=
            (Category.assoc _ _ _).symm

private theorem standardChart_projectiveLeftUnitInsertion_addition
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (coveringChartMap W true ≫ projectiveLeftUnitInsertion W) ≫
        projectiveAdditionMorphism W =
      coveringChartMap W true := by
  calc
    _ = (leftUnitStandardChartToMixedPair W ≫
          projectivePairChartMap W (false, true)) ≫
        projectiveAdditionMorphism W := by
          rw [leftUnitStandardChartToMixedPair_comp_globalChart]
    _ = leftUnitStandardChartToMixedPair W ≫
        (projectivePairChartMap W (false, true) ≫
          projectiveAdditionMorphism W) := Category.assoc _ _ _
    _ = leftUnitStandardChartToMixedPair W ≫
        projectivePairInfinityStandardAdditionMorphism W := by
          rw [projectivePairInfinityStandardChart_comp_projectiveAdditionMorphism]
    _ = (leftUnitStandardChartToOutputOpen W ≫
          projectivePairChartAdditionOutputOpen W (false, true) true) ≫
        projectivePairInfinityStandardAdditionMorphism W := by
          rw [leftUnitStandardChartToOutputOpen_comp_open]
    _ = leftUnitStandardChartToOutputOpen W ≫
        (projectivePairChartAdditionOutputOpen W (false, true) true ≫
          projectivePairInfinityStandardAdditionMorphism W) :=
      Category.assoc _ _ _
    _ = leftUnitStandardChartToOutputOpen W ≫
        projectivePairChartAdditionOutputMorphism W
          (false, true) true := by
            rw [projectivePairInfinityStandardSecantZOpen_comp_addition]
    _ = coveringChartMap W true :=
      leftUnitStandardChartToOutputOpen_comp_addition W

/-- The globally glued projective addition has the projective origin as a
left identity. -/
private theorem projectiveLeftUnitInsertion_comp_addition
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectiveLeftUnitInsertion W ≫ projectiveAdditionMorphism W =
      𝟙 (scheme W) := by
  letI : IsDominant (coveringChartMap W true) := by
    constructor
    have hopen := (coveringChartMap W true).isOpenEmbedding.isOpenMap
    exact hopen.denseRange_of_isPreirreducibleSpace _
  apply ext_of_isDominant_of_isSeparated
    (s := structureMap W) (ι := coveringChartMap W true)
  · calc
      (projectiveLeftUnitInsertion W ≫
            projectiveAdditionMorphism W) ≫ structureMap W =
          projectiveLeftUnitInsertion W ≫
            (projectiveAdditionMorphism W ≫ structureMap W) :=
        Category.assoc _ _ _
      _ = projectiveLeftUnitInsertion W ≫
          projectivePairStructureMap W := by
            rw [projectiveAdditionMorphism_comp_structureMap]
      _ = (projectiveLeftUnitInsertion W ≫
            pullback.fst (structureMap W) (structureMap W)) ≫
          structureMap W := by
            rw [projectivePairStructureMap, Category.assoc]
      _ = (structureMap W ≫
            (infinityChartOriginMorphism W ≫
              coveringChartMap W false)) ≫ structureMap W := by
                rw [projectiveLeftUnitInsertion_fst]
      _ = structureMap W ≫
          ((infinityChartOriginMorphism W ≫
              coveringChartMap W false) ≫ structureMap W) :=
        Category.assoc _ _ _
      _ = structureMap W ≫ 𝟙 (Spec (.of K)) := by
        rw [infinityChartOriginMorphism_comp_structureMap]
      _ = 𝟙 (scheme W) ≫ structureMap W := by simp
  calc
    _ = (coveringChartMap W true ≫ projectiveLeftUnitInsertion W) ≫
        projectiveAdditionMorphism W := (Category.assoc _ _ _).symm
    _ = coveringChartMap W true :=
      standardChart_projectiveLeftUnitInsertion_addition W
    _ = coveringChartMap W true ≫ 𝟙 (scheme W) :=
      (Category.comp_id _).symm

/-! ## The categorical left unit law -/

/-- In a cartesian monoidal category, inserting the unit in the first factor
is the binary-product lift of the unit section and the identity. -/
private theorem categoricalLeftUnitInsertion_eq_lift
    (W : WeierstrassCurve K) :
    (λ_ (toOver W)).inv ≫
        (infinitySectionOver W ▷ toOver W) =
      lift (toUnit (toOver W) ≫ infinitySectionOver W)
        (𝟙 (toOver W)) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · simp

/-- The concrete projective-pair insertion, regarded as a morphism in the
slice. -/
private noncomputable def projectiveLeftUnitInsertionOver
    (W : WeierstrassCurve K) :
    toOver W ⟶ toOver W ⊗ toOver W :=
  Over.homMk (projectiveLeftUnitInsertion W) (by
    rw [tensorProjectiveCubic_hom]
    change projectiveLeftUnitInsertion W ≫
        projectivePairStructureMap W = structureMap W
    rw [projectivePairStructureMap, ← Category.assoc,
      projectiveLeftUnitInsertion_fst, Category.assoc,
      infinityChartOriginMorphism_comp_structureMap,
      Category.comp_id])

@[simp]
private theorem projectiveLeftUnitInsertionOver_left
    (W : WeierstrassCurve K) :
    (projectiveLeftUnitInsertionOver W).left =
      projectiveLeftUnitInsertion W :=
  rfl

/-- The concrete slice insertion is the product lift of the infinity section
and the identity. -/
private theorem projectiveLeftUnitInsertionOver_eq_lift
    (W : WeierstrassCurve K) :
    projectiveLeftUnitInsertionOver W =
      lift (toUnit (toOver W) ≫ infinitySectionOver W)
        (𝟙 (toOver W)) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [lift_fst]
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.fst_left,
      projectiveLeftUnitInsertionOver_left, Over.toUnit_left]
    change projectiveLeftUnitInsertion W ≫
        pullback.fst (structureMap W) (structureMap W) =
      structureMap W ≫ (infinitySectionOver W).left
    convert projectiveLeftUnitInsertion_fst W using 1
    rw [infinityChartOriginMorphism_comp_coveringChartMap]
    constructor <;> intro h <;> exact h
  · rw [lift_snd]
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.snd_left,
      projectiveLeftUnitInsertionOver_left]
    exact projectiveLeftUnitInsertion_snd W

/-- The cartesian-monoidal insertion of the infinity section is the concrete
projective-pair insertion used in the chart calculation above. -/
private theorem categoricalLeftUnitInsertion_left
    (W : WeierstrassCurve K) :
    (((λ_ (toOver W)).inv ≫
          (infinitySectionOver W ▷ toOver W)).left) =
      projectiveLeftUnitInsertion W := by
  simpa only [projectiveLeftUnitInsertionOver_left] using
    congrArg (fun f ↦ f.left)
      ((categoricalLeftUnitInsertion_eq_lift W).trans
        (projectiveLeftUnitInsertionOver_eq_lift W).symm)

/-- The globally glued projective addition has the infinity section as its
categorical left unit. -/
theorem infinitySectionOver_projectiveAdditionOver_left_unit
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (infinitySectionOver W ▷ toOver W) ≫
        projectiveAdditionOver W =
      (λ_ (toOver W)).hom := by
  rw [← cancel_epi (λ_ (toOver W)).inv]
  rw [← Category.assoc, Iso.inv_hom_id]
  apply Over.OverMorphism.ext
  change (((λ_ (toOver W)).inv ≫
        (infinitySectionOver W ▷ toOver W)).left) ≫
      projectiveAdditionMorphism W = 𝟙 (scheme W)
  rw [categoricalLeftUnitInsertion_left]
  convert projectiveLeftUnitInsertion_comp_addition W using 1
  constructor <;> intro h <;> exact h

/-! ## The right unit on the dense standard chart -/

/-- Retain the first, universal standard-chart factor and evaluate the second
factor of the standard-by-infinity chart at the origin. -/
private noncomputable def rightUnitChartPairAlgHom
    (W : WeierstrassCurve K) :
    projectivePairChartCoordinateRing W (true, false) →ₐ[K]
      coveringChartCoordinateRing W true :=
  Algebra.TensorProduct.lift
    (AlgHom.id K (coveringChartCoordinateRing W true))
    ((Algebra.ofId K (coveringChartCoordinateRing W true)).comp
      (coveringInfinityChartOriginAlgHom W))
    (fun _ _ ↦ Commute.all _ _)

@[simp]
private theorem rightUnitChartPairAlgHom_firstUniversalPoint
    (W : WeierstrassCurve K) (j : Fin 3) :
    rightUnitChartPairAlgHom W
        (projectivePairChartFirstUniversalPoint W (true, false) j) =
      coveringChartUniversalPoint W true j := by
  simp [rightUnitChartPairAlgHom,
    projectivePairChartFirstUniversalPoint]

@[simp]
private theorem rightUnitChartPairAlgHom_secondUniversalPoint
    (W : WeierstrassCurve K) (j : Fin 3) :
    rightUnitChartPairAlgHom W
        (projectivePairChartSecondUniversalPoint W (true, false) j) =
      ![0, 1, 0] j := by
  fin_cases j <;>
    simp [rightUnitChartPairAlgHom,
      projectivePairChartSecondUniversalPoint,
      coveringInfinityChartOriginAlgHom_universalPoint]

private theorem rightUnitChartPairAlgHom_additionCoordinates
    (W : WeierstrassCurve K) (j : Fin 3) :
    rightUnitChartPairAlgHom W
        (projectivePairChartAdditionCoordinates W (true, false) j) =
      -coveringChartUniversalPoint W true j := by
  let f := (rightUnitChartPairAlgHom W).toRingHom
  let P := projectivePairChartFirstUniversalPoint W (true, false)
  let Q := projectivePairChartSecondUniversalPoint W (true, false)
  have hmap := congrFun
    (WeierstrassCurve.Projective.map_addXYZ
      (W' := projectivePairChartMappedCurve W (true, false))
      (P := P) (Q := Q) f) j
  have hcurve :
      (projectivePairChartMappedCurve W (true, false)).map f =
        W.map (algebraMap K (coveringChartCoordinateRing W true)) := by
    rw [projectivePairChartMappedCurve, WeierstrassCurve.map_map]
    congr 1
    ext r
    exact (rightUnitChartPairAlgHom W).commutes r
  have hP : f ∘ P = coveringChartUniversalPoint W true := by
    funext k
    exact rightUnitChartPairAlgHom_firstUniversalPoint W k
  have hQ : f ∘ Q = (![0, 1, 0] : Fin 3 →
      coveringChartCoordinateRing W true) := by
    funext k
    exact rightUnitChartPairAlgHom_secondUniversalPoint W k
  change
    ((projectivePairChartMappedCurve W (true, false)).map f).toProjective.addXYZ
        (f ∘ P) (f ∘ Q) j =
      (f ∘ (projectivePairChartMappedCurve W (true, false)).toProjective.addXYZ
        P Q) j at hmap
  rw [hcurve, hP, hQ] at hmap
  have hformula :=
    WeierstrassCurve.Projective.addXYZ_of_Z_eq_zero_right
      (W' := (W.map
        (algebraMap K (coveringChartCoordinateRing W true))).toProjective)
      (P := coveringChartUniversalPoint W true)
      (Q := (![0, 1, 0] : Fin 3 →
        coveringChartCoordinateRing W true))
      (by simpa using
        (W.map (algebraMap K
          (coveringChartCoordinateRing W true))).toProjective.equation_zero)
      (by rfl)
  rw [hformula] at hmap
  have hPz : coveringChartUniversalPoint W true (2 : Fin 3) = 1 :=
    coveringChartUniversalPoint_normalized W true
  rw [Pi.smul_apply, hPz] at hmap
  simpa [P, Q, f, projectivePairChartAdditionCoordinates,
    Pi.smul_apply] using hmap.symm

private theorem rightUnitChartPairAlgHom_additionZ
    (W : WeierstrassCurve K) :
    rightUnitChartPairAlgHom W
        (projectivePairChartAdditionCoordinates W (true, false)
          (coveringCoordinate true)) = -1 := by
  rw [rightUnitChartPairAlgHom_additionCoordinates,
    coveringChartUniversalPoint_normalized]

/-- The right-unit axis lands in the mixed chart's secant output-`Z` open,
because that output coordinate specializes to negative one. -/
private noncomputable def rightUnitChartOutputAlgHom
    (W : WeierstrassCurve K) :
    projectivePairChartAdditionOutputRing W (true, false) true →ₐ[K]
      coveringChartCoordinateRing W true :=
  IsLocalization.Away.liftAlgHom
    (projectivePairChartAdditionCoordinates W (true, false)
      (coveringCoordinate true))
    (f := rightUnitChartPairAlgHom W) (by
      rw [rightUnitChartPairAlgHom_additionZ]
      exact isUnit_neg_one)

@[simp]
private theorem rightUnitChartOutputAlgHom_algebraMap
    (W : WeierstrassCurve K)
    (a : projectivePairChartCoordinateRing W (true, false)) :
    rightUnitChartOutputAlgHom W
        (algebraMap (projectivePairChartCoordinateRing W (true, false))
          (projectivePairChartAdditionOutputRing W (true, false) true) a) =
      rightUnitChartPairAlgHom W a := by
  simp [rightUnitChartOutputAlgHom, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]

private theorem rightUnitChartOutputAlgHom_outputPoint
    (W : WeierstrassCurve K) [W.IsElliptic] (j : Fin 3) :
    rightUnitChartOutputAlgHom W
        (projectivePairChartAdditionOutputPoint W (true, false) true j) =
      coveringChartUniversalPoint W true j := by
  rw [projectivePairChartAdditionOutputPoint, map_mul,
    rightUnitChartOutputAlgHom_algebraMap,
    rightUnitChartPairAlgHom_additionCoordinates]
  have hunit : rightUnitChartOutputAlgHom W
      (↑(projectivePairChartAdditionOutputUnit W (true, false) true) :
        projectivePairChartAdditionOutputRing W (true, false) true) = -1 := by
    unfold projectivePairChartAdditionOutputUnit
    rw [IsUnit.unit_spec]
    rw [rightUnitChartOutputAlgHom_algebraMap,
      rightUnitChartPairAlgHom_additionZ]
  have hinv : rightUnitChartOutputAlgHom W
      (↑(projectivePairChartAdditionOutputUnit W (true, false) true)⁻¹ :
        projectivePairChartAdditionOutputRing W (true, false) true) = -1 := by
    let u := projectivePairChartAdditionOutputUnit W (true, false) true
    have hu : Units.map (rightUnitChartOutputAlgHom W).toMonoidHom u =
        (-1 : (coveringChartCoordinateRing W true)ˣ) := by
      apply Units.ext
      exact hunit
    have hi := congrArg Inv.inv hu
    have hiv := congrArg Units.val hi
    simpa [u] using hiv
  rw [hinv]
  simp

private theorem rightUnitChartOutputAlgHom_comp_outputAlgHom
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (rightUnitChartOutputAlgHom W).comp
        (projectivePairChartAdditionOutputAlgHom W
          (true, false) true) =
      AlgHom.id K (coveringChartCoordinateRing W true) := by
  apply AlgHom.coe_ringHom_injective
  apply Ideal.Quotient.ringHom_ext
  apply chartRingHom_ext (K := K) (coveringCoordinate true)
  · ext a
    change rightUnitChartOutputAlgHom W
        (projectivePairChartAdditionOutputAlgHom W (true, false) true
          (coveringChartStructureRingHom W true a)) =
      coveringChartStructureRingHom W true a
    rw [← coveringChartCoordinateRing_algebraMap,
      (projectivePairChartAdditionOutputAlgHom W
        (true, false) true).commutes,
      (rightUnitChartOutputAlgHom W).commutes]
  · intro j
    change rightUnitChartOutputAlgHom W
        (projectivePairChartAdditionOutputAlgHom W (true, false) true
          (Ideal.Quotient.mk (coveringChartIdeal W true)
            (coordinateChartRatio (coveringCoordinate true) j))) = _
    rw [projectivePairChartAdditionOutputAlgHom_ratio,
      rightUnitChartOutputAlgHom_outputPoint]
    rfl

/-- The dense standard chart mapped into the standard-by-infinity pair chart
along the right-unit axis. -/
private noncomputable def rightUnitStandardChartToMixedPair
    (W : WeierstrassCurve K) :
    coveringChartScheme W true ⟶
      projectivePairChartScheme W (true, false) :=
  Spec.map (CommRingCat.ofHom (rightUnitChartPairAlgHom W).toRingHom) ≫
    (projectivePairChartIsoSpecTensor W (true, false)).inv

/-- The canonical factor of the right-unit axis through the output-`Z`
principal open. -/
private noncomputable def rightUnitStandardChartToOutputOpen
    (W : WeierstrassCurve K) :
    coveringChartScheme W true ⟶
      Spec (.of
        (projectivePairChartAdditionOutputRing W (true, false) true)) :=
  Spec.map (CommRingCat.ofHom (rightUnitChartOutputAlgHom W).toRingHom)

private theorem rightUnitStandardChartToOutputOpen_comp_open
    (W : WeierstrassCurve K) :
    rightUnitStandardChartToOutputOpen W ≫
        projectivePairChartAdditionOutputOpen W (true, false) true =
      rightUnitStandardChartToMixedPair W := by
  apply (cancel_mono
    (projectivePairChartIsoSpecTensor W (true, false)).hom).1
  rw [Category.assoc,
    projectivePairChartAdditionOutputOpen_comp_iso_hom]
  rw [rightUnitStandardChartToOutputOpen,
    rightUnitStandardChartToMixedPair, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, ← Spec.map_comp]
  have hring :
      (rightUnitChartOutputAlgHom W).toRingHom.comp
          (algebraMap (projectivePairChartCoordinateRing W (true, false))
            (projectivePairChartAdditionOutputRing W (true, false) true)) =
        (rightUnitChartPairAlgHom W).toRingHom := by
    apply RingHom.ext
    intro a
    exact rightUnitChartOutputAlgHom_algebraMap W a
  rw [Spec.map_inj]
  apply CommRingCat.hom_ext
  exact hring

private theorem rightUnitStandardChartToOutputOpen_comp_addition
    (W : WeierstrassCurve K) [W.IsElliptic] :
    rightUnitStandardChartToOutputOpen W ≫
        projectivePairChartAdditionOutputMorphism W (true, false) true =
      coveringChartMap W true := by
  rw [rightUnitStandardChartToOutputOpen,
    projectivePairChartAdditionOutputMorphism, ← Category.assoc,
    ← Spec.map_comp]
  have hring := rightUnitChartOutputAlgHom_comp_outputAlgHom W
  have hring' :
      (rightUnitChartOutputAlgHom W).toRingHom.comp
          (projectivePairChartAdditionOutputAlgHom W
            (true, false) true).toRingHom =
        RingHom.id (coveringChartCoordinateRing W true) := by
    exact congrArg AlgHom.toRingHom hring
  change Spec.map (CommRingCat.ofHom
      ((rightUnitChartOutputAlgHom W).toRingHom.comp
        (projectivePairChartAdditionOutputAlgHom W
          (true, false) true).toRingHom)) ≫
      coveringChartMap W true = coveringChartMap W true
  rw [hring']
  simp

private theorem rightUnitStandardChartToMixedPair_comp_firstInput
    (W : WeierstrassCurve K) :
    rightUnitStandardChartToMixedPair W ≫
        projectivePairChartFirstInput W (true, false) =
      coveringChartMap W true := by
  rw [rightUnitStandardChartToMixedPair,
    projectivePairChartFirstInput,
    projectivePairChartMorphismOfCoordinateRingHom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, ← Spec.map_comp]
  have hring :
      (rightUnitChartPairAlgHom W).toRingHom.comp
          (Algebra.TensorProduct.includeLeft
            (R := K)
            (S := K)
            (A := coveringChartCoordinateRing W true)
            (B := coveringChartCoordinateRing W false)).toRingHom =
        RingHom.id (coveringChartCoordinateRing W true) := by
    apply RingHom.ext
    intro a
    simp [rightUnitChartPairAlgHom]
  have hcat :
      CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeft
            (R := K)
            (S := K)
            (A := coveringChartCoordinateRing W true)
            (B := coveringChartCoordinateRing W false)).toRingHom ≫
        CommRingCat.ofHom (rightUnitChartPairAlgHom W).toRingHom =
      𝟙 _ := by
    apply CommRingCat.hom_ext
    exact hring
  rw [hcat, Spec.map_id, Category.id_comp]

private theorem rightUnitStandardChartToMixedPair_comp_secondInput
    (W : WeierstrassCurve K) :
    rightUnitStandardChartToMixedPair W ≫
        projectivePairChartSecondInput W (true, false) =
      Spec.map (CommRingCat.ofHom
          (((Algebra.ofId K (coveringChartCoordinateRing W true)).comp
            (coveringInfinityChartOriginAlgHom W)).toRingHom)) ≫
        coveringChartMap W false := by
  rw [rightUnitStandardChartToMixedPair,
    projectivePairChartSecondInput,
    projectivePairChartMorphismOfCoordinateRingHom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  simp [rightUnitChartPairAlgHom]

private theorem rightUnitStandardChartToMixedPair_comp_secondInput_eq_infinity
    (W : WeierstrassCurve K) :
    rightUnitStandardChartToMixedPair W ≫
        projectivePairChartSecondInput W (true, false) =
      (coveringChartMap W true ≫ structureMap W) ≫
        (infinityChartOriginMorphism W ≫
          coveringChartMap W false) := by
  have hbase :
      Spec.map (CommRingCat.ofHom
          (((Algebra.ofId K (coveringChartCoordinateRing W true)).comp
            (coveringInfinityChartOriginAlgHom W)).toRingHom)) =
        Spec.map (CommRingCat.ofHom
            (coveringChartStructureRingHom W true)) ≫
          infinityChartOriginMorphism W := by
    rw [infinityChartOriginMorphism, ← Spec.map_comp, Spec.map_inj]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    rw [← coveringChartCoordinateRing_algebraMap]
    rfl
  calc
    _ = Spec.map (CommRingCat.ofHom
          (((Algebra.ofId K (coveringChartCoordinateRing W true)).comp
            (coveringInfinityChartOriginAlgHom W)).toRingHom)) ≫
        coveringChartMap W false :=
      rightUnitStandardChartToMixedPair_comp_secondInput W
    _ = (Spec.map (CommRingCat.ofHom
            (coveringChartStructureRingHom W true)) ≫
          infinityChartOriginMorphism W) ≫
        coveringChartMap W false := by rw [hbase]
    _ = Spec.map (CommRingCat.ofHom
          (coveringChartStructureRingHom W true)) ≫
        (infinityChartOriginMorphism W ≫
          coveringChartMap W false) := Category.assoc _ _ _
    _ = _ := by rw [coveringChartMap_comp_structureMap]

/-! ## The global right unit law -/

/-- Insert the projective infinity section in the second factor of the full
projective pair. -/
private noncomputable def projectiveRightUnitInsertion
    (W : WeierstrassCurve K) :
    scheme W ⟶ projectivePair W :=
  pullback.lift
    (𝟙 (scheme W))
    (structureMap W ≫
      (infinityChartOriginMorphism W ≫ coveringChartMap W false)) (by
      calc
        (𝟙 (scheme W)) ≫ structureMap W =
            structureMap W ≫ 𝟙 (Spec (.of K)) := by simp
        _ = structureMap W ≫
            ((infinityChartOriginMorphism W ≫
              coveringChartMap W false) ≫ structureMap W) := by
                rw [infinityChartOriginMorphism_comp_structureMap]
        _ = (structureMap W ≫
            (infinityChartOriginMorphism W ≫
              coveringChartMap W false)) ≫ structureMap W :=
                (Category.assoc _ _ _).symm)

@[reassoc]
private theorem projectiveRightUnitInsertion_fst
    (W : WeierstrassCurve K) :
    projectiveRightUnitInsertion W ≫
        pullback.fst (structureMap W) (structureMap W) =
      𝟙 (scheme W) := by
  exact pullback.lift_fst _ _ _

@[reassoc]
private theorem projectiveRightUnitInsertion_snd
    (W : WeierstrassCurve K) :
    projectiveRightUnitInsertion W ≫
        pullback.snd (structureMap W) (structureMap W) =
      structureMap W ≫
        (infinityChartOriginMorphism W ≫ coveringChartMap W false) := by
  exact pullback.lift_snd _ _ _

private theorem rightUnitStandardChartToMixedPair_comp_globalChart
    (W : WeierstrassCurve K) :
    rightUnitStandardChartToMixedPair W ≫
        projectivePairChartMap W (true, false) =
      coveringChartMap W true ≫ projectiveRightUnitInsertion W := by
  apply pullback.hom_ext
  · calc
      _ = rightUnitStandardChartToMixedPair W ≫
          projectivePairChartFirstInput W (true, false) := by
            rw [Category.assoc, projectivePairChartMap_comp_fst,
              ← projectivePairChartFirstInput_eq]
      _ = coveringChartMap W true :=
        rightUnitStandardChartToMixedPair_comp_firstInput W
      _ = coveringChartMap W true ≫ 𝟙 (scheme W) :=
        (Category.comp_id _).symm
      _ = coveringChartMap W true ≫
          (projectiveRightUnitInsertion W ≫
            pullback.fst (structureMap W) (structureMap W)) := by
              rw [projectiveRightUnitInsertion_fst]
      _ = (coveringChartMap W true ≫ projectiveRightUnitInsertion W) ≫
          pullback.fst (structureMap W) (structureMap W) :=
            (Category.assoc _ _ _).symm
  · calc
      _ = rightUnitStandardChartToMixedPair W ≫
          projectivePairChartSecondInput W (true, false) := by
            rw [Category.assoc, projectivePairChartMap_comp_snd,
              ← projectivePairChartSecondInput_eq]
      _ = (coveringChartMap W true ≫ structureMap W) ≫
          (infinityChartOriginMorphism W ≫
            coveringChartMap W false) :=
        rightUnitStandardChartToMixedPair_comp_secondInput_eq_infinity W
      _ = coveringChartMap W true ≫
          (structureMap W ≫
            (infinityChartOriginMorphism W ≫
              coveringChartMap W false)) := Category.assoc _ _ _
      _ = coveringChartMap W true ≫
          (projectiveRightUnitInsertion W ≫
            pullback.snd (structureMap W) (structureMap W)) := by
              rw [projectiveRightUnitInsertion_snd]
      _ = (coveringChartMap W true ≫ projectiveRightUnitInsertion W) ≫
          pullback.snd (structureMap W) (structureMap W) :=
            (Category.assoc _ _ _).symm

private theorem standardChart_projectiveRightUnitInsertion_addition
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (coveringChartMap W true ≫ projectiveRightUnitInsertion W) ≫
        projectiveAdditionMorphism W =
      coveringChartMap W true := by
  calc
    _ = (rightUnitStandardChartToMixedPair W ≫
          projectivePairChartMap W (true, false)) ≫
        projectiveAdditionMorphism W := by
          rw [rightUnitStandardChartToMixedPair_comp_globalChart]
    _ = rightUnitStandardChartToMixedPair W ≫
        (projectivePairChartMap W (true, false) ≫
          projectiveAdditionMorphism W) := Category.assoc _ _ _
    _ = rightUnitStandardChartToMixedPair W ≫
        projectivePairStandardInfinityAdditionMorphism W := by
          rw [projectivePairStandardInfinityChart_comp_projectiveAdditionMorphism]
    _ = (rightUnitStandardChartToOutputOpen W ≫
          projectivePairChartAdditionOutputOpen W (true, false) true) ≫
        projectivePairStandardInfinityAdditionMorphism W := by
          rw [rightUnitStandardChartToOutputOpen_comp_open]
    _ = rightUnitStandardChartToOutputOpen W ≫
        (projectivePairChartAdditionOutputOpen W (true, false) true ≫
          projectivePairStandardInfinityAdditionMorphism W) :=
      Category.assoc _ _ _
    _ = rightUnitStandardChartToOutputOpen W ≫
        projectivePairChartAdditionOutputMorphism W
          (true, false) true := by
            rw [projectivePairStandardInfinitySecantZOpen_comp_addition]
    _ = coveringChartMap W true :=
      rightUnitStandardChartToOutputOpen_comp_addition W

/-- The globally glued projective addition has the projective origin as a
right identity. -/
private theorem projectiveRightUnitInsertion_comp_addition
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectiveRightUnitInsertion W ≫ projectiveAdditionMorphism W =
      𝟙 (scheme W) := by
  letI : IsDominant (coveringChartMap W true) := by
    constructor
    have hopen := (coveringChartMap W true).isOpenEmbedding.isOpenMap
    exact hopen.denseRange_of_isPreirreducibleSpace _
  apply ext_of_isDominant_of_isSeparated
    (s := structureMap W) (ι := coveringChartMap W true)
  · calc
      (projectiveRightUnitInsertion W ≫
            projectiveAdditionMorphism W) ≫ structureMap W =
          projectiveRightUnitInsertion W ≫
            (projectiveAdditionMorphism W ≫ structureMap W) :=
        Category.assoc _ _ _
      _ = projectiveRightUnitInsertion W ≫
          projectivePairStructureMap W := by
            rw [projectiveAdditionMorphism_comp_structureMap]
      _ = (projectiveRightUnitInsertion W ≫
            pullback.fst (structureMap W) (structureMap W)) ≫
          structureMap W := by
            rw [projectivePairStructureMap, Category.assoc]
      _ = 𝟙 (scheme W) ≫ structureMap W := by
        rw [projectiveRightUnitInsertion_fst]
  · calc
      _ = (coveringChartMap W true ≫ projectiveRightUnitInsertion W) ≫
          projectiveAdditionMorphism W := (Category.assoc _ _ _).symm
      _ = coveringChartMap W true :=
        standardChart_projectiveRightUnitInsertion_addition W
      _ = coveringChartMap W true ≫ 𝟙 (scheme W) :=
        (Category.comp_id _).symm

/-! ## The categorical right unit law -/

/-- In a cartesian monoidal category, inserting the unit in the second factor
is the binary-product lift of the identity and the unit section. -/
private theorem categoricalRightUnitInsertion_eq_lift
    (W : WeierstrassCurve K) :
    (ρ_ (toOver W)).inv ≫
        (toOver W ◁ infinitySectionOver W) =
      lift (𝟙 (toOver W))
        (toUnit (toOver W) ≫ infinitySectionOver W) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · simp

/-- The concrete right insertion, regarded as a morphism in the slice. -/
private noncomputable def projectiveRightUnitInsertionOver
    (W : WeierstrassCurve K) :
    toOver W ⟶ toOver W ⊗ toOver W :=
  Over.homMk (projectiveRightUnitInsertion W) (by
    rw [tensorProjectiveCubic_hom]
    change projectiveRightUnitInsertion W ≫
        projectivePairStructureMap W = structureMap W
    rw [projectivePairStructureMap, ← Category.assoc,
      projectiveRightUnitInsertion_fst, Category.id_comp])

@[simp]
private theorem projectiveRightUnitInsertionOver_left
    (W : WeierstrassCurve K) :
    (projectiveRightUnitInsertionOver W).left =
      projectiveRightUnitInsertion W :=
  rfl

/-- The concrete slice right insertion is the product lift of the identity
and the infinity section. -/
private theorem projectiveRightUnitInsertionOver_eq_lift
    (W : WeierstrassCurve K) :
    projectiveRightUnitInsertionOver W =
      lift (𝟙 (toOver W))
        (toUnit (toOver W) ≫ infinitySectionOver W) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [lift_fst]
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.fst_left,
      projectiveRightUnitInsertionOver_left]
    exact projectiveRightUnitInsertion_fst W
  · rw [lift_snd]
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.snd_left,
      projectiveRightUnitInsertionOver_left, Over.toUnit_left]
    change projectiveRightUnitInsertion W ≫
        pullback.snd (structureMap W) (structureMap W) =
      structureMap W ≫ (infinitySectionOver W).left
    convert projectiveRightUnitInsertion_snd W using 1
    rw [infinityChartOriginMorphism_comp_coveringChartMap]
    constructor <;> intro h <;> exact h

/-- The cartesian-monoidal right insertion of the infinity section is the
concrete projective-pair insertion used in the chart calculation above. -/
private theorem categoricalRightUnitInsertion_left
    (W : WeierstrassCurve K) :
    (((ρ_ (toOver W)).inv ≫
          (toOver W ◁ infinitySectionOver W)).left) =
      projectiveRightUnitInsertion W := by
  simpa only [projectiveRightUnitInsertionOver_left] using
    congrArg (fun f ↦ f.left)
      ((categoricalRightUnitInsertion_eq_lift W).trans
        (projectiveRightUnitInsertionOver_eq_lift W).symm)

/-- The globally glued projective addition has the infinity section as its
categorical right unit. -/
theorem infinitySectionOver_projectiveAdditionOver_right_unit
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (toOver W ◁ infinitySectionOver W) ≫
        projectiveAdditionOver W =
      (ρ_ (toOver W)).hom := by
  rw [← cancel_epi (ρ_ (toOver W)).inv]
  rw [← Category.assoc, Iso.inv_hom_id]
  apply Over.OverMorphism.ext
  change (((ρ_ (toOver W)).inv ≫
        (toOver W ◁ infinitySectionOver W)).left) ≫
      projectiveAdditionMorphism W = 𝟙 (scheme W)
  rw [categoricalRightUnitInsertion_left]
  convert projectiveRightUnitInsertion_comp_addition W using 1
  constructor <;> intro h <;> exact h

/-! ## Commutativity on the dense secant-output chart -/

/-- Swapping the two inputs negates Mathlib's raw homogeneous secant triple.
The common factor `-1` disappears after projective normalization. -/
private theorem projectiveAddXYZ_swap
    {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (P Q : Fin 3 → R) :
    W.toProjective.addXYZ Q P = -W.toProjective.addXYZ P Q := by
  funext j
  fin_cases j <;>
    simp [WeierstrassCurve.Projective.addXYZ,
      WeierstrassCurve.Projective.addX,
      WeierstrassCurve.Projective.addY,
      WeierstrassCurve.Projective.negAddY,
      WeierstrassCurve.Projective.addZ,
      WeierstrassCurve.Projective.negY] <;>
    ring

/-- Swap the two tensor factors of the standard-by-standard chart ring. -/
private noncomputable def standardPairSwapAlgEquiv
    (W : WeierstrassCurve K) :
    projectivePairChartCoordinateRing W (true, true) ≃ₐ[K]
      projectivePairChartCoordinateRing W (true, true) :=
  Algebra.TensorProduct.comm K
    (coveringChartCoordinateRing W true)
    (coveringChartCoordinateRing W true)

@[simp]
private theorem standardPairSwapAlgEquiv_firstUniversalPoint
    (W : WeierstrassCurve K) (j : Fin 3) :
    standardPairSwapAlgEquiv W
        (projectivePairChartFirstUniversalPoint W (true, true) j) =
      projectivePairChartSecondUniversalPoint W (true, true) j := by
  simp [standardPairSwapAlgEquiv,
    projectivePairChartFirstUniversalPoint,
    projectivePairChartSecondUniversalPoint,
    Algebra.TensorProduct.includeLeft,
    Algebra.TensorProduct.includeRight]

@[simp]
private theorem standardPairSwapAlgEquiv_secondUniversalPoint
    (W : WeierstrassCurve K) (j : Fin 3) :
    standardPairSwapAlgEquiv W
        (projectivePairChartSecondUniversalPoint W (true, true) j) =
      projectivePairChartFirstUniversalPoint W (true, true) j := by
  simp [standardPairSwapAlgEquiv,
    projectivePairChartFirstUniversalPoint,
    projectivePairChartSecondUniversalPoint,
    Algebra.TensorProduct.includeLeft,
    Algebra.TensorProduct.includeRight]

private theorem standardPairSwapAlgEquiv_additionCoordinates
    (W : WeierstrassCurve K) (j : Fin 3) :
    standardPairSwapAlgEquiv W
        (projectivePairChartAdditionCoordinates W (true, true) j) =
      -projectivePairChartAdditionCoordinates W (true, true) j := by
  let f := (standardPairSwapAlgEquiv W).toRingHom
  let P := projectivePairChartFirstUniversalPoint W (true, true)
  let Q := projectivePairChartSecondUniversalPoint W (true, true)
  have hmap := congrFun
    (WeierstrassCurve.Projective.map_addXYZ
      (W' := projectivePairChartMappedCurve W (true, true))
      (P := P) (Q := Q) f) j
  have hcurve :
      (projectivePairChartMappedCurve W (true, true)).map f =
        projectivePairChartMappedCurve W (true, true) := by
    rw [projectivePairChartMappedCurve, WeierstrassCurve.map_map]
    congr 1
    ext r
    exact (standardPairSwapAlgEquiv W).commutes r
  have hP : f ∘ P = Q := by
    funext k
    exact standardPairSwapAlgEquiv_firstUniversalPoint W k
  have hQ : f ∘ Q = P := by
    funext k
    exact standardPairSwapAlgEquiv_secondUniversalPoint W k
  change
    ((projectivePairChartMappedCurve W (true, true)).map f).toProjective.addXYZ
        (f ∘ P) (f ∘ Q) j =
      (f ∘ (projectivePairChartMappedCurve W
        (true, true)).toProjective.addXYZ P Q) j at hmap
  rw [hcurve, hP, hQ, projectiveAddXYZ_swap] at hmap
  simpa [P, Q, f, projectivePairChartAdditionCoordinates] using hmap.symm

/-- The tensor-factor swap extends across the standard-pair raw output-`Z`
localization, since it sends the inverted coordinate to its negative. -/
private noncomputable def standardPairOutputZSwapAlgHom
    (W : WeierstrassCurve K) :
    projectivePairChartAdditionOutputRing W (true, true) true →ₐ[K]
      projectivePairChartAdditionOutputRing W (true, true) true :=
  IsLocalization.Away.liftAlgHom
    (projectivePairChartAdditionCoordinates W (true, true)
      (coveringCoordinate true))
    (f := (IsScalarTower.toAlgHom K
      (projectivePairChartCoordinateRing W (true, true))
      (projectivePairChartAdditionOutputRing W (true, true) true)).comp
        (standardPairSwapAlgEquiv W).toAlgHom) (by
      change IsUnit (algebraMap
        (projectivePairChartCoordinateRing W (true, true))
        (projectivePairChartAdditionOutputRing W (true, true) true)
        (standardPairSwapAlgEquiv W
          (projectivePairChartAdditionCoordinates W (true, true)
            (coveringCoordinate true))))
      rw [standardPairSwapAlgEquiv_additionCoordinates, map_neg]
      exact (IsLocalization.Away.algebraMap_isUnit
        (projectivePairChartAdditionCoordinates W (true, true)
          (coveringCoordinate true))).neg)

@[simp]
private theorem standardPairOutputZSwapAlgHom_algebraMap
    (W : WeierstrassCurve K)
    (a : projectivePairChartCoordinateRing W (true, true)) :
    standardPairOutputZSwapAlgHom W
        (algebraMap (projectivePairChartCoordinateRing W (true, true))
          (projectivePairChartAdditionOutputRing W (true, true) true) a) =
      algebraMap (projectivePairChartCoordinateRing W (true, true))
        (projectivePairChartAdditionOutputRing W (true, true) true)
        (standardPairSwapAlgEquiv W a) := by
  simp [standardPairOutputZSwapAlgHom,
    IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]

private theorem standardPairOutputZSwapAlgHom_outputPoint
    (W : WeierstrassCurve K) [W.IsElliptic] (j : Fin 3) :
    standardPairOutputZSwapAlgHom W
        (projectivePairChartAdditionOutputPoint W (true, true) true j) =
      projectivePairChartAdditionOutputPoint W (true, true) true j := by
  rw [projectivePairChartAdditionOutputPoint, map_mul,
    standardPairOutputZSwapAlgHom_algebraMap,
    standardPairSwapAlgEquiv_additionCoordinates, map_neg]
  let u := projectivePairChartAdditionOutputUnit W (true, true) true
  have hunit : standardPairOutputZSwapAlgHom W (↑u) = -(↑u) := by
    unfold u projectivePairChartAdditionOutputUnit
    rw [IsUnit.unit_spec,
      standardPairOutputZSwapAlgHom_algebraMap,
      standardPairSwapAlgEquiv_additionCoordinates, map_neg]
  have hinv : standardPairOutputZSwapAlgHom W (↑u⁻¹) = -(↑u⁻¹) := by
    have hu : Units.map (standardPairOutputZSwapAlgHom W).toMonoidHom u =
        -u := by
      apply Units.ext
      exact hunit
    have hi := congrArg Inv.inv hu
    have hiv := congrArg Units.val hi
    simpa using hiv
  rw [hinv]
  ring

private theorem standardPairOutputZSwapAlgHom_comp_outputAlgHom
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (standardPairOutputZSwapAlgHom W).comp
        (projectivePairChartAdditionOutputAlgHom W
          (true, true) true) =
      projectivePairChartAdditionOutputAlgHom W (true, true) true := by
  apply AlgHom.coe_ringHom_injective
  apply Ideal.Quotient.ringHom_ext
  apply chartRingHom_ext (K := K) (coveringCoordinate true)
  · ext a
    change standardPairOutputZSwapAlgHom W
        (projectivePairChartAdditionOutputAlgHom W (true, true) true
          (coveringChartStructureRingHom W true a)) =
      projectivePairChartAdditionOutputAlgHom W (true, true) true
        (coveringChartStructureRingHom W true a)
    rw [← coveringChartCoordinateRing_algebraMap,
      (projectivePairChartAdditionOutputAlgHom W
        (true, true) true).commutes,
      (standardPairOutputZSwapAlgHom W).commutes]
  · intro j
    change standardPairOutputZSwapAlgHom W
        (projectivePairChartAdditionOutputAlgHom W (true, true) true
          (Ideal.Quotient.mk (coveringChartIdeal W true)
            (coordinateChartRatio (coveringCoordinate true) j))) = _
    calc
      _ = standardPairOutputZSwapAlgHom W
          (projectivePairChartAdditionOutputPoint W
            (true, true) true j) := by
        rw [projectivePairChartAdditionOutputAlgHom_ratio]
      _ = projectivePairChartAdditionOutputPoint W
          (true, true) true j :=
        standardPairOutputZSwapAlgHom_outputPoint W j
      _ = _ := (projectivePairChartAdditionOutputAlgHom_ratio W
        (true, true) true j).symm

/-- Scheme endomorphism of the raw output-`Z` open induced by swapping the
two standard-chart inputs. -/
private noncomputable def standardPairOutputZSwap
    (W : WeierstrassCurve K) :
    Spec (.of (projectivePairChartAdditionOutputRing W
      (true, true) true)) ⟶
      Spec (.of (projectivePairChartAdditionOutputRing W
        (true, true) true)) :=
  Spec.map (CommRingCat.ofHom
    (standardPairOutputZSwapAlgHom W).toRingHom)

private theorem standardPairOutputZSwap_comp_outputMorphism
    (W : WeierstrassCurve K) [W.IsElliptic] :
    standardPairOutputZSwap W ≫
        projectivePairChartAdditionOutputMorphism W (true, true) true =
      projectivePairChartAdditionOutputMorphism W (true, true) true := by
  rw [standardPairOutputZSwap,
    projectivePairChartAdditionOutputMorphism, ← Category.assoc,
    ← Spec.map_comp]
  have hring := standardPairOutputZSwapAlgHom_comp_outputAlgHom W
  have hring' :
      (standardPairOutputZSwapAlgHom W).toRingHom.comp
          (projectivePairChartAdditionOutputAlgHom W
            (true, true) true).toRingHom =
        (projectivePairChartAdditionOutputAlgHom W
          (true, true) true).toRingHom := by
    exact congrArg AlgHom.toRingHom hring
  change Spec.map (CommRingCat.ofHom
      ((standardPairOutputZSwapAlgHom W).toRingHom.comp
        (projectivePairChartAdditionOutputAlgHom W
          (true, true) true).toRingHom)) ≫
      coveringChartMap W true =
    Spec.map (CommRingCat.ofHom
      (projectivePairChartAdditionOutputAlgHom W
        (true, true) true).toRingHom) ≫ coveringChartMap W true
  rw [hring']

@[simp]
private theorem standardPairOutputZSwapAlgHom_includeLeft
    (W : WeierstrassCurve K)
    (a : coveringChartCoordinateRing W true) :
    standardPairOutputZSwapAlgHom W
        (algebraMap (projectivePairChartCoordinateRing W (true, true))
          (projectivePairChartAdditionOutputRing W (true, true) true)
          (Algebra.TensorProduct.includeLeft (S := K) a)) =
      algebraMap (projectivePairChartCoordinateRing W (true, true))
        (projectivePairChartAdditionOutputRing W (true, true) true)
        (Algebra.TensorProduct.includeRight a) := by
  rw [standardPairOutputZSwapAlgHom_algebraMap]
  simp [standardPairSwapAlgEquiv,
    Algebra.TensorProduct.includeLeft,
    Algebra.TensorProduct.includeRight]

@[simp]
private theorem standardPairOutputZSwapAlgHom_includeRight
    (W : WeierstrassCurve K)
    (a : coveringChartCoordinateRing W true) :
    standardPairOutputZSwapAlgHom W
        (algebraMap (projectivePairChartCoordinateRing W (true, true))
          (projectivePairChartAdditionOutputRing W (true, true) true)
          (Algebra.TensorProduct.includeRight a)) =
      algebraMap (projectivePairChartCoordinateRing W (true, true))
        (projectivePairChartAdditionOutputRing W (true, true) true)
        (Algebra.TensorProduct.includeLeft (S := K) a) := by
  rw [standardPairOutputZSwapAlgHom_algebraMap]
  simp [standardPairSwapAlgEquiv,
    Algebra.TensorProduct.includeLeft,
    Algebra.TensorProduct.includeRight]

private theorem standardPairOutputZSwap_comp_open_comp_firstInput
    (W : WeierstrassCurve K) :
    (standardPairOutputZSwap W ≫
        projectivePairChartAdditionOutputOpen W (true, true) true) ≫
        projectivePairChartFirstInput W (true, true) =
      projectivePairChartAdditionOutputOpen W (true, true) true ≫
        projectivePairChartSecondInput W (true, true) := by
  simp only [standardPairOutputZSwap,
    projectivePairChartAdditionOutputOpen,
    projectivePairChartFirstInput, projectivePairChartSecondInput,
    projectivePairChartMorphismOfCoordinateRingHom,
    Category.assoc, Iso.inv_hom_id_assoc]
  simp only [← Category.assoc]
  apply congrArg (fun f ↦ f ≫ coveringChartMap W true)
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp,
    Spec.map_inj]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact standardPairOutputZSwapAlgHom_includeLeft W a

private theorem standardPairOutputZSwap_comp_open_comp_secondInput
    (W : WeierstrassCurve K) :
    (standardPairOutputZSwap W ≫
        projectivePairChartAdditionOutputOpen W (true, true) true) ≫
        projectivePairChartSecondInput W (true, true) =
      projectivePairChartAdditionOutputOpen W (true, true) true ≫
        projectivePairChartFirstInput W (true, true) := by
  simp only [standardPairOutputZSwap,
    projectivePairChartAdditionOutputOpen,
    projectivePairChartFirstInput, projectivePairChartSecondInput,
    projectivePairChartMorphismOfCoordinateRingHom,
    Category.assoc, Iso.inv_hom_id_assoc]
  simp only [← Category.assoc]
  apply congrArg (fun f ↦ f ≫ coveringChartMap W true)
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp,
    Spec.map_inj]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact standardPairOutputZSwapAlgHom_includeRight W a

/-! ## The localized swap and the global product braiding -/

/-- The symmetry of the projective fibre square, before packaging it in the
slice category. -/
private noncomputable def projectivePairSwap
    (W : WeierstrassCurve K) :
    projectivePair W ⟶ projectivePair W :=
  (pullbackSymmetry (structureMap W) (structureMap W)).hom

@[reassoc]
private theorem projectivePairSwap_fst
    (W : WeierstrassCurve K) :
    projectivePairSwap W ≫
        pullback.fst (structureMap W) (structureMap W) =
      pullback.snd (structureMap W) (structureMap W) := by
  exact pullbackSymmetry_hom_comp_fst _ _

@[reassoc]
private theorem projectivePairSwap_snd
    (W : WeierstrassCurve K) :
    projectivePairSwap W ≫
        pullback.snd (structureMap W) (structureMap W) =
      pullback.fst (structureMap W) (structureMap W) := by
  exact pullbackSymmetry_hom_comp_snd _ _

/-- On the raw output-`Z` open, the tensor-factor involution is the
restriction of the global symmetry of the projective fibre square. -/
private theorem standardPairOutputZSwap_comp_globalChart
    (W : WeierstrassCurve K) :
    (standardPairOutputZSwap W ≫
        projectivePairChartAdditionOutputOpen W (true, true) true) ≫
        projectivePairChartMap W (true, true) =
      (projectivePairChartAdditionOutputOpen W (true, true) true ≫
        projectivePairChartMap W (true, true)) ≫
        projectivePairSwap W := by
  apply pullback.hom_ext
  · calc
      _ = (standardPairOutputZSwap W ≫
            projectivePairChartAdditionOutputOpen W (true, true) true) ≫
          projectivePairChartFirstInput W (true, true) := by
            rw [Category.assoc, projectivePairChartMap_comp_fst,
              ← projectivePairChartFirstInput_eq]
      _ = projectivePairChartAdditionOutputOpen W (true, true) true ≫
          projectivePairChartSecondInput W (true, true) :=
        standardPairOutputZSwap_comp_open_comp_firstInput W
      _ = projectivePairChartAdditionOutputOpen W (true, true) true ≫
          (projectivePairChartMap W (true, true) ≫
            pullback.snd (structureMap W) (structureMap W)) := by
              rw [projectivePairChartMap_comp_snd,
                ← projectivePairChartSecondInput_eq]
      _ = (projectivePairChartAdditionOutputOpen W (true, true) true ≫
            projectivePairChartMap W (true, true)) ≫
          pullback.snd (structureMap W) (structureMap W) :=
        (Category.assoc _ _ _).symm
      _ = (projectivePairChartAdditionOutputOpen W (true, true) true ≫
            projectivePairChartMap W (true, true)) ≫
          (projectivePairSwap W ≫
            pullback.fst (structureMap W) (structureMap W)) := by
              rw [projectivePairSwap_fst]
      _ = ((projectivePairChartAdditionOutputOpen W (true, true) true ≫
              projectivePairChartMap W (true, true)) ≫
            projectivePairSwap W) ≫
          pullback.fst (structureMap W) (structureMap W) :=
        (Category.assoc _ _ _).symm
  · calc
      _ = (standardPairOutputZSwap W ≫
            projectivePairChartAdditionOutputOpen W (true, true) true) ≫
          projectivePairChartSecondInput W (true, true) := by
            rw [Category.assoc, projectivePairChartMap_comp_snd,
              ← projectivePairChartSecondInput_eq]
      _ = projectivePairChartAdditionOutputOpen W (true, true) true ≫
          projectivePairChartFirstInput W (true, true) :=
        standardPairOutputZSwap_comp_open_comp_secondInput W
      _ = projectivePairChartAdditionOutputOpen W (true, true) true ≫
          (projectivePairChartMap W (true, true) ≫
            pullback.fst (structureMap W) (structureMap W)) := by
              rw [projectivePairChartMap_comp_fst,
                ← projectivePairChartFirstInput_eq]
      _ = (projectivePairChartAdditionOutputOpen W (true, true) true ≫
            projectivePairChartMap W (true, true)) ≫
          pullback.fst (structureMap W) (structureMap W) :=
        (Category.assoc _ _ _).symm
      _ = (projectivePairChartAdditionOutputOpen W (true, true) true ≫
            projectivePairChartMap W (true, true)) ≫
          (projectivePairSwap W ≫
            pullback.snd (structureMap W) (structureMap W)) := by
              rw [projectivePairSwap_snd]
      _ = ((projectivePairChartAdditionOutputOpen W (true, true) true ≫
              projectivePairChartMap W (true, true)) ≫
            projectivePairSwap W) ≫
          pullback.snd (structureMap W) (structureMap W) :=
        (Category.assoc _ _ _).symm

private theorem standardPairOutputZ_swapped_addition_eq
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (projectivePairChartAdditionOutputOpen W (true, true) true ≫
        projectivePairChartMap W (true, true)) ≫
        (projectivePairSwap W ≫ projectiveAdditionMorphism W) =
      (projectivePairChartAdditionOutputOpen W (true, true) true ≫
        projectivePairChartMap W (true, true)) ≫
        projectiveAdditionMorphism W := by
  calc
    _ = ((projectivePairChartAdditionOutputOpen W (true, true) true ≫
            projectivePairChartMap W (true, true)) ≫
          projectivePairSwap W) ≫
        projectiveAdditionMorphism W :=
      (Category.assoc _ _ _).symm
    _ = ((standardPairOutputZSwap W ≫
            projectivePairChartAdditionOutputOpen W (true, true) true) ≫
          projectivePairChartMap W (true, true)) ≫
        projectiveAdditionMorphism W := by
          rw [standardPairOutputZSwap_comp_globalChart]
    _ = (standardPairOutputZSwap W ≫
          projectivePairChartAdditionOutputOpen W (true, true) true) ≫
        (projectivePairChartMap W (true, true) ≫
          projectiveAdditionMorphism W) := Category.assoc _ _ _
    _ = (standardPairOutputZSwap W ≫
          projectivePairChartAdditionOutputOpen W (true, true) true) ≫
        standardPairAdditionMorphism W := by
          rw [projectivePairStandardChart_comp_projectiveAdditionMorphism]
    _ = standardPairOutputZSwap W ≫
        (projectivePairChartAdditionOutputOpen W (true, true) true ≫
          standardPairAdditionMorphism W) := Category.assoc _ _ _
    _ = standardPairOutputZSwap W ≫
        projectivePairChartAdditionOutputMorphism W
          (true, true) true := by
            rw [projectivePairStandardOutputOpen_comp_standardPairAdditionMorphism]
    _ = projectivePairChartAdditionOutputMorphism W
          (true, true) true :=
      standardPairOutputZSwap_comp_outputMorphism W
    _ = projectivePairChartAdditionOutputOpen W (true, true) true ≫
        standardPairAdditionMorphism W :=
      (projectivePairStandardOutputOpen_comp_standardPairAdditionMorphism W).symm
    _ = projectivePairChartAdditionOutputOpen W (true, true) true ≫
        (projectivePairChartMap W (true, true) ≫
          projectiveAdditionMorphism W) := by
            rw [projectivePairStandardChart_comp_projectiveAdditionMorphism]
    _ = (projectivePairChartAdditionOutputOpen W (true, true) true ≫
          projectivePairChartMap W (true, true)) ≫
        projectiveAdditionMorphism W := (Category.assoc _ _ _).symm

/-- The nonempty standard-pair output-`Z` principal open used to extend
commutativity to the whole integral projective pair. -/
private noncomputable def standardPairOutputZToProjectivePair
    (W : WeierstrassCurve K) :
    Spec (.of (projectivePairChartAdditionOutputRing W
      (true, true) true)) ⟶ projectivePair W :=
  projectivePairChartAdditionOutputOpen W (true, true) true ≫
    projectivePairChartMap W (true, true)

private instance standardPairOutputZToProjectivePair_isOpenImmersion
    (W : WeierstrassCurve K) :
    IsOpenImmersion (standardPairOutputZToProjectivePair W) := by
  dsimp only [standardPairOutputZToProjectivePair]
  infer_instance

private noncomputable instance standardPairOutputZ_nonempty
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Nonempty (Spec (.of
      (projectivePairChartAdditionOutputRing W (true, true) true))) := by
  change Nonempty (Spec (.of (Localization.Away
    (projectivePairChartAdditionCoordinates W (true, true) (2 : Fin 3)))))
  letI : IsDomain (projectivePairChartCoordinateRing W (true, true)) :=
    projectivePairChartCoordinateRing_isDomain W (true, true)
  letI : Nontrivial (projectivePairChartCoordinateRing W (true, true)) :=
    (projectivePairChartCoordinateRing_isDomain W
      (true, true)).toNontrivial
  have hinj : Function.Injective
      (algebraMap (projectivePairChartCoordinateRing W (true, true))
        (Localization.Away
          (projectivePairChartAdditionCoordinates W
            (true, true) (2 : Fin 3)))) :=
    IsLocalization.injective
      (Localization.Away
        (projectivePairChartAdditionCoordinates W
          (true, true) (2 : Fin 3)))
      (powers_le_nonZeroDivisors_of_noZeroDivisors
        (standardPairRawOutputZ_ne_zero W))
  letI : Nontrivial
      (Localization.Away
        (projectivePairChartAdditionCoordinates W
          (true, true) (2 : Fin 3))) :=
    hinj.nontrivial
  exact PrimeSpectrum.nonempty_iff_nontrivial.mpr inferInstance

private theorem projectivePairSwap_comp_structureMap
    (W : WeierstrassCurve K) :
    projectivePairSwap W ≫ projectivePairStructureMap W =
      projectivePairStructureMap W := by
  rw [projectivePairStructureMap, ← Category.assoc,
    projectivePairSwap_fst]
  exact pullback.condition.symm

/-- The globally glued projective addition is invariant under exchanging its
two inputs. -/
private theorem projectivePairSwap_comp_addition
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectivePairSwap W ≫ projectiveAdditionMorphism W =
      projectiveAdditionMorphism W := by
  letI : IsIntegral (scheme W) :=
    GeometricallyIntegral.isIntegral_of_subsingleton (structureMap W)
  letI : Flat (structureMap W) := by infer_instance
  letI : UniversallyOpen (structureMap W) := by infer_instance
  letI : LocallyOfFiniteType (structureMap W) := by infer_instance
  letI : IsLocallyNoetherian (scheme W) :=
    LocallyOfFiniteType.isLocallyNoetherian (structureMap W)
  letI : IsIntegral (projectivePair W) := by infer_instance
  letI : IsDominant (standardPairOutputZToProjectivePair W) := by
    constructor
    have hopen :=
      (standardPairOutputZToProjectivePair W).isOpenEmbedding.isOpenMap
    exact hopen.denseRange_of_isPreirreducibleSpace _
  apply ext_of_isDominant_of_isSeparated
    (s := structureMap W) (ι := standardPairOutputZToProjectivePair W)
  · calc
      (projectivePairSwap W ≫ projectiveAdditionMorphism W) ≫
          structureMap W =
        projectivePairSwap W ≫
          (projectiveAdditionMorphism W ≫ structureMap W) :=
            Category.assoc _ _ _
      _ = projectivePairSwap W ≫ projectivePairStructureMap W := by
        rw [projectiveAdditionMorphism_comp_structureMap]
      _ = projectivePairStructureMap W :=
        projectivePairSwap_comp_structureMap W
      _ = projectiveAdditionMorphism W ≫ structureMap W :=
        (projectiveAdditionMorphism_comp_structureMap W).symm
  · exact standardPairOutputZ_swapped_addition_eq W

/-! ## The inverse axis -/

/-- The vertical derivative at the universal affine point.  It is also the
raw `Y`-coordinate, up to sign, of the projective sum of that point and its
Weierstrass inverse. -/
private noncomputable def standardVerticalDerivative
    (W : WeierstrassCurve K) : secantTargetCoordinateRing W :=
  (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃) •
      (1 : W.toAffine.CoordinateRing) +
    Polynomial.C (2 : K) •
      WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine Polynomial.X

/-- Ellipticity prevents the universal vertical derivative from vanishing
identically on the standard affine chart. -/
private theorem standardVerticalDerivative_ne_zero
    (W : WeierstrassCurve K) [W.IsElliptic] :
    standardVerticalDerivative W ≠ 0 := by
  intro h
  obtain ⟨hp, hq⟩ :=
    WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero h
  have htwo : (2 : K) = 0 := by
    exact Polynomial.C_eq_zero.mp hq
  have ha₁ : W.a₁ = 0 := by
    simpa using congrArg (fun p : Polynomial K ↦ p.coeff 1) hp
  have ha₃ : W.a₃ = 0 := by
    simpa [ha₁] using congrArg (fun p : Polynomial K ↦ p.coeff 0) hp
  letI : CharP K 2 :=
    CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero htwo
  apply W.isUnit_Δ.ne_zero
  rw [W.Δ_of_char_two, ha₁, ha₃]
  simp

/-- The vertical derivative transported to the standard projective-chart
coordinate ring. -/
private noncomputable def standardChartVerticalDerivative
    (W : WeierstrassCurve K) : coveringChartCoordinateRing W true :=
  standardAffineChartAlgEquiv W (standardVerticalDerivative W)

private theorem standardChartVerticalDerivative_ne_zero
    (W : WeierstrassCurve K) [W.IsElliptic] :
    standardChartVerticalDerivative W ≠ 0 := by
  simpa [standardChartVerticalDerivative] using
    (standardAffineChartAlgEquiv W).injective.ne
      (standardVerticalDerivative_ne_zero W)

private theorem standardVerticalDerivative_eq_coordinateExpression
    (W : WeierstrassCurve K) :
    standardVerticalDerivative W =
      2 * secantTargetY W +
        secantTargetCoefficientHom W W.a₁ * secantTargetX W +
        secantTargetCoefficientHom W W.a₃ := by
  have hmk :
      (Ideal.Quotient.mk (Ideal.span {W.toAffine.polynomial})) =
        WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine := rfl
  simp only [standardVerticalDerivative,
    WeierstrassCurve.Affine.CoordinateRing.smul,
    secantTargetY, secantTargetX, secantTargetCoefficientHom,
    RingHom.comp_apply, map_add, map_mul, map_ofNat,
    mul_one]
  rw [hmk]
  exact (add_comm _ _).trans (add_assoc _ _ _).symm

private theorem standardChartVerticalDerivative_eq_pointExpression
    (W : WeierstrassCurve K) :
    standardChartVerticalDerivative W =
      coveringChartUniversalPoint W true 1 -
        (W.map (algebraMap K
          (coveringChartCoordinateRing W true))).toProjective.negY
            (coveringChartUniversalPoint W true) := by
  rw [standardChartVerticalDerivative,
    standardVerticalDerivative_eq_coordinateExpression]
  simp only [map_add, map_mul, map_ofNat]
  rw [
    standardAffineChartAlgEquiv_X,
    standardAffineChartAlgEquiv_Y]
  rw [secantTargetCoefficientHom_eq_algebraMap]
  rw [(standardAffineChartAlgEquiv W).commutes]
  rw [(standardAffineChartAlgEquiv W).commutes]
  simp only [WeierstrassCurve.Projective.negY]
  have hPz : coveringChartUniversalPoint W true 2 = 1 := by
    simpa only [coveringCoordinate] using
      coveringChartUniversalPoint_normalized W true
  rw [hPz]
  simp only [WeierstrassCurve.map]
  ring

/-- The inverse of the normalized universal point on the standard chart. -/
private noncomputable def standardChartNegatedUniversalPoint
    (W : WeierstrassCurve K) :
    Fin 3 → coveringChartCoordinateRing W true :=
  (W.map (algebraMap K (coveringChartCoordinateRing W true))).toProjective.neg
    (coveringChartUniversalPoint W true)

@[simp]
private theorem standardChartNegatedUniversalPoint_normalized
    (W : WeierstrassCurve K) :
    standardChartNegatedUniversalPoint W (2 : Fin 3) = 1 := by
  rw [standardChartNegatedUniversalPoint,
    WeierstrassCurve.Projective.neg_Z]
  simpa only [coveringCoordinate] using
    coveringChartUniversalPoint_normalized W true

private theorem standardChartNegatedUniversalPoint_equation
    (W : WeierstrassCurve K) :
    (W.map (algebraMap K
      (coveringChartCoordinateRing W true))).toProjective.Equation
        (standardChartNegatedUniversalPoint W) := by
  let W' := W.map (algebraMap K (coveringChartCoordinateRing W true))
  let P := coveringChartUniversalPoint W true
  have hP : W'.toProjective.Equation P := by
    exact coveringChartUniversalPoint_equation W true
  have hPz : P 2 = 1 := by
    simpa only [coveringCoordinate] using
      coveringChartUniversalPoint_normalized W true
  have hP' : P = ![P 0, P 1, 1] := by
    funext j
    fin_cases j
    · rfl
    · rfl
    · exact hPz
  rw [hP'] at hP
  have hneg : W'.toProjective.Equation
      ![P 0, W'.toAffine.negY (P 0) (P 1), 1] := by
    rw [W'.toProjective.equation_some,
      W'.toAffine.equation_neg]
    exact W'.toProjective.equation_some (P 0) (P 1) |>.mp hP
  rw [standardChartNegatedUniversalPoint]
  change W'.toProjective.Equation (W'.toProjective.neg P)
  convert hneg using 1
  funext j
  fin_cases j
  · rfl
  · simp [WeierstrassCurve.Projective.neg,
      WeierstrassCurve.Projective.negY,
      WeierstrassCurve.Affine.negY,
      hPz]
  · exact hPz

/-- Pullback on the standard chart induced by Weierstrass negation. -/
private noncomputable def standardChartNegationAlgHom
    (W : WeierstrassCurve K) :
    coveringChartCoordinateRing W true →ₐ[K]
      coveringChartCoordinateRing W true :=
  coveringChartCoordinateRingAlgHomOfNormalizedPoint W true
    (standardChartNegatedUniversalPoint W)
    (standardChartNegatedUniversalPoint_equation W)
    (standardChartNegatedUniversalPoint_normalized W)

@[simp]
private theorem standardChartNegationAlgHom_universalPoint
    (W : WeierstrassCurve K) (j : Fin 3) :
    standardChartNegationAlgHom W
        (coveringChartUniversalPoint W true j) =
      standardChartNegatedUniversalPoint W j := by
  exact coveringChartCoordinateRingAlgHomOfNormalizedPoint_ratio
    W true (standardChartNegatedUniversalPoint W)
      (standardChartNegatedUniversalPoint_equation W)
      (standardChartNegatedUniversalPoint_normalized W) j

/-- The standard-chart graph `P ↦ (P, -P)` on coordinate rings. -/
private noncomputable def inverseChartPairAlgHom
    (W : WeierstrassCurve K) :
    projectivePairChartCoordinateRing W (true, true) →ₐ[K]
      coveringChartCoordinateRing W true :=
  Algebra.TensorProduct.lift
    (AlgHom.id K (coveringChartCoordinateRing W true))
    (standardChartNegationAlgHom W)
    (fun _ _ ↦ Commute.all _ _)

@[simp]
private theorem inverseChartPairAlgHom_firstUniversalPoint
    (W : WeierstrassCurve K) (j : Fin 3) :
    inverseChartPairAlgHom W
        (projectivePairChartFirstUniversalPoint W (true, true) j) =
      coveringChartUniversalPoint W true j := by
  simp [inverseChartPairAlgHom,
    projectivePairChartFirstUniversalPoint]

@[simp]
private theorem inverseChartPairAlgHom_secondUniversalPoint
    (W : WeierstrassCurve K) (j : Fin 3) :
    inverseChartPairAlgHom W
        (projectivePairChartSecondUniversalPoint W (true, true) j) =
      standardChartNegatedUniversalPoint W j := by
  simp [inverseChartPairAlgHom,
    projectivePairChartSecondUniversalPoint]

/-- The raw addition triple on the inverse graph is the vertical derivative
multiple of the projective origin. -/
private theorem inverseChartPairAlgHom_additionCoordinates
    (W : WeierstrassCurve K) (j : Fin 3) :
    inverseChartPairAlgHom W
        (projectivePairChartAdditionCoordinates W (true, true) j) =
      (-((W.map (algebraMap K
          (coveringChartCoordinateRing W true))).toProjective.dblZ
            (coveringChartUniversalPoint W true)) •
        (![0, 1, 0] : Fin 3 →
          coveringChartCoordinateRing W true)) j := by
  let f := (inverseChartPairAlgHom W).toRingHom
  let P := projectivePairChartFirstUniversalPoint W (true, true)
  let Q := projectivePairChartSecondUniversalPoint W (true, true)
  have hmap := congrFun
    (WeierstrassCurve.Projective.map_addXYZ
      (W' := projectivePairChartMappedCurve W (true, true))
      (P := P) (Q := Q) f) j
  have hcurve :
      (projectivePairChartMappedCurve W (true, true)).map f =
        W.map (algebraMap K (coveringChartCoordinateRing W true)) := by
    rw [projectivePairChartMappedCurve, WeierstrassCurve.map_map]
    congr 1
    ext r
    exact (inverseChartPairAlgHom W).commutes r
  have hP : f ∘ P = coveringChartUniversalPoint W true := by
    funext k
    exact inverseChartPairAlgHom_firstUniversalPoint W k
  have hQ : f ∘ Q = standardChartNegatedUniversalPoint W := by
    funext k
    exact inverseChartPairAlgHom_secondUniversalPoint W k
  change
    ((projectivePairChartMappedCurve W (true, true)).map f).toProjective.addXYZ
        (f ∘ P) (f ∘ Q) j =
      (f ∘ (projectivePairChartMappedCurve W
        (true, true)).toProjective.addXYZ P Q) j at hmap
  rw [hcurve, hP, hQ] at hmap
  have hformula :=
    WeierstrassCurve.Projective.addXYZ_neg
      (W' := (W.map (algebraMap K
        (coveringChartCoordinateRing W true))).toProjective)
      (P := coveringChartUniversalPoint W true)
      (coveringChartUniversalPoint_equation W true)
  rw [show standardChartNegatedUniversalPoint W =
      (W.map (algebraMap K
        (coveringChartCoordinateRing W true))).toProjective.neg
          (coveringChartUniversalPoint W true) by rfl,
    hformula] at hmap
  simpa [P, Q, f, projectivePairChartAdditionCoordinates]
    using hmap.symm

private theorem standardChart_dblZ_eq_verticalDerivative_cube
    (W : WeierstrassCurve K) :
    (W.map (algebraMap K
      (coveringChartCoordinateRing W true))).toProjective.dblZ
        (coveringChartUniversalPoint W true) =
      standardChartVerticalDerivative W ^ 3 := by
  rw [WeierstrassCurve.Projective.dblZ,
    ← standardChartVerticalDerivative_eq_pointExpression]
  have hPz : coveringChartUniversalPoint W true 2 = 1 := by
    simpa only [coveringCoordinate] using
      coveringChartUniversalPoint_normalized W true
  rw [hPz, one_mul]

private theorem inverseChartPairAlgHom_additionY
    (W : WeierstrassCurve K) :
    inverseChartPairAlgHom W
        (projectivePairChartAdditionCoordinates W (true, true)
          (1 : Fin 3)) =
      -(standardChartVerticalDerivative W ^ 3) := by
  rw [inverseChartPairAlgHom_additionCoordinates,
    standardChart_dblZ_eq_verticalDerivative_cube]
  simp [Pi.smul_apply]

/-- The dense principal open of the standard chart on which the universal
vertical derivative is invertible. -/
private abbrev inverseChartOpenRing (W : WeierstrassCurve K) :=
  Localization.Away (standardChartVerticalDerivative W)

private abbrev inverseChartOpenScheme (W : WeierstrassCurve K) :=
  Spec (.of (inverseChartOpenRing W))

/-- The inverse graph followed by the canonical map to its derivative
principal open, on coordinate rings. -/
private noncomputable def inverseChartPairToOpenAlgHom
    (W : WeierstrassCurve K) :
    projectivePairChartCoordinateRing W (true, true) →ₐ[K]
      inverseChartOpenRing W :=
  (IsScalarTower.toAlgHom K
    (coveringChartCoordinateRing W true)
    (inverseChartOpenRing W)).comp (inverseChartPairAlgHom W)

@[simp]
private theorem inverseChartPairToOpenAlgHom_apply
    (W : WeierstrassCurve K)
    (a : projectivePairChartCoordinateRing W (true, true)) :
    inverseChartPairToOpenAlgHom W a =
      algebraMap (coveringChartCoordinateRing W true)
        (inverseChartOpenRing W) (inverseChartPairAlgHom W a) := by
  rfl

/-- The inverse graph lands in the raw output-`Y` open, because that output
becomes the negative cube of the inverted vertical derivative. -/
private noncomputable def inverseChartOutputAlgHom
    (W : WeierstrassCurve K) :
    projectivePairChartAdditionOutputRing W (true, true) false →ₐ[K]
      inverseChartOpenRing W :=
  IsLocalization.Away.liftAlgHom
    (projectivePairChartAdditionCoordinates W (true, true)
      (coveringCoordinate false))
    (f := inverseChartPairToOpenAlgHom W) (by
      change IsUnit (algebraMap
        (coveringChartCoordinateRing W true)
        (inverseChartOpenRing W)
        (inverseChartPairAlgHom W
          (projectivePairChartAdditionCoordinates W (true, true)
            (coveringCoordinate false))))
      rw [show coveringCoordinate false = (1 : Fin 3) by rfl,
        inverseChartPairAlgHom_additionY, map_neg, map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit
        (standardChartVerticalDerivative W)).pow 3 |>.neg)

@[simp]
private theorem inverseChartOutputAlgHom_algebraMap
    (W : WeierstrassCurve K)
    (a : projectivePairChartCoordinateRing W (true, true)) :
    inverseChartOutputAlgHom W
        (algebraMap (projectivePairChartCoordinateRing W (true, true))
          (projectivePairChartAdditionOutputRing W
            (true, true) false) a) =
      inverseChartPairToOpenAlgHom W a := by
  simp [inverseChartOutputAlgHom,
    IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]

private theorem inverseChartOutputAlgHom_outputPoint
    (W : WeierstrassCurve K) [W.IsElliptic] (j : Fin 3) :
    inverseChartOutputAlgHom W
        (projectivePairChartAdditionOutputPoint W
          (true, true) false j) =
      (![0, 1, 0] : Fin 3 → inverseChartOpenRing W) j := by
  fin_cases j
  · rw [projectivePairChartAdditionOutputPoint, map_mul,
      inverseChartOutputAlgHom_algebraMap,
      inverseChartPairToOpenAlgHom_apply,
      inverseChartPairAlgHom_additionCoordinates]
    simp [Pi.smul_apply]
  · have hnorm :=
      projectivePairChartAdditionOutputPoint_normalized W
        (true, true) false
    change inverseChartOutputAlgHom W
        (projectivePairChartAdditionOutputPoint W
          (true, true) false (coveringCoordinate false)) = 1
    rw [hnorm, map_one]
  · rw [projectivePairChartAdditionOutputPoint, map_mul,
      inverseChartOutputAlgHom_algebraMap,
      inverseChartPairToOpenAlgHom_apply,
      inverseChartPairAlgHom_additionCoordinates]
    simp [Pi.smul_apply]

private theorem inverseChartOutputAlgHom_comp_outputAlgHom
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (inverseChartOutputAlgHom W).comp
        (projectivePairChartAdditionOutputAlgHom W
          (true, true) false) =
      (Algebra.ofId K (inverseChartOpenRing W)).comp
        (coveringInfinityChartOriginAlgHom W) := by
  apply AlgHom.coe_ringHom_injective
  apply Ideal.Quotient.ringHom_ext
  apply chartRingHom_ext (K := K) (coveringCoordinate false)
  · ext a
    change inverseChartOutputAlgHom W
        (projectivePairChartAdditionOutputAlgHom W
          (true, true) false
          (coveringChartStructureRingHom W false a)) =
      (Algebra.ofId K (inverseChartOpenRing W))
        (coveringInfinityChartOriginAlgHom W
          (coveringChartStructureRingHom W false a))
    rw [← coveringChartCoordinateRing_algebraMap,
      (projectivePairChartAdditionOutputAlgHom W
        (true, true) false).commutes,
      (inverseChartOutputAlgHom W).commutes,
      (coveringInfinityChartOriginAlgHom W).commutes]
    rfl
  · intro j
    change inverseChartOutputAlgHom W
        (projectivePairChartAdditionOutputAlgHom W
          (true, true) false
          (Ideal.Quotient.mk (coveringChartIdeal W false)
            (coordinateChartRatio (coveringCoordinate false) j))) = _
    rw [projectivePairChartAdditionOutputAlgHom_ratio,
      inverseChartOutputAlgHom_outputPoint]
    change (![0, 1, 0] : Fin 3 → inverseChartOpenRing W) j =
      (Algebra.ofId K (inverseChartOpenRing W))
        (coveringInfinityChartOriginAlgHom W
          (coveringChartUniversalPoint W false j))
    rw [coveringInfinityChartOriginAlgHom_universalPoint]
    fin_cases j <;> simp

/-- The derivative principal open mapped to the standard chart. -/
private noncomputable def inverseChartOpenToStandardChart
    (W : WeierstrassCurve K) :
    inverseChartOpenScheme W ⟶ coveringChartScheme W true :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (coveringChartCoordinateRing W true)
      (inverseChartOpenRing W)))

private instance inverseChartOpenToStandardChart_isOpenImmersion
    (W : WeierstrassCurve K) :
    IsOpenImmersion (inverseChartOpenToStandardChart W) := by
  dsimp only [inverseChartOpenToStandardChart, inverseChartOpenRing]
  infer_instance

/-- The inverse graph on the derivative principal open, valued in the
standard projective-pair chart. -/
private noncomputable def inverseChartOpenToStandardPair
    (W : WeierstrassCurve K) :
    inverseChartOpenScheme W ⟶
      projectivePairChartScheme W (true, true) :=
  Spec.map (CommRingCat.ofHom
      (inverseChartPairToOpenAlgHom W).toRingHom) ≫
    (projectivePairChartIsoSpecTensor W (true, true)).inv

/-- The inverse graph factored through the standard-pair raw output-`Y`
principal open. -/
private noncomputable def inverseChartOpenToOutputOpen
    (W : WeierstrassCurve K) :
    inverseChartOpenScheme W ⟶
      Spec (.of (projectivePairChartAdditionOutputRing W
        (true, true) false)) :=
  Spec.map (CommRingCat.ofHom (inverseChartOutputAlgHom W).toRingHom)

private theorem inverseChartOpenToOutputOpen_comp_open
    (W : WeierstrassCurve K) :
    inverseChartOpenToOutputOpen W ≫
        projectivePairChartAdditionOutputOpen W
          (true, true) false =
      inverseChartOpenToStandardPair W := by
  apply (cancel_mono
    (projectivePairChartIsoSpecTensor W (true, true)).hom).1
  rw [Category.assoc,
    projectivePairChartAdditionOutputOpen_comp_iso_hom]
  rw [inverseChartOpenToOutputOpen,
    inverseChartOpenToStandardPair, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, ← Spec.map_comp]
  rw [Spec.map_inj]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact inverseChartOutputAlgHom_algebraMap W a

private theorem inverseChartOpenToOutputOpen_comp_addition
    (W : WeierstrassCurve K) [W.IsElliptic] :
    inverseChartOpenToOutputOpen W ≫
        projectivePairChartAdditionOutputMorphism W
          (true, true) false =
      Spec.map (CommRingCat.ofHom
          (algebraMap K (inverseChartOpenRing W))) ≫
        infinityChartOriginMorphism W ≫ coveringChartMap W false := by
  rw [inverseChartOpenToOutputOpen,
    projectivePairChartAdditionOutputMorphism, ← Category.assoc,
    ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
      (((inverseChartOutputAlgHom W).comp
        (projectivePairChartAdditionOutputAlgHom W
          (true, true) false)).toRingHom)) ≫
      coveringChartMap W false = _
  have hring := inverseChartOutputAlgHom_comp_outputAlgHom W
  rw [hring]
  rw [infinityChartOriginMorphism, ← Category.assoc,
    ← Spec.map_comp]
  rfl

private theorem negationGraded_standardCoordinate
    (W : WeierstrassCurve K) :
    negationGraded W (MvPolynomial.X (2 : Fin 3)) =
      MvPolynomial.X (2 : Fin 3) := by
  change negationRingHom W (MvPolynomial.X (2 : Fin 3)) = _
  simp [negationRingHom_X, negationCoordinates,
    WeierstrassCurve.Projective.neg]

private noncomputable def negationAwayMapOfEq
    (W : WeierstrassCurve K)
    (s s' : MvPolynomial (Fin 3) K)
    (hss : negationGraded W s = s') :
    HomogeneousLocalization.Away (homogeneousPieces K) s →+*
      HomogeneousLocalization.Away (homogeneousPieces K) s' :=
  hss ▸ HomogeneousLocalization.Away.map (negationGraded W) s

/-- The degree-zero standard-chart substitution induced directly by the
homogeneous negation map. -/
private noncomputable def standardNegationAwayRingHom
    (W : WeierstrassCurve K) :
    HomogeneousLocalization.Away (homogeneousPieces K)
        (MvPolynomial.X (2 : Fin 3)) →+*
    HomogeneousLocalization.Away (homogeneousPieces K)
      (MvPolynomial.X (2 : Fin 3)) :=
  negationAwayMapOfEq W
    (MvPolynomial.X (2 : Fin 3)) (MvPolynomial.X (2 : Fin 3))
    (negationGraded_standardCoordinate W)

/-- The standard-chart quotient map with its source written using the
literal homogeneous coordinate `Z = X 2`. -/
private noncomputable def standardChartQuotientRingHom
    (W : WeierstrassCurve K) :
    HomogeneousLocalization.Away (homogeneousPieces K)
        (MvPolynomial.X (2 : Fin 3)) →+*
      coveringChartCoordinateRing W true := by
  change coveringChartRing K true →+*
    coveringChartCoordinateRing W true
  exact Ideal.Quotient.mk (coveringChartIdeal W true)

@[simp]
private theorem standardChartQuotientRingHom_ratio
    (W : WeierstrassCurve K) (j : Fin 3) :
    standardChartQuotientRingHom W
        (coordinateChartRatio (K := K) (2 : Fin 3) j) =
      coveringChartUniversalPoint W true j := by
  rfl

private theorem standardChartQuotientRingHom_constant
    (W : WeierstrassCurve K) (a : K) :
    standardChartQuotientRingHom W
        (coordinateChartConstantHom (K := K) (2 : Fin 3) a) =
      algebraMap K (coveringChartCoordinateRing W true) a := by
  exact DFunLike.congr_fun
    (coveringChartCoordinateRing_algebraMap W true).symm a

private theorem negationAwayMap_mk
    (W : WeierstrassCurve K)
    (s s' : MvPolynomial (Fin 3) K)
    (hs : s ∈ homogeneousPieces K 1)
    (hs' : s' ∈ homogeneousPieces K 1)
    (hss : negationGraded W s = s') {n : ℕ}
    (q : MvPolynomial (Fin 3) K) (hq : q ∈ homogeneousPieces K n) :
    negationAwayMapOfEq W s s' hss
        (HomogeneousLocalization.Away.mk (homogeneousPieces K) hs n q
          (by simpa using hq)) =
      HomogeneousLocalization.Away.mk (homogeneousPieces K) hs' n
        (negationGraded W q)
        (by simpa using (negationGraded W).map_mem hq) := by
  unfold negationAwayMapOfEq
  cases hss
  rw [show hs' = (negationGraded W).map_mem hs from
    Subsingleton.elim _ _]
  simpa only using HomogeneousLocalization.Away.map_mk
    (negationGraded W) s hs n q (by simpa using hq)

private theorem standardNegationAwayRingHom_mk
    (W : WeierstrassCurve K) {n : ℕ}
    (q : MvPolynomial (Fin 3) K) (hq : q ∈ homogeneousPieces K n) :
    standardNegationAwayRingHom W
        (HomogeneousLocalization.Away.mk (homogeneousPieces K)
          (MvPolynomial.isHomogeneous_X K (2 : Fin 3)) n q
          (by simpa using hq)) =
      HomogeneousLocalization.Away.mk (homogeneousPieces K)
        (MvPolynomial.isHomogeneous_X K (2 : Fin 3)) n
        (negationGraded W q)
        (by simpa using (negationGraded W).map_mem hq) := by
  change (negationAwayMapOfEq W
      (MvPolynomial.X (2 : Fin 3)) (MvPolynomial.X (2 : Fin 3))
      (negationGraded_standardCoordinate W) :
        HomogeneousLocalization.Away (homogeneousPieces K)
            (MvPolynomial.X (2 : Fin 3)) →+*
          HomogeneousLocalization.Away (homogeneousPieces K)
            (MvPolynomial.X (2 : Fin 3))) _ = _
  exact negationAwayMap_mk W
    (MvPolynomial.X (2 : Fin 3)) (MvPolynomial.X (2 : Fin 3))
    (MvPolynomial.isHomogeneous_X K (2 : Fin 3))
    (MvPolynomial.isHomogeneous_X K (2 : Fin 3))
    (negationGraded_standardCoordinate W) q hq

private theorem standardNegationAwayRingHom_ratio
    (W : WeierstrassCurve K) (j : Fin 3) :
    standardNegationAwayRingHom W
        (coordinateChartRatio (K := K) (2 : Fin 3) j) =
      MvPolynomial.eval₂Hom
        (coordinateChartConstantHom (K := K) (2 : Fin 3))
        (coordinateChartRatio (K := K) (2 : Fin 3))
        (negationCoordinates W j) := by
  have hj : MvPolynomial.X j ∈ homogeneousPieces K 1 := by
    exact MvPolynomial.isHomogeneous_X K j
  change standardNegationAwayRingHom W
      (HomogeneousLocalization.Away.mk (homogeneousPieces K)
        (MvPolynomial.isHomogeneous_X K (2 : Fin 3)) 1
        (MvPolynomial.X j) hj) = _
  rw [standardNegationAwayRingHom_mk]
  · rw [coordinateChartAwayMk_eq_eval₂Hom
      (K := K) (2 : Fin 3) (negationGraded W (MvPolynomial.X j))
        ((negationGraded W).map_mem hj)]
    exact congrArg
      (MvPolynomial.eval₂Hom
        (coordinateChartConstantHom (K := K) (2 : Fin 3))
        (coordinateChartRatio (K := K) (2 : Fin 3)))
      (negationRingHom_X W j)
  · exact hj

private theorem standardNegationAwayRingHom_constant
    (W : WeierstrassCurve K) (a : K) :
    standardNegationAwayRingHom W
        (coordinateChartConstantHom (K := K) (2 : Fin 3) a) =
      coordinateChartConstantHom (K := K) (2 : Fin 3) a := by
  rw [coordinateChartConstantHom_apply]
  rw [standardNegationAwayRingHom_mk]
  · apply HomogeneousLocalization.val_injective
    change Localization.mk
        (negationRingHom W (MvPolynomial.C a)) _ =
      Localization.mk (MvPolynomial.C a) _
    rw [negationRingHom_C]
  · exact MvPolynomial.isHomogeneous_C (Fin 3) a

private theorem eval₂Hom_negationCoordinates
    {A : Type u} [CommRing A] [Algebra K A]
    (W : WeierstrassCurve K) (P : Fin 3 → A) :
    (fun j ↦ MvPolynomial.eval₂Hom (algebraMap K A) P
      (negationCoordinates W j)) =
      (W.map (algebraMap K A)).toProjective.neg P := by
  funext j
  fin_cases j <;>
    simp [negationCoordinates, WeierstrassCurve.Projective.neg,
      WeierstrassCurve.Projective.negY, WeierstrassCurve.map]

private theorem standardNegationAwayRingHom_ratio_quotient
    (W : WeierstrassCurve K) (j : Fin 3) :
    standardChartQuotientRingHom W
        (standardNegationAwayRingHom W
          (coordinateChartRatio (K := K) (2 : Fin 3) j)) =
      standardChartNegatedUniversalPoint W j := by
  rw [standardNegationAwayRingHom_ratio]
  rw [MvPolynomial.map_eval₂Hom]
  have hconst :
      (standardChartQuotientRingHom W).comp
          (coordinateChartConstantHom (K := K) (2 : Fin 3)) =
        algebraMap K (coveringChartCoordinateRing W true) := by
    ext a
    exact standardChartQuotientRingHom_constant W a
  have hratio :
      (fun k ↦ standardChartQuotientRingHom W
        (coordinateChartRatio (K := K) (2 : Fin 3) k)) =
        coveringChartUniversalPoint W true := by
    funext k
    exact standardChartQuotientRingHom_ratio W k
  rw [hconst, hratio]
  exact congrFun
    (eval₂Hom_negationCoordinates W
      (coveringChartUniversalPoint W true)) j

/-- The explicit normalized-point chart map is the quotient of the
degree-zero homogeneous substitution induced by global negation. -/
private theorem standardChartNegationAlgHom_comp_quotient
    (W : WeierstrassCurve K) :
    (standardChartNegationAlgHom W).toRingHom.comp
        (standardChartQuotientRingHom W) =
      (standardChartQuotientRingHom W).comp
        (standardNegationAwayRingHom W) := by
  apply chartRingHom_ext (K := K) (2 : Fin 3)
  · ext a
    change standardChartNegationAlgHom W
        (standardChartQuotientRingHom W
          (coordinateChartConstantHom (K := K) (2 : Fin 3) a)) =
      standardChartQuotientRingHom W
        (standardNegationAwayRingHom W
          (coordinateChartConstantHom (K := K) (2 : Fin 3) a))
    rw [standardNegationAwayRingHom_constant]
    rw [standardChartQuotientRingHom_constant]
    exact (standardChartNegationAlgHom W).commutes a
  · intro j
    change standardChartNegationAlgHom W
        (coveringChartUniversalPoint W true j) =
      standardChartQuotientRingHom W
        (standardNegationAwayRingHom W
          (coordinateChartRatio (K := K) (2 : Fin 3) j))
    rw [standardChartNegationAlgHom_universalPoint,
      standardNegationAwayRingHom_ratio_quotient]

/-- Negation restricted to the standard affine chart. -/
private noncomputable def standardChartNegationMorphism
    (W : WeierstrassCurve K) :
    coveringChartScheme W true ⟶ coveringChartScheme W true :=
  Spec.map (CommRingCat.ofHom
    (standardChartNegationAlgHom W).toRingHom)

private theorem standardChartNegationMorphism_comp_quotientInclusion
    (W : WeierstrassCurve K) :
    standardChartNegationMorphism W ≫
        coveringChartQuotientInclusion W true =
      coveringChartQuotientInclusion W true ≫
        Spec.map (CommRingCat.ofHom
          (standardNegationAwayRingHom W)) := by
  rw [standardChartNegationMorphism,
    coveringChartQuotientInclusion, ← Spec.map_comp,
    ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
      ((standardChartNegationAlgHom W).toRingHom.comp
        (standardChartQuotientRingHom W))) =
    Spec.map (CommRingCat.ofHom
      ((standardChartQuotientRingHom W).comp
        (standardNegationAwayRingHom W)))
  rw [standardChartNegationAlgHom_comp_quotient]

private theorem negationAwayMap_specMap_comp_awayι
    (W : WeierstrassCurve K)
    (s s' : MvPolynomial (Fin 3) K)
    (hs : s ∈ homogeneousPieces K 1)
    (hs' : s' ∈ homogeneousPieces K 1)
    (hss : negationGraded W s = s') :
    Spec.map (CommRingCat.ofHom
        (negationAwayMapOfEq W s s' hss)) ≫
        Proj.awayι (homogeneousPieces K) s hs (by omega) =
      Proj.awayι (homogeneousPieces K) s' hs' (by omega) ≫
        ambientNegation W := by
  unfold negationAwayMapOfEq ambientNegation
  cases hss
  rw [show hs' = (negationGraded W).map_mem hs from
    Subsingleton.elim _ _]
  exact (Proj.awayι_comp_map
    (negationGraded W) (negation_irrelevant_le W) (by omega) s hs).symm

private theorem standardNegationAway_comp_coveringChartAway
    (W : WeierstrassCurve K) :
    Spec.map (CommRingCat.ofHom
        (standardNegationAwayRingHom W)) ≫
        coveringChartAway K true =
      coveringChartAway K true ≫ ambientNegation W := by
  change Spec.map (CommRingCat.ofHom
      (negationAwayMapOfEq W
        (MvPolynomial.X (2 : Fin 3)) (MvPolynomial.X (2 : Fin 3))
        (negationGraded_standardCoordinate W))) ≫
      Proj.awayι (homogeneousPieces K) (MvPolynomial.X (2 : Fin 3))
        (MvPolynomial.isHomogeneous_X K (2 : Fin 3)) (by omega) =
    Proj.awayι (homogeneousPieces K) (MvPolynomial.X (2 : Fin 3))
        (MvPolynomial.isHomogeneous_X K (2 : Fin 3)) (by omega) ≫
      ambientNegation W
  exact negationAwayMap_specMap_comp_awayι W
    (MvPolynomial.X (2 : Fin 3)) (MvPolynomial.X (2 : Fin 3))
    (MvPolynomial.isHomogeneous_X K (2 : Fin 3))
    (MvPolynomial.isHomogeneous_X K (2 : Fin 3))
    (negationGraded_standardCoordinate W)

private theorem standardChartNegationMorphism_comp_ambientMap
    (W : WeierstrassCurve K) :
    standardChartNegationMorphism W ≫
        coveringChartAmbientMap W true =
      coveringChartAmbientMap W true ≫ ambientNegation W := by
  calc
    _ = (standardChartNegationMorphism W ≫
          coveringChartQuotientInclusion W true) ≫
        coveringChartAway K true := by
          rw [coveringChartAmbientMap, Category.assoc]
    _ = (coveringChartQuotientInclusion W true ≫
          Spec.map (CommRingCat.ofHom
            (standardNegationAwayRingHom W))) ≫
        coveringChartAway K true := by
          rw [standardChartNegationMorphism_comp_quotientInclusion]
          rfl
    _ = coveringChartQuotientInclusion W true ≫
        (Spec.map (CommRingCat.ofHom
            (standardNegationAwayRingHom W)) ≫
          coveringChartAway K true) := Category.assoc _ _ _
    _ = coveringChartQuotientInclusion W true ≫
        (coveringChartAway K true ≫ ambientNegation W) :=
      congrArg (fun f ↦ coveringChartQuotientInclusion W true ≫ f)
        (standardNegationAway_comp_coveringChartAway W)
    _ = _ := by
      rw [coveringChartAmbientMap, Category.assoc]

/-- The explicit standard-chart substitution really is the restriction of
the globally defined cubic negation morphism. -/
private theorem standardChartNegationMorphism_comp_chartMap
    (W : WeierstrassCurve K) :
    standardChartNegationMorphism W ≫ coveringChartMap W true =
      coveringChartMap W true ≫ negation W := by
  apply (cancel_mono (inclusion W)).1
  calc
    (standardChartNegationMorphism W ≫
          coveringChartMap W true) ≫ inclusion W =
      standardChartNegationMorphism W ≫
        (coveringChartMap W true ≫ inclusion W) :=
      Category.assoc _ _ _
    _ = standardChartNegationMorphism W ≫
        coveringChartAmbientMap W true := by
          rw [coveringChartMap_comp_inclusion]
    _ = coveringChartAmbientMap W true ≫ ambientNegation W :=
      standardChartNegationMorphism_comp_ambientMap W
    _ = (coveringChartMap W true ≫ inclusion W) ≫
        ambientNegation W := by rw [coveringChartMap_comp_inclusion]
    _ = coveringChartMap W true ≫
        (inclusion W ≫ ambientNegation W) :=
      Category.assoc _ _ _
    _ = coveringChartMap W true ≫
        (negation W ≫ inclusion W) := by
          rw [negation_comp_inclusion]
    _ = (coveringChartMap W true ≫ negation W) ≫ inclusion W :=
      (Category.assoc _ _ _).symm

private theorem inverseChartOpenToStandardPair_comp_firstInput
    (W : WeierstrassCurve K) :
    inverseChartOpenToStandardPair W ≫
        projectivePairChartFirstInput W (true, true) =
      inverseChartOpenToStandardChart W ≫ coveringChartMap W true := by
  rw [inverseChartOpenToStandardPair,
    projectivePairChartFirstInput,
    projectivePairChartMorphismOfCoordinateRingHom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, ← Spec.map_comp,
    inverseChartOpenToStandardChart]
  congr 1
  rw [Spec.map_inj]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  simp [inverseChartPairToOpenAlgHom, inverseChartPairAlgHom]

private theorem inverseChartOpenToStandardPair_comp_secondInput
    (W : WeierstrassCurve K) :
    inverseChartOpenToStandardPair W ≫
        projectivePairChartSecondInput W (true, true) =
      (inverseChartOpenToStandardChart W ≫
        standardChartNegationMorphism W) ≫ coveringChartMap W true := by
  rw [inverseChartOpenToStandardPair,
    projectivePairChartSecondInput,
    projectivePairChartMorphismOfCoordinateRingHom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, ← Spec.map_comp,
    inverseChartOpenToStandardChart, standardChartNegationMorphism,
    ← Category.assoc, ← Spec.map_comp]
  congr 1
  rw [Spec.map_inj]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  simp [inverseChartPairToOpenAlgHom, inverseChartPairAlgHom]

private theorem inverseChartOpenToStandardPair_comp_secondInput_eq_negation
    (W : WeierstrassCurve K) :
    inverseChartOpenToStandardPair W ≫
        projectivePairChartSecondInput W (true, true) =
      (inverseChartOpenToStandardChart W ≫ coveringChartMap W true) ≫
        negation W := by
  calc
    _ = (inverseChartOpenToStandardChart W ≫
          standardChartNegationMorphism W) ≫
        coveringChartMap W true :=
      inverseChartOpenToStandardPair_comp_secondInput W
    _ = inverseChartOpenToStandardChart W ≫
        (standardChartNegationMorphism W ≫
          coveringChartMap W true) := Category.assoc _ _ _
    _ = inverseChartOpenToStandardChart W ≫
        (coveringChartMap W true ≫ negation W) := by
          rw [standardChartNegationMorphism_comp_chartMap]
    _ = _ := (Category.assoc _ _ _).symm

/-- Insert a point and its checked Weierstrass inverse into the projective
fiber square. -/
private noncomputable def projectiveInverseInsertion
    (W : WeierstrassCurve K) : scheme W ⟶ projectivePair W :=
  pullback.lift (𝟙 (scheme W)) (negation W) (by simp)

@[reassoc]
private theorem projectiveInverseInsertion_fst
    (W : WeierstrassCurve K) :
    projectiveInverseInsertion W ≫
        pullback.fst (structureMap W) (structureMap W) =
      𝟙 (scheme W) := by
  exact pullback.lift_fst _ _ _

@[reassoc]
private theorem projectiveInverseInsertion_snd
    (W : WeierstrassCurve K) :
    projectiveInverseInsertion W ≫
        pullback.snd (structureMap W) (structureMap W) =
      negation W := by
  exact pullback.lift_snd _ _ _

/-- The derivative principal open mapped into the projective cubic. -/
private noncomputable def inverseChartOpenToCubic
    (W : WeierstrassCurve K) :
    inverseChartOpenScheme W ⟶ scheme W :=
  inverseChartOpenToStandardChart W ≫ coveringChartMap W true

private instance inverseChartOpenToCubic_isOpenImmersion
    (W : WeierstrassCurve K) :
    IsOpenImmersion (inverseChartOpenToCubic W) := by
  dsimp only [inverseChartOpenToCubic]
  infer_instance

private theorem inverseChartOpenToStandardPair_comp_globalChart
    (W : WeierstrassCurve K) :
    inverseChartOpenToStandardPair W ≫
        projectivePairChartMap W (true, true) =
      inverseChartOpenToCubic W ≫ projectiveInverseInsertion W := by
  apply pullback.hom_ext
  · calc
      _ = inverseChartOpenToStandardPair W ≫
          projectivePairChartFirstInput W (true, true) := by
            rw [Category.assoc, projectivePairChartMap_comp_fst,
              ← projectivePairChartFirstInput_eq]
      _ = inverseChartOpenToCubic W :=
        inverseChartOpenToStandardPair_comp_firstInput W
      _ = inverseChartOpenToCubic W ≫ 𝟙 (scheme W) :=
        (Category.comp_id _).symm
      _ = inverseChartOpenToCubic W ≫
          (projectiveInverseInsertion W ≫
            pullback.fst (structureMap W) (structureMap W)) := by
              rw [projectiveInverseInsertion_fst]
      _ = (inverseChartOpenToCubic W ≫
            projectiveInverseInsertion W) ≫
          pullback.fst (structureMap W) (structureMap W) :=
        (Category.assoc _ _ _).symm
  · calc
      _ = inverseChartOpenToStandardPair W ≫
          projectivePairChartSecondInput W (true, true) := by
            rw [Category.assoc, projectivePairChartMap_comp_snd,
              ← projectivePairChartSecondInput_eq]
      _ = inverseChartOpenToCubic W ≫ negation W :=
        inverseChartOpenToStandardPair_comp_secondInput_eq_negation W
      _ = inverseChartOpenToCubic W ≫
          (projectiveInverseInsertion W ≫
            pullback.snd (structureMap W) (structureMap W)) := by
              rw [projectiveInverseInsertion_snd]
      _ = (inverseChartOpenToCubic W ≫
            projectiveInverseInsertion W) ≫
          pullback.snd (structureMap W) (structureMap W) :=
        (Category.assoc _ _ _).symm

private theorem inverseChartOpenToCubic_comp_structureMap
    (W : WeierstrassCurve K) :
    inverseChartOpenToCubic W ≫ structureMap W =
      Spec.map (CommRingCat.ofHom
        (algebraMap K (inverseChartOpenRing W))) := by
  rw [inverseChartOpenToCubic, Category.assoc,
    coveringChartMap_comp_structureMap,
    inverseChartOpenToStandardChart, ← Spec.map_comp,
    Spec.map_inj]
  apply CommRingCat.hom_ext
  ext a
  exact (IsScalarTower.algebraMap_apply K
    (coveringChartCoordinateRing W true)
    (inverseChartOpenRing W) a).symm

private theorem inverseChartOpen_projectiveInverseInsertion_addition
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (inverseChartOpenToCubic W ≫ projectiveInverseInsertion W) ≫
        projectiveAdditionMorphism W =
      Spec.map (CommRingCat.ofHom
          (algebraMap K (inverseChartOpenRing W))) ≫
        infinityChartOriginMorphism W ≫ coveringChartMap W false := by
  calc
    _ = (inverseChartOpenToStandardPair W ≫
          projectivePairChartMap W (true, true)) ≫
        projectiveAdditionMorphism W := by
          rw [inverseChartOpenToStandardPair_comp_globalChart]
    _ = inverseChartOpenToStandardPair W ≫
        (projectivePairChartMap W (true, true) ≫
          projectiveAdditionMorphism W) := Category.assoc _ _ _
    _ = inverseChartOpenToStandardPair W ≫
        standardPairAdditionMorphism W := by
          rw [projectivePairStandardChart_comp_projectiveAdditionMorphism]
    _ = (inverseChartOpenToOutputOpen W ≫
          projectivePairChartAdditionOutputOpen W
            (true, true) false) ≫
        standardPairAdditionMorphism W := by
          rw [inverseChartOpenToOutputOpen_comp_open]
    _ = inverseChartOpenToOutputOpen W ≫
        (projectivePairChartAdditionOutputOpen W
            (true, true) false ≫ standardPairAdditionMorphism W) :=
      Category.assoc _ _ _
    _ = inverseChartOpenToOutputOpen W ≫
        projectivePairChartAdditionOutputMorphism W
          (true, true) false := by
            rw [projectivePairInfinityOutputOpen_comp_standardPairAdditionMorphism]
    _ = _ := inverseChartOpenToOutputOpen_comp_addition W

private noncomputable instance inverseChartOpen_nonempty
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Nonempty (inverseChartOpenScheme W) := by
  change Nonempty (Spec (.of (Localization.Away
    (standardChartVerticalDerivative W))))
  letI : IsDomain (coveringChartCoordinateRing W true) :=
    coveringChartCoordinateRing_isDomain W true
  letI : Nontrivial (coveringChartCoordinateRing W true) :=
    (coveringChartCoordinateRing_isDomain W true).toNontrivial
  have hinj : Function.Injective
      (algebraMap (coveringChartCoordinateRing W true)
        (Localization.Away (standardChartVerticalDerivative W))) :=
    IsLocalization.injective
      (Localization.Away (standardChartVerticalDerivative W))
      (powers_le_nonZeroDivisors_of_noZeroDivisors
        (standardChartVerticalDerivative_ne_zero W))
  letI : Nontrivial
      (Localization.Away (standardChartVerticalDerivative W)) :=
    hinj.nontrivial
  exact PrimeSpectrum.nonempty_iff_nontrivial.mpr inferInstance

/-- Adding the checked inverse morphism gives the infinity section. -/
private theorem projectiveInverseInsertion_comp_addition
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectiveInverseInsertion W ≫ projectiveAdditionMorphism W =
      structureMap W ≫
        (infinityChartOriginMorphism W ≫ coveringChartMap W false) := by
  letI : IsIntegral (scheme W) :=
    GeometricallyIntegral.isIntegral_of_subsingleton (structureMap W)
  letI : IsDominant (inverseChartOpenToCubic W) := by
    constructor
    have hopen := (inverseChartOpenToCubic W).isOpenEmbedding.isOpenMap
    exact hopen.denseRange_of_isPreirreducibleSpace _
  apply ext_of_isDominant_of_isSeparated
    (s := structureMap W) (ι := inverseChartOpenToCubic W)
  · calc
      (projectiveInverseInsertion W ≫
          projectiveAdditionMorphism W) ≫ structureMap W =
        projectiveInverseInsertion W ≫
          (projectiveAdditionMorphism W ≫ structureMap W) :=
        Category.assoc _ _ _
      _ = projectiveInverseInsertion W ≫
          projectivePairStructureMap W := by
            rw [projectiveAdditionMorphism_comp_structureMap]
      _ = (projectiveInverseInsertion W ≫
            pullback.fst (structureMap W) (structureMap W)) ≫
          structureMap W := by
            rw [projectivePairStructureMap, Category.assoc]
      _ = 𝟙 (scheme W) ≫ structureMap W := by
        rw [projectiveInverseInsertion_fst]
      _ = structureMap W := Category.id_comp _
      _ = structureMap W ≫ 𝟙 (Spec (.of K)) :=
        (Category.comp_id _).symm
      _ = structureMap W ≫
          ((infinityChartOriginMorphism W ≫
              coveringChartMap W false) ≫ structureMap W) := by
        rw [infinityChartOriginMorphism_comp_structureMap]
      _ = (structureMap W ≫
          (infinityChartOriginMorphism W ≫
            coveringChartMap W false)) ≫ structureMap W :=
        (Category.assoc _ _ _).symm
  · calc
      inverseChartOpenToCubic W ≫
          (projectiveInverseInsertion W ≫
            projectiveAdditionMorphism W) =
        (inverseChartOpenToCubic W ≫
          projectiveInverseInsertion W) ≫
            projectiveAdditionMorphism W :=
        (Category.assoc _ _ _).symm
      _ = Spec.map (CommRingCat.ofHom
            (algebraMap K (inverseChartOpenRing W))) ≫
          infinityChartOriginMorphism W ≫ coveringChartMap W false :=
        inverseChartOpen_projectiveInverseInsertion_addition W
      _ = (inverseChartOpenToCubic W ≫ structureMap W) ≫
          infinityChartOriginMorphism W ≫ coveringChartMap W false := by
            rw [inverseChartOpenToCubic_comp_structureMap]
      _ = inverseChartOpenToCubic W ≫
          (structureMap W ≫
            (infinityChartOriginMorphism W ≫
              coveringChartMap W false)) := by
                simp only [Category.assoc]

/-! ## Categorical commutativity -/

/-- The projective addition is commutative in the slice over the coefficient
field. -/
theorem projectiveAdditionOver_comm
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (β_ (toOver W) (toOver W)).hom ≫ projectiveAdditionOver W =
      projectiveAdditionOver W := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Over.braiding_hom_left,
    projectiveAdditionOver_left]
  exact projectivePairSwap_comp_addition W

/-! ## Categorical inverse laws -/

/-- The concrete inverse-graph insertion as a morphism in the slice. -/
private noncomputable def projectiveInverseInsertionOver
    (W : WeierstrassCurve K) :
    toOver W ⟶ toOver W ⊗ toOver W :=
  Over.homMk (projectiveInverseInsertion W) (by
    rw [tensorProjectiveCubic_hom]
    change projectiveInverseInsertion W ≫
        projectivePairStructureMap W = structureMap W
    rw [projectivePairStructureMap, ← Category.assoc,
      projectiveInverseInsertion_fst, Category.id_comp])

@[simp]
private theorem projectiveInverseInsertionOver_left
    (W : WeierstrassCurve K) :
    (projectiveInverseInsertionOver W).left =
      projectiveInverseInsertion W :=
  rfl

private theorem projectiveInverseInsertionOver_eq_lift
    (W : WeierstrassCurve K) :
    projectiveInverseInsertionOver W =
      lift (𝟙 (toOver W)) (negationOver W) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [lift_fst]
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.fst_left,
      projectiveInverseInsertionOver_left]
    exact projectiveInverseInsertion_fst W
  · rw [lift_snd]
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.snd_left,
      projectiveInverseInsertionOver_left]
    exact projectiveInverseInsertion_snd W

/-- Adding a point to its checked Weierstrass inverse gives the infinity
section. -/
theorem projectiveAdditionOver_negation_right_inv
    (W : WeierstrassCurve K) [W.IsElliptic] :
    lift (𝟙 (toOver W)) (negationOver W) ≫
        projectiveAdditionOver W =
      toUnit (toOver W) ≫ infinitySectionOver W := by
  rw [← projectiveInverseInsertionOver_eq_lift]
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, projectiveInverseInsertionOver_left,
    projectiveAdditionOver_left, Over.toUnit_left]
  change projectiveInverseInsertion W ≫
      projectiveAdditionMorphism W =
    structureMap W ≫ (infinitySectionOver W).left
  rw [projectiveInverseInsertion_comp_addition,
    infinityChartOriginMorphism_comp_coveringChartMap]
  rfl

private theorem inverseLift_eq_swapped_rightInverseLift
    (W : WeierstrassCurve K) :
    lift (negationOver W) (𝟙 (toOver W)) =
      lift (𝟙 (toOver W)) (negationOver W) ≫
        (β_ (toOver W) (toOver W)).hom := by
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · simp

/-- The symmetric inverse equation, obtained from the checked
commutativity of projective addition. -/
theorem projectiveAdditionOver_negation_left_inv
    (W : WeierstrassCurve K) [W.IsElliptic] :
    lift (negationOver W) (𝟙 (toOver W)) ≫
        projectiveAdditionOver W =
      toUnit (toOver W) ≫ infinitySectionOver W := by
  rw [inverseLift_eq_swapped_rightInverseLift,
    Category.assoc, projectiveAdditionOver_comm,
    projectiveAdditionOver_negation_right_inv]

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
