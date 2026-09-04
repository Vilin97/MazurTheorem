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
structure is assumed while the equations are established.  The named
downstream consumer is `projectiveGrpObj`, which installs these checked
morphisms as the canonical group-object structure used by the modular-curve
interfaces.
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

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
