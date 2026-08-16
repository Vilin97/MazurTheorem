/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.PointedIncidence
import MazurTorsion.AlgebraicGeometry.Jacobian.UniversalEffectiveDivisorDescent
import MazurTorsion.AlgebraicGeometry.Jacobian.FpqcDescent
import MazurTorsion.AlgebraicGeometry.Jacobian.CoherentComponentBaseChange
import MazurTorsion.AlgebraicGeometry.Jacobian.OrderedIncidenceOpenRestriction
import MazurTorsion.AlgebraicGeometry.Jacobian.AffineIdealSheafPullback
import MazurTorsion.AlgebraicGeometry.Jacobian.GeometricSupportAssignedSplitChart
import MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedGraphQuotient
import MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedIncidenceNeighborhood
import MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedAffineChart
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-!
# The pointed symmetric power maps to the incidence quotient

For a challenge curve, insertion of the distinguished point is equivariant
for permutations of the remaining ordered coordinates.  It therefore
descends from `C × C^(n+1)` to `C × Sym^(n+1)(C)` and lands in the quotient
of the degree-`n + 2` ordered incidence family.

This produces the canonical comparison whose expected isomorphism identifies
the universal effective divisor with `C × Sym^(n+1)(C)`.  The named
downstream consumer is `PicardRepresentability`; after the local monic-chart
comparison proves this morphism is an isomorphism, finite flatness, rank, and
the Cartier equation follow from the pointed symmetric-power presentation.
-/

noncomputable section

universe u

open scoped TensorProduct
open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.PointedIncidenceDescent

open FiniteGroupQuotient
open UniversalEffectiveDivisor
open AffineIdealSheafPullback
open FiniteSupportEtaleCoordinates
open FiniteSupportCoordinateMaps
open FiniteEtaleCoproductPower
open CoherentComponentBaseChange
open OrderedIncidenceOpenRestriction
open GeometricSupportAssignedSplitChart
open GeometricAssignedRootCoordinates
open GeometricAssignedGraphQuotient
open GeometricAssignedAffineChart
open SmoothCurveEtaleCoordinate
open SplitFiniteBaseChange
open SplitFinitePowerPoint
open SplitFiniteSymmetricQuotient
open SplitComponentGraphIdeal

variable (K : Type u) [Field K]
variable (C : Over (Spec (.of K)))
variable [GeometricallyIrreducible C.hom] [IsProper C.hom]
variable [SmoothOfRelativeDimension 1 C.hom]

omit [GeometricallyIrreducible C.hom]
    [SmoothOfRelativeDimension 1 C.hom] in
/-- On every open chart in the curve-level incidence ambient, the defining
ideal retains its scheme-theoretic product multiplicities and each factor is
the kernel of the pulled-back coordinate graph.  This is the global-curve
consumer of the generic open-restriction calculation. -/
theorem curveOrderedIncidenceIdeal_comap_eq_prod_pullbackKernels
    (d : ℕ) {Y : Scheme.{u}}
    (f : Y ⟶ (orderedAmbient (Spec (.of K)) d C).left)
    [IsOpenImmersion f] :
    (orderedIncidenceIdeal (Spec (.of K)) d C).comap f =
      Finset.univ.prod (fun i ↦
        (pullback.fst f
          (coordinateGraphι (Spec (.of K)) d C i).left).ker) :=
  orderedIncidenceIdeal_comap_eq_prod_pullbackKernels
    (Spec (.of K)) d C f

omit [GeometricallyIrreducible C.hom]
    [SmoothOfRelativeDimension 1 C.hom] in
/-- After first restricting the curve-level incidence ambient to an affine
open, any further affine base change still preserves the full product of
coordinate-graph ideals.  This is the ideal-sheaf bridge used by the fpqc
split chart; unlike the first restriction, the second morphism need not be
an open immersion. -/
theorem curveOrderedIncidenceIdeal_affineChart_comap_eq_prod_pullbackKernels
    (d : ℕ)
    (U : (orderedAmbient (Spec (.of K)) d C).left.affineOpens)
    {Y : Scheme.{u}} [IsAffine Y] (f : Y ⟶ U.1) :
    (orderedIncidenceIdeal (Spec (.of K)) d C).comap (f ≫ U.1.ι) =
      Finset.univ.prod (fun i ↦
        (pullback.fst (f ≫ U.1.ι)
          (coordinateGraphι (Spec (.of K)) d C i).left).ker) := by
  letI : IsAffine U.1 := U.2
  calc
    (orderedIncidenceIdeal (Spec (.of K)) d C).comap (f ≫ U.1.ι) =
        ((orderedIncidenceIdeal (Spec (.of K)) d C).comap U.1.ι).comap f :=
      Scheme.IdealSheafData.comap_comp _ _ _
    _ = (Finset.univ.prod (fun i ↦
        (coordinateGraphIdeal (Spec (.of K)) d C i).comap U.1.ι)).comap f := by
      rw [orderedIncidenceIdeal_comap_of_isOpenImmersion]
    _ = Finset.univ.prod (fun i ↦
        ((coordinateGraphIdeal (Spec (.of K)) d C i).comap U.1.ι).comap f) :=
      idealSheaf_comap_finsetProd_of_isAffine _ _ _
    _ = Finset.univ.prod (fun i ↦
        (coordinateGraphIdeal (Spec (.of K)) d C i).comap (f ≫ U.1.ι)) := by
      simp only [Scheme.IdealSheafData.comap_comp]
    _ = Finset.univ.prod (fun i ↦
        (pullback.fst (f ≫ U.1.ι)
          (coordinateGraphι (Spec (.of K)) d C i).left).ker) := by
      congr 1
      funext i
      exact coordinateGraphIdeal_comap_eq_pullbackKernel
        (Spec (.of K)) d C (f ≫ U.1.ι) i

/-- The ordered divisor coordinates underlying a point of the incidence
ambient product. -/
noncomputable def orderedSupportPoint (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left) :
    (PermutationPower.power (Spec (.of K)) (Fin d) C).left :=
  (Limits.prod.snd : orderedAmbient (Spec (.of K)) d C ⟶
    PermutationPower.power (Spec (.of K)) (Fin d) C).left z

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- The number of distinct underlying curve points in the ordered support of
an incidence-ambient point. -/
noncomputable abbrev orderedSupportDistinctCard (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left) :=
  distinctSupportCard K C d (orderedSupportPoint K C d z)

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- The deduplicated support tuple used for the corrected local chart. -/
noncomputable def orderedSupportDistinctPoint (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left) :
    (PermutationPower.power (Spec (.of K))
      (Fin (orderedSupportDistinctCard K C d z)) C).left :=
  distinctSupportOrderedPoint K C d (orderedSupportPoint K C d z)

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- Assign an ordered divisor coordinate to its distinct support index. -/
noncomputable def orderedSupportIndex (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left) (i : Fin d) :
    Fin (orderedSupportDistinctCard K C d z) :=
  pointSupportIndex K C d (orderedSupportPoint K C d z) i

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- Multiplicity of a distinct support point in the original ordered
divisor. -/
noncomputable def orderedSupportMultiplicity (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left)
    (j : Fin (orderedSupportDistinctCard K C d z)) : ℕ :=
  FiniteSupportIndex.topologicalSupportMultiplicity (Spec (.of K)) d C
    (orderedSupportPoint K C d z) j

omit [GeometricallyIrreducible C.hom] [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] in
/-- The deduplicated support multiplicities retain the full divisor degree. -/
theorem sum_orderedSupportMultiplicity (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left) :
    ∑ j : Fin (orderedSupportDistinctCard K C d z),
        orderedSupportMultiplicity K C d z j = d :=
  FiniteSupportIndex.sum_topologicalSupportMultiplicity (Spec (.of K)) d C
    (orderedSupportPoint K C d z)

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- The corrected chart family has one member per distinct support point. -/
noncomputable abbrev orderedSupportDistinctCharts (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left) :=
  DistinctCharts K C d (orderedSupportPoint K C d z)

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- Chosen charts indexed once per distinct support point. -/
noncomputable def orderedSupportDistinctChartData (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left) :
    orderedSupportDistinctCharts K C d z :=
  distinctCharts K C d (orderedSupportPoint K C d z)

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- Chosen finite étale neighborhoods indexed once per distinct support
point. -/
noncomputable def orderedSupportDistinctNeighborhoodData (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left) :
    DistinctNeighborhoods K C d (orderedSupportPoint K C d z) :=
  distinctNeighborhoods K C d (orderedSupportPoint K C d z)

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- The topologically deduplicated support tuple has a simultaneous split
chart whose local-neighborhood family is indexed once per distinct support
point.  The original degree-`d` tuple is retained separately by
`orderedSupportIndex`. -/
theorem orderedSupport_exists_distinctCommonSplitChart (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left) :
    HasDistinctCommonSplitChartAtSupport K C d
      (orderedSupportPoint K C d z) :=
  exists_distinctCommonSplitChartAtSupport K C d
    (orderedSupportPoint K C d z)

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- The geometric-support tuple of an incidence point admits a simultaneous
split chart, identifying only coordinate morphisms that are genuinely equal
over the original residue field. -/
theorem orderedSupport_exists_geometricDistinctCommonSplitChart (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left) :
    HasGeometricDistinctCommonSplitChartAtSupport K C d
      (orderedSupportPoint K C d z) :=
  exists_geometricDistinctCommonSplitChartAtSupport K C d
    (orderedSupportPoint K C d z)

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- The occurrence-wise repetition of the geometric-support charts has a
simultaneous split cover over its dimension-`d` coordinate-base product.
Unlike the deduplicated support base, this base retains one independently
varying coordinate for every ordered occurrence; unlike an arbitrary
occurrence family, equal geometric coordinates use the same chart data.
This is the input chart for the block-stabilizer quotient comparison. -/
theorem orderedSupport_exists_geometricAssignedCommonSplitChart (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left) :
    HasCommonSplitChartAtSupport K C d (orderedSupportPoint K C d z)
      (geometricAssignedCharts K C d (orderedSupportPoint K C d z))
      (geometricAssignedNeighborhoods K C d
        (orderedSupportPoint K C d z)) :=
  exists_commonSplitChartAtSupport K C d (orderedSupportPoint K C d z)
    (geometricAssignedCharts K C d (orderedSupportPoint K C d z))
    (geometricAssignedNeighborhoods K C d
      (orderedSupportPoint K C d z))

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- The actual ordered support of an incidence point has an affine,
dimension-`d`, occurrence-wise étale chart stable under the subgroup that
permutes equal geometric occurrences. -/
noncomputable abbrev orderedSupportGeometricAssignedAffineComponent (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left) :
    Over (coordinateBase K) :=
  commonAffineComponent K C d (orderedSupportPoint K C d z)

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- Quotient of the affine occurrence-wise chart by the exact stabilizer of
the incidence point's geometric support assignment. -/
noncomputable abbrev orderedSupportGeometricAssignedAffineQuotient (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left) : Scheme.{u} :=
  GeometricAssignedAffineChart.componentQuotient K C d
    (orderedSupportPoint K C d z)

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- The repeated distinct-support point in the affine occurrence chart is
fixed by its full block stabilizer.  This is the central point for the local
monic-quotient comparison. -/
theorem orderedSupportGeometricAssignedAffinePoint_fixed (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left)
    (g : geometricAssignedStabilizer K C d
      (orderedSupportPoint K C d z)) :
    (GeometricAssignedAffineChart.componentAction K C d
        (orderedSupportPoint K C d z)).hom g
      (commonAffineComponentPoint K C d (orderedSupportPoint K C d z)) =
        commonAffineComponentPoint K C d (orderedSupportPoint K C d z) :=
  componentAction_fixed_commonAffineComponentPoint K C d
    (orderedSupportPoint K C d z) g

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- The same central affine-chart point maps to the incidence point's exact
ordered curve support after transporting the ground-field presentation.  In
particular, this statement retains the common residue-field correlation and
is stronger than equality of the individual underlying coordinates. -/
theorem orderedSupportGeometricAssignedAffinePoint_mapsToOrderedCurvePower
    (d : ℕ) (z : (orderedAmbient (Spec (.of K)) d C).left) :
    (componentToCurvePower K C d (orderedSupportPoint K C d z)).left
        (commonAffineComponentPoint K C d
          (orderedSupportPoint K C d z)) =
      curvePowerPointOverCoordinateBase K C d
        (orderedSupportPoint K C d z) :=
  componentToCurvePower_commonAffineComponentPoint K C d
    (orderedSupportPoint K C d z)

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- At an incidence support, the actual selected-component chart is finite
étale over its occurrence-wise affine coordinate base, and the induced
coordinate morphism on block quotients factors through that base quotient. -/
theorem orderedSupportGeometricAssignedAffineQuotient_coordinateFactorization
    (d : ℕ) (z : (orderedAmbient (Spec (.of K)) d C).left) :
    componentQuotientToBaseQuotient K C d
          (orderedSupportPoint K C d z) ≫
        quotientToCoordinateQuotient K C d
          (orderedSupportPoint K C d z) =
      componentQuotientToCoordinateQuotient K C d
        (orderedSupportPoint K C d z) :=
  componentQuotientToBaseQuotient_comp_quotientToCoordinateQuotient
    K C d (orderedSupportPoint K C d z)

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- The correlated affine-base point below the exact occurrence-component
point is fixed by the geometric-support block stabilizer. -/
theorem orderedSupportGeometricAssignedExactAffineBasePoint_fixed
    (d : ℕ) (z : (orderedAmbient (Spec (.of K)) d C).left)
    (g : geometricAssignedStabilizer K C d
      (orderedSupportPoint K C d z)) :
    (GeometricAssignedAffineChart.action K C d
        (orderedSupportPoint K C d z)).hom g
      (exactCommonAffineBasePoint K C d (orderedSupportPoint K C d z)) =
        exactCommonAffineBasePoint K C d (orderedSupportPoint K C d z) :=
  action_fixed_exactCommonAffineBasePoint K C d
    (orderedSupportPoint K C d z) g

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- At an ordered incidence support, the selected occurrence-component map
has a block-stable affine constant-rank neighborhood of its exact correlated
base point.  The source preimage is block-stable too, and an affine fpqc
cover splits the restricted map into finitely many sheets of the exact fiber
rank. -/
theorem orderedSupportGeometricAssigned_exists_blockStableAffineFpqcSplit
    (d : ℕ) (z : (orderedAmbient (Spec (.of K)) d C).left) :
    let p := orderedSupportPoint K C d z
    ∃ (V : (commonAffineBase K C d p).left.Opens)
        (hV : IsAffineOpen V),
      (GeometricAssignedAffineChart.action K C d p).IsStableOpen V ∧
      (componentAction K C d p).IsStableOpen
        ((componentToBasePower K C d p).left ⁻¹ᵁ V) ∧
      exactCommonAffineBasePoint K C d p ∈ V ∧
      let f := (componentToBasePower K C d p).left
      let fV := f ∣_ V
      letI : IsAffine V.toScheme := hV
      letI : IsAffine (f ⁻¹ᵁ V).toScheme := isAffine_of_isAffineHom fV
      letI : Algebra Γ(V, ⊤) Γ(f ⁻¹ᵁ V, ⊤) := fV.appTop.hom.toAlgebra
      ∃ (T : Type u) (_ : CommRing T) (_ : Algebra Γ(V, ⊤) T)
        (_ : Module.FaithfullyFlat Γ(V, ⊤) T)
        (_ : Module.Finite Γ(V, ⊤) T)
        (_ : Algebra.Etale Γ(V, ⊤) T) (m : ℕ)
        (_e : T ⊗[Γ(V, ⊤)] Γ(f ⁻¹ᵁ V, ⊤) ≃ₐ[T] (Fin m → T))
        (q : Spec (.of T) ⟶ V.toScheme)
        (_E : pullback fV q ≅ Spec (.of (Fin m → T))),
        _E.hom ≫ EtaleSplitChart.splitProjection T m =
            pullback.snd fV q ∧
          m = f.finrank (exactCommonAffineBasePoint K C d p) ∧
            Flat q ∧ Surjective q ∧ QuasiCompact q :=
  exists_componentToBasePower_affineOpen_fpqc_splitCover K C d
    (orderedSupportPoint K C d z)

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- At an ordered incidence support, the finite product of all block
translates of a chosen affine finite étale split cover remains an affine
finite étale fpqc cover. -/
theorem orderedSupportGeometricAssigned_blockRefinement_isAffine_finiteEtale_fpqc
    (d : ℕ) (z : (orderedAmbient (Spec (.of K)) d C).left)
    {V : (commonAffineBase K C d
      (orderedSupportPoint K C d z)).left.Opens}
    (hVs : (GeometricAssignedAffineChart.action K C d
      (orderedSupportPoint K C d z)).IsStableOpen V)
    {Z : Scheme.{u}} (q : Z ⟶ V.toScheme)
    [IsAffine V.toScheme] [IsAffine Z]
    [IsFinite q] [Etale q] [Surjective q] :
    IsAffine (componentFpqcBlockRefinement K C d
        (orderedSupportPoint K C d z) hVs q).left ∧
      IsFinite (componentFpqcBlockRefinement K C d
        (orderedSupportPoint K C d z) hVs q).hom ∧
      Etale (componentFpqcBlockRefinement K C d
        (orderedSupportPoint K C d z) hVs q).hom ∧
      Flat (componentFpqcBlockRefinement K C d
        (orderedSupportPoint K C d z) hVs q).hom ∧
      Surjective (componentFpqcBlockRefinement K C d
        (orderedSupportPoint K C d z) hVs q).hom ∧
      QuasiCompact (componentFpqcBlockRefinement K C d
        (orderedSupportPoint K C d z) hVs q).hom :=
  componentFpqcBlockRefinement_isAffine_finiteEtale_fpqc K C d
    (orderedSupportPoint K C d z) hVs q

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- At an ordered incidence support, the chosen finite-sheet presentation
pulls from the original fpqc chart to its common block-translate
refinement. -/
noncomputable def orderedSupportGeometricAssigned_blockRefinementSplitIso
    (d : ℕ) (z : (orderedAmbient (Spec (.of K)) d C).left)
    {V : (commonAffineBase K C d
      (orderedSupportPoint K C d z)).left.Opens}
    (hVs : (GeometricAssignedAffineChart.action K C d
      (orderedSupportPoint K C d z)).IsStableOpen V)
    {T : Type u} [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (m : ℕ)
    (E : pullback
      ((componentToBasePower K C d
        (orderedSupportPoint K C d z)).left ∣_ V) q ≅
          Spec (.of (Fin m → T)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection T m =
      pullback.snd
        ((componentToBasePower K C d
          (orderedSupportPoint K C d z)).left ∣_ V) q) :
    componentFpqcBlockSplitSource K C d
        (orderedSupportPoint K C d z) hVs q ≅
      splitFinite
        (componentFpqcBlockRefinement K C d
          (orderedSupportPoint K C d z) hVs q).left m :=
  componentFpqcBlockSplitIso K C d
    (orderedSupportPoint K C d z) hVs q m E hE

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- The transported finite-sheet presentation at an ordered incidence
support carries the genuine geometric-support block action. -/
noncomputable def orderedSupportGeometricAssigned_blockRefinementSplitAction
    (d : ℕ) (z : (orderedAmbient (Spec (.of K)) d C).left)
    {V : (commonAffineBase K C d
      (orderedSupportPoint K C d z)).left.Opens}
    (hVs : (GeometricAssignedAffineChart.action K C d
      (orderedSupportPoint K C d z)).IsStableOpen V)
    (hpre : (componentAction K C d
      (orderedSupportPoint K C d z)).IsStableOpen
        ((componentToBasePower K C d
          (orderedSupportPoint K C d z)).left ⁻¹ᵁ V))
    {T : Type u} [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (m : ℕ)
    (E : pullback
      ((componentToBasePower K C d
        (orderedSupportPoint K C d z)).left ∣_ V) q ≅
          Spec (.of (Fin m → T)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection T m =
      pullback.snd
        ((componentToBasePower K C d
          (orderedSupportPoint K C d z)).left ∣_ V) q) :
    SchemeAction (geometricAssignedStabilizer K C d
      (orderedSupportPoint K C d z))
      (splitFinite
        (componentFpqcBlockRefinement K C d
          (orderedSupportPoint K C d z) hVs q).left m).left :=
  componentFpqcBlockSplitAction K C d
    (orderedSupportPoint K C d z) hVs hpre q m E hE

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- On a chosen geometric-support fpqc split chart, the degree-preserving
assigned coproduct power contains a point mapping to the exact original
ordered support.  Repeated geometric coordinates use the same family member
and remain repeated factors in the degree-`d` power. -/
theorem orderedSupport_exists_geometricAssignedCoproductPowerPoint
    (d : ℕ) (z : (orderedAmbient (Spec (.of K)) d C).left)
    (V : (geometricDistinctCommonBase K C d
      (orderedSupportPoint K C d z)).left.Opens)
    (hV : commonBasePoint K C
      (geometricDistinctSupportCard K C d
        (orderedSupportPoint K C d z))
      (geometricDistinctSupportOrderedPoint K C d
        (orderedSupportPoint K C d z))
      (geometricDistinctCharts K C d (orderedSupportPoint K C d z))
      (geometricDistinctNeighborhoods K C d
        (orderedSupportPoint K C d z)) ∈ V)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) [Surjective q] :
    ∃ p : (assignedCoproductPowerOverGround K C d
        (orderedSupportPoint K C d z) V T q).left,
      (assignedCoproductPowerToCurvePower K C d
        (orderedSupportPoint K C d z) V T q).left p =
          orderedSupportPoint K C d z :=
  exists_assignedCoproductPowerPoint_over_support K C d
    (orderedSupportPoint K C d z) V hV T q

/-- The sheet tuple extracted from an assigned split-family point over an
actual incidence support.  Its remaining arguments are the common split
chart, its componentwise presentations, and the chosen point. -/
noncomputable abbrev orderedSupportGeometricAssignedSheetTuple (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left) :=
  assignedSupportSheetTuple K C d (orderedSupportPoint K C d z)

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- For a point of the assigned component product over an incidence support,
the global split-sheet label selected by an ordered coordinate belongs to
the distinct geometric-support member assigned to that coordinate.  This is
the curve-level consumer of the family-sheet bookkeeping used by the local
ordered-root comparison. -/
theorem orderedSupportGeometricAssignedSheetOwner_productPoint
    (d : ℕ) (z : (orderedAmbient (Spec (.of K)) d C).left)
    (V : (geometricDistinctCommonBase K C d
      (orderedSupportPoint K C d z)).left.Opens)
    (T : Type u) [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (r : Fin (geometricDistinctSupportCard K C d
      (orderedSupportPoint K C d z)) → ℕ)
    (E : ∀ j, pullback
        (restrictedPulledComponentToBase K C
          (geometricDistinctSupportCard K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctSupportOrderedPoint K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctCharts K C d (orderedSupportPoint K C d z))
          (geometricDistinctNeighborhoods K C d
            (orderedSupportPoint K C d z)) V j) q ≅
      Spec (.of (Fin (r j) → T)))
    (hE : ∀ j, (E j).hom ≫ EtaleSplitChart.splitProjection T (r j) =
      pullback.snd
        (restrictedPulledComponentToBase K C
          (geometricDistinctSupportCard K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctSupportOrderedPoint K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctCharts K C d (orderedSupportPoint K C d z))
          (geometricDistinctNeighborhoods K C d
            (orderedSupportPoint K C d z)) V j) q)
    (w : (assignedComponentProductOverGround K C d
      (orderedSupportPoint K C d z) V (Spec (.of T)) q).left)
    (i : Fin d) :
    splitFamilySheetOwner
        (coherentBase K C d (orderedSupportPoint K C d z) V
          (Spec (.of T)) q)
        (geometricDistinctSupportCard K C d
          (orderedSupportPoint K C d z)) r
        (orderedSupportGeometricAssignedSheetTuple K C d z V T q r E hE
          ((assignedProductToCoproductPower K C d
            (orderedSupportPoint K C d z) V
            (Spec (.of T)) q).left w) i) =
      geometricPointSupportIndex K C d
        (orderedSupportPoint K C d z) i :=
  assignedSupportSheetOwner_productPoint K C d
    (orderedSupportPoint K C d z) V T q r E hE w i

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- Reindex the actual ordered support positions by the root variables of
the split symmetric-power component they select.  The orbit permutation is
included explicitly, so this equivalence does not confuse the component's
arbitrary quotient representative with the actual ordered sheet tuple. -/
noncomputable def orderedSupportGeometricAssignedPositionEquivRootIndex
    (d : ℕ) (z : (orderedAmbient (Spec (.of K)) d C).left)
    (V : (geometricDistinctCommonBase K C d
      (orderedSupportPoint K C d z)).left.Opens)
    (T : Type u) [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (r : Fin (geometricDistinctSupportCard K C d
      (orderedSupportPoint K C d z)) → ℕ)
    (E : ∀ j, pullback
        (restrictedPulledComponentToBase K C
          (geometricDistinctSupportCard K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctSupportOrderedPoint K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctCharts K C d (orderedSupportPoint K C d z))
          (geometricDistinctNeighborhoods K C d
            (orderedSupportPoint K C d z)) V j) q ≅
      Spec (.of (Fin (r j) → T)))
    (hE : ∀ j, (E j).hom ≫ EtaleSplitChart.splitProjection T (r j) =
      pullback.snd
        (restrictedPulledComponentToBase K C
          (geometricDistinctSupportCard K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctSupportOrderedPoint K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctCharts K C d (orderedSupportPoint K C d z))
          (geometricDistinctNeighborhoods K C d
            (orderedSupportPoint K C d z)) V j) q)
    (p : (assignedCoproductPowerOverGround K C d
      (orderedSupportPoint K C d z) V (Spec (.of T)) q).left) :
    let m := totalSheets (geometricDistinctSupportCard K C d
      (orderedSupportPoint K C d z)) r
    let c := assignedSupportComponent K C d
      (orderedSupportPoint K C d z) V T q r E hE p
    Fin d ≃ componentRootIndex d m c :=
  GeometricAssignedRootCoordinates.positionEquivRootIndex K C d
    (orderedSupportPoint K C d z) V T q r E hE p

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- The root index attached to an actual ordered support position lies on
the exact split sheet selected by that position. -/
@[simp]
theorem orderedSupportGeometricAssignedPositionEquivRootIndex_fst
    (d : ℕ) (z : (orderedAmbient (Spec (.of K)) d C).left)
    (V : (geometricDistinctCommonBase K C d
      (orderedSupportPoint K C d z)).left.Opens)
    (T : Type u) [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (r : Fin (geometricDistinctSupportCard K C d
      (orderedSupportPoint K C d z)) → ℕ)
    (E : ∀ j, pullback
        (restrictedPulledComponentToBase K C
          (geometricDistinctSupportCard K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctSupportOrderedPoint K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctCharts K C d (orderedSupportPoint K C d z))
          (geometricDistinctNeighborhoods K C d
            (orderedSupportPoint K C d z)) V j) q ≅
      Spec (.of (Fin (r j) → T)))
    (hE : ∀ j, (E j).hom ≫ EtaleSplitChart.splitProjection T (r j) =
      pullback.snd
        (restrictedPulledComponentToBase K C
          (geometricDistinctSupportCard K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctSupportOrderedPoint K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctCharts K C d (orderedSupportPoint K C d z))
          (geometricDistinctNeighborhoods K C d
            (orderedSupportPoint K C d z)) V j) q)
    (p : (assignedCoproductPowerOverGround K C d
      (orderedSupportPoint K C d z) V (Spec (.of T)) q).left)
    (i : Fin d) :
    (orderedSupportGeometricAssignedPositionEquivRootIndex K C d z V T q
      r E hE p i).1 =
        orderedSupportGeometricAssignedSheetTuple K C d z V T q r E hE p i :=
  GeometricAssignedRootCoordinates.positionEquivRootIndex_fst K C d
    (orderedSupportPoint K C d z) V T q r E hE p i

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- For a point coming from the assigned component product, the
orbit-adapted root variable attached to coordinate `i` lies over the genuine
distinct geometric-support member assigned to `i`. -/
theorem orderedSupportGeometricAssignedRootOwner_productPoint
    (d : ℕ) (z : (orderedAmbient (Spec (.of K)) d C).left)
    (V : (geometricDistinctCommonBase K C d
      (orderedSupportPoint K C d z)).left.Opens)
    (T : Type u) [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (r : Fin (geometricDistinctSupportCard K C d
      (orderedSupportPoint K C d z)) → ℕ)
    (E : ∀ j, pullback
        (restrictedPulledComponentToBase K C
          (geometricDistinctSupportCard K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctSupportOrderedPoint K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctCharts K C d (orderedSupportPoint K C d z))
          (geometricDistinctNeighborhoods K C d
            (orderedSupportPoint K C d z)) V j) q ≅
      Spec (.of (Fin (r j) → T)))
    (hE : ∀ j, (E j).hom ≫ EtaleSplitChart.splitProjection T (r j) =
      pullback.snd
        (restrictedPulledComponentToBase K C
          (geometricDistinctSupportCard K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctSupportOrderedPoint K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctCharts K C d (orderedSupportPoint K C d z))
          (geometricDistinctNeighborhoods K C d
            (orderedSupportPoint K C d z)) V j) q)
    (w : (assignedComponentProductOverGround K C d
      (orderedSupportPoint K C d z) V (Spec (.of T)) q).left)
    (i : Fin d) :
    let B := coherentBase K C d (orderedSupportPoint K C d z) V
      (Spec (.of T)) q
    let p := (assignedProductToCoproductPower K C d
      (orderedSupportPoint K C d z) V (Spec (.of T)) q).left w
    splitFamilySheetOwner B
        (geometricDistinctSupportCard K C d
          (orderedSupportPoint K C d z)) r
        (orderedSupportGeometricAssignedPositionEquivRootIndex K C d z V
          T q r E hE p i).1 =
      geometricPointSupportIndex K C d (orderedSupportPoint K C d z) i := by
  dsimp only
  rw [orderedSupportGeometricAssignedPositionEquivRootIndex_fst]
  exact orderedSupportGeometricAssignedSheetOwner_productPoint K C d z V
    T q r E hE w i

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- On the geometric split chart attached to an actual incidence support,
base change sends the universal linear factor for ordered position `i` to
the concrete affine-line graph equation of that position's coherent
coordinate function. -/
theorem orderedSupportGeometricAssignedRootLinearFactor_map
    (d : ℕ) (z : (orderedAmbient (Spec (.of K)) d C).left)
    (V : (geometricDistinctCommonBase K C d
      (orderedSupportPoint K C d z)).left.Opens)
    (T : Type u) [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (r : Fin (geometricDistinctSupportCard K C d
      (orderedSupportPoint K C d z)) → ℕ)
    (E : ∀ j, pullback
        (restrictedPulledComponentToBase K C
          (geometricDistinctSupportCard K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctSupportOrderedPoint K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctCharts K C d (orderedSupportPoint K C d z))
          (geometricDistinctNeighborhoods K C d
            (orderedSupportPoint K C d z)) V j) q ≅
      Spec (.of (Fin (r j) → T)))
    (hE : ∀ j, (E j).hom ≫ EtaleSplitChart.splitProjection T (r j) =
      pullback.snd
        (restrictedPulledComponentToBase K C
          (geometricDistinctSupportCard K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctSupportOrderedPoint K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctCharts K C d (orderedSupportPoint K C d z))
          (geometricDistinctNeighborhoods K C d
            (orderedSupportPoint K C d z)) V j) q)
    (w : (assignedComponentProductOverGround K C d
      (orderedSupportPoint K C d z) V (Spec (.of T)) q).left)
    (i : Fin d) :
    let p := (assignedProductToCoproductPower K C d
      (orderedSupportPoint K C d z) V (Spec (.of T)) q).left w
    let m := totalSheets (geometricDistinctSupportCard K C d
      (orderedSupportPoint K C d z)) r
    let c := assignedSupportComponent K C d
      (orderedSupportPoint K C d z) V T q r E hE p
    (rootLinearFactor Γ(Spec (.of K), ⊤) d m c
        (orderedSupportGeometricAssignedPositionEquivRootIndex K C d z V
          T q r E hE p i)).map
      (GeometricAssignedRootCoordinates.rootCoordinateHom K C d
        (orderedSupportPoint K C d z) V T q r E hE w) =
      Polynomial.X - Polynomial.C
        (GeometricAssignedRootCoordinates.rootValue K C d
          (orderedSupportPoint K C d z) V T q i) :=
  GeometricAssignedRootCoordinates.rootLinearFactor_map K C d
    (orderedSupportPoint K C d z) V T q r E hE w i

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- At an actual incidence support, specialization sends the entire product
of universal ordered graph ideals to the entire product of concrete
owner-sheet graph ideals on the coherent base.  In particular this retains
all repeated ordered occurrences, not only their reduced support. -/
theorem orderedSupportGeometricAssignedGraphIdeal_map
    (d : ℕ) (z : (orderedAmbient (Spec (.of K)) d C).left)
    (V : (geometricDistinctCommonBase K C d
      (orderedSupportPoint K C d z)).left.Opens)
    (T : Type u) [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (r : Fin (geometricDistinctSupportCard K C d
      (orderedSupportPoint K C d z)) → ℕ)
    (E : ∀ j, pullback
        (restrictedPulledComponentToBase K C
          (geometricDistinctSupportCard K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctSupportOrderedPoint K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctCharts K C d (orderedSupportPoint K C d z))
          (geometricDistinctNeighborhoods K C d
            (orderedSupportPoint K C d z)) V j) q ≅
      Spec (.of (Fin (r j) → T)))
    (hE : ∀ j, (E j).hom ≫ EtaleSplitChart.splitProjection T (r j) =
      pullback.snd
        (restrictedPulledComponentToBase K C
          (geometricDistinctSupportCard K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctSupportOrderedPoint K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctCharts K C d (orderedSupportPoint K C d z))
          (geometricDistinctNeighborhoods K C d
            (orderedSupportPoint K C d z)) V j) q)
    (w : (assignedComponentProductOverGround K C d
      (orderedSupportPoint K C d z) V (Spec (.of T)) q).left) :
    let p := (assignedProductToCoproductPower K C d
      (orderedSupportPoint K C d z) V (Spec (.of T)) q).left w
    let m := totalSheets (geometricDistinctSupportCard K C d
      (orderedSupportPoint K C d z)) r
    let c := assignedSupportComponent K C d
      (orderedSupportPoint K C d z) V T q r E hE p
    Ideal.map
        (GeometricAssignedRootCoordinates.orderedAmbientCoordinateHom K C d
          (orderedSupportPoint K C d z) V T q r E hE w)
        (orderedGraphIdeal Γ(Spec (.of K), ⊤) d m c) =
      GeometricAssignedRootCoordinates.evaluatedOrderedGraphIdeal K C d
        (orderedSupportPoint K C d z) V T q r E hE w :=
  GeometricAssignedRootCoordinates.orderedAmbientCoordinateHom_map_orderedGraphIdeal
    K C d (orderedSupportPoint K C d z) V T q r E hE w

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- At an actual incidence support, the full evaluated graph quotient on the
coherent split chart is finite flat of constant rank `d`.  This is the
curve-level consumer of the arbitrary-base-change graph quotient theorem;
the remaining localization step identifies this affine family with the
restricted curve-level incidence family. -/
theorem orderedSupportGeometricAssignedGraphQuotient_finrank
    (d : ℕ) (z : (orderedAmbient (Spec (.of K)) d C).left)
    (V : (geometricDistinctCommonBase K C d
      (orderedSupportPoint K C d z)).left.Opens)
    (T : Type u) [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (r : Fin (geometricDistinctSupportCard K C d
      (orderedSupportPoint K C d z)) → ℕ)
    (E : ∀ j, pullback
        (restrictedPulledComponentToBase K C
          (geometricDistinctSupportCard K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctSupportOrderedPoint K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctCharts K C d (orderedSupportPoint K C d z))
          (geometricDistinctNeighborhoods K C d
            (orderedSupportPoint K C d z)) V j) q ≅
      Spec (.of (Fin (r j) → T)))
    (hE : ∀ j, (E j).hom ≫ EtaleSplitChart.splitProjection T (r j) =
      pullback.snd
        (restrictedPulledComponentToBase K C
          (geometricDistinctSupportCard K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctSupportOrderedPoint K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctCharts K C d (orderedSupportPoint K C d z))
          (geometricDistinctNeighborhoods K C d
            (orderedSupportPoint K C d z)) V j) q)
    (w : (assignedComponentProductOverGround K C d
      (orderedSupportPoint K C d z) V (Spec (.of T)) q).left)
    [Nontrivial Γ(coherentBase K C d (orderedSupportPoint K C d z) V
      (Spec (.of T)) q, ⊤)] :
    (evaluatedGraphSpecProjection K C d
      (orderedSupportPoint K C d z) V T q r E hE w).finrank =
        fun _ ↦ d :=
  evaluatedGraphSpecProjection_finrank K C d
    (orderedSupportPoint K C d z) V T q r E hE w

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- For an actual incidence support, the split sheet selected by ordered
position `i` maps to its genuine curve chart with the matching root
coordinate, and is the first open-and-closed graph summand of the
equal-coordinate pullback. -/
theorem orderedSupportGeometricAssignedRootSheet_exists_graphCoproduct
    (d : ℕ) (z : (orderedAmbient (Spec (.of K)) d C).left)
    (V : (geometricDistinctCommonBase K C d
      (orderedSupportPoint K C d z)).left.Opens)
    (T : Type u) [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (r : Fin (geometricDistinctSupportCard K C d
      (orderedSupportPoint K C d z)) → ℕ)
    (E : ∀ j, pullback
        (restrictedPulledComponentToBase K C
          (geometricDistinctSupportCard K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctSupportOrderedPoint K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctCharts K C d (orderedSupportPoint K C d z))
          (geometricDistinctNeighborhoods K C d
            (orderedSupportPoint K C d z)) V j) q ≅
      Spec (.of (Fin (r j) → T)))
    (hE : ∀ j, (E j).hom ≫ EtaleSplitChart.splitProjection T (r j) =
      pullback.snd
        (restrictedPulledComponentToBase K C
          (geometricDistinctSupportCard K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctSupportOrderedPoint K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctCharts K C d (orderedSupportPoint K C d z))
          (geometricDistinctNeighborhoods K C d
            (orderedSupportPoint K C d z)) V j) q)
    (w : (assignedComponentProductOverGround K C d
      (orderedSupportPoint K C d z) V (Spec (.of T)) q).left)
    (i : Fin d) :
    let z₀ := orderedSupportPoint K C d z
    let B := GeometricAssignedRootCoordinates.base K C d z₀ V T q
    let f := ((geometricDistinctCharts K C d z₀)
      (geometricPointSupportIndex K C d z₀ i)).schemeMap
    let coordinate := GeometricAssignedRootCoordinates.baseCoordinate
      K C d z₀ V T q i
    let sheet := GeometricAssignedRootCoordinates.rootSheetToChart
      K C d z₀ V T q r E hE w i
    let graph : B ⟶ pullback f coordinate :=
      pullback.lift sheet (𝟙 B) (by
        simpa only [Category.id_comp] using
          GeometricAssignedRootCoordinates.rootSheetToChart_comp_schemeMap
            K C d z₀ V T q r E hE w i)
    ∃ (W : Scheme.{u}) (G : pullback f coordinate ≅ B ⨿ W),
      graph ≫ G.hom = coprod.inl := by
  dsimp only
  exact GeometricAssignedRootCoordinates.rootSheet_exists_graphCoproduct
    K C d (orderedSupportPoint K C d z) V T q r E hE w i

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- Around the split sheet selected by an actual incidence support, there is
an open neighbourhood in the relative curve-chart product on which the
whole equal-coordinate closed locus is exactly the genuine sheet graph.
Thus complementary sheets can be removed before transporting the ordered
incidence ideal to the evaluated graph-product algebra. -/
theorem orderedSupportGeometricAssigned_exists_incidenceOpen_graph_isPullback
    (d : ℕ) (z : (orderedAmbient (Spec (.of K)) d C).left)
    (V : (geometricDistinctCommonBase K C d
      (orderedSupportPoint K C d z)).left.Opens)
    (T : Type u) [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (r : Fin (geometricDistinctSupportCard K C d
      (orderedSupportPoint K C d z)) → ℕ)
    (E : ∀ j, pullback
        (restrictedPulledComponentToBase K C
          (geometricDistinctSupportCard K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctSupportOrderedPoint K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctCharts K C d (orderedSupportPoint K C d z))
          (geometricDistinctNeighborhoods K C d
            (orderedSupportPoint K C d z)) V j) q ≅
      Spec (.of (Fin (r j) → T)))
    (hE : ∀ j, (E j).hom ≫ EtaleSplitChart.splitProjection T (r j) =
      pullback.snd
        (restrictedPulledComponentToBase K C
          (geometricDistinctSupportCard K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctSupportOrderedPoint K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctCharts K C d (orderedSupportPoint K C d z))
          (geometricDistinctNeighborhoods K C d
            (orderedSupportPoint K C d z)) V j) q)
    (w : (assignedComponentProductOverGround K C d
      (orderedSupportPoint K C d z) V (Spec (.of T)) q).left)
    (i : Fin d) :
    let z₀ := orderedSupportPoint K C d z
    let B := GeometricAssignedRootCoordinates.base K C d z₀ V T q
    let f := ((geometricDistinctCharts K C d z₀)
      (geometricPointSupportIndex K C d z₀ i)).schemeMap
    let coordinate := GeometricAssignedRootCoordinates.baseCoordinate
      K C d z₀ V T q i
    let A := EqualCoordinateClosedImmersion.ambient
      (coordinateLine K).hom f coordinate
    let inclusion := EqualCoordinateClosedImmersion.equalCoordinateInclusion
      (coordinateLine K).hom f coordinate
    let sheet := GeometricAssignedRootCoordinates.rootSheetToChart
      K C d z₀ V T q r E hE w i
    let graph : B ⟶ pullback f coordinate :=
      EtaleGraphNeighborhood.graph f coordinate sheet
        (GeometricAssignedRootCoordinates.rootSheetToChart_comp_schemeMap
          K C d z₀ V T q r E hE w i)
    ∃ (W : Scheme.{u}) (F : pullback f coordinate ≅ B ⨿ W)
      (U : A.Opens) (graphToU : B ⟶ U.toScheme),
      graph ≫ F.hom = coprod.inl ∧
      IsPullback graphToU graph U.ι inclusion ∧
      inclusion.ker.comap U.ι = graphToU.ker := by
  dsimp only
  exact
    GeometricAssignedIncidenceNeighborhood.exists_occurrenceOpen_graphIdeal
      K C d (orderedSupportPoint K C d z) V T q r E hE w i

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- On the split symmetric-power component selected by an actual incidence
support, the scheme-theoretic product of its ordered coordinate-graph ideals
is the exact kernel of the sheetwise ordered-root algebra map.  The base ring
is the ring of global functions on the coherent affine splitting base. -/
theorem orderedSupportGeometricAssignedGraphIdeal_eq_ker
    (d : ℕ) (z : (orderedAmbient (Spec (.of K)) d C).left)
    (V : (geometricDistinctCommonBase K C d
      (orderedSupportPoint K C d z)).left.Opens)
    (T : Type u) [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (r : Fin (geometricDistinctSupportCard K C d
      (orderedSupportPoint K C d z)) → ℕ)
    (E : ∀ j, pullback
        (restrictedPulledComponentToBase K C
          (geometricDistinctSupportCard K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctSupportOrderedPoint K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctCharts K C d (orderedSupportPoint K C d z))
          (geometricDistinctNeighborhoods K C d
            (orderedSupportPoint K C d z)) V j) q ≅
      Spec (.of (Fin (r j) → T)))
    (hE : ∀ j, (E j).hom ≫ EtaleSplitChart.splitProjection T (r j) =
      pullback.snd
        (restrictedPulledComponentToBase K C
          (geometricDistinctSupportCard K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctSupportOrderedPoint K C d
            (orderedSupportPoint K C d z))
          (geometricDistinctCharts K C d (orderedSupportPoint K C d z))
          (geometricDistinctNeighborhoods K C d
            (orderedSupportPoint K C d z)) V j) q)
    (p : (assignedCoproductPowerOverGround K C d
      (orderedSupportPoint K C d z) V (Spec (.of T)) q).left) :
    let B := coherentBase K C d (orderedSupportPoint K C d z) V
      (Spec (.of T)) q
    let m := totalSheets (geometricDistinctSupportCard K C d
      (orderedSupportPoint K C d z)) r
    let c := assignedSupportComponent K C d
      (orderedSupportPoint K C d z) V T q r E hE p
    orderedGraphIdeal Γ(B, ⊤) d m c =
      RingHom.ker (ambientToOrderedRoot Γ(B, ⊤) d m c) :=
  orderedGraphIdeal_eq_ker _ d _ _

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- Every ordered incidence-ambient point therefore carries a finite family
of actual affine étale curve-coordinate charts, one for each occurrence in
its ordered support. -/
theorem orderedSupportPoint_nonempty_charts (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left) :
    Nonempty (FiniteSupportEtaleCoordinates.Charts K C d
      (orderedSupportPoint K C d z)) :=
  FiniteSupportEtaleCoordinates.nonempty_charts K C d
    (orderedSupportPoint K C d z)

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- Chosen coordinate charts on the ordered support of an incidence point. -/
noncomputable def orderedSupportCharts (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left) :
    FiniteSupportEtaleCoordinates.Charts K C d
      (orderedSupportPoint K C d z) :=
  FiniteSupportEtaleCoordinates.charts K C d (orderedSupportPoint K C d z)

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- Chosen finite étale Zariski-main neighborhoods on the ordered support. -/
noncomputable def orderedSupportNeighborhoods (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left) :=
  FiniteSupportEtaleCoordinates.neighborhoods K C d
    (orderedSupportPoint K C d z) (orderedSupportCharts K C d z)

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- The common étale base of all selected support neighborhoods. -/
noncomputable abbrev orderedSupportCommonBase (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left) :=
  FiniteSupportEtaleCoordinates.commonBase K C d
    (orderedSupportPoint K C d z) (orderedSupportCharts K C d z)
      (orderedSupportNeighborhoods K C d z)

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- The finite family of support components over their common étale base. -/
noncomputable abbrev orderedSupportComponentFamily (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left) :=
  FiniteSupportEtaleCoordinates.commonComponentFamily K C d
    (orderedSupportPoint K C d z) (orderedSupportCharts K C d z)
      (orderedSupportNeighborhoods K C d z)

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
instance orderedSupportComponentFamily_isFinite (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left) :
    IsFinite (orderedSupportComponentFamily K C d z).hom := inferInstance

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
instance orderedSupportComponentFamily_etale (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left) :
    Etale (orderedSupportComponentFamily K C d z).hom := inferInstance

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- Before choosing its fpqc splitting, every finite component around the
actual ordered support is already an open-and-closed summand of the
base-changed curve-coordinate chart. -/
theorem orderedSupportPulledComponent_exists_coordinatePullbackCoproduct
    (d : ℕ) (z : (orderedAmbient (Spec (.of K)) d C).left) (i : Fin d) :
    ∃ (W : Scheme.{u})
      (E : pullback ((orderedSupportCharts K C d z) i).schemeMap
          (commonBaseToCoordinateLine K C d (orderedSupportPoint K C d z)
            (orderedSupportCharts K C d z)
            (orderedSupportNeighborhoods K C d z) i) ≅
        (pulledComponentOverCommonBase K C d
          (orderedSupportPoint K C d z) (orderedSupportCharts K C d z)
          (orderedSupportNeighborhoods K C d z) i).left ⨿ W),
      pulledComponentToCoordinatePullback K C d
          (orderedSupportPoint K C d z) (orderedSupportCharts K C d z)
          (orderedSupportNeighborhoods K C d z) i ≫ E.hom = coprod.inl :=
  pulledComponent_exists_coordinatePullbackCoproduct K C d
    (orderedSupportPoint K C d z) (orderedSupportCharts K C d z)
      (orderedSupportNeighborhoods K C d z) i

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- On the actual ordered support, the nested restriction/fpqc/coherent
component is canonically the direct base change of the original selected
finite component. -/
noncomputable def orderedSupportCoherentPulledComponentDirectIso
    (d : ℕ) (z : (orderedAmbient (Spec (.of K)) d C).left)
    (V : (commonBase K C d (orderedSupportPoint K C d z)
      (orderedSupportCharts K C d z)
      (orderedSupportNeighborhoods K C d z)).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :
    (coherentFpqcPulledComponent K C d (orderedSupportPoint K C d z)
      (orderedSupportCharts K C d z)
      (orderedSupportNeighborhoods K C d z) V T q i).left ≅
    pullback
      (pulledComponentOverCommonBase K C d (orderedSupportPoint K C d z)
        (orderedSupportCharts K C d z)
        (orderedSupportNeighborhoods K C d z) i).hom
      (coherentBaseToCommonBase K C d (orderedSupportPoint K C d z)
        (orderedSupportCharts K C d z)
        (orderedSupportNeighborhoods K C d z) V T q i) :=
  coherentPulledComponentDirectIso K C d (orderedSupportPoint K C d z)
    (orderedSupportCharts K C d z)
    (orderedSupportNeighborhoods K C d z) V T q i

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- Over the coherent split base at the actual ordered support, the entire
selected finite component is a coproduct summand of the base-changed curve
coordinate chart. -/
theorem orderedSupportCoherentComponent_exists_coordinatePullbackCoproduct
    (d : ℕ) (z : (orderedAmbient (Spec (.of K)) d C).left)
    (V : (commonBase K C d (orderedSupportPoint K C d z)
      (orderedSupportCharts K C d z)
      (orderedSupportNeighborhoods K C d z)).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :
    let z₀ := orderedSupportPoint K C d z
    let c₀ := orderedSupportCharts K C d z
    let n₀ := orderedSupportNeighborhoods K C d z
    ∃ (W : Scheme.{u})
      (E : pullback (c₀ i).schemeMap
          (coherentBaseToCoordinateLine K C d z₀ c₀ n₀ V T q i) ≅
        (coherentFpqcPulledComponent K C d z₀ c₀ n₀ V T q i).left ⨿ W),
      coherentComponentToCoordinatePullback K C d z₀ c₀ n₀ V T q i ≫
        E.hom = coprod.inl := by
  dsimp only
  exact coherentComponent_exists_coordinatePullbackCoproduct K C d
    (orderedSupportPoint K C d z) (orderedSupportCharts K C d z)
      (orderedSupportNeighborhoods K C d z) V T q i

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- The coherent product base attached to the actual ordered support of an
incidence-ambient point. -/
noncomputable abbrev orderedSupportCoherentBase (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left)
    (V : (orderedSupportCommonBase K C d z).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) : Scheme.{u} :=
  coherentFpqcBase K C d (orderedSupportPoint K C d z)
    (orderedSupportCharts K C d z) (orderedSupportNeighborhoods K C d z)
      V T q

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- One coherent component attached to an actual ordered support
coordinate. -/
noncomputable abbrev orderedSupportCoherentComponent (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left)
    (V : (orderedSupportCommonBase K C d z).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :=
  coherentFpqcPulledComponent K C d (orderedSupportPoint K C d z)
    (orderedSupportCharts K C d z) (orderedSupportNeighborhoods K C d z)
      V T q i

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- The affine-line coordinate on the coherent base associated to an actual
ordered support coordinate. -/
noncomputable def orderedSupportCoherentBaseCoordinate (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left)
    (V : (orderedSupportCommonBase K C d z).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :
    orderedSupportCoherentBase K C d z V T q ⟶
      Spec (.of (SmoothCurveEtaleCoordinate.coordinateRing K)) :=
  coherentBaseToCoordinateLine K C d (orderedSupportPoint K C d z)
    (orderedSupportCharts K C d z) (orderedSupportNeighborhoods K C d z)
      V T q i

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- A split sheet over the actual ordered support, mapped back to its chosen
affine curve chart. -/
noncomputable def orderedSupportSplitSheetToChart (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left)
    (V : (orderedSupportCommonBase K C d z).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) (m : ℕ)
    (E : orderedSupportCoherentComponent K C d z V T q i ≅
      splitFinite (orderedSupportCoherentBase K C d z V T q) m)
    (j : Fin m) :
    orderedSupportCoherentBase K C d z V T q ⟶
      (((orderedSupportCharts K C d z) i).V : C.left.Opens).toScheme :=
  coherentSplitSheetToChart K C d (orderedSupportPoint K C d z)
    (orderedSupportCharts K C d z) (orderedSupportNeighborhoods K C d z)
      V T q i m E j

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- The actual ordered-support sheet has the coordinate supplied by its
matching coherent-base factor. -/
theorem orderedSupportSplitSheetToChart_comp_schemeMap (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left)
    (V : (orderedSupportCommonBase K C d z).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) (m : ℕ)
    (E : orderedSupportCoherentComponent K C d z V T q i ≅
      splitFinite (orderedSupportCoherentBase K C d z V T q) m)
    (j : Fin m) :
    orderedSupportSplitSheetToChart K C d z V T q i m E j ≫
        ((orderedSupportCharts K C d z) i).schemeMap =
      orderedSupportCoherentBaseCoordinate K C d z V T q i := by
  exact coherentSplitSheetToChart_comp_schemeMap K C d
    (orderedSupportPoint K C d z) (orderedSupportCharts K C d z)
      (orderedSupportNeighborhoods K C d z) V T q i m E j

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- On the actual support chart used by pointed incidence, every selected
split sheet is the first open-and-closed graph summand in the base change of
the curve's étale coordinate.  This is the geometric input for comparison
with the explicit monic-root incidence chart. -/
theorem orderedSupportSplitSheet_exists_graphCoproduct (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left)
    (V : (orderedSupportCommonBase K C d z).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) (m : ℕ)
    (E : orderedSupportCoherentComponent K C d z V T q i ≅
      splitFinite (orderedSupportCoherentBase K C d z V T q) m)
    (j : Fin m) :
    let B := orderedSupportCoherentBase K C d z V T q
    let f := ((orderedSupportCharts K C d z) i).schemeMap
    let baseCoordinate :=
      orderedSupportCoherentBaseCoordinate K C d z V T q i
    let sheetToChart :=
      orderedSupportSplitSheetToChart K C d z V T q i m E j
    let graph : B ⟶ pullback f baseCoordinate :=
      pullback.lift sheetToChart (𝟙 B) (by
        simpa only [Category.id_comp] using
          orderedSupportSplitSheetToChart_comp_schemeMap
            K C d z V T q i m E j)
    ∃ (W : Scheme.{u}) (G : pullback f baseCoordinate ≅ B ⨿ W),
      graph ≫ G.hom = coprod.inl := by
  exact coherentSplitSheet_exists_graphCoproduct K C d
    (orderedSupportPoint K C d z) (orderedSupportCharts K C d z)
      (orderedSupportNeighborhoods K C d z) V T q i m E j

/-- The pointwise split-chart assertion specialized to the actual ordered
support of an incidence-ambient point. -/
noncomputable abbrev OrderedSupportSplitChart (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left) : Prop :=
  FiniteSupportEtaleCoordinates.HasCommonSplitChartAtSupport K C d
    (orderedSupportPoint K C d z) (orderedSupportCharts K C d z)
      (orderedSupportNeighborhoods K C d z)

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- Every ordered incidence-ambient point has a common finite étale fpqc
split chart carrying a point above its exact ordered support. -/
theorem orderedSupport_exists_splitChart (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left) :
    OrderedSupportSplitChart K C d z :=
  FiniteSupportEtaleCoordinates.exists_commonSplitChartAtSupport K C d
    (orderedSupportPoint K C d z) (orderedSupportCharts K C d z)
      (orderedSupportNeighborhoods K C d z)

/-- A chosen ordered-incidence lift of a point of the incidence quotient. -/
noncomputable def orderedIncidenceLift (n : ℕ)
    (y : curveOrderedIncidenceQuotientSucc K C n) :
    orderedIncidence (Spec (.of K)) (n + 1) C :=
  Classical.choose
    ((curveOrderedIncidenceQuotientProjectionSucc K C n).surjective y)

@[simp]
theorem orderedIncidenceQuotientProjection_lift (n : ℕ)
    (y : curveOrderedIncidenceQuotientSucc K C n) :
    curveOrderedIncidenceQuotientProjectionSucc K C n
        (orderedIncidenceLift K C n y) = y :=
  Classical.choose_spec
    ((curveOrderedIncidenceQuotientProjectionSucc K C n).surjective y)

/-- The chosen quotient lift, embedded in the ordered incidence ambient
product so that its divisor support can be charted. -/
noncomputable def orderedIncidenceAmbientLift (n : ℕ)
    (y : curveOrderedIncidenceQuotientSucc K C n) :
    (orderedAmbient (Spec (.of K)) (n + 1) C).left :=
  orderedIncidenceι (Spec (.of K)) (n + 1) C
    (orderedIncidenceLift K C n y)

/-- Every point of the actual incidence quotient therefore has an ordered
lift whose exact support is carried by one common finite étale fpqc split
chart. -/
theorem incidenceQuotientPoint_exists_orderedSupportSplitChart (n : ℕ)
    (y : curveOrderedIncidenceQuotientSucc K C n) :
    OrderedSupportSplitChart K C (n + 1)
      (orderedIncidenceAmbientLift K C n y) :=
  orderedSupport_exists_splitChart K C (n + 1)
    (orderedIncidenceAmbientLift K C n y)

/-- Ordered insertion followed by the quotient of the larger incidence
family. -/
noncomputable def orderedPointedToIncidenceQuotient (n : ℕ) :
    (orderedAmbient (Spec (.of K)) (n + 1) C).left ⟶
      curveOrderedIncidenceQuotientSucc K C (n + 1) :=
  PointedIncidence.orderedPointedIncidenceMap
      (Spec (.of K)) (n + 1) C ≫
    curveOrderedIncidenceQuotientProjectionSucc K C (n + 1)

/-- Ordered pointed addition is invariant under permutations of the
remaining coordinates after passing to the incidence quotient. -/
theorem orderedPointedToIncidenceQuotient_invariant
    (n : ℕ) (g : Equiv.Perm (Fin (n + 1))) :
    (orderedAmbientAction (Spec (.of K)) (n + 1) C).hom g ≫
        orderedPointedToIncidenceQuotient K C n =
      orderedPointedToIncidenceQuotient K C n := by
  rw [orderedPointedToIncidenceQuotient, ← Category.assoc,
    PointedIncidence.orderedAmbientAction_comp_orderedPointedIncidenceMap,
    Category.assoc]
  exact congrArg
    (fun q ↦ PointedIncidence.orderedPointedIncidenceMap
      (Spec (.of K)) (n + 1) C ≫ q)
    (FiniteGroupQuotient.hom_quotientπ
      (orderedIncidenceAction (Spec (.of K)) (n + 2) C)
      (curveOrderedIncidence_hasAffineOrbit_succ K C (n + 1))
      (PointedIncidence.fixZeroPermutation (n + 1) g))

/-- Descent of pointed addition from the ambient quotient to the larger
incidence quotient. -/
noncomputable def ambientQuotientToIncidenceQuotientPointed (n : ℕ) :
    curveOrderedAmbientQuotientSucc K C n ⟶
      curveOrderedIncidenceQuotientSucc K C (n + 1) :=
  FiniteGroupQuotient.descendedMap
    (orderedAmbientAction (Spec (.of K)) (n + 1) C)
    (curveOrderedAmbient_hasAffineOrbit_succ K C n)
    (orderedPointedToIncidenceQuotient K C n)
    (orderedPointedToIncidenceQuotient_invariant K C n)

@[reassoc]
theorem curveOrderedAmbientQuotientProjection_comp_pointedDescent
    (n : ℕ) :
    curveOrderedAmbientQuotientProjectionSucc K C n ≫
        ambientQuotientToIncidenceQuotientPointed K C n =
      orderedPointedToIncidenceQuotient K C n :=
  FiniteGroupQuotient.quotientπ_comp_descendedMap
    (orderedAmbientAction (Spec (.of K)) (n + 1) C)
    (curveOrderedAmbient_hasAffineOrbit_succ K C n)
    (orderedPointedToIncidenceQuotient K C n)
    (orderedPointedToIncidenceQuotient_invariant K C n)

/-- The pointed symmetric-power comparison
`C × Sym^(n+1)(C) ⟶ D_(n+2)`. -/
noncomputable def productSymmetricPowerToIncidenceQuotient (n : ℕ) :
    (C ⨯ SymmetricPower.curveSchemeSucc K C n).left ⟶
      curveOrderedIncidenceQuotientSucc K C (n + 1) :=
  (curveAmbientQuotientSymmetricProductIso K C n).inv ≫
    ambientQuotientToIncidenceQuotientPointed K C n

/-- Pulling the pointed comparison back to ordered coordinates is exactly
scheme-theoretic insertion followed by the incidence quotient projection. -/
@[reassoc]
theorem curveOrderedAmbientToSymmetricProduct_comp_pointedComparison
    (n : ℕ) :
    curveOrderedAmbientToSymmetricProductSucc K C n ≫
        productSymmetricPowerToIncidenceQuotient K C n =
      orderedPointedToIncidenceQuotient K C n := by
  rw [productSymmetricPowerToIncidenceQuotient, ← Category.assoc]
  change curveOrderedAmbientToSymmetricProductSucc K C n ≫
      curveSymmetricProductToAmbientQuotientSucc K C n ≫
        ambientQuotientToIncidenceQuotientPointed K C n = _
  rw [← Category.assoc,
    curveOrderedAmbientToSymmetricProductSucc_comp_inverse,
    curveOrderedAmbientQuotientProjection_comp_pointedDescent]

/-- Ordered pointed addition respects the structure maps to the field. -/
@[reassoc]
theorem orderedPointedToIncidenceQuotient_comp_structureMap (n : ℕ) :
    orderedPointedToIncidenceQuotient K C n ≫
        curveOrderedIncidenceQuotientStructureMapSucc K C (n + 1) =
      (orderedAmbient (Spec (.of K)) (n + 1) C).hom := by
  rw [orderedPointedToIncidenceQuotient, Category.assoc,
    curveOrderedIncidenceQuotientProjection_comp_structureMap,
    curveOrderedIncidenceStructureMapSucc, ← Category.assoc,
    PointedIncidence.orderedPointedIncidenceMap_comp_ι]
  exact (PointedIncidence.orderedAmbientInsertion
    (Spec (.of K)) (n + 1) C).w

/-- The pointed symmetric-power comparison is a morphism over the ground
field. -/
@[reassoc]
theorem productSymmetricPowerToIncidenceQuotient_comp_structureMap
    (n : ℕ) :
    productSymmetricPowerToIncidenceQuotient K C n ≫
        curveOrderedIncidenceQuotientStructureMapSucc K C (n + 1) =
      (C ⨯ SymmetricPower.curveSchemeSucc K C n).hom := by
  let q := curveOrderedAmbientQuotientProjectionSucc K C n
  let e := curveAmbientQuotientToSymmetricProductSucc K C n
  haveI : Epi q := FiniteGroupQuotient.epi_quotientπ
    (orderedAmbientAction (Spec (.of K)) (n + 1) C)
    (curveOrderedAmbient_hasAffineOrbit_succ K C n)
  haveI : IsIso e := curveAmbientQuotientToSymmetricProductSucc_isIso K C n
  haveI : Epi (q ≫ e) := inferInstance
  have hqe : q ≫ e = curveOrderedAmbientToSymmetricProductSucc K C n :=
    curveOrderedAmbientQuotientProjection_comp_toSymmetricProduct K C n
  haveI : Epi (curveOrderedAmbientToSymmetricProductSucc K C n) := hqe ▸ inferInstance
  apply (cancel_epi (curveOrderedAmbientToSymmetricProductSucc K C n)).mp
  rw [← Category.assoc,
    curveOrderedAmbientToSymmetricProduct_comp_pointedComparison,
    orderedPointedToIncidenceQuotient_comp_structureMap,
    curveOrderedAmbientToSymmetricProductSucc_comp_structureMap]

/-- The incidence quotient, packaged as a scheme over the ground field. -/
noncomputable def curveOrderedIncidenceQuotientOverSucc (n : ℕ) :
    Over (Spec (.of K)) :=
  Over.mk (curveOrderedIncidenceQuotientStructureMapSucc K C n)

/-- The pointed comparison as a morphism over the ground field. -/
noncomputable def productSymmetricPowerToIncidenceQuotientOver (n : ℕ) :
    C ⨯ SymmetricPower.curveSchemeSucc K C n ⟶
      curveOrderedIncidenceQuotientOverSucc K C (n + 1) :=
  Over.homMk (productSymmetricPowerToIncidenceQuotient K C n)
    (productSymmetricPowerToIncidenceQuotient_comp_structureMap K C n)

/-- The descended incidence morphism, packaged over the ground field. -/
noncomputable def curveDescendedIncidenceOverSucc (n : ℕ) :
    curveOrderedIncidenceQuotientOverSucc K C n ⟶
      C ⨯ SymmetricPower.curveSchemeSucc K C n :=
  Over.homMk (curveDescendedIncidenceιSucc K C n)
    (curveDescendedIncidenceιSucc_comp_structureMap K C n)

/-- Add the distinguished point to an effective divisor:
`C × Sym^(n+1)(C) ⟶ Sym^(n+2)(C)`.  This definition is obtained from
the checked incidence quotient and is the map used by the local root-chart
comparison. -/
noncomputable def pointedSymmetricPowerAddition (n : ℕ) :
    C ⨯ SymmetricPower.curveSchemeSucc K C n ⟶
      SymmetricPower.curveSchemeSucc K C (n + 1) :=
  productSymmetricPowerToIncidenceQuotientOver K C n ≫
    curveDescendedIncidenceOverSucc K C (n + 1) ≫
      (Limits.prod.snd :
        C ⨯ SymmetricPower.curveSchemeSucc K C (n + 1) ⟶
          SymmetricPower.curveSchemeSucc K C (n + 1))

theorem pointedSymmetricPowerAddition_left (n : ℕ) :
    (pointedSymmetricPowerAddition K C n).left =
      productSymmetricPowerToIncidenceQuotient K C n ≫
        curveDescendedIncidenceιSucc K C (n + 1) ≫
          (Limits.prod.snd :
            C ⨯ SymmetricPower.curveSchemeSucc K C (n + 1) ⟶
              SymmetricPower.curveSchemeSucc K C (n + 1)).left :=
  rfl

/-- The incidence comparison retains the distinguished curve coordinate. -/
@[reassoc]
theorem productSymmetricPowerToIncidenceQuotient_comp_descendedIncidence_fst
    (n : ℕ) :
    productSymmetricPowerToIncidenceQuotient K C n ≫
        curveDescendedIncidenceιSucc K C (n + 1) ≫
          (Limits.prod.fst :
            C ⨯ SymmetricPower.curveSchemeSucc K C (n + 1) ⟶ C).left =
      (Limits.prod.fst :
        C ⨯ SymmetricPower.curveSchemeSucc K C n ⟶ C).left := by
  let q := curveOrderedAmbientQuotientProjectionSucc K C n
  let e := curveAmbientQuotientToSymmetricProductSucc K C n
  haveI : Epi q := FiniteGroupQuotient.epi_quotientπ
    (orderedAmbientAction (Spec (.of K)) (n + 1) C)
    (curveOrderedAmbient_hasAffineOrbit_succ K C n)
  haveI : IsIso e := curveAmbientQuotientToSymmetricProductSucc_isIso K C n
  haveI : Epi (q ≫ e) := inferInstance
  have hqe : q ≫ e = curveOrderedAmbientToSymmetricProductSucc K C n :=
    curveOrderedAmbientQuotientProjection_comp_toSymmetricProduct K C n
  haveI : Epi (curveOrderedAmbientToSymmetricProductSucc K C n) := hqe ▸ inferInstance
  apply (cancel_epi (curveOrderedAmbientToSymmetricProductSucc K C n)).mp
  rw [← Category.assoc,
    curveOrderedAmbientToSymmetricProduct_comp_pointedComparison,
    orderedPointedToIncidenceQuotient]
  simp only [Category.assoc]
  rw [curveOrderedIncidenceQuotientProjection_comp_descendedIncidenceι_assoc,
    PointedIncidence.orderedPointedIncidenceMap_comp_ι_assoc]
  change
    (PointedIncidence.orderedAmbientInsertion
        (Spec (.of K)) (n + 1) C ≫
      Limits.prod.map (𝟙 C)
        (SymmetricPower.curveProjectionSucc K C (n + 1)) ≫
      (Limits.prod.fst :
        C ⨯ SymmetricPower.curveSchemeSucc K C (n + 1) ⟶ C)).left =
    (Limits.prod.map (𝟙 C)
        (SymmetricPower.curveProjectionSucc K C n) ≫
      (Limits.prod.fst :
        C ⨯ SymmetricPower.curveSchemeSucc K C n ⟶ C)).left
  rw [Limits.prod.map_fst, Limits.prod.map_fst, Category.comp_id,
    PointedIncidence.orderedAmbientInsertion_comp_pointProjection]
  rfl

/-- The composite into `C × Sym^(n+2)(C)` is the graph of pointed
addition.  Thus proving the incidence comparison is an isomorphism is
exactly the construction of the universal effective divisor as this graph. -/
theorem productSymmetricPowerToIncidenceQuotientOver_comp_descendedIncidenceOver
    (n : ℕ) :
    productSymmetricPowerToIncidenceQuotientOver K C n ≫
        curveDescendedIncidenceOverSucc K C (n + 1) =
      Limits.prod.lift
        (Limits.prod.fst :
          C ⨯ SymmetricPower.curveSchemeSucc K C n ⟶ C)
        (pointedSymmetricPowerAddition K C n) := by
  apply Limits.prod.hom_ext
  · rw [Limits.prod.lift_fst, Category.assoc]
    apply CostructuredArrow.hom_ext
    exact
      productSymmetricPowerToIncidenceQuotient_comp_descendedIncidence_fst
        K C n
  · rw [Limits.prod.lift_snd, Category.assoc]
    rfl

/-- On ordered coordinates, pointed addition prepends the distinguished
point and then takes the symmetric quotient. -/
@[reassoc]
theorem curveOrderedAmbientToSymmetricProduct_comp_pointedAddition
    (n : ℕ) :
    curveOrderedAmbientToSymmetricProductSucc K C n ≫
        (pointedSymmetricPowerAddition K C n).left =
      (PointedIncidence.prependPower
          (Spec (.of K)) (n + 1) C).left ≫
        (SymmetricPower.curveProjectionSucc K C (n + 1)).left := by
  rw [pointedSymmetricPowerAddition_left, ← Category.assoc,
    curveOrderedAmbientToSymmetricProduct_comp_pointedComparison,
    orderedPointedToIncidenceQuotient]
  simp only [Category.assoc]
  rw [curveOrderedIncidenceQuotientProjection_comp_descendedIncidenceι_assoc,
    PointedIncidence.orderedPointedIncidenceMap_comp_ι_assoc]
  change
    (PointedIncidence.orderedAmbientInsertion
        (Spec (.of K)) (n + 1) C ≫
      Limits.prod.map (𝟙 C)
        (SymmetricPower.curveProjectionSucc K C (n + 1)) ≫
      (Limits.prod.snd :
        C ⨯ SymmetricPower.curveSchemeSucc K C (n + 1) ⟶
          SymmetricPower.curveSchemeSucc K C (n + 1))).left =
    (PointedIncidence.prependPower (Spec (.of K)) (n + 1) C ≫
      SymmetricPower.curveProjectionSucc K C (n + 1)).left
  apply congrArg Over.Hom.left
  rw [Limits.prod.map_snd, ← Category.assoc,
    PointedIncidence.orderedAmbientInsertion, Limits.prod.lift_snd]

/-- The pointed comparison covers every point of the incidence quotient.
Lift an incidence point to the ordered incidence family, choose a coordinate
graph containing that lift, delete the chosen coordinate, and reinsert it as
coordinate zero.  The explicit reindexing identity shows that the resulting
point differs from the original lift by a permutation, hence has the same
image in the quotient. -/
theorem productSymmetricPowerToIncidenceQuotient_surjective (n : ℕ) :
    Function.Surjective
      (productSymmetricPowerToIncidenceQuotient K C n) := by
  classical
  intro y
  let q := curveOrderedIncidenceQuotientProjectionSucc K C (n + 1)
  obtain ⟨a, ha⟩ := q.surjective y
  obtain ⟨i, z, hz⟩ :=
    orderedIncidence_exists_coordinateGraph_preimage
      (Spec (.of K)) (n + 2) C a
  let b : (orderedAmbient (Spec (.of K)) (n + 1) C).left :=
    (PointedIncidence.removeCoordinate
      (Spec (.of K)) (n + 1) C i).left
        ((coordinateGraphι (Spec (.of K)) (n + 2) C i).left z)
  let g : Equiv.Perm (Fin (n + 2)) :=
    (PointedIncidence.moveZeroTo (n + 1) i).symm
  have hrecover :
      (orderedAmbientAction (Spec (.of K)) (n + 2) C).hom g
          ((PointedIncidence.orderedAmbientInsertion
            (Spec (.of K)) (n + 1) C).left b) =
        orderedIncidenceι (Spec (.of K)) (n + 2) C a := by
    change
      (orderedAmbientPermutationHom (Spec (.of K)) (n + 2) C g).left
          ((PointedIncidence.orderedAmbientInsertion
            (Spec (.of K)) (n + 1) C).left b) =
        orderedIncidenceι (Spec (.of K)) (n + 2) C a
    have h := congrArg Over.Hom.left
      (PointedIncidence.coordinateGraphι_comp_removeCoordinate_comp_insertion_comp_permutation
        (Spec (.of K)) (n + 1) C i)
    have hz' := congrArg
      (fun m : (coordinateGraph (Spec (.of K)) (n + 2) C i).left ⟶
          (orderedAmbient (Spec (.of K)) (n + 2) C).left ↦ m z) h
    simpa only [Over.comp_left, Scheme.Hom.comp_apply, b, g] using hz'.trans hz
  have horbit :
      (orderedIncidenceAction (Spec (.of K)) (n + 2) C).hom g
          (PointedIncidence.orderedPointedIncidenceMap
            (Spec (.of K)) (n + 1) C b) = a := by
    apply (orderedIncidenceι (Spec (.of K)) (n + 2) C).isEmbedding.injective
    let v := PointedIncidence.orderedPointedIncidenceMap
      (Spec (.of K)) (n + 1) C b
    have hequivariant := congrArg
      (fun m : orderedIncidence (Spec (.of K)) (n + 2) C ⟶
          (orderedAmbient (Spec (.of K)) (n + 2) C).left ↦ m v)
      (orderedIncidenceAction_comp_ι
        (Spec (.of K)) (n + 2) C g)
    have hinsertion := congrArg
      (fun m : (orderedAmbient (Spec (.of K)) (n + 1) C).left ⟶
          (orderedAmbient (Spec (.of K)) (n + 2) C).left ↦ m b)
      (PointedIncidence.orderedPointedIncidenceMap_comp_ι
        (Spec (.of K)) (n + 1) C)
    calc
      orderedIncidenceι (Spec (.of K)) (n + 2) C
          ((orderedIncidenceAction (Spec (.of K)) (n + 2) C).hom g v) =
          (orderedAmbientAction (Spec (.of K)) (n + 2) C).hom g
            (orderedIncidenceι (Spec (.of K)) (n + 2) C v) := by
        simpa only [Scheme.Hom.comp_apply] using hequivariant
      _ = (orderedAmbientAction (Spec (.of K)) (n + 2) C).hom g
            ((PointedIncidence.orderedAmbientInsertion
              (Spec (.of K)) (n + 1) C).left b) := by
        exact congrArg
          ((orderedAmbientAction (Spec (.of K)) (n + 2) C).hom g)
          (by simpa only [v, Scheme.Hom.comp_apply] using hinsertion)
      _ = orderedIncidenceι (Spec (.of K)) (n + 2) C a := hrecover
  refine ⟨curveOrderedAmbientToSymmetricProductSucc K C n b, ?_⟩
  calc
    productSymmetricPowerToIncidenceQuotient K C n
        (curveOrderedAmbientToSymmetricProductSucc K C n b) =
        orderedPointedToIncidenceQuotient K C n b := by
      have h := congrArg
        (fun m : (orderedAmbient (Spec (.of K)) (n + 1) C).left ⟶
            curveOrderedIncidenceQuotientSucc K C (n + 1) ↦ m b)
        (curveOrderedAmbientToSymmetricProduct_comp_pointedComparison K C n)
      simpa only [Scheme.Hom.comp_apply] using h
    _ = q a := by
      change q
          (PointedIncidence.orderedPointedIncidenceMap
            (Spec (.of K)) (n + 1) C b) = q a
      apply (FiniteGroupQuotient.quotientπ_apply_eq_iff
        (orderedIncidenceAction (Spec (.of K)) (n + 2) C)
        (curveOrderedIncidence_hasAffineOrbit_succ K C (n + 1)) _ _).mpr
      exact ⟨g, horbit⟩
    _ = y := ha

instance productSymmetricPowerToIncidenceQuotient_surjectiveProperty
    (n : ℕ) :
    Surjective (productSymmetricPowerToIncidenceQuotient K C n) :=
  ⟨productSymmetricPowerToIncidenceQuotient_surjective K C n⟩

/-- The pointed symmetric-power comparison is proper. -/
instance productSymmetricPowerToIncidenceQuotient_isProper (n : ℕ) :
    IsProper (productSymmetricPowerToIncidenceQuotient K C n) := by
  let f := productSymmetricPowerToIncidenceQuotient K C n
  let t := curveOrderedIncidenceQuotientStructureMapSucc K C (n + 1)
  letI : IsProper t :=
    curveOrderedIncidenceQuotientStructureMapSucc_isProper K C (n + 1)
  letI : IsSeparated t := IsProper.toIsSeparated
  letI : IsProper (f ≫ t) := by
    rw [productSymmetricPowerToIncidenceQuotient_comp_structureMap K C n]
    exact curveProductSymmetricPower_isProper K C n
  exact IsProper.of_comp f t

/-- Pointed addition is proper.  The remaining local task for finiteness is
therefore only quasi-finiteness of its divisor fibers. -/
instance pointedSymmetricPowerAddition_isProper (n : ℕ) :
    IsProper (pointedSymmetricPowerAddition K C n).left := by
  rw [pointedSymmetricPowerAddition_left]
  infer_instance

/-- Every point fiber of pointed addition is finite.  After choosing an
ordered lift of the target divisor and an ordered lift of each source
divisor, a point of the fiber determines a permutation carrying the
prepended source tuple to the fixed target tuple.  Choosing one such
permutation gives an injection of the fiber into the finite symmetric
group: equality of permutations forces equality of the prepended tuples,
and `unprependPower` then recovers the source lift. -/
theorem pointedSymmetricPowerAddition_finite_preimage_singleton
    (n : ℕ)
    (y : (SymmetricPower.curveSchemeSucc K C (n + 1)).left) :
    ((pointedSymmetricPowerAddition K C n).left ⁻¹' {y}).Finite := by
  classical
  let f := (pointedSymmetricPowerAddition K C n).left
  let p := curveOrderedAmbientToSymmetricProductSucc K C n
  let r := (SymmetricPower.curveProjectionSucc K C (n + 1)).left
  let σ := SymmetricPower.Action (Spec (.of K)) (n + 2) C
  let hσ := SymmetricPower.curve_hasAffineOrbits_succ K C (n + 1)
  obtain ⟨b, hb⟩ := r.surjective y
  let a (z : f ⁻¹' {y}) :
      (orderedAmbient (Spec (.of K)) (n + 1) C).left :=
    Classical.choose (p.surjective z.1)
  have ha (z : f ⁻¹' {y}) : p (a z) = z.1 :=
    Classical.choose_spec (p.surjective z.1)
  have hz (z : f ⁻¹' {y}) : f z.1 = y := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using z.2
  have horbit (z : f ⁻¹' {y}) :
      ∃ g : Equiv.Perm (Fin (n + 2)),
        σ.hom g
            ((PointedIncidence.prependPower
              (Spec (.of K)) (n + 1) C).left (a z)) = b := by
    apply (FiniteGroupQuotient.quotientπ_apply_eq_iff σ hσ
      ((PointedIncidence.prependPower
        (Spec (.of K)) (n + 1) C).left (a z)) b).mp
    change r
        ((PointedIncidence.prependPower
          (Spec (.of K)) (n + 1) C).left (a z)) = r b
    rw [hb]
    calc
      r ((PointedIncidence.prependPower
          (Spec (.of K)) (n + 1) C).left (a z)) =
          f (p (a z)) := by
        have h := congrArg
          (fun q : (orderedAmbient (Spec (.of K)) (n + 1) C).left ⟶
              (SymmetricPower.curveSchemeSucc K C (n + 1)).left ↦ q (a z))
          (curveOrderedAmbientToSymmetricProduct_comp_pointedAddition
            K C n)
        simpa only [Scheme.Hom.comp_apply] using h.symm
      _ = f z.1 := congrArg f (ha z)
      _ = y := hz z
  let permutation (z : f ⁻¹' {y}) : Equiv.Perm (Fin (n + 2)) :=
    Classical.choose (horbit z)
  have hpermutation (z : f ⁻¹' {y}) :
      σ.hom (permutation z)
          ((PointedIncidence.prependPower
            (Spec (.of K)) (n + 1) C).left (a z)) = b :=
    Classical.choose_spec (horbit z)
  have hinjective : Function.Injective permutation := by
    intro z w hzw
    apply Subtype.ext
    have haction :
        σ.hom (permutation z)
            ((PointedIncidence.prependPower
              (Spec (.of K)) (n + 1) C).left (a z)) =
          σ.hom (permutation z)
            ((PointedIncidence.prependPower
              (Spec (.of K)) (n + 1) C).left (a w)) := by
      simpa only [hzw] using
        (hpermutation z).trans (hpermutation w).symm
    have hprepend :
        (PointedIncidence.prependPower
            (Spec (.of K)) (n + 1) C).left (a z) =
          (PointedIncidence.prependPower
            (Spec (.of K)) (n + 1) C).left (a w) :=
      (σ.hom (permutation z)).isEmbedding.injective haction
    have haw : a z = a w :=
      PointedIncidence.prependPower_injective
        (Spec (.of K)) (n + 1) C hprepend
    exact (ha z).symm.trans ((congrArg p haw).trans (ha w))
  letI : Finite (f ⁻¹' {y}) :=
    Finite.of_injective permutation hinjective
  exact Set.toFinite (f ⁻¹' {y})

/-- Pointed addition is locally quasi-finite because all of its point
fibers inject into a finite symmetric group. -/
instance pointedSymmetricPowerAddition_locallyQuasiFinite (n : ℕ) :
    LocallyQuasiFinite (pointedSymmetricPowerAddition K C n).left := by
  apply LocallyQuasiFinite.of_finite_preimage_singleton
  exact pointedSymmetricPowerAddition_finite_preimage_singleton K C n

/-- Pointed addition is finite: it is proper and locally quasi-finite. -/
instance pointedSymmetricPowerAddition_isFinite (n : ℕ) :
    IsFinite (pointedSymmetricPowerAddition K C n).left :=
  IsFinite.of_isProper_of_locallyQuasiFinite
    (pointedSymmetricPowerAddition K C n).left

/-- A point fiber of the comparison with the incidence quotient is contained
in a point fiber of pointed addition, obtained by applying the descended
incidence morphism and then projecting to the symmetric-power coordinate. -/
theorem productSymmetricPowerToIncidenceQuotient_finite_preimage_singleton
    (n : ℕ) (y : curveOrderedIncidenceQuotientSucc K C (n + 1)) :
    ((productSymmetricPowerToIncidenceQuotient K C n) ⁻¹' {y}).Finite := by
  let t :=
    (Limits.prod.snd :
      C ⨯ SymmetricPower.curveSchemeSucc K C (n + 1) ⟶
        SymmetricPower.curveSchemeSucc K C (n + 1)).left
      (curveDescendedIncidenceιSucc K C (n + 1) y)
  refine
    (pointedSymmetricPowerAddition_finite_preimage_singleton K C n t).subset ?_
  intro z hz
  have hzy : productSymmetricPowerToIncidenceQuotient K C n z = y := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hz
  change (pointedSymmetricPowerAddition K C n).left z = t
  rw [pointedSymmetricPowerAddition_left]
  simp only [Scheme.Hom.comp_apply, hzy, t]

/-- The comparison with the incidence quotient is locally quasi-finite. -/
instance productSymmetricPowerToIncidenceQuotient_locallyQuasiFinite
    (n : ℕ) :
    LocallyQuasiFinite
      (productSymmetricPowerToIncidenceQuotient K C n) := by
  apply LocallyQuasiFinite.of_finite_preimage_singleton
  exact
    productSymmetricPowerToIncidenceQuotient_finite_preimage_singleton K C n

/-- The comparison with the incidence quotient is finite.  The subsequent
local monic-root calculation can therefore identify a finite algebra rather
than first establishing quasi-compactness separately. -/
instance productSymmetricPowerToIncidenceQuotient_isFinite (n : ℕ) :
    IsFinite (productSymmetricPowerToIncidenceQuotient K C n) :=
  IsFinite.of_isProper_of_locallyQuasiFinite
    (productSymmetricPowerToIncidenceQuotient K C n)

/-- The candidate degree-`n + 2` universal effective divisor, written in
its explicit pointed symmetric-power presentation
`(x, D) ↦ (x, x + D)`.  The named downstream consumer is the Abel map in
`PicardRepresentability`; flatness, rank, and Cartier-ness are deliberately
left to the local monic-root comparison. -/
noncomputable def pointedUniversalEffectiveDivisor (n : ℕ) :
    (C ⨯ SymmetricPower.curveSchemeSucc K C n).left ⟶
      (C ⨯ SymmetricPower.curveSchemeSucc K C (n + 1)).left :=
  (Limits.prod.lift
    (Limits.prod.fst :
      C ⨯ SymmetricPower.curveSchemeSucc K C n ⟶ C)
    (pointedSymmetricPowerAddition K C n)).left

/-- The explicit pointed divisor factors through the finite incidence
quotient and its descended finite morphism. -/
theorem pointedUniversalEffectiveDivisor_eq_incidenceComposite (n : ℕ) :
    pointedUniversalEffectiveDivisor K C n =
      productSymmetricPowerToIncidenceQuotient K C n ≫
        curveDescendedIncidenceιSucc K C (n + 1) := by
  exact congrArg Over.Hom.left
    (productSymmetricPowerToIncidenceQuotientOver_comp_descendedIncidenceOver
      K C n).symm

/-- The pointed universal-divisor candidate is finite over
`C × Sym^(n+2)(C)`. -/
instance pointedUniversalEffectiveDivisor_isFinite (n : ℕ) :
    IsFinite (pointedUniversalEffectiveDivisor K C n) := by
  rw [pointedUniversalEffectiveDivisor_eq_incidenceComposite]
  infer_instance

/-- The pointed comparison is an isomorphism once it becomes one after an
fpqc cover of the incidence quotient.  The downstream consumer is the local
monic-root chart comparison: its explicit affine isomorphisms provide the
pullback instance, while this theorem performs the global descent step. -/
theorem productSymmetricPowerToIncidenceQuotient_isIso_of_fpqc
    (n : ℕ) (T : Scheme.{u})
    (q : T ⟶ curveOrderedIncidenceQuotientSucc K C (n + 1))
    [Surjective q] [Flat q] [QuasiCompact q]
    [IsIso (pullback.fst q
      (productSymmetricPowerToIncidenceQuotient K C n))] :
    IsIso (productSymmetricPowerToIncidenceQuotient K C n) := by
  exact MorphismProperty.of_pullback_fst_of_descendsAlong
    (P := MorphismProperty.isomorphisms Scheme.{u})
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := q) (g := productSymmetricPowerToIncidenceQuotient K C n)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance

/-- The pointed comparison may be checked on an independently chosen fpqc
chart around every point of the incidence quotient. -/
theorem productSymmetricPowerToIncidenceQuotient_isIso_of_pointwise_fpqc
    (n : ℕ)
    (U : curveOrderedIncidenceQuotientSucc K C (n + 1) →
      (curveOrderedIncidenceQuotientSucc K C (n + 1)).Opens)
    (mem : ∀ y, y ∈ U y)
    (T : curveOrderedIncidenceQuotientSucc K C (n + 1) → Scheme.{u})
    (q : ∀ y, T y ⟶ (U y).toScheme)
    [∀ y, Surjective (q y)] [∀ y, Flat (q y)] [∀ y, QuasiCompact (q y)]
    [∀ y, IsIso (pullback.fst (q y)
      (productSymmetricPowerToIncidenceQuotient K C n ∣_ U y))] :
    IsIso (productSymmetricPowerToIncidenceQuotient K C n) :=
  FpqcDescent.isIso_of_pointwise_fpqc_pullback
    (productSymmetricPowerToIncidenceQuotient K C n) U mem T q

/-- The universal-divisor candidate is flat once the local monic-root model
identifies its pullback along an fpqc chart as flat. -/
theorem pointedUniversalEffectiveDivisor_flat_of_fpqc
    (n : ℕ) (T : Scheme.{u})
    (q : T ⟶ (C ⨯ SymmetricPower.curveSchemeSucc K C (n + 1)).left)
    [Surjective q] [Flat q] [QuasiCompact q]
    [Flat (pullback.fst q (pointedUniversalEffectiveDivisor K C n))] :
    Flat (pointedUniversalEffectiveDivisor K C n) :=
  FpqcDescent.flat_of_fpqc_pullback
    (pointedUniversalEffectiveDivisor K C n) q

/-- Flatness of the universal-divisor candidate may be checked on one fpqc
chart chosen around each point of `C × Sym^(n+2)(C)`. -/
theorem pointedUniversalEffectiveDivisor_flat_of_pointwise_fpqc
    (n : ℕ)
    (U : (C ⨯ SymmetricPower.curveSchemeSucc K C (n + 1)).left →
      (C ⨯ SymmetricPower.curveSchemeSucc K C (n + 1)).left.Opens)
    (mem : ∀ y, y ∈ U y)
    (T : (C ⨯ SymmetricPower.curveSchemeSucc K C (n + 1)).left → Scheme.{u})
    (q : ∀ y, T y ⟶ (U y).toScheme)
    [∀ y, Surjective (q y)] [∀ y, Flat (q y)] [∀ y, QuasiCompact (q y)]
    [∀ y, Flat (pullback.fst (q y)
      (pointedUniversalEffectiveDivisor K C n ∣_ U y))] :
    Flat (pointedUniversalEffectiveDivisor K C n) :=
  FpqcDescent.flat_of_pointwise_fpqc_pullback
    (pointedUniversalEffectiveDivisor K C n) U mem T q

/-- If the local monic-root model has constant rank `n + 2`, then the
global universal-divisor candidate is finite flat of that same rank. -/
theorem pointedUniversalEffectiveDivisor_finrank_eq_of_fpqc
    (n : ℕ) (T : Scheme.{u})
    (q : T ⟶ (C ⨯ SymmetricPower.curveSchemeSucc K C (n + 1)).left)
    [Surjective q] [Flat q] [QuasiCompact q]
    [Flat (pullback.fst q (pointedUniversalEffectiveDivisor K C n))]
    (h : (pullback.fst q (pointedUniversalEffectiveDivisor K C n)).finrank =
      fun _ ↦ n + 2) :
    (pointedUniversalEffectiveDivisor K C n).finrank = fun _ ↦ n + 2 := by
  letI : Flat (pointedUniversalEffectiveDivisor K C n) :=
    pointedUniversalEffectiveDivisor_flat_of_fpqc K C n T q
  exact FpqcDescent.finrank_eq_of_surjective_baseChange
    (pointedUniversalEffectiveDivisor K C n) q (n + 2) h

/-- The constant degree of the universal-divisor candidate may likewise be
checked on independently chosen pointwise fpqc charts. -/
theorem pointedUniversalEffectiveDivisor_finrank_eq_of_pointwise_fpqc
    (n : ℕ)
    (U : (C ⨯ SymmetricPower.curveSchemeSucc K C (n + 1)).left →
      (C ⨯ SymmetricPower.curveSchemeSucc K C (n + 1)).left.Opens)
    (mem : ∀ y, y ∈ U y)
    (T : (C ⨯ SymmetricPower.curveSchemeSucc K C (n + 1)).left → Scheme.{u})
    (q : ∀ y, T y ⟶ (U y).toScheme)
    [∀ y, Surjective (q y)] [∀ y, Flat (q y)] [∀ y, QuasiCompact (q y)]
    [∀ y, Flat (pullback.fst (q y)
      (pointedUniversalEffectiveDivisor K C n ∣_ U y))]
    (h : ∀ y, (pullback.fst (q y)
      (pointedUniversalEffectiveDivisor K C n ∣_ U y)).finrank =
        fun _ ↦ n + 2) :
    (pointedUniversalEffectiveDivisor K C n).finrank = fun _ ↦ n + 2 :=
  FpqcDescent.finrank_eq_of_pointwise_fpqc_baseChange
    (pointedUniversalEffectiveDivisor K C n) U mem T q (n + 2) h

end MazurTorsion.AlgebraicGeometry.Jacobian.PointedIncidenceDescent
