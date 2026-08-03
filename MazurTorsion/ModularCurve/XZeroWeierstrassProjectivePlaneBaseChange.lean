/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassGeometricIntegrality
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Coefficient extension on the projective Weierstrass ambient plane

For a field extension `K → L`, this file constructs the graded coefficient map on
`K[X,Y,Z]`, verifies the irrelevant-ideal hypothesis for `Proj` from the coordinate generators,
and obtains the resulting projection `P²_L ⟶ P²_K`.  It fixes all three coordinates, sends the
Weierstrass cubic to the coefficient-extended cubic, and satisfies Mathlib's canonical square on
the standard `D₊(Z)` charts.

The final declarations record two honest consumers needed by the geometric-integrality lane.  The
underlying `Proj` point map carries the coefficient-extended cubic zero locus exactly to the
original cubic zero locus, and an explicitly ambient-compatible `StandardChartComparison`
identifies its canonical open range with the pullback of the mapped cubic's `D₊(Z)` open.  No
projective-plane pullback
isomorphism, cubic base-change isomorphism, or scheme-level restriction of the ambient projection
is claimed here.
-/

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open scoped DirectSum

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- Extend coefficients from `K` to `L` in the homogeneous coordinate ring of projective
two-space. -/
noncomputable def projectiveCoefficientMap :
    MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 3) L :=
  MvPolynomial.map (algebraMap K L)

@[simp]
theorem projectiveCoefficientMap_C (a : K) :
    projectiveCoefficientMap (K := K) (L := L) (MvPolynomial.C a) =
      MvPolynomial.C (algebraMap K L a) := by
  simp [projectiveCoefficientMap]

@[simp]
theorem projectiveCoefficientMap_X (i : Fin 3) :
    projectiveCoefficientMap (K := K) (L := L) (MvPolynomial.X i) =
      MvPolynomial.X i := by
  simp [projectiveCoefficientMap]

/-- Coefficient extension preserves every homogeneous degree. -/
noncomputable def projectiveGradedCoefficientMap :
    homogeneousPieces K →+*ᵍ homogeneousPieces L where
  __ := projectiveCoefficientMap (K := K) (L := L)
  map_mem := fun h ↦ MvPolynomial.IsHomogeneous.map h (algebraMap K L)

@[simp]
theorem projectiveGradedCoefficientMap_X (i : Fin 3) :
    projectiveGradedCoefficientMap (K := K) (L := L) (MvPolynomial.X i) =
      MvPolynomial.X i :=
  projectiveCoefficientMap_X i

/-- Coefficient extension takes the actual homogeneous Weierstrass equation to the equation of
the mapped Weierstrass curve. -/
@[simp]
theorem projectiveCoefficientMap_polynomial (W : WeierstrassCurve K) :
    projectiveCoefficientMap (K := K) (L := L) W.toProjective.polynomial =
      (W.map (algebraMap K L)).toProjective.polynomial := by
  simp [projectiveCoefficientMap, WeierstrassCurve.Projective.polynomial]

@[simp]
theorem projectiveGradedCoefficientMap_polynomial (W : WeierstrassCurve K) :
    projectiveGradedCoefficientMap (K := K) (L := L) W.toProjective.polynomial =
      (W.map (algebraMap K L)).toProjective.polynomial :=
  projectiveCoefficientMap_polynomial W

/-- For the standard polynomial grading, the irrelevant ideal is contained in the ideal generated
by the coordinate variables.  The converse is not needed for `Proj.map`. -/
private theorem irrelevant_toIdeal_le_idealOfVars
    (F : Type u) [Field F] :
    (HomogeneousIdeal.irrelevant (homogeneousPieces F)).toIdeal ≤
      MvPolynomial.idealOfVars (Fin 3) F := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro i hi p hp
  change p ∈ MvPolynomial.idealOfVars (Fin 3) F
  rw [← pow_one (MvPolynomial.idealOfVars (Fin 3) F),
    MvPolynomial.mem_pow_idealOfVars_iff']
  intro m hm
  by_contra hcoeff
  have hdegree : Finsupp.degree m = i := by
    rw [Finsupp.degree_eq_weight_one, ← Pi.one_def]
    exact hp hcoeff
  omega

/-- The irrelevant ideal after coefficient extension is covered by the mapped source irrelevant
ideal.  This is the exact hypothesis required by `Proj.map`, proved from the three coordinates
rather than postulated. -/
theorem projectiveGradedCoefficientMap_irrelevant_le :
    HomogeneousIdeal.irrelevant (homogeneousPieces L) ≤
      (HomogeneousIdeal.irrelevant (homogeneousPieces K)).map
        (projectiveGradedCoefficientMap (K := K) (L := L)) := by
  change (HomogeneousIdeal.irrelevant (homogeneousPieces L)).toIdeal ≤
    Ideal.map (projectiveGradedCoefficientMap (K := K) (L := L))
      (HomogeneousIdeal.irrelevant (homogeneousPieces K)).toIdeal
  refine (irrelevant_toIdeal_le_idealOfVars L).trans ?_
  apply Ideal.span_le.2
  rintro _ ⟨i, rfl⟩
  rw [← projectiveCoefficientMap_X (K := K) (L := L) i]
  exact Ideal.mem_map_of_mem _
    (HomogeneousIdeal.mem_irrelevant_of_mem (homogeneousPieces K) (by omega)
      (MvPolynomial.isHomogeneous_X K i))

/-- The projective-plane projection induced by extension of homogeneous-coordinate
coefficients. -/
noncomputable def projectivePlaneBaseChangeProjection :
    projectivePlane L ⟶ projectivePlane K :=
  Proj.map (projectiveGradedCoefficientMap (K := K) (L := L))
    (projectiveGradedCoefficientMap_irrelevant_le (K := K) (L := L))

/-- The projective-plane projection pulls a coordinate basic open back to the same coordinate
basic open. -/
theorem projectivePlaneBaseChangeProjection_preimage_basicOpen (i : Fin 3) :
    projectivePlaneBaseChangeProjection (K := K) (L := L) ⁻¹ᵁ
        Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X i) =
      Proj.basicOpen (homogeneousPieces L) (MvPolynomial.X i) := by
  simpa only [projectivePlaneBaseChangeProjection,
    projectiveGradedCoefficientMap_X] using
      (Proj.map_preimage_basicOpen
        (projectiveGradedCoefficientMap (K := K) (L := L))
        (projectiveGradedCoefficientMap_irrelevant_le (K := K) (L := L))
        (MvPolynomial.X i))

/-- Mathlib's degree-zero localized coefficient map gives the canonical commutative square on
the `i`th coordinate chart.  The `i = 2` specialization is the standard `D₊(Z)` square. -/
@[reassoc]
theorem coordinateAway_comp_projectivePlaneBaseChangeProjection (i : Fin 3) :
    Proj.awayι (homogeneousPieces L)
          (projectiveGradedCoefficientMap (K := K) (L := L) (MvPolynomial.X i))
          ((projectiveGradedCoefficientMap (K := K) (L := L)).map_mem
            (MvPolynomial.isHomogeneous_X K i)) (by omega) ≫
        projectivePlaneBaseChangeProjection (K := K) (L := L) =
      Spec.map (CommRingCat.ofHom
          (HomogeneousLocalization.Away.map
            (projectiveGradedCoefficientMap (K := K) (L := L))
            (MvPolynomial.X i))) ≫
        Proj.awayι (homogeneousPieces K) (MvPolynomial.X i)
          (MvPolynomial.isHomogeneous_X K i) (by omega) := by
  exact Proj.awayι_comp_map
    (projectiveGradedCoefficientMap (K := K) (L := L))
    (projectiveGradedCoefficientMap_irrelevant_le (K := K) (L := L))
    (by omega) (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X K i)

/-- The named standard `D₊(Z)` instance of the coordinate-away square. -/
@[reassoc]
theorem standardAway_comp_projectivePlaneBaseChangeProjection :
    Proj.awayι (homogeneousPieces L)
          (projectiveGradedCoefficientMap (K := K) (L := L)
            (MvPolynomial.X (2 : Fin 3)))
          ((projectiveGradedCoefficientMap (K := K) (L := L)).map_mem
            (MvPolynomial.isHomogeneous_X K 2)) (by omega) ≫
        projectivePlaneBaseChangeProjection (K := K) (L := L) =
      Spec.map (CommRingCat.ofHom
          (HomogeneousLocalization.Away.map
            (projectiveGradedCoefficientMap (K := K) (L := L))
            (MvPolynomial.X (2 : Fin 3)))) ≫
        Proj.awayι (homogeneousPieces K) (MvPolynomial.X (2 : Fin 3))
          (MvPolynomial.isHomogeneous_X K 2) (by omega) :=
  coordinateAway_comp_projectivePlaneBaseChangeProjection (K := K) (L := L) 2

/-- On underlying projective-spectrum points, coefficient extension carries the mapped cubic zero
locus exactly into the original cubic zero locus.  This is the point-level content of the ambient
projection preserving the equation; it does not install a morphism between the reduced induced
cubic schemes. -/
theorem projectiveSpectrum_comap_mem_weierstrassZeroLocus_iff
    (W : WeierstrassCurve K) (p : ProjectiveSpectrum (homogeneousPieces L)) :
    ProjectiveSpectrum.comap
          (projectiveGradedCoefficientMap (K := K) (L := L))
          (projectiveGradedCoefficientMap_irrelevant_le (K := K) (L := L)) p ∈
        ProjectiveSpectrum.zeroLocus (homogeneousPieces K)
          {W.toProjective.polynomial} ↔
      p ∈ ProjectiveSpectrum.zeroLocus (homogeneousPieces L)
        {(W.map (algebraMap K L)).toProjective.polynomial} := by
  rw [ProjectiveSpectrum.mem_zeroLocus, ProjectiveSpectrum.mem_zeroLocus]
  simp only [Set.singleton_subset_iff]
  change W.toProjective.polynomial ∈
      ((ProjectiveSpectrum.comap
          (projectiveGradedCoefficientMap (K := K) (L := L))
          (projectiveGradedCoefficientMap_irrelevant_le (K := K) (L := L)) p).1 :
        Set (MvPolynomial (Fin 3) K)) ↔
    (W.map (algebraMap K L)).toProjective.polynomial ∈
      (p.asHomogeneousIdeal : Set (MvPolynomial (Fin 3) L))
  change projectiveGradedCoefficientMap (K := K) (L := L)
      W.toProjective.polynomial ∈
        (p.asHomogeneousIdeal : Set (MvPolynomial (Fin 3) L)) ↔ _
  rw [projectiveGradedCoefficientMap_polynomial]

/-- Extra compatibility required of a projective base-change comparison before it can be used
to transport the canonical coordinate open.  This equality is deliberately separate from
`StandardChartComparison`: neither its target isomorphism nor the ambient equality is constructed
in this file. -/
def StandardChartComparison.IsAmbientCompatible
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L]
    (D : StandardChartComparison W L) : Prop :=
  (D.targetBaseChangeIso.hom ≫ inclusion (W.map (algebraMap K L))) ≫
      projectivePlaneBaseChangeProjection (K := K) (L := L) =
    fieldBaseChangeAmbientMap W L

/-- An ambient-compatible comparison identifies the canonical standard open in the actual field
pullback with the inverse image of the mapped cubic's `D₊(Z)` open.  This is the compiled
downstream consumer of `StandardChartComparison.IsAmbientCompatible`; constructing the target
isomorphism and this equality remains explicit work. -/
theorem StandardChartComparison.canonicalStandardOpenMap_opensRange_eq_preimage_mapped
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L]
    (D : StandardChartComparison W L) (hD : D.IsAmbientCompatible W L) :
    (canonicalStandardOpenMap W L).opensRange =
      D.targetBaseChangeIso.hom ⁻¹ᵁ
        (inclusion (W.map (algebraMap K L)) ⁻¹ᵁ
          Proj.basicOpen (homogeneousPieces L) (MvPolynomial.X (2 : Fin 3))) := by
  rw [canonicalStandardOpenMap_opensRange_eq_preimage_basicOpen, ← hD]
  simp only [Scheme.Hom.comp_preimage,
    projectivePlaneBaseChangeProjection_preimage_basicOpen]

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
