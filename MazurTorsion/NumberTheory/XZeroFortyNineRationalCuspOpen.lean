/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/

import Mathlib.AlgebraicGeometry.Morphisms.Affine
import MazurTorsion.NumberTheory.XZeroFortyNineSchemeModel

/-!
# A rational-cusp-avoiding open of the represented `X_0(49)` target

Inside the explicit projective cubic, the standard projective basic open
`D(X)` removes both rational cusps: the point at infinity has coordinates
`[0 : 1 : 0]`, while the finite cusp has coordinates `[0 : 0 : 1]`.
This file constructs that open as an actual scheme and proves that every
scheme-valued rational point factoring through it avoids both rational cusp
morphisms.  It does not identify `D(X)` with the complement of all geometric
cusps.

The design boundary is deliberately target-side.  No modular interpretation
or comparison with a coarse moduli fibre is asserted here.  The named
downstream consumer is
`MazurTorsion.XZeroFortyNine.CoarseComparison.RationalFiberOpenComparison`,
whose comparison map will land in this open rather than carrying a separate
noncuspidality hypothesis.  The affine presentation below also supplies the
coordinate-ring target for a future scheme-level eta-coordinate comparison.
-/

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
open MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic

namespace MazurTorsion.XZeroFortyNine.SchemeModel

/-- The ambient projective basic open on which the homogeneous `X` coordinate
is nonzero. -/
def xNonzeroAmbientOpen :
    (WeierstrassProjectiveCubic.projectivePlane ℚ).Opens :=
  Proj.basicOpen (homogeneousPieces ℚ) (MvPolynomial.X 0)

/-- The pullback of `D(X)` to the represented projective cubic. -/
def rationalCuspAvoidingOpen : scheme.Opens :=
  WeierstrassProjectiveCubic.inclusion curve ⁻¹ᵁ xNonzeroAmbientOpen

/-- The rational-cusp-avoiding `D(X)` open as an actual scheme. -/
abbrev rationalCuspAvoidingScheme : Scheme := rationalCuspAvoidingOpen.toScheme

/-- The pullback `D(X)` is affine: the ambient Proj basic open is affine, and
the projective cubic is closed in the ambient projective plane. -/
theorem rationalCuspAvoidingOpen_isAffine :
    IsAffineOpen rationalCuspAvoidingOpen := by
  exact
    (Proj.isAffineOpen_basicOpen
      (homogeneousPieces ℚ) (MvPolynomial.X 0)
      (MvPolynomial.isHomogeneous_X ℚ 0) (by omega)).preimage
        (WeierstrassProjectiveCubic.inclusion curve)

instance rationalCuspAvoidingScheme_isAffine :
    IsAffine rationalCuspAvoidingScheme :=
  rationalCuspAvoidingOpen_isAffine

/-- The affine coordinate ring of the rational-cusp-avoiding open. -/
abbrev rationalCuspAvoidingCoordinateRing :=
  Γ(scheme, rationalCuspAvoidingOpen)

/-- The canonical affine presentation of the rational-cusp-avoiding open. -/
def rationalCuspAvoidingIsoSpec :
    rationalCuspAvoidingScheme ≅
      Spec (.of rationalCuspAvoidingCoordinateRing) :=
  rationalCuspAvoidingOpen_isAffine.isoSpec

/-- The open immersion of the rational-cusp-avoiding locus into the projective
cubic. -/
def rationalCuspAvoidingInclusion : rationalCuspAvoidingScheme ⟶ scheme :=
  rationalCuspAvoidingOpen.ι

instance rationalCuspAvoidingInclusion_isOpenImmersion :
    IsOpenImmersion rationalCuspAvoidingInclusion := by
  dsimp only [rationalCuspAvoidingInclusion]
  infer_instance

/-- The rational-cusp-avoiding open over `Spec Q`, using the restriction of
the projective cubic's structure morphism. -/
noncomputable def rationalCuspAvoidingOver : Over (Spec (.of ℚ)) :=
  Over.mk (rationalCuspAvoidingInclusion ≫
    WeierstrassProjectiveCubic.structureMap curve)

private theorem X_mem_ambientPoint_closedPoint_iff
    (P : Fin 3 → ℚ) (hP : P ≠ 0) :
    MvPolynomial.X 0 ∈
        (ambientPoint P hP (IsLocalRing.closedPoint ℚ)).asHomogeneousIdeal ↔
      P 0 = 0 := by
  simpa [MvPolynomial.eval] using
    (mem_ambientPoint_closedPoint_iff P hP (MvPolynomial.X 0)
      (n := 1) (by omega) (MvPolynomial.isHomogeneous_X ℚ 0))

private theorem pointOfNonsingularRepresentative_closedPoint_not_mem_DX
    (P : Fin 3 → ℚ) (hP : curve.toProjective.Nonsingular P)
    (hX : P 0 = 0) :
    (pointOfNonsingularRepresentative curve P hP ≫
        WeierstrassProjectiveCubic.inclusion curve)
        (IsLocalRing.closedPoint ℚ) ∉ xNonzeroAmbientOpen := by
  rw [pointOfNonsingularRepresentative_comp_inclusion]
  change ambientPoint P (nonsingular_ne_zero curve P hP)
      (IsLocalRing.closedPoint ℚ) ∉
    Proj.basicOpen (homogeneousPieces ℚ) (MvPolynomial.X 0)
  rw [Proj.mem_basicOpen, not_not,
    X_mem_ambientPoint_closedPoint_iff]
  exact hX

/-- The point at infinity is outside `D(X)`. -/
theorem infinityCusp_closedPoint_not_mem_rationalCuspAvoidingOpen :
    infinityCusp (IsLocalRing.closedPoint ℚ) ∉ rationalCuspAvoidingOpen := by
  change (infinityCusp ≫ WeierstrassProjectiveCubic.inclusion curve)
      (IsLocalRing.closedPoint ℚ) ∉ xNonzeroAmbientOpen
  have hpoint :
      infinityCusp ≫ WeierstrassProjectiveCubic.inclusion curve =
        pointOfNonsingularRepresentative curve ![0, 1, 0]
            curve.toProjective.nonsingular_zero ≫
          WeierstrassProjectiveCubic.inclusion curve := by
    calc
      infinityCusp ≫ WeierstrassProjectiveCubic.inclusion curve =
          affinePointMorphism curve (.zero : curve.toAffine.Point) ≫
            WeierstrassProjectiveCubic.inclusion curve := by rfl
      _ = pointOfNonsingularRepresentative curve ![0, 1, 0]
            curve.toProjective.nonsingular_zero ≫
          WeierstrassProjectiveCubic.inclusion curve :=
        congrArg (· ≫ WeierstrassProjectiveCubic.inclusion curve)
          (affinePointMorphism_zero curve)
  rw [hpoint]
  exact pointOfNonsingularRepresentative_closedPoint_not_mem_DX
    ![0, 1, 0] curve.toProjective.nonsingular_zero (by simp)

/-- The finite cusp `(0,0)` is outside `D(X)`. -/
theorem finiteCusp_closedPoint_not_mem_rationalCuspAvoidingOpen :
    finiteCusp (IsLocalRing.closedPoint ℚ) ∉ rationalCuspAvoidingOpen := by
  change (finiteCusp ≫ WeierstrassProjectiveCubic.inclusion curve)
      (IsLocalRing.closedPoint ℚ) ∉ xNonzeroAmbientOpen
  have hpoint :
      finiteCusp ≫ WeierstrassProjectiveCubic.inclusion curve =
        pointOfNonsingularRepresentative curve ![0, 0, 1]
            ((curve.toProjective.nonsingular_some 0 0).mpr
              nonsingular_zero_zero) ≫
          WeierstrassProjectiveCubic.inclusion curve := by
    rw [finiteCusp, rationalPointEquiv_apply, T,
      affinePointMorphism_some]
  rw [hpoint]
  exact pointOfNonsingularRepresentative_closedPoint_not_mem_DX
    ![0, 0, 1]
    ((curve.toProjective.nonsingular_some 0 0).mpr nonsingular_zero_zero)
    (by simp)

private theorem comp_openInclusion_apply_mem
    {X Y : Scheme} (U : X.Opens) (g : Y ⟶ U.toScheme) (y : Y) :
    (g ≫ U.ι) y ∈ U := by
  change (g y).val ∈ U
  exact (g y).property

/-- Any rational point factoring through the represented `D(X)` open avoids
both cusp morphisms. -/
theorem comp_rationalCuspAvoidingInclusion_isNoncuspidal
    (g : Spec (.of ℚ) ⟶ rationalCuspAvoidingScheme) :
    IsNoncuspidal (g ≫ rationalCuspAvoidingInclusion) := by
  constructor
  · intro h
    apply infinityCusp_closedPoint_not_mem_rationalCuspAvoidingOpen
    have hmem : (g ≫ rationalCuspAvoidingInclusion) (IsLocalRing.closedPoint ℚ) ∈
        rationalCuspAvoidingOpen := by
      exact comp_openInclusion_apply_mem rationalCuspAvoidingOpen g
        (IsLocalRing.closedPoint ℚ)
    rwa [h] at hmem
  · intro h
    apply finiteCusp_closedPoint_not_mem_rationalCuspAvoidingOpen
    have hmem : (g ≫ rationalCuspAvoidingInclusion) (IsLocalRing.closedPoint ℚ) ∈
        rationalCuspAvoidingOpen := by
      exact comp_openInclusion_apply_mem rationalCuspAvoidingOpen g
        (IsLocalRing.closedPoint ℚ)
    rwa [h] at hmem

/-- The represented rational-cusp-avoiding open has no rational
scheme-valued points. -/
theorem rationalCuspAvoidingScheme_rationalPoints_isEmpty :
    IsEmpty (Spec (.of ℚ) ⟶ rationalCuspAvoidingScheme) := by
  constructor
  intro g
  exact not_isNoncuspidal _
    (comp_rationalCuspAvoidingInclusion_isNoncuspidal g)

/-- Equivalently in affine coordinates, the coordinate ring of `D(X)` has no
ring homomorphism to `Q`. -/
theorem rationalCuspAvoidingCoordinateRing_hom_rat_isEmpty :
    IsEmpty
      (CommRingCat.of rationalCuspAvoidingCoordinateRing ⟶ CommRingCat.of ℚ) := by
  constructor
  intro f
  exact rationalCuspAvoidingScheme_rationalPoints_isEmpty.false
    (Spec.map f ≫ rationalCuspAvoidingIsoSpec.inv)

end MazurTorsion.XZeroFortyNine.SchemeModel
