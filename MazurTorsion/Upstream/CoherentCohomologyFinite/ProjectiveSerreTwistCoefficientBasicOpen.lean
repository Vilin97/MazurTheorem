/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistCoefficientFraction

/-!
# Coefficient extension on a projective pair basic open

The coefficient-extension morphism restricts from
`D₊(XᵢXⱼ)` over the larger coefficient ring to the corresponding basic
open over the smaller ring.  On global sections this restricted morphism
carries the standard degree-zero ratio to the same ratio after coefficient
extension.
-/


open CategoryTheory AlgebraicGeometry HomogeneousLocalization

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

variable {k R : Type} [CommRing k] [CommRing R]
variable (φ : k →+* R) (d : ℕ)

/--
The inverse image of a pair basic open under coefficient extension, with
an arbitrary name for the image of its defining homogeneous polynomial.
Keeping this equality explicit avoids dependent transports in section
naturality arguments.
-/
theorem coefficientMap_preimage_pairBasicOpenTo
    (i j : Fin (d + 1))
    (t : MvPolynomial (Fin (d + 1)) R)
    (h :
      coefficientGradedHom φ d
          (coordinate k i * coordinate k j) = t) :
    coefficientMap φ d ⁻¹ᵁ
        Proj.basicOpen (homogeneousGrading k d)
          (coordinate k i * coordinate k j) =
      Proj.basicOpen (homogeneousGrading R d) t := by
  simp [coefficientMap, h]

/-- The inverse image of `D₊(XᵢXⱼ)` is the same pair basic open. -/
@[simp]
theorem coefficientMap_preimage_pairBasicOpen
    (i j : Fin (d + 1)) :
    coefficientMap φ d ⁻¹ᵁ
        Proj.basicOpen (homogeneousGrading k d)
          (coordinate k i * coordinate k j) =
      Proj.basicOpen (homogeneousGrading R d)
        (coordinate R i * coordinate R j) :=
  coefficientMap_preimage_pairBasicOpenTo φ d i j
    (coordinate R i * coordinate R j) (by simp)

/--
The restriction of coefficient extension between corresponding pair basic
opens.
-/
def coefficientPairBasicOpenMap
    (i j : Fin (d + 1)) :
    (Proj.basicOpen (homogeneousGrading R d)
      (coordinate R i * coordinate R j)).toScheme ⟶
    (Proj.basicOpen (homogeneousGrading k d)
      (coordinate k i * coordinate k j)).toScheme :=
  (coefficientMap φ d).resLE _ _
    (coefficientMap_preimage_pairBasicOpen φ d i j).symm.le

/--
Naturality of `awayToSection` for coefficient extension, with the target
denominator retained as an explicit equality parameter.
-/
theorem coefficientAwayToSection_naturalityTo
    (i j : Fin (d + 1))
    (t : MvPolynomial (Fin (d + 1)) R)
    (h :
      coefficientGradedHom φ d
          (coordinate k i * coordinate k j) = t)
    (x : Away (homogeneousGrading k d)
      (coordinate k i * coordinate k j)) :
    (coefficientMap φ d).appLE
        (Proj.basicOpen (homogeneousGrading k d)
          (coordinate k i * coordinate k j))
        (Proj.basicOpen (homogeneousGrading R d) t)
        (coefficientMap_preimage_pairBasicOpenTo
          φ d i j t h).symm.le
        (Proj.awayToSection (homogeneousGrading k d)
          (coordinate k i * coordinate k j) x) =
      Proj.awayToSection (homogeneousGrading R d) t
        (homogeneousAwayMapTo
          (coefficientGradedHom φ d)
          (coordinate k i * coordinate k j) t h x) := by
  subst t
  have hnat :=
    Proj.awayToSection_comp_appLE
      (coefficientGradedHom φ d)
      (coefficientIrrelevantLE φ d)
      (coordinate_mul_mem_degreeTwo k d i j)
  change
    ((Proj.awayToSection (homogeneousGrading k d)
          (coordinate k i * coordinate k j) ≫
        (Proj.map (coefficientGradedHom φ d)
          (coefficientIrrelevantLE φ d)).appLE
            (Proj.basicOpen (homogeneousGrading k d)
              (coordinate k i * coordinate k j))
            (Proj.basicOpen (homogeneousGrading R d)
              ((coefficientGradedHom φ d)
                (coordinate k i * coordinate k j))) (by rfl)) x) =
      ((CommRingCat.ofHom
          (HomogeneousLocalization.map (coefficientGradedHom φ d) (by
            rintro _ ⟨q, rfl⟩
            exact ⟨q, by simp⟩)) ≫
        Proj.awayToSection (homogeneousGrading R d)
          ((coefficientGradedHom φ d)
            (coordinate k i * coordinate k j))) x)
  exact ConcreteCategory.congr_hom hnat x

/--
On top sections of corresponding pair basic opens, coefficient extension
carries `Xᵢ / Xⱼ` to `Xᵢ / Xⱼ`.
-/
theorem coefficientPairBasicOpenMap_appTop_awayFraction
    (i j : Fin (d + 1)) :
    (coefficientPairBasicOpenMap φ d i j).appTop
        ((Proj.basicOpen (homogeneousGrading k d)
          (coordinate k i * coordinate k j)).topIso.inv
          (Proj.awayToSection (homogeneousGrading k d)
            (coordinate k i * coordinate k j)
            (awayFraction k d i j))) =
      (Proj.basicOpen (homogeneousGrading R d)
        (coordinate R i * coordinate R j)).topIso.inv
          (Proj.awayToSection (homogeneousGrading R d)
            (coordinate R i * coordinate R j)
            (awayFraction R d i j)) := by
  change
    ((coefficientMap φ d).resLE
      (Proj.basicOpen (homogeneousGrading k d)
        (coordinate k i * coordinate k j))
      (Proj.basicOpen (homogeneousGrading R d)
        (coordinate R i * coordinate R j)) _).app ⊤
      ((Proj.basicOpen (homogeneousGrading k d)
        (coordinate k i * coordinate k j)).topIso.inv
        (Proj.awayToSection (homogeneousGrading k d)
          (coordinate k i * coordinate k j)
          (awayFraction k d i j))) = _
  rw [Scheme.Hom.resLE_app_top]
  change
    (Proj.basicOpen (homogeneousGrading R d)
        (coordinate R i * coordinate R j)).topIso.inv
      ((coefficientMap φ d).appLE
        (Proj.basicOpen (homogeneousGrading k d)
          (coordinate k i * coordinate k j))
        (Proj.basicOpen (homogeneousGrading R d)
          (coordinate R i * coordinate R j))
        (coefficientMap_preimage_pairBasicOpen φ d i j).symm.le
        ((Proj.basicOpen (homogeneousGrading k d)
          (coordinate k i * coordinate k j)).topIso.hom
          ((Proj.basicOpen (homogeneousGrading k d)
            (coordinate k i * coordinate k j)).topIso.inv
            (Proj.awayToSection (homogeneousGrading k d)
              (coordinate k i * coordinate k j)
              (awayFraction k d i j))))) = _
  rw [Iso.inv_hom_id_apply]
  have hnat :
      (coefficientMap φ d).appLE
          (Proj.basicOpen (homogeneousGrading k d)
            (coordinate k i * coordinate k j))
          (Proj.basicOpen (homogeneousGrading R d)
            (coordinate R i * coordinate R j))
          (coefficientMap_preimage_pairBasicOpen
            φ d i j).symm.le
          (Proj.awayToSection (homogeneousGrading k d)
            (coordinate k i * coordinate k j)
            (awayFraction k d i j)) =
        Proj.awayToSection (homogeneousGrading R d)
          (coordinate R i * coordinate R j)
          (coefficientPairAwayMap φ d i j
            (awayFraction k d i j)) := by
    simpa [coefficientPairAwayMap] using
      coefficientAwayToSection_naturalityTo φ d i j
        (coordinate R i * coordinate R j) (by simp)
        (awayFraction k d i j)
  exact congrArg
    (Proj.basicOpen (homogeneousGrading R d)
      (coordinate R i * coordinate R j)).topIso.inv
    (hnat.trans (by
      rw [coefficientPairAwayMap_awayFraction]))

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
