/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.AffineCuspPolynomialChart
import MazurTorsion.AlgebraicGeometry.PicardSectionBaseChange

/-!
# Base change of the represented affine cusp section

This file is a concrete consumer of the section base-change API.  The affine
scheme `Spec ℤ[q]` is equipped with the represented zero section constructed in
`AffineCuspPolynomialChart`.  We base change that section to `Spec (ZMod 5)`
and `Spec (ZMod 11)`, prove that both resulting morphisms remain sections, and
identify their composites with the canonical base-change map.

This is an actual represented affine chart, not an identification with an
integral modular curve.  The remaining modular-geometric step is to identify a
neighbourhood of the infinity section on `X₀(N)` with this chart.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry.Scheme.Modules

namespace MazurTorsion.ModularCurve.AffineCuspPolynomialChart

/-- The structural morphism of the represented integral polynomial cusp chart. -/
noncomputable def integerStructuralMap :
    Spec (.of (CoordinateRing ℤ)) ⟶ Spec (.of ℤ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ (CoordinateRing ℤ)))

/-- Reduction of the integral base to `ZMod n`. -/
noncomputable def integerResidueMap (n : ℕ) :
    Spec (.of (ZMod n)) ⟶ Spec (.of ℤ) :=
  Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod n)))

/-- The represented zero section, regarded as a section after the trivial base
change of the integral chart. -/
noncomputable def integerZeroSectionOnTrivialBaseChange :
    Spec (.of ℤ) ⟶
      pullback integerStructuralMap (𝟙 (Spec (.of ℤ))) :=
  baseChangeZero integerStructuralMap (zeroSection ℤ).toSpec
    (zeroSection ℤ).isSection (𝟙 (Spec (.of ℤ)))

/-- The zero section on the trivial base change is a section of its second
projection. -/
theorem integerZeroSectionOnTrivialBaseChange_snd :
    integerZeroSectionOnTrivialBaseChange ≫
        pullback.snd integerStructuralMap (𝟙 (Spec (.of ℤ))) =
      𝟙 (Spec (.of ℤ)) :=
  baseChangeZero_snd integerStructuralMap (zeroSection ℤ).toSpec
    (zeroSection ℤ).isSection (𝟙 (Spec (.of ℤ)))

/-- The represented integral zero section after base change to `ZMod n`. -/
noncomputable def integerZeroSectionAtResidue (n : ℕ) :
    Spec (.of (ZMod n)) ⟶ pullback integerStructuralMap (integerResidueMap n) :=
  baseChangeSection integerStructuralMap
    integerZeroSectionOnTrivialBaseChange
    integerZeroSectionOnTrivialBaseChange_snd (integerResidueMap n)
    (by simp)

/-- The residue-ring zero section remains a section. -/
theorem integerZeroSectionAtResidue_snd (n : ℕ) :
    integerZeroSectionAtResidue n ≫
        pullback.snd integerStructuralMap (integerResidueMap n) =
      𝟙 (Spec (.of (ZMod n))) :=
  baseChangeSection_snd integerStructuralMap
    integerZeroSectionOnTrivialBaseChange
    integerZeroSectionOnTrivialBaseChange_snd (integerResidueMap n)
    (by simp)

/-- The residue-ring zero section agrees with direct base change of the
represented integral zero section. -/
theorem integerZeroSectionAtResidue_eq_baseChangeZero (n : ℕ) :
    integerZeroSectionAtResidue n =
      baseChangeZero integerStructuralMap (zeroSection ℤ).toSpec
        (zeroSection ℤ).isSection (integerResidueMap n) :=
  baseChangeSection_baseChangeZero integerStructuralMap
    (zeroSection ℤ).toSpec (zeroSection ℤ).isSection
    (integerResidueMap n) (by simp)

/-- The characteristic-five zero section maps to the integral zero section
through the canonical base-change map. -/
theorem integerZeroSectionAtFive_baseChangeMap :
    integerZeroSectionAtResidue 5 ≫
        baseChangeMap integerStructuralMap (integerResidueMap 5) (by simp) =
      integerResidueMap 5 ≫ integerZeroSectionOnTrivialBaseChange :=
  baseChangeSection_baseChangeMap integerStructuralMap
    integerZeroSectionOnTrivialBaseChange
    integerZeroSectionOnTrivialBaseChange_snd (integerResidueMap 5)
    (by simp)

/-- The characteristic-five base change is still a section. -/
theorem integerZeroSectionAtFive_snd :
    integerZeroSectionAtResidue 5 ≫
        pullback.snd integerStructuralMap (integerResidueMap 5) =
      𝟙 (Spec (.of (ZMod 5))) :=
  integerZeroSectionAtResidue_snd 5

/-- The characteristic-eleven zero section maps to the integral zero section
through the canonical base-change map. -/
theorem integerZeroSectionAtEleven_baseChangeMap :
    integerZeroSectionAtResidue 11 ≫
        baseChangeMap integerStructuralMap (integerResidueMap 11) (by simp) =
      integerResidueMap 11 ≫ integerZeroSectionOnTrivialBaseChange :=
  baseChangeSection_baseChangeMap integerStructuralMap
    integerZeroSectionOnTrivialBaseChange
    integerZeroSectionOnTrivialBaseChange_snd (integerResidueMap 11)
    (by simp)

/-- The characteristic-eleven base change is still a section. -/
theorem integerZeroSectionAtEleven_snd :
    integerZeroSectionAtResidue 11 ≫
        pullback.snd integerStructuralMap (integerResidueMap 11) =
      𝟙 (Spec (.of (ZMod 11))) :=
  integerZeroSectionAtResidue_snd 11

end MazurTorsion.ModularCurve.AffineCuspPolynomialChart
