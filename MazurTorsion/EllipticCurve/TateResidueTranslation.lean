/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

/-!
# Integral lifts for the residue-translation step of Tate's algorithm

The first coordinate change in Tate's algorithm moves a singular point of the reduced cubic to
the origin.  This file makes that step independent of a choice of representatives: residue-field
coordinates are lifted to the local ring, the resulting unit-scale change is transported to the
fraction field, and the transformed integral equation is recorded explicitly.

If the chosen residue point is singular, the transformed coefficients `a₃`, `a₄`, and `a₆`
belong to the maximal ideal.  This is only the initial translation step.  No blowup, Kodaira
classification, identity-component comparison, or component-order bound is asserted here.
-/

noncomputable section

namespace MazurTorsion.EllipticCurve

open IsLocalRing

/-- A fixed integral representative of a residue-field element. -/
noncomputable def residueLift
    (R : Type*) [CommRing R] [IsLocalRing R]
    (x : IsLocalRing.ResidueField R) : R :=
  Classical.choose (IsLocalRing.residue_surjective x)

@[simp]
theorem residue_residueLift
    (R : Type*) [CommRing R] [IsLocalRing R]
    (x : IsLocalRing.ResidueField R) :
    IsLocalRing.residue R (residueLift R x) = x :=
  Classical.choose_spec (IsLocalRing.residue_surjective x)

/-- The unit-scale integral change whose three translation parameters lift prescribed residue
classes. -/
noncomputable def integralResidueTranslation
    (R : Type*) [CommRing R] [IsLocalRing R]
    (r s t : IsLocalRing.ResidueField R) :
    WeierstrassCurve.VariableChange R :=
  ⟨1, residueLift R r, residueLift R s, residueLift R t⟩

/-- Reducing the chosen integral translation recovers the prescribed residue translation. -/
@[simp]
theorem integralResidueTranslation_map_residue
    (R : Type*) [CommRing R] [IsLocalRing R]
    (r s t : IsLocalRing.ResidueField R) :
    (integralResidueTranslation R r s t).map (IsLocalRing.residue R) =
      (⟨1, r, s, t⟩ :
        WeierstrassCurve.VariableChange (IsLocalRing.ResidueField R)) := by
  ext <;> simp [integralResidueTranslation]

/-- The residue translation transported to the fraction field. -/
noncomputable def genericResidueTranslation
    (R K : Type*) [CommRing R] [IsLocalRing R]
    [Field K] [Algebra R K]
    (r s t : IsLocalRing.ResidueField R) :
    WeierstrassCurve.VariableChange K :=
  (integralResidueTranslation R r s t).map (algebraMap R K)

/-- An explicit integral equation for the generically translated curve. -/
noncomputable def residueTranslatedIntegralModel
    (R K : Type*) [CommRing R] [IsDomain R] [IsLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) [W.IsIntegral R]
    (r s t : IsLocalRing.ResidueField R) : WeierstrassCurve R :=
  integralResidueTranslation R r s t • W.integralModel R

/-- The explicit translated integral equation has generic fibre equal to the translated original
equation. -/
theorem residueTranslatedIntegralModel_map
    (R K : Type*) [CommRing R] [IsDomain R] [IsLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) [W.IsIntegral R]
    (r s t : IsLocalRing.ResidueField R) :
    (residueTranslatedIntegralModel R K W r s t).map (algebraMap R K) =
      genericResidueTranslation R K r s t • W := by
  rw [residueTranslatedIntegralModel, ← WeierstrassCurve.map_variableChange,
    genericResidueTranslation]
  congr 1
  simpa only [WeierstrassCurve.baseChange] using W.baseChange_integralModel_eq R

/-- Every residue-class translation of an integral equation remains integral over the DVR. -/
theorem isIntegral_genericResidueTranslation
    (R K : Type*) [CommRing R] [IsDomain R] [IsLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) [W.IsIntegral R]
    (r s t : IsLocalRing.ResidueField R) :
    WeierstrassCurve.IsIntegral R
      (genericResidueTranslation R K r s t • W) := by
  let W' := residueTranslatedIntegralModel R K W r s t
  have hmap : W'.map (algebraMap R K) =
      genericResidueTranslation R K r s t • W :=
    residueTranslatedIntegralModel_map R K W r s t
  apply WeierstrassCurve.isIntegral_of_exists_lift R
  · exact ⟨W'.a₁, by simpa [WeierstrassCurve.map] using congrArg (fun V ↦ V.a₁) hmap⟩
  · exact ⟨W'.a₂, by simpa [WeierstrassCurve.map] using congrArg (fun V ↦ V.a₂) hmap⟩
  · exact ⟨W'.a₃, by simpa [WeierstrassCurve.map] using congrArg (fun V ↦ V.a₃) hmap⟩
  · exact ⟨W'.a₄, by simpa [WeierstrassCurve.map] using congrArg (fun V ↦ V.a₄) hmap⟩
  · exact ⟨W'.a₆, by simpa [WeierstrassCurve.map] using congrArg (fun V ↦ V.a₆) hmap⟩

/-- The special fibre of the explicit translated integral equation is exactly the corresponding
residue-field coordinate change of the original special fibre. -/
theorem residueTranslatedIntegralModel_map_residue
    (R K : Type*) [CommRing R] [IsDomain R] [IsLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) [W.IsIntegral R]
    (r s t : IsLocalRing.ResidueField R) :
    (residueTranslatedIntegralModel R K W r s t).map (IsLocalRing.residue R) =
      (⟨1, r, s, t⟩ :
          WeierstrassCurve.VariableChange (IsLocalRing.ResidueField R)) •
        (W.integralModel R).map (IsLocalRing.residue R) := by
  rw [residueTranslatedIntegralModel, ← WeierstrassCurve.map_variableChange,
    integralResidueTranslation_map_residue]

/-- Moving a singular point of the special fibre to the origin makes `a₃`, `a₄`, and `a₆`
divisible by the maximal ideal in the explicit translated equation.  These are the first three
coefficient divisibilities in the tame Tate algorithm. -/
theorem residueTranslatedIntegralModel_a₃_a₄_a₆_mem_maximalIdeal_of_singular
    (R K : Type*) [CommRing R] [IsDomain R] [IsLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) [W.IsIntegral R]
    (x y : IsLocalRing.ResidueField R)
    (hequation : ((W.integralModel R).map (IsLocalRing.residue R)).toAffine.Equation x y)
    (hsingular :
      ¬ ((W.integralModel R).map (IsLocalRing.residue R)).toAffine.Nonsingular x y) :
    let W' := residueTranslatedIntegralModel R K W x 0 y
    W'.a₃ ∈ IsLocalRing.maximalIdeal R ∧
      W'.a₄ ∈ IsLocalRing.maximalIdeal R ∧
      W'.a₆ ∈ IsLocalRing.maximalIdeal R := by
  let W₀ := (W.integralModel R).map (IsLocalRing.residue R)
  let W' := residueTranslatedIntegralModel R K W x 0 y
  have hspecial : W'.map (IsLocalRing.residue R) =
      (⟨1, x, 0, y⟩ :
        WeierstrassCurve.VariableChange (IsLocalRing.ResidueField R)) • W₀ := by
    simpa [W₀, W'] using
      residueTranslatedIntegralModel_map_residue R K W x 0 y
  have hequation₀ : W₀.toAffine.Equation x y := by
    simpa [W₀] using hequation
  have hsingular₀ : ¬ W₀.toAffine.Nonsingular x y := by
    simpa [W₀] using hsingular
  have hequationOrigin : (W'.map (IsLocalRing.residue R)).toAffine.Equation 0 0 := by
    rw [hspecial]
    exact (W₀.toAffine.equation_iff_variableChange x y).mp hequation₀
  have hsingularOrigin :
      ¬ (W'.map (IsLocalRing.residue R)).toAffine.Nonsingular 0 0 := by
    rw [hspecial]
    exact mt (W₀.toAffine.nonsingular_iff_variableChange x y).mpr hsingular₀
  have ha₆ : IsLocalRing.residue R W'.a₆ = 0 := by
    exact ((W'.map (IsLocalRing.residue R)).toAffine.equation_zero).mp hequationOrigin
  have hnot : ¬ (IsLocalRing.residue R W'.a₃ ≠ 0 ∨
      IsLocalRing.residue R W'.a₄ ≠ 0) := by
    intro h
    apply hsingularOrigin
    exact ((W'.map (IsLocalRing.residue R)).toAffine.nonsingular_zero).mpr ⟨ha₆, h⟩
  have ha₃ : IsLocalRing.residue R W'.a₃ = 0 := not_ne_iff.mp (not_or.mp hnot).1
  have ha₄ : IsLocalRing.residue R W'.a₄ = 0 := not_ne_iff.mp (not_or.mp hnot).2
  exact ⟨(IsLocalRing.residue_eq_zero_iff W'.a₃).mp ha₃,
    (IsLocalRing.residue_eq_zero_iff W'.a₄).mp ha₄,
    (IsLocalRing.residue_eq_zero_iff W'.a₆).mp ha₆⟩

end MazurTorsion.EllipticCurve
