/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.ConstantFlatBadFiberClosedFiberConsumers
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfKummerRankZero

/-!
# Rank-zero consumers of the five- and eleven-adic bad-level Euler bounds

The concrete constant-flat closed-fibre theorem already feeds four genuine quasi-finite fppf
Euler estimates, one for each factor ordering at levels `5` and `11`.  This file connects those
carrier-preserving estimates to the checked Kummer rank-zero criterion.

The extension presentation, localization exactness, endpoint `H¹` bounds, Mordell--Weil Kummer
map, injectivity, and torsion-cardinality law all remain explicit.  Finiteness of the middle
represented `H¹` is derived from the actual low-degree exact sequence and the two endpoint
bounds; it is not assumed.
-/

noncomputable section

namespace AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme

open FiniteFlatCommGroupScheme

universe u

namespace FppfLowDegreeExactSequence

variable {coeffPrime : ℕ} [NeZero coeffPrime]
variable {G : QuasiFiniteFlatCommGroupScheme (Spec (.of ℤ))}

/-- Package a proved cardinal bound on the middle represented `H¹` of an actual extension.
Finiteness is derived from the two endpoint bounds and low-degree exactness. -/
private noncomputable def middleFppfHOneBoundedData
    {K Q : QuasiFiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfExtensionPresentation K G Q)
    (kernelHOneData : FinitePGroup.BoundedData coeffPrime K.FppfHOne.{0})
    (quotientHOneData : FinitePGroup.BoundedData coeffPrime Q.FppfHOne.{0})
    (length : ℕ) (card_le : Nat.card G.FppfHOne.{0} ≤ coeffPrime ^ length) :
    FinitePGroup.BoundedData coeffPrime G.FppfHOne.{0} := by
  letI : Finite
      D.toFppfQuotientPresentation.kernelPresentation.kernel.FppfHOne.{0} := by
    simpa using kernelHOneData.finite
  letI : Finite D.toFppfQuotientPresentation.quotient.FppfHOne.{0} := by
    simpa using quotientHOneData.finite
  exact
    { finite := D.toFppfQuotientPresentation.middleFppfHOne_finite
      length := length
      card_le := card_le }

/-- Actual bounded data for the represented middle `H¹` in the constant-kernel ordering at
bad level `5`.  The length-one closed-fibre contribution is the concrete theorem from the
closed-fibre control module. -/
noncomputable def
    fppfHOneBoundedDataOfConstantFlatKernelMuFlatQuotientClosedFiberAtFive
    (hprime : coeffPrime.Prime) (hprime2 : coeffPrime ≠ 2)
    (datum : MuFlatDatum coeffPrime 5)
    (D : FppfExtensionPresentation
      (mazurConstantFlat coeffPrime 5) G (muFlat coeffPrime 5 datum))
    (localizationData : MazurConstantFlatHOneLocalizationData coeffPrime 5)
    (ambientConstantHOneData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantAmbientFppfHOne coeffPrime))
    (quotientHOneData : FinitePGroup.BoundedData coeffPrime
      (muFlat coeffPrime 5 datum).FppfHOne.{0}) :
    FinitePGroup.BoundedData coeffPrime G.FppfHOne.{0} :=
  middleFppfHOneBoundedData D
    (localizationData.globalHOneBoundedDataAtFive ambientConstantHOneData)
    quotientHOneData
    (1 + ambientConstantHOneData.length + quotientHOneData.length)
    (fppfHOne_natCard_le_pow_of_constantFlatKernel_muFlatQuotient_localized_closedFiberAtFive
      hprime hprime2 datum D localizationData ambientConstantHOneData quotientHOneData
      (1 + ambientConstantHOneData.length + quotientHOneData.length) le_rfl)

@[simp]
theorem
    fppfHOneBoundedDataOfConstantFlatKernelMuFlatQuotientClosedFiberAtFive_length
    (hprime : coeffPrime.Prime) (hprime2 : coeffPrime ≠ 2)
    (datum : MuFlatDatum coeffPrime 5)
    (D : FppfExtensionPresentation
      (mazurConstantFlat coeffPrime 5) G (muFlat coeffPrime 5 datum))
    (localizationData : MazurConstantFlatHOneLocalizationData coeffPrime 5)
    (ambientConstantHOneData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantAmbientFppfHOne coeffPrime))
    (quotientHOneData : FinitePGroup.BoundedData coeffPrime
      (muFlat coeffPrime 5 datum).FppfHOne.{0}) :
    (fppfHOneBoundedDataOfConstantFlatKernelMuFlatQuotientClosedFiberAtFive
      hprime hprime2 datum D localizationData ambientConstantHOneData
      quotientHOneData).length =
        1 + ambientConstantHOneData.length + quotientHOneData.length :=
  rfl

/-- Actual bounded data in the constant-kernel ordering at bad level `11`. -/
noncomputable def
    fppfHOneBoundedDataOfConstantFlatKernelMuFlatQuotientClosedFiberAtEleven
    (hprime : coeffPrime.Prime) (hprime2 : coeffPrime ≠ 2)
    (datum : MuFlatDatum coeffPrime 11)
    (D : FppfExtensionPresentation
      (mazurConstantFlat coeffPrime 11) G (muFlat coeffPrime 11 datum))
    (localizationData : MazurConstantFlatHOneLocalizationData coeffPrime 11)
    (ambientConstantHOneData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantAmbientFppfHOne coeffPrime))
    (quotientHOneData : FinitePGroup.BoundedData coeffPrime
      (muFlat coeffPrime 11 datum).FppfHOne.{0}) :
    FinitePGroup.BoundedData coeffPrime G.FppfHOne.{0} :=
  middleFppfHOneBoundedData D
    (localizationData.globalHOneBoundedDataAtEleven ambientConstantHOneData)
    quotientHOneData
    (1 + ambientConstantHOneData.length + quotientHOneData.length)
    (fppfHOne_natCard_le_pow_of_constantFlatKernel_muFlatQuotient_localized_closedFiberAtEleven
      hprime hprime2 datum D localizationData ambientConstantHOneData quotientHOneData
      (1 + ambientConstantHOneData.length + quotientHOneData.length) le_rfl)

@[simp]
theorem
    fppfHOneBoundedDataOfConstantFlatKernelMuFlatQuotientClosedFiberAtEleven_length
    (hprime : coeffPrime.Prime) (hprime2 : coeffPrime ≠ 2)
    (datum : MuFlatDatum coeffPrime 11)
    (D : FppfExtensionPresentation
      (mazurConstantFlat coeffPrime 11) G (muFlat coeffPrime 11 datum))
    (localizationData : MazurConstantFlatHOneLocalizationData coeffPrime 11)
    (ambientConstantHOneData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantAmbientFppfHOne coeffPrime))
    (quotientHOneData : FinitePGroup.BoundedData coeffPrime
      (muFlat coeffPrime 11 datum).FppfHOne.{0}) :
    (fppfHOneBoundedDataOfConstantFlatKernelMuFlatQuotientClosedFiberAtEleven
      hprime hprime2 datum D localizationData ambientConstantHOneData
      quotientHOneData).length =
        1 + ambientConstantHOneData.length + quotientHOneData.length :=
  rfl

/-- Actual bounded data for the reverse factor ordering at bad level `5`. -/
noncomputable def
    fppfHOneBoundedDataOfMuFlatKernelConstantFlatQuotientClosedFiberAtFive
    (hprime : coeffPrime.Prime) (hprime2 : coeffPrime ≠ 2)
    (datum : MuFlatDatum coeffPrime 5)
    (D : FppfExtensionPresentation
      (muFlat coeffPrime 5 datum) G (mazurConstantFlat coeffPrime 5))
    (kernelHOneData : FinitePGroup.BoundedData coeffPrime
      (muFlat coeffPrime 5 datum).FppfHOne.{0})
    (localizationData : MazurConstantFlatHOneLocalizationData coeffPrime 5)
    (ambientConstantHOneData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantAmbientFppfHOne coeffPrime)) :
    FinitePGroup.BoundedData coeffPrime G.FppfHOne.{0} :=
  middleFppfHOneBoundedData D kernelHOneData
    (localizationData.globalHOneBoundedDataAtFive ambientConstantHOneData)
    (kernelHOneData.length + 1 + ambientConstantHOneData.length)
    (fppfHOne_natCard_le_pow_of_muFlatKernel_constantFlatQuotient_localized_closedFiberAtFive
      hprime hprime2 datum D kernelHOneData localizationData ambientConstantHOneData
      (kernelHOneData.length + 1 + ambientConstantHOneData.length) le_rfl)

@[simp]
theorem
    fppfHOneBoundedDataOfMuFlatKernelConstantFlatQuotientClosedFiberAtFive_length
    (hprime : coeffPrime.Prime) (hprime2 : coeffPrime ≠ 2)
    (datum : MuFlatDatum coeffPrime 5)
    (D : FppfExtensionPresentation
      (muFlat coeffPrime 5 datum) G (mazurConstantFlat coeffPrime 5))
    (kernelHOneData : FinitePGroup.BoundedData coeffPrime
      (muFlat coeffPrime 5 datum).FppfHOne.{0})
    (localizationData : MazurConstantFlatHOneLocalizationData coeffPrime 5)
    (ambientConstantHOneData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantAmbientFppfHOne coeffPrime)) :
    (fppfHOneBoundedDataOfMuFlatKernelConstantFlatQuotientClosedFiberAtFive
      hprime hprime2 datum D kernelHOneData localizationData
      ambientConstantHOneData).length =
        kernelHOneData.length + 1 + ambientConstantHOneData.length :=
  rfl

/-- Actual bounded data for the reverse factor ordering at bad level `11`. -/
noncomputable def
    fppfHOneBoundedDataOfMuFlatKernelConstantFlatQuotientClosedFiberAtEleven
    (hprime : coeffPrime.Prime) (hprime2 : coeffPrime ≠ 2)
    (datum : MuFlatDatum coeffPrime 11)
    (D : FppfExtensionPresentation
      (muFlat coeffPrime 11 datum) G (mazurConstantFlat coeffPrime 11))
    (kernelHOneData : FinitePGroup.BoundedData coeffPrime
      (muFlat coeffPrime 11 datum).FppfHOne.{0})
    (localizationData : MazurConstantFlatHOneLocalizationData coeffPrime 11)
    (ambientConstantHOneData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantAmbientFppfHOne coeffPrime)) :
    FinitePGroup.BoundedData coeffPrime G.FppfHOne.{0} :=
  middleFppfHOneBoundedData D kernelHOneData
    (localizationData.globalHOneBoundedDataAtEleven ambientConstantHOneData)
    (kernelHOneData.length + 1 + ambientConstantHOneData.length)
    (fppfHOne_natCard_le_pow_of_muFlatKernel_constantFlatQuotient_localized_closedFiberAtEleven
      hprime hprime2 datum D kernelHOneData localizationData ambientConstantHOneData
      (kernelHOneData.length + 1 + ambientConstantHOneData.length) le_rfl)

@[simp]
theorem
    fppfHOneBoundedDataOfMuFlatKernelConstantFlatQuotientClosedFiberAtEleven_length
    (hprime : coeffPrime.Prime) (hprime2 : coeffPrime ≠ 2)
    (datum : MuFlatDatum coeffPrime 11)
    (D : FppfExtensionPresentation
      (muFlat coeffPrime 11 datum) G (mazurConstantFlat coeffPrime 11))
    (kernelHOneData : FinitePGroup.BoundedData coeffPrime
      (muFlat coeffPrime 11 datum).FppfHOne.{0})
    (localizationData : MazurConstantFlatHOneLocalizationData coeffPrime 11)
    (ambientConstantHOneData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantAmbientFppfHOne coeffPrime)) :
    (fppfHOneBoundedDataOfMuFlatKernelConstantFlatQuotientClosedFiberAtEleven
      hprime hprime2 datum D kernelHOneData localizationData
      ambientConstantHOneData).length =
        kernelHOneData.length + 1 + ambientConstantHOneData.length :=
  rfl

/-- The constant-kernel level-five Euler estimate feeds the actual represented-fppf Kummer
rank-zero criterion. -/
theorem
    finrank_eq_zero_of_fppfKummer_constantFlatKernel_muFlatQuotient_closedFiberAtFive
    (hprime : coeffPrime.Prime) (hprime2 : coeffPrime ≠ 2)
    (datum : MuFlatDatum coeffPrime 5)
    (D : FppfExtensionPresentation
      (mazurConstantFlat coeffPrime 5) G (muFlat coeffPrime 5 datum))
    (localizationData : MazurConstantFlatHOneLocalizationData coeffPrime 5)
    (ambientConstantHOneData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantAmbientFppfHOne coeffPrime))
    (quotientHOneData : FinitePGroup.BoundedData coeffPrime
      (muFlat coeffPrime 5 datum).FppfHOne.{0})
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) coeffPrime).ker =
      coeffPrime ^ torsionLength)
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) coeffPrime).range) →* G.FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hbound : 1 + ambientConstantHOneData.length +
      quotientHOneData.length ≤ torsionLength) :
    Module.finrank ℤ A = 0 := by
  let middleHOneData :=
    fppfHOneBoundedDataOfConstantFlatKernelMuFlatQuotientClosedFiberAtFive
      hprime hprime2 datum D localizationData ambientConstantHOneData quotientHOneData
  letI : Finite G.FppfHOne.{0} := middleHOneData.finite
  apply FiniteFlatCommGroupScheme.finrank_eq_zero_of_injective_kummer_of_card_le_torsion
    coeffPrime torsionLength hprime hkernel kummer hkummer
  exact middleHOneData.card_le.trans
    ((Nat.pow_le_pow_iff_right hprime.one_lt).mpr (by
      simpa [middleHOneData] using hbound))

/-- The constant-kernel level-eleven Euler estimate feeds the same rank-zero criterion. -/
theorem
    finrank_eq_zero_of_fppfKummer_constantFlatKernel_muFlatQuotient_closedFiberAtEleven
    (hprime : coeffPrime.Prime) (hprime2 : coeffPrime ≠ 2)
    (datum : MuFlatDatum coeffPrime 11)
    (D : FppfExtensionPresentation
      (mazurConstantFlat coeffPrime 11) G (muFlat coeffPrime 11 datum))
    (localizationData : MazurConstantFlatHOneLocalizationData coeffPrime 11)
    (ambientConstantHOneData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantAmbientFppfHOne coeffPrime))
    (quotientHOneData : FinitePGroup.BoundedData coeffPrime
      (muFlat coeffPrime 11 datum).FppfHOne.{0})
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) coeffPrime).ker =
      coeffPrime ^ torsionLength)
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) coeffPrime).range) →* G.FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hbound : 1 + ambientConstantHOneData.length +
      quotientHOneData.length ≤ torsionLength) :
    Module.finrank ℤ A = 0 := by
  let middleHOneData :=
    fppfHOneBoundedDataOfConstantFlatKernelMuFlatQuotientClosedFiberAtEleven
      hprime hprime2 datum D localizationData ambientConstantHOneData quotientHOneData
  letI : Finite G.FppfHOne.{0} := middleHOneData.finite
  apply FiniteFlatCommGroupScheme.finrank_eq_zero_of_injective_kummer_of_card_le_torsion
    coeffPrime torsionLength hprime hkernel kummer hkummer
  exact middleHOneData.card_le.trans
    ((Nat.pow_le_pow_iff_right hprime.one_lt).mpr (by
      simpa [middleHOneData] using hbound))

/-- The reverse, multiplicative-kernel ordering at level five also yields rank zero from the
actual localized Euler bound. -/
theorem
    finrank_eq_zero_of_fppfKummer_muFlatKernel_constantFlatQuotient_closedFiberAtFive
    (hprime : coeffPrime.Prime) (hprime2 : coeffPrime ≠ 2)
    (datum : MuFlatDatum coeffPrime 5)
    (D : FppfExtensionPresentation
      (muFlat coeffPrime 5 datum) G (mazurConstantFlat coeffPrime 5))
    (kernelHOneData : FinitePGroup.BoundedData coeffPrime
      (muFlat coeffPrime 5 datum).FppfHOne.{0})
    (localizationData : MazurConstantFlatHOneLocalizationData coeffPrime 5)
    (ambientConstantHOneData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantAmbientFppfHOne coeffPrime))
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) coeffPrime).ker =
      coeffPrime ^ torsionLength)
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) coeffPrime).range) →* G.FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hbound : kernelHOneData.length + 1 +
      ambientConstantHOneData.length ≤ torsionLength) :
    Module.finrank ℤ A = 0 := by
  let middleHOneData :=
    fppfHOneBoundedDataOfMuFlatKernelConstantFlatQuotientClosedFiberAtFive
      hprime hprime2 datum D kernelHOneData localizationData ambientConstantHOneData
  letI : Finite G.FppfHOne.{0} := middleHOneData.finite
  apply FiniteFlatCommGroupScheme.finrank_eq_zero_of_injective_kummer_of_card_le_torsion
    coeffPrime torsionLength hprime hkernel kummer hkummer
  exact middleHOneData.card_le.trans
    ((Nat.pow_le_pow_iff_right hprime.one_lt).mpr (by
      simpa [middleHOneData] using hbound))

/-- The reverse, multiplicative-kernel ordering at level eleven yields the corresponding
rank-zero endpoint. -/
theorem
    finrank_eq_zero_of_fppfKummer_muFlatKernel_constantFlatQuotient_closedFiberAtEleven
    (hprime : coeffPrime.Prime) (hprime2 : coeffPrime ≠ 2)
    (datum : MuFlatDatum coeffPrime 11)
    (D : FppfExtensionPresentation
      (muFlat coeffPrime 11 datum) G (mazurConstantFlat coeffPrime 11))
    (kernelHOneData : FinitePGroup.BoundedData coeffPrime
      (muFlat coeffPrime 11 datum).FppfHOne.{0})
    (localizationData : MazurConstantFlatHOneLocalizationData coeffPrime 11)
    (ambientConstantHOneData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantAmbientFppfHOne coeffPrime))
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) coeffPrime).ker =
      coeffPrime ^ torsionLength)
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) coeffPrime).range) →* G.FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hbound : kernelHOneData.length + 1 +
      ambientConstantHOneData.length ≤ torsionLength) :
    Module.finrank ℤ A = 0 := by
  let middleHOneData :=
    fppfHOneBoundedDataOfMuFlatKernelConstantFlatQuotientClosedFiberAtEleven
      hprime hprime2 datum D kernelHOneData localizationData ambientConstantHOneData
  letI : Finite G.FppfHOne.{0} := middleHOneData.finite
  apply FiniteFlatCommGroupScheme.finrank_eq_zero_of_injective_kummer_of_card_le_torsion
    coeffPrime torsionLength hprime hkernel kummer hkummer
  exact middleHOneData.card_le.trans
    ((Nat.pow_le_pow_iff_right hprime.one_lt).mpr (by
      simpa [middleHOneData] using hbound))

end FppfLowDegreeExactSequence

end AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme
