/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.ConstantFlatBadFiberClosedFiberControl
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.QuasiFiniteBadLevelEuler

/-!
# Five- and eleven-adic consumers of concrete constant-flat closed-fibre control

This file specializes the concrete closed-fibre theorem to the two auxiliary fibres used by the
formal-immersion route.  The resulting data feed the existing localization construction and both
factor orderings of the bad-level Euler estimate without a caller-supplied bad-fibre bound.
-/

noncomputable section

namespace AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme

open FiniteFlatCommGroupScheme

/-- The actual supported-cokernel sections at the auxiliary fibre `5` have length at most one. -/
noncomputable def mazurConstantFlatBadFiberBoundedDataAtFive
    (coeffPrime : ℕ) [NeZero coeffPrime] :
    FinitePGroup.BoundedData coeffPrime
      (MazurConstantFlatBadFiberHZero coeffPrime 5) :=
  (mazurConstantFlatBadFiberClosedFiberControl coeffPrime 5).boundedDataAtFive coeffPrime

/-- The actual supported-cokernel sections at the auxiliary fibre `11` have length at most one. -/
noncomputable def mazurConstantFlatBadFiberBoundedDataAtEleven
    (coeffPrime : ℕ) [NeZero coeffPrime] :
    FinitePGroup.BoundedData coeffPrime
      (MazurConstantFlatBadFiberHZero coeffPrime 11) :=
  (mazurConstantFlatBadFiberClosedFiberControl coeffPrime 11).boundedDataAtEleven coeffPrime

@[simp]
theorem mazurConstantFlatBadFiberBoundedDataAtFive_length
    (coeffPrime : ℕ) [NeZero coeffPrime] :
    (mazurConstantFlatBadFiberBoundedDataAtFive coeffPrime).length = 1 :=
  rfl

@[simp]
theorem mazurConstantFlatBadFiberBoundedDataAtEleven_length
    (coeffPrime : ℕ) [NeZero coeffPrime] :
    (mazurConstantFlatBadFiberBoundedDataAtEleven coeffPrime).length = 1 :=
  rfl

namespace MazurConstantFlatHOneLocalizationData

/-- At level `5`, concrete bad-fibre control feeds the exact global localization datum. -/
noncomputable def globalHOneBoundedDataAtFive
    {coeffPrime : ℕ} [NeZero coeffPrime]
    (D : MazurConstantFlatHOneLocalizationData coeffPrime 5)
    (ambientData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantAmbientFppfHOne coeffPrime)) :
    FinitePGroup.BoundedData coeffPrime
      (mazurConstantFlat coeffPrime 5).FppfHOne.{0} :=
  D.globalHOneBoundedData
    (mazurConstantFlatBadFiberBoundedDataAtFive coeffPrime) ambientData

/-- At level `11`, concrete bad-fibre control feeds the exact global localization datum. -/
noncomputable def globalHOneBoundedDataAtEleven
    {coeffPrime : ℕ} [NeZero coeffPrime]
    (D : MazurConstantFlatHOneLocalizationData coeffPrime 11)
    (ambientData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantAmbientFppfHOne coeffPrime)) :
    FinitePGroup.BoundedData coeffPrime
      (mazurConstantFlat coeffPrime 11).FppfHOne.{0} :=
  D.globalHOneBoundedData
    (mazurConstantFlatBadFiberBoundedDataAtEleven coeffPrime) ambientData

@[simp]
theorem globalHOneBoundedDataAtFive_length
    {coeffPrime : ℕ} [NeZero coeffPrime]
    (D : MazurConstantFlatHOneLocalizationData coeffPrime 5)
    (ambientData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantAmbientFppfHOne coeffPrime)) :
    (D.globalHOneBoundedDataAtFive ambientData).length =
      1 + ambientData.length :=
  rfl

@[simp]
theorem globalHOneBoundedDataAtEleven_length
    {coeffPrime : ℕ} [NeZero coeffPrime]
    (D : MazurConstantFlatHOneLocalizationData coeffPrime 11)
    (ambientData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantAmbientFppfHOne coeffPrime)) :
    (D.globalHOneBoundedDataAtEleven ambientData).length =
      1 + ambientData.length :=
  rfl

end MazurConstantFlatHOneLocalizationData

namespace FppfLowDegreeExactSequence

universe u

variable {coeffPrime : ℕ} [NeZero coeffPrime]
variable {G : QuasiFiniteFlatCommGroupScheme (Spec (.of ℤ))}

/-- The constant-kernel Euler estimate at the actual auxiliary fibre `5`. -/
theorem
    fppfHOne_natCard_le_pow_of_constantFlatKernel_muFlatQuotient_localized_closedFiberAtFive
    (hprime : coeffPrime.Prime) (hprime2 : coeffPrime ≠ 2)
    (datum : MuFlatDatum coeffPrime 5)
    (D : FppfExtensionPresentation
      (mazurConstantFlat coeffPrime 5) G (muFlat coeffPrime 5 datum))
    (localizationData : MazurConstantFlatHOneLocalizationData coeffPrime 5)
    (ambientConstantHOneData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantAmbientFppfHOne coeffPrime))
    (quotientHOneData : FinitePGroup.BoundedData coeffPrime
      (muFlat coeffPrime 5 datum).FppfHOne.{0})
    (bound : ℕ)
    (hbound : 1 + ambientConstantHOneData.length +
      quotientHOneData.length ≤ bound) :
    Nat.card G.FppfHOne.{0} ≤ coeffPrime ^ bound := by
  exact
    fppfHOne_natCard_le_pow_of_constantFlatKernel_muFlatQuotient_localized
      hprime hprime2 (by decide) datum D localizationData
      (mazurConstantFlatBadFiberBoundedDataAtFive coeffPrime)
      ambientConstantHOneData quotientHOneData bound (by simpa using hbound)

/-- The constant-kernel Euler estimate at the actual auxiliary fibre `11`. -/
theorem
    fppfHOne_natCard_le_pow_of_constantFlatKernel_muFlatQuotient_localized_closedFiberAtEleven
    (hprime : coeffPrime.Prime) (hprime2 : coeffPrime ≠ 2)
    (datum : MuFlatDatum coeffPrime 11)
    (D : FppfExtensionPresentation
      (mazurConstantFlat coeffPrime 11) G (muFlat coeffPrime 11 datum))
    (localizationData : MazurConstantFlatHOneLocalizationData coeffPrime 11)
    (ambientConstantHOneData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantAmbientFppfHOne coeffPrime))
    (quotientHOneData : FinitePGroup.BoundedData coeffPrime
      (muFlat coeffPrime 11 datum).FppfHOne.{0})
    (bound : ℕ)
    (hbound : 1 + ambientConstantHOneData.length +
      quotientHOneData.length ≤ bound) :
    Nat.card G.FppfHOne.{0} ≤ coeffPrime ^ bound := by
  exact
    fppfHOne_natCard_le_pow_of_constantFlatKernel_muFlatQuotient_localized
      hprime hprime2 (by decide) datum D localizationData
      (mazurConstantFlatBadFiberBoundedDataAtEleven coeffPrime)
      ambientConstantHOneData quotientHOneData bound (by simpa using hbound)

/-- The reverse-order Euler estimate at the actual auxiliary fibre `5`. -/
theorem
    fppfHOne_natCard_le_pow_of_muFlatKernel_constantFlatQuotient_localized_closedFiberAtFive
    (hprime : coeffPrime.Prime) (hprime2 : coeffPrime ≠ 2)
    (datum : MuFlatDatum coeffPrime 5)
    (D : FppfExtensionPresentation
      (muFlat coeffPrime 5 datum) G (mazurConstantFlat coeffPrime 5))
    (kernelHOneData : FinitePGroup.BoundedData coeffPrime
      (muFlat coeffPrime 5 datum).FppfHOne.{0})
    (localizationData : MazurConstantFlatHOneLocalizationData coeffPrime 5)
    (ambientConstantHOneData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantAmbientFppfHOne coeffPrime))
    (bound : ℕ)
    (hbound : kernelHOneData.length + 1 +
      ambientConstantHOneData.length ≤ bound) :
    Nat.card G.FppfHOne.{0} ≤ coeffPrime ^ bound := by
  exact
    fppfHOne_natCard_le_pow_of_muFlatKernel_constantFlatQuotient_localized
      hprime hprime2 (by decide) datum D kernelHOneData localizationData
      (mazurConstantFlatBadFiberBoundedDataAtFive coeffPrime)
      ambientConstantHOneData bound (by simpa using hbound)

/-- The reverse-order Euler estimate at the actual auxiliary fibre `11`. -/
theorem
    fppfHOne_natCard_le_pow_of_muFlatKernel_constantFlatQuotient_localized_closedFiberAtEleven
    (hprime : coeffPrime.Prime) (hprime2 : coeffPrime ≠ 2)
    (datum : MuFlatDatum coeffPrime 11)
    (D : FppfExtensionPresentation
      (muFlat coeffPrime 11 datum) G (mazurConstantFlat coeffPrime 11))
    (kernelHOneData : FinitePGroup.BoundedData coeffPrime
      (muFlat coeffPrime 11 datum).FppfHOne.{0})
    (localizationData : MazurConstantFlatHOneLocalizationData coeffPrime 11)
    (ambientConstantHOneData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantAmbientFppfHOne coeffPrime))
    (bound : ℕ)
    (hbound : kernelHOneData.length + 1 +
      ambientConstantHOneData.length ≤ bound) :
    Nat.card G.FppfHOne.{0} ≤ coeffPrime ^ bound := by
  exact
    fppfHOne_natCard_le_pow_of_muFlatKernel_constantFlatQuotient_localized
      hprime hprime2 (by decide) datum D kernelHOneData localizationData
      (mazurConstantFlatBadFiberBoundedDataAtEleven coeffPrime)
      ambientConstantHOneData bound (by simpa using hbound)

end FppfLowDegreeExactSequence

end AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme
