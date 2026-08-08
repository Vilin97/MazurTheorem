/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.AdmissibleClosedFiberConnectedEtale

/-!
# Coefficient-five and coefficient-eleven closed-fibre consumers

An integral finite-flat fppf extension with actual `mu_p` kernel and constant `Z/pZ` quotient
reduces at the coefficient prime to the connected--etale sequence proved in
`AdmissibleClosedFiberConnectedEtale`.  This file specializes that construction and its refined
point-exponent law at `p = 5` and `p = 11`.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme

namespace FppfQuotientPresentation

/-- The actual connected--etale sequence on the characteristic-five fibre of an integral
multiplicative-kernel, constant-quotient extension. -/
def connectedEtaleDatumClosedFiberAtCoefficientFive
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme ℤ 5)
    (quotientIso : D.quotient ≅
      constantScheme ℤ (Multiplicative (ZMod 5))) :
    ((baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod 5))))).obj G).ConnectedEtaleDatum :=
  D.connectedEtaleDatumClosedFiberOfMuKernelConstantQuotientBaseChange
    (p := 5) (by decide) kernelIso quotientIso

/-- The actual connected--etale sequence on the characteristic-eleven fibre. -/
def connectedEtaleDatumClosedFiberAtCoefficientEleven
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme ℤ 11)
    (quotientIso : D.quotient ≅
      constantScheme ℤ (Multiplicative (ZMod 11))) :
    ((baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod 11))))).obj G).ConnectedEtaleDatum :=
  D.connectedEtaleDatumClosedFiberOfMuKernelConstantQuotientBaseChange
    (p := 11) (by decide) kernelIso quotientIso

/-- On the characteristic-five fibre, every fifth power lies in the actual connected kernel. -/
theorem baseChange_point_pow_mem_connectedPart_rangeAtCoefficientFive
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme ℤ 5)
    (quotientIso : D.quotient ≅
      constantScheme ℤ (Multiplicative (ZMod 5)))
    (B : Type) [CommRing B] [Algebra (ZMod 5) B]
    (x : ((baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod 5))))).obj G).Point
        (AffineCommGroupScheme.testObject (R := ZMod 5) B)) :
    x ^ 5 ∈ Set.range
      (mapPoint
        ((baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod 5))))).map
            D.kernelPresentation.inclusion)
        (AffineCommGroupScheme.testObject (R := ZMod 5) B)) :=
  D.baseChange_point_pow_mem_connectedPart_range_of_muKernel_constantQuotient
    (p := 5) (by decide) kernelIso quotientIso B x

/-- On the characteristic-eleven fibre, every eleventh power lies in the actual connected
kernel. -/
theorem baseChange_point_pow_mem_connectedPart_rangeAtCoefficientEleven
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme ℤ 11)
    (quotientIso : D.quotient ≅
      constantScheme ℤ (Multiplicative (ZMod 11)))
    (B : Type) [CommRing B] [Algebra (ZMod 11) B]
    (x : ((baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod 11))))).obj G).Point
        (AffineCommGroupScheme.testObject (R := ZMod 11) B)) :
    x ^ 11 ∈ Set.range
      (mapPoint
        ((baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod 11))))).map
            D.kernelPresentation.inclusion)
        (AffineCommGroupScheme.testObject (R := ZMod 11) B)) :=
  D.baseChange_point_pow_mem_connectedPart_range_of_muKernel_constantQuotient
    (p := 11) (by decide) kernelIso quotientIso B x

end FppfQuotientPresentation

end AlgebraicGeometry.FiniteFlatCommGroupScheme
