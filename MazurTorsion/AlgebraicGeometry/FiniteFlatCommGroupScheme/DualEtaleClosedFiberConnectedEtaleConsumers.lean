/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.AdmissibleClosedFiberConnectedEtale
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.CartierDualEtalePrimeIdentification
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FiniteEtalePrimeGroupSchemeConstant

/-!
# Closed-fibre connected--etale structure from dual etaleness

Let an integral finite-flat quotient presentation have a prime-order kernel with an actual
finite-free realization whose Cartier dual is etale, and a finite-etale quotient of the same
prime order.  Cartier biduality identifies the kernel with `μ_p`, while the integral
finite-etale classification identifies the quotient with the constant cyclic group.  After
base change to `ZMod p`, these genuine identifications construct the connected--etale datum and
show that every `p`th power lies in its connected part.

The Cartier-dual etaleness premise remains explicit: this file does not supply the missing
Oort--Tate/Raynaud theorem which would derive it from mixed-characteristic closed-fibre data.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme

open AffineFiniteFreeCommGroupScheme

namespace FppfQuotientPresentation

/-- A dual-etale prime-order kernel and finite-etale prime-order quotient give the actual
connected--etale sequence on the characteristic-`p` closed fibre. -/
def connectedEtaleDatumClosedFiberOfDualEtaleKernelInt
    {p : ℕ} [NeZero p]
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    (K : AffineFiniteFreeCommGroupScheme ℤ)
    (e : D.kernelPresentation.kernel ≅ K.realize)
    (hp : p.Prime)
    (hkernelOrder : D.kernelPresentation.kernel.HasConstantOrder p)
    (hkernelDualEtale : Etale (cartierDual K).realize.structureMap)
    (hEtale : Etale D.quotient.structureMap)
    (horder : D.quotient.HasConstantOrder p) :
    ((baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod p))))).obj G).ConnectedEtaleDatum :=
  D.connectedEtaleDatumClosedFiberOfMuKernelConstantQuotientBaseChange hp
    (isoMuOfRealizationCartierDualEtalePrimeInt
      D.kernelPresentation.kernel K e p hp hkernelOrder hkernelDualEtale)
    (finiteEtalePrimeIsoConstantInt D.quotient p hp hEtale horder)

/-- The quotient exponent puts every `p`th power in the actual connected part constructed from
the dual-etale kernel realization. -/
theorem
    baseChange_point_pow_mem_connectedPart_of_dualEtaleKernelInt
    {p : ℕ} [NeZero p]
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    (K : AffineFiniteFreeCommGroupScheme ℤ)
    (e : D.kernelPresentation.kernel ≅ K.realize)
    (hp : p.Prime)
    (hkernelOrder : D.kernelPresentation.kernel.HasConstantOrder p)
    (hkernelDualEtale : Etale (cartierDual K).realize.structureMap)
    (hEtale : Etale D.quotient.structureMap)
    (horder : D.quotient.HasConstantOrder p)
    (B : Type) [CommRing B] [Algebra (ZMod p) B]
    (x : ((baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod p))))).obj G).Point
        (AffineCommGroupScheme.testObject (R := ZMod p) B)) :
    x ^ p ∈ Set.range
      (mapPoint
        (D.connectedEtaleDatumClosedFiberOfDualEtaleKernelInt
          K e hp hkernelOrder hkernelDualEtale hEtale horder).inclusion
        (AffineCommGroupScheme.testObject (R := ZMod p) B)) := by
  let kernelIso := isoMuOfRealizationCartierDualEtalePrimeInt
    D.kernelPresentation.kernel K e p hp hkernelOrder hkernelDualEtale
  let quotientIso := finiteEtalePrimeIsoConstantInt
    D.quotient p hp hEtale horder
  change x ^ p ∈ Set.range
    (mapPoint
      ((baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod p))))).map
          D.kernelPresentation.inclusion)
      (AffineCommGroupScheme.testObject (R := ZMod p) B))
  exact D.baseChange_point_pow_mem_connectedPart_range_of_muKernel_constantQuotient
    hp kernelIso quotientIso B x

/-- The actual characteristic-five connected--etale datum. -/
def connectedEtaleDatumClosedFiberOfDualEtaleKernelIntAtFive
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    (K : AffineFiniteFreeCommGroupScheme ℤ)
    (e : D.kernelPresentation.kernel ≅ K.realize)
    (hkernelOrder : D.kernelPresentation.kernel.HasConstantOrder 5)
    (hkernelDualEtale : Etale (cartierDual K).realize.structureMap)
    (hEtale : Etale D.quotient.structureMap)
    (horder : D.quotient.HasConstantOrder 5) :
    ((baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod 5))))).obj G).ConnectedEtaleDatum :=
  D.connectedEtaleDatumClosedFiberOfDualEtaleKernelInt
    K e (by decide) hkernelOrder hkernelDualEtale hEtale horder

/-- The actual characteristic-eleven connected--etale datum. -/
def connectedEtaleDatumClosedFiberOfDualEtaleKernelIntAtEleven
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    (K : AffineFiniteFreeCommGroupScheme ℤ)
    (e : D.kernelPresentation.kernel ≅ K.realize)
    (hkernelOrder : D.kernelPresentation.kernel.HasConstantOrder 11)
    (hkernelDualEtale : Etale (cartierDual K).realize.structureMap)
    (hEtale : Etale D.quotient.structureMap)
    (horder : D.quotient.HasConstantOrder 11) :
    ((baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod 11))))).obj G).ConnectedEtaleDatum :=
  D.connectedEtaleDatumClosedFiberOfDualEtaleKernelInt
    K e (by decide) hkernelOrder hkernelDualEtale hEtale horder

/-- On the characteristic-five fibre, every fifth power lies in the connected term constructed
from the dual-etale kernel realization. -/
theorem
    baseChange_point_pow_mem_connectedPart_of_dualEtaleKernelIntAtFive
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    (K : AffineFiniteFreeCommGroupScheme ℤ)
    (e : D.kernelPresentation.kernel ≅ K.realize)
    (hkernelOrder : D.kernelPresentation.kernel.HasConstantOrder 5)
    (hkernelDualEtale : Etale (cartierDual K).realize.structureMap)
    (hEtale : Etale D.quotient.structureMap)
    (horder : D.quotient.HasConstantOrder 5)
    (B : Type) [CommRing B] [Algebra (ZMod 5) B]
    (x : ((baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod 5))))).obj G).Point
        (AffineCommGroupScheme.testObject (R := ZMod 5) B)) :
    x ^ 5 ∈ Set.range
      (mapPoint
        (D.connectedEtaleDatumClosedFiberOfDualEtaleKernelIntAtFive
          K e hkernelOrder hkernelDualEtale hEtale horder).inclusion
        (AffineCommGroupScheme.testObject (R := ZMod 5) B)) :=
  D.baseChange_point_pow_mem_connectedPart_of_dualEtaleKernelInt
    K e (by decide) hkernelOrder hkernelDualEtale hEtale horder B x

/-- On the characteristic-eleven fibre, every eleventh power lies in the connected term
constructed from the dual-etale kernel realization. -/
theorem
    baseChange_point_pow_mem_connectedPart_of_dualEtaleKernelIntAtEleven
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    (K : AffineFiniteFreeCommGroupScheme ℤ)
    (e : D.kernelPresentation.kernel ≅ K.realize)
    (hkernelOrder : D.kernelPresentation.kernel.HasConstantOrder 11)
    (hkernelDualEtale : Etale (cartierDual K).realize.structureMap)
    (hEtale : Etale D.quotient.structureMap)
    (horder : D.quotient.HasConstantOrder 11)
    (B : Type) [CommRing B] [Algebra (ZMod 11) B]
    (x : ((baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod 11))))).obj G).Point
        (AffineCommGroupScheme.testObject (R := ZMod 11) B)) :
    x ^ 11 ∈ Set.range
      (mapPoint
        (D.connectedEtaleDatumClosedFiberOfDualEtaleKernelIntAtEleven
          K e hkernelOrder hkernelDualEtale hEtale horder).inclusion
        (AffineCommGroupScheme.testObject (R := ZMod 11) B)) :=
  D.baseChange_point_pow_mem_connectedPart_of_dualEtaleKernelInt
    K e (by decide) hkernelOrder hkernelDualEtale hEtale horder B x

end FppfQuotientPresentation

end AlgebraicGeometry.FiniteFlatCommGroupScheme
