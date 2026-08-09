/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.AdmissibleClosedFiberConnectedEtale
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.ArtinSchreierAdmissiblePrimeFiberConsumers
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.QuotientEtaleDescent

/-!
# All-etale constant-by-constant prime-fibre consumers

An actual finite-flat fppf quotient presentation over `Spec (ZMod p)` whose geometric kernel
and quotient are both the represented constant group `Z/pZ` is entirely etale.  The connected
part of its connected--etale sequence is therefore the trivial constant group and its etale
quotient is the middle group itself.

The Artin--Schreier computation gives exact `p`-length one for the represented fppf `H¹` of
each constant factor.  Low-degree exactness for the supplied quotient presentation then gives
the middle `H¹` a genuine `p`-length bound of two.  The final coefficient-five and
coefficient-eleven theorems feed this actual cohomology bound into the represented Kummer
rank-zero criterion.  The geometric quotient presentation, both factor isomorphisms, the
Mordell--Weil Kummer homomorphism and its injectivity, and the torsion-cardinality law all remain
explicit inputs.

No assertion here classifies an arbitrary order-`p` factor as constant, nor does it supply a
missing Raynaud or Oort--Tate identification.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme

open CommGroupScheme

universe u

namespace FppfQuotientPresentation

/-- A constant-kernel, constant-quotient fppf extension on the coefficient-prime fibre is
itself etale. -/
theorem etale_of_constantKernel_constantQuotientPrimeFiber
    {p : ℕ} [NeZero p]
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod p)))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅
      constantScheme (ZMod p) (Multiplicative (ZMod p)))
    (quotientIso : D.quotient ≅
      constantScheme (ZMod p) (Multiplicative (ZMod p))) :
    Etale G.structureMap :=
  D.middle_etale_of_kernel_quotient_etale
    (etale_structureMap_of_iso kernelIso
      (constantScheme_etale (ZMod p) (Multiplicative (ZMod p))))
    (etale_structureMap_of_iso quotientIso
      (constantScheme_etale (ZMod p) (Multiplicative (ZMod p))))

/-- The actual all-etale connected--etale sequence of a constant-by-constant prime-fibre
extension.  Its connected part is the trivial constant group and its etale projection is the
identity of the middle group. -/
def allEtaleConnectedEtaleDatumOfConstantKernelConstantQuotientPrimeFiber
    {p : ℕ} [NeZero p]
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod p)))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅
      constantScheme (ZMod p) (Multiplicative (ZMod p)))
    (quotientIso : D.quotient ≅
      constantScheme (ZMod p) (Multiplicative (ZMod p))) :
    G.ConnectedEtaleDatum :=
  { connectedPart := trivialConstantScheme (ZMod p)
    etaleQuotient := G
    inclusion := zeroHom (trivialConstantScheme (ZMod p)) G
    project := 𝟙 G
    geometricallyConnected := trivialConstantScheme_geometricallyConnected
    etale := D.etale_of_constantKernel_constantQuotientPrimeFiber kernelIso quotientIso
    exactOnPoints := fun X x ↦ by
      constructor
      · intro hx
        refine ⟨1, ?_⟩
        rw [mapPoint_zeroHom_eq_one]
        simpa only [mapPoint_id, MonoidHom.id_apply] using hx.symm
      · rintro ⟨y, rfl⟩
        exact mapPoint_zeroHom_eq_one
          (trivialConstantScheme (ZMod p)) G X y }

/-- Concrete all-etale connected--etale data over `Spec (ZMod 5)`. -/
def allEtaleConnectedEtaleDatumOfConstantKernelConstantQuotientPrimeFiberAtFive
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod 5)))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅
      constantScheme (ZMod 5) (Multiplicative (ZMod 5)))
    (quotientIso : D.quotient ≅
      constantScheme (ZMod 5) (Multiplicative (ZMod 5))) :
    G.ConnectedEtaleDatum :=
  D.allEtaleConnectedEtaleDatumOfConstantKernelConstantQuotientPrimeFiber
    kernelIso quotientIso

/-- Concrete all-etale connected--etale data over `Spec (ZMod 11)`. -/
def allEtaleConnectedEtaleDatumOfConstantKernelConstantQuotientPrimeFiberAtEleven
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod 11)))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅
      constantScheme (ZMod 11) (Multiplicative (ZMod 11)))
    (quotientIso : D.quotient ≅
      constantScheme (ZMod 11) (Multiplicative (ZMod 11))) :
    G.ConnectedEtaleDatum :=
  D.allEtaleConnectedEtaleDatumOfConstantKernelConstantQuotientPrimeFiber
    kernelIso quotientIso

/-- On the coefficient-prime fibre, an actual extension of the represented constant
order-`p` group by itself has represented fppf `H¹` of `p`-length at most two. -/
noncomputable def middleHOneBoundedDataOfConstantKernelConstantQuotientPrimeFiber
    {p : ℕ} [NeZero p]
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod p)))}
    (D : FppfQuotientPresentation G) (hp : p.Prime)
    (kernelIso : D.kernelPresentation.kernel ≅
      constantScheme (ZMod p) (Multiplicative (ZMod p)))
    (quotientIso : D.quotient ≅
      constantScheme (ZMod p) (Multiplicative (ZMod p))) :
    FinitePGroup.BoundedData p G.FppfHOne.{0} := by
  letI : Fact p.Prime := ⟨hp⟩
  let kernelHOneData :=
    (ArtinSchreier.constantSchemeFppfHOne_zmod_prime_certifiedData p).toBoundedData.congr
      (CommGroupScheme.fppfHOneMulEquivOfIso
        ((finiteFlatCommGroupSchemeProperty _).ι.mapIso kernelIso)).symm
  let quotientHOneData :=
    (ArtinSchreier.constantSchemeFppfHOne_zmod_prime_certifiedData p).toBoundedData.congr
      (CommGroupScheme.fppfHOneMulEquivOfIso
        ((finiteFlatCommGroupSchemeProperty _).ι.mapIso quotientIso)).symm
  exact FinitePGroup.BoundedData.middleOfMulExact kernelHOneData quotientHOneData
    (fppfHOneMap D.kernelPresentation.inclusion) (fppfHOneMap D.project)
    D.exact_fppfHOneMap_inclusion_project

@[simp]
theorem middleHOneBoundedDataOfConstantKernelConstantQuotientPrimeFiber_length
    {p : ℕ} [NeZero p]
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod p)))}
    (D : FppfQuotientPresentation G) (hp : p.Prime)
    (kernelIso : D.kernelPresentation.kernel ≅
      constantScheme (ZMod p) (Multiplicative (ZMod p)))
    (quotientIso : D.quotient ≅
      constantScheme (ZMod p) (Multiplicative (ZMod p))) :
    (D.middleHOneBoundedDataOfConstantKernelConstantQuotientPrimeFiber hp
      kernelIso quotientIso).length = 2 := by
  rfl

/-- The all-constant fppf `H¹` bound over `Spec (ZMod 5)`. -/
noncomputable def middleHOneBoundedDataOfConstantKernelConstantQuotientPrimeFiberAtFive
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod 5)))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅
      constantScheme (ZMod 5) (Multiplicative (ZMod 5)))
    (quotientIso : D.quotient ≅
      constantScheme (ZMod 5) (Multiplicative (ZMod 5))) :
    FinitePGroup.BoundedData 5 G.FppfHOne.{0} :=
  D.middleHOneBoundedDataOfConstantKernelConstantQuotientPrimeFiber
    (by decide) kernelIso quotientIso

/-- The all-constant fppf `H¹` bound over `Spec (ZMod 11)`. -/
noncomputable def middleHOneBoundedDataOfConstantKernelConstantQuotientPrimeFiberAtEleven
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod 11)))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅
      constantScheme (ZMod 11) (Multiplicative (ZMod 11)))
    (quotientIso : D.quotient ≅
      constantScheme (ZMod 11) (Multiplicative (ZMod 11))) :
    FinitePGroup.BoundedData 11 G.FppfHOne.{0} :=
  D.middleHOneBoundedDataOfConstantKernelConstantQuotientPrimeFiber
    (by decide) kernelIso quotientIso

@[simp]
theorem middleHOneBoundedDataOfConstantKernelConstantQuotientPrimeFiberAtFive_length
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod 5)))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅
      constantScheme (ZMod 5) (Multiplicative (ZMod 5)))
    (quotientIso : D.quotient ≅
      constantScheme (ZMod 5) (Multiplicative (ZMod 5))) :
    (D.middleHOneBoundedDataOfConstantKernelConstantQuotientPrimeFiberAtFive
      kernelIso quotientIso).length = 2 :=
  D.middleHOneBoundedDataOfConstantKernelConstantQuotientPrimeFiber_length
    (by decide) kernelIso quotientIso

@[simp]
theorem middleHOneBoundedDataOfConstantKernelConstantQuotientPrimeFiberAtEleven_length
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod 11)))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅
      constantScheme (ZMod 11) (Multiplicative (ZMod 11)))
    (quotientIso : D.quotient ≅
      constantScheme (ZMod 11) (Multiplicative (ZMod 11))) :
    (D.middleHOneBoundedDataOfConstantKernelConstantQuotientPrimeFiberAtEleven
      kernelIso quotientIso).length = 2 :=
  D.middleHOneBoundedDataOfConstantKernelConstantQuotientPrimeFiber_length
    (by decide) kernelIso quotientIso

/-- The length-two all-constant prime-fibre bound feeds the actual represented fppf Kummer
criterion. -/
theorem finrank_eq_zero_of_fppfKummer_constantKernelConstantQuotientPrimeFiber
    {p : ℕ} [NeZero p]
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod p)))}
    (D : FppfQuotientPresentation G) (hp : p.Prime)
    (kernelIso : D.kernelPresentation.kernel ≅
      constantScheme (ZMod p) (Multiplicative (ZMod p)))
    (quotientIso : D.quotient ≅
      constantScheme (ZMod p) (Multiplicative (ZMod p)))
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) p).ker =
      p ^ torsionLength)
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) p).range) →* G.FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hbound : 2 ≤ torsionLength) :
    Module.finrank ℤ A = 0 := by
  let middleHOneData :=
    D.middleHOneBoundedDataOfConstantKernelConstantQuotientPrimeFiber hp
      kernelIso quotientIso
  letI : Finite G.FppfHOne.{0} := middleHOneData.finite
  apply finrank_eq_zero_of_injective_kummer_of_card_le_torsion
    p torsionLength hp hkernel kummer hkummer
  exact middleHOneData.card_le.trans
    ((Nat.pow_le_pow_iff_right hp.one_lt).mpr (by
      simpa [middleHOneData] using hbound))

/-- A genuine coefficient-five constant-by-constant quotient presentation feeds the represented
Kummer rank-zero criterion. -/
theorem finrank_eq_zero_of_fppfKummer_constantKernelConstantQuotientPrimeFiberAtFive
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod 5)))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅
      constantScheme (ZMod 5) (Multiplicative (ZMod 5)))
    (quotientIso : D.quotient ≅
      constantScheme (ZMod 5) (Multiplicative (ZMod 5)))
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) 5).ker =
      5 ^ torsionLength)
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) 5).range) →* G.FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hbound : 2 ≤ torsionLength) :
    Module.finrank ℤ A = 0 :=
  D.finrank_eq_zero_of_fppfKummer_constantKernelConstantQuotientPrimeFiber
    (by decide) kernelIso quotientIso torsionLength hkernel kummer hkummer hbound

/-- A genuine coefficient-eleven constant-by-constant quotient presentation feeds the
represented Kummer rank-zero criterion. -/
theorem finrank_eq_zero_of_fppfKummer_constantKernelConstantQuotientPrimeFiberAtEleven
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod 11)))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅
      constantScheme (ZMod 11) (Multiplicative (ZMod 11)))
    (quotientIso : D.quotient ≅
      constantScheme (ZMod 11) (Multiplicative (ZMod 11)))
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) 11).ker =
      11 ^ torsionLength)
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) 11).range) →* G.FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hbound : 2 ≤ torsionLength) :
    Module.finrank ℤ A = 0 :=
  D.finrank_eq_zero_of_fppfKummer_constantKernelConstantQuotientPrimeFiber
    (by decide) kernelIso quotientIso torsionLength hkernel kummer hkummer hbound

end FppfQuotientPresentation

end AlgebraicGeometry.FiniteFlatCommGroupScheme
