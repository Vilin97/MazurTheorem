/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenCrossPrimeKernel
import MazurTorsion.NumberTheory.XOneThirteenFiniteMumfordExponentTables

/-!
# Transport of the finite `X₁(13)` exponent tables through `ZMod 19`

This file uses the additive group `ZMod 19` as a concrete carrier for both
nineteen-element finite targets.  Its equivalences with the checked Mumford
record sets are only equivalences of underlying finite types: no group law is
placed on the record sets, and the lookup tables are not asserted to compute
Jacobian addition.

The cross-prime certificate constructor below still takes the rational source,
the two additive reduction homomorphisms, and their prime-power kernel
statements as explicit hypotheses.  In particular, this file does not
construct rational reduction maps.
-/

namespace MazurTorsion.XOneThirteenCrossPrimeExponentTransport

open XOneThirteenCrossPrimeKernel
open XOneThirteenFiniteField
open XOneThirteenFiniteMumford
open XOneThirteenFiniteMumfordFive
open XOneThirteenFiniteMumfordExponentTables

local instance : NeZero 19 := ⟨by norm_num⟩

/-- The canonical finite representative of a residue modulo nineteen. -/
def zmodNineteenEquivFin : ZMod 19 ≃ Fin 19 :=
  (ZMod.finEquiv 19).symm.toEquiv

/-- The checked exponent table over `𝔽₃`, transported to a `ZMod 19`
carrier. -/
noncomputable def zmodNineteenEquivRecordsF3 :
    ZMod 19 ≃ BalancedMumfordF3 :=
  zmodNineteenEquivFin.trans finNineteenEquivBalancedMumfordF3

/-- The checked exponent table over `𝔽₅`, transported to a `ZMod 19`
carrier. -/
noncomputable def zmodNineteenEquivRecordsF5 :
    ZMod 19 ≃ BalancedMumfordF5 :=
  zmodNineteenEquivFin.trans finNineteenEquivBalancedMumfordF5

/-- Direct lookup of the `𝔽₃` record attached to a common residue exponent. -/
def recordAtThree (e : ZMod 19) : BalancedMumfordF3 :=
  recordOfExponentF3 (zmodNineteenEquivFin e)

/-- Direct lookup of the `𝔽₅` record attached to a common residue exponent. -/
def recordAtFive (e : ZMod 19) : BalancedMumfordF5 :=
  recordOfExponentF5 (zmodNineteenEquivFin e)

@[simp]
theorem zmodNineteenEquivRecordsF3_apply (e : ZMod 19) :
    zmodNineteenEquivRecordsF3 e = recordAtThree e :=
  rfl

@[simp]
theorem zmodNineteenEquivRecordsF5_apply (e : ZMod 19) :
    zmodNineteenEquivRecordsF5 e = recordAtFive e :=
  rfl

/-- A common residue exponent produces checked curve-point records at both
primes exactly for the six audited exponent representatives. -/
theorem commonExponent_isCurvePoint_at_both_iff (e : ZMod 19) :
    ((∃ P : PointCertificate,
        recordAtThree e = curvePointMumford P) ∧
      (∃ P : PointCertificateF5,
        recordAtFive e = curvePointMumfordF5 P)) ↔
      zmodNineteenEquivFin e ∈ curvePointExponents := by
  rw [recordAtThree, recordAtFive,
    recordOfExponentF3_isCurvePoint_iff,
    recordOfExponentF5_isCurvePoint_iff, and_self]

/-! ## Honest specialization of the cross-prime certificate -/

/-- Package supplied reduction homomorphisms to the concrete additive group
`ZMod 19` into the existing honest cross-prime certificate.

The two kernel-power premises remain visible and the record equivalences are
the checked exponent-table transports above. -/
noncomputable def certificateOfZModNineteenReductions
    {G : Type*} [AddCommGroup G] [AddGroup.FG G]
    (reductionAtThree reductionAtFive : G →+ ZMod 19)
    (hkernelThree : ∃ a, Nat.card reductionAtThree.ker = 3 ^ a)
    (hkernelFive : ∃ b, Nat.card reductionAtFive.ker = 5 ^ b) :
    Certificate G (ZMod 19) (ZMod 19) where
  reductionAtThree := reductionAtThree
  reductionAtFive := reductionAtFive
  recordsAtThree := zmodNineteenEquivRecordsF3
  recordsAtFive := zmodNineteenEquivRecordsF5
  kernelAtThree_isThreePower := hkernelThree
  kernelAtFive_isFivePower := hkernelFive

/-- Small downstream consumer: supplied concrete reductions and their kernel
certificates force the source to be finite of rank zero and cardinality
dividing nineteen. -/
theorem source_endpoint_of_zmodNineteenReductions
    {G : Type*} [AddCommGroup G] [AddGroup.FG G]
    (reductionAtThree reductionAtFive : G →+ ZMod 19)
    (hkernelThree : ∃ a, Nat.card reductionAtThree.ker = 3 ^ a)
    (hkernelFive : ∃ b, Nat.card reductionAtFive.ker = 5 ^ b) :
    Finite G ∧ Module.finrank ℤ G = 0 ∧ Nat.card G ∣ 19 := by
  exact Certificate.rational_group_endpoint
    (certificateOfZModNineteenReductions reductionAtThree reductionAtFive
      hkernelThree hkernelFive)

end MazurTorsion.XOneThirteenCrossPrimeExponentTransport
