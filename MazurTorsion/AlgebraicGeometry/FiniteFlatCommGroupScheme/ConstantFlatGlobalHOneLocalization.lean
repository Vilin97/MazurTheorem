/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfCardinalityBound
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.SupportedFppfHOneCertifiedData

/-!
# The global bad-fibre localization handoff for the constant-flat factor

The checked supported-cokernel calculation identifies Mazur's constant-flat model with the
ambient constant group only after restriction to `D(level)`.  It does not by itself identify
their global `H¹` groups over `Spec ℤ`.  The missing global input has the shape of the relevant
part of the bad-fibre localization sequence:

`H⁰(Q_level) → H¹((Z/pZ)^flat) → H¹(Z/pZ)`.

Here `Q_level` is not replaced by an abstract finite group: it is the actual value at the
terminal relative test scheme of the fppf cokernel sheaf already proved to be supported on the
closed level fibre.  `MazurConstantFlatHOneLocalizationData` records a boundary homomorphism on
that carrier and exactness at the genuine global represented `H¹` of `mazurConstantFlat`.

The numerical theorem is unconditional once this exact localization datum and endpoint upper
bounds are supplied.  It proves finiteness and the expected sum-of-lengths bound for the global
constant-flat `H¹`; it does not infer a global localization sequence merely from good-open
support.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme

open CommGroupScheme
open FiniteFlatCommGroupScheme

/-- Global sections of the actual supported constant-flat fppf cokernel sheaf, written
multiplicatively for the low-degree exact-sequence API. -/
noncomputable abbrev MazurConstantFlatBadFiberHZero
    (coeffPrime level : ℕ) [NeZero coeffPrime] :=
  Multiplicative
    ((constantFlatPointCokernelFppfSheaf
      (R := ℤ) (G := Multiplicative (ZMod coeffPrime)) (level : ℤ)).obj.obj
        (Opposite.op (CommGroupScheme.baseObject (Spec (.of ℤ)))))

/-- The ambient global constant-group `H¹` appearing after the bad-fibre boundary term. -/
noncomputable abbrev MazurConstantAmbientFppfHOne
    (coeffPrime : ℕ) [NeZero coeffPrime] :=
  (FiniteFlatCommGroupScheme.constantScheme ℤ
    (Multiplicative (ZMod coeffPrime))).obj.FppfHOne.{0}

/-- The exact global localization datum needed to compare the constant-flat `H¹` with the
ambient constant-group `H¹`.  The source of `boundary` is the actual supported cokernel sheaf
on the terminal relative test scheme. -/
structure MazurConstantFlatHOneLocalizationData
    (coeffPrime level : ℕ) [NeZero coeffPrime] where
  /-- Boundary from supported bad-fibre sections to global constant-flat `H¹`. -/
  boundary : MazurConstantFlatBadFiberHZero coeffPrime level →*
    (mazurConstantFlat coeffPrime level).FppfHOne.{0}
  /-- Exactness at the actual global constant-flat `H¹` carrier. -/
  exact_boundary_inclusion : Function.MulExact boundary
    (CommGroupScheme.fppfHOneMap
      (constantFlatInclusion
        (R := ℤ) (G := Multiplicative (ZMod coeffPrime)) (level : ℤ)))

namespace MazurConstantFlatHOneLocalizationData

variable {coeffPrime level : ℕ} [NeZero coeffPrime]

/-- Exact bad-fibre localization propagates endpoint upper bounds to the genuine global
constant-flat `H¹`. -/
noncomputable def globalHOneBoundedData
    (D : MazurConstantFlatHOneLocalizationData coeffPrime level)
    (badFiberData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantFlatBadFiberHZero coeffPrime level))
    (ambientData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantAmbientFppfHOne coeffPrime)) :
    FinitePGroup.BoundedData coeffPrime
      (mazurConstantFlat coeffPrime level).FppfHOne.{0} :=
  FinitePGroup.BoundedData.middleOfMulExact badFiberData ambientData
    D.boundary
    (CommGroupScheme.fppfHOneMap
      (constantFlatInclusion
        (R := ℤ) (G := Multiplicative (ZMod coeffPrime)) (level : ℤ)))
    D.exact_boundary_inclusion

@[simp]
theorem globalHOneBoundedData_length
    (D : MazurConstantFlatHOneLocalizationData coeffPrime level)
    (badFiberData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantFlatBadFiberHZero coeffPrime level))
    (ambientData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantAmbientFppfHOne coeffPrime)) :
    (D.globalHOneBoundedData badFiberData ambientData).length =
      badFiberData.length + ambientData.length :=
  rfl

/-- The explicit cardinal bound exposed without replacing the global constant-flat carrier. -/
theorem globalHOne_natCard_le
    (D : MazurConstantFlatHOneLocalizationData coeffPrime level)
    (badFiberData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantFlatBadFiberHZero coeffPrime level))
    (ambientData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantAmbientFppfHOne coeffPrime)) :
    Nat.card (mazurConstantFlat coeffPrime level).FppfHOne.{0} ≤
      coeffPrime ^ (badFiberData.length + ambientData.length) :=
  (D.globalHOneBoundedData badFiberData ambientData).card_le

end MazurConstantFlatHOneLocalizationData

end AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme
