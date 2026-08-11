/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenFiniteMumford
import MazurTorsion.NumberTheory.XOneThirteenFiniteMumfordFive

/-!
# Audited exponent tables for the finite `X₁(13)` Mumford records

This file records the same nineteen-row table over `𝔽₃` and `𝔽₅`.  The
integer coefficients in the displayed rows are reduced in the corresponding
field.  The convention is the one used by the imported balanced encodings:

* `O = ∞⁺` is the curve-point base point and `I = ∞⁻`;
* `D = [I - O]`;
* `rawDegreeZero n` represents `(n - 1)D`, so row zero
  `rawDegreeZero 1` is the identity, row one is `D`, and row eighteen is
  `-D`;
* `rawDegreeOne x y n` represents `[(x,y) - O] + (n - 1)D`;
* a degree-two row is ordered `(u₀,u₁,v₀,v₁)`, with
  `u = X² + u₁X + u₀` and `v = v₁X + v₀`.

The exponent labels retain the audited ordering of these coordinate records.
This finite certificate does not install a group law on the record types and
does not identify either record set with an actual Jacobian.

For mathematical provenance, the generalized curve model and its six
rational points are from Bruin--Derickx--Stoll, *Functiones et Approximatio*
65 (2021), 191--197, DOI 10.7169/facm/1945, p. 3.  The classical order-19
torsion and six-cusp intersection statements are from Mazur--Tate,
*Inventiones Mathematicae* 22 (1973), 41--49, DOI 10.1007/BF01425572,
pp. 43--46.  Neither paper prints this completed-square record table.  The
coordinate conversion, exponent assignment, and finite identities were
independently derived and are checked here by Lean; no source code or source
text is copied.
-/

namespace MazurTorsion.XOneThirteenFiniteMumfordExponentTables

open XOneThirteenFiniteMumford
open XOneThirteenFiniteMumfordFive
open XOneThirteenFiniteField

local instance : DecidableEq RawBalancedMumfordF3 := by
  unfold RawBalancedMumfordF3
  infer_instance

local instance : DecidableEq BalancedMumfordF3 := by
  exact Subtype.instDecidableEq

local instance : DecidableEq RawBalancedMumfordF5 := by
  unfold RawBalancedMumfordF5
  infer_instance

local instance : DecidableEq BalancedMumfordF5 := by
  exact Subtype.instDecidableEq

/-! ## The two nineteen-row tables -/

/-- The audited exponent ordering of all balanced records over `𝔽₃`. -/
def recordOfExponentF3 : Fin 19 → BalancedMumfordF3
  | 0 => ⟨rawDegreeZero 1, by decide⟩
  | 1 => ⟨rawDegreeZero 2, by decide⟩
  | 2 => ⟨rawDegreeTwo 0 1 1 0, by decide⟩
  | 3 => ⟨rawDegreeOne (-1) (-1) 0, by decide⟩
  | 4 => ⟨rawDegreeOne (-1) (-1) 1, by decide⟩
  | 5 => ⟨rawDegreeOne 0 1 0, by decide⟩
  | 6 => ⟨rawDegreeOne 0 1 1, by decide⟩
  | 7 => ⟨rawDegreeTwo 1 2 0 1, by decide⟩
  | 8 => ⟨rawDegreeTwo 0 0 (-1) (-2), by decide⟩
  | 9 => ⟨rawDegreeTwo 0 1 1 2, by decide⟩
  | 10 => ⟨rawDegreeTwo 0 1 (-1) (-2), by decide⟩
  | 11 => ⟨rawDegreeTwo 0 0 1 2, by decide⟩
  | 12 => ⟨rawDegreeTwo 1 2 0 (-1), by decide⟩
  | 13 => ⟨rawDegreeOne 0 (-1) 0, by decide⟩
  | 14 => ⟨rawDegreeOne 0 (-1) 1, by decide⟩
  | 15 => ⟨rawDegreeOne (-1) 1 0, by decide⟩
  | 16 => ⟨rawDegreeOne (-1) 1 1, by decide⟩
  | 17 => ⟨rawDegreeTwo 0 1 (-1) 0, by decide⟩
  | 18 => ⟨rawDegreeZero 0, by decide⟩
  | _ => ⟨rawDegreeZero 1, by decide⟩

/-- The same audited exponent ordering over `𝔽₅`. -/
def recordOfExponentF5 : Fin 19 → BalancedMumfordF5
  | 0 => ⟨rawDegreeZeroF5 1, by decide⟩
  | 1 => ⟨rawDegreeZeroF5 2, by decide⟩
  | 2 => ⟨rawDegreeTwoF5 0 1 1 0, by decide⟩
  | 3 => ⟨rawDegreeOneF5 (-1) (-1) 0, by decide⟩
  | 4 => ⟨rawDegreeOneF5 (-1) (-1) 1, by decide⟩
  | 5 => ⟨rawDegreeOneF5 0 1 0, by decide⟩
  | 6 => ⟨rawDegreeOneF5 0 1 1, by decide⟩
  | 7 => ⟨rawDegreeTwoF5 1 2 0 1, by decide⟩
  | 8 => ⟨rawDegreeTwoF5 0 0 (-1) (-2), by decide⟩
  | 9 => ⟨rawDegreeTwoF5 0 1 1 2, by decide⟩
  | 10 => ⟨rawDegreeTwoF5 0 1 (-1) (-2), by decide⟩
  | 11 => ⟨rawDegreeTwoF5 0 0 1 2, by decide⟩
  | 12 => ⟨rawDegreeTwoF5 1 2 0 (-1), by decide⟩
  | 13 => ⟨rawDegreeOneF5 0 (-1) 0, by decide⟩
  | 14 => ⟨rawDegreeOneF5 0 (-1) 1, by decide⟩
  | 15 => ⟨rawDegreeOneF5 (-1) 1 0, by decide⟩
  | 16 => ⟨rawDegreeOneF5 (-1) 1 1, by decide⟩
  | 17 => ⟨rawDegreeTwoF5 0 1 (-1) 0, by decide⟩
  | 18 => ⟨rawDegreeZeroF5 0, by decide⟩
  | _ => ⟨rawDegreeZeroF5 1, by decide⟩

/-- Every displayed `𝔽₃` row satisfies the imported validity predicate. -/
theorem recordOfExponentF3_valid (e : Fin 19) :
    IsValid (recordOfExponentF3 e).1 :=
  (recordOfExponentF3 e).2

/-- Every displayed `𝔽₅` row satisfies the imported validity predicate. -/
theorem recordOfExponentF5_valid (e : Fin 19) :
    IsValidF5 (recordOfExponentF5 e).1 :=
  (recordOfExponentF5 e).2

/-! ## Exhaustiveness from injectivity and the checked cardinalities -/

theorem recordOfExponentF3_injective :
    Function.Injective recordOfExponentF3 := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

theorem recordOfExponentF5_injective :
    Function.Injective recordOfExponentF5 := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

/-- The nineteen exponent labels enumerate all balanced records over `𝔽₃`. -/
noncomputable def finNineteenEquivBalancedMumfordF3 :
    Fin 19 ≃ BalancedMumfordF3 :=
  Equiv.ofBijective recordOfExponentF3
    ((Fintype.bijective_iff_injective_and_card recordOfExponentF3).mpr
      ⟨recordOfExponentF3_injective, by
        simp [card_balancedMumfordF3]⟩)

/-- The nineteen exponent labels enumerate all balanced records over `𝔽₅`. -/
noncomputable def finNineteenEquivBalancedMumfordF5 :
    Fin 19 ≃ BalancedMumfordF5 :=
  Equiv.ofBijective recordOfExponentF5
    ((Fintype.bijective_iff_injective_and_card recordOfExponentF5).mpr
      ⟨recordOfExponentF5_injective, by
        simp [card_balancedMumfordF5]⟩)

/-! ## Rows arising from checked curve points -/

/-- The six exponent labels whose rows are records of checked curve points. -/
def curvePointExponents : Finset (Fin 19) :=
  {0, 1, 4, 6, 14, 16}

/-- Exactly the rows `0,1,4,6,14,16` over `𝔽₃` lie in the image of the
checked curve-point map. -/
theorem recordOfExponentF3_isCurvePoint_iff (e : Fin 19) :
    (∃ P : PointCertificate,
      recordOfExponentF3 e = curvePointMumford P) ↔
        e ∈ curvePointExponents := by
  fin_cases e <;> decide

/-- Exactly the rows `0,1,4,6,14,16` over `𝔽₅` lie in the image of the
checked curve-point map. -/
theorem recordOfExponentF5_isCurvePoint_iff (e : Fin 19) :
    (∃ P : PointCertificateF5,
      recordOfExponentF5 e = curvePointMumfordF5 P) ↔
        e ∈ curvePointExponents := by
  fin_cases e <;> decide

end MazurTorsion.XOneThirteenFiniteMumfordExponentTables
