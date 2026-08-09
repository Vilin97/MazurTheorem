/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import EllipticCurves.ReductionAtPrime
import MazurTorsion.NumberTheory.XOneEighteenRealCubicQuotient

/-!
# The mod-seventeen point count for the `X₁(18)` elliptic quotient

The rational-coefficient model of the real-cubic quotient is

`y² + xy + y = x³ - x² + 25x + 1`.

This file records its integral model and verifies, by kernel reduction over
`ZMod 17`, that its good special fibre has exactly 21 points.  The result is
deliberately only a finite-field and integral-model certificate: using it to
specialize torsion over the real cubic coefficient field still requires a
prime of its ring of integers above seventeen and the corresponding formal
kernel theorem.
-/

open WeierstrassCurve

namespace MazurTorsion.XOneEighteenQuotientMod17

open WeierstrassCurve.Affine
  IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum
open MazurTorsion.XOneEighteenRealCubicQuotient

private instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- The integral rational-coefficient model `[1,-1,1,25,1]`. -/
def integralRationalModel : WeierstrassCurve ℤ :=
  ⟨1, -1, 1, 25, 1⟩

/-- Base change of the integral model is the rational-coefficient model over
the real cubic field. -/
theorem integralRationalModel_map_K :
    integralRationalModel.map (algebraMap ℤ K) = rationalModel := by
  ext <;> simp [integralRationalModel, rationalModel]

/-- The discriminant of the integral model is `-2 * 3^12`. -/
theorem integralRationalModel_discriminant :
    integralRationalModel.Δ = -1062882 := by
  norm_num [integralRationalModel, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The integer height-one prime `(17)`. -/
def intPrimeSeventeen : HeightOneSpectrum ℤ :=
  .ofPrime (p := Ideal.span {(17 : ℤ)})
    (Ideal.prime_span_singleton_iff.mpr
      (Nat.prime_iff_prime_int.mp (by decide)))

@[simp] theorem intPrimeSeventeen_asIdeal :
    intPrimeSeventeen.asIdeal = Ideal.span {(17 : ℤ)} :=
  rfl

noncomputable instance :
    DecidableEq (ℤ ⧸ intPrimeSeventeen.asIdeal) :=
  (Int.quotientSpanNatEquivZMod 17).toEquiv.decidableEq

/-- Good reduction at seventeen, checked from the integral discriminant. -/
instance integralRationalModel_red_isElliptic :
    (redCurve intPrimeSeventeen integralRationalModel).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  change
    (integralRationalModel.map
      (algebraMap ℤ (ℤ ⧸ intPrimeSeventeen.asIdeal))).Δ ≠ 0
  rw [Ne, WeierstrassCurve.map_Δ,
    Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem,
    intPrimeSeventeen_asIdeal,
    Ideal.mem_span_singleton]
  norm_num [integralRationalModel_discriminant]

/-- The concrete special fibre over `F₁₇`. -/
def rationalModelModSeventeen : WeierstrassCurve (ZMod 17) :=
  ⟨1, -1, 1, 25, 1⟩

instance rationalModelModSeventeen_isElliptic :
    rationalModelModSeventeen.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  decide

/-- The canonical identification of the integer residue field at seventeen
with `ZMod 17`. -/
noncomputable def residueSeventeenAlgEquiv :
    (ℤ ⧸ intPrimeSeventeen.asIdeal) ≃ₐ[ℤ] ZMod 17 :=
  AlgEquiv.ofRingEquiv
    (f := Int.quotientSpanNatEquivZMod 17) fun x ↦ by
      change (Int.quotientSpanNatEquivZMod 17 :
        (ℤ ⧸ Ideal.span {((17 : ℕ) : ℤ)}) →+* ZMod 17)
          (Ideal.Quotient.mk (Ideal.span {((17 : ℕ) : ℤ)}) x) =
            Int.castRingHom (ZMod 17) x
      simpa only [RingHom.comp_apply] using DFunLike.congr_fun
        (Int.quotientSpanNatEquivZMod_comp_Quotient_mk 17) x

private theorem baseChange_modSeventeen :
    ((integralRationalModel.toAffine ⁄ (ZMod 17)) :
      WeierstrassCurve _).toAffine =
        rationalModelModSeventeen.toAffine := by
  ext <;> decide +kernel

/-- The abstract residue-field point group is additively equivalent to the
computable point group over `ZMod 17`. -/
noncomputable def reducedPointEquiv :
    (redCurve intPrimeSeventeen integralRationalModel).Point ≃+
      rationalModelModSeventeen.toAffine.Point :=
  (Point.mapEquiv (W' := integralRationalModel.toAffine)
      residueSeventeenAlgEquiv).trans
    (Point.congr baseChange_modSeventeen)

noncomputable instance reducedPoint_finite :
    Finite (redCurve intPrimeSeventeen integralRationalModel).Point :=
  .of_equiv rationalModelModSeventeen.toAffine.Point
    reducedPointEquiv.symm.toEquiv

/-- The special fibre at seventeen has exactly 21 points. -/
theorem card_reducedCurve_seventeen :
    Nat.card (redCurve intPrimeSeventeen integralRationalModel).Point = 21 := by
  calc
    Nat.card (redCurve intPrimeSeventeen integralRationalModel).Point =
        Fintype.card rationalModelModSeventeen.toAffine.Point :=
      (Nat.card_congr reducedPointEquiv.toEquiv).trans
        Nat.card_eq_fintype_card
    _ = 21 := by decide

/-- Concrete form of the same point-count certificate. -/
theorem card_rationalModelModSeventeen :
    Fintype.card rationalModelModSeventeen.toAffine.Point = 21 := by
  decide

/-- Every point of the abstract special fibre has additive order dividing
21.  This is the form intended for a later number-field torsion
specialization theorem. -/
theorem reducedPoint_addOrderOf_dvd_twentyOne
    (P : (redCurve intPrimeSeventeen integralRationalModel).Point) :
    addOrderOf P ∣ 21 := by
  rw [← card_reducedCurve_seventeen]
  exact addOrderOf_dvd_natCard P

/-- Every point of the special fibre has additive order dividing 21. -/
theorem addOrderOf_dvd_twentyOne
    (P : rationalModelModSeventeen.toAffine.Point) :
    addOrderOf P ∣ 21 := by
  simpa [card_rationalModelModSeventeen] using addOrderOf_dvd_natCard P

end MazurTorsion.XOneEighteenQuotientMod17
