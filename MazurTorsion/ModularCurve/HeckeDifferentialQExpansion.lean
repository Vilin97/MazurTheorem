/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.QExpansionFirstCoefficient
import Mathlib.NumberTheory.Divisors
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Hecke eigen-differentials detect a local q-linear term

For a local function with expansion `F(q)`, its cotangent differential is represented in the
standard logarithmic basis by

`q * dF/dq`.

Hecke operators act on a global differential expansion, not on the generally nonlinear function
series `F` itself.  The global differential and `dF` need agree only on the cotangent space; for
an elliptic quotient their full local expansions differ by a unit.  This file records precisely
that first-order relation.  It then transfers nonvanishing of the first coefficient of a Hecke
eigen-differential to the q-linear term required by the completed-stalk criterion.

The Hecke family is indexed by positive natural numbers.  This matches the mathematical Hecke
operators and avoids introducing a fictitious `T₀`.  The zero constant coefficient is instead
the ordinary cusp condition on the differential expansion.

## Provenance

The prime-index q-expansion rules are recorded in A. O. L. Atkin and J. Lehner,
"Hecke operators on Gamma_0(m)", *Math. Ann.* 185 (1970), 134–160, equation (3.1), p. 141,
DOI 10.1007/BF01359701; the displayed divisor-sum operator below is the standard weight-two
formula obtained from those rules and Hecke multiplicativity.  The cotangent/q-expansion role in
the formal-immersion argument follows B. Mazur, "Rational isogenies of prime degree",
*Invent. Math.* 44 (1978), Lemma 2.1 and the cotangent diagram on p. 141, and Proposition 3.1 on
pp. 142–143.  The elementary coefficient identities involving `q * dF/dq` are proved here.
These sources are bibliographic guidance only: no source text, code, or data is copied, and this
Lean implementation is released under Apache-2.0.
-/

namespace MazurTorsion.ModularCurve

open _root_.AlgebraicGeometry
open CategoryTheory

universe u

namespace HeckeDifferentialQExpansion

variable {K : Type u} [Field K]

/-- The q-expansion of the differential `dF`, written in the logarithmic basis `dq / q`. -/
noncomputable def logarithmicDerivativeExpansion (F : PowerSeries K) : PowerSeries K :=
  PowerSeries.X * PowerSeries.derivative K F

/-- Passing from a local function expansion to its logarithmic differential preserves the
coefficient in degree one. -/
@[simp]
theorem coeff_one_logarithmicDerivativeExpansion (F : PowerSeries K) :
    PowerSeries.coeff 1 (logarithmicDerivativeExpansion F) =
      PowerSeries.coeff 1 F := by
  simp [logarithmicDerivativeExpansion, PowerSeries.coeff_derivative]

/-- A logarithmic differential expansion has zero constant coefficient. -/
@[simp]
theorem coeff_zero_logarithmicDerivativeExpansion (F : PowerSeries K) :
    PowerSeries.coeff 0 (logarithmicDerivativeExpansion F) = 0 := by
  simp [logarithmicDerivativeExpansion]

/-- The standard weight-two q-expansion formula for `T_n` at level `N` with trivial character.

The coefficient in degree `m` is

`sum_{d | gcd(m,n), gcd(d,N)=1} d * a_(mn/d^2)`.

This definition is deliberately an operator on formal series.  Identifying a geometric Hecke
correspondence with this operator is a separate modular q-expansion theorem. -/
noncomputable def weightTwoHeckeQExpansion
    (level n : {n : ℕ // 0 < n}) :
    Module.End K (PowerSeries K) where
  toFun F := PowerSeries.mk fun m ↦
    ∑ d ∈ (Nat.gcd m n.1).divisors.filter (fun d ↦ Nat.Coprime d level.1),
      (d : K) * PowerSeries.coeff (m * n.1 / d ^ 2) F
  map_add' F G := by
    ext m
    simp only [PowerSeries.coeff_mk]
    simp_rw [map_add, mul_add]
    rw [Finset.sum_add_distrib]
    simp only [PowerSeries.coeff_mk]
  map_smul' c F := by
    ext m
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_smul, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    simp only [RingHom.id_apply]
    ring

@[simp]
theorem coeff_weightTwoHeckeQExpansion
    (level n : {n : ℕ // 0 < n}) (m : ℕ) (F : PowerSeries K) :
    PowerSeries.coeff m (weightTwoHeckeQExpansion level n F) =
      ∑ d ∈ (Nat.gcd m n.1).divisors.filter (fun d ↦ Nat.Coprime d level.1),
        (d : K) * PowerSeries.coeff (m * n.1 / d ^ 2) F := by
  change PowerSeries.coeff m (PowerSeries.mk fun m ↦
      ∑ d ∈ (Nat.gcd m n.1).divisors.filter (fun d ↦ Nat.Coprime d level.1),
        (d : K) * PowerSeries.coeff (m * n.1 / d ^ 2) F) = _
  rw [PowerSeries.coeff_mk]

/-- The first coefficient of the standard q-expansion `T_n F` is the `n`-th coefficient of
`F`. -/
@[simp]
theorem coeff_one_weightTwoHeckeQExpansion
    (level n : {n : ℕ // 0 < n}) (F : PowerSeries K) :
    PowerSeries.coeff 1 (weightTwoHeckeQExpansion level n F) =
      PowerSeries.coeff n.1 F := by
  rw [coeff_weightTwoHeckeQExpansion, Nat.gcd_one_left, Nat.divisors_one]
  have hfilter :
      ({1} : Finset ℕ).filter (fun d ↦ Nat.Coprime d level.1) = {1} := by
    apply Finset.filter_eq_self.mpr
    intro d hd
    simp only [Finset.mem_singleton] at hd
    subst d
    exact Nat.coprime_one_left level.1
  rw [hfilter]
  simp

/-- A nonzero simultaneous eigen-differential has nonzero first coefficient when positive-index
Hecke operators recover its positive coefficients in first position. -/
theorem coeff_one_ne_zero_of_simultaneousEigenDifferential
    (Omega : PowerSeries K) (hOmega : Omega ≠ 0)
    (hconstant : PowerSeries.coeff 0 Omega = 0)
    (T : {n : ℕ // 0 < n} → Module.End K (PowerSeries K))
    (eigenvalue : {n : ℕ // 0 < n} → K)
    (hfirst : ∀ n, PowerSeries.coeff 1 (T n Omega) =
      PowerSeries.coeff n.1 Omega)
    (heigen : ∀ n, T n Omega = eigenvalue n • Omega) :
    PowerSeries.coeff 1 Omega ≠ 0 := by
  intro hone
  apply hOmega
  apply (PowerSeries.forall_coeff_eq_zero Omega).mp
  intro n
  cases n with
  | zero => exact hconstant
  | succ n =>
      let m : {n : ℕ // 0 < n} := ⟨n + 1, Nat.succ_pos n⟩
      calc
        PowerSeries.coeff (n + 1) Omega =
            PowerSeries.coeff 1 (T m Omega) := (hfirst m).symm
        _ = PowerSeries.coeff 1 (eigenvalue m • Omega) := by rw [heigen m]
        _ = eigenvalue m * PowerSeries.coeff 1 Omega := by
          simpa only [smul_eq_mul] using
            PowerSeries.coeff_smul 1 Omega (eigenvalue m)
        _ = 0 := by rw [hone, mul_zero]

/-- Multiplying `q dF/dq` by a series changes its degree-one coefficient only by the constant
coefficient of that series. -/
@[simp]
theorem coeff_one_mul_logarithmicDerivativeExpansion
    (U F : PowerSeries K) :
    PowerSeries.coeff 1 (U * logarithmicDerivativeExpansion F) =
      PowerSeries.coeff 0 U * PowerSeries.coeff 1 F := by
  rw [PowerSeries.coeff_one_mul]
  simp only [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    coeff_zero_logarithmicDerivativeExpansion,
    coeff_one_logarithmicDerivativeExpansion, mul_zero, zero_add]
  exact mul_comm _ _

/-- The honest first-order bridge from an eigen-differential to a local parameter series.

The global differential `Omega` need not equal `q dF/dq` as a full power series.  Mazur's
cotangent comparison supplies only the displayed degree-one relation, up to a nonzero scalar;
that is exactly what the formal-immersion criterion needs. -/
theorem parameter_coeff_one_ne_zero_of_simultaneousEigenDifferential
    (F Omega : PowerSeries K)
    (scale : K) (_hscale : scale ≠ 0)
    (hfirstOrder : PowerSeries.coeff 1 Omega =
      scale * PowerSeries.coeff 1 F)
    (hOmega : Omega ≠ 0)
    (hconstant : PowerSeries.coeff 0 Omega = 0)
    (T : {n : ℕ // 0 < n} → Module.End K (PowerSeries K))
    (eigenvalue : {n : ℕ // 0 < n} → K)
    (hfirst : ∀ n, PowerSeries.coeff 1 (T n Omega) =
      PowerSeries.coeff n.1 Omega)
    (heigen : ∀ n, T n Omega = eigenvalue n • Omega) :
    PowerSeries.coeff 1 F ≠ 0 := by
  have hfirstOmega : PowerSeries.coeff 1 Omega ≠ 0 :=
    coeff_one_ne_zero_of_simultaneousEigenDifferential Omega hOmega hconstant
      T eigenvalue hfirst heigen
  intro hF
  apply hfirstOmega
  rw [hfirstOrder, hF, mul_zero]

/-- Specialization to the standard weight-two Hecke action on q-expansions.  The
first-coefficient recursion is now a theorem of the explicit operator, rather than a premise. -/
theorem parameter_coeff_one_ne_zero_of_weightTwoHeckeEigenDifferential
    (level : {n : ℕ // 0 < n}) (F Omega : PowerSeries K)
    (scale : K) (hscale : scale ≠ 0)
    (hfirstOrder : PowerSeries.coeff 1 Omega =
      scale * PowerSeries.coeff 1 F)
    (hOmega : Omega ≠ 0)
    (hconstant : PowerSeries.coeff 0 Omega = 0)
    (eigenvalue : {n : ℕ // 0 < n} → K)
    (heigen : ∀ n,
      weightTwoHeckeQExpansion level n Omega = eigenvalue n • Omega) :
    PowerSeries.coeff 1 F ≠ 0 :=
  parameter_coeff_one_ne_zero_of_simultaneousEigenDifferential
    F Omega scale hscale hfirstOrder hOmega hconstant
      (weightTwoHeckeQExpansion level) eigenvalue
      (fun n ↦ coeff_one_weightTwoHeckeQExpansion level n Omega) heigen

/-- The elliptic-quotient form of the bridge: an invariant eigen-differential is a unit multiple
of the differential of a local parameter.  Only the unit's nonzero constant coefficient enters
the cotangent calculation. -/
theorem
    parameter_coeff_one_ne_zero_of_weightTwoHeckeEigenDifferential_of_unitMultiple
    (level : {n : ℕ // 0 < n}) (F Omega U : PowerSeries K)
    (hDifferential : Omega = U * logarithmicDerivativeExpansion F)
    (hunitConstant : PowerSeries.coeff 0 U ≠ 0)
    (hOmega : Omega ≠ 0)
    (eigenvalue : {n : ℕ // 0 < n} → K)
    (heigen : ∀ n,
      weightTwoHeckeQExpansion level n Omega = eigenvalue n • Omega) :
    PowerSeries.coeff 1 F ≠ 0 := by
  have hfirstOrder : PowerSeries.coeff 1 Omega =
      PowerSeries.coeff 0 U * PowerSeries.coeff 1 F := by
    rw [hDifferential, coeff_one_mul_logarithmicDerivativeExpansion]
  have hconstant : PowerSeries.coeff 0 Omega = 0 := by
    rw [hDifferential, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply U]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply
      (logarithmicDerivativeExpansion F)]
    rw [coeff_zero_logarithmicDerivativeExpansion, mul_zero]
  exact parameter_coeff_one_ne_zero_of_weightTwoHeckeEigenDifferential
    level F Omega (PowerSeries.coeff 0 U) hunitConstant hfirstOrder hOmega
      hconstant eigenvalue heigen

end HeckeDifferentialQExpansion

namespace DegreeOneCotangentCertificate

variable {X Y : Scheme.{u}}

/-- A nonzero Hecke eigen-differential with the same degree-one cotangent class as the pulled-back
local parameter proves formal immersion. -/
theorem isFormalImmersionAt_of_heckeEigenDifferential_qExpansion
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 pi]
    (Y : Scheme.{u}) [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (g : Spec (.of K) ⟶ X)
    [IsIso (X.descResidueField (Scheme.stalkClosedPointTo g))]
    [IsIso (Y.descResidueField (Scheme.stalkClosedPointTo (g ≫ f)))]
    (hx : g (IsLocalRing.closedPoint K) ≠ genericPoint X)
    (qCoordinate :
      Scheme.CompletedStalk X (g (IsLocalRing.closedPoint K)) ≃+* PowerSeries K)
    (targetParameter : IsLocalRing.maximalIdeal
      (Y.presheaf.stalk (f (g (IsLocalRing.closedPoint K)))))
    (F Omega : PowerSeries K)
    (hqExpansion :
      qCoordinate (algebraMap
        (X.presheaf.stalk (g (IsLocalRing.closedPoint K)))
        (Scheme.CompletedStalk X (g (IsLocalRing.closedPoint K)))
        ((f.stalkMap (g (IsLocalRing.closedPoint K))).hom targetParameter)) = F)
    (scale : K) (hscale : scale ≠ 0)
    (hfirstOrder : PowerSeries.coeff 1 Omega =
      scale * PowerSeries.coeff 1 F)
    (hOmega : Omega ≠ 0)
    (hconstant : PowerSeries.coeff 0 Omega = 0)
    (T : {n : ℕ // 0 < n} → Module.End K (PowerSeries K))
    (eigenvalue : {n : ℕ // 0 < n} → K)
    (hfirst : ∀ n, PowerSeries.coeff 1 (T n Omega) =
      PowerSeries.coeff n.1 Omega)
    (heigen : ∀ n, T n Omega = eigenvalue n • Omega) :
    AlgebraicGeometry.IsFormalImmersionAt f
      (g (IsLocalRing.closedPoint K)) := by
  apply isFormalImmersionAt_of_smoothRelativeCurve_rationalPoint_of_qExpansionCoeffOne
    K X pi Y f g hx qCoordinate targetParameter
  rw [hqExpansion]
  exact
    HeckeDifferentialQExpansion.parameter_coeff_one_ne_zero_of_simultaneousEigenDifferential
      F Omega scale hscale hfirstOrder hOmega hconstant T eigenvalue hfirst heigen

/-- Formal immersion from the explicit weight-two Hecke q-expansion action on the pulled-back
parameter differential. -/
theorem isFormalImmersionAt_of_weightTwoHeckeEigenDifferential_qExpansion
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 pi]
    (Y : Scheme.{u}) [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (g : Spec (.of K) ⟶ X)
    [IsIso (X.descResidueField (Scheme.stalkClosedPointTo g))]
    [IsIso (Y.descResidueField (Scheme.stalkClosedPointTo (g ≫ f)))]
    (hx : g (IsLocalRing.closedPoint K) ≠ genericPoint X)
    (qCoordinate :
      Scheme.CompletedStalk X (g (IsLocalRing.closedPoint K)) ≃+* PowerSeries K)
    (targetParameter : IsLocalRing.maximalIdeal
      (Y.presheaf.stalk (f (g (IsLocalRing.closedPoint K)))))
    (level : {n : ℕ // 0 < n}) (F Omega : PowerSeries K)
    (hqExpansion :
      qCoordinate (algebraMap
        (X.presheaf.stalk (g (IsLocalRing.closedPoint K)))
        (Scheme.CompletedStalk X (g (IsLocalRing.closedPoint K)))
        ((f.stalkMap (g (IsLocalRing.closedPoint K))).hom targetParameter)) = F)
    (scale : K) (hscale : scale ≠ 0)
    (hfirstOrder : PowerSeries.coeff 1 Omega =
      scale * PowerSeries.coeff 1 F)
    (hOmega : Omega ≠ 0)
    (hconstant : PowerSeries.coeff 0 Omega = 0)
    (eigenvalue : {n : ℕ // 0 < n} → K)
    (heigen : ∀ n,
      HeckeDifferentialQExpansion.weightTwoHeckeQExpansion level n Omega =
        eigenvalue n • Omega) :
    AlgebraicGeometry.IsFormalImmersionAt f
      (g (IsLocalRing.closedPoint K)) := by
  apply isFormalImmersionAt_of_heckeEigenDifferential_qExpansion
    K X pi Y f g hx qCoordinate targetParameter F Omega hqExpansion
      scale hscale hfirstOrder hOmega hconstant
      (HeckeDifferentialQExpansion.weightTwoHeckeQExpansion level)
      eigenvalue
  · intro n
    exact HeckeDifferentialQExpansion.coeff_one_weightTwoHeckeQExpansion
      level n Omega
  · exact heigen

end DegreeOneCotangentCertificate

end MazurTorsion.ModularCurve
