/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.DegreeOneCotangent
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Detecting a formal immersion from the first `q`-coefficient

Let `R` be a Noetherian local ring and suppose that its completion has a chosen coordinate

`R̂ ≃ K⟦q⟧`.

An element of the square of the maximal ideal has zero `q¹`-coefficient.  Consequently, if the
pullback of a target local parameter has nonzero `q¹`-coefficient, its class in the source
cotangent space is nonzero.  This is the exact algebraic bridge from a normalized cusp
`q`-expansion calculation to the degree-one formal-immersion consumer.

The coordinate is placed on the completed stalk, rather than the stalk itself: this is the
geometrically correct form of a formal parameter at a smooth curve point.
-/

namespace MazurTorsion.ModularCurve

open _root_.AlgebraicGeometry
open CategoryTheory
open Ideal

universe u

namespace QExpansionFirstCoefficient

variable {K : Type u} [Field K]

/-- A series in the square of the maximal ideal of `K⟦q⟧` has zero first coefficient. -/
theorem coeff_one_eq_zero_of_mem_maximalIdeal_sq
    {F : PowerSeries K}
    (hF : F ∈ IsLocalRing.maximalIdeal (PowerSeries K) ^ 2) :
    PowerSeries.coeff 1 F = 0 := by
  rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at hF
  exact hF 1 (by omega)

/-- The first coefficient of a normalized first-order expansion `c q + q² F` is `c`. -/
@[simp]
theorem coeff_one_C_mul_X_add_X_sq_mul (c : K) (F : PowerSeries K) :
    PowerSeries.coeff 1
      (PowerSeries.C c * PowerSeries.X + PowerSeries.X ^ 2 * F) = c := by
  simp [PowerSeries.coeff_X_pow_mul']

/-- In a completed local `q`-coordinate, a stalk element lying in `m²` has zero first
coefficient.  This transports the concrete power-series calculation through the actual
completion map and the chosen coordinate. -/
theorem coeff_one_completion_eq_zero_of_mem_maximalIdeal_sq
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (qCoordinate : LocalCompletion.Ring R ≃+* PowerSeries K)
    {a : R} (ha : a ∈ IsLocalRing.maximalIdeal R ^ 2) :
    PowerSeries.coeff 1
        (qCoordinate (algebraMap R (LocalCompletion.Ring R) a)) = 0 := by
  have hcompletion :
      algebraMap R (LocalCompletion.Ring R) a ∈
        IsLocalRing.maximalIdeal (LocalCompletion.Ring R) ^ 2 := by
    have hmap := Ideal.mem_map_of_mem
      (algebraMap R (LocalCompletion.Ring R)) ha
    simpa only [Ideal.map_pow, ← AdicCompletion.maximalIdeal_eq_map] using hmap
  have hseries :
      qCoordinate (algebraMap R (LocalCompletion.Ring R) a) ∈
        IsLocalRing.maximalIdeal (PowerSeries K) ^ 2 := by
    have hmap := Ideal.mem_map_of_mem (qCoordinate :
      LocalCompletion.Ring R →+* PowerSeries K) hcompletion
    have hmaximal :
        (IsLocalRing.maximalIdeal (LocalCompletion.Ring R)).map
            (qCoordinate : LocalCompletion.Ring R →+* PowerSeries K) =
          IsLocalRing.maximalIdeal (PowerSeries K) :=
      IsLocalRing.map_maximalIdeal_of_surjective
        (qCoordinate : LocalCompletion.Ring R →+* PowerSeries K) qCoordinate.surjective
    rw [Ideal.map_pow, hmaximal] at hmap
    exact hmap
  exact coeff_one_eq_zero_of_mem_maximalIdeal_sq hseries

end QExpansionFirstCoefficient

namespace DegreeOneCotangentCertificate

variable {X Y : Scheme.{u}}

/-- The normalized first-`q`-coefficient consumer for the degree-one formal-immersion argument.

The completed source stalk is supplied with its genuine formal coordinate `K⟦q⟧`.  A target
maximal-ideal element supplies the target cotangent vector.  Nonvanishing of the `q¹`-coefficient
of its pullback then proves the actual formal-immersion predicate on completed local rings. -/
theorem isFormalImmersionAt_of_smoothRelativeCurve_rationalPoint_of_qExpansionCoeffOne
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 π]
    (Y : Scheme.{u}) [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (g : Spec (.of K) ⟶ X)
    [IsIso (X.descResidueField (Scheme.stalkClosedPointTo g))]
    [IsIso (Y.descResidueField (Scheme.stalkClosedPointTo (g ≫ f)))]
    (hx : g (IsLocalRing.closedPoint K) ≠ genericPoint X)
    (qCoordinate :
      Scheme.CompletedStalk X (g (IsLocalRing.closedPoint K)) ≃+* PowerSeries K)
    (a : IsLocalRing.maximalIdeal
      (Y.presheaf.stalk (f (g (IsLocalRing.closedPoint K)))))
    (hcoeff : PowerSeries.coeff 1
      (qCoordinate (algebraMap
        (X.presheaf.stalk (g (IsLocalRing.closedPoint K)))
        (Scheme.CompletedStalk X (g (IsLocalRing.closedPoint K)))
        ((f.stalkMap (g (IsLocalRing.closedPoint K))).hom a))) ≠ 0) :
    AlgebraicGeometry.IsFormalImmersionAt f (g (IsLocalRing.closedPoint K)) := by
  letI : Smooth π := SmoothOfRelativeDimension.smooth 1 π
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  apply isFormalImmersionAt_of_smoothRelativeCurve_rationalPoint K X π Y f g hx
    (Ideal.toCotangent
      (IsLocalRing.maximalIdeal
        (Y.presheaf.stalk (f (g (IsLocalRing.closedPoint K))))) a)
  intro hzero
  apply hcoeff
  apply QExpansionFirstCoefficient.coeff_one_completion_eq_zero_of_mem_maximalIdeal_sq
    qCoordinate
  rw [Scheme.Hom.cotangentMapAtResidue_apply,
    Scheme.Hom.cotangentMapAtInt_toCotangent,
    Ideal.toCotangent_eq_zero] at hzero
  exact hzero

/-- A normalized expansion `c q + q² F`, with nonzero leading coefficient, proves formal
immersion.  This is the concrete series-identity endpoint for a checked Hecke or modular-symbol
calculation at the cusp. -/
theorem isFormalImmersionAt_of_smoothRelativeCurve_rationalPoint_of_normalizedQExpansion
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 π]
    (Y : Scheme.{u}) [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (g : Spec (.of K) ⟶ X)
    [IsIso (X.descResidueField (Scheme.stalkClosedPointTo g))]
    [IsIso (Y.descResidueField (Scheme.stalkClosedPointTo (g ≫ f)))]
    (hx : g (IsLocalRing.closedPoint K) ≠ genericPoint X)
    (qCoordinate :
      Scheme.CompletedStalk X (g (IsLocalRing.closedPoint K)) ≃+* PowerSeries K)
    (a : IsLocalRing.maximalIdeal
      (Y.presheaf.stalk (f (g (IsLocalRing.closedPoint K)))))
    (c : K) (hc : c ≠ 0) (F : PowerSeries K)
    (hqExpansion :
      qCoordinate (algebraMap
        (X.presheaf.stalk (g (IsLocalRing.closedPoint K)))
        (Scheme.CompletedStalk X (g (IsLocalRing.closedPoint K)))
        ((f.stalkMap (g (IsLocalRing.closedPoint K))).hom a)) =
        PowerSeries.C c * PowerSeries.X + PowerSeries.X ^ 2 * F) :
    AlgebraicGeometry.IsFormalImmersionAt f (g (IsLocalRing.closedPoint K)) := by
  apply isFormalImmersionAt_of_smoothRelativeCurve_rationalPoint_of_qExpansionCoeffOne
    K X π Y f g hx qCoordinate a
  rw [hqExpansion, QExpansionFirstCoefficient.coeff_one_C_mul_X_add_X_sq_mul]
  exact hc

end DegreeOneCotangentCertificate

end MazurTorsion.ModularCurve
