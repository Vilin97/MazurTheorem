/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.AffineCuspPolynomialChart

/-!
# Transporting the represented cusp chart across an affine presentation

The polynomial cusp chart is useful only after an affine neighbourhood of the
modular cusp has been identified with it.  This file makes that identification
an honest algebraic datum.  Given an `R`-algebra equivalence

`T ≃ₐ[R] MvPolynomial PUnit R`,

we construct the induced isomorphism of affine schemes and transport all of the
checked local geometry: the zero section, its point on every special fibre, a
fibre coordinate, the localized `q`-parameter, its maximal-ideal generator
property, its nonzero cotangent class, and Noetherianity.

The formal-immersion and arithmetic consumers at five and eleven therefore ask
for one genuine chart equivalence and the quotient-side Hecke expansion.  They
do not ask callers to restate the cusp prime or any of its local commutative
algebra.  No modular curve is identified with this affine chart here; producing
that equivalence for an actual integral `X₀(N)` remains a geometric theorem.
-/

noncomputable section

open Algebra TensorProduct AlgebraicGeometry CategoryTheory
open Ideal.Fiber

namespace MazurTorsion.ModularCurve.AffineCuspPolynomialChart

open MazurTorsion.ModularCurve.AffineCuspQExpansion

universe u

/-- An affine presentation of the one-coordinate cusp chart.

The direction of the equivalence is chosen so that its `Spec` map identifies
the represented polynomial chart with `Spec T`. -/
structure AffinePresentation
    (R T : Type u) [CommRing R] [CommRing T] [Algebra R T] where
  coordinateEquiv : T ≃ₐ[R] CoordinateRing R

namespace AffinePresentation

variable {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]

/-- The affine-scheme isomorphism contravariantly induced by the coordinate
equivalence. -/
noncomputable def specIso (C : AffinePresentation R T) :
    Spec (.of (CoordinateRing R)) ≅ Spec (.of T) where
  hom := Spec.map (CommRingCat.ofHom C.coordinateEquiv.toRingHom)
  inv := Spec.map (CommRingCat.ofHom C.coordinateEquiv.symm.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ← Spec.map_id]
    rw [Spec.map_inj]
    exact C.coordinateEquiv.toRingEquiv.toCommRingCatIso.inv_hom_id
  inv_hom_id := by
    rw [← Spec.map_comp, ← Spec.map_id]
    rw [Spec.map_inj]
    exact C.coordinateEquiv.toRingEquiv.toCommRingCatIso.hom_inv_id

/-- Evaluation at the transported cusp. -/
noncomputable def zeroRetraction (C : AffinePresentation R T) : T →ₐ[R] R :=
  (AffineCuspPolynomialChart.zeroRetraction R).comp
    C.coordinateEquiv.toAlgHom

/-- The zero section transported to `Spec T`. -/
noncomputable def zeroSection (C : AffinePresentation R T) :
    AffineStructuralSection (R := R) (T := T) where
  toSpec := Spec.map (CommRingCat.ofHom C.zeroRetraction.toRingHom)
  isSection := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    convert Spec.map_id (.of R)
    ext r
    simp [zeroRetraction, AffineCuspPolynomialChart.zeroRetraction]

/-- The coordinate-ring map recovered from the transported section is the
transported zero evaluation. -/
theorem zeroSection_retraction (C : AffinePresentation R T) :
    C.zeroSection.retraction = C.zeroRetraction := by
  apply AlgHom.ext
  intro t
  simp [Ideal.Fiber.AffineStructuralSection.retraction, zeroSection,
    zeroRetraction]

/-- The transported section is literally the polynomial zero section followed
by the affine-scheme chart isomorphism. -/
theorem zeroSection_toSpec (C : AffinePresentation R T) :
    C.zeroSection.toSpec =
      (AffineCuspPolynomialChart.zeroSection R).toSpec ≫ C.specIso.hom := by
  change Spec.map (CommRingCat.ofHom C.zeroRetraction.toRingHom) = _
  change Spec.map (CommRingCat.ofHom C.zeroRetraction.toRingHom) =
    Spec.map (CommRingCat.ofHom
      (AffineCuspPolynomialChart.zeroRetraction R).toRingHom) ≫
      Spec.map (CommRingCat.ofHom C.coordinateEquiv.toRingHom)
  rw [← Spec.map_comp]
  rw [Spec.map_inj]
  ext t
  rfl

/-- Base change of the coordinate equivalence to the residue field. -/
noncomputable def fiberEquiv
    (C : AffinePresentation R T) (p : Ideal R) [p.IsPrime] :
    p.Fiber T ≃ₐ[p.ResidueField] p.Fiber (CoordinateRing R) :=
  Algebra.TensorProduct.congr
    (AlgEquiv.refl : p.ResidueField ≃ₐ[p.ResidueField] p.ResidueField)
    C.coordinateEquiv

/-- The transported special fibre, explicitly identified with a polynomial
ring over the residue field. -/
noncomputable def fiberCoordinate
    (C : AffinePresentation R T) (p : Ideal R) [p.IsPrime] :
    p.Fiber T ≃ₐ[p.ResidueField] Polynomial p.ResidueField :=
  (C.fiberEquiv p).trans
    (AffineCuspPolynomialChart.fiberCoordinate R p)

/-- The transported fibre coordinate before applying `fiberCoordinate`. -/
noncomputable def fiberVariable
    (C : AffinePresentation R T) (p : Ideal R) [p.IsPrime] : p.Fiber T :=
  (C.fiberCoordinate p).symm Polynomial.X

/-- The transported variable maps to the variable on the represented
polynomial chart. -/
theorem fiberEquiv_fiberVariable
    (C : AffinePresentation R T) (p : Ideal R) [p.IsPrime] :
    C.fiberEquiv p (C.fiberVariable p) =
      AffineCuspPolynomialChart.fiberVariable R p := by
  simp [fiberVariable, fiberCoordinate,
    AffineCuspPolynomialChart.fiberVariable]

/-- Base change of the transported zero section agrees with base change of the
polynomial zero section through the fibre equivalence. -/
theorem fiberRetraction_eq_transport
    (C : AffinePresentation R T) (p : Ideal R) [p.IsPrime] :
    C.zeroSection.fiberRetraction p =
      ((AffineCuspPolynomialChart.zeroSection R).fiberRetraction p).comp
        (C.fiberEquiv p).toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro k t
  simp [AffineStructuralSection.fiberRetraction, C.zeroSection_retraction,
    AffineCuspPolynomialChart.zeroSection_retraction, zeroRetraction,
    fiberEquiv]

/-- The cusp prime itself is transported by the fibre equivalence. -/
theorem fiberPrime_eq_comap
    (C : AffinePresentation R T) (p : Ideal R) [p.IsPrime] :
    C.zeroSection.fiberPrime p =
      ((AffineCuspPolynomialChart.zeroSection R).fiberPrime p).comap
        (C.fiberEquiv p).toRingHom := by
  ext x
  simp only [AffineStructuralSection.fiberPrime, RingHom.mem_ker,
    Ideal.mem_comap]
  rw [C.fiberRetraction_eq_transport]
  rfl

/-- In the transported coordinate, the fibre section is evaluation at zero. -/
theorem fiberRetraction_eq_eval
    (C : AffinePresentation R T) (p : Ideal R) [p.IsPrime] :
    C.zeroSection.fiberRetraction p =
      (Polynomial.aeval (0 : p.ResidueField)).comp
        (C.fiberCoordinate p).toAlgHom := by
  rw [C.fiberRetraction_eq_transport,
    AffineCuspPolynomialChart.fiberRetraction_eq_eval]
  rfl

/-- The point selected by the transported section is the principal ideal of
the transported fibre coordinate. -/
theorem fiberPrime_eq_span
    (C : AffinePresentation R T) (p : Ideal R) [p.IsPrime] :
    C.zeroSection.fiberPrime p = Ideal.span {C.fiberVariable p} := by
  ext f
  rw [AffineStructuralSection.fiberPrime, RingHom.mem_ker]
  rw [C.fiberRetraction_eq_eval]
  rw [Ideal.mem_span_singleton]
  rw [← map_dvd_iff (C.fiberCoordinate p)]
  simp [fiberVariable, Polynomial.X_dvd_iff,
    Polynomial.coeff_zero_eq_aeval_zero]

/-- The local parameter on the transported chart. -/
noncomputable def qParameter
    (C : AffinePresentation R T) (p : Ideal R) [p.IsPrime] :
    Localization.AtPrime (C.zeroSection.fiberPrime p) :=
  algebraMap (p.Fiber T) (Localization.AtPrime (C.zeroSection.fiberPrime p))
    (C.fiberVariable p)

/-- The transported `q`-parameter generates the cusp maximal ideal. -/
theorem maximalIdeal_eq_span_qParameter
    (C : AffinePresentation R T) (p : Ideal R) [p.IsPrime] :
    IsLocalRing.maximalIdeal
        (Localization.AtPrime (C.zeroSection.fiberPrime p)) =
      Ideal.span {C.qParameter p} := by
  let locMap := algebraMap (p.Fiber T)
    (Localization.AtPrime (C.zeroSection.fiberPrime p))
  calc
    IsLocalRing.maximalIdeal
        (Localization.AtPrime (C.zeroSection.fiberPrime p)) =
        Ideal.map locMap (C.zeroSection.fiberPrime p) :=
      Localization.AtPrime.map_eq_maximalIdeal.symm
    _ = Ideal.map locMap (Ideal.span {C.fiberVariable p}) :=
      congrArg (Ideal.map locMap) (C.fiberPrime_eq_span p)
    _ = Ideal.span {C.qParameter p} := by
      rw [Ideal.map_span]
      simp [locMap, qParameter]

/-- The transported fibre coordinate is nonzero. -/
theorem fiberVariable_ne_zero
    (C : AffinePresentation R T) (p : Ideal R) [p.IsPrime] :
    C.fiberVariable p ≠ 0 := by
  intro hzero
  have hX := congrArg (C.fiberCoordinate p) hzero
  apply (Polynomial.X_ne_zero :
    (Polynomial.X : Polynomial p.ResidueField) ≠ 0)
  simpa only [fiberVariable, AlgEquiv.apply_symm_apply, map_zero] using hX

/-- Localization at the transported cusp does not kill `q`. -/
theorem qParameter_ne_zero
    (C : AffinePresentation R T) (p : Ideal R) [p.IsPrime] :
    C.qParameter p ≠ 0 := by
  letI : IsDomain (p.Fiber T) :=
    (C.fiberCoordinate p).toRingEquiv.toMulEquiv.isDomain _
  intro hzero
  apply C.fiberVariable_ne_zero p
  apply (IsLocalization.injective
      (Localization.AtPrime (C.zeroSection.fiberPrime p))
      (C.zeroSection.fiberPrime p).primeCompl_le_nonZeroDivisors)
  simpa [qParameter] using hzero

/-- The transported parameter survives modulo the square of the maximal ideal,
so it defines a nonzero cotangent class. -/
theorem qParameter_not_mem_maximalIdeal_sq
    (C : AffinePresentation R T) (p : Ideal R) [p.IsPrime] :
    C.qParameter p ∉
      IsLocalRing.maximalIdeal
          (Localization.AtPrime (C.zeroSection.fiberPrime p)) ^ 2 := by
  letI : IsDomain (p.Fiber T) :=
    (C.fiberCoordinate p).toRingEquiv.toMulEquiv.isDomain _
  intro hsq
  rw [C.maximalIdeal_eq_span_qParameter,
    Ideal.span_singleton_pow] at hsq
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hsq
  have hcancel : (1 : Localization.AtPrime
      (C.zeroSection.fiberPrime p)) = C.qParameter p * c := by
    apply mul_left_cancel₀ (C.qParameter_ne_zero p)
    simpa [pow_two, mul_assoc] using hc
  have hunit : IsUnit (C.qParameter p) :=
    isUnit_iff_exists_inv.mpr ⟨c, hcancel.symm⟩
  have hmem : C.qParameter p ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime (C.zeroSection.fiberPrime p)) := by
    rw [C.maximalIdeal_eq_span_qParameter]
    exact Ideal.mem_span_singleton_self _
  exact (IsLocalRing.mem_maximalIdeal (C.qParameter p)).mp hmem hunit

/-- Noetherianity of the arbitrary affine presentation, transported from the
polynomial coordinate ring. -/
theorem isNoetherianRing
    (C : AffinePresentation R T) [IsNoetherianRing R] : IsNoetherianRing T :=
  isNoetherianRing_of_ringEquiv (CoordinateRing R)
    C.coordinateEquiv.symm.toRingEquiv

/-- Noetherianity of every transported special fibre. -/
theorem fiberIsNoetherianRing
    (C : AffinePresentation R T) (p : Ideal R) [p.IsPrime] :
    IsNoetherianRing (p.Fiber T) :=
  isNoetherianRing_of_ringEquiv (Polynomial p.ResidueField)
    (C.fiberCoordinate p).symm.toRingEquiv

/-- A Hecke eigen-expansion on any affine presentation of the polynomial cusp
chart proves formal immersion for the genuine map out of `Spec T`.

No Noetherian structure, cusp prime, local generator, or cotangent nonvanishing
is supplied by the caller: all of them are transported from `coordinateEquiv`.
The remaining arguments belong to the quotient-side q-expansion. -/
theorem isFormalImmersionAtSpecMap_of_heckeEigen_qExpansion
    {S : Type u} [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (C : AffinePresentation R T)
    (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T)
    (sourceParameter : Localization.AtPrime
      ((C.zeroSection.fiberPrime p).comap (Ideal.Fiber.map p g)))
    (hsourceMem : sourceParameter ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime
        ((C.zeroSection.fiberPrime p).comap (Ideal.Fiber.map p g))))
    (qCoordinate :
      LocalCompletion.Ring
          (Localization.AtPrime (C.zeroSection.fiberPrime p)) ≃+*
        PowerSeries
          (IsLocalRing.ResidueField
            (Localization.AtPrime (C.zeroSection.fiberPrime p))))
    (Q : PowerSeries
      (IsLocalRing.ResidueField
        (Localization.AtPrime (C.zeroSection.fiberPrime p))))
    (hqExpansion :
      qCoordinate
          (completionRingHom
            (Localization.AtPrime (C.zeroSection.fiberPrime p))
            (localizedMap p g (C.zeroSection.fiberPrime p)
              sourceParameter)) = Q)
    (hQ : Q ≠ 0)
    (hecke : ℕ → Module.End
      (IsLocalRing.ResidueField
        (Localization.AtPrime (C.zeroSection.fiberPrime p)))
      (PowerSeries
        (IsLocalRing.ResidueField
          (Localization.AtPrime (C.zeroSection.fiberPrime p)))))
    (eigenvalue : ℕ →
      IsLocalRing.ResidueField
        (Localization.AtPrime (C.zeroSection.fiberPrime p)))
    (hfirst : ∀ n, PowerSeries.coeff 1 (hecke n Q) =
      PowerSeries.coeff n Q)
    (heigen : ∀ n, hecke n Q = eigenvalue n • Q) :
    IsFormalImmersionAt
      (Spec.map (CommRingCat.ofHom g.toRingHom))
      (targetSpecPoint p (C.zeroSection.fiberPrime p)) := by
  letI : IsNoetherianRing T := C.isNoetherianRing
  letI : IsNoetherianRing (p.Fiber T) := C.fiberIsNoetherianRing p
  exact
    isFormalImmersionAtSpecMap_of_heckeEigen_qExpansion_of_structuralSection
      p g C.zeroSection (C.qParameter p)
      (C.maximalIdeal_eq_span_qParameter p)
      (C.qParameter_not_mem_maximalIdeal_sq p) sourceParameter hsourceMem
      qCoordinate Q hqExpansion hQ hecke eigenvalue hfirst heigen

end AffinePresentation

section ArithmeticConsumers

open MazurTorsion.EllipticCurve
open MazurTorsion.IntegerPrimeSpecialization
open MazurTorsion.OrderThirtyFive
open MazurTorsion.PrimeOrder
open WeierstrassCurve WeierstrassCurve.Affine

private abbrev FiveBase := atFive.adicCompletionIntegers ℚ

private abbrev FivePrime : Ideal FiveBase :=
  MazurTorsion.PrimeOrder.affineCuspSpecialFiberIdealAtFive

private noncomputable abbrev FiveCuspPrime
    {T : Type} [CommRing T] [Algebra FiveBase T]
    (C : AffinePresentation FiveBase T) : Ideal (FivePrime.Fiber T) :=
  C.zeroSection.fiberPrime FivePrime

/-- At the selected auxiliary prime five, a genuine affine presentation of the
polynomial cusp chart feeds the unconditional prime-order endpoint.

The chart equivalence constructs the integral cusp section and all local cusp
algebra.  The remaining hypotheses are the quotient map and q-expansion, the
noncuspidality of the modular section, and its collision with the cusp under
the bad-valuation assumption. -/
theorem rationalPoint_primeOrder_ne_of_affinePresentationAtFive
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {S T : Type} [CommRing S] [CommRing T]
    [Algebra FiveBase S] [Algebra FiveBase T]
    [IsNoetherianRing S]
    (C : AffinePresentation FiveBase T)
    (g : S →ₐ[FiveBase] T)
    (modularSection : Spec (.of FiveBase) ⟶ Spec (.of T))
    (sourceParameter : Localization.AtPrime
      ((FiveCuspPrime C).comap (Ideal.Fiber.map FivePrime g)))
    (hsourceMem : sourceParameter ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime
        ((FiveCuspPrime C).comap (Ideal.Fiber.map FivePrime g))))
    (qCoordinate :
      LocalCompletion.Ring (Localization.AtPrime (FiveCuspPrime C)) ≃+*
        PowerSeries
          (IsLocalRing.ResidueField
            (Localization.AtPrime (FiveCuspPrime C))))
    (Q : PowerSeries
      (IsLocalRing.ResidueField
        (Localization.AtPrime (FiveCuspPrime C))))
    (hqExpansion :
      qCoordinate
          (completionRingHom (Localization.AtPrime (FiveCuspPrime C))
            (localizedMap FivePrime g (FiveCuspPrime C)
              sourceParameter)) = Q)
    (hQ : Q ≠ 0)
    (hecke : ℕ → Module.End
      (IsLocalRing.ResidueField
        (Localization.AtPrime (FiveCuspPrime C)))
      (PowerSeries
        (IsLocalRing.ResidueField
          (Localization.AtPrime (FiveCuspPrime C)))))
    (eigenvalue : ℕ →
      IsLocalRing.ResidueField
        (Localization.AtPrime (FiveCuspPrime C)))
    (hfirst : ∀ n, PowerSeries.coeff 1 (hecke n Q) =
      PowerSeries.coeff n Q)
    (heigen : ∀ n, hecke n Q = eigenvalue n • Q)
    (hne : modularSection ≠ C.zeroSection.toSpec)
    (hspecializes : ¬ atFive.valuation ℚ E.j ≤ 1 →
      modularSection (IsLocalRing.closedPoint FiveBase) =
        C.zeroSection.toSpec (IsLocalRing.closedPoint FiveBase))
    (hquotient : ¬ atFive.valuation ℚ E.j ≤ 1 →
      modularSection ≫ Spec.map (CommRingCat.ofHom g.toRingHom) =
        C.zeroSection.toSpec ≫
          Spec.map (CommRingCat.ofHom g.toRingHom))
    (P : E.toAffine.Point)
    (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  letI : IsNoetherianRing T := C.isNoetherianRing
  letI : IsNoetherianRing (FivePrime.Fiber T) :=
    C.fiberIsNoetherianRing FivePrime
  exact
    rationalPoint_primeOrder_ne_of_affineCuspHeckeQExpansionAtFive_of_structuralSection
      g C.zeroSection modularSection (C.qParameter FivePrime)
      (C.maximalIdeal_eq_span_qParameter FivePrime)
      (C.qParameter_not_mem_maximalIdeal_sq FivePrime)
      sourceParameter hsourceMem qCoordinate Q hqExpansion hQ hecke eigenvalue
      hfirst heigen hne hspecializes hquotient P N hprime hN

private abbrev ElevenBase := atEleven.adicCompletionIntegers ℚ

private abbrev ElevenPrime : Ideal ElevenBase :=
  MazurTorsion.OrderThirtyFive.affineCuspSpecialFiberIdealAtEleven

private noncomputable abbrev ElevenCuspPrime
    {T : Type} [CommRing T] [Algebra ElevenBase T]
    (C : AffinePresentation ElevenBase T) : Ideal (ElevenPrime.Fiber T) :=
  C.zeroSection.fiberPrime ElevenPrime

/-- At auxiliary prime eleven, the same transported affine cusp chart feeds the
unconditional order-35 endpoint.  As at five, no local cusp prime, generator,
cotangent class, or Noetherian instance is assumed separately. -/
theorem rationalPoint_orderThirtyFive_ne_of_affinePresentationAtEleven
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {S T : Type} [CommRing S] [CommRing T]
    [Algebra ElevenBase S] [Algebra ElevenBase T]
    [IsNoetherianRing S]
    (C : AffinePresentation ElevenBase T)
    (g : S →ₐ[ElevenBase] T)
    (modularSection : Spec (.of ElevenBase) ⟶ Spec (.of T))
    (sourceParameter : Localization.AtPrime
      ((ElevenCuspPrime C).comap (Ideal.Fiber.map ElevenPrime g)))
    (hsourceMem : sourceParameter ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime
        ((ElevenCuspPrime C).comap (Ideal.Fiber.map ElevenPrime g))))
    (qCoordinate :
      LocalCompletion.Ring (Localization.AtPrime (ElevenCuspPrime C)) ≃+*
        PowerSeries
          (IsLocalRing.ResidueField
            (Localization.AtPrime (ElevenCuspPrime C))))
    (Q : PowerSeries
      (IsLocalRing.ResidueField
        (Localization.AtPrime (ElevenCuspPrime C))))
    (hqExpansion :
      qCoordinate
          (completionRingHom (Localization.AtPrime (ElevenCuspPrime C))
            (localizedMap ElevenPrime g (ElevenCuspPrime C)
              sourceParameter)) = Q)
    (hQ : Q ≠ 0)
    (hecke : ℕ → Module.End
      (IsLocalRing.ResidueField
        (Localization.AtPrime (ElevenCuspPrime C)))
      (PowerSeries
        (IsLocalRing.ResidueField
          (Localization.AtPrime (ElevenCuspPrime C)))))
    (eigenvalue : ℕ →
      IsLocalRing.ResidueField
        (Localization.AtPrime (ElevenCuspPrime C)))
    (hfirst : ∀ n, PowerSeries.coeff 1 (hecke n Q) =
      PowerSeries.coeff n Q)
    (heigen : ∀ n, hecke n Q = eigenvalue n • Q)
    (hne : modularSection ≠ C.zeroSection.toSpec)
    (hspecializes : ¬ atEleven.valuation ℚ E.j ≤ 1 →
      modularSection (IsLocalRing.closedPoint ElevenBase) =
        C.zeroSection.toSpec (IsLocalRing.closedPoint ElevenBase))
    (hquotient : ¬ atEleven.valuation ℚ E.j ≤ 1 →
      modularSection ≫ Spec.map (CommRingCat.ofHom g.toRingHom) =
        C.zeroSection.toSpec ≫
          Spec.map (CommRingCat.ofHom g.toRingHom))
    (P : E.toAffine.Point) :
    addOrderOf P ≠ 35 := by
  letI : IsNoetherianRing T := C.isNoetherianRing
  letI : IsNoetherianRing (ElevenPrime.Fiber T) :=
    C.fiberIsNoetherianRing ElevenPrime
  exact
    rationalPoint_orderThirtyFive_ne_of_affineCuspHeckeQExpansionAtEleven_of_structuralSection
      g C.zeroSection modularSection (C.qParameter ElevenPrime)
      (C.maximalIdeal_eq_span_qParameter ElevenPrime)
      (C.qParameter_not_mem_maximalIdeal_sq ElevenPrime)
      sourceParameter hsourceMem qCoordinate Q hqExpansion hQ hecke eigenvalue
      hfirst heigen hne hspecializes hquotient P

end ArithmeticConsumers

end MazurTorsion.ModularCurve.AffineCuspPolynomialChart
