/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FormalImmersionAffineFiberSpec
import MazurTorsion.ModularCurve.HeckeFirstCoefficient

/-!
# An affine cusp uniformizer feeds the `Spec.map` formal-immersion criterion

This file narrows the remaining handoff from an explicit modular affine chart
to the checked affine-fibre formal-immersion machinery.  For an affine map
`Spec T → Spec S`, a prime `q` of the special fibre of `T` is the proposed
cusp.  The geometric chart calculation is asked to prove that an element
called `qParameter`:

* generates the maximal ideal of the localized special fibre at `q`; and
* does not lie in its square.

Those two concrete equalities imply that the source cotangent space has
dimension one.  Thus a nonzero first-`q`-coefficient of one pulled-back
cotangent vector supplies `Ideal.Fiber.IsAffineFiberDegreeOneCotangent`, and
the existing stalk comparison proves formal immersion for the genuine map
`Spec.map g`.

No integral `X₀(N)` is manufactured here.  An application to the Mazur route
must still construct the represented modular chart, identify its cusp prime
and `q`-parameter, prove the two residue-map surjections, and calculate the
first coefficient of the optimal-quotient map.  The final theorem exposes
exactly those obligations rather than hiding them in a proposed modular-curve
structure.
-/

open Algebra TensorProduct AlgebraicGeometry
open MazurTorsion.ModularCurve

namespace Ideal.Fiber

universe u

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T]

/-- The canonical map into a local ring's maximal-ideal-adic completion.

Naming this map keeps the completion algebra instance stable when the local
ring is itself a dependent localization such as `Localization.AtPrime q`.
The four affine-cusp Hecke consumers below are its downstream users. -/
noncomputable def completionRingHom
    (A : Type u) [CommRing A] [IsLocalRing A] :
    A →+* LocalCompletion.Ring A :=
  algebraMap A (LocalCompletion.Ring A)

/-- The cotangent class of an explicitly supplied maximal-ideal element.
This helper keeps the localization ring instances coherent when the element
is used with `localizedRingMap`. -/
private noncomputable def cotangentClass
    {A : Type*} [CommRing A] [IsLocalRing A]
    (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A) :
    IsLocalRing.CotangentSpace A :=
  (IsLocalRing.maximalIdeal A).toCotangent ⟨a, ha⟩

/-- A unit linear term in the local affine `q`-expansion produces the
explicit cotangent vector detected by the degree-one criterion.

The equality says that the pullback of `sourceParameter` is a unit multiple
of `qParameter`, modulo the square of the cusp maximal ideal.  If its
cotangent class vanished, both the pullback and the remainder would lie in
that square, forcing `qParameter` into the square because the coefficient is
a unit. -/
theorem exists_detectedVector_of_unit_qExpansion
    (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime]
    (qParameter : Localization.AtPrime q)
    (hqLinear : qParameter ∉
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ 2)
    (sourceParameter :
      Localization.AtPrime (q.comap (map p g)))
    (hsourceMem : sourceParameter ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime (q.comap (map p g))))
    (unitCoefficient remainder : Localization.AtPrime q)
    (hunit : IsUnit unitCoefficient)
    (hremainder : remainder ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ 2)
    (hfirstOrder : localizedMap p g q sourceParameter =
      unitCoefficient * qParameter + remainder) :
    ∃ detectedVector : IsLocalRing.CotangentSpace
        (Localization.AtPrime (q.comap (map p g))),
      IsLocalRing.cotangentMapAtResidue (localizedRingMap p g q)
        detectedVector ≠ 0 := by
  let detectedVector : IsLocalRing.CotangentSpace
      (Localization.AtPrime (q.comap (map p g))) :=
    cotangentClass sourceParameter hsourceMem
  refine ⟨detectedVector, ?_⟩
  intro hzero
  rw [IsLocalRing.cotangentMapAtResidue_apply] at hzero
  dsimp [detectedVector, cotangentClass] at hzero
  have hsourceSquare : localizedMap p g q sourceParameter ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ 2 := by
    rwa [Ideal.toCotangent_eq_zero] at hzero
  have hunitQ : unitCoefficient * qParameter ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ 2 := by
    have heq : unitCoefficient * qParameter =
        localizedMap p g q sourceParameter - remainder := by
      rw [hfirstOrder]
      abel
    rw [heq]
    exact (IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ 2).sub_mem
      hsourceSquare hremainder
  exact hqLinear
    ((IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ 2).unit_mul_mem_iff_mem
      hunit |>.mp hunitQ)

/-- A nonzero simultaneous Hecke eigen-expansion detects an actual source
cotangent vector on the localized affine fibre.

Unlike `exists_detectedVector_of_unit_qExpansion`, this criterion does not
ask the caller to exhibit the linear coefficient directly.  The completed
local ring is identified with power series over its residue field, and the
degree-one Hecke recursion proves that the first coefficient is nonzero.  If
the pulled-back cotangent class vanished, its representative would lie in
the square of the cusp maximal ideal, whose completed `q`-expansion has zero
first coefficient. -/
theorem exists_detectedVector_of_heckeEigen_qExpansion
    (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime]
    [IsNoetherianRing (p.Fiber T)]
    (sourceParameter :
      Localization.AtPrime (q.comap (map p g)))
    (hsourceMem : sourceParameter ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime (q.comap (map p g))))
    (qCoordinate :
      LocalCompletion.Ring (Localization.AtPrime q) ≃+*
        PowerSeries (IsLocalRing.ResidueField (Localization.AtPrime q)))
    (Q : PowerSeries
      (IsLocalRing.ResidueField (Localization.AtPrime q)))
    (hqExpansion :
      qCoordinate
          (completionRingHom (Localization.AtPrime q)
            (localizedMap p g q sourceParameter)) = Q)
    (hQ : Q ≠ 0)
    (hecke : ℕ → Module.End
      (IsLocalRing.ResidueField (Localization.AtPrime q))
      (PowerSeries
        (IsLocalRing.ResidueField (Localization.AtPrime q))))
    (eigenvalue : ℕ →
      IsLocalRing.ResidueField (Localization.AtPrime q))
    (hfirst : ∀ n, PowerSeries.coeff 1 (hecke n Q) =
      PowerSeries.coeff n Q)
    (heigen : ∀ n, hecke n Q = eigenvalue n • Q) :
    ∃ detectedVector : IsLocalRing.CotangentSpace
        (Localization.AtPrime (q.comap (map p g))),
      IsLocalRing.cotangentMapAtResidue (localizedRingMap p g q)
        detectedVector ≠ 0 := by
  let detectedVector : IsLocalRing.CotangentSpace
      (Localization.AtPrime (q.comap (map p g))) :=
    cotangentClass sourceParameter hsourceMem
  refine ⟨detectedVector, ?_⟩
  intro hzero
  rw [IsLocalRing.cotangentMapAtResidue_apply] at hzero
  dsimp [detectedVector, cotangentClass] at hzero
  have hpullbackSquare : localizedMap p g q sourceParameter ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ 2 := by
    rwa [Ideal.toCotangent_eq_zero] at hzero
  have hcoeffZero : PowerSeries.coeff 1 Q = 0 := by
    rw [← hqExpansion]
    simpa only [completionRingHom] using
      QExpansionFirstCoefficient.coeff_one_completion_eq_zero_of_mem_maximalIdeal_sq
        qCoordinate hpullbackSquare
  exact
    (HeckeFirstCoefficient.coeff_one_ne_zero_of_simultaneousEigenvector
        Q hQ hecke eigenvalue hfirst heigen) hcoeffZero

/-- A genuine uniformizer on the localized target affine fibre supplies the
one-dimensional part of the affine-fibre cotangent certificate.

Here `T` is the coordinate ring of the source scheme, so the localization at
`q` is the target of the contravariant local-ring map.  The remaining vector
and its nonzero image are precisely the first-order quotient-map calculation.
The proof does not assume cotangent dimension one: it derives it from the
principal maximal ideal and the assertion that `qParameter` survives modulo
its square. -/
theorem isAffineFiberDegreeOneCotangent_of_qParameter
    (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime]
    [IsNoetherianRing (p.Fiber T)]
    (hresidue : Function.Surjective
      (IsLocalRing.ResidueField.map (localizedRingMap p g q)))
    (qParameter : Localization.AtPrime q)
    (hmaximal : IsLocalRing.maximalIdeal (Localization.AtPrime q) =
      Ideal.span {qParameter})
    (hqLinear : qParameter ∉
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ 2)
    (detectedVector : IsLocalRing.CotangentSpace
      (Localization.AtPrime (q.comap (map p g))))
    (hdetected : IsLocalRing.cotangentMapAtResidue
      (localizedRingMap p g q) detectedVector ≠ 0) :
    IsAffineFiberDegreeOneCotangent p g q := by
  have hqMem : qParameter ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
    rw [hmaximal]
    exact Ideal.mem_span_singleton_self qParameter
  have hprincipal :
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)).IsPrincipal := by
    let qParameter' :
        IsLocalRing.maximalIdeal (Localization.AtPrime q) :=
      ⟨qParameter, hqMem⟩
    refine ⟨⟨qParameter', ?_⟩⟩
    ext x
    constructor
    · intro hx
      have hx' : x ∈ Ideal.span {qParameter} := by
        rw [← hmaximal]
        exact hx
      rw [Ideal.mem_span_singleton] at hx'
      obtain ⟨a, rfl⟩ := hx'
      exact Submodule.mem_span_singleton.mpr
        ⟨a, by simpa [smul_eq_mul, qParameter'] using
          (mul_comm a qParameter)⟩
    · intro hx
      rw [Submodule.mem_span_singleton] at hx
      obtain ⟨a, ha⟩ := hx
      have hx' : x ∈ Ideal.span {qParameter} := by
        rw [Ideal.mem_span_singleton]
        exact ⟨a, ha.symm.trans (mul_comm a qParameter)⟩
      rw [hmaximal]
      exact hx'
  have hnotField : ¬ IsField (Localization.AtPrime q) := by
    intro hfield
    have hzero : qParameter = 0 := by
      have : qParameter ∈ (⊥ : Ideal (Localization.AtPrime q)) := by
        rw [← IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield]
        exact hqMem
      simpa using this
    apply hqLinear
    rw [hzero]
    exact (IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ 2).zero_mem
  have hle : Module.finrank
      (IsLocalRing.ResidueField (Localization.AtPrime q))
      (IsLocalRing.CotangentSpace (Localization.AtPrime q)) ≤ 1 :=
    IsLocalRing.finrank_cotangentSpace_le_one_iff.mpr hprincipal
  have hne : Module.finrank
      (IsLocalRing.ResidueField (Localization.AtPrime q))
      (IsLocalRing.CotangentSpace (Localization.AtPrime q)) ≠ 0 := by
    intro hzero
    exact hnotField
      (IsLocalRing.finrank_cotangentSpace_eq_zero_iff.mp hzero)
  have hfinrank : Module.finrank
      (IsLocalRing.ResidueField (Localization.AtPrime q))
      (IsLocalRing.CotangentSpace (Localization.AtPrime q)) = 1 := by
    omega
  exact ⟨hresidue, hfinrank, ⟨detectedVector, hdetected⟩⟩

/-- The uniformizer calculation reaches formal immersion for the actual
affine-scheme morphism.  Noetherianity of the ambient affine rings discharges
the completion finiteness inputs; Noetherianity of the special-fibre chart is
used above to turn principality into the exact cotangent dimension. -/
theorem isFormalImmersionAtSpecMap_of_qParameter
    (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime]
    [IsNoetherianRing S] [IsNoetherianRing T]
    [IsNoetherianRing (p.Fiber T)]
    (hresidueFiber : Function.Surjective
      (IsLocalRing.ResidueField.map (localizedRingMap p g q)))
    (qParameter : Localization.AtPrime q)
    (hmaximal : IsLocalRing.maximalIdeal (Localization.AtPrime q) =
      Ideal.span {qParameter})
    (hqLinear : qParameter ∉
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ 2)
    (detectedVector : IsLocalRing.CotangentSpace
      (Localization.AtPrime (q.comap (map p g))))
    (hdetected : IsLocalRing.cotangentMapAtResidue
      (localizedRingMap p g q) detectedVector ≠ 0)
    (hresidueAmbient : Function.Surjective
      (IsLocalRing.ResidueField.map (ambientLocalizedMap p g q))) :
    IsFormalImmersionAt (Spec.map (CommRingCat.ofHom g.toRingHom))
      (targetSpecPoint p q) :=
  (isAffineFiberDegreeOneCotangent_of_qParameter p g q hresidueFiber
    qParameter hmaximal hqLinear detectedVector
      hdetected).isFormalImmersionAtSpecMap_of_isNoetherian
        p g q hresidueAmbient

end Ideal.Fiber

namespace MazurTorsion.ModularCurve.AffineCuspQExpansion

open Ideal.Fiber

universe u

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T]

/-- The named downstream handoff for a represented modular affine cusp chart.

It consumes an actual first-order identity in the localized special-fibre
ring: the pullback of a quotient-side parameter is a unit times `q`, modulo
`q²`.  The preceding theorem proves that this equality detects a cotangent
vector; the principal cusp maximal ideal then gives the degree-one
certificate and formal immersion of the genuine `Spec.map` morphism. -/
theorem isFormalImmersionAtSpecMap_of_unit_qExpansion
    (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime]
    [IsNoetherianRing S] [IsNoetherianRing T]
    [IsNoetherianRing (p.Fiber T)]
    (hresidueFiber : Function.Surjective
      (IsLocalRing.ResidueField.map (localizedRingMap p g q)))
    (qParameter : Localization.AtPrime q)
    (hmaximal : IsLocalRing.maximalIdeal (Localization.AtPrime q) =
      Ideal.span {qParameter})
    (hqLinear : qParameter ∉
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ 2)
    (sourceParameter :
      Localization.AtPrime (q.comap (map p g)))
    (hsourceMem : sourceParameter ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime (q.comap (map p g))))
    (unitCoefficient remainder : Localization.AtPrime q)
    (hunit : IsUnit unitCoefficient)
    (hremainder : remainder ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ 2)
    (hfirstOrder : localizedMap p g q sourceParameter =
      unitCoefficient * qParameter + remainder)
    (hresidueAmbient : Function.Surjective
      (IsLocalRing.ResidueField.map (ambientLocalizedMap p g q))) :
    IsFormalImmersionAt (Spec.map (CommRingCat.ofHom g.toRingHom))
      (targetSpecPoint p q) := by
  obtain ⟨detectedVector, hdetected⟩ :=
    exists_detectedVector_of_unit_qExpansion p g q qParameter hqLinear
      sourceParameter hsourceMem unitCoefficient remainder hunit
      hremainder hfirstOrder
  exact isFormalImmersionAtSpecMap_of_qParameter p g q hresidueFiber
    qParameter hmaximal hqLinear detectedVector hdetected hresidueAmbient

/-- A Hecke eigen-expansion on the completed local ring of the represented
affine cusp proves formal immersion for the genuine `Spec.map` morphism.

The principal-uniformizer hypotheses establish that the source curve has a
one-dimensional cotangent space.  Nonvanishing and the first-coefficient
Hecke recursion then supply the detected quotient-side vector, so the
existing affine-fibre-to-ambient completion comparison applies without a
separate asserted linear coefficient. -/
theorem isFormalImmersionAtSpecMap_of_heckeEigen_qExpansion
    (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime]
    [IsNoetherianRing S] [IsNoetherianRing T]
    [IsNoetherianRing (p.Fiber T)]
    (qParameter : Localization.AtPrime q)
    (hmaximal : IsLocalRing.maximalIdeal (Localization.AtPrime q) =
      Ideal.span {qParameter})
    (hqLinear : qParameter ∉
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ 2)
    (sourceParameter :
      Localization.AtPrime (q.comap (map p g)))
    (hsourceMem : sourceParameter ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime (q.comap (map p g))))
    (qCoordinate :
      LocalCompletion.Ring (Localization.AtPrime q) ≃+*
        PowerSeries (IsLocalRing.ResidueField (Localization.AtPrime q)))
    (Q : PowerSeries
      (IsLocalRing.ResidueField (Localization.AtPrime q)))
    (hqExpansion :
      qCoordinate
          (completionRingHom (Localization.AtPrime q)
            (localizedMap p g q sourceParameter)) = Q)
    (hQ : Q ≠ 0)
    (hecke : ℕ → Module.End
      (IsLocalRing.ResidueField (Localization.AtPrime q))
      (PowerSeries
        (IsLocalRing.ResidueField (Localization.AtPrime q))))
    (eigenvalue : ℕ →
      IsLocalRing.ResidueField (Localization.AtPrime q))
    (hfirst : ∀ n, PowerSeries.coeff 1 (hecke n Q) =
      PowerSeries.coeff n Q)
    (heigen : ∀ n, hecke n Q = eigenvalue n • Q)
    (hresidueAmbient : Function.Surjective
      (IsLocalRing.ResidueField.map (ambientLocalizedMap p g q))) :
    IsFormalImmersionAt (Spec.map (CommRingCat.ofHom g.toRingHom))
      (targetSpecPoint p q) := by
  have hresidueFiber : Function.Surjective
      (IsLocalRing.ResidueField.map (localizedRingMap p g q)) :=
    localizedResidueFieldMap_surjective_of_ambient p g q hresidueAmbient
  obtain ⟨detectedVector, hdetected⟩ :=
    exists_detectedVector_of_heckeEigen_qExpansion p g q sourceParameter
      hsourceMem qCoordinate Q hqExpansion hQ hecke eigenvalue hfirst heigen
  exact isFormalImmersionAtSpecMap_of_qParameter p g q hresidueFiber
    qParameter hmaximal hqLinear detectedVector hdetected hresidueAmbient

end MazurTorsion.ModularCurve.AffineCuspQExpansion
