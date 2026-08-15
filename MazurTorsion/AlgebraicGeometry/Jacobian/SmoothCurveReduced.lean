/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.RingTheory.Filtration
import TauCeti.RingTheory.Smooth.DimensionOne
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Reducedness of smooth relative curves

This file supplies the reducedness input needed to pass from geometric
irreducibility to integrality for a smooth relative curve.  The local proof
uses the étale presentation over a one-variable polynomial ring, flatness,
and Krull's intersection theorem.

The named downstream consumers are `Genus` and `PicardGeometry`.
-/

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.Jacobian.SmoothCurveReduced

universe u v w

open IsLocalRing

/-- A localization at a prime of a standard-smooth relative curve over a
field is reduced.  This version does not assume that the smooth algebra is
already a domain. -/
theorem localizationAtPrime_isReduced
    (K : Type u) (A : Type v) [Field K] [CommRing A] [Algebra K A]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 K A]
    (q : Ideal A) [q.IsPrime] :
    IsReduced (Localization.AtPrime q) := by
  letI : Algebra.IsStandardSmooth K A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  obtain ⟨g, hg⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial 1 K A
  let P := MvPolynomial (Fin 1) K
  letI : IsPrincipalIdealRing P := IsPrincipalIdealRing.of_surjective
    (MvPolynomial.uniqueAlgEquiv K (Fin 1)).symm.toRingHom
    (MvPolynomial.uniqueAlgEquiv K (Fin 1)).symm.surjective
  letI : Algebra P A := g.toRingHom.toAlgebra
  haveI : Algebra.Etale P A := by
    rw [← RingHom.etale_algebraMap]
    exact hg
  let p : Ideal P := q.under P
  letI : p.IsPrime := Ideal.IsPrime.comap g.toRingHom
  have hpq : q.LiesOver p := by
    rw [Ideal.liesOver_iff]
  letI : q.LiesOver p := hpq
  let R := Localization.AtPrime p
  let S := Localization.AtPrime q
  letI : Algebra R S := Localization.AtPrime.algebraOfLiesOver p q
  letI : Localization.AtPrime.IsLiesOverAlgebra p q := inferInstance
  haveI : Algebra.IsUnramifiedAt P q := inferInstance
  haveI : Algebra.FormallyUnramified R S := inferInstance
  haveI : Algebra.EssFiniteType R S := .of_comp P _ _
  have hm : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S :=
    Algebra.FormallyUnramified.map_maximalIdeal
  have hmRPrincipal : (maximalIdeal R).IsPrincipal := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p]
    exact (IsPrincipalIdealRing.principal p).map_ringHom _
  obtain ⟨r, hr⟩ := hmRPrincipal
  by_cases hr0 : r = 0
  · have hmR : maximalIdeal R = ⊥ := by
      rw [hr, hr0, Ideal.span_singleton_eq_bot]
    have hmS : maximalIdeal S = ⊥ := by
      rw [← hm, hmR, Ideal.map_bot]
    refine ⟨fun x hx ↦ ?_⟩
    have hxM : x ∈ maximalIdeal S :=
      (nilpotent_iff_mem_prime.mp hx) (maximalIdeal S)
        (maximalIdeal.isMaximal S).isPrime
    rw [hmS] at hxM
    exact hxM
  · have hrRegular : IsSMulRegular S r := by
      apply IsSMulRegular.of_flat
      exact IsSMulRegular.of_ne_zero hr0
    refine ⟨fun x hx ↦ ?_⟩
    have hpow : ∀ n : ℕ, x ∈ (maximalIdeal S) ^ n := by
      intro n
      induction n generalizing x with
      | zero => simp
      | succ n ih =>
          have hxM : x ∈ maximalIdeal S :=
            (nilpotent_iff_mem_prime.mp hx) (maximalIdeal S)
              (maximalIdeal.isMaximal S).isPrime
          have hxMap : x ∈ (Ideal.span {r}).map (algebraMap R S) := by
            have hxMap' : x ∈ (maximalIdeal R).map (algebraMap R S) := by
              rw [hm]
              exact hxM
            rw [hr] at hxMap'
            exact hxMap'
          rw [Ideal.map_span, Set.image_singleton,
            Ideal.mem_span_singleton] at hxMap
          obtain ⟨y, hy⟩ := hxMap
          have hxy : x = r • y := by
            simpa only [Algebra.smul_def] using hy
          have hyNil : IsNilpotent y := by
            obtain ⟨N, hN⟩ := hx
            refine ⟨N, ?_⟩
            apply (IsSMulRegular.pow N hrRegular).right_eq_zero_of_smul
            rw [← smul_pow, ← hxy]
            exact hN
          rw [hxy, pow_succ']
          change (algebraMap R S r) * y ∈
            maximalIdeal S * (maximalIdeal S) ^ n
          refine Ideal.mul_mem_mul ?_ (ih y hyNil)
          rw [← hm]
          apply Ideal.mem_map_of_mem (algebraMap R S)
          rw [hr]
          exact Ideal.mem_span_singleton_self r
    have hxInf : x ∈ ⨅ n : ℕ, (maximalIdeal S) ^ n := by
      simpa using hpow
    have hintersection : (⨅ n : ℕ, (maximalIdeal S) ^ n) = ⊥ :=
      Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal S)
        (maximalIdeal.isMaximal S).ne_top
    rw [hintersection] at hxInf
    exact hxInf

/-- Any chosen localization at a prime of a standard-smooth relative curve
over a field is reduced.  This form applies directly to scheme stalks. -/
theorem isReduced_of_isLocalizationAtPrime_of_isStandardSmoothOfRelativeDimension_one
    (K : Type u) (A : Type v) (Aq : Type w)
    [Field K] [CommRing A] [Algebra K A]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 K A]
    [CommRing Aq] [Algebra A Aq]
    (q : Ideal A) [q.IsPrime] [IsLocalization.AtPrime Aq q] : IsReduced Aq := by
  letI : IsReduced (Localization.AtPrime q) :=
    localizationAtPrime_isReduced K A q
  let e : Localization.AtPrime q ≃ₐ[A] Aq :=
    IsLocalization.algEquiv q.primeCompl _ _
  exact isReduced_of_injective e.symm.toRingHom e.symm.injective

open CategoryTheory _root_.AlgebraicGeometry

/-- A scheme smooth of relative dimension one over a field is reduced. -/
theorem scheme_isReduced_of_smoothRelativeDimension_one
    (K : Type u) [Field K] (X : Scheme.{u})
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] : IsReduced X := by
  letI (x : X) : _root_.IsReduced (X.presheaf.stalk x) := by
    obtain ⟨U, hU, V, hV, hx, e, hstd⟩ :=
      SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
        (n := 1) (f := f) x
    have hfxU : f.base x ∈ U := e hx
    have hUtop : U = ⊤ := by
      apply top_unique
      intro y _
      simpa only [Subsingleton.elim y (f.base x)] using hfxU
    subst U
    letI : Nonempty V := ⟨⟨x, hx⟩⟩
    letI : Field Γ(Spec (.of K), ⊤) :=
      ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
        (Field.toIsField K)).toField
    letI : Algebra Γ(Spec (.of K), ⊤) Γ(X, V) :=
      (f.appLE ⊤ V e).hom.toAlgebra
    letI : Algebra.IsStandardSmoothOfRelativeDimension 1
        Γ(Spec (.of K), ⊤) Γ(X, V) := hstd.toAlgebra
    let q : Ideal Γ(X, V) := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
    letI : q.IsPrime := (hV.primeIdealOf ⟨x, hx⟩).isPrime
    letI : Algebra Γ(X, V) (X.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
    letI : IsLocalization.AtPrime (X.presheaf.stalk x) q :=
      hV.isLocalization_stalk ⟨x, hx⟩
    exact
      isReduced_of_isLocalizationAtPrime_of_isStandardSmoothOfRelativeDimension_one
        Γ(Spec (.of K), ⊤) Γ(X, V) (X.presheaf.stalk x) q
  exact isReduced_of_isReduced_stalk X

/-- Smoothness of relative dimension one over a field remains reduced after
every field extension. -/
theorem geometricallyReduced_of_smoothRelativeDimension_one
    (K : Type u) [Field K] (X : Scheme.{u})
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] :
    GeometricallyReduced f := by
  rw [geometricallyReduced_iff]
  intro L _ y Z fst snd h
  letI : SmoothOfRelativeDimension 1 snd :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback h
      inferInstance
  exact scheme_isReduced_of_smoothRelativeDimension_one L Z snd

/-- A geometrically irreducible scheme smooth of relative dimension one over
a field is integral. -/
theorem scheme_isIntegral_of_geometricallyIrreducible_of_smoothRelativeDimension_one
    (K : Type u) [Field K] (X : Scheme.{u})
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    [GeometricallyIrreducible f] : IsIntegral X := by
  letI : GeometricallyReduced f :=
    geometricallyReduced_of_smoothRelativeDimension_one K X f
  letI : GeometricallyIntegral f :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f
  exact GeometricallyIntegral.isIntegral_of_subsingleton f

end MazurTorsion.AlgebraicGeometry.Jacobian.SmoothCurveReduced
