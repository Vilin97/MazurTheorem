/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Vasily Ilin
-/
module

public import MazurTorsion.Upstream.AINTLIB.FltRegular.NumberTheory.Unramified
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.NumberTheory.NumberField.ClassNumber
import MazurTorsion.Upstream.AINTLIB.FltRegular.NumberTheory.Hilbert92
import MazurTorsion.Upstream.AINTLIB.FltRegular.NumberTheory.RegularPrimes
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Algebra.Field.Shrink
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RingTheory.Finiteness.Small

@[expose] public section

open scoped NumberField

universe u

variable {K : Type} {p : ℕ} [hpri : Fact p.Prime] [Field K]

open Polynomial Module

variable {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L]
  (σ : L ≃ₐ[K] L) (hσ : ∀ x, x ∈ Subgroup.zpowers σ) (hKL : finrank K L = p)

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra A L] [Algebra A K]
    [Algebra B L] [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing A K]
    [IsIntegralClosure B A L]

instance : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L

include hσ in
lemma comap_span_galRestrict_eq_of_cyclic (β : B) (η : Bˣ)
    (hβ : η * (galRestrict A K L B σ) β = β) (σ' : L ≃ₐ[K] L) :
    (Ideal.span {β}).comap (galRestrict A K L B σ') = Ideal.span {β} := by
  suffices (Ideal.span {β}).map
      (galRestrict A K L B σ'⁻¹).toRingEquiv.toRingHom = Ideal.span {β} by
    rwa [RingEquiv.toRingHom_eq_coe, Ideal.map_comap_of_equiv, map_inv] at this
  apply_fun (Ideal.span {·}) at hβ
  rw [← Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_eq_top.mpr η.isUnit,
    ← Ideal.one_eq_top, one_mul, ← Set.image_singleton, ← Ideal.map_span] at hβ
  change Ideal.map (galRestrict A K L B σ : B →+* B) _ = _ at hβ
  generalize σ'⁻¹ = σ'
  obtain ⟨n, rfl : σ ^ n = σ'⟩ := mem_powers_iff_mem_zpowers.mpr (hσ σ')
  rw [map_pow]
  induction n with
  | zero =>
    simp only [pow_zero, RingEquiv.toRingHom_eq_coe]
    exact Ideal.map_id _
  | succ n IH =>
    simp only [RingEquiv.toRingHom_eq_coe, pow_succ] at IH ⊢
    conv_lhs at IH => rw [← hβ, Ideal.map_map]
    exact IH

variable [IsGalois K L]

/-- Universe-polymorphic Hilbert 90 when the base field is small.  The
cohomological Hilbert 90 theorem in the pinned Mathlib revision requires both
fields to live in `Type`; shrinking the finite extension removes that
implementation restriction without changing the field. -/
private lemma exists_div_of_norm_eq_one_of_small [IsCyclic (L ≃ₐ[K] L)]
    {g : L ≃ₐ[K] L} (hg : ∀ x, x ∈ Subgroup.zpowers g) {x : L}
    (hx : Algebra.norm K x = 1) : ∃ y : Lˣ, y / g y = x := by
  letI : Small.{0} L := Module.Finite.small K L
  let e : Shrink.{0} L ≃ₐ[K] L := Shrink.algEquiv K L
  letI : IsGalois K (Shrink.{0} L) := IsGalois.of_algEquiv e.symm
  let gs : Shrink.{0} L ≃ₐ[K] Shrink.{0} L := e.autCongr.symm g
  have hgs : ∀ τ, τ ∈ Subgroup.zpowers gs := by
    intro τ
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg (e.autCongr τ))
    apply Subgroup.mem_zpowers_iff.mpr
    refine ⟨n, ?_⟩
    apply e.autCongr.injective
    rw [map_zpow, MulEquiv.apply_symm_apply]
    exact hn
  letI : IsCyclic (Shrink.{0} L ≃ₐ[K] Shrink.{0} L) :=
    isCyclic_iff_exists_zpowers_eq_top.mpr
      ⟨gs, (Subgroup.eq_top_iff' _).mpr hgs⟩
  have hx' : Algebra.norm K (e.symm x) = 1 := by
    rw [← Algebra.norm_eq_of_algEquiv e]
    simpa [e] using hx
  obtain ⟨y, hy⟩ := groupCohomology.exists_div_of_norm_eq_one hgs hx'
  let y' : Lˣ := Units.map e.toRingEquiv.toRingHom y
  refine ⟨y', ?_⟩
  apply e.symm.injective
  simpa [y', gs] using hy

/-- Universe-polymorphic integral Hilbert 90 over a small base field. -/
private lemma exists_mul_galRestrict_of_norm_eq_one_of_small [IsCyclic (L ≃ₐ[K] L)]
    [IsDomain A] {g : L ≃ₐ[K] L} (hg : ∀ x, x ∈ Subgroup.zpowers g) {η : B}
    (hη : Algebra.norm K (algebraMap B L η) = 1) :
    ∃ ε : B, ε ≠ 0 ∧ η * galRestrict A K L B g ε = ε := by
  have : Module.IsTorsionFree A L := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L :=
    IsIntegralClosure.isLocalization A K L B
  let η' : Lˣ := Units.mk0 (algebraMap B L η) (fun h ↦ by simp [h] at hη)
  obtain ⟨ε, hε⟩ := exists_div_of_norm_eq_one_of_small hg hη
  obtain ⟨a, b, h⟩ :=
    IsLocalization.exists_mk'_eq (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) ε.1
  obtain ⟨t, ht, ht'⟩ := b.prop
  have : t • IsLocalization.mk' L a b = algebraMap _ _ a := by
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply A B L, ht', IsLocalization.mk'_spec']
  refine ⟨a, ?_, ?_⟩
  · rintro rfl
    simp only [IsLocalization.mk'_zero, _root_.map_zero, div_zero, ← h] at hε
    rw [← hε, Algebra.norm_zero] at hη
    exact zero_ne_one hη
  · replace hε := hε.symm
    rw [← h, eq_div_iff_mul_eq] at hε
    · replace hε := congr_arg (t • ·) hε
      rw [Algebra.smul_def, mul_left_comm, ← Algebra.smul_def t, ← g.toAlgHom_apply,
        ← AlgHom.map_smul_of_tower, this] at hε
      apply IsIntegralClosure.algebraMap_injective B A L
      rw [map_mul, ← hε]
      congr 1
      exact algebraMap_galRestrictHom_apply A K L B g a
    · intro hzero
      rw [(map_eq_zero _).mp hzero, zero_div] at hε
      rw [hε, Algebra.norm_zero] at hη
      exact zero_ne_one hη

include hσ in
open FiniteDimensional in
theorem exists_not_isPrincipal_and_isPrincipal_map_aux
    [IsDedekindDomain A] [Algebra.Unramified A B] (η : Bˣ)
    (hη : Algebra.norm K (algebraMap B L η) = 1)
    (hη' : ¬∃ α : Bˣ, algebraMap B L η = (algebraMap B L α) / σ (algebraMap B L α)) :
    ∃ I : Ideal A, ¬I.IsPrincipal ∧ (I.map (algebraMap A B)).IsPrincipal := by
  have := isCyclic_iff_exists_zpowers_eq_top.2 ⟨σ, (Subgroup.eq_top_iff' _).2 hσ⟩
  obtain ⟨β, hβ_zero, hβ⟩ := exists_mul_galRestrict_of_norm_eq_one_of_small (A := A)
    (B := B) hσ hη
  haveI : IsDomain B :=
    (IsIntegralClosure.equiv A B L (integralClosure A L)).toMulEquiv.isDomain (integralClosure A L)
  have hβ' := comap_map_eq_of_unramified K L _
    (comap_span_galRestrict_eq_of_cyclic σ hσ (A := A) (B := B) β η hβ)
  refine ⟨(Ideal.span {β}).comap (algebraMap A B), ?_, ?_⟩
  · rintro ⟨⟨γ, hγ : _ = Ideal.span _⟩⟩
    rw [hγ, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_span_singleton] at hβ'
    obtain ⟨a, rfl⟩ := hβ'
    rw [map_mul, AlgEquiv.commutes, mul_left_comm, (mul_right_injective₀ _).eq_iff] at hβ
    · apply hη'
      use a
      conv_rhs => enter [1]; rw [← hβ]
      rw [map_mul, ← algebraMap_galRestrict_apply A]
      refine (mul_div_cancel_right₀ _ ?_).symm
      · rw [ne_eq,
          (injective_iff_map_eq_zero' _).mp (IsIntegralClosure.algebraMap_injective B A L),
          (injective_iff_map_eq_zero' _).mp (galRestrict A K L B σ).injective]
        exact a.isUnit.ne_zero
    · exact (mul_ne_zero_iff.mp hβ_zero).1
  · rw [hβ']
    exact ⟨⟨_, rfl⟩⟩

theorem Ideal.isPrincipal_pow_finrank_of_isPrincipal_map [IsDedekindDomain A] {I : Ideal A}
    (hI : (I.map (algebraMap A B)).IsPrincipal) : (I ^ finrank K L).IsPrincipal := by
  haveI : IsDomain B :=
    (IsIntegralClosure.equiv A B L (integralClosure A L)).toMulEquiv.isDomain (integralClosure A L)
  haveI := IsIntegralClosure.isNoetherian A K L B
  haveI := IsIntegralClosure.isDedekindDomain A K L B
  haveI := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  have hAB : Function.Injective (algebraMap A B) := by
    refine Function.Injective.of_comp (f := algebraMap B L) ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective _ _)
  rw [← Module.isTorsionFree_iff_algebraMap_injective] at hAB
  letI : Algebra (FractionRing A) (FractionRing B) := FractionRing.liftAlgebra _ _
  have : IsScalarTower A (FractionRing A) (FractionRing B) :=
    FractionRing.isScalarTower_liftAlgebra _ _
  have H : RingHom.comp (algebraMap (FractionRing A) (FractionRing B))
    (FractionRing.algEquiv A K).symm.toRingEquiv =
      RingHom.comp (FractionRing.algEquiv B L).symm.toRingEquiv (algebraMap K L) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors A)
    ext
    simp only [RingHom.coe_comp, RingHom.coe_coe, AlgEquiv.coe_ringEquiv, Function.comp_apply,
      AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply A B L, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  have : Algebra.IsSeparable (FractionRing A) (FractionRing B) :=
    Algebra.IsSeparable.of_equiv_equiv _ _ H
  have hLK : finrank (FractionRing A) (FractionRing B) = finrank K L := by
    simpa only [Cardinal.toNat_lift] using! congr_arg Cardinal.toNat
      (Algebra.lift_rank_eq_of_equiv_equiv (FractionRing.algEquiv A K).symm.toRingEquiv
        (FractionRing.algEquiv B L).symm.toRingEquiv H).symm
  rw [← hLK, ← Ideal.relNorm_algebraMap, ← (I.map (algebraMap A B)).span_singleton_generator,
    Ideal.relNorm_singleton]
  exact ⟨⟨_, rfl⟩⟩

/-- This is the first part of **Hilbert Theorem 94**, which states that if `L/K` is an unramified
  cyclic finite extension of number fields of odd prime degree,
  then there is an ideal of `K` that capitulates in `L`. -/
theorem exists_not_isPrincipal_and_isPrincipal_map (K : Type) (L : Type u)
    [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Algebra.Unramified (𝓞 K) (𝓞 L)]
    [h : IsCyclic (L ≃ₐ[K] L)]
    (hKL : Nat.Prime (finrank K L))
    (hKL' : finrank K L ≠ 2) :
    ∃ I : Ideal (𝓞 K), ¬I.IsPrincipal ∧
      (I.map (algebraMap (𝓞 K) (𝓞 L))).IsPrincipal := by
  obtain ⟨⟨σ, hσ⟩⟩ := h
  obtain ⟨η, hη, hη'⟩ := Hilbert92 hKL hKL' σ hσ
  exact exists_not_isPrincipal_and_isPrincipal_map_aux σ hσ η hη (not_exists.mpr hη')

/-- This is the second part of **Hilbert Theorem 94**, which states that if `L/K` is an unramified
  cyclic finite extension of number fields of odd prime degree,
  then the degree divides the class number of `K`. -/
theorem dvd_card_classGroup_of_unramified_isCyclic {K : Type} {L : Type u}
    [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Algebra.Unramified (𝓞 K) (𝓞 L)]
    [IsCyclic (L ≃ₐ[K] L)]
    (hKL : Nat.Prime (finrank K L))
    (hKL' : finrank K L ≠ 2) :
    finrank K L ∣ Fintype.card (ClassGroup (𝓞 K)) := by
  obtain ⟨I, hI, hI'⟩ := exists_not_isPrincipal_and_isPrincipal_map K L hKL hKL'
  have := Fact.mk hKL
  rw [hKL.dvd_iff_not_coprime]
  exact fun h ↦ hI (isPrincipal_of_isPrincipal_pow_of_coprime h
    (Ideal.isPrincipal_pow_finrank_of_isPrincipal_map hI'))
