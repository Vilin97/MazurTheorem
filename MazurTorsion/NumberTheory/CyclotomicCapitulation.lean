/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.CyclotomicHilbert94
import Mathlib.RingTheory.ClassGroup.ExtendedHom

/-!
# Equivariant capitulation for inverse-cyclotomic extensions

This module refines the Hilbert-94 class-number obstruction by exposing the
capitulation map itself.  Extension of ideals commutes with the cyclotomic
action on the base and the chosen lifted action on the extension field.
Consequently, the capitulation kernel is cyclotomic-Galois stable.

For an everywhere finite-place unramified inverse extension of odd prime
degree, the kernel is nontrivial and every one of its elements has exponent
dividing the extension degree.  This is the strongest honest equivariant
consequence of Hilbert 94 used here.  It does not identify the kernel with an
inverse-cyclotomic quotient; that further assertion is global
class-field-theory content.
-/

open scoped NumberField nonZeroDivisors

namespace NumberTheory.CyclotomicCharacter.InverseExtension

universe u

variable {p : ℕ} [Fact p.Prime]
variable {L : Type u} [Field L] [NumberField L]
variable [Algebra (PrimeCyclotomicField p) L]
variable [IsScalarTower ℚ (PrimeCyclotomicField p) L]

/-- Extension of ideals from the cyclotomic base to the inverse extension,
on ordinary ideal class groups. -/
noncomputable def capitulationHom (_E : InverseExtension p L) :
    ClassGroup (NumberField.RingOfIntegers (PrimeCyclotomicField p)) →*
      ClassGroup (NumberField.RingOfIntegers L) :=
  ClassGroup.extendedHom
    (NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (NumberField.RingOfIntegers L)

/-- The class-group automorphism of the extension field induced by the
chosen lift of a cyclotomic Galois automorphism. -/
noncomputable def upperClassGroupAutomorphism (E : InverseExtension p L)
    (σ : Gal(PrimeCyclotomicField p/ℚ)) :
    ClassGroup (NumberField.RingOfIntegers L) ≃*
      ClassGroup (NumberField.RingOfIntegers L) :=
  NumberTheory.UnramifiedArtin.classGroupEquiv
    (NumberField.RingOfIntegers L) L (E.liftIntegerEquiv σ)

private noncomputable def mapIdeal0
    {R : Type*} [CommRing R] [IsDomain R]
    (g : R ≃+* R) (I : (Ideal R)⁰) : (Ideal R)⁰ :=
  ⟨I.1.map g, mem_nonZeroDivisors_iff_ne_zero.mpr <|
    (Ideal.map_eq_bot_iff_of_injective g.injective).not.mpr <|
      mem_nonZeroDivisors_iff_ne_zero.mp I.2⟩

private theorem classGroupEquiv_mk0
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (g : R ≃+* R) (I : (Ideal R)⁰) :
    NumberTheory.UnramifiedArtin.classGroupEquiv R K g (ClassGroup.mk0 I) =
      ClassGroup.mk0 (mapIdeal0 g I) := by
  rw [← ClassGroup.mk_mk0 K,
    NumberTheory.UnramifiedArtin.classGroupEquiv_mk,
    ← ClassGroup.mk_mk0 K]
  congr 1
  apply Units.ext
  exact NumberTheory.UnramifiedArtin.ringEquivOfRingEquiv_coeIdeal R K g I.1

private theorem mapIdeal0_extendedIdeal
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] [Module.IsTorsionFree R S]
    (g : R ≃+* R) (h : S ≃+* S)
    (hsemilinear : ∀ r : R, h (algebraMap R S r) = algebraMap R S (g r))
    (I : (Ideal R)⁰) :
    mapIdeal0 h (ClassGroup.extendedIdeal R S I) =
      ClassGroup.extendedIdeal R S (mapIdeal0 g I) := by
  apply Subtype.ext
  change Ideal.map h.toRingHom (Ideal.map (algebraMap R S) I.1) =
    Ideal.map (algebraMap R S) (Ideal.map g.toRingHom I.1)
  rw [Ideal.map_map (algebraMap R S) h.toRingHom,
    Ideal.map_map g.toRingHom (algebraMap R S)]
  congr 1
  ext r
  exact hsemilinear r

/-- Capitulation is equivariant for the cyclotomic action and the chosen
lifted action on the extension field. -/
theorem capitulationHom_equivariant
    (E : InverseExtension p L)
    (σ : Gal(PrimeCyclotomicField p/ℚ))
    (c : ClassGroup
      (NumberField.RingOfIntegers (PrimeCyclotomicField p))) :
    E.capitulationHom (classGroupAutomorphism p σ c) =
      E.upperClassGroupAutomorphism σ (E.capitulationHom c) := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  simp only [classGroupAutomorphism, upperClassGroupAutomorphism,
    capitulationHom, classGroupEquiv_mk0, ClassGroup.extendedHom_mk0]
  congr 1
  exact (mapIdeal0_extendedIdeal
    (baseIntegerEquiv σ) (E.liftIntegerEquiv σ)
    (E.liftIntegerEquiv_algebraMap σ) I).symm

/-- The subgroup of ideal classes that become principal in the extension. -/
noncomputable abbrev capitulationKernel (E : InverseExtension p L) :
    Subgroup (ClassGroup
      (NumberField.RingOfIntegers (PrimeCyclotomicField p))) :=
  E.capitulationHom.ker

/-- The capitulation kernel is stable under every cyclotomic Galois
automorphism. -/
theorem capitulationKernel_stable
    (E : InverseExtension p L)
    (σ : Gal(PrimeCyclotomicField p/ℚ))
    {c : ClassGroup
      (NumberField.RingOfIntegers (PrimeCyclotomicField p))}
    (hc : c ∈ E.capitulationKernel) :
    classGroupAutomorphism p σ c ∈ E.capitulationKernel := by
  rw [MonoidHom.mem_ker] at hc ⊢
  rw [E.capitulationHom_equivariant σ c, hc, map_one]

/-- Hilbert 94 gives a nontrivial ideal class that capitulates in an
everywhere finite-place unramified inverse extension. -/
theorem exists_nontrivial_capitulating_class
    (hp : 2 < p) (E : InverseExtension p L)
    (hunramified : E.IsUnramifiedAtFinitePlaces) :
    ∃ c : ClassGroup
        (NumberField.RingOfIntegers (PrimeCyclotomicField p)),
      c ≠ 1 ∧ E.capitulationHom c = 1 := by
  let K := PrimeCyclotomicField p
  let R := NumberField.RingOfIntegers K
  let S := NumberField.RingOfIntegers L
  letI : IsGalois K L := E.isGalois
  letI : Algebra.Unramified R S :=
    E.algebraUnramified_iff_isUnramifiedAtFinitePlaces.mpr hunramified
  letI : IsCyclic Gal(L/K) :=
    isCyclic_of_surjective E.galEquiv.symm.toMonoidHom
      E.galEquiv.symm.surjective
  have hfinrank : Module.finrank K L = p := by
    calc
      Module.finrank K L = Nat.card Gal(L/K) :=
        (IsGalois.card_aut_eq_finrank K L).symm
      _ = Nat.card (Multiplicative (ZMod p)) :=
        Nat.card_congr E.galEquiv.toEquiv
      _ = p := by simp
  have hprime : Nat.Prime (Module.finrank K L) := by
    rw [hfinrank]
    exact Fact.out
  have hne_two : Module.finrank K L ≠ 2 := by
    rw [hfinrank]
    omega
  obtain ⟨I, hI, hImap⟩ :=
    exists_not_isPrincipal_and_isPrincipal_map K L hprime hne_two
  have hIzero : I ≠ 0 := fun hzero => hI (hzero ▸ bot_isPrincipal)
  let I0 : (Ideal R)⁰ :=
    ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hIzero⟩
  refine ⟨ClassGroup.mk0 I0, ?_, ?_⟩
  · intro hc
    apply hI
    exact (ClassGroup.mk0_eq_one_iff I0.prop).mp hc
  · rw [capitulationHom, ClassGroup.extendedHom_mk0]
    exact (ClassGroup.mk0_eq_one_iff
      (ClassGroup.extendedIdeal R S I0).prop).mpr hImap

/-- Every capitulating class has exponent dividing the prime extension
degree. -/
theorem capitulating_class_pow_eq_one
    (E : InverseExtension p L)
    (c : ClassGroup
      (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
    (hc : E.capitulationHom c = 1) :
    c ^ p = 1 := by
  let K := PrimeCyclotomicField p
  let R := NumberField.RingOfIntegers K
  let S := NumberField.RingOfIntegers L
  letI : IsGalois K L := E.isGalois
  have hfinrank : Module.finrank K L = p := by
    calc
      Module.finrank K L = Nat.card Gal(L/K) :=
        (IsGalois.card_aut_eq_finrank K L).symm
      _ = Nat.card (Multiplicative (ZMod p)) :=
        Nat.card_congr E.galEquiv.toEquiv
      _ = p := by simp
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  have hc' : ClassGroup.mk0 (ClassGroup.extendedIdeal R S I) = 1 := by
    simpa only [capitulationHom, ClassGroup.extendedHom_mk0] using hc
  have hmap : (I.1.map (algebraMap R S)).IsPrincipal :=
    (ClassGroup.mk0_eq_one_iff
      (ClassGroup.extendedIdeal R S I).prop).mp hc'
  have hpow : (I.1 ^ Module.finrank K L).IsPrincipal :=
    Ideal.isPrincipal_pow_finrank_of_isPrincipal_map hmap
  rw [← map_pow]
  apply (ClassGroup.mk0_eq_one_iff (I ^ p).prop).mpr
  change (I.1 ^ p).IsPrincipal
  rwa [hfinrank] at hpow

/-- Under the Hilbert-94 hypotheses, the capitulation kernel is a nonzero
cyclotomic-Galois-stable subgroup. -/
theorem capitulationKernel_ne_bot
    (hp : 2 < p) (E : InverseExtension p L)
    (hunramified : E.IsUnramifiedAtFinitePlaces) :
    E.capitulationKernel ≠ ⊥ := by
  obtain ⟨c, hc, hcap⟩ :=
    E.exists_nontrivial_capitulating_class hp hunramified
  intro hbot
  apply hc
  have hmem : c ∈ E.capitulationKernel := MonoidHom.mem_ker.mpr hcap
  rw [hbot] at hmem
  exact hmem

/-- Every element of the capitulation kernel is killed by the prime
extension degree. -/
theorem capitulationKernel_pow_eq_one
    (E : InverseExtension p L)
    (c : E.capitulationKernel) :
    (c.1 : ClassGroup
      (NumberField.RingOfIntegers (PrimeCyclotomicField p))) ^ p = 1 :=
  E.capitulating_class_pow_eq_one c.1 (MonoidHom.mem_ker.mp c.2)

/-- A single downstream-friendly package of the checked equivariant
Hilbert-94 conclusion: a nontrivial exponent-`p` class whose entire
cyclotomic orbit capitulates. -/
theorem exists_nontrivial_p_torsion_capitulating_orbit
    (hp : 2 < p) (E : InverseExtension p L)
    (hunramified : E.IsUnramifiedAtFinitePlaces) :
    ∃ c : ClassGroup
        (NumberField.RingOfIntegers (PrimeCyclotomicField p)),
      c ≠ 1 ∧ c ^ p = 1 ∧
        ∀ σ : Gal(PrimeCyclotomicField p/ℚ),
          E.capitulationHom (classGroupAutomorphism p σ c) = 1 := by
  obtain ⟨c, hc, hcap⟩ :=
    E.exists_nontrivial_capitulating_class hp hunramified
  refine ⟨c, hc, E.capitulating_class_pow_eq_one c hcap, ?_⟩
  intro σ
  exact MonoidHom.mem_ker.mp
    (E.capitulationKernel_stable σ (MonoidHom.mem_ker.mpr hcap))

end NumberTheory.CyclotomicCharacter.InverseExtension
