/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.ConstantPrimeFiniteEtaleTorsorObstruction
import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.LocalRing.NonLocalRing
import Mathlib.RingTheory.Smooth.IntegralClosure

/-!
# Idempotents and prime-order actions on finite-étale torsor algebras

This file closes the algebraic step immediately after the arithmetic obstruction for a
constant-prime torsor algebra.  A non-domain finite étale algebra over `ℤ` really has a
nontrivial idempotent.  The proof first splits its reduced Artinian generic fibre and then
descends the resulting idempotent by smooth base change for integral closure.

We also construct the actual action on idempotents induced by a semiring action and prove that
an orbit under `Multiplicative (ZMod p)` has cardinality one or `p`.  If invariant idempotents
are trivial, the idempotent supplied by the finite-étale argument has an orbit of cardinality
`p`, with concrete order-five and order-eleven endpoints.

This still does not turn an arbitrary global Čech class into a finite-étale torsor algebra, nor
does it construct the torsor action or prove that its invariant idempotents are trivial.  Those
effective-descent and torsor-transitivity inputs remain explicit.
-/

noncomputable section

open scoped TensorProduct

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme.ConstantPrimeEtale

universe u v

/-- A non-domain finite étale algebra over `ℤ` has an actual nontrivial idempotent.

The key descent step is not a reducedness shortcut: the idempotent is constructed in the
reduced Artinian generic fibre and descended using the theorem that smooth base change commutes
with integral closure. -/
theorem exists_nontrivial_isIdempotentElem_of_not_isDomain
    (B : Type u) [CommRing B] [Nontrivial B] [Module.Finite ℤ B] [Algebra.Etale ℤ B]
    (hB : ¬ IsDomain B) :
    ∃ e : B, IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by
  classical
  let C := ℚ ⊗[ℤ] B
  have hinclude : Function.Injective
      (Algebra.TensorProduct.includeRight : B →ₐ[ℤ] C) :=
    Algebra.TensorProduct.includeRight_injective
      (RingHom.injective_int (algebraMap ℤ ℚ))
  letI : Nontrivial C := hinclude.nontrivial
  have hC : ¬ IsDomain C := by
    intro h
    letI : IsDomain C := h
    exact hB (hinclude.isDomain Algebra.TensorProduct.includeRight.toRingHom)
  haveI : IsReduced C :=
    Algebra.FormallyUnramified.isReduced_of_field ℚ C
  haveI : IsArtinianRing C := IsArtinianRing.of_finite ℚ C
  have hnotLocal : ¬ IsLocalRing C := by
    intro h
    letI : IsLocalRing C := h
    exact hC (IsField.isDomain (IsArtinianRing.isField_of_isReduced_of_isLocalRing C))
  letI : Nontrivial (MaximalSpectrum C) :=
    (IsLocalRing.not_isLocalRing_tfae.out 0 1).mp hnotLocal
  obtain ⟨m₀, m₁, hm⟩ := exists_pair_ne (MaximalSpectrum C)
  let E := IsArtinianRing.equivPi C
  let f : ∀ m : MaximalSpectrum C, C ⧸ m.asIdeal := Pi.single m₀ 1
  have hf : IsIdempotentElem f := by
    rw [IsIdempotentElem]
    ext m
    by_cases h : m = m₀
    · subst m
      simp [f]
    · simp [f, h]
  let eC : C := E.symm f
  have heC : IsIdempotentElem eC := hf.map E.symm
  have heC0 : eC ≠ 0 := by
    intro h
    have := congr_arg (fun x : C ↦ E x m₀) h
    simp [eC, f] at this
  have heC1 : eC ≠ 1 := by
    intro h
    have := congr_arg (fun x : C ↦ E x m₁) h
    simp [eC, f, hm.symm] at this
  let τ : C ≃ₐ[ℤ] B ⊗[ℤ] ℚ := Algebra.TensorProduct.comm ℤ ℚ B
  let eQ : B ⊗[ℤ] ℚ := τ eC
  have heQ : IsIdempotentElem eQ := heC.map τ
  have heQ0 : eQ ≠ 0 := by
    intro h
    apply heC0
    apply τ.injective
    simpa [eQ] using h
  have heQ1 : eQ ≠ 1 := by
    intro h
    apply heC1
    apply τ.injective
    simpa [eQ] using h
  have heQIntegral : IsIntegral B eQ := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub (by simp), ?_⟩
    simpa [pow_two] using sub_eq_zero.mpr heQ.eq
  let eIntegral : integralClosure B (B ⊗[ℤ] ℚ) := ⟨eQ, heQIntegral⟩
  obtain ⟨z, hz⟩ :=
    (TensorProduct.toIntegralClosure_bijective_of_smooth
      (R := ℤ) (S := B) (B := ℚ)).surjective eIntegral
  have hIntSurjective :
      Function.Surjective (algebraMap ℤ (integralClosure ℤ ℚ)) := by
    intro x
    obtain ⟨n, hn⟩ :=
      (IsIntegralClosure.equiv ℤ ℤ ℚ (integralClosure ℤ ℚ)).surjective x
    exact ⟨n, by simpa using hn⟩
  obtain ⟨e, rfl⟩ :=
    (Algebra.TensorProduct.includeLeft_surjective B B hIntSurjective) z
  have heMap :
      (Algebra.TensorProduct.includeLeft : B →ₐ[B] B ⊗[ℤ] ℚ) e = eQ := by
    have := congr_arg Subtype.val hz
    simpa [TensorProduct.toIntegralClosure, eIntegral] using this
  have hincludeLeft : Function.Injective
      (Algebra.TensorProduct.includeLeft : B →ₐ[B] B ⊗[ℤ] ℚ) :=
    Algebra.TensorProduct.includeLeft_injective
      (RingHom.injective_int (algebraMap ℤ ℚ))
  refine ⟨e, ?_, ?_, ?_⟩
  · apply hincludeLeft
    simp only [map_mul, heMap, heQ.eq]
  · intro h
    apply heQ0
    rw [← heMap, h, map_zero]
  · intro h
    apply heQ1
    rw [← heMap, h, map_one]

/-- A prime-rank finite étale `ℤ`-algebra has a nontrivial idempotent.  This consumes the
arithmetic no-domain theorem rather than assuming a connectedness certificate. -/
theorem exists_nontrivial_isIdempotentElem_of_finrank_eq_prime
    (B : Type u) [CommRing B] [Module.Finite ℤ B] [Algebra.Etale ℤ B]
    (p : ℕ) (hp : p.Prime) (hrank : Module.finrank ℤ B = p) :
    ∃ e : B, IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by
  letI : Nontrivial B := Module.nontrivial_of_finrank_pos (R := ℤ) (by simpa [hrank] using hp.pos)
  exact exists_nontrivial_isIdempotentElem_of_not_isDomain B
    (not_isDomain_of_finrank_eq_prime B p hp hrank)

/-- The subtype of idempotents of a semiring. -/
abbrev IdempotentElements (B : Type v) [Semiring B] := {e : B // IsIdempotentElem e}

/-- A multiplicative semiring action preserves idempotents and therefore induces an actual
action on the subtype of idempotent elements. -/
@[instance_reducible]
def idempotentMulAction (G : Type u) (B : Type v) [Monoid G] [Semiring B]
    [MulSemiringAction G B] : MulAction G (IdempotentElements B) where
  smul g e := ⟨g • (e : B), by
    rw [IsIdempotentElem, ← smul_mul', e.property]⟩
  one_smul e := Subtype.ext (one_smul G (e : B))
  mul_smul g h e := Subtype.ext (mul_smul g h (e : B))

/-- Every idempotent orbit under the constant group of prime order has cardinality one or the
prime. -/
theorem idempotent_orbit_ncard_eq_one_or_prime
    (B : Type v) [CommRing B] (p : ℕ) (hp : p.Prime)
    [MulSemiringAction (Multiplicative (ZMod p)) B]
    (e : IdempotentElements B) :
    letI := idempotentMulAction (Multiplicative (ZMod p)) B
    (MulAction.orbit (Multiplicative (ZMod p)) e).ncard = 1 ∨
      (MulAction.orbit (Multiplicative (ZMod p)) e).ncard = p := by
  letI := idempotentMulAction (Multiplicative (ZMod p)) B
  apply hp.eq_one_or_self_of_dvd
  rw [← MulAction.index_stabilizer]
  have hcard : Nat.card (Multiplicative (ZMod p)) = p :=
    (Nat.card_congr
      (Multiplicative.ofAdd : ZMod p ≃ Multiplicative (ZMod p))).trans (Nat.card_zmod p)
  have hdvd := (MulAction.stabilizer (Multiplicative (ZMod p)) e).index_dvd_card
  rw [hcard] at hdvd
  exact hdvd

/-- The only invariant idempotents for the given semiring action are zero and one.  This is the
exact algebraic transitivity input still required from a genuine torsor action. -/
def HasOnlyTrivialInvariantIdempotents
    (G : Type u) (B : Type v) [Monoid G] [Semiring B] [MulSemiringAction G B] : Prop :=
  ∀ e : IdempotentElements B, (∀ g : G, g • (e : B) = e) → e = 0 ∨ e = 1

/-- Under the actual invariant-idempotent condition, every nontrivial idempotent has a full
prime-order orbit. -/
theorem idempotent_orbit_ncard_eq_prime_of_nontrivial
    (B : Type v) [CommRing B] (p : ℕ) (hp : p.Prime)
    [MulSemiringAction (Multiplicative (ZMod p)) B]
    (hinv : HasOnlyTrivialInvariantIdempotents (Multiplicative (ZMod p)) B)
    (e : IdempotentElements B) (he0 : e ≠ 0) (he1 : e ≠ 1) :
    letI := idempotentMulAction (Multiplicative (ZMod p)) B
    (MulAction.orbit (Multiplicative (ZMod p)) e).ncard = p := by
  letI := idempotentMulAction (Multiplicative (ZMod p)) B
  rcases idempotent_orbit_ncard_eq_one_or_prime B p hp e with h | h
  · obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h
    have hs : (MulAction.orbit (Multiplicative (ZMod p)) e).Subsingleton := by
      rw [ha]
      exact Set.subsingleton_singleton
    have hfixed : e ∈ MulAction.fixedPoints (Multiplicative (ZMod p))
        (IdempotentElements B) :=
      MulAction.subsingleton_orbit_iff_mem_fixedPoints.mp hs
    have hfixedB : ∀ g : Multiplicative (ZMod p), g • (e : B) = e := fun g ↦
      congr_arg Subtype.val (hfixed g)
    rcases hinv e hfixedB with h0 | h1
    · exact (he0 h0).elim
    · exact (he1 h1).elim
  · exact h

/-- A prime-rank finite étale algebra with a genuine prime-order action has a nontrivial
idempotent with full orbit, once torsor transitivity is expressed by trivial invariants. -/
theorem exists_nontrivial_idempotent_with_orbit_ncard_eq_prime
    (B : Type u) [CommRing B] [Module.Finite ℤ B] [Algebra.Etale ℤ B]
    (p : ℕ) (hp : p.Prime) (hrank : Module.finrank ℤ B = p)
    [MulSemiringAction (Multiplicative (ZMod p)) B]
    (hinv : HasOnlyTrivialInvariantIdempotents (Multiplicative (ZMod p)) B) :
    ∃ e : IdempotentElements B, e ≠ 0 ∧ e ≠ 1 ∧
      (letI := idempotentMulAction (Multiplicative (ZMod p)) B
       (MulAction.orbit (Multiplicative (ZMod p)) e).ncard = p) := by
  obtain ⟨e, he, he0, he1⟩ :=
    exists_nontrivial_isIdempotentElem_of_finrank_eq_prime B p hp hrank
  let e' : IdempotentElements B := ⟨e, he⟩
  have he0' : e' ≠ 0 := by
    intro h
    exact he0 (congr_arg Subtype.val h)
  have he1' : e' ≠ 1 := by
    intro h
    exact he1 (congr_arg Subtype.val h)
  exact ⟨e', he0', he1',
    idempotent_orbit_ncard_eq_prime_of_nontrivial B p hp hinv e' he0' he1'⟩

/-- The genuine order-five endpoint of the finite-étale idempotent-orbit theorem. -/
theorem exists_nontrivial_idempotent_with_orbit_ncard_eq_five
    (B : Type u) [CommRing B] [Module.Finite ℤ B] [Algebra.Etale ℤ B]
    (hrank : Module.finrank ℤ B = 5)
    [MulSemiringAction (Multiplicative (ZMod 5)) B]
    (hinv : HasOnlyTrivialInvariantIdempotents (Multiplicative (ZMod 5)) B) :
    ∃ e : IdempotentElements B, e ≠ 0 ∧ e ≠ 1 ∧
      (letI := idempotentMulAction (Multiplicative (ZMod 5)) B
       (MulAction.orbit (Multiplicative (ZMod 5)) e).ncard = 5) :=
  exists_nontrivial_idempotent_with_orbit_ncard_eq_prime B 5 (by decide) hrank hinv

/-- The genuine order-eleven endpoint of the finite-étale idempotent-orbit theorem. -/
theorem exists_nontrivial_idempotent_with_orbit_ncard_eq_eleven
    (B : Type u) [CommRing B] [Module.Finite ℤ B] [Algebra.Etale ℤ B]
    (hrank : Module.finrank ℤ B = 11)
    [MulSemiringAction (Multiplicative (ZMod 11)) B]
    (hinv : HasOnlyTrivialInvariantIdempotents (Multiplicative (ZMod 11)) B) :
    ∃ e : IdempotentElements B, e ≠ 0 ∧ e ≠ 1 ∧
      (letI := idempotentMulAction (Multiplicative (ZMod 11)) B
       (MulAction.orbit (Multiplicative (ZMod 11)) e).ncard = 11) :=
  exists_nontrivial_idempotent_with_orbit_ncard_eq_prime B 11 (by decide) hrank hinv

end AlgebraicGeometry.FiniteFlatCommGroupScheme.ConstantPrimeEtale
