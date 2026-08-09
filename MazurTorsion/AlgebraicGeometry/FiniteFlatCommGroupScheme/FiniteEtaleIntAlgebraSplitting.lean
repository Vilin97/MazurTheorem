/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.Away.Lemmas
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.LinearAlgebra.FreeModule.PID
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.ConstantPrimeFiniteEtaleIdempotentAction

/-!
# Sections of finite étale integer algebras

Every nonzero finite étale algebra over `ℤ` has an actual `ℤ`-algebra map back to `ℤ`.
Equivalently, every nonempty finite étale affine cover of `Spec ℤ` has a section.

The proof is an induction on module rank.  A domain factor is `ℤ` by the checked arithmetic
no-unramified-extension theorem.  Otherwise, the nontrivial idempotent descended from the
generic fibre splits off a nonzero finite étale quotient of strictly smaller rank.  Recursing
on that quotient and composing with the quotient map constructs the section.

This is an unconditional arithmetic-geometric input to constant-torsor triviality.  Turning an
arbitrary global Čech class for a represented constant group into its finite étale torsor
algebra is a separate effective-descent step and is not asserted here.
-/

noncomputable section

open scoped TensorProduct

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme.ConstantPrimeEtale

universe u

private theorem span_idempotent_ne_top
    {B : Type u} [CommRing B] {e : B}
    (he : IsIdempotentElem e) (he1 : e ≠ 1) :
    Ideal.span ({e} : Set B) ≠ ⊤ := by
  rw [ne_eq, Ideal.span_singleton_eq_top]
  intro hunit
  exact he1 ((IsIdempotentElem.iff_eq_one_of_isUnit hunit).mp he)

private theorem exists_intAlgHom_of_finrank_eq (n : ℕ) :
    ∀ (B : Type u) [CommRing B] [Module.Finite ℤ B] [Algebra.Etale ℤ B],
      Module.finrank ℤ B = n → 0 < n → Nonempty (B →ₐ[ℤ] ℤ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro B _ _ _ hrank hn
      letI : Nontrivial B := Module.nontrivial_of_finrank_pos (R := ℤ) (hrank ▸ hn)
      by_cases hdomain : IsDomain B
      · letI : IsDomain B := hdomain
        exact ⟨(intAlgEquiv B).symm.toAlgHom⟩
      · obtain ⟨e, he, he0, he1⟩ :=
          exists_nontrivial_isIdempotentElem_of_not_isDomain B hdomain
        let Q := B ⧸ Ideal.span ({1 - e} : Set B)
        let Q' := B ⧸ Ideal.span ({e} : Set B)
        have honeSub_ne_one : 1 - e ≠ 1 := by
          intro h
          apply he0
          exact sub_eq_zero.mp (by simpa using h)
        letI : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr
          (span_idempotent_ne_top he.one_sub honeSub_ne_one)
        letI : Nontrivial Q' := Ideal.Quotient.nontrivial_iff.mpr
          (span_idempotent_ne_top he he1)
        let hQFinite : Module.Finite ℤ Q :=
          Module.Finite.quotient ℤ (Ideal.span ({1 - e} : Set B))
        let hQ'Finite : Module.Finite ℤ Q' :=
          Module.Finite.quotient ℤ (Ideal.span ({e} : Set B))
        letI : Module.Finite ℤ Q := hQFinite
        letI : Module.Finite ℤ Q' := hQ'Finite
        letI : IsLocalization.Away e Q :=
          IsLocalization.Away.quotient_of_isIdempotentElem he
        letI : Algebra.Etale B Q := Algebra.Etale.of_isLocalizationAway e
        let hQEtale : Algebra.Etale ℤ Q := Algebra.Etale.comp ℤ B Q
        letI : Algebra.Etale ℤ Q := hQEtale
        letI : IsLocalization.Away (1 - e) Q' := by
          apply IsLocalization.away_of_isIdempotentElem he.one_sub
          · change RingHom.ker
                (Ideal.Quotient.mk (Ideal.span ({e} : Set B))) =
              Ideal.span ({1 - (1 - e)} : Set B)
            rw [Ideal.mk_ker, sub_sub_cancel]
          · exact Ideal.Quotient.mk_surjective
        letI : Algebra.Etale B Q' := Algebra.Etale.of_isLocalizationAway (1 - e)
        let hQ'Etale : Algebra.Etale ℤ Q' := Algebra.Etale.comp ℤ B Q'
        letI : Algebra.Etale ℤ Q' := hQ'Etale
        letI : Module.Flat ℤ Q := Algebra.Smooth.flat ℤ Q
        letI : Module.Flat ℤ Q' := Algebra.Smooth.flat ℤ Q'
        letI : Module.IsTorsionFree ℤ Q := Module.Flat.isTorsionFree
        letI : Module.IsTorsionFree ℤ Q' := Module.Flat.isTorsionFree
        letI : Module.Free ℤ Q := Module.free_of_finite_type_torsion_free'
        letI : Module.Free ℤ Q' := Module.free_of_finite_type_torsion_free'
        have hQpos : 0 < Module.finrank ℤ Q := Module.finrank_pos
        have hQ'pos : 0 < Module.finrank ℤ Q' := Module.finrank_pos
        let split : B ≃ₐ[ℤ] Q' × Q :=
          AlgEquiv.prodQuotientOfIsIdempotentElem ℤ he he.one_sub
            (by simp) (by simp [he])
        have hsum : n = Module.finrank ℤ Q' + Module.finrank ℤ Q := by
          calc
            n = Module.finrank ℤ B := hrank.symm
            _ = Module.finrank ℤ (Q' × Q) := split.toLinearEquiv.finrank_eq
            _ = Module.finrank ℤ Q' + Module.finrank ℤ Q :=
              Module.finrank_prod (R := ℤ) (M := Q') (M' := Q)
        have hQlt : Module.finrank ℤ Q < n := by
          rw [hsum]
          exact Nat.lt_add_of_pos_left hQ'pos
        have hrec : Nonempty (Q →ₐ[ℤ] ℤ) :=
          @ih (Module.finrank ℤ Q) hQlt Q inferInstance hQFinite hQEtale rfl hQpos
        obtain ⟨f⟩ := hrec
        exact ⟨f.comp (Ideal.Quotient.mkₐ ℤ (Ideal.span ({1 - e} : Set B)))⟩

/-- Every positive-rank finite étale `ℤ`-algebra has an actual `ℤ`-algebra map to `ℤ`.
On affine spectra, this is a section of the structural finite étale morphism. -/
theorem exists_intAlgHom
    (B : Type u) [CommRing B] [Module.Finite ℤ B] [Algebra.Etale ℤ B]
    (hB : 0 < Module.finrank ℤ B) :
    Nonempty (B →ₐ[ℤ] ℤ) :=
  exists_intAlgHom_of_finrank_eq (Module.finrank ℤ B) B rfl hB

/-- A rank-five finite étale `ℤ`-algebra has an actual integral section. -/
theorem exists_intAlgHom_of_finrank_eq_five
    (B : Type u) [CommRing B] [Module.Finite ℤ B] [Algebra.Etale ℤ B]
    (hrank : Module.finrank ℤ B = 5) :
    Nonempty (B →ₐ[ℤ] ℤ) :=
  exists_intAlgHom B (by simp [hrank])

/-- A rank-eleven finite étale `ℤ`-algebra has an actual integral section. -/
theorem exists_intAlgHom_of_finrank_eq_eleven
    (B : Type u) [CommRing B] [Module.Finite ℤ B] [Algebra.Etale ℤ B]
    (hrank : Module.finrank ℤ B = 11) :
    Nonempty (B →ₐ[ℤ] ℤ) :=
  exists_intAlgHom B (by simp [hrank])

end AlgebraicGeometry.FiniteFlatCommGroupScheme.ConstantPrimeEtale
