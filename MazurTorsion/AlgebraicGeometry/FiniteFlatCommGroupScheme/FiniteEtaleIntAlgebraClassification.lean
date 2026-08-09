/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Algebra.Algebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FiniteEtaleIntAlgebraSplitting

/-!
# Classification of finite étale integer algebras

Every module-finite étale `ℤ`-algebra is an actual finite product of copies of `ℤ`, indexed by
its module rank.  The proof strengthens the section theorem by carrying both idempotent factors
through a rank induction and reassembling their classifications along
`Fin m ⊕ Fin n ≃ Fin (m + n)`.

This is the unconditional arithmetic classification needed after effective descent produces a
finite étale constant-torsor algebra.  The construction of that algebra from an arbitrary
global represented-constant Čech class, and the comparison which trivializes the original
cocycle from a section, remain separate geometric steps and are not asserted here.
-/

noncomputable section

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme.ConstantPrimeEtale

universe u

/-- Functions on a disjoint union are the product of the two function algebras. -/
private def sumPiAlgEquivProdPi (α β : Type u) :
    ((α ⊕ β) → ℤ) ≃ₐ[ℤ] (α → ℤ) × (β → ℤ) where
  toFun f := (fun a ↦ f (Sum.inl a), fun b ↦ f (Sum.inr b))
  invFun f := Sum.elim f.1 f.2
  left_inv f := by
    ext x
    cases x <;> rfl
  right_inv f := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

private theorem span_idempotent_ne_top_of_ne_one
    {B : Type u} [CommRing B] {e : B}
    (he : IsIdempotentElem e) (he1 : e ≠ 1) :
    Ideal.span ({e} : Set B) ≠ ⊤ := by
  rw [ne_eq, Ideal.span_singleton_eq_top]
  intro hunit
  exact he1 ((IsIdempotentElem.iff_eq_one_of_isUnit hunit).mp he)

private theorem intAlgEquivPiFin_of_finrank_eq (n : ℕ) :
    ∀ (B : Type u) [CommRing B] [Module.Finite ℤ B] [Algebra.Etale ℤ B],
      Module.finrank ℤ B = n → Nonempty (B ≃ₐ[ℤ] (Fin n → ℤ)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro B _ _ _ hrank
      letI : Module.Flat ℤ B := Algebra.Smooth.flat ℤ B
      letI : Module.IsTorsionFree ℤ B := Module.Flat.isTorsionFree
      letI : Module.Free ℤ B := Module.free_of_finite_type_torsion_free'
      by_cases hn : n = 0
      · have hrank0 : Module.finrank ℤ B = 0 := hrank.trans hn
        letI : Subsingleton B :=
          (Module.finrank_eq_zero_iff_of_free ℤ B).mp hrank0
        rw [hn]
        exact ⟨default⟩
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        letI : Nontrivial B :=
          Module.nontrivial_of_finrank_pos (R := ℤ) (hrank ▸ hnpos)
        by_cases hdomain : IsDomain B
        · letI : IsDomain B := hdomain
          have hn1 : n = 1 := hrank.symm.trans (finrank_eq_one B)
          rw [hn1]
          exact ⟨(intAlgEquiv B).symm.trans
            (AlgEquiv.funUnique ℤ (Fin 1) ℤ).symm⟩
        · obtain ⟨e, he, he0, he1⟩ :=
            exists_nontrivial_isIdempotentElem_of_not_isDomain B hdomain
          let Q := B ⧸ Ideal.span ({1 - e} : Set B)
          let Q' := B ⧸ Ideal.span ({e} : Set B)
          have honeSub_ne_one : 1 - e ≠ 1 := by
            intro h
            apply he0
            exact sub_eq_zero.mp (by simpa using h)
          letI : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr
            (span_idempotent_ne_top_of_ne_one he.one_sub honeSub_ne_one)
          letI : Nontrivial Q' := Ideal.Quotient.nontrivial_iff.mpr
            (span_idempotent_ne_top_of_ne_one he he1)
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
          have hQ'lt : Module.finrank ℤ Q' < n := by
            rw [hsum]
            exact Nat.lt_add_of_pos_right hQpos
          let EQ : Q ≃ₐ[ℤ] (Fin (Module.finrank ℤ Q) → ℤ) :=
            (@ih (Module.finrank ℤ Q) hQlt Q inferInstance hQFinite hQEtale rfl).some
          let EQ' : Q' ≃ₐ[ℤ] (Fin (Module.finrank ℤ Q') → ℤ) :=
            (@ih (Module.finrank ℤ Q') hQ'lt Q' inferInstance hQ'Finite hQ'Etale rfl).some
          let reindex :
              ((Fin (Module.finrank ℤ Q') ⊕ Fin (Module.finrank ℤ Q)) → ℤ) ≃ₐ[ℤ]
                (Fin (Module.finrank ℤ Q' + Module.finrank ℤ Q) → ℤ) :=
            AlgEquiv.piCongrLeft ℤ
              (fun _ : Fin (Module.finrank ℤ Q' + Module.finrank ℤ Q) ↦ ℤ)
              finSumFinEquiv
          let E : B ≃ₐ[ℤ]
              (Fin (Module.finrank ℤ Q' + Module.finrank ℤ Q) → ℤ) :=
            split |>.trans (AlgEquiv.prodCongr EQ' EQ) |>.trans
              (sumPiAlgEquivProdPi
                (Fin (Module.finrank ℤ Q')) (Fin (Module.finrank ℤ Q))).symm |>.trans
              reindex
          rw [hsum]
          exact ⟨E⟩

/-- Every module-finite étale `ℤ`-algebra is the product of as many copies of `ℤ` as its
module rank. -/
noncomputable def intAlgEquivPiFin
    (B : Type u) [CommRing B] [Module.Finite ℤ B] [Algebra.Etale ℤ B] :
    B ≃ₐ[ℤ] (Fin (Module.finrank ℤ B) → ℤ) :=
  (intAlgEquivPiFin_of_finrank_eq (Module.finrank ℤ B) B rfl).some

/-- A rank-five finite étale `ℤ`-algebra is actually `ℤ⁵`. -/
noncomputable def intAlgEquivPiFinFive
    (B : Type u) [CommRing B] [Module.Finite ℤ B] [Algebra.Etale ℤ B]
    (hrank : Module.finrank ℤ B = 5) :
    B ≃ₐ[ℤ] (Fin 5 → ℤ) := by
  rw [← hrank]
  exact intAlgEquivPiFin B

/-- A rank-eleven finite étale `ℤ`-algebra is actually `ℤ¹¹`. -/
noncomputable def intAlgEquivPiFinEleven
    (B : Type u) [CommRing B] [Module.Finite ℤ B] [Algebra.Etale ℤ B]
    (hrank : Module.finrank ℤ B = 11) :
    B ≃ₐ[ℤ] (Fin 11 → ℤ) := by
  rw [← hrank]
  exact intAlgEquivPiFin B

end AlgebraicGeometry.FiniteFlatCommGroupScheme.ConstantPrimeEtale
