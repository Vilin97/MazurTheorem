/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Products of graph ideals in an étale algebra

The quotient by a product of graph ideals retains nilpotent structure when
the graphs meet.  This file isolates the commutative-algebra mechanism used
in the Jacobian incidence chart: an étale algebra is formally étale, so an
isomorphism after the square-zero passage from an ideal product to the
corresponding intersection lifts uniquely to the product quotient.

The named downstream consumer is
`GeometricAssignedAffineSupportCoproduct`.
-/

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.Jacobian.EtaleQuotientProduct

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- The quotient map obtained by extending an ideal along an algebra map. -/
noncomputable def extendedQuotientMap (I : Ideal R) :
    R ⧸ I →+* S ⧸ I.map (algebraMap R S) :=
  Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S)
    Ideal.le_comap_map

@[simp]
theorem extendedQuotientMap_mk (I : Ideal R) (x : R) :
    extendedQuotientMap R S I (Ideal.Quotient.mk I x) =
      Ideal.Quotient.mk (I.map (algebraMap R S))
        (algebraMap R S x) :=
  rfl

/-- Quotienting an étale algebra by an extended ideal is the corresponding
étale base change. -/
theorem extendedQuotientMap_etale [Algebra.Etale R S] (I : Ideal R) :
    (extendedQuotientMap R S I).Etale := by
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I
  letI : Algebra.Etale (R ⧸ I) (TensorProduct R (R ⧸ I) S) :=
    Algebra.Etale.baseChange R S (R ⧸ I)
  have he : Algebra.Etale (R ⧸ I)
      (S ⧸ I.map (algebraMap R S)) :=
    Algebra.Etale.of_equiv e.symm
  rw [show extendedQuotientMap R S I =
      algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S)) by
    ext x
    rfl]
  exact RingHom.etale_algebraMap.mpr he

/-- The passage from the intersection of two ideals to their product is a
square-zero thickening.  Formal étaleness therefore lifts an isomorphism on
the intersection quotient uniquely to the product quotient. -/
theorem extendedQuotientMap_bijective_mul_of_inf
    [Algebra.Etale R S] (I J : Ideal R)
    (h : Function.Bijective (extendedQuotientMap R S (I ⊓ J))) :
    Function.Bijective (extendedQuotientMap R S (I * J)) := by
  let f : R →+* S := algebraMap R S
  let P : Ideal R := I * J
  let Q : Ideal R := I ⊓ J
  have hPQ : P ≤ Q := Ideal.mul_le_inf
  let A := R ⧸ P
  let B := S ⧸ P.map f
  let N : Ideal A := Q.map (Ideal.Quotient.mk P)
  let M : Ideal B := (Q.map f).map (Ideal.Quotient.mk (P.map f))
  have hN : N ^ 2 = ⊥ := by
    rw [show N ^ 2 = (Q ^ 2).map (Ideal.Quotient.mk P) by
      simp only [N, Ideal.map_pow]]
    rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    simpa only [P, Q, pow_two] using
      Ideal.mul_mono (inf_le_left : I ⊓ J ≤ I)
        (inf_le_right : I ⊓ J ≤ J)
  have hM : M ^ 2 = ⊥ := by
    rw [show M ^ 2 = ((Q ^ 2).map f).map
        (Ideal.Quotient.mk (P.map f)) by
      simp only [M, Ideal.map_pow, Ideal.map_map]]
    rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    apply Ideal.map_mono
    simpa only [P, Q, pow_two] using
      Ideal.mul_mono (inf_le_left : I ⊓ J ≤ I)
        (inf_le_right : I ⊓ J ≤ J)
  let qP : A →+* B := extendedQuotientMap R S P
  let qQ : R ⧸ Q →+* S ⧸ Q.map f :=
    extendedQuotientMap R S Q
  let eQ : R ⧸ Q ≃+* S ⧸ Q.map f :=
    RingEquiv.ofBijective qQ h
  let eR : (A ⧸ N) ≃+* R ⧸ Q :=
    DoubleQuot.quotQuotEquivQuotOfLE hPQ
  have hMapPQ : P.map f ≤ Q.map f := Ideal.map_mono hPQ
  let eS : (B ⧸ M) ≃+* S ⧸ Q.map f :=
    DoubleQuot.quotQuotEquivQuotOfLE hMapPQ
  let reductionEquiv : (B ⧸ M) ≃+* (A ⧸ N) :=
    (eS.trans eQ.symm).trans eR.symm
  letI : Algebra A B := qP.toAlgebra
  have hqPEtale : qP.Etale :=
    extendedQuotientMap_etale R S P
  letI : Algebra.Etale A B := hqPEtale.toAlgebra
  let reduction : B →ₐ[A] A ⧸ N :=
    { toRingHom := reductionEquiv.toRingHom.comp
        (Ideal.Quotient.mk M)
      commutes' := by
        intro a
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
        have heQ : eQ.symm
            (Ideal.Quotient.mk (Q.map f) (f r)) =
              Ideal.Quotient.mk Q r := by
          apply eQ.toEquiv.symm_apply_eq.mpr
          rfl
        change eR.symm
            (eQ.symm (eS
              (DoubleQuot.quotQuotMk (P.map f) (Q.map f) (f r)))) =
          DoubleQuot.quotQuotMk P Q r
        rw [DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk,
          heQ,
          DoubleQuot.quotQuotEquivQuotOfLE_symm_mk] }
  let lift : B →ₐ[A] A :=
    Algebra.FormallySmooth.lift N ⟨2, hN⟩ reduction
  have hlift_left : lift.comp (Algebra.ofId A B) = AlgHom.id A A := by
    ext
  have hlift_right : (Algebra.ofId A B).comp lift = AlgHom.id A B := by
    apply Algebra.FormallyUnramified.lift_unique M ⟨2, hM⟩
    ext b
    apply reductionEquiv.injective
    change reductionEquiv
        (Ideal.Quotient.mk M (algebraMap A B (lift b))) =
      reductionEquiv (Ideal.Quotient.mk M b)
    rw [show reductionEquiv
          (Ideal.Quotient.mk M (algebraMap A B (lift b))) =
        Ideal.Quotient.mk N (lift b) by
      exact reduction.commutes (lift b)]
    exact AlgHom.congr_fun
      (Algebra.FormallySmooth.comp_lift N ⟨2, hN⟩ reduction) b
  let e : A ≃ₐ[A] B :=
    AlgEquiv.ofAlgHom (Algebra.ofId A B) lift hlift_right hlift_left
  have hqP : qP = algebraMap A B := by
    rfl
  change Function.Bijective qP
  rw [hqP]
  exact e.bijective

end MazurTorsion.AlgebraicGeometry.Jacobian.EtaleQuotientProduct
