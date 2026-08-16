/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.RingTheory.Flat.Equalizer

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

open TensorProduct

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

/-- Extension of ideals along a flat algebra preserves binary
intersections.  The proof writes an intersection as the kernel of the two
quotient maps, tensors that kernel with the flat algebra, and then identifies
the resulting tensor ranges with the extended ideals. -/
theorem idealMap_inf_of_flat [Module.Flat R S] (I J : Ideal R) :
    (I ⊓ J).map (algebraMap R S) =
      I.map (algebraMap R S) ⊓ J.map (algebraMap R S) := by
  let qI : R →ₗ[R] R ⧸ I :=
    (Ideal.Quotient.mkₐ R I).toLinearMap
  let qJ : R →ₗ[R] R ⧸ J :=
    (Ideal.Quotient.mkₐ R J).toLinearMap
  let q : R →ₗ[R] (R ⧸ I) × (R ⧸ J) := qI.prod qJ
  have hker : LinearMap.ker q = ((I ⊓ J : Ideal R) : Submodule R R) := by
    ext r
    change (Ideal.Quotient.mk I r, Ideal.Quotient.mk J r) = 0 ↔
      r ∈ I ∧ r ∈ J
    simp only [Prod.mk_eq_zero, Ideal.Quotient.eq_zero_iff_mem]
  apply le_antisymm (Ideal.map_inf_le (algebraMap R S))
  intro x hx
  let y : S ⊗[R] R := (Algebra.TensorProduct.rid R R S).symm x
  have htenI : x ⊗ₜ[R] (Ideal.Quotient.mk I 1) = 0 := by
    change Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I
        (Ideal.Quotient.mk (I.map (algebraMap R S)) x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx.1, map_zero]
  have htenJ : x ⊗ₜ[R] (Ideal.Quotient.mk J 1) = 0 := by
    change Algebra.TensorProduct.quotIdealMapEquivTensorQuot S J
        (Ideal.Quotient.mk (J.map (algebraMap R S)) x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx.2, map_zero]
  have hyker : y ∈ LinearMap.ker (LinearMap.lTensor S q) := by
    rw [LinearMap.mem_ker]
    apply (TensorProduct.prodRight R R S (R ⧸ I) (R ⧸ J)).injective
    change (x ⊗ₜ[R] (Ideal.Quotient.mk I 1),
      x ⊗ₜ[R] (Ideal.Quotient.mk J 1)) = 0
    rw [htenI, htenJ]
    rfl
  have hyrange : y ∈ LinearMap.range
      (LinearMap.lTensor S
        (((I ⊓ J : Ideal R) : Submodule R R).subtype)) := by
    rw [← hker]
    change y ∈ LinearMap.range
      (AlgebraTensorModule.lTensor R S (LinearMap.ker q).subtype)
    rw [← Module.Flat.ker_lTensor_eq R S q]
    change y ∈ LinearMap.ker (LinearMap.lTensor S q)
    exact hyker
  have hyideal : y ∈ (I ⊓ J).map
      (Algebra.TensorProduct.includeRight : R →ₐ[R] S ⊗[R] R) := by
    rw [← Submodule.restrictScalars_mem R]
    rw [Ideal.map_includeRight_eq]
    exact hyrange
  have hmapped := Ideal.mem_map_of_mem
    (Algebra.TensorProduct.rid R R S).toAlgHom hyideal
  rw [Ideal.map_mapₐ
    (I := I ⊓ J)
    (Algebra.TensorProduct.includeRight : R →ₐ[R] S ⊗[R] R)
    (Algebra.TensorProduct.rid R R S).toAlgHom] at hmapped
  have hcomp : (Algebra.TensorProduct.rid R R S).toAlgHom.comp
      (Algebra.TensorProduct.includeRight : R →ₐ[R] S ⊗[R] R) =
      Algebra.ofId R S := by
    ext
  rw [hcomp] at hmapped
  change Algebra.TensorProduct.rid R R S y ∈
    (I ⊓ J).map (algebraMap R S) at hmapped
  have hy : Algebra.TensorProduct.rid R R S y = x := by
    change Algebra.TensorProduct.rid R R S
      ((Algebra.TensorProduct.rid R R S).symm x) = x
    exact (Algebra.TensorProduct.rid R R S).apply_symm_apply x
  rw [hy] at hmapped
  exact hmapped

/-- Once the extended quotient map is an isomorphism for an ideal, it
remains one after quotienting by any larger ideal. -/
theorem extendedQuotientMap_bijective_of_le
    (I J : Ideal R) (hIJ : I ≤ J)
    (h : Function.Bijective (extendedQuotientMap R S I)) :
    Function.Bijective (extendedQuotientMap R S J) := by
  let f : R →+* S := algebraMap R S
  let qI : R ⧸ I →+* S ⧸ I.map f :=
    extendedQuotientMap R S I
  let eI : R ⧸ I ≃+* S ⧸ I.map f := RingEquiv.ofBijective qI h
  let NI : Ideal (R ⧸ I) := J.map (Ideal.Quotient.mk I)
  let MI : Ideal (S ⧸ I.map f) :=
    (J.map f).map (Ideal.Quotient.mk (I.map f))
  have hMI : MI = NI.map eI.toRingHom := by
    simp only [MI, NI, Ideal.map_map]
    congr 1
  let eQuot : (R ⧸ I) ⧸ NI ≃+* (S ⧸ I.map f) ⧸ MI :=
    Ideal.quotientEquiv NI MI eI hMI
  let eR : (R ⧸ I) ⧸ NI ≃+* R ⧸ J :=
    DoubleQuot.quotQuotEquivQuotOfLE hIJ
  have hMapIJ : I.map f ≤ J.map f := Ideal.map_mono hIJ
  let eS : (S ⧸ I.map f) ⧸ MI ≃+* S ⧸ J.map f :=
    DoubleQuot.quotQuotEquivQuotOfLE hMapIJ
  let eJ : R ⧸ J ≃+* S ⧸ J.map f :=
    eR.symm.trans (eQuot.trans eS)
  have hqJ : extendedQuotientMap R S J = eJ.toRingHom := by
    apply Ideal.Quotient.ringHom_ext
    ext r
    rfl
  rw [hqJ]
  exact eJ.bijective

/-- A flat algebra that is unchanged on two closed quotients is unchanged
on their scheme-theoretic union, represented by the intersection of their
ideals.  This is the affine Mayer--Vietoris step used when graph sections
collide. -/
theorem extendedQuotientMap_bijective_inf_of_bijective
    [Module.Flat R S] (I J : Ideal R)
    (hI : Function.Bijective (extendedQuotientMap R S I))
    (hJ : Function.Bijective (extendedQuotientMap R S J)) :
    Function.Bijective (extendedQuotientMap R S (I ⊓ J)) := by
  let f : R →+* S := algebraMap R S
  have hMapInf : (I ⊓ J).map f = I.map f ⊓ J.map f :=
    idealMap_inf_of_flat R S I J
  have hSup : Function.Bijective
      (extendedQuotientMap R S (I ⊔ J)) :=
    extendedQuotientMap_bijective_of_le R S I (I ⊔ J) le_sup_left hI
  have mem_of_injective (K : Ideal R)
      (hK : Function.Injective (extendedQuotientMap R S K))
      {r : R} (hr : f r ∈ K.map f) : r ∈ K := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply hK
    rw [map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hr
  constructor
  · rintro ⟨r⟩ ⟨s⟩ hrs
    apply Ideal.Quotient.eq.mpr
    have hrs' : f r - f s ∈ (I ⊓ J).map f := by
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hrs
    rw [hMapInf] at hrs'
    have hrsI : f (r - s) ∈ I.map f := by
      rw [map_sub]
      exact hrs'.1
    have hrsJ : f (r - s) ∈ J.map f := by
      rw [map_sub]
      exact hrs'.2
    exact ⟨mem_of_injective I hI.1 hrsI,
      mem_of_injective J hJ.1 hrsJ⟩
  · intro z
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨ri, hri⟩ := hI.2
      (Ideal.Quotient.mk (I.map f) s)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective ri
    obtain ⟨tj, htj⟩ := hJ.2
      (Ideal.Quotient.mk (J.map f) s)
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective tj
    have hrI : f r - s ∈ I.map f :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hri
    have htJ : f t - s ∈ J.map f :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp htj
    have hrtMap : f (r - t) ∈ (I ⊔ J).map f := by
      rw [Ideal.map_sup]
      rw [map_sub]
      have h := Ideal.sub_mem (I.map f ⊔ J.map f)
        (Submodule.mem_sup_left hrI)
        (Submodule.mem_sup_right htJ)
      convert h using 1
      abel
    have hrt : r - t ∈ I ⊔ J :=
      mem_of_injective (I ⊔ J) hSup.1 hrtMap
    rcases Submodule.mem_sup.mp hrt with ⟨i, hi, j, hj, hij⟩
    let u : R := r - i
    have huEq : u = t + j := by
      dsimp only [u]
      calc
        r - i = t + (r - t) - i := by abel
        _ = t + (i + j) - i := by rw [← hij]
        _ = t + j := by abel
    have hfi : f i ∈ I.map f := Ideal.mem_map_of_mem f hi
    have hfj : f j ∈ J.map f := Ideal.mem_map_of_mem f hj
    have huI : f u - s ∈ I.map f := by
      have h := Ideal.sub_mem (I.map f) hrI hfi
      dsimp only [u]
      rw [map_sub]
      convert h using 1
      abel
    have huJ : f u - s ∈ J.map f := by
      have h := Ideal.add_mem (J.map f) htJ hfj
      rw [huEq, map_add]
      convert h using 1
      abel
    refine ⟨Ideal.Quotient.mk (I ⊓ J) u, ?_⟩
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      (hMapInf.symm ▸ ⟨huI, huJ⟩)

/-- The extended quotient map for the unit ideal is an isomorphism between
zero rings. -/
theorem extendedQuotientMap_bijective_top :
    Function.Bijective (extendedQuotientMap R S (⊤ : Ideal R)) := by
  let f : R →+* S := algebraMap R S
  constructor
  · rintro ⟨r⟩ ⟨s⟩ _
    apply Ideal.Quotient.eq.mpr
    exact Submodule.mem_top
  · rintro ⟨s⟩
    refine ⟨Ideal.Quotient.mk (⊤ : Ideal R) 0, ?_⟩
    apply Ideal.Quotient.eq.mpr
    rw [Ideal.map_top]
    exact Submodule.mem_top

/-- If the quotient maps on the two sides of a commutative affine square
are the first-isomorphism-theorem presentations of the same ring, then the
extended quotient map across the square is bijective. -/
theorem extendedQuotientMap_bijective_of_kernel_square
    {T : Type u} [CommRing T]
    (I : Ideal R) (g : S →+* T)
    (hg : Function.Surjective g)
    (hgf : Function.Surjective (g.comp (algebraMap R S)))
    (hkerR : I = RingHom.ker (g.comp (algebraMap R S)))
    (hkerS : I.map (algebraMap R S) = RingHom.ker g) :
    Function.Bijective (extendedQuotientMap R S I) := by
  let f : R →+* S := algebraMap R S
  let eR : R ⧸ I ≃+* T :=
    (Ideal.quotEquivOfEq hkerR).trans
      (RingHom.quotientKerEquivOfSurjective hgf)
  let eS : S ⧸ I.map f ≃+* T :=
    (Ideal.quotEquivOfEq hkerS).trans
      (RingHom.quotientKerEquivOfSurjective hg)
  let e : R ⧸ I ≃+* S ⧸ I.map f := eR.trans eS.symm
  have he : extendedQuotientMap R S I = e.toRingHom := by
    apply Ideal.Quotient.ringHom_ext
    ext r
    change Ideal.Quotient.mk (I.map f) (f r) =
      eS.symm (eR (Ideal.Quotient.mk I r))
    apply eS.injective
    rw [eS.apply_symm_apply]
    rfl
  rw [he]
  exact e.bijective

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

/-- For a finite product of ideals in an étale algebra, it is enough that
the extended quotient map be bijective for each factor.  Inductively, flat
Mayer--Vietoris handles the intersection with the new factor and formal
étaleness restores the full product, including all collision nilpotents. -/
theorem extendedQuotientMap_bijective_finsetProd
    [Algebra.Etale R S] {ι : Type*} (s : Finset ι)
    (I : ι → Ideal R)
    (h : ∀ i ∈ s,
      Function.Bijective (extendedQuotientMap R S (I i))) :
    Function.Bijective
      (extendedQuotientMap R S (∏ i ∈ s, I i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty]
      rw [Ideal.one_eq_top]
      exact extendedQuotientMap_bijective_top R S
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      apply extendedQuotientMap_bijective_mul_of_inf R S
      apply extendedQuotientMap_bijective_inf_of_bijective R S
      · exact h a (Finset.mem_insert_self a s)
      · exact ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)

/-- Fintype-indexed form of
`extendedQuotientMap_bijective_finsetProd`. -/
theorem extendedQuotientMap_bijective_fintypeProd
    [Algebra.Etale R S] {ι : Type*} [Fintype ι]
    (I : ι → Ideal R)
    (h : ∀ i, Function.Bijective
      (extendedQuotientMap R S (I i))) :
    Function.Bijective
      (extendedQuotientMap R S (∏ i, I i)) := by
  classical
  exact extendedQuotientMap_bijective_finsetProd
    R S Finset.univ I (fun i _ ↦ h i)

end MazurTorsion.AlgebraicGeometry.Jacobian.EtaleQuotientProduct
