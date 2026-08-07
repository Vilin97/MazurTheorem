/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FormalImmersionSpecialFiber
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-!
# Affine fibres and the formal-immersion cotangent criterion

This file proves that localization of an affine fibre is natural in the
ambient algebra.  The comparison with the corresponding quotient of the
ambient local ring is proved on both tensor-product generators; in particular,
the quotient equality in `localizationAlgEquivQuotient` is transported
explicitly rather than treated as definitional equality.

The downstream consumer transports a degree-one cotangent calculation on the
affine fibre to the quotient-cotangent certificate used by the formal
immersion machinery.  It also supplies the resulting surjectivity theorem for
completed ambient local rings, with residue-field surjectivity and finiteness
kept as explicit independent hypotheses.
-/

open Algebra TensorProduct AlgebraicGeometry

namespace Ideal.Fiber

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T]

/-- A ring homomorphism bundled with the `NonAssocSemiring` structures
inherited from its `CommRing` instances.  This is the instance-coherent form
required by the local-ring residue and cotangent APIs. -/
abbrev CotangentRingHom (A B : Type*) [CommRing A] [CommRing B] :=
  @RingHom A B
    CommRing.toCommSemiring.toSemiring.toNonAssocSemiring
    CommRing.toCommSemiring.toSemiring.toNonAssocSemiring

/-- The map on affine fibres induced by an algebra homomorphism. -/
noncomputable def map (p : Ideal R) [p.IsPrime] (g : S →ₐ[R] T) :
    p.Fiber S →ₐ[R] p.Fiber T :=
  Algebra.TensorProduct.map (AlgHom.id R p.ResidueField) g

@[simp] theorem map_includeRight (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (s : S) :
    map p g (Algebra.TensorProduct.includeRight s) =
      Algebra.TensorProduct.includeRight (g s) := by
  simp [map]

@[simp] theorem map_comap_includeRight (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) :
    (q.comap (map p g)).comap Algebra.TensorProduct.includeRight =
      (q.comap Algebra.TensorProduct.includeRight).comap g := by
  ext s
  simp [map]

private theorem algEquivAux₂_algebraMap_includeRight
    (p : Ideal R) [p.IsPrime] (q : Ideal (p.Fiber S)) [q.IsPrime]
    (s : S) :
    (algEquivAux₂ p q)
        (algebraMap (p.Fiber S) (Localization.AtPrime q)
          (Algebra.TensorProduct.includeRight s)) =
      Ideal.Quotient.mk
        ((p.map (algebraMap R S)).map
          (algebraMap S (Localization.AtPrime
            (q.comap Algebra.TensorProduct.includeRight))))
        (algebraMap S (Localization.AtPrime
          (q.comap Algebra.TensorProduct.includeRight)) s) := by
  letI : Algebra S (p.Fiber S) := Algebra.TensorProduct.rightAlgebra
  simp only [algEquivAux₂, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply]
  rw [show
    (Localization.localAlgEquiv _ _ (algEquivAux₁ p).symm _).symm
        (algebraMap (p.Fiber S) (Localization.AtPrime q)
          (Algebra.TensorProduct.includeRight s)) =
      algebraMap _ _ ((algEquivAux₁ p)
        (Algebra.TensorProduct.includeRight s)) by
    simp [Localization.localAlgEquiv_symm_apply,
      Localization.localRingEquiv]]
  rw [show Algebra.TensorProduct.includeRight s =
      algebraMap S (p.Fiber S) s by rfl,
    (algEquivAux₁ p).commutes]
  let pS : Ideal S := p.map (algebraMap R S)
  let SpS := S ⧸ pS
  let e₁ := algEquivAux₁ (S := S) p
  let q' : Ideal _ := q.comap e₁.symm
  let r := q.comap Algebra.TensorProduct.includeRight
  let A := Localization (Algebra.algebraMapSubmonoid S p.primeCompl) ⧸
    pS.map (algebraMap S
      (Localization (Algebra.algebraMapSubmonoid S p.primeCompl)))
  let L := Localization.AtPrime q'
  let Q := Localization.AtPrime r ⧸
    pS.map (algebraMap S (Localization.AtPrime r))
  haveI : (q'.under SpS).LiesOver r :=
    under_liesOver_of_liesOver SpS q' (q.under S)
  have hsubmonoid : Algebra.algebraMapSubmonoid SpS r.primeCompl =
      (q'.under SpS).primeCompl :=
    algebraMapSubmonoid_primeCompl_of_liesOver_surjective
      (q'.under SpS) r Ideal.Quotient.mk_surjective
  letI : IsLocalization (Algebra.algebraMapSubmonoid SpS r.primeCompl) L := by
    rw [hsubmonoid]
    exact IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid SpS
        (Algebra.algebraMapSubmonoid S p.primeCompl)) L q'
  letI := IsScalarTower.to₁₃₄ R S SpS L
  letI := IsScalarTower.to₁₃₄ R S SpS Q
  convert
    (IsLocalization.map_eq
      (M := Algebra.algebraMapSubmonoid SpS r.primeCompl)
      (S := L) (T := Algebra.algebraMapSubmonoid SpS r.primeCompl)
      (Q := Q) (g := RingHom.id SpS) (by intro x hx; exact hx)
      (Ideal.Quotient.mk pS s)) using 1
  · apply congrArg
    change
      (algebraMap A L) ((algebraMap S A) s) =
        (algebraMap SpS L) ((algebraMap S SpS) s)
    rw [← IsScalarTower.algebraMap_apply S A L,
      ← IsScalarTower.algebraMap_apply S SpS L]
  · change
      (algebraMap S Q) s =
        (algebraMap SpS Q) ((algebraMap S SpS) s)
    rw [← IsScalarTower.algebraMap_apply S SpS Q]

/-- On an ambient-ring generator, the affine-fibre localization equivalence
is the canonical quotient class in the ambient local ring. -/
theorem localizationAlgEquivQuotient_algebraMap_includeRight
    (p : Ideal R) [p.IsPrime] (q : Ideal (p.Fiber S)) [q.IsPrime]
    (s : S) :
    let r := q.comap Algebra.TensorProduct.includeRight
    letI : Algebra (Localization.AtPrime p) (Localization.AtPrime r) :=
      Localization.AtPrime.algebraOfLiesOver p r
    (localizationAlgEquivQuotient p q)
        (algebraMap (p.Fiber S) (Localization.AtPrime q)
          (Algebra.TensorProduct.includeRight s)) =
      Ideal.Quotient.mk (p.map (algebraMap R (Localization.AtPrime r)))
        (algebraMap S (Localization.AtPrime r) s) := by
  let r := q.comap Algebra.TensorProduct.includeRight
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime r) :=
    Localization.AtPrime.algebraOfLiesOver p r
  change
    (quotientEquivAlgOfEq (Localization.AtPrime p) (Ideal.map_map _ _))
        ((algEquivAux₂ p q)
          (algebraMap (p.Fiber S) (Localization.AtPrime q)
            (Algebra.TensorProduct.includeRight s))) = _
  rw [algEquivAux₂_algebraMap_includeRight]
  exact quotientEquivAlgOfEq_mk (Localization.AtPrime p) _ _

/-- The local map between affine fibres induced at a prime of the target
fibre. -/
noncomputable def localizedMap (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime] :
    Localization.AtPrime (q.comap (map p g)) →ₐ[Localization.AtPrime p]
      Localization.AtPrime q :=
  Localization.localAlgHom' p (q.comap (map p g)) q (map p g) rfl

/-- The underlying ring map of `localizedMap`, re-bundled against the ring
instances used by local-ring cotangent constructions. -/
noncomputable def localizedRingMap (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime] :
    CotangentRingHom (Localization.AtPrime (q.comap (map p g)))
      (Localization.AtPrime q) where
  toFun := localizedMap p g q
  map_one' := map_one (localizedMap p g q)
  map_mul' := map_mul (localizedMap p g q)
  map_zero' := map_zero (localizedMap p g q)
  map_add' := map_add (localizedMap p g q)

@[simp] theorem localizedRingMap_apply (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime]
    (x : Localization.AtPrime (q.comap (map p g))) :
    localizedRingMap p g q x = localizedMap p g q x :=
  rfl

/-- The localized ambient map after quotienting by the special-fibre ideals. -/
noncomputable def localizedQuotientMapAlg (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime] :
    let qS := q.comap (map p g)
    let rS := qS.comap Algebra.TensorProduct.includeRight
    let rT := q.comap Algebra.TensorProduct.includeRight
    letI : Algebra (Localization.AtPrime p) (Localization.AtPrime rS) :=
      Localization.AtPrime.algebraOfLiesOver p rS
    letI : Algebra (Localization.AtPrime p) (Localization.AtPrime rT) :=
      Localization.AtPrime.algebraOfLiesOver p rT
    Localization.AtPrime rS ⧸ p.map (algebraMap R (Localization.AtPrime rS))
      →ₐ[Localization.AtPrime p]
    Localization.AtPrime rT ⧸ p.map (algebraMap R (Localization.AtPrime rT)) := by
  let qS := q.comap (map p g)
  let rS := qS.comap Algebra.TensorProduct.includeRight
  let rT := q.comap Algebra.TensorProduct.includeRight
  let hST : rS = rT.comap g := map_comap_includeRight p g q
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime rS) :=
    Localization.AtPrime.algebraOfLiesOver p rS
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime rT) :=
    Localization.AtPrime.algebraOfLiesOver p rT
  let gLoc : Localization.AtPrime rS →ₐ[Localization.AtPrime p]
      Localization.AtPrime rT :=
    Localization.localAlgHom' p rS rT g hST
  have hcomp : gLoc.toRingHom.comp
      (algebraMap R (Localization.AtPrime rS)) =
      algebraMap R (Localization.AtPrime rT) := by
    ext x
    simp [gLoc,
      IsScalarTower.algebraMap_apply R T (Localization.AtPrime rT)]
  have hideal : p.map (algebraMap R (Localization.AtPrime rS)) ≤
      (p.map (algebraMap R (Localization.AtPrime rT))).comap gLoc := by
    rw [← Ideal.map_le_iff_le_comap]
    exact le_of_eq ((Ideal.map_map _ _).trans
      (congrArg (fun h ↦ p.map h) hcomp))
  exact Ideal.quotientMapₐ _ gLoc hideal

/-- The localized quotient map sends an ambient generator to its image under
the original algebra homomorphism. -/
theorem localizedQuotientMapAlg_mk (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime] (s : S) :
    let qS := q.comap (map p g)
    let rS := qS.comap Algebra.TensorProduct.includeRight
    let rT := q.comap Algebra.TensorProduct.includeRight
    letI : Algebra (Localization.AtPrime p) (Localization.AtPrime rS) :=
      Localization.AtPrime.algebraOfLiesOver p rS
    letI : Algebra (Localization.AtPrime p) (Localization.AtPrime rT) :=
      Localization.AtPrime.algebraOfLiesOver p rT
    localizedQuotientMapAlg p g q
        (Ideal.Quotient.mk (p.map (algebraMap R (Localization.AtPrime rS)))
          (algebraMap S (Localization.AtPrime rS) s)) =
      Ideal.Quotient.mk (p.map (algebraMap R (Localization.AtPrime rT)))
        (algebraMap T (Localization.AtPrime rT) (g s)) := by
  let qS := q.comap (map p g)
  let rS := qS.comap Algebra.TensorProduct.includeRight
  let rT := q.comap Algebra.TensorProduct.includeRight
  let hST : rS = rT.comap g := map_comap_includeRight p g q
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime rS) :=
    Localization.AtPrime.algebraOfLiesOver p rS
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime rT) :=
    Localization.AtPrime.algebraOfLiesOver p rT
  change
    Ideal.quotientMapₐ
        (p.map (algebraMap R (Localization.AtPrime rT)))
        (Localization.localAlgHom' p rS rT g hST) _
        (Ideal.Quotient.mk
          (p.map (algebraMap R (Localization.AtPrime rS)))
          (algebraMap S (Localization.AtPrime rS) s)) = _
  rw [Ideal.quotient_map_mkₐ]
  apply congrArg (Ideal.Quotient.mk
    (p.map (algebraMap R (Localization.AtPrime rT))))
  change
    Localization.localAlgHom rS rT g hST
        (algebraMap S (Localization.AtPrime rS) s) = _
  rw [Localization.localAlgHom_apply]
  exact Localization.localRingHom_to_map rS rT g.toRingHom hST s

/-- Localization of an affine fibre is natural with respect to the ambient
algebra homomorphism and the localized special-fibre quotient map. -/
theorem localizationAlgEquivQuotient_naturality
    (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime] :
    let qS := q.comap (map p g)
    let rS := qS.comap Algebra.TensorProduct.includeRight
    let rT := q.comap Algebra.TensorProduct.includeRight
    letI : Algebra (Localization.AtPrime p) (Localization.AtPrime rS) :=
      Localization.AtPrime.algebraOfLiesOver p rS
    letI : Algebra (Localization.AtPrime p) (Localization.AtPrime rT) :=
      Localization.AtPrime.algebraOfLiesOver p rT
    (localizationAlgEquivQuotient p q).toAlgHom.comp
        (localizedMap p g q) =
      (localizedQuotientMapAlg p g q).comp
        (localizationAlgEquivQuotient p qS).toAlgHom := by
  let qS := q.comap (map p g)
  let hqS : qS = q.comap (map p g) := rfl
  let rS := qS.comap Algebra.TensorProduct.includeRight
  let rT := q.comap Algebra.TensorProduct.includeRight
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime rS) :=
    Localization.AtPrime.algebraOfLiesOver p rS
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime rT) :=
    Localization.AtPrime.algebraOfLiesOver p rT
  apply IsLocalization.algHom_ext qS.primeCompl
  apply Algebra.TensorProduct.ext
  · ext a
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective a
    change
      ((localizationAlgEquivQuotient p q).toAlgHom.comp
          (localizedMap p g q))
          (algebraMap (Localization.AtPrime p)
            (Localization.AtPrime qS) a) =
        ((localizedQuotientMapAlg p g q).comp
          (localizationAlgEquivQuotient p qS).toAlgHom)
          (algebraMap (Localization.AtPrime p)
            (Localization.AtPrime qS) a)
    exact (((localizationAlgEquivQuotient p q).toAlgHom.comp
      (localizedMap p g q)).commutes a).trans
        (((localizedQuotientMapAlg p g q).comp
          (localizationAlgEquivQuotient p qS).toAlgHom).commutes a).symm
  · ext s
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply]
    have hlocal :
      localizedMap p g q
          ((Algebra.algHom (Localization.AtPrime p) (p.Fiber S)
            (Localization.AtPrime qS))
              (Algebra.TensorProduct.includeRight s)) =
        algebraMap (p.Fiber T) (Localization.AtPrime q)
          (Algebra.TensorProduct.includeRight (g s)) := by
      change
        Localization.localAlgHom qS q (map p g) hqS
            (algebraMap (p.Fiber S) (Localization.AtPrime qS)
              (Algebra.TensorProduct.includeRight s)) = _
      rw [Localization.localAlgHom_apply]
      exact (Localization.localRingHom_to_map qS q
        (map p g).toRingHom hqS
          (Algebra.TensorProduct.includeRight s)).trans
        (congrArg (algebraMap (p.Fiber T) (Localization.AtPrime q))
          (map_includeRight p g s))
    have heS :
        (localizationAlgEquivQuotient p qS)
            ((Algebra.algHom (Localization.AtPrime p) (p.Fiber S)
              (Localization.AtPrime qS))
                (Algebra.TensorProduct.includeRight s)) =
          Ideal.Quotient.mk
            (p.map (algebraMap R (Localization.AtPrime rS)))
            (algebraMap S (Localization.AtPrime rS) s) :=
      localizationAlgEquivQuotient_algebraMap_includeRight p qS s
    calc
      _ = (localizationAlgEquivQuotient p q)
          (algebraMap (p.Fiber T) (Localization.AtPrime q)
            (Algebra.TensorProduct.includeRight (g s))) :=
        congrArg (localizationAlgEquivQuotient p q) hlocal
      _ = Ideal.Quotient.mk
          (p.map (algebraMap R (Localization.AtPrime rT)))
          (algebraMap T (Localization.AtPrime rT) (g s)) :=
        localizationAlgEquivQuotient_algebraMap_includeRight p q (g s)
      _ = (localizedQuotientMapAlg p g q)
          (Ideal.Quotient.mk
            (p.map (algebraMap R (Localization.AtPrime rS)))
            (algebraMap S (Localization.AtPrime rS) s)) :=
        (localizedQuotientMapAlg_mk p g q s).symm
      _ = _ := congrArg (localizedQuotientMapAlg p g q) heS.symm

private theorem cotangentMap_comp
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
    (f : A →+* B) (g : B →+* C) [IsLocalHom f] [IsLocalHom g] :
    IsLocalRing.cotangentMap (g.comp f) =
      (IsLocalRing.cotangentMap g).comp (IsLocalRing.cotangentMap f) := by
  ext z
  obtain ⟨a, rfl⟩ :=
    (IsLocalRing.maximalIdeal A).toCotangent_surjective z
  rfl

private theorem cotangentMap_congr
    {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    (f g : A →+* B) [IsLocalHom f] [IsLocalHom g] (h : f = g) :
    IsLocalRing.cotangentMap f = IsLocalRing.cotangentMap g := by
  subst g
  rfl

private instance ringEquivToRingHom_isLocalHom
    {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) :
    IsLocalHom e.toRingHom :=
  ⟨fun x hx ↦ (isLocalHom_equiv e).map_nonunit x hx⟩

private theorem cotangentMap_ringEquiv_surjective
    {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    Function.Surjective (IsLocalRing.cotangentMap e.toRingHom) := by
  intro z
  obtain ⟨b, rfl⟩ :=
    (IsLocalRing.maximalIdeal B).toCotangent_surjective z
  let a : IsLocalRing.maximalIdeal A :=
    ⟨e.symm (b : B),
      map_nonunit e.symm.toRingHom (b : B) b.property⟩
  refine ⟨(IsLocalRing.maximalIdeal A).toCotangent a, ?_⟩
  rw [IsLocalRing.cotangentMap_toCotangent]
  congr 1
  apply Subtype.ext
  exact e.apply_symm_apply (b : B)

private theorem map_le_maximalIdeal_localizationOfFiber
    (p : Ideal R) [p.IsPrime]
    (q : Ideal (p.Fiber S)) [q.IsPrime] :
    let r := q.comap Algebra.TensorProduct.includeRight
    p.map (algebraMap R (Localization.AtPrime r)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime r) := by
  let r := q.comap Algebra.TensorProduct.includeRight
  change p.map (algebraMap R (Localization.AtPrime r)) ≤
    IsLocalRing.maximalIdeal (Localization.AtPrime r)
  rw [← Localization.AtPrime.map_eq_maximalIdeal (I := r),
    IsScalarTower.algebraMap_eq R S (Localization.AtPrime r),
    ← Ideal.map_map]
  exact Ideal.map_mono
    (Ideal.map_le_iff_le_comap.mpr (le_of_eq (Ideal.over_def r p)))

private instance localizedRingMap_isLocalHom
    (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime] :
    IsLocalHom (localizedRingMap p g q) := by
  let hlocal := Localization.isLocalHom_localRingHom
    (q.comap (map p g)) q (map p g).toRingHom rfl
  refine ⟨fun x hx ↦ hlocal.map_nonunit x ?_⟩
  exact hx

/-- Degree-one cotangent data on the local ring map of an actual affine
special fibre. -/
def IsAffineFiberDegreeOneCotangent
    (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime] : Prop :=
  let f := localizedRingMap p g q
  Function.Surjective (IsLocalRing.ResidueField.map f) ∧
    Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q))
      (IsLocalRing.CotangentSpace (Localization.AtPrime q)) = 1 ∧
    ∃ z : IsLocalRing.CotangentSpace
        (Localization.AtPrime (q.comap (map p g))),
      (IsLocalRing.cotangentMapAtResidue f z :
        IsLocalRing.CotangentSpace (Localization.AtPrime q)) ≠ 0

private theorem quotientMap_isLocalHom'
    {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f] (I : Ideal A) (J : Ideal B)
    [IsLocalRing (A ⧸ I)] [IsLocalHom (Ideal.Quotient.mk I)]
    [IsLocalRing (B ⧸ J)] [IsLocalHom (Ideal.Quotient.mk J)]
    (hIJ : I.map f ≤ J) :
    IsLocalHom
      (Ideal.quotientMap J f (Ideal.map_le_iff_le_comap.mp hIJ)) := by
  let fbar : A ⧸ I →+* B ⧸ J :=
    Ideal.quotientMap J f (Ideal.map_le_iff_le_comap.mp hIJ)
  refine ((IsLocalRing.local_hom_TFAE fbar).out 1 0).mp ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have ha : a ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.maximalIdeal_comap (Ideal.Quotient.mk I)]
    exact hx
  change Ideal.Quotient.mk J (f a) ∈
    IsLocalRing.maximalIdeal (B ⧸ J)
  exact map_nonunit (Ideal.Quotient.mk J) (f a)
    (map_nonunit f a ha)

private theorem cotangentMap_surjective_of_square
    {A B A' B' : Type*}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing A'] [IsLocalRing B']
    (f : A →+* B) (eA : A →+* A') (eB : B →+* B')
    (f' : A' →+* B')
    [IsLocalHom f] [IsLocalHom eA] [IsLocalHom eB] [IsLocalHom f']
    (hf : Function.Surjective (IsLocalRing.cotangentMap f))
    (heB : Function.Surjective (IsLocalRing.cotangentMap eB))
    (hsquare :
      (IsLocalRing.cotangentMap eB).comp
          (IsLocalRing.cotangentMap f) =
        (IsLocalRing.cotangentMap f').comp
          (IsLocalRing.cotangentMap eA)) :
    Function.Surjective (IsLocalRing.cotangentMap f') := by
  intro y
  obtain ⟨y', hy'⟩ := heB y
  obtain ⟨x, hx⟩ := hf y'
  refine ⟨IsLocalRing.cotangentMap eA x, ?_⟩
  calc
    IsLocalRing.cotangentMap f'
        (IsLocalRing.cotangentMap eA x) =
      IsLocalRing.cotangentMap eB
        (IsLocalRing.cotangentMap f x) :=
      (LinearMap.congr_fun hsquare x).symm
    _ = IsLocalRing.cotangentMap eB y' :=
      congrArg (IsLocalRing.cotangentMap eB) hx
    _ = y := hy'

private theorem quotientCotangentSurjective_of_ringEquiv_square
    {A B C D : Type*}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing C] [IsLocalRing D]
    (f : A →+* B) [IsLocalHom f]
    (I : Ideal A) (J : Ideal B)
    (hI : I ≤ IsLocalRing.maximalIdeal A)
    (hJ : J ≤ IsLocalRing.maximalIdeal B)
    (hIJ : I.map f ≤ J)
    (g : C →+* D) [IsLocalHom g]
    (eC : C ≃+* A ⧸ I) (eD : D ≃+* B ⧸ J)
    (hg : Function.Surjective (IsLocalRing.cotangentMap g))
    (hsquare :
      let fbar : A ⧸ I →+* B ⧸ J :=
        Ideal.quotientMap J f (Ideal.map_le_iff_le_comap.mp hIJ)
      eD.toRingHom.comp g = fbar.comp eC.toRingHom) :
    IsLocalRing.IsQuotientCotangentSurjective f I J hI hJ hIJ := by
  letI : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
    (hI.trans_lt (IsLocalRing.maximalIdeal.isMaximal _).lt_top).ne
  letI : IsLocalRing (A ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  letI : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  letI : Nontrivial (B ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
    (hJ.trans_lt (IsLocalRing.maximalIdeal.isMaximal _).lt_top).ne
  letI : IsLocalRing (B ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective
  letI : IsLocalHom (Ideal.Quotient.mk J) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective
  let fbar : A ⧸ I →+* B ⧸ J :=
    Ideal.quotientMap J f (Ideal.map_le_iff_le_comap.mp hIJ)
  letI : IsLocalHom fbar := quotientMap_isLocalHom' f I J hIJ
  change Function.Surjective (IsLocalRing.cotangentMap fbar)
  have heD : Function.Surjective
      (IsLocalRing.cotangentMap eD.toRingHom) :=
    cotangentMap_ringEquiv_surjective eD
  have hcotangent :
      (IsLocalRing.cotangentMap eD.toRingHom).comp
          (IsLocalRing.cotangentMap g) =
        (IsLocalRing.cotangentMap fbar).comp
          (IsLocalRing.cotangentMap eC.toRingHom) := by
    rw [← cotangentMap_comp, ← cotangentMap_comp]
    exact cotangentMap_congr _ _ hsquare
  exact cotangentMap_surjective_of_square g eC.toRingHom eD.toRingHom
    fbar hg heD hcotangent

/-- The prime of `S` below the source point of the affine fibre. -/
noncomputable def sourceBasePrime (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) : Ideal S :=
  (q.comap (map p g)).comap Algebra.TensorProduct.includeRight

/-- The prime of `T` below a point of the affine fibre. -/
noncomputable def targetBasePrime (p : Ideal R) [p.IsPrime]
    (q : Ideal (p.Fiber T)) : Ideal T :=
  q.comap Algebra.TensorProduct.includeRight

/-- The source ambient prime is the inverse image of the target ambient
prime. -/
theorem sourceBasePrime_eq_comap (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) :
    sourceBasePrime p g q = (targetBasePrime p q).comap g :=
  map_comap_includeRight p g q

/-- Ring-hom version of `sourceBasePrime_eq_comap`. -/
theorem sourceBasePrime_eq_comap_toRingHom (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) :
    sourceBasePrime p g q = (targetBasePrime p q).comap g.toRingHom :=
  sourceBasePrime_eq_comap p g q

/-- The source ambient prime under a prime of the fibre is prime. -/
instance sourceBasePrime_isPrime (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime] :
    (sourceBasePrime p g q).IsPrime := by
  unfold sourceBasePrime
  infer_instance

/-- The target ambient prime under a prime of the fibre is prime. -/
instance targetBasePrime_isPrime (p : Ideal R) [p.IsPrime]
    (q : Ideal (p.Fiber T)) [q.IsPrime] :
    (targetBasePrime p q).IsPrime := by
  unfold targetBasePrime
  infer_instance

/-- The source ambient prime lies over the base prime. -/
theorem sourceBasePrime_liesOver (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime] :
    (sourceBasePrime p g q).LiesOver p := by
  unfold sourceBasePrime
  infer_instance

/-- The target ambient prime lies over the base prime. -/
theorem targetBasePrime_liesOver (p : Ideal R) [p.IsPrime]
    (q : Ideal (p.Fiber T)) [q.IsPrime] :
    (targetBasePrime p q).LiesOver p := by
  unfold targetBasePrime
  infer_instance

/-- The ambient local-ring map under a point of the affine fibre. -/
noncomputable def ambientLocalizedMap (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime] :
    CotangentRingHom (Localization.AtPrime (sourceBasePrime p g q))
      (Localization.AtPrime (targetBasePrime p q)) := by
  letI : (sourceBasePrime p g q).IsPrime := sourceBasePrime_isPrime p g q
  letI : (targetBasePrime p q).IsPrime := targetBasePrime_isPrime p q
  exact
    { toFun := Localization.localRingHom (sourceBasePrime p g q)
        (targetBasePrime p q) g.toRingHom
          (sourceBasePrime_eq_comap_toRingHom p g q)
      map_one' := map_one (Localization.localRingHom (sourceBasePrime p g q)
        (targetBasePrime p q) g.toRingHom
          (sourceBasePrime_eq_comap_toRingHom p g q))
      map_mul' := map_mul (Localization.localRingHom (sourceBasePrime p g q)
        (targetBasePrime p q) g.toRingHom
          (sourceBasePrime_eq_comap_toRingHom p g q))
      map_zero' := map_zero (Localization.localRingHom (sourceBasePrime p g q)
        (targetBasePrime p q) g.toRingHom
          (sourceBasePrime_eq_comap_toRingHom p g q))
      map_add' := map_add (Localization.localRingHom (sourceBasePrime p g q)
        (targetBasePrime p q) g.toRingHom
          (sourceBasePrime_eq_comap_toRingHom p g q)) }

private instance ambientLocalizedMap_isLocalHom
    (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime] :
    IsLocalHom (ambientLocalizedMap p g q) := by
  letI : (sourceBasePrime p g q).IsPrime := sourceBasePrime_isPrime p g q
  letI : (targetBasePrime p q).IsPrime := targetBasePrime_isPrime p q
  let hlocal := Localization.isLocalHom_localRingHom
    (sourceBasePrime p g q) (targetBasePrime p q) g.toRingHom
      (sourceBasePrime_eq_comap_toRingHom p g q)
  refine ⟨fun x hx ↦ hlocal.map_nonunit x ?_⟩
  exact hx

/-- The ideal cutting out the special fibre in the ambient source local ring. -/
noncomputable def sourceSpecialFiberIdeal (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime] :
    Ideal (Localization.AtPrime (sourceBasePrime p g q)) :=
  letI : (sourceBasePrime p g q).IsPrime := sourceBasePrime_isPrime p g q
  p.map (algebraMap R (Localization.AtPrime (sourceBasePrime p g q)))

/-- The ideal cutting out the special fibre in the ambient target local ring. -/
noncomputable def targetSpecialFiberIdeal (p : Ideal R) [p.IsPrime]
    (q : Ideal (p.Fiber T)) [q.IsPrime] :
    Ideal (Localization.AtPrime (targetBasePrime p q)) :=
  letI : (targetBasePrime p q).IsPrime := targetBasePrime_isPrime p q
  p.map (algebraMap R (Localization.AtPrime (targetBasePrime p q)))

/-- The source special-fibre ideal lies in the local maximal ideal. -/
theorem sourceSpecialFiberIdeal_le (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime] :
    sourceSpecialFiberIdeal p g q ≤
      IsLocalRing.maximalIdeal
        (Localization.AtPrime (sourceBasePrime p g q)) := by
  letI : (sourceBasePrime p g q).IsPrime := sourceBasePrime_isPrime p g q
  exact map_le_maximalIdeal_localizationOfFiber p (q.comap (map p g))

/-- The target special-fibre ideal lies in the local maximal ideal. -/
theorem targetSpecialFiberIdeal_le (p : Ideal R) [p.IsPrime]
    (q : Ideal (p.Fiber T)) [q.IsPrime] :
    targetSpecialFiberIdeal p q ≤
      IsLocalRing.maximalIdeal
        (Localization.AtPrime (targetBasePrime p q)) := by
  letI : (targetBasePrime p q).IsPrime := targetBasePrime_isPrime p q
  exact map_le_maximalIdeal_localizationOfFiber p q

/-- The ambient localized map carries the source special-fibre ideal exactly
onto the target special-fibre ideal. -/
theorem sourceSpecialFiberIdeal_map (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime] :
    (sourceSpecialFiberIdeal p g q).map (ambientLocalizedMap p g q) =
      targetSpecialFiberIdeal p q := by
  letI : (sourceBasePrime p g q).IsPrime := sourceBasePrime_isPrime p g q
  letI : (targetBasePrime p q).IsPrime := targetBasePrime_isPrime p q
  unfold sourceSpecialFiberIdeal targetSpecialFiberIdeal
  rw [Ideal.map_map]
  apply congrArg (fun h ↦ p.map h)
  ext x
  change ambientLocalizedMap p g q
      (algebraMap R (Localization.AtPrime (sourceBasePrime p g q)) x) = _
  rw [IsScalarTower.algebraMap_apply R S
    (Localization.AtPrime (sourceBasePrime p g q))]
  change Localization.localRingHom (sourceBasePrime p g q)
      (targetBasePrime p q) g.toRingHom
        (sourceBasePrime_eq_comap_toRingHom p g q)
        (algebraMap S (Localization.AtPrime (sourceBasePrime p g q))
          (algebraMap R S x)) = _
  rw [Localization.localRingHom_to_map]
  change algebraMap T (Localization.AtPrime (targetBasePrime p q))
      (g (algebraMap R S x)) = _
  rw [g.commutes, ← IsScalarTower.algebraMap_apply R T
    (Localization.AtPrime (targetBasePrime p q))]

/-- The exact ambient quotient-cotangent conclusion transported from an
affine-fibre calculation. -/
noncomputable abbrev IsAmbientQuotientCotangentSurjective
    (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime] : Prop :=
  letI : (sourceBasePrime p g q).IsPrime := sourceBasePrime_isPrime p g q
  letI : (targetBasePrime p q).IsPrime := targetBasePrime_isPrime p q
  IsLocalRing.IsQuotientCotangentSurjective
    (ambientLocalizedMap p g q) (sourceSpecialFiberIdeal p g q)
      (targetSpecialFiberIdeal p q) (sourceSpecialFiberIdeal_le p g q)
      (targetSpecialFiberIdeal_le p q) (sourceSpecialFiberIdeal_map p g q).le

/-- Degree-one affine-fibre data makes the local cotangent map on the fibre
surjective. -/
theorem IsAffineFiberDegreeOneCotangent.localizedCotangentSurjective
    (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime]
    (hdegreeOne : IsAffineFiberDegreeOneCotangent p g q) :
    Function.Surjective
      (IsLocalRing.cotangentMap (localizedRingMap p g q)) := by
  change Function.Surjective (IsLocalRing.ResidueField.map
      (localizedRingMap p g q)) ∧
    Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q))
      (IsLocalRing.CotangentSpace (Localization.AtPrime q)) = 1 ∧
    ∃ z : IsLocalRing.CotangentSpace
        (Localization.AtPrime (q.comap (map p g))),
      (IsLocalRing.cotangentMapAtResidue
        (localizedRingMap p g q) z :
          IsLocalRing.CotangentSpace (Localization.AtPrime q)) ≠ 0
      at hdegreeOne
  exact IsLocalRing.cotangentMap_surjective_of_degreeOne_of_apply_ne_zero
    (localizedRingMap p g q) hdegreeOne.1 hdegreeOne.2.1
    hdegreeOne.2.2.choose hdegreeOne.2.2.choose_spec

/-- The affine-fibre degree-one calculation supplies the quotient cotangent
surjection for the ambient localized map. -/
theorem IsAffineFiberDegreeOneCotangent.isQuotientCotangentSurjective
    (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime]
    (hdegreeOne : IsAffineFiberDegreeOneCotangent p g q) :
    IsAmbientQuotientCotangentSurjective p g q := by
  letI : (sourceBasePrime p g q).IsPrime := sourceBasePrime_isPrime p g q
  letI : (targetBasePrime p q).IsPrime := targetBasePrime_isPrime p q
  letI : (sourceBasePrime p g q).LiesOver p := sourceBasePrime_liesOver p g q
  letI : (targetBasePrime p q).LiesOver p := targetBasePrime_liesOver p q
  let qS := q.comap (map p g)
  let rS := sourceBasePrime p g q
  let rT := targetBasePrime p q
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime rS) :=
    Localization.AtPrime.algebraOfLiesOver p rS
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime rT) :=
    Localization.AtPrime.algebraOfLiesOver p rT
  let gLoc := ambientLocalizedMap p g q
  let I := sourceSpecialFiberIdeal p g q
  let J := targetSpecialFiberIdeal p q
  let hI := sourceSpecialFiberIdeal_le p g q
  let hJ := targetSpecialFiberIdeal_le p q
  let hIJ : I.map gLoc ≤ J := (sourceSpecialFiberIdeal_map p g q).le
  let fbar : Localization.AtPrime rS ⧸ I →+*
      Localization.AtPrime rT ⧸ J :=
    Ideal.quotientMap J gLoc (Ideal.map_le_iff_le_comap.mp hIJ)
  letI : Algebra (Localization.AtPrime p)
      (Localization.AtPrime
        (qS.comap Algebra.TensorProduct.includeRight)) :=
    Localization.AtPrime.algebraOfLiesOver p
      (qS.comap Algebra.TensorProduct.includeRight)
  letI : Algebra (Localization.AtPrime p)
      (Localization.AtPrime
        (q.comap Algebra.TensorProduct.includeRight)) :=
    Localization.AtPrime.algebraOfLiesOver p
      (q.comap Algebra.TensorProduct.includeRight)
  let eS := localizationAlgEquivQuotient p qS
  let eT := localizationAlgEquivQuotient p q
  have hqmap : (localizedQuotientMapAlg p g q).toRingHom = fbar := by
    rfl
  have hnatAlg := localizationAlgEquivQuotient_naturality p g q
  have hsquare : eT.toRingEquiv.toRingHom.comp
      (localizedRingMap p g q) =
      fbar.comp eS.toRingEquiv.toRingHom := by
    ext x
    change eT (localizedMap p g q x) = fbar (eS x)
    rw [← hqmap]
    exact DFunLike.congr_fun hnatAlg x
  exact quotientCotangentSurjective_of_ringEquiv_square gLoc I J hI hJ
    hIJ (localizedRingMap p g q) eS.toRingEquiv eT.toRingEquiv
      (hdegreeOne.localizedCotangentSurjective p g q) hsquare

/-- Package affine-fibre degree-one data as the checked special-fibre
certificate consumed by the formal-completion criterion. -/
noncomputable def
    IsAffineFiberDegreeOneCotangent.quotientCotangentCertificate
    (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime]
    (hdegreeOne : IsAffineFiberDegreeOneCotangent p g q)
    (hfinite : Module.Finite
      (Localization.AtPrime (targetBasePrime p q) ⧸
        targetSpecialFiberIdeal p q)
      ((IsLocalRing.maximalIdeal
          (Localization.AtPrime (targetBasePrime p q))).map
        (Ideal.Quotient.mk (targetSpecialFiberIdeal p q)))) :
    IsLocalRing.QuotientCotangentCertificate
      (ambientLocalizedMap p g q) where
  sourceIdeal := sourceSpecialFiberIdeal p g q
  targetIdeal := targetSpecialFiberIdeal p q
  sourceIdeal_le := sourceSpecialFiberIdeal_le p g q
  targetIdeal_le := targetSpecialFiberIdeal_le p q
  map_sourceIdeal_le := (sourceSpecialFiberIdeal_map p g q).le
  targetIdeal_le_map_maximalIdeal := by
    rw [← sourceSpecialFiberIdeal_map p g q]
    exact Ideal.map_mono (sourceSpecialFiberIdeal_le p g q)
  finite_target_maximalIdeal := hfinite
  quotient_cotangent_surjective :=
    hdegreeOne.isQuotientCotangentSurjective p g q

/-- A genuine formal-completion consumer: the transported degree-one
affine-fibre calculation makes the ambient completed local map surjective,
once the independent residue and finiteness inputs are supplied. -/
theorem IsAffineFiberDegreeOneCotangent.ambientCompletionMapSurjective
    (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime]
    [Module.Finite (Localization.AtPrime (sourceBasePrime p g q))
      (IsLocalRing.maximalIdeal
        (Localization.AtPrime (sourceBasePrime p g q)))]
    [Module.Finite (Localization.AtPrime (targetBasePrime p q))
      (IsLocalRing.maximalIdeal
        (Localization.AtPrime (targetBasePrime p q)))]
    (hdegreeOne : IsAffineFiberDegreeOneCotangent p g q)
    (hfinite : Module.Finite
      (Localization.AtPrime (targetBasePrime p q) ⧸
        targetSpecialFiberIdeal p q)
      ((IsLocalRing.maximalIdeal
          (Localization.AtPrime (targetBasePrime p q))).map
        (Ideal.Quotient.mk (targetSpecialFiberIdeal p q))))
    (hresidue : Function.Surjective
      (IsLocalRing.ResidueField.map (ambientLocalizedMap p g q))) :
    Function.Surjective
      (AlgebraicGeometry.LocalCompletion.map
        (ambientLocalizedMap p g q)) :=
  LocalCompletion.map_surjective_of_quotientCotangentCertificate_of_finite_maximalIdeals
    (ambientLocalizedMap p g q)
    (hdegreeOne.quotientCotangentCertificate p g q hfinite) hresidue

end Ideal.Fiber
