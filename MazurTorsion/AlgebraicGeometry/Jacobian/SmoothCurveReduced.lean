/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Jacobson.Ring
import TauCeti.RingTheory.Smooth.DimensionOne
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.ProductFormula.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Separated
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

open scoped TensorProduct

namespace MazurTorsion.AlgebraicGeometry.Jacobian.SmoothCurveReduced

universe u v w

open IsLocalRing
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.SchemeWeilDivisor

/-- A nonzero standard-smooth algebra of relative dimension one over a field
has a nonzero maximal ideal. -/
theorem exists_ne_bot_isMaximal
    (K : Type u) (A : Type v) [Field K] [CommRing A] [Nontrivial A]
    [Algebra K A] [Algebra.IsStandardSmoothOfRelativeDimension 1 K A] :
    ∃ q : Ideal A, q ≠ ⊥ ∧ q.IsMaximal := by
  obtain ⟨q, hq⟩ := Ideal.exists_maximal A
  refine ⟨q, ?_, hq⟩
  intro hq0
  have hbot : (⊥ : Ideal A).IsMaximal := hq0 ▸ hq
  letI : Field A := (Ring.isField_iff_maximal_bot.mpr hbot).toField
  letI : Algebra.IsStandardSmooth K A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  obtain ⟨g, hg⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial 1 K A
  let P := MvPolynomial (Fin 1) K
  letI : Algebra P A := g.toRingHom.toAlgebra
  haveI : Algebra.Etale P A := by
    rw [← RingHom.etale_algebraMap]
    exact hg
  have hgInjective : Function.Injective g := by
    intro a b hab
    rw [← sub_eq_zero]
    by_contra hab0
    have hreg : IsSMulRegular A (a - b) := by
      apply IsSMulRegular.of_flat
      exact IsSMulRegular.of_ne_zero hab0
    have hone : (1 : A) = 0 := by
      apply hreg.right_eq_zero_of_smul
      change g (a - b) * 1 = 0
      rw [map_sub, hab, sub_self, zero_mul]
    exact one_ne_zero hone
  letI : Module.Finite K A := finite_of_finite_type_of_isJacobsonRing K A
  letI : Module.Finite K P := Module.Finite.of_injective g.toLinearMap hgInjective
  letI : Module.Finite K (Polynomial K) :=
    Module.Finite.equiv (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toLinearEquiv
  exact Polynomial.not_finite (R := K) inferInstance

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

open CategoryTheory Limits _root_.AlgebraicGeometry

/-- Every point of a smooth relative curve has an affine neighbourhood whose
coordinate ring is étale over a one-variable polynomial ring.  The base ring
is written as the global sections of `Spec K`; it is canonically isomorphic
to `K` and is the ring occurring directly in the scheme chart API.

The named downstream consumer is the local comparison between pointed
symmetric powers and the universal monic-root incidence family. -/
theorem exists_affineOpen_etaleCoordinate
    (K : Type u) [Field K] (X : Scheme.{u})
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] (x : X) :
    ∃ V : X.affineOpens, x ∈ (V : X.Opens) ∧
      let e : (V : X.Opens) ≤ f ⁻¹ᵁ (⊤ : (Spec (.of K)).Opens) := by simp
      letI : Algebra Γ(Spec (.of K), ⊤) Γ(X, (V : X.Opens)) :=
        (f.appLE ⊤ (V : X.Opens) e).hom.toAlgebra
      ∃ g : MvPolynomial (Fin 1) Γ(Spec (.of K), ⊤) →ₐ[Γ(Spec (.of K), ⊤)]
          Γ(X, (V : X.Opens)), g.Etale := by
  obtain ⟨U, hU, V, hV, hx, e, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := 1) (f := f) x
  have hfxU : f.base x ∈ U := e hx
  have hUtop : U = ⊤ := by
    apply top_unique
    intro y _
    simpa only [Subsingleton.elim y (f.base x)] using hfxU
  subst U
  refine ⟨⟨V, hV⟩, hx, ?_⟩
  let e' : V ≤ f ⁻¹ᵁ (⊤ : (Spec (.of K)).Opens) := by simp
  letI : Algebra Γ(Spec (.of K), ⊤) Γ(X, V) :=
    (f.appLE ⊤ V e').hom.toAlgebra
  letI : Algebra.IsStandardSmoothOfRelativeDimension 1
      Γ(Spec (.of K), ⊤) Γ(X, V) := by
    exact hstd.toAlgebra
  exact
    Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
      1 Γ(Spec (.of K), ⊤) Γ(X, V)

/-- The diagonal of a separated étale morphism is simultaneously an open
and a closed immersion.  In the local universal-divisor construction this
selects the genuine curve diagonal as an open-and-closed component of the
equal-coordinate root family. -/
theorem etale_diagonal_openClosed {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Etale f] [IsSeparated f] :
    IsOpenImmersion (pullback.diagonal f) ∧
      IsClosedImmersion (pullback.diagonal f) := by
  exact ⟨inferInstance, inferInstance⟩

/-- Affine étale coordinates satisfy the open-and-closed diagonal
hypothesis required by the monic-root chart comparison. -/
theorem specMap_etale_diagonal_openClosed
    {R A : Type u} [CommRing R] [CommRing A]
    (g : R →+* A) (hg : g.Etale) :
    let f := Spec.map (CommRingCat.ofHom g)
    IsOpenImmersion (pullback.diagonal f) ∧
      IsClosedImmersion (pullback.diagonal f) := by
  let f := Spec.map (CommRingCat.ofHom g)
  haveI : Etale f := HasRingHomProperty.Spec_iff.mpr hg
  exact etale_diagonal_openClosed f

/-- For an étale affine coordinate, the self-fiber product splits as the
diagonal factor and a complementary factor.  The diagonal factor is the
one retained when the affine-line monic root family is transported to a
curve chart. -/
theorem etale_tensorSquare_exists_diagonalProduct
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.Etale R A] :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra A T),
      Nonempty (A ⊗[R] A ≃ₐ[A] A × T) := by
  exact Algebra.FormallyUnramified.exists_algEquiv_prod R A

/-- The étale tensor-square splitting can be chosen so that projection to
the first factor is the multiplication map.  This records which open-and-
closed component is the actual diagonal, information intentionally omitted
from the more economical `exists_algEquiv_prod` interface.

The named downstream consumer is the étale monic-root chart used in the
pointed incidence comparison. -/
theorem etale_tensorSquare_exists_diagonalProduct_compatible
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.Etale R A] :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra A T)
      (e : A ⊗[R] A ≃ₐ[A] A × T),
      ∀ x, (e x).1 = Algebra.TensorProduct.lmul'' R x := by
  obtain ⟨e, he, hspan⟩ :
      ∃ e, IsIdempotentElem e ∧
        KaehlerDifferential.ideal R A = A ⊗[R] A ∙ e :=
    (Ideal.isIdempotentElem_iff_of_fg _
      (KaehlerDifferential.ideal_fg R A)).mp <|
        (Ideal.cotangent_subsingleton_iff _).mp <|
          inferInstanceAs (Subsingleton Ω[A⁄R])
  let e₁ := AlgEquiv.prodQuotientOfIsIdempotentElem (R := A)
    he he.one_sub (by simp) (by simp [he])
  let μ : A ⊗[R] A →ₐ[A] A := Algebra.TensorProduct.lmul'' R
  have hker : RingHom.ker μ = KaehlerDifferential.ideal R A := by
    rfl
  have hμsurj : Function.Surjective μ := by
    intro a
    refine ⟨a ⊗ₜ[R] 1, ?_⟩
    change a * 1 = a
    exact mul_one a
  let e₂ : (A ⊗[R] A ⧸ Ideal.span {e}) ≃ₐ[A] A :=
    ((Ideal.span {e}).quotientEquivAlgOfEq A
      (hspan.symm.trans hker.symm)).trans <|
      Ideal.quotientKerAlgEquivOfSurjective hμsurj
  let T := (A ⊗[R] A) ⧸ Ideal.span {1 - e}
  let E : A ⊗[R] A ≃ₐ[A] A × T := e₁.trans (.prodCongr e₂ .refl)
  refine ⟨T, inferInstance, inferInstance, E, ?_⟩
  intro x
  change e₂ (Ideal.Quotient.mk (Ideal.span {e}) x) =
    Algebra.TensorProduct.lmul'' R x
  change ((Ideal.quotientEquivAlgOfEq A (hspan.symm.trans hker.symm)).trans
      (Ideal.quotientKerAlgEquivOfSurjective hμsurj))
      (Ideal.Quotient.mk (Ideal.span {e}) x) = μ x
  change (Ideal.quotientKerAlgEquivOfSurjective hμsurj)
      ((Ideal.quotientEquivAlgOfEq A (hspan.symm.trans hker.symm))
        (Ideal.Quotient.mk (Ideal.span {e}) x)) = μ x
  rw [Ideal.quotientEquivAlgOfEq_mk,
    Ideal.quotientKerAlgEquivOfSurjective_mk]

/-- Scheme-level form of the compatible étale tensor-square splitting:
the self-fiber product is a coproduct whose first summand is exactly the
diagonal.  This is the open-and-closed sheet selected by a curve point in
the local root chart. -/
theorem etale_pullback_exists_diagonalCoproduct
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.Etale R A] :
    let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra A T)
      (E : pullback f f ≅ Spec (.of A) ⨿ Spec (.of T)),
      pullback.diagonal f ≫ E.hom = coprod.inl := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
  obtain ⟨T, _, _, e, he⟩ :=
    etale_tensorSquare_exists_diagonalProduct_compatible R A
  let eSpec : Spec (.of (A ⊗[R] A)) ≅ Spec (.of (A × T)) :=
    (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op).symm
  let E : pullback f f ≅ Spec (.of A) ⨿ Spec (.of T) :=
    pullbackSpecIso R A A ≪≫ eSpec ≪≫
      (asIso (coprodSpec A T)).symm
  refine ⟨T, inferInstance, inferInstance, E, ?_⟩
  apply (cancel_mono (coprodSpec A T)).mp
  change pullback.diagonal f ≫ E.hom ≫ coprodSpec A T =
    coprod.inl ≫ coprodSpec A T
  rw [coprodSpec_inl]
  rw [diagonal_SpecMap R A]
  dsimp only [E]
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv,
    Category.assoc, Iso.inv_hom_id_assoc, IsIso.inv_hom_id,
    Category.comp_id]
  dsimp only [eSpec]
  change Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom) ≫
      Spec.map e.symm.toRingEquiv.toCommRingCatIso.hom =
    Spec.map (CommRingCat.ofHom (RingHom.fst A T))
  rw [← Spec.map_comp, Spec.map_inj]
  ext z
  change Algebra.TensorProduct.lmul'' R (e.symm z) = z.1
  exact (he (e.symm z)).symm.trans (congrArg Prod.fst (e.apply_symm_apply z))

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

/-- A geometrically irreducible smooth relative curve over a field has a
codimension-one point, without any rational-point hypothesis. -/
theorem nonempty_codimensionOnePoint
    (K : Type u) [Field K] (X : Scheme.{u})
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    [GeometricallyIrreducible f] : Nonempty (CodimensionOnePoint X) := by
  letI : IsIntegral X :=
    scheme_isIntegral_of_geometricallyIrreducible_of_smoothRelativeDimension_one K X f
  let x₀ : X := Classical.choice inferInstance
  obtain ⟨U, hU, V, hV, hx₀, e, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := 1) (f := f) x₀
  have hfxU : f.base x₀ ∈ U := e hx₀
  have hUtop : U = ⊤ := by
    apply top_unique
    intro y _
    simpa only [Subsingleton.elim y (f.base x₀)] using hfxU
  subst U
  letI : Nonempty V := ⟨⟨x₀, hx₀⟩⟩
  letI : Field Γ(Spec (.of K), ⊤) :=
    ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField K)).toField
  letI : Algebra Γ(Spec (.of K), ⊤) Γ(X, V) :=
    (f.appLE ⊤ V e).hom.toAlgebra
  letI : Algebra.IsStandardSmoothOfRelativeDimension 1
      Γ(Spec (.of K), ⊤) Γ(X, V) := hstd.toAlgebra
  obtain ⟨q, hq0, hq⟩ := exists_ne_bot_isMaximal Γ(Spec (.of K), ⊤) Γ(X, V)
  let z : Spec Γ(X, V) := ⟨q, hq.isPrime⟩
  let x : X := hV.fromSpec z
  have hxV : x ∈ V := by
    change x ∈ (V : Set X)
    rw [← hV.range_fromSpec]
    exact ⟨z, rfl⟩
  have hprime : hV.primeIdealOf ⟨x, hxV⟩ = z := by
    apply hV.fromSpec.isOpenEmbedding.injective
    rw [hV.fromSpec_primeIdealOf]
  have hxne : x ≠ genericPoint X := by
    intro hx
    have hgenericV : genericPoint X ∈ V := hx ▸ hxV
    apply hq0
    calc
      q = z.asIdeal := rfl
      _ = (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
        congrArg PrimeSpectrum.asIdeal hprime.symm
      _ = (hV.primeIdealOf ⟨genericPoint X, hgenericV⟩).asIdeal := by
        exact congrArg (fun y : V ↦ (hV.primeIdealOf y).asIdeal)
          (by apply Subtype.ext; exact hx)
      _ = (genericPoint (Spec Γ(X, V))).asIdeal := by
        rw [hV.primeIdealOf_genericPoint]
      _ = ⊥ := by
        rw [genericPoint_eq_bot_of_affine]
        rfl
  exact ⟨⟨x,
    coheight_eq_one_of_ne_genericPoint_of_smoothRelativeDimension_one K X f x hxne⟩⟩

end MazurTorsion.AlgebraicGeometry.Jacobian.SmoothCurveReduced
