/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.DivisorLineBundle
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.GroupTheory.ArchimedeanDensely
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order
import TauCeti.RingTheory.Smooth.DimensionOne

/-!
# Affine charts for the divisor--line-bundle dictionary

This file identifies height-one primes of a Dedekind affine chart with the ambient
codimension-one points lying in that chart. It proves that the Dedekind-domain valuations agree
with Tau Ceti's scheme-theoretic orders, so the earlier compatibility package is automatic once
the affine coordinate ring is known to be Dedekind. That remaining condition is reduced to
dimension at most one and integral closedness.

The compatibility is consumed here, rather than merely recorded: it transports the affine
principal-divisor order system to the ambient points of the chart and constructs a canonical
divisor-to-scheme-Picard map which kills those principal divisors. This is the checked local
boundary needed before the affine line bundles in `DivisorLineBundle` can be glued on a curve.
The unconditional Picard target is the coordinate spectrum `Spec Γ(X, U)`. The file isolates
strong monoidality of pullback as an upstream-compatible sufficient datum for transport to
`Pic(U)` and consumes that datum to preserve the principal kernel, class descent, and range
equivalence. Constructing the datum and overlap-compatible gluing to `X` remain separate
obligations. For smooth curves over a field, locally standard-smooth relative dimension one is
now proved to force both dimension at most one and integral closedness. Consequently every
nonempty affine chart has the required Dedekind order compatibility without an additional
normality hypothesis.
-/

namespace MazurTorsion.AlgebraicGeometry.AffineChart

universe u

open CategoryTheory MonoidalCategory
open _root_.AlgebraicGeometry
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open IsDedekindDomain WithZero

private lemma heightOneSpectrum_height
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (v : HeightOneSpectrum R) : v.asIdeal.height = 1 := by
  refine le_antisymm ?_ ?_
  · suffices h : (v.asIdeal.height : WithBot ℕ∞) ≤ 1 by
      norm_cast at h
    exact v.asIdeal.height_le_ringKrullDim_of_isPrime.trans (by
      rw [← Nat.cast_one, ← Ring.krullDimLE_iff]
      infer_instance)
  · apply le_of_eq_of_le _
      (Ideal.height_add_one_le_of_lt_of_isPrime
        (Ideal.bot_lt_of_maximal v.asIdeal
          (Ring.not_isField_of_ne_of_ne v.ne_bot v.isPrime.ne_top)))
    simp

/-- Height-one primes of a Dedekind domain are exactly the codimension-one points of its
affine spectrum. -/
noncomputable def heightOneSpectrumEquivCodimensionOnePointSpec
    (R : Type u) [CommRing R] [IsDedekindDomain R] :
    HeightOneSpectrum R ≃ CodimensionOnePoint (Spec (.of R)) where
  toFun v :=
    let y : Spec (.of R) := ⟨v.asIdeal, v.isPrime⟩
    ⟨y, by
      calc
        Order.coheight y = y.asIdeal.height := (idealHeight_eq_coheight (.of R) y).symm
        _ = 1 := heightOneSpectrum_height R v⟩
  invFun x :=
    ⟨x.1.asIdeal, x.1.isPrime, by
      apply x.1.asIdeal.ne_bot_of_height_eq_one
      rw [idealHeight_eq_coheight]
      exact x.2⟩
  left_inv v := by
    ext
    rfl
  right_inv x := by
    ext
    rfl

private noncomputable def codimensionOnePointEquivOfIso
    {Y Z : Scheme.{u}} (e : Y ≅ Z) :
    CodimensionOnePoint Y ≃ CodimensionOnePoint Z where
  toFun y :=
    ⟨e.hom y.1, by
      calc
        Order.coheight (e.hom y.1) = Order.coheight y.1 :=
          coheight_eq_of_isOpenImmersion e.hom
        _ = 1 := y.2⟩
  invFun z :=
    ⟨e.inv z.1, by
      calc
        Order.coheight (e.inv z.1) = Order.coheight z.1 :=
          coheight_eq_of_isOpenImmersion e.inv
        _ = 1 := z.2⟩
  left_inv y := by
    ext
    exact congrArg (fun f : Y ⟶ Y ↦ f y.1) e.hom_inv_id
  right_inv z := by
    ext
    exact congrArg (fun f : Z ⟶ Z ↦ f z.1) e.inv_hom_id

private noncomputable def codimensionOnePointOpenEquiv
    (X : Scheme.{u}) (U : X.Opens) :
    CodimensionOnePoint U ≃ {x : CodimensionOnePoint X // x.1 ∈ U} where
  toFun x :=
    ⟨⟨x.1.1, by
      calc
        Order.coheight x.1.1 = Order.coheight x.1 :=
          coheight_eq_of_isOpenImmersion U.ι
        _ = 1 := x.2⟩, x.1.2⟩
  invFun x :=
    let y : (U : Scheme) := ⟨x.1.1, x.2⟩
    ⟨y, by
      calc
        Order.coheight y = Order.coheight x.1.1 :=
          (coheight_eq_of_isOpenImmersion U.ι).symm
        _ = 1 := x.1.2⟩
  left_inv x := by
    ext
    rfl
  right_inv x := by
    ext
    rfl

/-- Height-one primes of the coordinate ring of a Dedekind affine open are exactly the
ambient codimension-one points which lie in that open. -/
noncomputable def affineOpenHeightOneSpectrumEquiv
    (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U)
    [IsDedekindDomain Γ(X, U)] :
    HeightOneSpectrum Γ(X, U) ≃ {x : CodimensionOnePoint X // x.1 ∈ U} :=
  (heightOneSpectrumEquivCodimensionOnePointSpec Γ(X, U)).trans <|
    (codimensionOnePointEquivOfIso hU.isoSpec.symm).trans <|
      codimensionOnePointOpenEquiv X U

/-- The ambient point underlying the chart equivalence is the image under the canonical open
immersion from the affine spectrum. -/
@[simp]
lemma affineOpenHeightOneSpectrumEquiv_apply_val
    (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U)
    [IsDedekindDomain Γ(X, U)] (v : HeightOneSpectrum Γ(X, U)) :
    (affineOpenHeightOneSpectrumEquiv X U hU v).1.1 =
      hU.fromSpec ⟨v.asIdeal, v.isPrime⟩ := by
  rfl

/-- The inverse chart equivalence recovers the prime ideal attached to the corresponding point
of the affine open. -/
@[simp]
lemma affineOpenHeightOneSpectrumEquiv_symm_asIdeal
    (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U)
    [IsDedekindDomain Γ(X, U)]
    (x : {x : CodimensionOnePoint X // x.1 ∈ U}) :
    ((affineOpenHeightOneSpectrumEquiv X U hU).symm x).asIdeal =
      (hU.primeIdealOf ⟨x.1.1, x.2⟩).asIdeal := by
  rfl

end MazurTorsion.AlgebraicGeometry.AffineChart

namespace MazurTorsion.AlgebraicGeometry.PicardIso

open CategoryTheory MonoidalCategory
open _root_.AlgebraicGeometry
open TauCeti.AlgebraicGeometry

/-- Pullback along a scheme isomorphism is an equivalence of the underlying categories of
sheaves of modules. This uses only Mathlib's pullback identity, composition, and congruence
isomorphisms; no tensor compatibility is needed here. -/
noncomputable def modulesEquivalence {Y Z : Scheme.{u}} (e : Y ≅ Z) :
    Z.Modules ≌ Y.Modules :=
  CategoryTheory.Equivalence.mk
    (Scheme.Modules.pullback e.hom)
    (Scheme.Modules.pullback e.inv)
    (((Scheme.Modules.pullbackComp e.inv e.hom) ≪≫
      Scheme.Modules.pullbackCongr e.inv_hom_id) ≪≫
      Scheme.Modules.pullbackId Z).symm
    (((Scheme.Modules.pullbackComp e.hom e.inv) ≪≫
      Scheme.Modules.pullbackCongr e.hom_inv_id) ≪≫
      Scheme.Modules.pullbackId Y)

/-- An upstream-compatible sufficient datum for transporting AINTLIB Picard groups along a
scheme isomorphism: strong monoidality of sheaf-module pullback for the two AINTLIB tensor
structures. The pinned upstream AINTLIB source proves this for every scheme morphism, but that
pullback-monoidal cone is not present in the current checked import graph. -/
noncomputable def PullbackMonoidalData {Y Z : Scheme.{u}} (e : Y ≅ Z) : Type _ :=
  letI := Scheme.Modules.monoidalCategory Z
  letI := Scheme.Modules.monoidalCategory Y
  (Scheme.Modules.pullback e.hom).Monoidal

/-- Strong monoidality of pullback turns the underlying module-category equivalence into an
additive equivalence of AINTLIB Picard groups. -/
noncomputable def equivOfPullbackMonoidal {Y Z : Scheme.{u}} (e : Y ≅ Z)
    (hmonoidal : PullbackMonoidalData e) :
    PicardGroup Z ≃+ PicardGroup Y := by
  letI := Scheme.Modules.monoidalCategory Z
  letI := Scheme.Modules.monoidalCategory Y
  letI : (Scheme.Modules.pullback e.hom).Monoidal := hmonoidal
  let E := modulesEquivalence e
  letI : E.functor.Monoidal := by
    change (Scheme.Modules.pullback e.hom).Monoidal
    infer_instance
  exact MulEquiv.toAdditive (Units.mapEquiv (Skeleton.mulEquiv E))

/-- The Picard equivalence is induced on underlying isomorphism classes by sheaf-module
pullback. -/
@[simp]
lemma equivOfPullbackMonoidal_apply_val {Y Z : Scheme.{u}} (e : Y ≅ Z)
    (hmonoidal : PullbackMonoidalData e) (p : Scheme.Pic Z) :
    letI := Scheme.Modules.monoidalCategory Z
    letI := Scheme.Modules.monoidalCategory Y
    (Additive.toMul
      (equivOfPullbackMonoidal e hmonoidal (Additive.ofMul p))).val =
      (Scheme.Modules.pullback e.hom).mapSkeleton.obj p.val := by
  rfl

/-- The Picard equivalence does not depend on the chosen strong monoidal structure. -/
theorem equivOfPullbackMonoidal_independent
    {Y Z : Scheme.{u}} (e : Y ≅ Z)
    (h₁ h₂ : PullbackMonoidalData e) :
    equivOfPullbackMonoidal e h₁ = equivOfPullbackMonoidal e h₂ := by
  letI := Scheme.Modules.monoidalCategory Z
  letI := Scheme.Modules.monoidalCategory Y
  ext p
  apply Units.ext
  simpa using
    (equivOfPullbackMonoidal_apply_val e h₁ (Additive.toMul p)).trans
      (equivOfPullbackMonoidal_apply_val e h₂ (Additive.toMul p)).symm

/-- The inverse Picard equivalence is induced on isomorphism classes by pullback along the
inverse scheme isomorphism. -/
@[simp]
lemma equivOfPullbackMonoidal_symm_apply_val
    {Y Z : Scheme.{u}} (e : Y ≅ Z)
    (hmonoidal : PullbackMonoidalData e) (p : Scheme.Pic Y) :
    letI := Scheme.Modules.monoidalCategory Z
    letI := Scheme.Modules.monoidalCategory Y
    (Additive.toMul
      ((equivOfPullbackMonoidal e hmonoidal).symm (Additive.ofMul p))).val =
      (Scheme.Modules.pullback e.inv).mapSkeleton.obj p.val := by
  rfl

end MazurTorsion.AlgebraicGeometry.PicardIso

namespace MazurTorsion.AlgebraicGeometry.AffineChart

open CategoryTheory MonoidalCategory
open _root_.AlgebraicGeometry
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open IsDedekindDomain WithZero
open scoped nonZeroDivisors

/-- The exact local compatibility needed to compare the affine Dedekind divisor construction
with the scheme-theoretic divisor on a curve. The equality is an equality of additive order
homomorphisms, not merely an equality at a chosen rational function. -/
structure DedekindOrderCompatibility
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U) : Prop where
  isDedekindDomain : IsDedekindDomain Γ(X, U)
  order_eq :
    letI := isDedekindDomain
    letI : IsFractionRing Γ(X, U) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U hU
    ∀ v : HeightOneSpectrum Γ(X, U),
      WeilDivisor.adicOrd Γ(X, U) X.functionField v =
        SchemeWeilDivisor.orderAt
          ((affineOpenHeightOneSpectrumEquiv X U hU v).1)

private lemma withZeroMulInt_orderMonoidIso_eq_refl (e : ℤᵐ⁰ ≃*o ℤᵐ⁰) :
    e = OrderMonoidIso.refl ℤᵐ⁰ := by
  let f : Multiplicative ℤ ≃*o Multiplicative ℤ :=
    OrderMonoidIso.unitsWithZero.symm.trans
      (e.unitsCongr.trans OrderMonoidIso.unitsWithZero)
  have hf : f = OrderMonoidIso.refl (Multiplicative ℤ) := Subsingleton.elim _ _
  ext x
  by_cases hx : x = 0
  · subst x
    simp
  · let ux : (ℤᵐ⁰)ˣ := Units.mk0 x hx
    have hfx := DFunLike.congr_fun hf (OrderMonoidIso.unitsWithZero ux)
    have hu : e.unitsCongr ux = ux := by
      apply OrderMonoidIso.unitsWithZero.injective
      simpa [f, ux] using hfx
    exact congrArg Units.val hu

private lemma valuation_eq_of_isEquiv_of_surjective
    {F : Type u} [Field F]
    {v w : Valuation F ℤᵐ⁰}
    [v.IsRankOneDiscrete] [w.IsRankOneDiscrete]
    (h : v.IsEquiv w) (hv : Function.Surjective v) (hw : Function.Surjective w) :
    v = w := by
  let ev := Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt v
  let ew := Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt w
  let e : ℤᵐ⁰ ≃*o ℤᵐ⁰ := ev.symm.trans (h.orderMonoidIso.trans ew)
  have he : e = OrderMonoidIso.refl ℤᵐ⁰ := withZeroMulInt_orderMonoidIso_eq_refl e
  ext x
  have hx := DFunLike.congr_fun he (ev (v.restrict x))
  change ew (h.orderMonoidIso (ev.symm (ev (v.restrict x)))) = ev (v.restrict x) at hx
  rw [ev.symm_apply_apply, h.orderMonoidIso_spec,
    Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
      hw,
    Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
      hv] at hx
  exact hx.symm

private lemma toAdd_unzero_inv_eq_neg_log (a : ℤᵐ⁰) (hai : a⁻¹ ≠ 0) :
    Multiplicative.toAdd (WithZero.unzero hai) = -WithZero.log a := by
  have hcoe : ((WithZero.unzero hai : Multiplicative ℤ) : ℤᵐ⁰) = a⁻¹ :=
    WithZero.coe_unzero hai
  have hlog := congrArg WithZero.log hcoe
  change Multiplicative.toAdd (WithZero.unzero hai) = WithZero.log (a⁻¹) at hlog
  simpa only [WithZero.log_inv] using hlog

private lemma algebraMap_eq_mapToFractionRing
    (R S K : Type u)
    [CommRing R] [IsDedekindDomain R]
    [CommRing S] [IsDomain S] [Field K]
    [Algebra R S] [Algebra R K] [Algebra S K]
    [IsScalarTower R S K]
    [IsFractionRing R K] [IsFractionRing S K]
    (v : HeightOneSpectrum R) [IsLocalization.AtPrime S v.asIdeal] :
    algebraMap S K =
      (Localization.mapToFractionRing K v.asIdeal.primeCompl S
        v.asIdeal.primeCompl_le_nonZeroDivisors).toRingHom := by
  apply IsLocalization.ringHom_ext v.asIdeal.primeCompl
  ext r
  change algebraMap S K (algebraMap R S r) = _
  rw [← IsScalarTower.algebraMap_apply R S K]
  simp

private lemma map_top_eq_localizationSubalgebra
    (R S K : Type u)
    [CommRing R] [IsDedekindDomain R]
    [CommRing S] [IsDomain S] [Field K]
    [Algebra R S] [Algebra R K] [Algebra S K]
    [IsScalarTower R S K]
    [IsFractionRing R K] [IsFractionRing S K]
    (v : HeightOneSpectrum R) [IsLocalization.AtPrime S v.asIdeal] :
    Subring.map (algebraMap S K) ⊤ =
      (Localization.subalgebra.ofField K v.asIdeal.primeCompl
        v.asIdeal.primeCompl_le_nonZeroDivisors).toSubring := by
  ext x
  rw [Subring.mem_map, algebraMap_eq_mapToFractionRing R S K v]
  simp only [Subring.mem_top, true_and]
  change (∃ y, Localization.mapToFractionRing K v.asIdeal.primeCompl S
      v.asIdeal.primeCompl_le_nonZeroDivisors y = x) ↔ _
  rw [show x ∈ (Localization.subalgebra.ofField K v.asIdeal.primeCompl
      v.asIdeal.primeCompl_le_nonZeroDivisors).toSubring ↔
      x ∈ (Localization.mapToFractionRing K v.asIdeal.primeCompl S
        v.asIdeal.primeCompl_le_nonZeroDivisors).range by
    rw [Localization.subalgebra.mem_range_mapToFractionRing_iff_ofField]
    rfl]
  constructor <;> rintro ⟨y, rfl⟩ <;> exact ⟨y, rfl⟩

private lemma adicValuation_eq_localizedValuation
    (R S K : Type u)
    [CommRing R] [IsDedekindDomain R]
    [CommRing S] [IsDomain S] [Field K]
    [Algebra R S] [Algebra R K] [Algebra S K]
    [IsScalarTower R S K]
    [IsFractionRing R K] [IsFractionRing S K]
    (v : HeightOneSpectrum R) [IsLocalization.AtPrime S v.asIdeal] :
    letI : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S v.asIdeal
    letI : IsDiscreteValuationRing S :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R v.ne_bot S
    v.valuation K = (IsDiscreteValuationRing.maximalIdeal S).valuation K := by
  letI : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S v.asIdeal
  letI : IsDiscreteValuationRing S :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R v.ne_bot S
  have hsubring :
      (v.valuation K).valuationSubring.toSubring =
        ((IsDiscreteValuationRing.maximalIdeal S).valuation K).valuationSubring.toSubring := by
    rw [← v.valuationSubringAtPrime_eq_valuationSubring,
      v.valuationSubringAtPrime_toSubring,
      ← map_top_eq_localizationSubalgebra R S K v,
      IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring]
  have hequiv :
      (v.valuation K).IsEquiv
        ((IsDiscreteValuationRing.maximalIdeal S).valuation K) := by
    rw [Valuation.isEquiv_iff_valuationSubring]
    apply ValuationSubring.ext
    intro x
    exact SetLike.ext_iff.mp hsubring x
  apply valuation_eq_of_isEquiv_of_surjective hequiv
  · exact v.valuation_surjective K
  · exact (IsDiscreteValuationRing.maximalIdeal S).valuation_surjective K

private lemma adicOrd_eq_localizedOrdFrac
    (R S K : Type u)
    [CommRing R] [IsDedekindDomain R]
    [CommRing S] [IsDomain S] [Field K]
    [Algebra R S] [Algebra R K] [Algebra S K]
    [IsScalarTower R S K]
    [IsFractionRing R K] [IsFractionRing S K]
    (v : HeightOneSpectrum R) [IsLocalization.AtPrime S v.asIdeal]
    (u : Additive Kˣ) :
    letI : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S v.asIdeal
    letI : IsDiscreteValuationRing S :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R v.ne_bot S
    WeilDivisor.adicOrd R K v u =
      Multiplicative.toAdd
        (WithZero.unzero
          (show Ring.ordFrac S ((Additive.toMul u : Kˣ) : K) ≠ 0 by simp)) := by
  letI : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S v.asIdeal
  letI : IsDiscreteValuationRing S :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R v.ne_bot S
  let k : K := ((Additive.toMul u : Kˣ) : K)
  let a : ℤᵐ⁰ := v.valuation K k
  have ha : a ≠ 0 := (v.valuation K).ne_zero_iff.mpr (Units.ne_zero _)
  have hord : Ring.ordFrac S k = a⁻¹ := by
    rw [Ring.ordFrac_eq_valuation_inv,
      ← adicValuation_eq_localizedValuation R S K v]
  rw [WeilDivisor.adicOrd_apply]
  change -WithZero.log a = _
  rw [← toAdd_unzero_inv_eq_neg_log a (inv_ne_zero ha)]
  congr 1
  apply WithZero.coe_injective
  simpa [k] using hord.symm

/-- On a Dedekind affine chart, the normalized height-one-prime order agrees with Tau Ceti's
scheme-theoretic order at the corresponding ambient codimension-one point. -/
theorem affineOpen_order_eq
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
    [IsDedekindDomain Γ(X, U)] :
    letI : IsFractionRing Γ(X, U) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U hU
    ∀ v : HeightOneSpectrum Γ(X, U),
      WeilDivisor.adicOrd Γ(X, U) X.functionField v =
        SchemeWeilDivisor.orderAt
          ((affineOpenHeightOneSpectrumEquiv X U hU v).1) := by
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  intro v
  let e := affineOpenHeightOneSpectrumEquiv X U hU
  let x : CodimensionOnePoint X := (e v).1
  let y : U := ⟨x.1, (e v).2⟩
  have hprime : (hU.primeIdealOf y).asIdeal = v.asIdeal := by
    simpa [e, x, y] using
      (affineOpenHeightOneSpectrumEquiv_symm_asIdeal X U hU (e v)).symm
  letI : Algebra Γ(X, U) (X.presheaf.stalk x.1) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf y
  letI : IsLocalization v.asIdeal.primeCompl (X.presheaf.stalk x.1) := by
    have hcompl : v.asIdeal.primeCompl =
        (hU.primeIdealOf y).asIdeal.primeCompl := by
      ext r
      simp only [Ideal.mem_primeCompl_iff]
      rw [hprime]
    rw [hcompl]
    exact hU.isLocalization_stalk y
  letI : IsScalarTower Γ(X, U) (X.presheaf.stalk x.1) X.functionField :=
    functionField_isScalarTower X U y
  apply AddMonoidHom.ext
  intro f
  rw [SchemeWeilDivisor.orderAt_apply]
  rw [Scheme.ord_eq_unzero_ordHom x.2 (Units.ne_zero _)]
  simpa [Scheme.ordHom] using
    (adicOrd_eq_localizedOrdFrac Γ(X, U) (X.presheaf.stalk x.1)
      X.functionField v f)

/-- For an affine open with Dedekind coordinate ring, the order compatibility required by the
chart divisor API is automatic. The remaining geometric obligation is precisely the Dedekind
domain instance for `Γ(X, U)`. -/
theorem dedekindOrderCompatibilityOfIsDedekindDomain
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
    [IsDedekindDomain Γ(X, U)] :
    DedekindOrderCompatibility X U hU where
  isDedekindDomain := inferInstance
  order_eq := affineOpen_order_eq X U hU

/-- For a nonempty affine open of an integral locally Noetherian scheme, the remaining
Dedekind-domain boundary is exactly dimension at most one plus integral closedness. Domain and
Noetherian hypotheses already follow from the ambient assumptions. -/
theorem affineOpen_isDedekindDomain_iff
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U) :
    IsDedekindDomain Γ(X, U) ↔
      Ring.DimensionLEOne Γ(X, U) ∧ IsIntegrallyClosed Γ(X, U) := by
  constructor
  · intro h
    letI : IsDedekindDomain Γ(X, U) := h
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hdim, hnormal⟩
    letI : Ring.DimensionLEOne Γ(X, U) := hdim
    letI : IsIntegrallyClosed Γ(X, U) := hnormal
    letI : IsNoetherianRing Γ(X, U) :=
      IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    letI : IsIntegralClosure Γ(X, U) Γ(X, U) (FractionRing Γ(X, U)) :=
      (isIntegrallyClosed_iff_isIntegralClosure (FractionRing Γ(X, U))).mp hnormal
    exact
      { toIsDomain := inferInstance
        toIsDedekindRing :=
          { toIsNoetherian := inferInstance
            toDimensionLEOne := inferInstance
            toIsIntegralClosure := inferInstance } }

/-- The missing commutative-algebra implication for one affine smooth-relative-curve map. This
map-specific boundary asks only for the dimension and normality consequences actually consumed
by the chart divisor API; it does not assert the implication uniformly over arbitrary bases. -/
def SmoothRelativeCurveRingConditions
    (R A : Type u) [CommRing R] [CommRing A] (f : R →+* A) : Prop :=
  RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) f →
    Ring.DimensionLEOne A ∧ IsIntegrallyClosed A

/-- A standard-smooth relative curve chart over a field has dimension at most one. The proof
uses an étale presentation over the one-variable polynomial ring and quasi-finite contraction
of prime chains. -/
theorem dimensionLEOne_of_standardSmoothRelDimOne_over_field
    (K A : Type u) [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 K A] :
    Ring.DimensionLEOne A := by
  obtain ⟨g, hg⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial 1 K A
  letI : Algebra (MvPolynomial (Fin 1) K) A := g.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin 1) K) A := by
    rw [← RingHom.etale_algebraMap]
    exact hg
  haveI : Algebra.QuasiFinite (MvPolynomial (Fin 1) K) A := inferInstance
  have hstrict : StrictMono
      (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin 1) K) A)) := by
    intro P Q hPQ
    have hle : P.asIdeal.under (MvPolynomial (Fin 1) K) ≤
        Q.asIdeal.under (MvPolynomial (Fin 1) K) :=
      Ideal.comap_mono hPQ.le
    refine lt_of_le_of_ne hle ?_
    intro heq
    have hPQeq : P.asIdeal = Q.asIdeal :=
      Algebra.QuasiFinite.eq_of_le_of_under_eq
        (R := MvPolynomial (Fin 1) K) P.asIdeal Q.asIdeal hPQ.le
          (congrArg PrimeSpectrum.asIdeal heq)
    exact hPQ.ne (PrimeSpectrum.ext hPQeq)
  have hkrull : Ring.KrullDimLE 1 A := by
    rw [Ring.krullDimLE_iff]
    calc
      ringKrullDim A ≤ ringKrullDim (MvPolynomial (Fin 1) K) :=
        Order.krullDim_le_of_strictMono _ hstrict
      _ = 1 := by
        rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
          ringKrullDim_eq_zero_of_field]
        simp
      _ ≤ 1 := le_rfl
  letI : Ring.KrullDimLE 1 A := hkrull
  exact
    { maximalOfPrime := fun hne hp => hp.isMaximal_of_ne_bot hne }

/-- A standard-smooth relative curve domain over a field is integrally closed.

Tau Ceti proves that every prime localization is a valuation ring. In particular, every maximal
localization is integrally closed, so integral closedness follows from the maximal-localization
criterion. -/
theorem isIntegrallyClosed_of_standardSmoothRelDimOne_over_field
    (K A : Type u) [Field K] [CommRing A] [IsDomain A]
    (f : K →+* A) (hf : f.IsStandardSmoothOfRelativeDimension 1) :
    IsIntegrallyClosed A := by
  letI : Algebra K A := f.toAlgebra
  letI : Algebra.IsStandardSmoothOfRelativeDimension 1 K A := hf.toAlgebra
  letI : Algebra.IsStandardSmooth K A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  apply IsIntegrallyClosed.of_localization_maximal
  intro Q _ hmax
  letI : Q.IsPrime := hmax.isPrime
  letI : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  have hvaluation : ValuationRing (Localization.AtPrime Q) :=
    _root_.TauCeti.RingTheory.valuationRing_localizationAtPrime_of_isStandardSmoothOfRelativeDimension_one
      K A Q
  have hnormal : IsIntegrallyClosed (Localization.AtPrime Q) ∧
      ∀ P : Ideal (Localization.AtPrime Q), P ≠ ⊥ → P.IsPrime →
        P = IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
      (Localization.AtPrime Q)).out 1 3).mp hvaluation
  exact hnormal.1

private theorem dimensionLEOne_of_ringHom_standardSmoothRelDimOne_over_field
    (K A : Type u) [Field K] [CommRing A] [IsDomain A]
    (f : K →+* A) (hf : f.IsStandardSmoothOfRelativeDimension 1) :
    Ring.DimensionLEOne A := by
  letI : Algebra K A := f.toAlgebra
  letI : Algebra.IsStandardSmoothOfRelativeDimension 1 K A := hf.toAlgebra
  exact dimensionLEOne_of_standardSmoothRelDimOne_over_field K A

/-- A locally standard-smooth relative curve chart over a field has dimension at most one.
The local standard charts cover the unit ideal, so every maximal-prime height can be computed
after localizing at one chart element outside that prime. -/
theorem dimensionLEOne_of_locallyStandardSmoothRelDimOne_over_field
    (K A : Type u) [Field K] [CommRing A] [IsDomain A]
    (f : K →+* A)
    (hf : RingHom.Locally
      (RingHom.IsStandardSmoothOfRelativeDimension 1) f) :
    Ring.DimensionLEOne A := by
  obtain ⟨s, hs, hstd⟩ := hf
  have hkrull : Ring.KrullDimLE 1 A := by
    rw [Ring.krullDimLE_iff, ringKrullDim_le_iff_isMaximal_height_le]
    intro P hP
    letI : P.IsPrime := hP.isPrime
    have hnot : ¬ s ⊆ (P : Set A) := by
      intro hsub
      apply hP.ne_top
      rw [eq_top_iff, ← hs]
      exact Ideal.span_le.mpr hsub
    obtain ⟨t, hts, htP⟩ := Set.not_subset.mp hnot
    have ht0 : t ≠ 0 := by
      intro ht
      apply htP
      rw [ht]
      exact P.zero_mem
    letI : IsDomain (Localization.Away t) := Localization.Away.isDomain ht0
    letI : Ring.DimensionLEOne (Localization.Away t) :=
      dimensionLEOne_of_ringHom_standardSmoothRelDimOne_over_field K
        (Localization.Away t) ((algebraMap A (Localization.Away t)).comp f) (hstd t hts)
    have hdisj : Disjoint (Submonoid.powers t : Set A) (P : Set A) :=
      (Ideal.disjoint_powers_iff_notMem_of_isPrime t).mpr htP
    letI : (P.map (algebraMap A (Localization.Away t))).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint
        (Submonoid.powers t) (Localization.Away t) P inferInstance hdisj
    rw [← IsLocalization.height_map_of_disjoint
      (S := Localization.Away t) (Submonoid.powers t) P hdisj]
    exact (Ideal.height_le_ringKrullDim_of_isPrime).trans
      (Ring.krullDimLE_iff.mp
        (inferInstance : Ring.KrullDimLE 1 (Localization.Away t)))
  letI : Ring.KrullDimLE 1 A := hkrull
  exact
    { maximalOfPrime := fun hne hp => hp.isMaximal_of_ne_bot hne }

/-- A locally standard-smooth relative curve domain over a field is integrally closed.

Each nonzero member of the standard-open cover has an integrally closed localization by the
standard-smooth theorem. If an element of the fraction field is integral, each such localization
puts a suitable power of the cover element times it back in the original ring. Since those cover
elements span the unit ideal, the localized membership statements glue in the original ring. -/
theorem isIntegrallyClosed_of_locallyStandardSmoothRelDimOne_over_field
    (K A : Type u) [Field K] [CommRing A] [IsDomain A]
    (f : K →+* A)
    (hf : RingHom.Locally
      (RingHom.IsStandardSmoothOfRelativeDimension 1) f) :
    IsIntegrallyClosed A := by
  obtain ⟨s, hs, hstd⟩ := hf
  apply (isIntegrallyClosed_iff (FractionRing A)).mpr
  intro x hx
  let M : Submodule A (FractionRing A) :=
    LinearMap.range (Algebra.linearMap A (FractionRing A))
  have hxM : x ∈ M := by
    apply Submodule.mem_of_span_eq_top_of_smul_pow_mem M s hs x
    intro t
    by_cases ht : (t : A) = 0
    · refine ⟨1, ?_⟩
      simp [ht, M]
    · have hpowers : Submonoid.powers (t : A) ≤ A⁰ := by
        rw [Submonoid.powers_le]
        simpa [mem_nonZeroDivisors_iff_ne_zero]
      letI : IsDomain (Localization.Away (t : A)) :=
        Localization.Away.isDomain ht
      letI : Algebra (Localization.Away (t : A)) (FractionRing A) :=
        IsLocalization.localizationAlgebraOfSubmonoidLe
          (Localization.Away (t : A)) (FractionRing A)
          (Submonoid.powers (t : A)) A⁰ hpowers
      haveI : IsScalarTower A (Localization.Away (t : A)) (FractionRing A) :=
        IsLocalization.localization_isScalarTower_of_submonoid_le
          (Localization.Away (t : A)) (FractionRing A)
          (Submonoid.powers (t : A)) A⁰ hpowers
      letI : IsFractionRing (Localization.Away (t : A)) (FractionRing A) :=
        IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
          (Submonoid.powers (t : A)) (Localization.Away (t : A)) (FractionRing A)
      have hnormal : IsIntegrallyClosed (Localization.Away (t : A)) :=
        isIntegrallyClosed_of_standardSmoothRelDimOne_over_field K
          (Localization.Away (t : A))
          ((algebraMap A (Localization.Away (t : A))).comp f) (hstd t t.2)
      obtain ⟨y, hy⟩ :=
        (isIntegrallyClosed_iff (FractionRing A)).mp hnormal hx.tower_top
      obtain ⟨⟨a, d⟩, hd⟩ :=
        IsLocalization.surj (Submonoid.powers (t : A)) y
      obtain ⟨n, hn⟩ := d.2
      refine ⟨n, ?_⟩
      rw [Algebra.smul_def]
      refine ⟨a, ?_⟩
      change algebraMap A (FractionRing A) a =
        algebraMap A (FractionRing A) ((t : A) ^ n) * x
      have hd' := congrArg
        (algebraMap (Localization.Away (t : A)) (FractionRing A)) hd
      rw [map_mul] at hd'
      simp_rw [← IsScalarTower.algebraMap_apply A
        (Localization.Away (t : A)) (FractionRing A)] at hd'
      rw [hy, ← hn] at hd'
      simpa [mul_comm] using hd'.symm
  exact hxM

/-- The mapwise normality predicate for a locally standard-smooth relative curve domain. The
predicate is retained as a compatibility interface and is discharged unconditionally below. -/
def SmoothRelativeCurveNormality
    (K A : Type u) [Field K] [CommRing A] [IsDomain A]
    (f : K →+* A) : Prop :=
  RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) f →
    IsIntegrallyClosed A

/-- The normality predicate for a relative curve domain over a field is unconditional. -/
theorem smoothRelativeCurveNormality_of_field
    (K A : Type u) [Field K] [CommRing A] [IsDomain A]
    (f : K →+* A) : SmoothRelativeCurveNormality K A f :=
  isIntegrallyClosed_of_locallyStandardSmoothRelDimOne_over_field K A f

/-- Over a field, the normality-only boundary and the checked dimension theorem supply the
existing two-part smooth-relative-curve ring conditions. -/
theorem smoothRelativeCurveRingConditions_of_field_of_normality
    (K A : Type u) [Field K] [CommRing A] [IsDomain A]
    (f : K →+* A) (hnormal : SmoothRelativeCurveNormality K A f) :
    SmoothRelativeCurveRingConditions K A f := by
  intro hlocal
  exact ⟨dimensionLEOne_of_locallyStandardSmoothRelDimOne_over_field K A f hlocal,
    hnormal hlocal⟩

/-- Over a field-domain chart, the two-part smooth-relative-curve boundary is exactly the
normality boundary because relative dimension one already forces dimension at most one. -/
theorem smoothRelativeCurveRingConditions_iff_normality_of_field
    (K A : Type u) [Field K] [CommRing A] [IsDomain A]
    (f : K →+* A) :
    SmoothRelativeCurveRingConditions K A f ↔
      SmoothRelativeCurveNormality K A f := by
  constructor
  · intro h hlocal
    exact (h hlocal).2
  · exact smoothRelativeCurveRingConditions_of_field_of_normality K A f

/-- A locally standard-smooth relative curve domain over a field satisfies both ring conditions
needed by the affine divisor API. -/
theorem smoothRelativeCurveRingConditions_of_field
    (K A : Type u) [Field K] [CommRing A] [IsDomain A]
    (f : K →+* A) : SmoothRelativeCurveRingConditions K A f :=
  smoothRelativeCurveRingConditions_of_field_of_normality K A f
    (smoothRelativeCurveNormality_of_field K A f)

/-- The map-specific smooth-relative-curve ring conditions directly provide the Dedekind order
compatibility required to construct the chart divisor line bundle. -/
theorem dedekindOrderCompatibilityOfSmoothRelativeCurveRingConditions
    (R : Type u) [CommRing R]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of R)) [SmoothOfRelativeDimension 1 f]
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
    (h : SmoothRelativeCurveRingConditions
      Γ(Spec (.of R), ⊤) Γ(X, U) (f.appLE ⊤ U le_top).hom) :
    DedekindOrderCompatibility X U hU := by
  have hlocal : RingHom.Locally
      (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (f.appLE ⊤ U le_top).hom :=
    HasRingHomProperty.appLE (@SmoothOfRelativeDimension 1) f inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have hDedekind : IsDedekindDomain Γ(X, U) :=
    (affineOpen_isDedekindDomain_iff X U hU).2 (h hlocal)
  letI : IsDedekindDomain Γ(X, U) := hDedekind
  exact dedekindOrderCompatibilityOfIsDedekindDomain X U hU

/-- Every nonempty affine chart of a smooth relative curve over a field has the Dedekind order
compatibility required by the divisor API. -/
theorem dedekindOrderCompatibilityOfSmoothRelativeCurve
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U) :
    DedekindOrderCompatibility X U hU := by
  letI : Field Γ(Spec (.of K), ⊤) :=
    ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField K)).toField
  apply dedekindOrderCompatibilityOfSmoothRelativeCurveRingConditions K X f U hU
  exact smoothRelativeCurveRingConditions_of_field
    Γ(Spec (.of K), ⊤) Γ(X, U) (f.appLE ⊤ U le_top).hom

/-- Compatibility alias retaining the historical normality-input API. The hypothesis is no
longer needed because locally standard-smooth relative curve domains are integrally closed. -/
theorem dedekindOrderCompatibilityOfSmoothRelativeCurveNormality
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
    (_hnormal : RingHom.Locally
      (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (f.appLE ⊤ U le_top).hom → IsIntegrallyClosed Γ(X, U)) :
    DedekindOrderCompatibility X U hU :=
  dedekindOrderCompatibilityOfSmoothRelativeCurve K X f U hU

/-- A sufficient datum for transporting AINTLIB Picard groups along the affine-chart
isomorphism: strong monoidality of sheaf-module pullback for the AINTLIB tensor structures. -/
abbrev ChartPullbackMonoidalData
    (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U) : Type _ :=
  PicardIso.PullbackMonoidalData hU.isoSpec

/-- Conditional Picard equivalence induced by pullback along
`U ≅ Spec Γ(X, U)`. No geometric assumptions beyond the supplied monoidality datum are used.
-/
noncomputable def picardEquivSpecToOpen
    (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U)
    (hmonoidal : ChartPullbackMonoidalData X U hU) :
    PicardGroup (Spec (.of Γ(X, U))) ≃+ PicardGroup U :=
  PicardIso.equivOfPullbackMonoidal hU.isoSpec hmonoidal

namespace DedekindOrderCompatibility

variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
variable (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
variable (h : DedekindOrderCompatibility X U hU)

/-- The scheme orders on ambient codimension-one points lying in an affine Dedekind chart form
an order system. Its finite-support proof is transported from the coordinate ring. -/
noncomputable def ambientOrderSystem :
    OrderSystem {x : CodimensionOnePoint X // x.1 ∈ U} (Additive X.functionFieldˣ) := by
  letI := h.isDedekindDomain
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  let e := affineOpenHeightOneSpectrumEquiv X U hU
  refine
    { ord := fun x ↦ SchemeWeilDivisor.orderAt x.1
      finite_support := ?_ }
  intro g
  refine
    ((WeilDivisor.OrderSystem.ofDedekindDomain Γ(X, U) X.functionField).finite_support g).image
      e |>.subset ?_
  intro x hx
  refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  rw [Function.mem_support] at hx ⊢
  rw [WeilDivisor.OrderSystem.ofDedekindDomain_ord, h.order_eq, e.apply_symm_apply]
  exact hx

/-- The transported chart order system uses the scheme-theoretic order homomorphism. -/
@[simp]
lemma ambientOrderSystem_ord
    (x : {x : CodimensionOnePoint X // x.1 ∈ U}) :
    (h.ambientOrderSystem X U hU).ord x =
      SchemeWeilDivisor.orderAt x.1 := by
  rfl

/-- The canonical chart-point equivalence using the Dedekind instance supplied by the
compatibility hypothesis. -/
noncomputable def pointEquiv :
    HeightOneSpectrum Γ(X, U) ≃ {x : CodimensionOnePoint X // x.1 ∈ U} := by
  letI := h.isDedekindDomain
  exact affineOpenHeightOneSpectrumEquiv X U hU

/-- Reindex affine Weil divisors along the canonical equivalence between height-one primes and
ambient codimension-one points in the chart. -/
noncomputable def divisorEquiv :
    WeilDivisor (HeightOneSpectrum Γ(X, U)) ≃+
      WeilDivisor {x : CodimensionOnePoint X // x.1 ∈ U} :=
  Finsupp.domCongr (h.pointEquiv X U hU)

/-- The coordinate-ring order system using the instances supplied by the compatibility
hypothesis. -/
noncomputable def affineOrderSystem :
    OrderSystem (HeightOneSpectrum Γ(X, U)) (Additive X.functionFieldˣ) := by
  letI := h.isDedekindDomain
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  exact WeilDivisor.OrderSystem.ofDedekindDomain Γ(X, U) X.functionField

/-- Reindexing the affine principal divisor along the chart-point equivalence gives the
principal divisor formed from scheme orders at the ambient codimension-one points in the chart.
-/
lemma principalDivisor_reindex_eq_ambientPrincipalDivisor
    (g : Additive X.functionFieldˣ) :
    h.divisorEquiv X U hU
        ((h.affineOrderSystem X U hU).principalDivisor g) =
      (h.ambientOrderSystem X U hU).principalDivisor g := by
  letI := h.isDedekindDomain
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  let e := h.pointEquiv X U hU
  ext x
  change Finsupp.domCongr e ((h.affineOrderSystem X U hU).principalDivisor g) x =
    (h.ambientOrderSystem X U hU).principalDivisor g x
  rw [Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain]
  rw [Finsupp.mapDomain_equiv_apply]
  change
    WeilDivisor.coeff ((h.affineOrderSystem X U hU).principalDivisor g) (e.symm x) =
      WeilDivisor.coeff ((h.ambientOrderSystem X U hU).principalDivisor g) x
  rw [WeilDivisor.OrderSystem.coeff_principalDivisor,
    WeilDivisor.OrderSystem.coeff_principalDivisor]
  change WeilDivisor.adicOrd Γ(X, U) X.functionField (e.symm x) g =
    SchemeWeilDivisor.orderAt x.1 g
  rw [h.order_eq]
  change SchemeWeilDivisor.orderAt (e (e.symm x)).1 g =
    SchemeWeilDivisor.orderAt x.1 g
  rw [e.apply_symm_apply]

/-- Divisors on ambient codimension-one points lying in the chart map canonically to the
scheme Picard group of the affine coordinate scheme. -/
noncomputable def divisorToSchemePic :
    WeilDivisor {x : CodimensionOnePoint X // x.1 ∈ U} →+
      PicardGroup (Spec (.of Γ(X, U))) := by
  letI := h.isDedekindDomain
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  exact
    (AffineDedekind.divisorToSchemePic Γ(X, U) X.functionField).comp
      (h.divisorEquiv X U hU).symm.toAddMonoidHom

/-- Evaluation of the chart divisor map is the affine Dedekind construction after inverse
reindexing along `divisorEquiv`. -/
@[simp]
lemma divisorToSchemePic_apply
    (D : WeilDivisor {x : CodimensionOnePoint X // x.1 ∈ U}) :
    h.divisorToSchemePic X U hU D =
      letI := h.isDedekindDomain
      letI : IsFractionRing Γ(X, U) X.functionField :=
        functionField_isFractionRing_of_isAffineOpen X U hU
      AffineDedekind.divisorToSchemePic Γ(X, U) X.functionField
        ((h.divisorEquiv X U hU).symm D) := by
  rfl

/-- The chart-compatible divisor-to-Picard map kills the principal divisor formed from ambient
scheme orders. This is the downstream consumer of both fields of `DedekindOrderCompatibility`.
-/
lemma divisorToSchemePic_principalDivisor
    (g : Additive X.functionFieldˣ) :
    h.divisorToSchemePic X U hU
        ((h.ambientOrderSystem X U hU).principalDivisor g) = 0 := by
  letI := h.isDedekindDomain
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  let e := h.divisorEquiv X U hU
  rw [← h.principalDivisor_reindex_eq_ambientPrincipalDivisor X U hU g]
  change AffineDedekind.divisorToSchemePic Γ(X, U) X.functionField
      (e.symm (e ((h.affineOrderSystem X U hU).principalDivisor g))) = 0
  rw [AddEquiv.symm_apply_apply]
  exact AffineDedekind.divisorToSchemePic_principalDivisor
    Γ(X, U) X.functionField g

/-- The chart divisor-to-Picard map has exactly the principal divisors for the ambient chart
order system as its kernel. Thus the conditional chart comparison gives an exact descent, not
only principal triviality. -/
theorem divisorToSchemePic_kernel :
    (h.divisorToSchemePic X U hU).ker =
      (h.ambientOrderSystem X U hU).principalSubgroup := by
  letI := h.isDedekindDomain
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  let e := h.divisorEquiv X U hU
  apply AddSubgroup.ext
  intro D
  rw [AddMonoidHom.mem_ker]
  constructor
  · intro hD
    have hD' : e.symm D ∈
        (h.affineOrderSystem X U hU).principalSubgroup := by
      change e.symm D ∈
        (WeilDivisor.OrderSystem.ofDedekindDomain
          Γ(X, U) X.functionField).principalSubgroup
      rw [← AffineDedekind.divisorToSchemePic_kernel Γ(X, U) X.functionField]
      exact hD
    obtain ⟨g, hg⟩ := (h.affineOrderSystem X U hU).mem_principalSubgroup.mp hD'
    apply (h.ambientOrderSystem X U hU).mem_principalSubgroup.mpr
    refine ⟨g, ?_⟩
    rw [← h.principalDivisor_reindex_eq_ambientPrincipalDivisor X U hU g]
    calc
      e ((h.affineOrderSystem X U hU).principalDivisor g) =
          e (e.symm D) := congrArg _ hg
      _ = D := e.apply_symm_apply D
  · intro hD
    obtain ⟨g, rfl⟩ := (h.ambientOrderSystem X U hU).mem_principalSubgroup.mp hD
    exact h.divisorToSchemePic_principalDivisor X U hU g

/-- Descend the chart divisor-to-Picard construction to divisor classes for the ambient chart
order system. -/
noncomputable def classToSchemePic :
    (h.ambientOrderSystem X U hU).ClassGroup →+
      PicardGroup (Spec (.of Γ(X, U))) :=
  DivisorPicard.classToPic (h.ambientOrderSystem X U hU)
    (h.divisorToSchemePic X U hU)
    (DivisorPicard.principalTrivial_of_principalKernel
      (h.ambientOrderSystem X U hU) (h.divisorToSchemePic X U hU)
      (h.divisorToSchemePic_kernel X U hU))

/-- The descended chart map agrees with the divisor construction on representatives. -/
@[simp]
lemma classToSchemePic_divisorClass
    (D : WeilDivisor {x : CodimensionOnePoint X // x.1 ∈ U}) :
    h.classToSchemePic X U hU
        ((h.ambientOrderSystem X U hU).divisorClass D) =
      h.divisorToSchemePic X U hU D :=
  DivisorPicard.classToPic_divisorClass
    (h.ambientOrderSystem X U hU) (h.divisorToSchemePic X U hU)
    (DivisorPicard.principalTrivial_of_principalKernel
      (h.ambientOrderSystem X U hU) (h.divisorToSchemePic X U hU)
      (h.divisorToSchemePic_kernel X U hU)) D

/-- Exactness of the chart divisor map makes the descended class map injective. -/
theorem classToSchemePic_injective :
    Function.Injective (h.classToSchemePic X U hU) :=
  DivisorPicard.classToPic_injective
    (h.ambientOrderSystem X U hU) (h.divisorToSchemePic X U hU)
    (DivisorPicard.principalTrivial_of_principalKernel
      (h.ambientOrderSystem X U hU) (h.divisorToSchemePic X U hU)
      (h.divisorToSchemePic_kernel X U hU))
    (h.divisorToSchemePic_kernel X U hU)

/-- The strongest chart-level divisor-class/Picard equivalence available without a Picard
surjectivity theorem: ambient chart divisor classes are equivalent to the range of their
canonical affine realization. -/
noncomputable def classEquivSchemePicRange :
    (h.ambientOrderSystem X U hU).ClassGroup ≃+
      (h.classToSchemePic X U hU).range :=
  DivisorPicard.classEquivPicardRange
    (h.ambientOrderSystem X U hU) (h.divisorToSchemePic X U hU)
      (h.divisorToSchemePic_kernel X U hU)

/-- The range equivalence has the descended chart class as its underlying Picard value. -/
@[simp]
lemma classEquivSchemePicRange_apply_val
    (c : (h.ambientOrderSystem X U hU).ClassGroup) :
    (h.classEquivSchemePicRange X U hU c).1 =
      h.classToSchemePic X U hU c := by
  exact DivisorPicard.classEquivPicardRange_apply_val
    (h.ambientOrderSystem X U hU) (h.divisorToSchemePic X U hU)
      (h.divisorToSchemePic_kernel X U hU) c

/-- Transport the checked affine-chart divisor map from the coordinate spectrum to the open
subscheme itself. -/
noncomputable def divisorToOpenPic
    (hmonoidal : ChartPullbackMonoidalData X U hU) :
    WeilDivisor {x : CodimensionOnePoint X // x.1 ∈ U} →+ PicardGroup U :=
  (picardEquivSpecToOpen X U hU hmonoidal).toAddMonoidHom.comp
    (h.divisorToSchemePic X U hU)

/-- The open-chart Picard class is represented by pullback of the coordinate-spectrum
isomorphism class. -/
@[simp]
lemma divisorToOpenPic_apply_val
    (hmonoidal : ChartPullbackMonoidalData X U hU)
    (D : WeilDivisor {x : CodimensionOnePoint X // x.1 ∈ U}) :
    letI := Scheme.Modules.monoidalCategory (Spec (.of Γ(X, U)))
    letI := Scheme.Modules.monoidalCategory (U : Scheme)
    (Additive.toMul (divisorToOpenPic X U hU h hmonoidal D)).val =
      (Scheme.Modules.pullback hU.isoSpec.hom).mapSkeleton.obj
        (Additive.toMul (h.divisorToSchemePic X U hU D)).val := by
  exact PicardIso.equivOfPullbackMonoidal_apply_val hU.isoSpec hmonoidal
    (Additive.toMul (h.divisorToSchemePic X U hU D))

/-- Principal divisors have trivial Picard class after transport to the affine open. -/
lemma divisorToOpenPic_principalDivisor
    (hmonoidal : ChartPullbackMonoidalData X U hU)
    (g : Additive X.functionFieldˣ) :
    divisorToOpenPic X U hU h hmonoidal
        ((h.ambientOrderSystem X U hU).principalDivisor g) = 0 := by
  rw [divisorToOpenPic, AddMonoidHom.comp_apply,
    h.divisorToSchemePic_principalDivisor X U hU g, map_zero]

/-- Transport to the open subscheme preserves the exact principal kernel. -/
theorem divisorToOpenPic_kernel
    (hmonoidal : ChartPullbackMonoidalData X U hU) :
    (divisorToOpenPic X U hU h hmonoidal).ker =
      (h.ambientOrderSystem X U hU).principalSubgroup := by
  rw [divisorToOpenPic, AddMonoidHom.ker_comp_of_injective
    (h.divisorToSchemePic X U hU)
    (picardEquivSpecToOpen X U hU hmonoidal).toAddMonoidHom
    (picardEquivSpecToOpen X U hU hmonoidal).injective]
  exact h.divisorToSchemePic_kernel X U hU

/-- Transport the descended divisor-class map to the Picard group of the open subscheme. -/
noncomputable def classToOpenPic
    (hmonoidal : ChartPullbackMonoidalData X U hU) :
    (h.ambientOrderSystem X U hU).ClassGroup →+ PicardGroup U :=
  (picardEquivSpecToOpen X U hU hmonoidal).toAddMonoidHom.comp
    (h.classToSchemePic X U hU)

/-- The open-chart class map agrees with the transported divisor construction on
representatives. -/
@[simp]
lemma classToOpenPic_divisorClass
    (hmonoidal : ChartPullbackMonoidalData X U hU)
    (D : WeilDivisor {x : CodimensionOnePoint X // x.1 ∈ U}) :
    classToOpenPic X U hU h hmonoidal
        ((h.ambientOrderSystem X U hU).divisorClass D) =
      divisorToOpenPic X U hU h hmonoidal D := by
  rw [classToOpenPic, divisorToOpenPic, AddMonoidHom.comp_apply,
    AddMonoidHom.comp_apply, h.classToSchemePic_divisorClass]

/-- Exactness remains injective after transporting chart divisor classes to `PicardGroup U`. -/
theorem classToOpenPic_injective
    (hmonoidal : ChartPullbackMonoidalData X U hU) :
    Function.Injective (classToOpenPic X U hU h hmonoidal) :=
  (picardEquivSpecToOpen X U hU hmonoidal).injective.comp
    (h.classToSchemePic_injective X U hU)

/-- The strongest honest open-chart comparison: divisor classes are equivalent to their range
in `PicardGroup U`, without asserting that every Picard class is hit. -/
noncomputable def classEquivOpenPicRange
    (hmonoidal : ChartPullbackMonoidalData X U hU) :
    (h.ambientOrderSystem X U hU).ClassGroup ≃+
      (classToOpenPic X U hU h hmonoidal).range :=
  AddEquiv.ofBijective (classToOpenPic X U hU h hmonoidal).rangeRestrict
    ⟨fun _ _ hxy ↦ classToOpenPic_injective X U hU h hmonoidal
        (congrArg Subtype.val hxy), by
      rintro ⟨_, ⟨c, rfl⟩⟩
      exact ⟨c, rfl⟩⟩

/-- The open-chart range equivalence has the descended Picard class as its underlying value. -/
@[simp]
lemma classEquivOpenPicRange_apply_val
    (hmonoidal : ChartPullbackMonoidalData X U hU)
    (c : (h.ambientOrderSystem X U hU).ClassGroup) :
    (classEquivOpenPicRange X U hU h hmonoidal c).1 =
      classToOpenPic X U hU h hmonoidal c := by
  rfl

end DedekindOrderCompatibility

end MazurTorsion.AlgebraicGeometry.AffineChart
