/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.DivisorLineBundle
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order

/-!
# Affine charts for the divisor--line-bundle dictionary

This file identifies height-one primes of a Dedekind affine chart with the ambient
codimension-one points lying in that chart. It then isolates the exact compatibility still
needed between the Dedekind-domain valuations and Tau Ceti's scheme-theoretic orders.

The compatibility is consumed here, rather than merely recorded: it transports the affine
principal-divisor order system to the ambient points of the chart and constructs a canonical
divisor-to-scheme-Picard map which kills those principal divisors. This is the checked local
boundary needed before the affine line bundles in `DivisorLineBundle` can be glued on a curve.
The unconditional Picard target is the coordinate spectrum `Spec Γ(X, U)`. The file isolates
strong monoidality of pullback as an upstream-compatible sufficient datum for transport to
`Pic(U)` and consumes that datum to preserve the principal kernel, class descent, and range
equivalence. Constructing the datum and overlap-compatible gluing to `X` remain separate
obligations.
-/

namespace MazurTorsion.AlgebraicGeometry.AffineChart

universe u

open CategoryTheory MonoidalCategory
open _root_.AlgebraicGeometry
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open IsDedekindDomain

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
open IsDedekindDomain

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
