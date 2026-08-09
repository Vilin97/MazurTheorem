/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import EllipticCurves.X18WeakMordellWeil
public import EllipticCurves.Mathlib.AdicCompletionExtension
public import EllipticCurves.WeierstrassFormalGroup.Filtration

@[expose] public section

/-!
# The local two-descent condition used for `X₁(18)`

This is the local, finite-place slice of Michael Stoll's
`EllipticCurves/SelmerGroup.lean`, commit
`3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f`.  It contains only base change of the
`x - T` descent map and the cardinality formula for its image over an adic completion.
The global semilocal Selmer-group machinery from the source file is deliberately not
imported here.

The declarations concerning point base change are reused from
`EllipticCurves.Mathlib.EllipticCurvePoint`; the rest follows the pinned source proof.
-/

open Polynomial IsDedekindDomain

namespace WeierstrassCurve.Affine

variable {K : Type*} [Field K] (W : Affine K)

section BaseChange

variable {L₀ : Type*} [Field L₀] (σ : K →+* L₀)

lemma map_f : (W.map σ).toAffine.f = W.f.map σ := by
  simp only [f, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_X,
    Polynomial.map_C, map_a₂, map_a₄, map_a₆]

instance [W.IsCharNeTwoNF] : (W.map σ).IsCharNeTwoNF where
  a₁ := by simp [map_a₁]
  a₃ := by simp [map_a₃]

lemma eval_map_f (x : K) : (W.map σ).toAffine.f.eval (σ x) = σ (W.f.eval x) := by
  rw [map_f, Polynomial.eval_map, Polynomial.eval₂_at_apply]

lemma map_fCofactor (x : K) :
    (W.fCofactor x).map σ = (W.map σ).toAffine.fCofactor (σ x) := by
  simp only [fCofactor, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul,
    Polynomial.map_X, Polynomial.map_C, map_a₂, map_a₄, map_add, map_mul, map_pow]

variable (L : Type*) [Field L] [Algebra K L]

instance [W.IsCharNeTwoNF] : (W⁄L).IsCharNeTwoNF :=
  inferInstanceAs (W.map (algebraMap K L)).IsCharNeTwoNF

lemma eval_baseChange_f (x : K) :
    (W⁄L).toAffine.f.eval (algebraMap K L x) = algebraMap K L (W.f.eval x) :=
  W.eval_map_f (algebraMap K L) x

lemma baseChange_fCofactor (x : K) :
    (W.fCofactor x).map (algebraMap K L) = (W⁄L).toAffine.fCofactor (algebraMap K L x) :=
  W.map_fCofactor (algebraMap K L) x

lemma baseChange_f : (W⁄L).toAffine.f = W.f.map (algebraMap K L) :=
  W.map_f (algebraMap K L)

lemma baseChange_discr_f : (W⁄L).toAffine.f.discr = algebraMap K L W.f.discr := by
  change (W.map (algebraMap K L)).toAffine.f.discr = _
  rw [discr_f, discr_f]
  simp only [map_a₂, map_a₄, map_a₆, map_sub, map_add, map_mul, map_pow, map_ofNat]

/-- Base change of the cubic étale algebra. -/
noncomputable def mapA : W.A →+* (W⁄L).toAffine.A :=
  AdjoinRoot.map (algebraMap K L) W.f (W⁄L).toAffine.f (W.baseChange_f L).dvd

@[simp]
lemma mapA_mk (p : K[X]) :
    W.mapA L (AdjoinRoot.mk W.f p) = AdjoinRoot.mk (W⁄L).toAffine.f (p.map (algebraMap K L)) :=
  AdjoinRoot.map_mk _ _ _

/-- Restriction of square classes to the base-changed cubic étale algebra. -/
noncomputable def localRes : W.M →* Units.modPow (W⁄L).toAffine.A 2 :=
  Units.modPow.map (W.mapA L).toMonoidHom 2

@[simp]
lemma localRes_mk (u : W.Aˣ) :
    W.localRes L (QuotientGroup.mk u) =
      QuotientGroup.mk (Units.map (W.mapA L).toMonoidHom u) :=
  rfl

@[simp]
lemma localRes_unit {a : W.A} (ha : IsUnit a) :
    W.localRes L (ha.unit : W.M) =
      ((ha.map (W.mapA L).toMonoidHom).unit : Units.modPow (W⁄L).toAffine.A 2) := by
  rw [localRes, Units.modPow.map_unit]

lemma norm_mapA (a : W.A) :
    Algebra.norm L (W.mapA L a) = algebraMap K L (Algebra.norm K a) := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
  rw [mapA_mk, AdjoinRoot.norm_mk_eq_resultant (W⁄L).toAffine.monic_f,
    AdjoinRoot.norm_mk_eq_resultant W.monic_f, W.baseChange_f,
    natDegree_map_eq_of_injective (algebraMap K L).injective,
    natDegree_map_eq_of_injective (algebraMap K L).injective, resultant_map_map]

lemma normM_localRes (a : W.M) :
    normM (W := (W⁄L).toAffine) (W.localRes L a) =
      Units.modPow.map (algebraMap K L).toMonoidHom 2 (W.normM a) := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective _ a
  simp only [QuotientGroup.mk'_apply, localRes_mk, normM, Units.modPow.map_mk]
  exact congrArg _ (Units.ext (by simpa using W.norm_mapA L u))

variable [W.IsElliptic] [W.IsCharNeTwoNF]

instance : (W⁄L).IsElliptic := inferInstanceAs (W.map (algebraMap K L)).IsElliptic

variable [DecidableEq L]

/-- Square classes whose restriction belongs to the image of the local descent map. -/
noncomputable def localCondition : Subgroup W.M :=
  ((μ (W := (W⁄L).toAffine)).range).comap (W.localRes L)

lemma mem_localCondition_iff {a : W.M} :
    a ∈ W.localCondition L ↔ W.localRes L a ∈ (μ (W := (W⁄L).toAffine)).range :=
  Subgroup.mem_comap

variable [DecidableEq K]

theorem localRes_μX (x : K) :
    W.localRes L (W.μX x) = μX (W := (W⁄L).toAffine) (algebraMap K L x) := by
  rcases eq_or_ne (W.f.eval x) 0 with hx | hx
  · have hxL : (W⁄L).toAffine.f.eval (algebraMap K L x) = 0 := by
      rw [W.eval_baseChange_f, hx, map_zero]
    rw [μX_of_eval_f_eq_zero hxL, μX_of_eval_f_eq_zero hx, localRes_unit]
    refine congrArg _ (Units.ext ?_)
    rw [IsUnit.unit_spec, IsUnit.unit_spec]
    simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, mapA_mk, Polynomial.map_add,
      Polynomial.map_sub, Polynomial.map_C, Polynomial.map_X, W.baseChange_fCofactor]
  · have hxL : (W⁄L).toAffine.f.eval (algebraMap K L x) ≠ 0 := by
      rw [W.eval_baseChange_f]
      exact fun h0 ↦ hx ((map_eq_zero _).mp h0)
    rw [μX_of_eval_f_ne_zero hxL, μX_of_eval_f_ne_zero hx, localRes_unit]
    refine congrArg _ (Units.ext ?_)
    rw [IsUnit.unit_spec, IsUnit.unit_spec]
    simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, mapA_mk, Polynomial.map_sub,
      Polynomial.map_C, Polynomial.map_X]

/-- Naturality of `x - T` descent under field extension. -/
theorem localRes_comp_μ :
    (W.localRes L).comp (μ (W := W)) =
      (μ (W := (W⁄L).toAffine)).comp (AddMonoidHom.toMultiplicative (W.pointMap L)) := by
  refine MonoidHom.ext fun P' ↦ ?_
  obtain ⟨P, rfl⟩ := Multiplicative.ofAdd.surjective P'
  simp only [MonoidHom.comp_apply, AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd,
    μ_apply]
  cases P with
  | zero =>
      rw [show (Point.zero : W.Point) = 0 from rfl, μ₀_zero, map_one, W.pointMap_zero L,
        μ₀_zero (W := (W⁄L).toAffine)]
  | some x y hP =>
      rw [μ₀_some, W.pointMap_some L hP, μ₀_some (W := (W⁄L).toAffine), W.localRes_μX L x]

/-- Every global descent class satisfies the local condition. -/
theorem range_μ_le_localCondition : (μ (W := W)).range ≤ W.localCondition L := by
  rw [localCondition, ← Subgroup.map_le_iff_le_comap, MonoidHom.map_range, localRes_comp_μ]
  rintro _ ⟨P, rfl⟩
  exact ⟨_, rfl⟩

end BaseChange

end WeierstrassCurve.Affine

/-!
## A finite-index Euler characteristic

These lemmas are the narrow portion of Stoll's `EllipticCurves/Mathlib/SelmerGroup.lean`
needed by the local cardinality formula.
-/

lemma AddMonoidHom.ker_nsmulAddMonoidHom {G : Type*} [AddCommGroup G] [IsAddTorsionFree G]
    {n : ℕ} (hn : n ≠ 0) : (nsmulAddMonoidHom (α := G) n).ker = ⊥ :=
  AddMonoidHom.ker_eq_bot _ fun a b hab ↦
    nsmul_right_injective hn (by simpa only [nsmulAddMonoidHom_apply] using hab)

lemma AddMonoidHom.range_nsmulAddMonoidHom (R : Type*) [CommRing R] (n : ℕ) :
    (nsmulAddMonoidHom (α := R) n).range = (Ideal.span {(n : R)}).toAddSubgroup := by
  ext x
  simp only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply, Submodule.mem_toAddSubgroup,
    Ideal.mem_span_singleton']
  constructor <;> exact fun ⟨c, hc⟩ ↦ ⟨c, by rw [← hc, nsmul_eq_mul, mul_comm]⟩

open AddSubgroup in
private lemma relIndex_range_comp_subtype {G : Type*} [AddCommGroup G]
    (U : AddSubgroup G) (n : ℕ) :
    (((nsmulAddMonoidHom (α := G) n).comp U.subtype).range).relIndex
        (nsmulAddMonoidHom (α := G) n).range =
      ((nsmulAddMonoidHom (α := G) n).ker ⊔ U).index := by
  set φG := nsmulAddMonoidHom (α := G) n
  set B : AddSubgroup G := (φG.comp U.subtype).range
  set C : AddSubgroup G := φG.ker ⊔ U
  set ρ := (QuotientAddGroup.mk' (B.addSubgroupOf φG.range)).comp φG.rangeRestrict with hρdef
  have hρ : Function.Surjective ρ :=
    (QuotientAddGroup.mk'_surjective _).comp φG.rangeRestrict_surjective
  have hker : ρ.ker = C := by
    ext g
    rw [AddMonoidHom.mem_ker, hρdef, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_zero_iff]
    constructor
    · intro ⟨u, hu⟩
      refine AddSubgroup.mem_sup.mpr ⟨g - u, ?_, u, u.2, by abel⟩
      rw [AddMonoidHom.mem_ker, map_sub]
      have : φG (u : G) = φG g := hu
      rw [this, sub_self]
    · intro hg
      obtain ⟨k, hk, u, hu, rfl⟩ := AddSubgroup.mem_sup.mp hg
      refine ⟨⟨u, hu⟩, ?_⟩
      have hk0 : φG k = 0 := hk
      change φG (u : G) = φG (k + u)
      rw [map_add, hk0, zero_add]
  calc B.relIndex φG.range
      = Nat.card (φG.range ⧸ B.addSubgroupOf φG.range) := rfl
    _ = Nat.card (G ⧸ C) := Nat.card_congr <| ((QuotientAddGroup.quotientKerEquivOfSurjective
          ρ hρ).symm.trans (QuotientAddGroup.quotientAddEquivOfEq hker)).toEquiv
    _ = C.index := rfl

open AddSubgroup in
private lemma relIndex_sup_ker_mul_card_ker {G : Type*} [AddCommGroup G]
    (U : AddSubgroup G) (n : ℕ) :
    U.relIndex ((nsmulAddMonoidHom (α := G) n).ker ⊔ U) *
        Nat.card (nsmulAddMonoidHom (α := U) n).ker =
      Nat.card (nsmulAddMonoidHom (α := G) n).ker := by
  set φG := nsmulAddMonoidHom (α := G) n
  set φU := nsmulAddMonoidHom (α := U) n
  have h2 : Nat.card (φG.ker ⧸ U.addSubgroupOf φG.ker) = U.relIndex (φG.ker ⊔ U) :=
    Nat.card_congr (QuotientAddGroup.quotientInfEquivSumNormalQuotient φG.ker U).toEquiv
  have h3 : Nat.card (U.addSubgroupOf φG.ker) = Nat.card φU.ker :=
    Nat.card_congr
      ⟨fun x ↦ ⟨⟨(x : G), x.2⟩, Subtype.ext (x : φG.ker).2⟩,
        fun y ↦ ⟨⟨(y : U), congrArg Subtype.val y.2⟩, (y : U).2⟩,
        fun x ↦ rfl, fun y ↦ rfl⟩
  rw [← h2, ← h3]
  exact (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _).symm

open AddSubgroup in
/-- The ratio `#(G/nG) / #G[n]` is unchanged on finite-index subgroups. -/
theorem AddSubgroup.index_range_nsmul_mul_card_ker {G : Type*} [AddCommGroup G]
    (U : AddSubgroup G) [U.FiniteIndex] (n : ℕ) :
    (nsmulAddMonoidHom (α := G) n).range.index *
        Nat.card ((nsmulAddMonoidHom (α := U) n)).ker =
      Nat.card ((nsmulAddMonoidHom (α := G) n)).ker *
        (nsmulAddMonoidHom (α := U) n).range.index := by
  set φG := nsmulAddMonoidHom (α := G) n
  set φU := nsmulAddMonoidHom (α := U) n
  set B : AddSubgroup G := (φG.comp U.subtype).range
  set C : AddSubgroup G := φG.ker ⊔ U
  have hBA : B ≤ φG.range := by
    rintro _ ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  have hBU : B ≤ U := by
    rintro _ ⟨u, rfl⟩
    exact U.nsmul_mem u.2 n
  have hUC : U ≤ C := le_sup_right
  have hrBU : B.relIndex U = φU.range.index := by
    have h : B.addSubgroupOf U = φU.range := by
      ext u
      exact ⟨fun ⟨w, hw⟩ ↦ ⟨w, Subtype.ext hw⟩,
        fun ⟨w, hw⟩ ↦ ⟨w, congrArg Subtype.val hw⟩⟩
    rw [relIndex, h]
  have hrBA : B.relIndex φG.range = C.index := relIndex_range_comp_subtype U n
  have hUK : U.relIndex C * Nat.card φU.ker = Nat.card φG.ker :=
    relIndex_sup_ker_mul_card_ker U n
  have h24 : C.index * φG.range.index = φU.range.index * U.index := by
    rw [← hrBA, ← hrBU, relIndex_mul_index hBA, relIndex_mul_index hBU]
  have hCne : C.index ≠ 0 := by
    intro h
    exact FiniteIndex.index_ne_zero (H := U)
      (Nat.eq_zero_of_zero_dvd (h ▸ AddSubgroup.index_dvd_of_le hUC))
  have hA : φG.range.index = φU.range.index * U.relIndex C := by
    refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hCne) ?_
    rw [h24, ← relIndex_mul_index hUC]
    ring
  calc φG.range.index * Nat.card φU.ker
      = φU.range.index * (U.relIndex C * Nat.card φU.ker) := by rw [hA]; ring
    _ = φU.range.index * Nat.card φG.ker := by rw [hUK]
    _ = Nat.card φG.ker * φU.range.index := mul_comm _ _

lemma AddEquiv.index_range_nsmulAddMonoidHom {M N : Type*}
    [AddCommGroup M] [AddCommGroup N] (e : M ≃+ N) (n : ℕ) :
    (nsmulAddMonoidHom (α := M) n).range.index =
      (nsmulAddMonoidHom (α := N) n).range.index := by
  simpa [AddEquiv.map_range_nsmulAddMonoidHom]
    using (AddSubgroup.index_map_equiv (nsmulAddMonoidHom (α := M) n).range e).symm

namespace WeierstrassCurve.Affine

open NumberField

variable {F : Type*} [Field F] [NumberField F] (W : Affine F)

local notation:max "F_[" v "]" => HeightOneSpectrum.adicCompletion F v
local notation:max "𝒪_[" v "]" => HeightOneSpectrum.adicCompletionIntegers F v
local notation:max "𝕎[" v "]" =>
  WeierstrassCurve.toAffine (W⁄(HeightOneSpectrum.adicCompletion F v))

instance instFiniteQuotientAsIdeal (v : HeightOneSpectrum (𝓞 F)) :
    Finite (𝓞 F ⧸ v.asIdeal) :=
  v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot

variable [W.IsElliptic] [W.IsCharNeTwoNF]

private lemma index_range_nsmul_two (v : HeightOneSpectrum (𝓞 F)) :
    (nsmulAddMonoidHom (α := 𝒪_[v]) 2).range.index =
      Nat.card (𝓞 F ⧸ v.asIdeal) ^
        (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {(2 : 𝓞 F)})).factors := by
  have h2v : Valued.v (algebraMap 𝒪_[v] F_[v] (2 : 𝒪_[v])) =
      WithZero.exp (-((Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span {(2 : 𝓞 F)})).factors : ℤ)) := by
    rw [map_ofNat, ← map_ofNat (algebraMap F F_[v]) 2,
      show Valued.v (algebraMap F F_[v] (2 : F)) = v.valuation F 2 from
        v.valuedAdicCompletion_eq_valuation' 2,
      ← map_ofNat (algebraMap (𝓞 F) F) 2, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.intValuation_if_neg v two_ne_zero]
  rw [AddMonoidHom.range_nsmulAddMonoidHom, Nat.cast_ofNat]
  calc (Ideal.span {(2 : 𝒪_[v])}).toAddSubgroup.index
      = Nat.card (𝒪_[v] ⧸ Ideal.span {(2 : 𝒪_[v])}) := rfl
    _ = Nat.card (𝒪_[v] ⧸ IsLocalRing.maximalIdeal 𝒪_[v] ^ (Associates.mk v.asIdeal).count
            (Associates.mk (Ideal.span {(2 : 𝓞 F)})).factors) :=
        Nat.card_congr (Ideal.quotEquivOfEq (v.span_singleton_eq_maximalIdeal_pow h2v)).toEquiv
    _ = Submodule.cardQuot (IsLocalRing.maximalIdeal 𝒪_[v] ^ (Associates.mk v.asIdeal).count
            (Associates.mk (Ideal.span {(2 : 𝓞 F)})).factors) :=
        (Submodule.cardQuot_apply _).symm
    _ = Submodule.cardQuot (IsLocalRing.maximalIdeal 𝒪_[v]) ^ (Associates.mk v.asIdeal).count
            (Associates.mk (Ideal.span {(2 : 𝓞 F)})).factors :=
        cardQuot_pow_of_prime (IsDiscreteValuationRing.not_a_field _)
    _ = Nat.card (𝓞 F ⧸ v.asIdeal) ^ (Associates.mk v.asIdeal).count
          (Associates.mk (Ideal.span {(2 : 𝓞 F)})).factors := by
        rw [Submodule.cardQuot_apply,
          ← Nat.card_congr (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv]

/-- The finite-place local image formula for the `x - T` descent map. -/
theorem card_range_μ_adicCompletion (v : HeightOneSpectrum (𝓞 F)) [DecidableEq F_[v]] :
    Nat.card (μ (W := 𝕎[v])).range =
      Nat.card (nsmulAddMonoidHom (α := 𝕎[v].Point) 2).ker *
        Nat.card (𝓞 F ⧸ v.asIdeal) ^
          (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {(2 : 𝓞 F)})).factors := by
  obtain ⟨U, hUfin, ⟨e⟩⟩ :=
    exists_finiteIndex_addSubgroup_equiv_adicCompletionIntegers v 𝕎[v]
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange (μ (W := 𝕎[v]))).toEquiv,
    ker_μ_eq, ← Subgroup.index_eq_card, AddSubgroup.index_toSubgroup]
  have hczO : CharZero 𝒪_[v] :=
    charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective (𝓞 F) 𝒪_[v])
  have hker : Nat.card ((nsmulAddMonoidHom (α := U) 2)).ker = 1 := by
    have : IsAddTorsionFree U := Function.Injective.isAddTorsionFree e.toAddMonoidHom e.injective
    rw [AddMonoidHom.ker_nsmulAddMonoidHom two_ne_zero]
    exact AddSubgroup.card_bot
  have hchi := AddSubgroup.index_range_nsmul_mul_card_ker U 2
  rw [hker, mul_one] at hchi
  rw [hchi]
  congr 1
  rw [e.index_range_nsmulAddMonoidHom 2, index_range_nsmul_two v]

/-- At an odd finite place the local image has the same size as rational `2`-torsion. -/
theorem card_range_μ_adicCompletion_of_two_notMem {v : HeightOneSpectrum (𝓞 F)}
    [DecidableEq F_[v]] (hv : (2 : 𝓞 F) ∉ v.asIdeal) :
    Nat.card (μ (W := 𝕎[v])).range =
      Nat.card (nsmulAddMonoidHom (α := 𝕎[v].Point) 2).ker := by
  have h0 : (Associates.mk v.asIdeal).count
      (Associates.mk (Ideal.span {(2 : 𝓞 F)})).factors = 0 := by
    by_contra h
    have h1 := (v.le_count_iff two_ne_zero 1).mp (Nat.one_le_iff_ne_zero.mpr h)
    rw [pow_one] at h1
    exact hv h1
  rw [W.card_range_μ_adicCompletion v, h0, pow_zero, mul_one]

end WeierstrassCurve.Affine

end
