/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate. Ticket T-A2d (step 4).

Selectively ported from AINTLIB commit
`7ecbba9dbb7fee076a1b77a6cd516fc6de46d684`, source blob
`b987dd389601b36b17803e93e680afde78d6dd51`.

Local exact-pin adaptation: independent declarations not used by `chartRingEquiv`
(`X_mem_nonzeroDivisors`, `dehomogenizeAux_map`, `homogenizeAt_map`, and the private
`isUnit_mk_X_pow`) are omitted. In particular, this leaf does not need AINTLIB's
`AwayCongr`. The required declarations otherwise retain their upstream statements and
proofs. Six goal-shaping `show` invocations are spelled `change` to satisfy this
repository's style linter; this is elaboration-only.
-/
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The affine charts of projective space, ring-theoretically

The degree-zero part of the homogeneous localization of `R[X_j : j ∈ σ]` away from a
variable `X i` is a polynomial ring on the remaining variables:
`(R[X]_{X i})₀ ≃+* R[u_j : j ≠ i]`, by dehomogenisation `X_j/X_i ↦ u_j`.

This is the chart description underlying `ℙⁿ_R = Proj R[X₀,…,Xₙ]` and, through
quotient gradings, the affine charts of projective hypersurfaces.
-/

namespace HomogeneousLocalization

variable {ι R A : Type*} [AddCommMonoid ι] [DecidableEq ι] [CommRing R] [CommRing A]
  [Algebra R A] {𝒜 : ι → Submodule R A} [GradedAlgebra 𝒜] (x : Submonoid A)

/-- `HomogeneousLocalization.val` as a ring homomorphism. -/
def valRingHom : HomogeneousLocalization 𝒜 x →+* Localization x where
  toFun := val
  map_one' := val_one
  map_mul' := val_mul
  map_zero' := val_zero
  map_add' := val_add

@[simp]
lemma valRingHom_apply (y : HomogeneousLocalization 𝒜 x) : valRingHom x y = y.val :=
  rfl

end HomogeneousLocalization

namespace MvPolynomial

open HomogeneousLocalization

variable (R : Type*) {σ : Type*} [CommRing R] [DecidableEq σ]

attribute [local instance] MvPolynomial.gradedAlgebra

omit [DecidableEq σ] in
lemma X_mem_homogeneousSubmodule_one (i : σ) :
    (X i : MvPolynomial σ R) ∈ homogeneousSubmodule σ R 1 :=
  (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X _ _)

/-- The dehomogenising evaluation `R[X] → R[u_j : j ≠ i]`, `X_i ↦ 1`, `X_j ↦ u_j`. -/
noncomputable def dehomogenizeAux (i : σ) :
    MvPolynomial σ R →+* MvPolynomial {j : σ // j ≠ i} R :=
  eval₂Hom C fun j => if h : j = i then 1 else X ⟨j, h⟩

@[simp]
lemma dehomogenizeAux_C (i : σ) (r : R) : dehomogenizeAux R i (C r) = C r :=
  eval₂Hom_C _ _ _

@[simp]
lemma dehomogenizeAux_X_self (i : σ) : dehomogenizeAux R i (X i) = 1 := by
  simp [dehomogenizeAux]

@[simp]
lemma dehomogenizeAux_X_ne (i : σ) {j : σ} (h : j ≠ i) :
    dehomogenizeAux R i (X j) = X ⟨j, h⟩ := by
  simp [dehomogenizeAux, h]

/-- Dehomogenisation at the variable `X i`: the chart map
`(R[X]_{X i})₀ → R[u_j : j ≠ i]`. -/
noncomputable def dehomogenizeAt (i : σ) :
    Away (homogeneousSubmodule σ R) (X i : MvPolynomial σ R) →+*
      MvPolynomial {j : σ // j ≠ i} R :=
  (Localization.awayLift (dehomogenizeAux R i) (X i)
    (isUnit_iff_exists_inv.mpr ⟨1, by simp⟩)).comp (valRingHom _)

/-- The constants `R` inside the chart ring `(R[X]_{X i})₀`. -/
noncomputable def awayConst (i : σ) (r : R) :
    Away (homogeneousSubmodule σ R) (X i : MvPolynomial σ R) :=
  Away.mk _ (X_mem_homogeneousSubmodule_one R i) 0 (C r)
    (by simp)

omit [DecidableEq σ] in
lemma val_awayConst' (i : σ) (r : R) :
    (awayConst R i r).val =
      Localization.mk (C r) (⟨(X i : MvPolynomial σ R) ^ 0, 0, rfl⟩ :
        Submonoid.powers (X i : MvPolynomial σ R)) := by
  rw [awayConst, Away.val_mk]

omit [DecidableEq σ] in
@[simp]
lemma val_awayConst (i : σ) (r : R) :
    (awayConst R i r).val = Localization.mk (C r) 1 := by
  rw [val_awayConst']
  exact congrArg _ (Subtype.ext (pow_zero _))

/-- The chart coordinate `X_j / X_i` in `(R[X]_{X i})₀`. -/
noncomputable def awayVar (i : σ) (j : {j : σ // j ≠ i}) :
    Away (homogeneousSubmodule σ R) (X i : MvPolynomial σ R) :=
  Away.mk _ (X_mem_homogeneousSubmodule_one R i) 1 (X j.1)
    (by simpa using (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X _ _))

omit [DecidableEq σ] in
lemma val_awayVar' (i : σ) (j : {j : σ // j ≠ i}) :
    (awayVar R i j).val =
      Localization.mk (X j.1) (⟨(X i : MvPolynomial σ R) ^ 1, 1, rfl⟩ :
        Submonoid.powers (X i : MvPolynomial σ R)) := by
  rw [awayVar, Away.val_mk]

/-- The constants, as a ring homomorphism into the chart ring. -/
noncomputable def awayConstHom (i : σ) :
    R →+* Away (homogeneousSubmodule σ R) (X i : MvPolynomial σ R) where
  toFun := awayConst R i
  map_one' := by
    apply val_injective
    rw [val_awayConst, val_one, map_one]
    exact Localization.mk_one
  map_mul' a b := by
    apply val_injective
    rw [val_mul, val_awayConst, val_awayConst, val_awayConst, Localization.mk_mul,
      map_mul, one_mul]
  map_zero' := by
    apply val_injective
    rw [val_awayConst, val_zero, map_zero]
    exact Localization.mk_zero _
  map_add' a b := by
    apply val_injective
    rw [val_add, val_awayConst, val_awayConst, val_awayConst,
      Localization.add_mk_self, map_add]

/-- Homogenisation into the chart at `X i`: `u_j ↦ X_j/X_i`. -/
noncomputable def homogenizeAt (i : σ) :
    MvPolynomial {j : σ // j ≠ i} R →+*
      Away (homogeneousSubmodule σ R) (X i : MvPolynomial σ R) :=
  eval₂Hom (awayConstHom R i) (awayVar R i)

private lemma dehomog_lift_mk_one (i : σ) (a : MvPolynomial σ R) :
    Localization.awayLift (dehomogenizeAux R i) (X i)
      (isUnit_iff_exists_inv.mpr ⟨1, by simp⟩) (Localization.mk a 1) =
    dehomogenizeAux R i a := by
  rw [Localization.mk_one_eq_algebraMap]
  exact IsLocalization.Away.lift_eq _ _ _

/-- Dehomogenising after homogenising is the identity. -/
lemma dehomogenizeAt_comp_homogenizeAt (i : σ) :
    (dehomogenizeAt R i).comp (homogenizeAt R i) = RingHom.id _ := by
  apply ringHom_ext
  · intro r
    change dehomogenizeAt R i (homogenizeAt R i (C r)) = C r
    have hval : homogenizeAt R i (C r) = awayConst R i r := by
      rw [homogenizeAt, eval₂Hom_C]
      rfl
    rw [hval]
    simp only [dehomogenizeAt, RingHom.comp_apply, valRingHom_apply, val_awayConst,
      dehomog_lift_mk_one, dehomogenizeAux_C]
  · intro j
    change dehomogenizeAt R i (homogenizeAt R i (X j)) = X j
    have hval : homogenizeAt R i (X j) = awayVar R i j := by
      rw [homogenizeAt, eval₂Hom_X']
    rw [hval]
    have hval2 : (awayVar R i j).val * Localization.mk (X i) 1 =
        Localization.mk (X j.1) 1 := by
      rw [val_awayVar', Localization.mk_mul, mul_one]
      rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      exact ⟨1, by simp [pow_one]; ring⟩
    have happ := congrArg (Localization.awayLift (dehomogenizeAux R i) (X i)
      (isUnit_iff_exists_inv.mpr ⟨1, by simp⟩)) hval2
    rw [map_mul, dehomog_lift_mk_one, dehomog_lift_mk_one] at happ
    simp only [dehomogenizeAux_X_self, mul_one, dehomogenizeAux_X_ne R i j.2] at happ
    change Localization.awayLift (dehomogenizeAux R i) (X i)
      (isUnit_iff_exists_inv.mpr ⟨1, by simp⟩) (awayVar R i j).val = X j
    exact happ

/-- `dehomogenizeAt` on the normal form `p / X_iⁿ`. -/
lemma dehomogenizeAt_mk (i : σ) {n : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ homogeneousSubmodule σ R (n • 1)) :
    dehomogenizeAt R i
        (Away.mk _ (X_mem_homogeneousSubmodule_one R i) n p hp) =
      dehomogenizeAux R i p := by
  have h1 : (Away.mk _ (X_mem_homogeneousSubmodule_one R i) n p hp).val *
      Localization.mk ((X i : MvPolynomial σ R) ^ n) 1 = Localization.mk p 1 := by
    rw [Away.val_mk, Localization.mk_mul, mul_one]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp [mul_comm]⟩
  have happ := congrArg (Localization.awayLift (dehomogenizeAux R i) (X i)
    (isUnit_iff_exists_inv.mpr ⟨1, by simp⟩)) h1
  rw [map_mul, dehomog_lift_mk_one, dehomog_lift_mk_one] at happ
  simp only [map_pow, dehomogenizeAux_X_self, one_pow, mul_one] at happ
  exact happ

/-- The composite `R[X] → (R[X]_{X i})₀ →(val) Localization`, through dehomogenisation
and homogenisation — the working ring hom for the clearing computation. -/
private noncomputable def clearingHom (i : σ) :
    MvPolynomial σ R →+* Localization (Submonoid.powers (X i : MvPolynomial σ R)) :=
  (valRingHom _).comp ((homogenizeAt R i).comp (dehomogenizeAux R i))

private lemma clearingHom_C (i : σ) (r : R) :
    clearingHom R i (C r) = Localization.mk (C r) 1 := by
  simp only [clearingHom, RingHom.comp_apply, dehomogenizeAux_C]
  change (homogenizeAt R i (C r)).val = _
  rw [homogenizeAt, eval₂Hom_C]
  exact val_awayConst R i r

private lemma clearingHom_X_self (i : σ) : clearingHom R i (X i) = 1 := by
  simp only [clearingHom, RingHom.comp_apply, dehomogenizeAux_X_self, map_one]

private lemma clearingHom_X_ne (i : σ) {j : σ} (h : j ≠ i) :
    clearingHom R i (X j) =
      Localization.mk (X j) (⟨(X i : MvPolynomial σ R) ^ 1, 1, rfl⟩ :
        Submonoid.powers (X i : MvPolynomial σ R)) := by
  simp only [clearingHom, RingHom.comp_apply, dehomogenizeAux_X_ne R i h]
  change (homogenizeAt R i (X ⟨j, h⟩)).val = _
  rw [homogenizeAt, eval₂Hom_X']
  exact val_awayVar' R i ⟨j, h⟩

/-- Uniform clearing identity for variables: `Φ(X_j) · ψ(X_i) = ψ(X_j)` for every `j`
(including `j = i`), where `ψ` is the localization map. -/
private lemma clearingHom_X_mul (i j : σ) :
    clearingHom R i (X j) * algebraMap (MvPolynomial σ R) _ (X i) =
      algebraMap (MvPolynomial σ R)
        (Localization (Submonoid.powers (X i : MvPolynomial σ R))) (X j) := by
  by_cases h : j = i
  · subst h
    rw [clearingHom_X_self, one_mul]
  · rw [clearingHom_X_ne R i h, ← Localization.mk_one_eq_algebraMap,
      ← Localization.mk_one_eq_algebraMap, Localization.mk_mul, mul_one]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp [pow_one, mul_comm]⟩

/-- Monomial clearing: homogenising the dehomogenisation of a degree-`n` homogeneous
polynomial recovers `p / X_iⁿ`, expressed at the level of the ambient localization. -/
private lemma clearingHom_mul_pow (i : σ) {p : MvPolynomial σ R} {n : ℕ}
    (hp : p.IsHomogeneous n) :
    clearingHom R i p * algebraMap (MvPolynomial σ R) _ ((X i) ^ n) =
      algebraMap (MvPolynomial σ R)
        (Localization (Submonoid.powers (X i : MvPolynomial σ R))) p := by
  classical
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : (d.sum fun _ e => e) = n := by
    simpa [Finsupp.weight_apply, smul_eq_mul, mul_one, Finsupp.sum]
      using hp (mem_support_iff.mp hd)
  rw [monomial_eq, map_mul, map_mul, ← hdeg]
  have hC : clearingHom R i (C (coeff d p)) =
      algebraMap (MvPolynomial σ R) _ (C (coeff d p)) := by
    rw [clearingHom_C, Localization.mk_one_eq_algebraMap]
  rw [hC, mul_assoc]
  congr 1
  -- Π Φ(X_j)^{d_j} · ψ(X_i)^{Σ d_j} = Π ψ(X_j)^{d_j}
  unfold Finsupp.prod Finsupp.sum
  beta_reduce
  have hΦ : clearingHom R i (∏ j ∈ d.support, X j ^ d j) =
      ∏ j ∈ d.support, clearingHom R i (X j) ^ d j := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun j _ => map_pow _ _ _
  have hψp : algebraMap (MvPolynomial σ R)
        (Localization (Submonoid.powers (X i : MvPolynomial σ R)))
        (∏ j ∈ d.support, X j ^ d j) =
      ∏ j ∈ d.support, (algebraMap (MvPolynomial σ R)
        (Localization (Submonoid.powers (X i : MvPolynomial σ R))) (X j)) ^ d j := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun j _ => map_pow _ _ _
  have hψX : algebraMap (MvPolynomial σ R)
        (Localization (Submonoid.powers (X i : MvPolynomial σ R)))
        ((X i) ^ (∑ j ∈ d.support, d j)) =
      ∏ j ∈ d.support, (algebraMap (MvPolynomial σ R)
        (Localization (Submonoid.powers (X i : MvPolynomial σ R))) (X i)) ^ d j := by
    rw [map_pow]
    exact (Finset.prod_pow_eq_pow_sum _ _ _).symm
  rw [hΦ, hψX, hψp, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => by rw [← mul_pow, clearingHom_X_mul]

/-- Homogenising after dehomogenising is the identity on the chart ring. -/
lemma homogenizeAt_comp_dehomogenizeAt (i : σ) :
    (homogenizeAt R i).comp (dehomogenizeAt R i) = RingHom.id _ := by
  refine RingHom.ext fun z => ?_
  obtain ⟨n, p, hp, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective _ (X_mem_homogeneousSubmodule_one R i) z
  rw [RingHom.comp_apply, dehomogenizeAt_mk, RingHom.id_apply]
  apply val_injective
  have hphom : p.IsHomogeneous n := by
    have := (mem_homogeneousSubmodule _ _).mp hp
    simpa using this
  have h1 := clearingHom_mul_pow R i hphom
  have h2 : (Away.mk _ (X_mem_homogeneousSubmodule_one R i) n p hp).val *
      algebraMap (MvPolynomial σ R) _ ((X i) ^ n) =
      algebraMap (MvPolynomial σ R)
        (Localization (Submonoid.powers (X i : MvPolynomial σ R))) p := by
    rw [Away.val_mk, ← Localization.mk_one_eq_algebraMap, ← Localization.mk_one_eq_algebraMap,
      Localization.mk_mul, mul_one]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp [mul_comm]⟩
  have hunit : IsUnit (algebraMap (MvPolynomial σ R)
      (Localization (Submonoid.powers (X i : MvPolynomial σ R))) ((X i) ^ n)) :=
    IsLocalization.map_units _
      (⟨(X i) ^ n, n, rfl⟩ : Submonoid.powers (X i : MvPolynomial σ R))
  change clearingHom R i p = _
  exact hunit.mul_right_cancel (h1.trans h2.symm)

/-- **The chart of projective space at `X i`**: the degree-zero homogeneous
localization away from `X i` is a polynomial ring on the remaining variables. -/
noncomputable def chartRingEquiv (i : σ) :
    Away (homogeneousSubmodule σ R) (X i : MvPolynomial σ R) ≃+*
      MvPolynomial {j : σ // j ≠ i} R :=
  RingEquiv.ofRingHom (dehomogenizeAt R i) (homogenizeAt R i)
    (dehomogenizeAt_comp_homogenizeAt R i) (homogenizeAt_comp_dehomogenizeAt R i)

end MvPolynomial
