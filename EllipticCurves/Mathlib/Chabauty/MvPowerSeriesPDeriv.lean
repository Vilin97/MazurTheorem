/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
-- Vendored from the Chabauty project (`Chabauty/ForMathlib/MvPowerSeriesPDeriv.lean`).

module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.MvPowerSeries.Substitution

public import Mathlib.RingTheory.MvPowerSeries.PiTopology

@[expose] public section

/-!
# Formal partial derivatives of multivariate power series

`MvPowerSeries.pderiv s` is the formal partial derivative with respect to the variable
`s`, as an `R`-linear map. Beyond the basic calculus (`MvPowerSeries.pderiv_C`,
`MvPowerSeries.pderiv_X`, compatibility with polynomials `MvPowerSeries.pderiv_coe`),
the Leibniz rule (`MvPowerSeries.pderiv_mul`) and the chain rule for substitution
(`MvPowerSeries.pderiv_subst`) are proved by continuity and density from the polynomial
case: both sides are continuous for the product topologies with *any* ring topology, so
the proofs instal the discrete topology and the statements remain topology-free.

Also provides `MvPowerSeries.continuous_subst`: substitution is continuous for the
product topologies over a topological ring of coefficients — each coefficient of
`subst a f` is a fixed finite linear combination of coefficients of `f`.
-/


open Filter Topology
open scoped MvPowerSeries.WithPiTopology

namespace MvPowerSeries

section subst

variable {σ R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- Substitution of power series is continuous, coefficientwise: each coefficient of
`subst a f` is a fixed finite linear combination of coefficients of `f`.
This generalizes `MvPowerSeries.continuous_subst` from discrete coefficients to any
topological ring of coefficients. -/
theorem continuous_subst' {τ : Type*} {a : τ → MvPowerSeries σ R}
    (ha : MvPowerSeries.HasSubst a) :
    Continuous (MvPowerSeries.subst a : MvPowerSeries τ R → MvPowerSeries σ R) := by
  classical
  have hc (e : σ →₀ ℕ) : (Function.support fun d : τ →₀ ℕ ↦
      MvPowerSeries.coeff e (d.prod fun s i ↦ (a s) ^ i)).Finite := by
    have h1 := MvPowerSeries.coeff_subst_finite ha
      ((fun _ ↦ 1) : MvPowerSeries τ R) e
    simpa [Function.HasFiniteSupport, show ∀ d, MvPowerSeries.coeff (R := R) d
      ((fun _ ↦ 1) : MvPowerSeries τ R) = 1 from fun d ↦ rfl] using h1
  refine continuous_pi fun e ↦ ?_
  change Continuous fun f : MvPowerSeries τ R ↦ MvPowerSeries.coeff e (MvPowerSeries.subst a f)
  have heq : (fun f : MvPowerSeries τ R ↦ MvPowerSeries.coeff e (MvPowerSeries.subst a f))
      = fun f ↦ ∑ d ∈ (hc e).toFinset,
          MvPowerSeries.coeff d f * MvPowerSeries.coeff e (d.prod fun s i ↦ (a s) ^ i) := by
    funext f
    rw [MvPowerSeries.coeff_subst ha]
    rw [finsum_eq_sum_of_support_subset]
    · exact Finset.sum_congr rfl fun d _ ↦ smul_eq_mul _ _
    · intro d hd
      rw [Function.mem_support] at hd
      rw [Set.Finite.coe_toFinset, Function.mem_support]
      exact fun h0 ↦ hd (by rw [h0, smul_zero])
  rw [heq]
  exact continuous_finsetSum _ fun d _ ↦
    (MvPowerSeries.WithPiTopology.continuous_coeff R d).mul continuous_const

end subst

variable {σ R : Type*} [CommRing R]

/-- Substitution along families with vanishing constant coefficients preserves the
constant coefficient. -/
theorem constantCoeff_subst_of_constantCoeff_zero {τ : Type*}
    {a : τ → MvPowerSeries σ R} (ha : HasSubst a)
    (ha' : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries τ R) :
    constantCoeff (subst a f) = constantCoeff f := by
  classical
  rw [constantCoeff_subst ha, finsum_eq_single _ 0 ?_]
  · simp
  · intro d hd
    obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hd
    rw [Finsupp.prod, map_prod, smul_eq_mul,
      Finset.prod_eq_zero hs (by
        rw [map_pow, ha' s, zero_pow (Nat.pos_of_ne_zero
          (Finsupp.mem_support_iff.mp hs)).ne']), mul_zero]

/-- The formal partial derivative of a multivariate power series. -/
noncomputable def pderiv (s : σ) : MvPowerSeries σ R →ₗ[R] MvPowerSeries σ R where
  toFun h := fun d ↦ ((d s + 1 : ℕ) : R) * coeff (d + Finsupp.single s 1) h
  map_add' f g := by
    funext d
    simp only [map_add, mul_add]
    rfl
  map_smul' c f := by
    funext d
    simp only [map_smul, smul_eq_mul, RingHom.id_apply]
    change _ * (c * _) = c * (_ * _)
    ring

@[simp]
theorem coeff_pderiv (s : σ) (h : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    coeff d (pderiv s h) = ((d s + 1 : ℕ) : R) * coeff (d + Finsupp.single s 1) h := rfl

/- Compatibility with the LeanPool mathlib pin, which predates
`MvPolynomial.coeff_pderiv`. -/
private theorem mvPolynomial_coeff_pderiv (s : σ) (p : MvPolynomial σ R)
    (d : σ →₀ ℕ) :
    MvPolynomial.coeff d (MvPolynomial.pderiv s p) =
      MvPolynomial.coeff (d + Finsupp.single s 1) p * (d s + 1) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add, MvPolynomial.coeff_add, hp, hq]
      ring
  | monomial n a =>
      rw [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial,
        MvPolynomial.coeff_monomial]
      by_cases h : n = d + Finsupp.single s 1
      · subst n
        simp
      · simp only [h, ↓reduceIte, zero_mul]
        by_cases hn : n s = 0
        · simp [hn]
        apply if_neg
        rwa [tsub_eq_iff_eq_add_of_le (fun _ ↦ by grind)]

theorem pderiv_coe (s : σ) (p : MvPolynomial σ R) :
    pderiv s (p : MvPowerSeries σ R)
      = (MvPolynomial.pderiv s p : MvPolynomial σ R) := by
  ext d
  rw [coeff_pderiv, MvPolynomial.coeff_coe, MvPolynomial.coeff_coe,
    mvPolynomial_coeff_pderiv]
  push_cast
  ring

@[simp]
theorem pderiv_C (s : σ) (c : R) : pderiv s (C c : MvPowerSeries σ R) = 0 := by
  classical
  ext d
  rw [coeff_pderiv, coeff_C, if_neg, mul_zero, map_zero]
  intro h0
  have := DFunLike.congr_fun h0 s
  simp at this

@[simp]
theorem pderiv_one (s : σ) : pderiv s (1 : MvPowerSeries σ R) = 0 := by
  rw [← map_one (C (σ := σ) (R := R))]
  exact pderiv_C s 1

theorem continuous_pderiv [TopologicalSpace R] [IsTopologicalSemiring R] (s : σ) :
    Continuous (pderiv (R := R) s : MvPowerSeries σ R → MvPowerSeries σ R) := by
  refine continuous_pi fun d ↦ ?_
  change Continuous fun h : MvPowerSeries σ R ↦
    ((d s + 1 : ℕ) : R) * coeff (d + Finsupp.single s 1) h
  exact continuous_const.mul (WithPiTopology.continuous_coeff R _)

/-- The Leibniz rule for formal partial derivatives of power series. -/
theorem pderiv_mul (s : σ) (f g : MvPowerSeries σ R) :
    pderiv s (f * g) = f * pderiv s g + pderiv s f * g := by
  let : UniformSpace R := ⊥
  let : DiscreteTopology R := ⟨rfl⟩
  have key := MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries (σ := σ) (R := R)
  -- first, the case of a polynomial second factor, by density in the first
  have step1 : ∀ (q : MvPolynomial σ R) (f : MvPowerSeries σ R),
      pderiv s (f * (q : MvPowerSeries σ R))
        = f * pderiv s (q : MvPowerSeries σ R) + pderiv s f * (q : MvPowerSeries σ R) := by
    intro q f
    have h1 : Continuous fun f : MvPowerSeries σ R ↦
        pderiv s (f * (q : MvPowerSeries σ R)) :=
      (continuous_pderiv s).comp (continuous_mul_const _)
    have h2 : Continuous fun f : MvPowerSeries σ R ↦
        f * pderiv s (q : MvPowerSeries σ R) + pderiv s f * (q : MvPowerSeries σ R) :=
      (continuous_mul_const _).add ((continuous_pderiv s).mul_const _)
    refine congrFun (key.equalizer h1 h2 (funext fun p ↦ ?_)) f
    change pderiv s ((p : MvPowerSeries σ R) * (q : MvPowerSeries σ R))
      = (p : MvPowerSeries σ R) * pderiv s (q : MvPowerSeries σ R)
        + pderiv s (p : MvPowerSeries σ R) * (q : MvPowerSeries σ R)
    rw [show (p : MvPowerSeries σ R) * (q : MvPowerSeries σ R)
        = ((p * q : MvPolynomial σ R) : MvPowerSeries σ R) by push_cast; ring]
    rw [pderiv_coe, pderiv_coe, pderiv_coe]
    have hleib := (MvPolynomial.pderiv s).leibniz p q
    rw [hleib]
    simp only [smul_eq_mul]
    push_cast [MvPolynomial.coe_add, MvPolynomial.coe_mul]
    ring
  -- then vary the second factor by density
  have h1 : Continuous fun g : MvPowerSeries σ R ↦ pderiv s (f * g) :=
    (continuous_pderiv s).comp (continuous_const.mul continuous_id)
  have h2 : Continuous fun g : MvPowerSeries σ R ↦ f * pderiv s g + pderiv s f * g :=
    (continuous_const.mul (continuous_pderiv s)).add (continuous_const.mul continuous_id)
  exact congrFun (key.equalizer h1 h2 (funext fun q ↦ step1 q f)) g

@[simp]
theorem pderiv_X [DecidableEq σ] (s t : σ) :
    pderiv s (X t : MvPowerSeries σ R) = if t = s then 1 else 0 := by
  rw [← MvPolynomial.coe_X, pderiv_coe, MvPolynomial.pderiv_X]
  simp only [Pi.single_apply]
  split <;> simp

/-- The chain rule for formal partial derivatives of a substitution. -/
theorem pderiv_subst {τ : Type*} [Fintype τ] {a : τ → MvPowerSeries σ R}
    (ha : HasSubst a) (s : σ) (f : MvPowerSeries τ R) :
    pderiv s (subst a f) = ∑ t : τ, subst a (pderiv t f) * pderiv s (a t) := by
  classical
  let : UniformSpace R := ⊥
  let : DiscreteTopology R := ⟨rfl⟩
  have key := MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries (σ := τ) (R := R)
  have h1 : Continuous fun f : MvPowerSeries τ R ↦ pderiv s (subst a f) :=
    (continuous_pderiv s).comp (continuous_subst' ha)
  have h2 : Continuous fun f : MvPowerSeries τ R ↦
      ∑ t : τ, subst a (pderiv t f) * pderiv s (a t) :=
    continuous_finsetSum _ fun t _ ↦
      ((continuous_subst' ha).comp
        (continuous_pderiv t)).mul_const _
  refine congrFun (key.equalizer h1 h2 (funext fun p ↦ ?_)) f
  change pderiv s (subst a (p : MvPowerSeries τ R))
    = ∑ t : τ, subst a (pderiv t (p : MvPowerSeries τ R)) * pderiv s (a t)
  induction p using MvPolynomial.induction_on with
  | C c =>
    have hCc : subst a (C c : MvPowerSeries τ R) = C c := by
      rw [← coe_substAlgHom ha]
      exact (substAlgHom ha).commutes c
    have h0 : subst a (0 : MvPowerSeries τ R) = 0 := by
      rw [← MvPowerSeries.coe_substAlgHom ha]
      exact map_zero _
    rw [MvPolynomial.coe_C, hCc, pderiv_C]
    symm
    refine Finset.sum_eq_zero fun t _ ↦ ?_
    rw [pderiv_C, h0, zero_mul]
  | add p q hp hq =>
    push_cast
    rw [MvPowerSeries.subst_add ha, map_add, hp, hq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [map_add, MvPowerSeries.subst_add ha]
    ring
  | mul_X p i ih =>
    push_cast
    rw [MvPowerSeries.subst_mul ha, MvPowerSeries.subst_X ha, pderiv_mul, ih]
    have hexp (t : τ) : subst a (pderiv t ((p : MvPowerSeries τ R) * X i))
        = (if i = t then subst a (p : MvPowerSeries τ R) else 0)
          + subst a (pderiv t (p : MvPowerSeries τ R)) * a i := by
      rw [pderiv_mul, pderiv_X, MvPowerSeries.subst_add ha, MvPowerSeries.subst_mul ha,
        MvPowerSeries.subst_mul ha, MvPowerSeries.subst_X ha]
      split
      · rw [← MvPowerSeries.coe_substAlgHom ha, map_one, mul_one]
      · rw [← MvPowerSeries.coe_substAlgHom ha, map_zero, mul_zero]
    simp only [hexp, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    ring

/-- Formal partial derivatives commute. -/
theorem pderiv_comm (s t : σ) (h : MvPowerSeries σ R) :
    pderiv s (pderiv t h) = pderiv t (pderiv s h) := by
  ext d
  rw [coeff_pderiv, coeff_pderiv, coeff_pderiv, coeff_pderiv,
    add_right_comm d (Finsupp.single s 1) (Finsupp.single t 1)]
  rcases eq_or_ne s t with rfl | hst
  · ring
  · have h1 : (d + Finsupp.single s 1 : σ →₀ ℕ) t = d t := by
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (Ne.symm hst), add_zero]
    have h2 : (d + Finsupp.single t 1 : σ →₀ ℕ) s = d s := by
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hst, add_zero]
    rw [h1, h2]
    ring

/-- A substitution whose family is annihilated by `∂_s` is annihilated by `∂_s`. -/
theorem pderiv_subst_eq_zero {τ : Type*} [Finite τ] {a : τ → MvPowerSeries σ R}
    (ha : HasSubst a) (s : σ) (hz : ∀ t, pderiv s (a t) = 0) (f : MvPowerSeries τ R) :
    pderiv s (subst a f) = 0 := by
  cases nonempty_fintype τ
  rw [pderiv_subst ha]
  exact Finset.sum_eq_zero fun t _ ↦ by rw [hz t, mul_zero]

theorem coeff_X_mul_pderiv (s : σ) (f : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    coeff d (X s * pderiv s f) = ((d s : ℕ) : R) * coeff d f := by
  classical
  rw [mul_comm, show (X s : MvPowerSeries σ R) = monomial (Finsupp.single s 1) 1 from rfl,
    coeff_mul_monomial]
  rcases eq_or_ne (d s) 0 with h0 | h0
  · rw [if_neg fun hle ↦ by simpa [h0] using Finsupp.single_le_iff.mp hle, h0]
    simp
  · have hle : Finsupp.single s 1 ≤ d :=
      Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h0)
    rw [if_pos hle, mul_one, coeff_pderiv, tsub_add_cancel_of_le hle, Finsupp.tsub_apply,
      Finsupp.single_eq_same]
    congr 2
    lia

/-- The Euler identity for formal power series: the operator `∑ s, X s * ∂/∂X s` acts on
the degree-`n` homogeneous part as multiplication by `n`. -/
theorem coeff_sum_X_mul_pderiv [Fintype σ] (f : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    coeff d (∑ s, X s * pderiv s f) = ((d.degree : ℕ) : R) * coeff d f := by
  rw [map_sum, Finset.sum_congr rfl fun s _ ↦ coeff_X_mul_pderiv s f d, ← Finset.sum_mul,
    Finsupp.degree_eq_sum]
  push_cast
  rfl

/-- A power series with zero constant term all of whose partial derivatives vanish is
zero, provided the coefficient ring has no additive torsion (e.g. characteristic zero
domains). -/
theorem eq_zero_of_pderiv_eq_zero [NoZeroSMulDivisors ℕ R] {f : MvPowerSeries σ R}
    (h : ∀ s, pderiv s f = 0) (h0 : constantCoeff f = 0) : f = 0 := by
  ext d
  rw [map_zero]
  rcases eq_or_ne d 0 with rfl | hd
  · exact h0
  · obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hd
    have hle : Finsupp.single s 1 ≤ d :=
      Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hs))
    have hc := congrArg (coeff (d - Finsupp.single s 1)) (h s)
    rw [coeff_pderiv, tsub_add_cancel_of_le hle, map_zero, ← nsmul_eq_mul] at hc
    rcases smul_eq_zero.mp hc with h1 | h2
    · exact absurd h1 (Nat.succ_ne_zero _)
    · exact h2

theorem coeff_rename_equiv {τ : Type*} (e : σ ≃ τ) (f : MvPowerSeries σ R) (d : τ →₀ ℕ) :
    coeff d (rename (⇑e) f) = coeff (Finsupp.equivMapDomain e.symm d) f := by
  have hemb : Finsupp.embDomain e.toEmbedding = Finsupp.equivMapDomain (M := ℕ) e := by
    funext v
    rw [Finsupp.embDomain_eq_mapDomain, Finsupp.equivMapDomain_eq_mapDomain]
    rfl
  have hd : Finsupp.embDomain e.toEmbedding (Finsupp.equivMapDomain e.symm d) = d := by
    rw [hemb, ← Finsupp.equivMapDomain_trans, Equiv.symm_trans_self,
      Finsupp.equivMapDomain_refl]
  calc coeff d (rename (⇑e) f)
      = coeff (Finsupp.embDomain e.toEmbedding (Finsupp.equivMapDomain e.symm d))
          (rename (⇑e) f) := by rw [hd]
    _ = coeff (Finsupp.equivMapDomain e.symm d) f := coeff_embDomain_rename _ _ _

/-- Formal partial derivatives commute with variable renaming along an equivalence. -/
theorem rename_pderiv {τ : Type*} (e : σ ≃ τ) (s : σ) (f : MvPowerSeries σ R) :
    rename (⇑e) (pderiv s f) = pderiv (e s) (rename (⇑e) f) := by
  ext d
  rw [coeff_pderiv, coeff_rename_equiv, coeff_rename_equiv, coeff_pderiv]
  have h1 : Finsupp.equivMapDomain e.symm (d + Finsupp.single (e s) 1)
      = Finsupp.equivMapDomain e.symm d + Finsupp.single s 1 := by
    ext t
    classical
    simp [Finsupp.single_apply, e.injective.eq_iff]
  have h2 : Finsupp.equivMapDomain e.symm d s = d (e s) := by
    simp
  rw [h1, h2]

/-- Formal partial derivatives commute with a coefficient ring homomorphism. -/
theorem map_pderiv {S : Type*} [CommRing S] (f : R →+* S) (s : σ) (g : MvPowerSeries σ R) :
    map f (pderiv s g) = pderiv s (map f g) := by
  ext d
  rw [coeff_map, coeff_pderiv, coeff_pderiv, coeff_map, map_mul, map_natCast]

end MvPowerSeries

end
