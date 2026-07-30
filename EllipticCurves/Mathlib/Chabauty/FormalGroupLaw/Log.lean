/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
-- Vendored from the Chabauty project (`Chabauty/Series/FormalGroupLaw/Log.lean`).

module

public import EllipticCurves.Mathlib.Chabauty.FormalGroupLaw.Invariance
public import Mathlib.NumberTheory.Padics.PadicVal.Defs

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import EllipticCurves.Mathlib.Chabauty.PadicValNat
public import EllipticCurves.Mathlib.Chabauty.LocalRing

@[expose] public section

/-!
# The formal logarithm of a formal group law

Over a field `K`, the formal logarithm `ChabautyColeman.FormalGroupLaw.log` is the radial
(Euler) antiderivative `ChabautyColeman.eulerAntideriv` of the row `∑_j (M⁻¹)_{ij} X_j` of the
invariant differential; `ChabautyColeman.FormalGroupLaw.exp` is its compositional inverse. That
`log`'s differential is the invariant differential (`pderiv_log`) uses the closedness proved in
`Chabauty.Series.FormalGroupLaw.Invariance` together with `CharZero`. Over a `p`-adic base,
`coeff_log_map_padic`/`coeff_log_map_scale` bound the `p`-power denominators and
`exists_integral_scaled_log` produces the `p`-scaled integral form.

## Main definitions
* `ChabautyColeman.eulerAntideriv`: the radial antiderivative (divide the degree-`k` part by `k`).
* `ChabautyColeman.FormalGroupLaw.log`, `ChabautyColeman.FormalGroupLaw.exp`.

## Main statements
* `ChabautyColeman.FormalGroupLaw.log_comp_exp`, `.exp_comp_log`: `log` and `exp` are inverse.
* `ChabautyColeman.FormalGroupLaw.pderiv_log`, `.log_subst_F`: the differential of `log`.
* `ChabautyColeman.FormalGroupLaw.exists_integral_scaled_log`: the `p`-scaled integral logarithm.

Blueprint nodes: `def:fgl-log`, `lem:fgl-log`.
-/


open MvPowerSeries IsLocalRing Filter Topology
open scoped MvPowerSeries.WithPiTopology

namespace ChabautyColeman
/-! ### The radial (Euler) antiderivative -/

section euler

variable {ι K : Type*} [Field K]

/-- The radial (Euler) antiderivative of a multivariate power series: divide the
degree-`k` homogeneous part by `k`. (At `k = 0` the junk value `(0 : K)⁻¹ = 0` kills
the constant term, as intended.) -/
noncomputable def eulerAntideriv (g : MvPowerSeries ι K) : MvPowerSeries ι K :=
  fun d ↦ (d.degree : K)⁻¹ * MvPowerSeries.coeff d g

theorem coeff_eulerAntideriv (g : MvPowerSeries ι K) (d : ι →₀ ℕ) :
    MvPowerSeries.coeff d (eulerAntideriv g)
      = (d.degree : K)⁻¹ * MvPowerSeries.coeff d g := rfl

@[simp]
theorem constantCoeff_eulerAntideriv (g : MvPowerSeries ι K) :
    constantCoeff (eulerAntideriv g) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_eulerAntideriv]
  simp

end euler

namespace FormalGroupLaw

/-! ### The formal logarithm and exponential -/

section log

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (Φ : FormalGroupLaw K ι)

/-- The formal logarithm of a formal group law over a field of characteristic zero:
the radial antiderivative of the row `∑_j (M⁻¹)_{ij} X_j` of the invariant
differential. That its differential is the invariant differential is proved with the
invariance identities. -/
noncomputable def log (i : ι) : MvPowerSeries ι K :=
  eulerAntideriv (∑ j, Φ.diffMatrix⁻¹ i j * MvPowerSeries.X j)

@[simp]
theorem constantCoeff_log (i : ι) : constantCoeff (Φ.log i) = 0 :=
  constantCoeff_eulerAntideriv _

/-- The linear term of the logarithm is `X i`. -/
theorem coeff_single_log (i j : ι) :
    MvPowerSeries.coeff (Finsupp.single j 1) (Φ.log i) = if i = j then 1 else 0 := by
  classical
  rw [log, coeff_eulerAntideriv, map_sum]
  have hterm (l : ι) : MvPowerSeries.coeff (Finsupp.single j 1)
      (Φ.diffMatrix⁻¹ i l * MvPowerSeries.X l)
      = if l = j then constantCoeff (Φ.diffMatrix⁻¹ i l) else 0 := by
    have hX : (MvPowerSeries.X l : MvPowerSeries ι K)
        = MvPowerSeries.monomial (Finsupp.single l 1) 1 := rfl
    by_cases hl : l = j
    · subst hl
      rw [if_pos rfl, hX, MvPowerSeries.coeff_mul_monomial, if_pos le_rfl]
      simp
    · rw [if_neg hl, hX, MvPowerSeries.coeff_mul_monomial, if_neg]
      intro hle
      have h1 := Finsupp.le_def.mp hle l
      rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hl] at h1
      exact absurd h1 (by lia)
  rw [Finset.sum_congr rfl fun l _ ↦ hterm l,
    Finset.sum_ite_eq' Finset.univ j (fun l ↦ constantCoeff (Φ.diffMatrix⁻¹ i l)),
    if_pos (Finset.mem_univ j)]
  have h2 : (Φ.diffMatrix⁻¹.map (constantCoeff (R := K))) i j
      = (1 : Matrix ι ι K) i j := by
    rw [Φ.diffMatrixInv_map_constantCoeff]
  rw [Matrix.map_apply, Matrix.one_apply] at h2
  rw [h2]
  simp [Finsupp.degree_single]

/-- The logarithm has zero constant term and identity linear part, so `Λ i - X i` has
order `≥ 2`. -/
theorem log_sub_X_order (i : ι) (e : ι →₀ ℕ) (he : e.degree ≤ 1) :
    coeff e (Φ.log i - X i) = 0 := by
  rw [map_sub]
  rcases Nat.lt_or_ge e.degree 1 with h | h
  · have h0 : e = 0 := (Finsupp.degree_eq_zero_iff e).mp (by lia)
    subst h0
    rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply,
      Φ.constantCoeff_log, constantCoeff_X, sub_zero]
  · have he1 : e.degree = 1 := by lia
    obtain ⟨j, rfl⟩ : ∃ j, e = Finsupp.single j 1 := by
      have hne0 : e ≠ 0 := by intro h0; rw [h0, map_zero] at he1; simp at he1
      obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr hne0
      refine ⟨j, ?_⟩
      have hej : 1 ≤ e j := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
      have hejle : e j ≤ 1 := he1 ▸ Finsupp.le_degree j e
      ext s
      rcases eq_or_ne s j with rfl | hs
      · rw [Finsupp.single_eq_same]; lia
      · rw [Finsupp.single_eq_of_ne hs]
        by_contra hne
        have hes : 1 ≤ e s := Nat.one_le_iff_ne_zero.mpr hne
        have hsum : e j + e s ≤ e.degree := by
          have hsub : ({j, s} : Finset ι) ⊆ e.support := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact hj
            · exact Finsupp.mem_support_iff.mpr hne
          calc e j + e s = ∑ x ∈ ({j, s} : Finset ι), e x := (Finset.sum_pair (Ne.symm hs)).symm
            _ ≤ ∑ x ∈ e.support, e x := Finset.sum_le_sum_of_subset hsub
            _ = e.degree := (Finsupp.degree_apply e).symm
        lia
    rw [Φ.coeff_single_log, coeff_X]
    rcases eq_or_ne i j with rfl | hij
    · simp
    · rw [if_neg hij, if_neg (fun h ↦ hij (Finsupp.single_left_injective one_ne_zero h).symm),
        sub_zero]

/-- The formal exponential of a formal group law: the compositional inverse of the
logarithm. -/
noncomputable def exp (i : ι) : MvPowerSeries ι K := invSubst Φ.log i

/-- `Λ ∘ Exp = X`: the logarithm composed with the exponential is the identity. -/
theorem log_comp_exp (i : ι) : subst Φ.exp (Φ.log i) = X i :=
  subst_invSubst (log_sub_X_order Φ) i

/-- `Exp ∘ Λ = X`: the exponential composed with the logarithm is the identity. -/
theorem exp_comp_log (i : ι) : subst Φ.log (Φ.exp i) = X i :=
  subst_a_invSubst (log_sub_X_order Φ) i

-- `∂_k` of the invariant differential row, rewritten with closedness
private lemma pderiv_log_row (i k : ι) :
    pderiv k (∑ j, Φ.diffMatrix⁻¹ i j * MvPowerSeries.X j)
      = (∑ j, MvPowerSeries.X j * pderiv j (Φ.diffMatrix⁻¹ i k)) + Φ.diffMatrix⁻¹ i k := by
  rw [map_sum]
  have hterm (j : ι) : pderiv k (Φ.diffMatrix⁻¹ i j * MvPowerSeries.X j)
      = MvPowerSeries.X j * pderiv j (Φ.diffMatrix⁻¹ i k)
        + if j = k then Φ.diffMatrix⁻¹ i j else 0 := by
    rw [pderiv_mul, pderiv_X, Φ.pderiv_diffMatrixInv_symm i j k, mul_comm
      (pderiv j (Φ.diffMatrix⁻¹ i k)) (MvPowerSeries.X j), add_comm]
    simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_congr rfl fun j _ ↦ hterm j, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ k fun j ↦ Φ.diffMatrix⁻¹ i j,
    if_pos (Finset.mem_univ k)]

variable [CharZero K]

/-- The differential of the formal logarithm is the invariant differential:
`∂_k Λ_i = (M⁻¹)_{ik}`. This is where characteristic zero is used: the Euler operator
plus one is invertible on coefficients. -/
theorem pderiv_log (i k : ι) :
    pderiv k (Φ.log i) = Φ.diffMatrix⁻¹ i k := by
  ext d
  have hdeg : (d + Finsupp.single k 1).degree = d.degree + 1 := by
    rw [map_add, Finsupp.degree_single]
  have hn : ((d.degree + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr d.degree.succ_ne_zero
  have hkey := congrArg (coeff (R := K) d) (pderiv_log_row Φ i k)
  rw [map_add, coeff_pderiv, coeff_sum_X_mul_pderiv] at hkey
  rw [coeff_pderiv, log, coeff_eulerAntideriv, hdeg, mul_left_comm, hkey,
    show ((d.degree : ℕ) : K) * coeff d (Φ.diffMatrix⁻¹ i k) + coeff d (Φ.diffMatrix⁻¹ i k)
        = ((d.degree + 1 : ℕ) : K) * coeff d (Φ.diffMatrix⁻¹ i k) by push_cast; ring,
    inv_mul_cancel_left₀ hn]

-- `∂/∂Y_k` of both sides of the additivity identity agree
private lemma pderiv_inr_log_subst (i k : ι) :
    pderiv (Sum.inr k) (MvPowerSeries.subst (fun j : ι ↦ Φ.F j) (Φ.log i))
      = pderiv (Sum.inr k)
          (MvPowerSeries.subst (fun s : ι ↦ (X (Sum.inl s) : MvPowerSeries (ι ⊕ ι) K))
              (Φ.log i)
            + MvPowerSeries.subst (fun s : ι ↦ (X (Sum.inr s) : MvPowerSeries (ι ⊕ ι) K))
              (Φ.log i)) := by
  have hsum : pderiv (Sum.inr k) (MvPowerSeries.subst (fun j : ι ↦ Φ.F j) (Φ.log i))
      = ∑ a, MvPowerSeries.subst (fun j : ι ↦ Φ.F j) (Φ.diffMatrix⁻¹ i a)
          * pderiv (Sum.inr k) (Φ.F a) := by
    rw [pderiv_subst (hasSubst_F Φ)]
    exact Finset.sum_congr rfl fun a _ ↦ by rw [Φ.pderiv_log i a]
  rw [map_add, hsum, diffMatrixInv_subst_F Φ i k, pderiv_Yemb, Φ.pderiv_log i k,
    pderiv_subst_eq_zero hasSubst_Xemb (Sum.inr k) (fun s ↦ by rw [pderiv_X]; simp) (Φ.log i),
    zero_add]

-- `∂/∂X_k` of both sides of the additivity identity agree
private lemma pderiv_inl_log_subst (i k : ι) :
    pderiv (Sum.inl k) (MvPowerSeries.subst (fun j : ι ↦ Φ.F j) (Φ.log i))
      = pderiv (Sum.inl k)
          (MvPowerSeries.subst (fun s : ι ↦ (X (Sum.inl s) : MvPowerSeries (ι ⊕ ι) K))
              (Φ.log i)
            + MvPowerSeries.subst (fun s : ι ↦ (X (Sum.inr s) : MvPowerSeries (ι ⊕ ι) K))
              (Φ.log i)) := by
  have hsum : pderiv (Sum.inl k) (MvPowerSeries.subst (fun j : ι ↦ Φ.F j) (Φ.log i))
      = ∑ a, MvPowerSeries.subst (fun j : ι ↦ Φ.F j) (Φ.diffMatrix⁻¹ i a)
          * pderiv (Sum.inl k) (Φ.F a) := by
    rw [pderiv_subst (hasSubst_F Φ)]
    exact Finset.sum_congr rfl fun a _ ↦ by rw [Φ.pderiv_log i a]
  rw [map_add, hsum, diffMatrixInv_subst_F_inl Φ i k, pderiv_Xemb, Φ.pderiv_log i k,
    pderiv_subst_eq_zero hasSubst_Yemb (Sum.inl k)
      (fun s ↦ by rw [pderiv_X]; simp) (Φ.log i),
    add_zero]

/-- The formal logarithm is additive on the formal group law:
`Λ(F(X,Y)) = Λ(X) + Λ(Y)` as formal power series in the two blocks of variables. -/
theorem log_subst_F (i : ι) :
    MvPowerSeries.subst (fun j : ι ↦ Φ.F j) (Φ.log i)
      = MvPowerSeries.subst (fun s : ι ↦ (X (Sum.inl s) : MvPowerSeries (ι ⊕ ι) K))
          (Φ.log i)
        + MvPowerSeries.subst (fun s : ι ↦ (X (Sum.inr s) : MvPowerSeries (ι ⊕ ι) K))
          (Φ.log i) := by
  rw [← sub_eq_zero]
  refine eq_zero_of_pderiv_eq_zero (fun s ↦ ?_) ?_
  · rw [map_sub, sub_eq_zero]
    rcases s with k | k
    · exact pderiv_inl_log_subst Φ i k
    · exact pderiv_inr_log_subst Φ i k
  · rw [map_sub, map_add,
      MvPowerSeries.constantCoeff_subst_of_constantCoeff_zero (hasSubst_F Φ)
        (fun j ↦ Φ.zero_constantCoeff j),
      MvPowerSeries.constantCoeff_subst_of_constantCoeff_zero (hasSubst_Xemb)
        (fun s ↦ by simp),
      MvPowerSeries.constantCoeff_subst_of_constantCoeff_zero hasSubst_Yemb
        (fun s ↦ by simp),
      constantCoeff_log]
    ring

end log

/-! ### Base change of the logarithm; p-adic denominator bounds -/

section logBaseChange

variable {O K : Type*} [CommRing O] [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (Φ : FormalGroupLaw O ι)

-- the integral row `∑_j (M⁻¹)_{ij} X_j` base-changes to the row over `K`
private lemma map_log_row (f : O →+* K) (i : ι) :
    MvPowerSeries.map f (∑ j, Φ.diffMatrix⁻¹ i j * MvPowerSeries.X j)
      = ∑ j, (Φ.map f).diffMatrix⁻¹ i j * MvPowerSeries.X j := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_mul, MvPowerSeries.map_X, Φ.diffMatrixInv_map f, Matrix.map_apply]

/-- The coefficients of the logarithm of a base-changed formal group law: the numerator
`f (coeff_d (∑_j (M⁻¹)_{ij} X_j))` is integral (in the image of `f`), and the only
denominator is the total degree `deg d`. This is the "denominator bookkeeping" behind
convergence of the logarithm. -/
theorem coeff_log_map (f : O →+* K) (i : ι) (d : ι →₀ ℕ) :
    MvPowerSeries.coeff d ((Φ.map f).log i)
      = (d.degree : K)⁻¹ * f (MvPowerSeries.coeff d (∑ j, Φ.diffMatrix⁻¹ i j * MvPowerSeries.X j))
      := by
  rw [log, coeff_eulerAntideriv, ← Φ.map_log_row f, coeff_map]

variable [IsLocalRing O] {p : ℕ}

/-- The `p`-power denominator bound for the logarithm of a base-changed formal group law
over a local ring of residue characteristic `p`: multiplying the degree-`d` coefficient by
`f(p)^(v_p(deg d))` clears the denominator, landing in the image of `f`. So the only
denominators are powers of `p`, with exponent `v_p(deg d)`. -/
theorem coeff_log_map_padic (hp : p.Prime) (hpmem : (p : O) ∈ maximalIdeal O)
    (f : O →+* K) (hfp : f (p : O) ≠ 0) (i : ι) (d : ι →₀ ℕ) :
    ∃ c : O, f (p : O) ^ (padicValNat p d.degree)
      * MvPowerSeries.coeff d ((Φ.map f).log i) = f c := by
  rw [Φ.coeff_log_map f]
  set k := d.degree with hk
  set cd := MvPowerSeries.coeff d (∑ j, Φ.diffMatrix⁻¹ i j * MvPowerSeries.X j) with hcd
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · exact ⟨0, by simp [hk0]⟩
  set v := padicValNat p k with hv
  obtain ⟨m, hm⟩ : p ^ v ∣ k := pow_padicValNat_dvd
  have hnd : ¬ p ∣ m := by
    intro hd
    have hdvd : p ^ (v + 1) ∣ k := by rw [hm, pow_succ]; exact mul_dvd_mul_left _ hd
    have := (Nat.pow_dvd_iff_le_padicValNat hp.ne_one (by lia)).mp hdvd
    lia
  obtain ⟨u, hu⟩ := isUnit_natCast_of_not_dvd hp hpmem hnd
  refine ⟨(↑u⁻¹ : O) * cd, ?_⟩
  have hkK : (k : K) = f (p : O) ^ v * f (↑u : O) := by
    have hkO : (k : O) = (p : O) ^ v * (↑u : O) := by rw [hm]; push_cast; rw [← hu]
    rw [← map_natCast f k, hkO, map_mul, map_pow]
  have hbne : f (↑u : O) ≠ 0 := (u.isUnit.map f).ne_zero
  have hfu : (f (↑u : O))⁻¹ = f (↑u⁻¹ : O) :=
    inv_eq_of_mul_eq_one_right (by rw [← map_mul, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, map_one])
  rw [map_mul, ← hfu, hkK]
  field_simp

/-- The `p`-scaled logarithm has integral coefficients, with the growing `p`-power made
explicit: `p^(deg d) · coeff_d Λ = f(p^(deg d - v_p(deg d)) · c)`. Substituting
`X_j ↦ p·U_j` therefore lands the logarithm in `O⟦U⟧`, and the exponent
`deg d - v_p(deg d) → ∞` drives convergence on `(pO)^n`. -/
theorem coeff_log_map_scale (hp : p.Prime) (hpmem : (p : O) ∈ maximalIdeal O)
    (f : O →+* K) (hfp : f (p : O) ≠ 0) (i : ι) (d : ι →₀ ℕ) :
    ∃ c : O, f (p : O) ^ d.degree * MvPowerSeries.coeff d ((Φ.map f).log i)
      = f ((p : O) ^ (d.degree - padicValNat p d.degree) * c) := by
  obtain ⟨c, hc⟩ := Φ.coeff_log_map_padic hp hpmem f hfp i d
  refine ⟨c, ?_⟩
  have hvle : padicValNat p d.degree ≤ d.degree :=
    (padicValNat_le_nat_log d.degree).trans (Nat.log_le_self p d.degree)
  rw [map_mul, map_pow, ← hc, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hvle]

end logBaseChange

/-! ### The p-scaled integral logarithm -/

section logConvergence

variable {O K : Type*} [CommRing O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (Φ : FormalGroupLaw O ι) {p : ℕ}

/-- Convergence of the logarithm on `(pO)^n`: after scaling the variables by `p`, the
logarithm of the base change `f_*Φ` descends to a power series `H` with coefficients in
`O` that tend to `0`. Concretely `H` is the integral form of `Λ(pU)`: its base change is
the `p`-scaled logarithm (`f (coeff_d H) = f(p)^{deg d} · coeff_d Λ`) and its coefficients
lie in growing powers of `𝔪`, so `H` — hence `Λ` on `(pO)^n` via `evalT` — converges. -/
theorem exists_integral_scaled_log (hp : p.Prime) (hpmem : (p : O) ∈ maximalIdeal O)
    (f : O →+* K) (hfp : f (p : O) ≠ 0) (i : ι) :
    ∃ H : MvPowerSeries ι O,
      (∀ d, f (coeff d H) = f (p : O) ^ d.degree * coeff d ((Φ.map f).log i)) ∧
      Tendsto (fun d ↦ coeff d H) cofinite (𝓝 0) := by
  have hb (d : ι →₀ ℕ) : ∃ b : O,
      f b = f (p : O) ^ d.degree * coeff d ((Φ.map f).log i)
        ∧ b ∈ maximalIdeal O ^ (d.degree - padicValNat p d.degree) := by
    obtain ⟨c, hc⟩ := Φ.coeff_log_map_scale hp hpmem f hfp i d
    exact ⟨(p : O) ^ (d.degree - padicValNat p d.degree) * c, hc.symm,
      Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hpmem _)⟩
  choose b hb1 hb2 using hb
  refine ⟨b, fun d ↦ hb1 d, ?_⟩
  exact MvPSeries.tendsto_coeff_zero_of_mem_pow (h := b)
    (e := fun d ↦ d.degree - padicValNat p d.degree) (fun d ↦ hb2 d)
    ((tendsto_sub_padicValNat_atTop hp.one_lt).comp Finsupp.tendsto_degree_cofinite)

end logConvergence

end FormalGroupLaw

end ChabautyColeman

end
