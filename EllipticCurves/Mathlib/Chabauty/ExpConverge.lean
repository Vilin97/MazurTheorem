/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
-- Vendored from the Chabauty project (`Chabauty/Series/ExpConverge.lean`).

module

public import EllipticCurves.Mathlib.Chabauty.FormalGroupLaw

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

@[expose] public section

/-!
# Convergence of the formal exponential

The formal exponential `Exp` of a formal group law (the compositional inverse of the
logarithm `Λ`, `ChabautyColeman.FormalGroupLaw.exp`) converges on `(pO)ⁿ` when `p` is odd.

The classical estimate is `v_p(coeff_d Exp) ≥ -(deg d - 1)/(p-1)`
(`ChabautyColeman.FormalGroupLaw.exp_bounded`), proved by strong induction on `deg d`
through the recursion `Exp = X - (Λ - X) ∘ Exp`. The bookkeeping is organised around:

* `Dexp p n = (n-1)/(p-1)`, the denominator-exponent bound, with the elementary inequality
  `(p-1) · v_p(M) ≤ M - 1` and the partition inequality `Dexp M + ∑ Dexp kᵢ ≤ Dexp (∑ kᵢ)`;
* `ChabautyColeman.IntLevel f p x k`, meaning `f(p)^k · x` is integral (in the image of `f`),
  which is additive, multiplicative (adding the levels) and monotone in `k`.

In the induction step the product `∏ᵢ Expᵢ^{mᵢ}` gains a slack `Dexp (deg m)` (partition
inequality) that exactly cancels the logarithm's `1/deg m` denominator; `(p-1) v_p(m) ≤ m-1`
closes the estimate. Scaling by `p^{deg d}` and using `deg d - Dexp(deg d) → ∞` (which needs
`p ≥ 3`) gives the integral, coefficient-decaying descent
`ChabautyColeman.FormalGroupLaw.exp_converges`.

Blueprint node: `lem:exp-converge`.
-/


open MvPowerSeries Finset Filter

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R] [Finite σ] {a : σ → MvPowerSeries σ R}

/-- The compositional inverse satisfies the defining recursion `E = X - (a - X) ∘ E`. -/
theorem invSubst_eq_sub
    (ha : ∀ (i : σ) (e : σ →₀ ℕ), e.degree ≤ 1 → coeff e (a i - X i) = 0) (i : σ) :
    invSubst a i = X i - subst (invSubst a) (a i - X i) := by
  have h := subst_invSubst ha i
  have hb : HasSubst (invSubst a) := hasSubst_invSubst ha
  rw [show a i = X i + (a i - X i) by ring, subst_add hb, subst_X hb] at h
  linear_combination h

end MvPowerSeries

namespace ChabautyColeman

/-! ## The denominator-exponent bound `Dexp` -/

/-- `Dexp p n = (n-1)/(p-1)` (natural-number division, i.e. `⌊(n-1)/(p-1)⌋`): an integer
upper bound for `v_p(n!)` that bounds the `p`-power denominators of the formal exponential. -/
def Dexp (p n : ℕ) : ℕ := (n - 1) / (p - 1)

theorem Dexp_eq (p n : ℕ) : Dexp p n = (n - 1) / (p - 1) := rfl

section
variable {p : ℕ}

private theorem one_add_pred_mul_le_pow (hp : 2 ≤ p) (v : ℕ) : (p - 1) * v + 1 ≤ p ^ v := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by lia⟩
  induction v with
  | zero => simp
  | succ v ih =>
    have h1 : (q + 1) * ((q + 1 - 1) * v + 1) ≤ (q + 1) * (q + 1) ^ v := Nat.mul_le_mul_left _ ih
    calc (q + 1 - 1) * (v + 1) + 1 ≤ (q + 1) * ((q + 1 - 1) * v + 1) := by
            simp only [Nat.add_sub_cancel]
            have hexp : (q + 1) * (q * v + 1) = (q * (v + 1) + 1) + q * q * v := by ring
            lia
      _ ≤ (q + 1) * (q + 1) ^ v := h1
      _ = (q + 1) ^ (v + 1) := (pow_succ' (q + 1) v).symm

/-- The key elementary inequality behind the exponential estimate: `(p-1) · v_p(M) ≤ M - 1`. -/
theorem pred_mul_padicValNat_le (hp : p.Prime) {M : ℕ} (hM : 1 ≤ M) :
    (p - 1) * padicValNat p M ≤ M - 1 := by
  have hle : p ^ padicValNat p M ≤ M := Nat.le_of_dvd (by lia) pow_padicValNat_dvd
  have hb := one_add_pred_mul_le_pow hp.two_le (padicValNat p M)
  lia

theorem pred_mul_Dexp_le (n : ℕ) : (p - 1) * Dexp p n ≤ n - 1 := by
  rw [Dexp_eq, mul_comm]; exact Nat.div_mul_le_self (n - 1) (p - 1)

theorem Dexp_mono {n m : ℕ} (h : n ≤ m) : Dexp p n ≤ Dexp p m :=
  Nat.div_le_div_right (Nat.sub_le_sub_right h 1)

theorem Dexp_le {n : ℕ} : Dexp p n ≤ n := (Nat.div_le_self _ _).trans (Nat.sub_le _ _)

theorem padicValNat_le_Dexp (hp : p.Prime) {M : ℕ} (hM : 1 ≤ M) :
    padicValNat p M ≤ Dexp p M := by
  have hp2 := hp.two_le
  rw [Dexp_eq, Nat.le_div_iff_mul_le (by lia : 0 < p - 1), mul_comm]
  exact pred_mul_padicValNat_le hp hM

/-- The **partition inequality**: parts `k i ≥ 1` summing to `N` over `s.card` parts satisfy
`Dexp s.card + ∑ Dexp (k i) ≤ Dexp N`. This absorbs the logarithm's `1/deg` denominator into
the product slack. -/
theorem Dexp_card_add_sum_le (hp : 2 ≤ p) {ι : Type*} (s : Finset ι) (k : ι → ℕ)
    (hk : ∀ i ∈ s, 1 ≤ k i) :
    Dexp p s.card + ∑ i ∈ s, Dexp p (k i) ≤ Dexp p (∑ i ∈ s, k i) := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp [Dexp_eq]
  have hcard1 : 1 ≤ s.card := hne.card_pos
  set N := ∑ i ∈ s, k i with hN
  have key : (∑ i ∈ s, (k i - 1)) + s.card = N := by
    have h1 : ∑ i ∈ s, ((k i - 1) + 1) = ∑ i ∈ s, k i :=
      Finset.sum_congr rfl fun i hi ↦ Nat.sub_add_cancel (hk i hi)
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at h1
    lia
  have hcard : Dexp p s.card * (p - 1) ≤ s.card - 1 := by rw [mul_comm]; exact pred_mul_Dexp_le _
  have hsum : (∑ i ∈ s, Dexp p (k i)) * (p - 1) ≤ ∑ i ∈ s, (k i - 1) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ ↦ by rw [mul_comm]; exact pred_mul_Dexp_le _
  have final : (Dexp p s.card + ∑ i ∈ s, Dexp p (k i)) * (p - 1) ≤ N - 1 := by
    rw [add_mul]
    calc Dexp p s.card * (p - 1) + (∑ i ∈ s, Dexp p (k i)) * (p - 1)
        ≤ (s.card - 1) + ∑ i ∈ s, (k i - 1) := Nat.add_le_add hcard hsum
      _ = N - 1 := by lia
  rw [Dexp_eq p N]
  exact (Nat.le_div_iff_mul_le (by lia : 0 < p - 1)).mpr final

/-- For `p ≥ 3`, the gap `n - Dexp p n → ∞` (this is where `p` odd enters). -/
theorem tendsto_sub_Dexp_atTop (hp : 3 ≤ p) :
    Tendsto (fun n ↦ n - Dexp p n) atTop atTop := by
  apply tendsto_atTop_atTop_of_monotone
  · refine monotone_nat_of_le_succ fun n ↦ ?_
    have h2 : Dexp p n ≤ Dexp p (n + 1) := by
      rw [Dexp_eq, Dexp_eq]; exact Nat.div_le_div_right (by lia)
    have h3 : Dexp p (n + 1) ≤ Dexp p n + 1 := by
      rw [Dexp_eq, Dexp_eq]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · calc (n + 1 - 1) / (p - 1) = n / (p - 1) := by rw [Nat.add_sub_cancel]
          _ ≤ ((n - 1) + (p - 1)) / (p - 1) := Nat.div_le_div_right (by lia)
          _ = (n - 1) / (p - 1) + 1 := Nat.add_div_right _ (by lia)
    lia
  · intro B
    refine ⟨2 * B + 2, ?_⟩
    have hD : Dexp p (2 * B + 2) ≤ (2 * B + 2 - 1) / 2 := by
      rw [Dexp_eq]; exact Nat.div_le_div_left (by lia) (by norm_num)
    lia

end

/-! ## `p`-integrality levels -/

section
variable {O K : Type*} [CommRing O] [CommRing K] {f : O →+* K} {p : ℕ}

/-- `x : K` is *`p`-integral of level `k`* (via `f : O →+* K`) if `f(p)^k · x` lies in the
image of `f`. It is monotone in `k`, additive, and multiplicative (adding levels). -/
def IntLevel (f : O →+* K) (p : ℕ) (x : K) (k : ℕ) : Prop :=
  ∃ c : O, f (p : O) ^ k * x = f c

theorem IntLevel.zero (k : ℕ) : IntLevel f p 0 k := ⟨0, by simp⟩

theorem IntLevel.of_f (c : O) : IntLevel f p (f c) 0 := ⟨c, by simp⟩

theorem IntLevel.add {x y : K} {k : ℕ} (hx : IntLevel f p x k) (hy : IntLevel f p y k) :
    IntLevel f p (x + y) k := by
  obtain ⟨cx, hcx⟩ := hx; obtain ⟨cy, hcy⟩ := hy
  exact ⟨cx + cy, by rw [map_add, ← hcx, ← hcy, mul_add]⟩

theorem IntLevel.neg {x : K} {k : ℕ} (hx : IntLevel f p x k) : IntLevel f p (-x) k := by
  obtain ⟨cx, hcx⟩ := hx
  exact ⟨-cx, by rw [map_neg, ← hcx, mul_neg]⟩

theorem IntLevel.mul {x y : K} {j k : ℕ} (hx : IntLevel f p x j) (hy : IntLevel f p y k) :
    IntLevel f p (x * y) (j + k) := by
  obtain ⟨cx, hcx⟩ := hx; obtain ⟨cy, hcy⟩ := hy
  exact ⟨cx * cy, by rw [map_mul, ← hcx, ← hcy, pow_add]; ring⟩

theorem IntLevel.mono {x : K} {j k : ℕ} (hx : IntLevel f p x j) (hjk : j ≤ k) :
    IntLevel f p x k := by
  obtain ⟨cx, hcx⟩ := hx
  exact ⟨(p : O) ^ (k - j) * cx, by
    rw [map_mul, map_pow, ← hcx, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hjk]⟩

theorem IntLevel.sum {ι : Type*} {s : Finset ι} {g : ι → K} {k : ℕ}
    (h : ∀ i ∈ s, IntLevel f p (g i) k) : IntLevel f p (∑ i ∈ s, g i) k := by
  classical
  induction s using Finset.induction with
  | empty => simpa using IntLevel.zero k
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi ↦ h i (mem_insert_of_mem hi))

theorem IntLevel.prod {ι : Type*} {s : Finset ι} {g : ι → K} {k : ι → ℕ}
    (h : ∀ i ∈ s, IntLevel f p (g i) (k i)) :
    IntLevel f p (∏ i ∈ s, g i) (∑ i ∈ s, k i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using IntLevel.of_f (f := f) (p := p) 1
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (mem_insert_self a s)).mul (ih fun i hi ↦ h i (mem_insert_of_mem hi))

theorem IntLevel.finsum {ι : Type*} {g : ι → K} {k : ℕ} (hfin : Function.HasFiniteSupport g)
    (h : ∀ i, IntLevel f p (g i) k) : IntLevel f p (∑ᶠ i, g i) k := by
  rw [finsum_eq_sum _ hfin]
  exact IntLevel.sum fun i _ ↦ h i

end

open IsLocalRing

namespace FormalGroupLaw

variable {O K : Type*} [CommRing O] [Field K] {ι : Type*} {f : O →+* K} {p : ℕ}

-- A product `∏ (b s)^{m s}` of series with zero constant coefficient vanishes in degree
-- `d` whenever `deg d < deg m` (its order is at least `deg m`).
private lemma coeff_prod_pow_eq_zero_of_lt {b : ι → MvPowerSeries ι K}
    (hb0 : ∀ s, constantCoeff (b s) = 0) {m d : ι →₀ ℕ} (hmd : d.degree < m.degree) :
    coeff d (m.prod fun s a ↦ b s ^ a) = 0 := by
  apply coeff_of_lt_order
  have horder : (m.degree : ℕ∞) ≤ (m.prod fun s a ↦ b s ^ a).order := by
    rw [Finsupp.prod]
    calc (m.degree : ℕ∞) = ∑ s ∈ m.support, (m s : ℕ∞) := by
          rw [Finsupp.degree_apply, Nat.cast_sum]
      _ ≤ ∑ s ∈ m.support, (b s ^ m s).order :=
          Finset.sum_le_sum fun s _ ↦ le_order_pow_of_constantCoeff_eq_zero _ (hb0 s)
      _ ≤ (∏ s ∈ m.support, b s ^ m s).order := le_order_prod _ _
  exact (show (d.degree : ℕ∞) < (m.degree : ℕ∞) by exact_mod_cast hmd).trans_le horder

section
variable [IsLocalRing O] [Fintype ι] [DecidableEq ι]

/-- The coefficients of the logarithm are `Dexp`-bounded: `f(p)^{Dexp(deg m)} · coeff_m Λ`
is integral. This relaxes `coeff_log_map_padic` (denominator `p^{v_p(deg m)}`) via
`v_p(deg m) ≤ Dexp(deg m)`. -/
theorem log_coeff_level (hp : p.Prime) (hpmem : (p : O) ∈ maximalIdeal O)
    (hfp : f (p : O) ≠ 0) (Φ : FormalGroupLaw O ι) (i : ι) (m : ι →₀ ℕ) (hm : 1 ≤ m.degree) :
    IntLevel f p (coeff m ((Φ.map f).log i)) (Dexp p m.degree) :=
  (show IntLevel f p (coeff m ((Φ.map f).log i)) (padicValNat p m.degree) from
    Φ.coeff_log_map_padic hp hpmem f hfp i m).mono (padicValNat_le_Dexp hp hm)

end

/-- The degree-`d` coefficient of a product `∏ᵢ (b i)^{mᵢ}` of `Dexp`-bounded series (below
degree `N`, with zero constant term) is bounded at level `Dexp N - Dexp (deg m)`. The slack
`Dexp (deg m)` is what absorbs the logarithm's `1/deg m` denominator. -/
private theorem prod_bound (hp2 : 2 ≤ p) {b : ι → MvPowerSeries ι K}
    (hb0 : ∀ s, constantCoeff (b s) = 0) {N : ℕ}
    (hbN : ∀ (s : ι) (e : ι →₀ ℕ), e.degree < N → IntLevel f p (coeff e (b s)) (Dexp p e.degree))
    (m : ι →₀ ℕ) (hm2 : 2 ≤ m.degree) {d : ι →₀ ℕ} (hd : d.degree = N) :
    IntLevel f p (coeff d (m.prod fun s e ↦ b s ^ e)) (Dexp p N - Dexp p m.degree) := by
  classical
  set T : Finset (Σ _ : ι, ℕ) := m.support.sigma (fun a ↦ Finset.range (m a)) with hT
  have hTcard : T.card = m.degree := by
    rw [hT, Finset.card_sigma, Finsupp.degree_apply]
    exact Finset.sum_congr rfl fun a _ ↦ Finset.card_range (m a)
  have hprodeq : (m.prod fun s e ↦ b s ^ e) = ∏ x ∈ T, b x.1 := by
    rw [hT, Finset.prod_sigma, Finsupp.prod]
    exact Finset.prod_congr rfl fun a _ ↦ by simp
  rw [hprodeq, coeff_prod]
  refine IntLevel.sum fun l hl ↦ ?_
  rw [mem_finsuppAntidiag] at hl
  obtain ⟨hlsum, -⟩ := hl
  by_cases hzero : ∃ x ∈ T, l x = 0
  · obtain ⟨x0, hx0T, hx0⟩ := hzero
    have hp0 : ∏ x ∈ T, coeff (l x) (b x.1) = 0 :=
      Finset.prod_eq_zero hx0T (by rw [hx0, coeff_zero_eq_constantCoeff_apply, hb0])
    rw [hp0]; exact IntLevel.zero _
  · replace hzero : ∀ x ∈ T, l x ≠ 0 := fun x hx hlx ↦ hzero ⟨x, hx, hlx⟩
    have hdeg1 : ∀ x ∈ T, 1 ≤ (l x).degree := fun x hx ↦
      Nat.one_le_iff_ne_zero.mpr fun h ↦ hzero x hx ((Finsupp.degree_eq_zero_iff _).mp h)
    have hsumdeg : ∑ x ∈ T, (l x).degree = N := by rw [← map_sum Finsupp.degree l T, hlsum, hd]
    have hcard2 : 2 ≤ T.card := hTcard ▸ hm2
    have hltN : ∀ x ∈ T, (l x).degree < N := by
      intro x0 hx0T
      obtain ⟨x1, hx1T, hx1ne⟩ := Finset.exists_mem_ne (by lia : 1 < T.card) x0
      have h2 : ∑ x ∈ ({x0, x1} : Finset _), (l x).degree ≤ ∑ x ∈ T, (l x).degree :=
        Finset.sum_le_sum_of_subset (by
          intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl <;> assumption)
      rw [Finset.sum_pair (Ne.symm hx1ne)] at h2
      have := hdeg1 x1 hx1T
      lia
    have hlevel : IntLevel f p (∏ x ∈ T, coeff (l x) (b x.1)) (∑ x ∈ T, Dexp p (l x).degree) :=
      IntLevel.prod fun x hx ↦ hbN x.1 (l x) (hltN x hx)
    refine hlevel.mono ?_
    have hpart := Dexp_card_add_sum_le hp2 T (fun x ↦ (l x).degree) hdeg1
    rw [hTcard, hsumdeg] at hpart
    lia

variable [IsLocalRing O] [Fintype ι] [DecidableEq ι]

/-- **The exponential coefficient bound**: `f(p)^{Dexp(deg d)} · coeff_d Exp` is integral,
i.e. `v_p(coeff_d Exp) ≥ -(deg d - 1)/(p-1)`. Proved by strong induction on `deg d` through
the recursion `Exp = X - (Λ - X) ∘ Exp`; the product slack `Dexp(deg m)` cancels the
logarithm's `1/deg m`, and `(p-1)·v_p(m) ≤ m - 1` closes the step. -/
theorem exp_bounded (hp : p.Prime) (hpmem : (p : O) ∈ maximalIdeal O) (hfp : f (p : O) ≠ 0)
    (Φ : FormalGroupLaw O ι) (i : ι) (d : ι →₀ ℕ) :
    IntLevel f p (coeff d ((Φ.map f).exp i)) (Dexp p d.degree) := by
  set G := Φ.map f with hG
  have ha : ∀ (j : ι) (e : ι →₀ ℕ), e.degree ≤ 1 → coeff e (G.log j - X j) = 0 :=
    fun j ↦ G.log_sub_X_order j
  have hexp0 : ∀ s, constantCoeff (G.exp s) = 0 := fun s ↦ constantCoeff_invSubst ha s
  have hsubst : HasSubst (G.exp) := hasSubst_invSubst ha
  have hrec : ∀ j, G.exp j = X j - subst G.exp (G.log j - X j) := fun j ↦ invSubst_eq_sub ha j
  suffices H : ∀ N, (∀ N' < N, ∀ (j : ι) (e : ι →₀ ℕ), e.degree = N' →
      IntLevel f p (coeff e (G.exp j)) (Dexp p e.degree)) →
      ∀ (j : ι) (e : ι →₀ ℕ), e.degree = N →
        IntLevel f p (coeff e (G.exp j)) (Dexp p e.degree) by
    have key : ∀ N, ∀ (j : ι) (e : ι →₀ ℕ), e.degree = N →
        IntLevel f p (coeff e (G.exp j)) (Dexp p e.degree) := fun N ↦ by
      induction N using Nat.strong_induction_on with
      | _ N ih => exact H N ih
    exact key d.degree i d rfl
  intro N ih j d hd
  rcases lt_or_ge d.degree 2 with hlt2 | hge2
  · have hEX : coeff d (G.exp j) = coeff d (X j : MvPowerSeries ι K) := by
      have h0 := coeff_invSubst_sub_X ha j d (by lia)
      rwa [map_sub, sub_eq_zero] at h0
    rw [hEX, coeff_X]
    refine (show IntLevel f p (if d = Finsupp.single j 1 then (1 : K) else 0) 0 from ?_).mono
      (Nat.zero_le _)
    split_ifs
    · exact ⟨1, by simp⟩
    · exact IntLevel.zero 0
  · have hXd : coeff d (X j : MvPowerSeries ι K) = 0 := by
      rw [coeff_X, if_neg]
      intro h; have hd1 : d.degree = 1 := by rw [h, Finsupp.degree_single]
      lia
    have hcoeff : coeff d (G.exp j) = -coeff d (subst G.exp (G.log j - X j)) := by
      rw [hrec j, map_sub, hXd, zero_sub]
    rw [hcoeff]
    refine IntLevel.neg ?_
    rw [coeff_subst hsubst]
    refine IntLevel.finsum (coeff_subst_finite hsubst (G.log j - X j) d) fun m ↦ ?_
    rw [smul_eq_mul]
    rcases eq_or_ne (coeff m (G.log j - X j)) 0 with h0 | h0
    · rw [h0, zero_mul]; exact IntLevel.zero _
    · have hm2 : 2 ≤ m.degree := by by_contra hc; exact h0 (ha j m (by lia))
      have hgm : coeff m (G.log j - X j) = coeff m (G.log j) := by
        rw [map_sub, coeff_X, if_neg, sub_zero]
        intro h; rw [h, Finsupp.degree_single] at hm2; lia
      rw [hgm]
      rcases lt_or_ge d.degree m.degree with hmd | hmd
      · have hP0 : coeff d (m.prod fun s a ↦ G.exp s ^ a) = 0 :=
          coeff_prod_pow_eq_zero_of_lt hexp0 hmd
        rw [hP0, mul_zero]; exact IntLevel.zero _
      · have hlog : IntLevel f p (coeff m (G.log j)) (Dexp p m.degree) :=
          log_coeff_level hp hpmem hfp Φ j m (by lia)
        have hprod : IntLevel f p (coeff d (m.prod fun s a ↦ G.exp s ^ a))
            (Dexp p d.degree - Dexp p m.degree) :=
          prod_bound hp.two_le hexp0 (fun s e he' ↦ ih e.degree (hd ▸ he') s e rfl) m hm2 rfl
        have hle : Dexp p m.degree ≤ Dexp p d.degree := Dexp_mono hmd
        have hmul := hlog.mul hprod
        rwa [show Dexp p m.degree + (Dexp p d.degree - Dexp p m.degree) = Dexp p d.degree
          by lia] at hmul

variable [UniformSpace O] [Fact (IsAdic (maximalIdeal O))]

open Topology in
/-- **Convergence of the exponential on `(pO)ⁿ`** (`p` odd). After scaling the variables by
`p`, the exponential of the base change `f_*Φ` descends to `H ∈ O⟦U⟧` whose base change is the
`p`-scaled exponential (`f (coeff_d H) = f(p)^{deg d} · coeff_d Exp`) and whose coefficients
tend to `0`. Here `p ≥ 3` is essential: `deg d - Dexp(deg d) → ∞` needs `p - 1 ≥ 2`. -/
theorem exp_converges (hp : p.Prime) (hp2 : p ≠ 2) (hpmem : (p : O) ∈ maximalIdeal O)
    (hfp : f (p : O) ≠ 0) (Φ : FormalGroupLaw O ι) (i : ι) :
    ∃ H : MvPowerSeries ι O,
      (∀ d, f (coeff d H) = f (p : O) ^ d.degree * coeff d ((Φ.map f).exp i)) ∧
      Tendsto (fun d ↦ coeff d H) cofinite (𝓝 0) := by
  have hp3 : 3 ≤ p := by have := hp.two_le; lia
  have hb (d : ι →₀ ℕ) : ∃ b : O,
      f b = f (p : O) ^ d.degree * coeff d ((Φ.map f).exp i)
        ∧ b ∈ maximalIdeal O ^ (d.degree - Dexp p d.degree) := by
    obtain ⟨c, hc⟩ := exp_bounded hp hpmem hfp Φ i d
    refine ⟨(p : O) ^ (d.degree - Dexp p d.degree) * c, ?_,
      Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hpmem _)⟩
    rw [map_mul, map_pow, ← hc, ← mul_assoc, ← pow_add, Nat.sub_add_cancel Dexp_le]
  choose b hb1 hb2 using hb
  exact ⟨b, fun d ↦ hb1 d, MvPSeries.tendsto_coeff_zero_of_mem_pow (h := b)
    (e := fun d ↦ d.degree - Dexp p d.degree) (fun d ↦ hb2 d)
    ((tendsto_sub_Dexp_atTop hp3).comp Finsupp.tendsto_degree_cofinite)⟩

end FormalGroupLaw

end ChabautyColeman

end
