/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
-- Vendored from the Chabauty project (`Chabauty/ForMathlib/MvPowerSeriesComp.lean`).

module

public import EllipticCurves.Mathlib.Chabauty.MvPowerSeriesPDeriv
public import Mathlib.Data.Finsupp.Weight

public import Mathlib.Data.Finsupp.Order
public import Mathlib.RingTheory.MvPowerSeries.Order
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Compositional inverses of multivariate formal substitutions

A family `a : σ → MvPowerSeries σ R` is a formal self-map `X ↦ (a_i(X))`; composition of
two such maps is `(a ∘ b)_i = subst b (a_i)`, with the identity `X`. Associativity is
`MvPowerSeries.subst_comp_subst_apply` and the identity laws are `subst_X` and `subst_self`,
so these maps form a monoid (subject to the `HasSubst` side conditions). This file records the
resulting uniqueness of compositional inverses; the construction of the inverse for a map
with identity linear part is developed separately.
-/


namespace MvPowerSeries

open Finset

variable {σ R : Type*} [CommRing R] {k : ℕ} {a E F : σ → MvPowerSeries σ R}

/-- A left compositional inverse equals a right compositional inverse. If `F` is a left
inverse of `a` (`F ∘ a = X`, i.e. `subst a (F i) = X i`) and `E` is a right inverse
(`a ∘ E = X`, i.e. `subst E (a i) = X i`), then `E = F`. In particular the compositional
inverse of a formal substitution, when it exists, is unique. -/
theorem leftInv_eq_rightInv (hE : HasSubst E) (hF : HasSubst a)
    (hFa : ∀ i, subst a (F i) = X i) (haE : ∀ i, subst E (a i) = X i) :
    E = F := by
  funext i
  calc E i = subst E (X i) := (subst_X hE i).symm
    _ = subst E (subst a (F i)) := by rw [hFa]
    _ = subst (fun t ↦ subst E (a t)) (F i) := subst_comp_subst_apply hF hE (F i)
    _ = subst (X : σ → MvPowerSeries σ R) (F i) := by simp only [haE]
    _ = F i := by rw [subst_self, id]

/-- Two power series *agree below degree `k`* if their coefficients coincide in all
degrees `< k`. -/
def AgreeBelow (k : ℕ) (f g : MvPowerSeries σ R) : Prop :=
  ∀ e : σ →₀ ℕ, e.degree < k → coeff e f = coeff e g

theorem AgreeBelow.mul {f f' g g' : MvPowerSeries σ R}
    (hf : AgreeBelow k f f') (hg : AgreeBelow k g g') :
    AgreeBelow k (f * g) (f' * g') := by
  classical
  intro d hd
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have hpe : p.1 + p.2 = d := by simpa using hp
  have h1 : p.1.degree ≤ d.degree := hpe ▸ Finsupp.degree_mono le_self_add
  have h2 : p.2.degree ≤ d.degree := hpe ▸ Finsupp.degree_mono le_add_self
  rw [hf p.1 (h1.trans_lt hd), hg p.2 (h2.trans_lt hd)]

theorem AgreeBelow.pow {f g : MvPowerSeries σ R} (h : AgreeBelow k f g)
    (n : ℕ) : AgreeBelow k (f ^ n) (g ^ n) := by
  induction n with
  | zero => simp [AgreeBelow]
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

/-- Factor one variable out of a product of powers `∏ (c s)^{m s}`. -/
theorem prod_pow_single_add (c : σ → MvPowerSeries σ R) (s : σ) (n : ℕ) (m' : σ →₀ ℕ) :
    (Finsupp.single s n + m').prod (fun s e ↦ c s ^ e)
      = c s ^ n * m'.prod fun s e ↦ c s ^ e := by
  rw [Finsupp.prod_add_index' (fun a ↦ pow_zero (c a)) (fun a b₁ b₂ ↦ pow_add (c a) b₁ b₂)]
  congr 1
  exact Finsupp.prod_single_index (pow_zero (c s))

theorem AgreeBelow.prod {b b' : σ → MvPowerSeries σ R}
    (hbb : ∀ s, AgreeBelow k (b s) (b' s)) (m : σ →₀ ℕ) :
    AgreeBelow k (m.prod fun s e ↦ b s ^ e) (m.prod fun s e ↦ b' s ^ e) := by
  induction m using Finsupp.induction with
  | zero => intro d _; simp
  | single_add s n m' hs hn ih =>
    rw [prod_pow_single_add, prod_pow_single_add]
    exact ((hbb s).pow n).mul ih

theorem constantCoeff_prod_pow_eq_zero {b : σ → MvPowerSeries σ R}
    (hb0 : ∀ s, constantCoeff (b s) = 0) {m : σ →₀ ℕ} (hm : m ≠ 0) :
    constantCoeff (m.prod fun s e ↦ b s ^ e) = 0 := by
  obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hm
  rw [Finsupp.prod, map_prod]
  refine Finset.prod_eq_zero hs ?_
  rw [map_pow, hb0, zero_pow (Finsupp.mem_support_iff.mp hs)]

theorem coeff_prod_pow_agree_boost {b b' : σ → MvPowerSeries σ R}
    (hb0 : ∀ s, constantCoeff (b s) = 0) (hb'0 : ∀ s, constantCoeff (b' s) = 0)
    (hbb : ∀ s, AgreeBelow k (b s) (b' s)) {m : σ →₀ ℕ} (hm2 : 2 ≤ m.degree)
    {d : σ →₀ ℕ} (hd : d.degree ≤ k) :
    coeff d (m.prod fun s e ↦ b s ^ e) = coeff d (m.prod fun s e ↦ b' s ^ e) := by
  classical
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm2
  obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hm0
  have hms : Finsupp.single s 1 ≤ m := Finsupp.single_le_iff.mpr
    (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hs))
  set m'' := m - Finsupp.single s 1 with hm''def
  have hm'' : m = Finsupp.single s 1 + m'' := by rw [hm''def, add_tsub_cancel_of_le hms]
  have hdeg'' : m''.degree = m.degree - 1 := by
    have := congrArg Finsupp.degree hm''
    rw [map_add, Finsupp.degree_single] at this; lia
  have hm''0 : m'' ≠ 0 := by rw [Ne, ← Finsupp.degree_eq_zero_iff]; lia
  have hsplit (c : σ → MvPowerSeries σ R) :
      m.prod (fun s e ↦ c s ^ e) = c s * m''.prod fun s e ↦ c s ^ e := by
    rw [hm'', prod_pow_single_add, pow_one]
  rw [hsplit b, hsplit b', coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have hpe : p.1 + p.2 = d := by simpa using hp
  have hpdeg : p.1.degree + p.2.degree = d.degree := by
    rw [← map_add, hpe]
  rcases Nat.eq_zero_or_pos p.1.degree with hp1z | hp1p
  · have : p.1 = 0 := (Finsupp.degree_eq_zero_iff p.1).mp hp1z
    simp [this, coeff_zero_eq_constantCoeff_apply, hb0 s, hb'0 s]
  · have hp2 : p.2.degree < k := by lia
    have hprod2 := AgreeBelow.prod hbb m'' p.2 hp2
    rcases lt_or_ge p.1.degree k with hp1k | hp1k
    · rw [hbb s p.1 hp1k, hprod2]
    · have hp20 : p.2 = 0 := (Finsupp.degree_eq_zero_iff p.2).mp (by lia)
      simp only [hp20, coeff_zero_eq_constantCoeff_apply,
        constantCoeff_prod_pow_eq_zero hb0 hm''0,
        constantCoeff_prod_pow_eq_zero hb'0 hm''0, mul_zero]

/-- The **boost lemma**: substituting a series `g` of order `≥ 2` into two families that
agree below degree `k` (and have zero constant coefficients) yields results agreeing below
degree `k + 1`. This one-degree gain is what makes the fixed-point iteration for the
compositional inverse converge. -/
theorem coeff_subst_agree_boost {b b' : σ → MvPowerSeries σ R}
    (hb : HasSubst b) (hb' : HasSubst b')
    (hb0 : ∀ s, constantCoeff (b s) = 0) (hb'0 : ∀ s, constantCoeff (b' s) = 0)
    (hbb : ∀ s, AgreeBelow k (b s) (b' s)) {g : MvPowerSeries σ R}
    (hg : ∀ e : σ →₀ ℕ, e.degree ≤ 1 → coeff e g = 0) {d : σ →₀ ℕ} (hd : d.degree ≤ k) :
    coeff d (subst b g) = coeff d (subst b' g) := by
  rw [coeff_subst hb, coeff_subst hb']
  refine finsum_congr fun m ↦ ?_
  rcases eq_or_ne (coeff m g) 0 with h0 | h0
  · rw [h0]; simp
  · have hm2 : 2 ≤ m.degree := by by_contra h; exact h0 (hg m (by lia))
    rw [coeff_prod_pow_agree_boost hb0 hb'0 hbb hm2 hd]

section CompositionalInverse

/-- The fixed-point iteration for the compositional inverse of `a`: `iterInv 0 = X` and
`iterInv (k+1) i = X i - (a i - X i)(iterInv k)`. -/
noncomputable def iterInv (a : σ → MvPowerSeries σ R) : ℕ → σ → MvPowerSeries σ R
  | 0 => X
  | k + 1 => fun i ↦ X i - subst (iterInv a k) (a i - X i)

@[simp]
theorem iterInv_zero : iterInv a 0 = X := rfl

theorem iterInv_succ (n : ℕ) (i : σ) :
    iterInv a (n + 1) i = X i - subst (iterInv a n) (a i - X i) := rfl

/-- The compositional inverse of `a`, assembled from the stabilized coefficients of the
iteration. -/
noncomputable def invSubst (a : σ → MvPowerSeries σ R) (i : σ) : MvPowerSeries σ R :=
  fun d ↦ coeff d (iterInv a (d.degree + 1) i)

theorem coeff_invSubst (a : σ → MvPowerSeries σ R) (i : σ) (d : σ →₀ ℕ) :
    coeff d (invSubst a i) = coeff d (iterInv a (d.degree + 1) i) :=
  coeff_apply (invSubst a i) d

attribute [irreducible] invSubst

theorem coeff_subst_low {b : σ → MvPowerSeries σ R} (hb : HasSubst b)
    (hb0 : ∀ s, constantCoeff (b s) = 0) {g : MvPowerSeries σ R}
    (hg : ∀ e' : σ →₀ ℕ, e'.degree ≤ 1 → coeff e' g = 0) {e : σ →₀ ℕ} (he : e.degree ≤ 1) :
    coeff e (subst b g) = 0 := by
  rw [coeff_subst hb, finsum_eq_zero_of_forall_eq_zero]
  intro m
  rcases eq_or_ne (coeff m g) 0 with h0 | h0
  · rw [h0, zero_smul]
  · have hm2 : 2 ≤ m.degree := by by_contra h; exact h0 (hg m (by lia))
    have horder : (m.degree : ℕ∞) ≤ (m.prod fun s e ↦ b s ^ e).order := by
      rw [Finsupp.prod]
      calc (m.degree : ℕ∞) = ∑ s ∈ m.support, (m s : ℕ∞) := by
            rw [Finsupp.degree_apply, Nat.cast_sum]
        _ ≤ ∑ s ∈ m.support, (b s ^ m s).order :=
            Finset.sum_le_sum fun s _ ↦ le_order_pow_of_constantCoeff_eq_zero _ (hb0 s)
        _ ≤ (∏ s ∈ m.support, b s ^ m s).order := le_order_prod _ _
    have hlt : (e.degree : ℕ∞) < (m.prod fun s e ↦ b s ^ e).order :=
      calc (e.degree : ℕ∞) ≤ 1 := by exact_mod_cast he
        _ < (m.degree : ℕ∞) := by exact_mod_cast (show 1 < m.degree by lia)
        _ ≤ _ := horder
    rw [coeff_of_lt_order hlt, smul_zero]

variable [Finite σ] {a : σ → MvPowerSeries σ R}
  (ha : ∀ i, ∀ e : σ →₀ ℕ, e.degree ≤ 1 → coeff e (a i - X i) = 0)

include ha

theorem constantCoeff_iterInv (k : ℕ) (i : σ) : constantCoeff (iterInv a k i) = 0 := by
  induction k generalizing i with
  | zero => simp [iterInv_zero]
  | succ k ih =>
    have hsub : HasSubst (iterInv a k) := hasSubst_of_constantCoeff_zero ih
    have hf : constantCoeff (a i - X i) = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply]; exact ha i 0 (by simp)
    rw [iterInv_succ, map_sub, constantCoeff_X, constantCoeff_subst_eq_zero hsub ih hf, sub_zero]

theorem hasSubst_iterInv (k : ℕ) : HasSubst (iterInv a k) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_iterInv ha k)

/-- Consecutive iterates agree below one more degree each step: this is the boost lemma
applied to the perturbation `a i - X i` (of order `≥ 2`). -/
theorem agreeBelow_iterInv_succ (k : ℕ) (i : σ) :
    AgreeBelow (k + 1) (iterInv a (k + 1) i) (iterInv a k i) := by
  induction k generalizing i with
  | zero =>
    intro e he
    have he0 : e = 0 := (Finsupp.degree_eq_zero_iff e).mp (by lia)
    subst he0
    rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_iterInv ha, constantCoeff_iterInv ha]
  | succ k ih =>
    intro e he
    rw [iterInv_succ (k + 1) i, iterInv_succ k i, map_sub, map_sub, sub_right_inj]
    exact coeff_subst_agree_boost (hasSubst_iterInv ha _) (hasSubst_iterInv ha _)
      (constantCoeff_iterInv ha _) (constantCoeff_iterInv ha _) ih (ha i) (by lia)

/-- Coefficient stabilization: from degree `d.degree + 1` onward the degree-`d`
coefficient of the iterates is constant. -/
theorem coeff_iterInv_stable (i : σ) (d : σ →₀ ℕ) {j : ℕ} (hj : d.degree + 1 ≤ j) :
    coeff d (iterInv a j i) = coeff d (iterInv a (d.degree + 1) i) := by
  induction j with
  | zero => lia
  | succ j ih =>
    rcases eq_or_lt_of_le hj with h | h
    · rw [← h]
    · rw [agreeBelow_iterInv_succ ha j i d (by lia), ih (by lia)]

theorem constantCoeff_invSubst (i : σ) : constantCoeff (invSubst a i) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_invSubst, coeff_zero_eq_constantCoeff_apply,
    constantCoeff_iterInv ha]

theorem hasSubst_invSubst : HasSubst (invSubst (R := R) a) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_invSubst ha)

theorem coeff_iterInv_eq_invSubst (i : σ) (d : σ →₀ ℕ) {j : ℕ} (hj : d.degree + 1 ≤ j) :
    coeff d (iterInv a j i) = coeff d (invSubst a i) := by
  rw [coeff_invSubst, coeff_iterInv_stable ha i d hj]

theorem agreeBelow_invSubst_iterInv (k : ℕ) (i : σ) :
    AgreeBelow k (invSubst a i) (iterInv a k i) := by
  intro e he
  rw [coeff_invSubst]
  exact (coeff_iterInv_stable ha i e (by lia)).symm

theorem subst_iterInv_eq (k : ℕ) (i : σ) :
    subst (iterInv a k) (a i) = iterInv a k i + X i - iterInv a (k + 1) i := by
  have h1 : iterInv a (k + 1) i = X i - subst (iterInv a k) (a i - X i) := iterInv_succ k i
  rw [← coe_substAlgHom (hasSubst_iterInv ha k), map_sub,
    coe_substAlgHom (hasSubst_iterInv ha k), subst_X (hasSubst_iterInv ha k)] at h1
  linear_combination h1

/-- **Existence** of the compositional inverse: `invSubst a` is a right inverse of `a`
(`a ∘ invSubst a = X`), for any `a` with zero constant term and identity linear part. -/
theorem subst_invSubst (i : σ) : subst (invSubst a) (a i) = X i := by
  ext d
  set k := d.degree + 1 with hk
  have hstep : coeff d (subst (invSubst a) (a i)) = coeff d (subst (iterInv a k) (a i)) := by
    have haX : a i = X i + (a i - X i) := by ring
    rw [haX, subst_add (hasSubst_invSubst ha), subst_add (hasSubst_iterInv ha k),
      subst_X (hasSubst_invSubst ha), subst_X (hasSubst_iterInv ha k), map_add, map_add]
    congr 1
    · exact agreeBelow_invSubst_iterInv ha k i d (by lia)
    · exact coeff_subst_agree_boost (hasSubst_invSubst ha) (hasSubst_iterInv ha k)
        (constantCoeff_invSubst ha) (constantCoeff_iterInv ha _)
        (fun s ↦ agreeBelow_invSubst_iterInv ha k s) (ha i) (by lia)
  rw [hstep, subst_iterInv_eq ha k i, map_sub, map_add,
    coeff_iterInv_eq_invSubst ha i d (by lia),
    coeff_iterInv_eq_invSubst ha i d (by lia)]
  abel

/-- Each iterate agrees with the identity `X` below degree `2`: the corrections have
order `≥ 2`. So `invSubst a` again has zero constant term and identity linear part. -/
theorem agreeBelow_iterInv_X (k : ℕ) (i : σ) : AgreeBelow 2 (iterInv a k i) (X i) := by
  induction k generalizing i with
  | zero => intro e _; rfl
  | succ k ih =>
    intro e he
    rw [iterInv_succ k i, map_sub,
      coeff_subst_low (hasSubst_iterInv ha k) (constantCoeff_iterInv ha k) (ha i) (by lia),
      sub_zero]

theorem coeff_invSubst_sub_X (i : σ) (e : σ →₀ ℕ) (he : e.degree ≤ 1) :
    coeff e (invSubst a i - X i) = 0 := by
  rw [map_sub, coeff_invSubst, agreeBelow_iterInv_X ha (e.degree + 1) i e (by lia), sub_self]

/-- **Two-sided**: `invSubst a` is also a left inverse of `a` (`invSubst a ∘ a = X`). -/
theorem subst_a_invSubst (i : σ) : subst a (invSubst a i) = X i := by
  have h1 : invSubst (invSubst a) = a :=
    leftInv_eq_rightInv (hasSubst_invSubst (coeff_invSubst_sub_X ha)) (hasSubst_invSubst ha)
      (subst_invSubst ha) (subst_invSubst (coeff_invSubst_sub_X ha))
  have h2 := subst_invSubst (coeff_invSubst_sub_X ha) i
  rwa [h1] at h2

end CompositionalInverse

end MvPowerSeries

end
