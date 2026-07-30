/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
Source: MichaelStollBayreuth/EllipticCurves at commit 3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f.
Exact-pin changes are documented in PORTING.md.
-/
module

public import Mathlib
public import EllipticCurves.Mathlib.Chabauty.FormalGroupLaw
public import EllipticCurves.Mathlib.AdicFormalGroupLog

/-!
# The Weierstrass fixed-point series and the chord data

For a Weierstrass curve `W` over a commutative ring `O`, this file builds the fixed-point
series `w(t) ∈ O⟦t⟧` (solution of `w = t³ + a₁tw + a₂t²w + a₃w² + a₄tw² + a₆w³`) and the
two-variable chord data of the curve `(t, w(t))`: `slopeSeries`, `interceptSeries`,
`thirdRootSeries`, `addSeries`, and the inverse `inverseSeries`, with their basic identities,
the swap-invariance giving commutativity, the `t₂ = 0` specialization, and naturality under
coefficient-ring maps.
-/

@[expose] public section

open ChabautyColeman PowerSeries IsDedekindDomain

namespace WeierstrassCurve

section wSeries

variable {O : Type*} [CommRing O] (W : WeierstrassCurve O)

/-- The right-hand side of the Weierstrass equation in the coordinates `(t, w)`, with the
parameter series `q` in place of `t` and the unknown `v` in place of `w`. -/
noncomputable def wStepAt (q v : PowerSeries O) : PowerSeries O :=
  q ^ 3 + C W.a₁ * q * v + C W.a₂ * q ^ 2 * v + C W.a₃ * v ^ 2 + C W.a₄ * q * v ^ 2 +
    C W.a₆ * v ^ 3

/-- One step of the fixed-point iteration defining `wSeries`: the right-hand side of the
Weierstrass equation in the coordinates `(t, w)`. -/
noncomputable def wStep (w : PowerSeries O) : PowerSeries O :=
  W.wStepAt X w

private lemma wStepAt_contract {q u v : PowerSeries O} (hq : X ∣ q) (hu : X ∣ u) (hv : X ∣ v)
    {k : ℕ} (h : X ^ k ∣ u - v) : X ^ (k + 1) ∣ W.wStepAt q u - W.wStepAt q v := by
  have h2 : X ^ (k + 1) ∣ u ^ 2 - v ^ 2 := by
    have : u ^ 2 - v ^ 2 = (u + v) * (u - v) := by ring
    rw [this, pow_succ, mul_comm (X ^ k)]
    exact mul_dvd_mul (dvd_add hu hv) h
  have h3 : X ^ (k + 1) ∣ u ^ 3 - v ^ 3 := by
    have : u ^ 3 - v ^ 3 = (u ^ 2 + u * v + v ^ 2) * (u - v) := by ring
    rw [this, pow_succ, mul_comm (X ^ k)]
    refine mul_dvd_mul ?_ h
    exact dvd_add (dvd_add ((hu.mul_right u).trans (by rw [pow_two])) (hu.mul_right v))
      ((hv.mul_right v).trans (by rw [pow_two]))
  have hXk : X ^ (k + 1) ∣ q * (u - v) := by
    rw [pow_succ, mul_comm (X ^ k)]
    exact mul_dvd_mul hq h
  have hstep : W.wStepAt q u - W.wStepAt q v = C W.a₁ * (q * (u - v)) +
      C W.a₂ * q * (q * (u - v)) + C W.a₃ * (u ^ 2 - v ^ 2) + C W.a₄ * q * (u ^ 2 - v ^ 2) +
      C W.a₆ * (u ^ 3 - v ^ 3) := by
    simp only [wStepAt]
    ring
  rw [hstep]
  exact dvd_add (dvd_add (dvd_add (dvd_add (hXk.mul_left _) ((hXk.mul_left _)))
    (h2.mul_left _)) (h2.mul_left _)) (h3.mul_left _)

/-- Two solutions of the Weierstrass equation at the same parameter series that both have
vanishing constant term agree. -/
private lemma eq_of_wStepAt_fixed {q v v' : PowerSeries O} (hq : X ∣ q) (hv : X ∣ v)
    (hv' : X ∣ v') (h : v = W.wStepAt q v) (h' : v' = W.wStepAt q v') : v = v' := by
  have key (k : ℕ) : X ^ k ∣ v - v' := by
    induction k with
    | zero => simp
    | succ k ih =>
      have := W.wStepAt_contract hq hv hv' ih
      rwa [← h, ← h'] at this
  ext n
  have h0 := X_pow_dvd_iff.mp (key (n + 1)) n (by lia)
  rwa [map_sub, sub_eq_zero] at h0

private lemma X_dvd_wStep {w : PowerSeries O} (hw : X ∣ w) : X ∣ W.wStep w := by
  obtain ⟨u, rfl⟩ := hw
  refine ⟨X ^ 2 + C W.a₁ * X * u + C W.a₂ * X ^ 2 * u + C W.a₃ * (X * u ^ 2) +
    C W.a₄ * X * (X * u ^ 2) + C W.a₆ * (X ^ 2 * u ^ 3), ?_⟩
  simp only [wStep, wStepAt]
  ring

private lemma wStep_contract {u v : PowerSeries O} (hu : X ∣ u) (hv : X ∣ v) {k : ℕ}
    (h : X ^ k ∣ u - v) : X ^ (k + 1) ∣ W.wStep u - W.wStep v :=
  W.wStepAt_contract dvd_rfl hu hv h

private lemma X_dvd_iterate (m : ℕ) : X ∣ (W.wStep)^[m] (0 : PowerSeries O) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Function.iterate_succ_apply']; exact W.X_dvd_wStep ih

private lemma iterate_congr (m d : ℕ) :
    X ^ m ∣ (W.wStep)^[m + d] (0 : PowerSeries O) - (W.wStep)^[m] (0 : PowerSeries O) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show m + 1 + d = (m + d) + 1 by ring, Function.iterate_succ_apply',
      Function.iterate_succ_apply']
    exact W.wStep_contract (W.X_dvd_iterate _) (W.X_dvd_iterate _) ih

/-- The power series `w(t) ∈ O⟦t⟧` describing a Weierstrass curve near the origin in the
coordinates `t = -x/y`, `w = -1/y`: the unique solution with `w ≡ t³ mod t⁴` of the
fixed-point equation `wSeries_eq` (Silverman, IV.1.1), obtained as the `t`-adic limit of
the iteration of the right-hand side starting at `0`. -/
noncomputable def wSeries : PowerSeries O :=
  PowerSeries.mk fun n ↦ coeff n ((W.wStep)^[n + 1] 0)

private lemma coeff_wSeries (n : ℕ) :
    coeff n W.wSeries = coeff n ((W.wStep)^[n + 1] 0) :=
  coeff_mk _ _

private lemma X_pow_dvd_wSeries_sub_iterate (m : ℕ) :
    X ^ m ∣ W.wSeries - (W.wStep)^[m] (0 : PowerSeries O) := by
  rw [X_pow_dvd_iff]
  intro k hk
  rw [map_sub, W.coeff_wSeries, sub_eq_zero]
  have h1 := W.iterate_congr (k + 1) (m - (k + 1))
  rw [show k + 1 + (m - (k + 1)) = m by lia] at h1
  have h2 := X_pow_dvd_iff.mp h1 k (by lia)
  rw [map_sub, sub_eq_zero] at h2
  exact h2.symm

private lemma X_dvd_wSeries : (X : PowerSeries O) ∣ W.wSeries := by
  have h := W.X_pow_dvd_wSeries_sub_iterate 1
  rw [pow_one] at h
  have h2 := dvd_add h (W.X_dvd_iterate 1)
  rwa [sub_add_cancel] at h2

private theorem wSeries_eq_wStep : W.wSeries = W.wStep W.wSeries := by
  have hX : (X : PowerSeries O) ∣ W.wSeries := W.X_dvd_wSeries
  have key (m : ℕ) : X ^ (m + 1) ∣ W.wSeries - W.wStep W.wSeries := by
    have h1 := W.X_pow_dvd_wSeries_sub_iterate (m + 1)
    have h2 : X ^ (m + 1) ∣ (W.wStep)^[m + 1] (0 : PowerSeries O) - W.wStep W.wSeries := by
      rw [Function.iterate_succ_apply']
      exact W.wStep_contract (W.X_dvd_iterate m) hX
        (dvd_sub_comm.mp (W.X_pow_dvd_wSeries_sub_iterate m))
    have := dvd_add h1 h2
    rwa [sub_add_sub_cancel] at this
  ext n
  have h := X_pow_dvd_iff.mp (key n) n (by lia)
  rwa [map_sub, sub_eq_zero] at h

private lemma X_pow_three_dvd_wStep {w : PowerSeries O} (hw : X ^ 3 ∣ w) :
    X ^ 3 ∣ W.wStep w := by
  obtain ⟨u, rfl⟩ := hw
  refine ⟨1 + C W.a₁ * X * u + C W.a₂ * X ^ 2 * u + C W.a₃ * (X ^ 3 * u ^ 2) +
    C W.a₄ * (X ^ 4 * u ^ 2) + C W.a₆ * (X ^ 6 * u ^ 3), ?_⟩
  simp only [wStep, wStepAt]
  ring

theorem X_pow_three_dvd_wSeries : (X : PowerSeries O) ^ 3 ∣ W.wSeries := by
  have h3 : X ^ 3 ∣ (W.wStep)^[3] (0 : PowerSeries O) := by
    have h0 : (X : PowerSeries O) ^ 3 ∣ 0 := dvd_zero _
    exact W.X_pow_three_dvd_wStep (W.X_pow_three_dvd_wStep (W.X_pow_three_dvd_wStep h0))
  have h := dvd_add (W.X_pow_dvd_wSeries_sub_iterate 3) h3
  rwa [sub_add_cancel] at h

@[simp]
theorem constantCoeff_wSeries : constantCoeff W.wSeries = 0 :=
  X_dvd_iff.mp (dvd_trans (dvd_pow_self X three_ne_zero) W.X_pow_three_dvd_wSeries)

theorem coeff_wSeries_of_lt {k : ℕ} (hk : k < 3) : coeff k W.wSeries = 0 :=
  X_pow_dvd_iff.mp W.X_pow_three_dvd_wSeries k hk

@[simp]
theorem coeff_wSeries_three : coeff 3 W.wSeries = 1 := by
  have h4 : X ^ 4 ∣ W.wStep W.wSeries - X ^ 3 := by
    obtain ⟨u, hu⟩ := W.X_pow_three_dvd_wSeries
    refine ⟨C W.a₁ * u + C W.a₂ * (X * u) + C W.a₃ * (X ^ 2 * u ^ 2) +
      C W.a₄ * (X ^ 3 * u ^ 2) + C W.a₆ * (X ^ 5 * u ^ 3), ?_⟩
    rw [hu]
    simp only [wStep, wStepAt]
    ring
  have h0 : coeff 3 (W.wStep W.wSeries - X ^ 3) = 0 := X_pow_dvd_iff.mp h4 3 (by lia)
  rw [map_sub, coeff_X_pow, if_pos rfl, sub_eq_zero] at h0
  rw [W.wSeries_eq_wStep, h0]

/-- The defining fixed-point equation of `wSeries`, i.e. the Weierstrass equation in the
coordinates `(t, w)`. -/
theorem wSeries_eq :
    W.wSeries = X ^ 3 + PowerSeries.C W.a₁ * X * W.wSeries +
      PowerSeries.C W.a₂ * X ^ 2 * W.wSeries + PowerSeries.C W.a₃ * W.wSeries ^ 2 +
      PowerSeries.C W.a₄ * X * W.wSeries ^ 2 + PowerSeries.C W.a₆ * W.wSeries ^ 3 :=
  W.wSeries_eq_wStep

/-- The unit part of `wSeries`: `w = t³·v` with `v(0) = 1`. -/
noncomputable def vSeries : PowerSeries O :=
  (W.X_pow_three_dvd_wSeries).choose

lemma wSeries_eq_X_pow_three_mul : W.wSeries = X ^ 3 * W.vSeries :=
  (W.X_pow_three_dvd_wSeries).choose_spec

@[simp]
lemma constantCoeff_vSeries : constantCoeff W.vSeries = 1 := by
  have h := congrArg (coeff 3) W.wSeries_eq_X_pow_three_mul
  rw [W.coeff_wSeries_three, show (3 : ℕ) = 0 + 3 from rfl,
    PowerSeries.coeff_X_pow_mul] at h
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact h.symm

/-!
### The chord construction

The slope and intercept of the chord through the points with parameters `t₁`, `t₂` on the
curve `(t, w(t))`, as power series in `O⟦t₁, t₂⟧` (variables indexed by `Unit ⊕ Unit`, as
in the formal-group-law kit).
-/

section Chord

open MvPowerSeries

-- coefficients of a one-variable series renamed into a single variable `s`
private lemma coeff_rename_single {τ : Type*} [DecidableEq τ] (s : τ) (w : PowerSeries O)
    (d : τ →₀ ℕ) :
    MvPowerSeries.coeff d (MvPowerSeries.rename (fun _ : Unit ↦ s) w) =
      if d = Finsupp.single s (d s) then PowerSeries.coeff (d s) w else 0 := by
  split_ifs with h
  · have hd : d = Finsupp.embDomain (⟨fun _ ↦ s, fun _ _ _ ↦ rfl⟩ : Unit ↪ τ)
        (Finsupp.single () (d s)) := by
      rw [Finsupp.embDomain_single]
      exact h
    have h1 := coeff_embDomain_rename (⟨fun _ ↦ s, fun _ _ _ ↦ rfl⟩ : Unit ↪ τ) w
      (Finsupp.single () (d s))
    rw [← hd] at h1
    exact h1
  · refine coeff_rename_eq_zero _ _ fun ⟨y, hy⟩ ↦ h ?_
    rw [← hy, Finsupp.unique_single y, Finsupp.mapDomain_single]
    simp

variable (W : WeierstrassCurve O)

/-- The slope (divided difference) series `λ(t₁, t₂) = (w(t₂) - w(t₁))/(t₂ - t₁)`,
defined directly by its coefficients: the coefficient of `t₁ⁱt₂ʲ` is the coefficient of
`t^(i+j+1)` in `wSeries`. -/
noncomputable def slopeSeries : MvPowerSeries (Unit ⊕ Unit) O :=
  fun d ↦ PowerSeries.coeff (d (Sum.inl ()) + d (Sum.inr ()) + 1) W.wSeries

lemma coeff_slopeSeries (d : Unit ⊕ Unit →₀ ℕ) :
    MvPowerSeries.coeff d W.slopeSeries =
      PowerSeries.coeff (d (Sum.inl ()) + d (Sum.inr ()) + 1) W.wSeries :=
  rfl

private lemma eq_single_iff (d : Unit ⊕ Unit →₀ ℕ) :
    d = Finsupp.single (Sum.inr ()) (d (Sum.inr ())) ↔ d (Sum.inl ()) = 0 := by
  constructor
  · intro h
    rw [h]
    simp
  · intro h
    ext t
    match t with
    | .inl () => simpa using h
    | .inr () => simp

private lemma eq_single_iff' (d : Unit ⊕ Unit →₀ ℕ) :
    d = Finsupp.single (Sum.inl ()) (d (Sum.inl ())) ↔ d (Sum.inr ()) = 0 := by
  constructor
  · intro h
    rw [h]
    simp
  · intro h
    ext t
    match t with
    | .inl () => simp
    | .inr () => simpa using h

/-- The defining property of the slope series:
`λ(t₁, t₂) · (t₂ - t₁) = w(t₂) - w(t₁)`. -/
theorem slopeSeries_mul_sub :
    W.slopeSeries * (MvPowerSeries.X (Sum.inr ()) - MvPowerSeries.X (Sum.inl ())) =
      MvPowerSeries.rename (fun _ ↦ Sum.inr ()) W.wSeries -
        MvPowerSeries.rename (fun _ ↦ Sum.inl ()) W.wSeries := by
  ext d
  set i := d (Sum.inl ()) with hi
  set j := d (Sum.inr ()) with hj
  rw [mul_sub, map_sub, map_sub,
    show (MvPowerSeries.X (Sum.inr ()) : MvPowerSeries (Unit ⊕ Unit) O) =
      MvPowerSeries.monomial (Finsupp.single (Sum.inr ()) 1) 1 from rfl,
    show (MvPowerSeries.X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit) O) =
      MvPowerSeries.monomial (Finsupp.single (Sum.inl ()) 1) 1 from rfl,
    MvPowerSeries.coeff_mul_monomial, MvPowerSeries.coeff_mul_monomial,
    coeff_rename_single, coeff_rename_single]
  have hsubr : 1 ≤ j → (d - Finsupp.single (Sum.inr ()) 1 : Unit ⊕ Unit →₀ ℕ) (Sum.inl ()) +
      (d - Finsupp.single (Sum.inr ()) 1 : Unit ⊕ Unit →₀ ℕ) (Sum.inr ()) + 1 = i + j := by
    intro h
    simp only [Finsupp.tsub_apply, Finsupp.single_apply]
    simp
    lia
  have hsubl : 1 ≤ i → (d - Finsupp.single (Sum.inl ()) 1 : Unit ⊕ Unit →₀ ℕ) (Sum.inl ()) +
      (d - Finsupp.single (Sum.inl ()) 1 : Unit ⊕ Unit →₀ ℕ) (Sum.inr ()) + 1 = i + j := by
    intro h
    simp only [Finsupp.tsub_apply, Finsupp.single_apply]
    simp
    lia
  simp only [mul_one, eq_single_iff, eq_single_iff', Finsupp.single_le_iff, coeff_slopeSeries]
  split_ifs with h1 h2 h3 h4 <;>
    grind

/-- The intercept series `ν(t₁, t₂) = w(t₁) - λ(t₁, t₂)·t₁` of the chord through the
points with parameters `t₁`, `t₂` on the curve `(t, w(t))`. -/
noncomputable def interceptSeries : MvPowerSeries (Unit ⊕ Unit) O :=
  MvPowerSeries.rename (fun _ ↦ Sum.inl ()) W.wSeries -
    W.slopeSeries * MvPowerSeries.X (Sum.inl ())

/-- The intercept series is symmetric in the two parameters. -/
theorem interceptSeries_eq :
    W.interceptSeries = MvPowerSeries.rename (fun _ ↦ Sum.inr ()) W.wSeries -
      W.slopeSeries * MvPowerSeries.X (Sum.inr ()) := by
  have h := W.slopeSeries_mul_sub
  simp only [interceptSeries]
  linear_combination h

@[simp]
lemma constantCoeff_slopeSeries : constantCoeff W.slopeSeries = 0 := by
  have h : constantCoeff W.slopeSeries =
      PowerSeries.coeff ((0 : Unit ⊕ Unit →₀ ℕ) (Sum.inl ()) + (0 : Unit ⊕ Unit →₀ ℕ)
        (Sum.inr ()) + 1) W.wSeries :=
    W.coeff_slopeSeries 0
  rw [h]
  exact W.coeff_wSeries_of_lt (by simp)

lemma constantCoeff_wSeries_mv : MvPowerSeries.constantCoeff W.wSeries = 0 :=
  W.constantCoeff_wSeries

@[simp]
lemma constantCoeff_interceptSeries : constantCoeff W.interceptSeries = 0 := by
  simp [interceptSeries, constantCoeff_rename, W.constantCoeff_wSeries_mv]

/-- The third-root series: the parameter `t₃(t₁, t₂)` of the third intersection point of
the chord through the points with parameters `t₁`, `t₂` with the curve `(t, w(t))`.
By Vieta applied to the cubic in `t` obtained by substituting `w = λt + ν` into the
Weierstrass equation,
`t₃ = -t₁ - t₂ - (a₁λ + a₂ν + a₃λ² + 2a₄λν + 3a₆λ²ν)/(1 + a₂λ + a₄λ² + a₆λ³)`. -/
noncomputable def thirdRootSeries : MvPowerSeries (Unit ⊕ Unit) O :=
  -MvPowerSeries.X (Sum.inl ()) - MvPowerSeries.X (Sum.inr ()) -
    (MvPowerSeries.C W.a₁ * W.slopeSeries + MvPowerSeries.C W.a₂ * W.interceptSeries +
        MvPowerSeries.C W.a₃ * W.slopeSeries ^ 2 +
        2 * MvPowerSeries.C W.a₄ * W.slopeSeries * W.interceptSeries +
        3 * MvPowerSeries.C W.a₆ * W.slopeSeries ^ 2 * W.interceptSeries) *
      MvPowerSeries.invOfUnit (1 + MvPowerSeries.C W.a₂ * W.slopeSeries +
        MvPowerSeries.C W.a₄ * W.slopeSeries ^ 2 + MvPowerSeries.C W.a₆ * W.slopeSeries ^ 3) 1

@[simp]
lemma constantCoeff_thirdRootSeries : constantCoeff W.thirdRootSeries = 0 := by
  simp [thirdRootSeries]

/-- The series `u(t) = 1 - a₁t - a₃w(t)`: minus the denominator `y` of the coordinates
`x = t/w`, `y = -1/w` of the negative of the point with parameter `t`, rescaled by `w`. -/
noncomputable def uSeries : PowerSeries O :=
  1 - PowerSeries.C W.a₁ * PowerSeries.X - PowerSeries.C W.a₃ * W.wSeries

@[simp]
lemma constantCoeff_uSeries : PowerSeries.constantCoeff W.uSeries = 1 := by
  simp [uSeries]

lemma mul_invOfUnit_uSeries : W.uSeries * PowerSeries.invOfUnit W.uSeries 1 = 1 :=
  PowerSeries.mul_invOfUnit _ _ (by simp)

lemma isUnit_uSeries : IsUnit W.uSeries :=
  IsUnit.of_mul_eq_one _ W.mul_invOfUnit_uSeries

/-- The formal inverse parameter series: the parameter `ι(t) = -t/(1 - a₁t - a₃w(t))` of
the negative of the point with parameter `t` on the curve `(t, w(t))`. -/
noncomputable def inverseSeries : PowerSeries O :=
  -(PowerSeries.X * PowerSeries.invOfUnit W.uSeries 1)

@[simp]
lemma constantCoeff_inverseSeries : PowerSeries.constantCoeff W.inverseSeries = 0 := by
  simp [inverseSeries]

lemma hasSubst_inverseSeries : PowerSeries.HasSubst (W.inverseSeries : PowerSeries O) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' W.constantCoeff_inverseSeries

private lemma subst_one_eq (a : PowerSeries O) (ha : PowerSeries.HasSubst a) :
    PowerSeries.subst a (1 : PowerSeries O) = 1 := by
  rw [← PowerSeries.coe_substAlgHom ha, map_one]

-- substitution along `ι` maps `invOfUnit` to `invOfUnit` of the image
private lemma subst_inverseSeries_invOfUnit {D : PowerSeries O}
    (hD : PowerSeries.constantCoeff D = 1)
    (hD' : PowerSeries.constantCoeff (PowerSeries.subst W.inverseSeries D) = 1) :
    PowerSeries.subst W.inverseSeries (PowerSeries.invOfUnit D 1) =
      PowerSeries.invOfUnit (PowerSeries.subst W.inverseSeries D) 1 := by
  have h1 : PowerSeries.subst W.inverseSeries D *
      PowerSeries.subst W.inverseSeries (PowerSeries.invOfUnit D 1) = 1 := by
    rw [← PowerSeries.subst_mul W.hasSubst_inverseSeries,
      PowerSeries.mul_invOfUnit _ 1 (by rw [hD]; rfl), subst_one_eq _ W.hasSubst_inverseSeries]
  have h2 : PowerSeries.subst W.inverseSeries D *
      PowerSeries.invOfUnit (PowerSeries.subst W.inverseSeries D) 1 = 1 :=
    PowerSeries.mul_invOfUnit _ 1 (by rw [hD']; rfl)
  calc PowerSeries.subst W.inverseSeries (PowerSeries.invOfUnit D 1)
      = PowerSeries.subst W.inverseSeries (PowerSeries.invOfUnit D 1) *
        (PowerSeries.subst W.inverseSeries D *
          PowerSeries.invOfUnit (PowerSeries.subst W.inverseSeries D) 1) := by
        rw [h2, mul_one]
    _ = (PowerSeries.subst W.inverseSeries D *
          PowerSeries.subst W.inverseSeries (PowerSeries.invOfUnit D 1)) *
        PowerSeries.invOfUnit (PowerSeries.subst W.inverseSeries D) 1 := by ring
    _ = PowerSeries.invOfUnit (PowerSeries.subst W.inverseSeries D) 1 := by rw [h1, one_mul]

private lemma subst_inverseSeries_wStepAt (v : PowerSeries O) :
    PowerSeries.subst W.inverseSeries (W.wStepAt X v) =
      W.wStepAt W.inverseSeries (PowerSeries.subst W.inverseSeries v) := by
  simp only [wStepAt, PowerSeries.subst_add W.hasSubst_inverseSeries,
    PowerSeries.subst_mul W.hasSubst_inverseSeries,
    PowerSeries.subst_pow W.hasSubst_inverseSeries, PowerSeries.subst_C,
    PowerSeries.subst_X W.hasSubst_inverseSeries]
  rfl

/-- Composition with the formal inverse maps `w` to `-w/u` (the `w`-coordinate of the
negative of a point). -/
theorem subst_inverseSeries_wSeries :
    PowerSeries.subst W.inverseSeries W.wSeries =
      -(W.wSeries * PowerSeries.invOfUnit W.uSeries 1) := by
  refine W.eq_of_wStepAt_fixed (q := W.inverseSeries)
    ⟨-(PowerSeries.invOfUnit W.uSeries 1), by rw [inverseSeries]; ring⟩ ?_ ?_ ?_ ?_
  · -- `X ∣ subst ι w`
    rw [PowerSeries.X_dvd_iff]
    exact MvPowerSeries.constantCoeff_subst_eq_zero W.hasSubst_inverseSeries.const
      (fun _ ↦ W.constantCoeff_inverseSeries) W.constantCoeff_wSeries
  · exact ((PowerSeries.X_dvd_iff.mpr W.constantCoeff_wSeries).mul_right _).neg_right
  · -- `w ∘ ι` solves the Weierstrass equation at `ι`
    conv_lhs => rw [W.wSeries_eq_wStep]
    rw [show W.wStep W.wSeries = W.wStepAt X W.wSeries from rfl,
      W.subst_inverseSeries_wStepAt]
  · -- `-w/u` solves the Weierstrass equation at `ι`
    refine (W.isUnit_uSeries.pow 3).mul_left_cancel ?_
    have h1 := W.mul_invOfUnit_uSeries
    have h2 := W.wSeries_eq_wStep
    rw [show W.wStep W.wSeries = W.wStepAt X W.wSeries from rfl, wStepAt] at h2
    simp only [wStepAt, inverseSeries, uSeries] at h1 h2 ⊢
    grobner

/-- Composition with the formal inverse maps `u` to its inverse. -/
theorem subst_inverseSeries_uSeries :
    PowerSeries.subst W.inverseSeries W.uSeries = PowerSeries.invOfUnit W.uSeries 1 := by
  refine W.isUnit_uSeries.mul_left_cancel ?_
  rw [W.mul_invOfUnit_uSeries]
  simp only [uSeries, PowerSeries.subst_sub W.hasSubst_inverseSeries,
    PowerSeries.subst_mul W.hasSubst_inverseSeries, PowerSeries.subst_C,
    PowerSeries.subst_X W.hasSubst_inverseSeries, subst_one_eq _ W.hasSubst_inverseSeries,
    W.subst_inverseSeries_wSeries]
  have h1 := W.mul_invOfUnit_uSeries
  simp only [uSeries, inverseSeries,
    show (MvPowerSeries.C : O →+* MvPowerSeries Unit O) = PowerSeries.C from rfl] at h1 ⊢
  grobner

/-- The formal inverse is an involution. -/
theorem subst_inverseSeries_self :
    PowerSeries.subst W.inverseSeries W.inverseSeries = PowerSeries.X := by
  have hinv := W.subst_inverseSeries_invOfUnit (D := W.uSeries) (by simp)
    (by rw [W.subst_inverseSeries_uSeries]
        simp [PowerSeries.constantCoeff_invOfUnit])
  have hdouble : PowerSeries.invOfUnit (PowerSeries.invOfUnit W.uSeries 1) 1 = W.uSeries := by
    have h1 : PowerSeries.invOfUnit W.uSeries 1 * W.uSeries = 1 := by
      rw [mul_comm]
      exact W.mul_invOfUnit_uSeries
    have h2 : PowerSeries.invOfUnit W.uSeries 1 *
        PowerSeries.invOfUnit (PowerSeries.invOfUnit W.uSeries 1) 1 = 1 :=
      PowerSeries.mul_invOfUnit _ 1 (by simp [PowerSeries.constantCoeff_invOfUnit])
    calc PowerSeries.invOfUnit (PowerSeries.invOfUnit W.uSeries 1) 1
        = (PowerSeries.invOfUnit W.uSeries 1 * W.uSeries) *
          PowerSeries.invOfUnit (PowerSeries.invOfUnit W.uSeries 1) 1 := by rw [h1, one_mul]
      _ = W.uSeries * (PowerSeries.invOfUnit W.uSeries 1 *
          PowerSeries.invOfUnit (PowerSeries.invOfUnit W.uSeries 1) 1) := by ring
      _ = W.uSeries := by rw [h2, mul_one]
  have hexp : PowerSeries.subst W.inverseSeries (-(PowerSeries.X *
      PowerSeries.invOfUnit W.uSeries 1)) = -(W.inverseSeries *
      PowerSeries.subst W.inverseSeries (PowerSeries.invOfUnit W.uSeries 1)) := by
    rw [← PowerSeries.coe_substAlgHom W.hasSubst_inverseSeries, map_neg, map_mul,
      PowerSeries.coe_substAlgHom W.hasSubst_inverseSeries,
      PowerSeries.subst_X W.hasSubst_inverseSeries]
  rw [show PowerSeries.subst W.inverseSeries W.inverseSeries = -(W.inverseSeries *
      PowerSeries.subst W.inverseSeries (PowerSeries.invOfUnit W.uSeries 1)) from hexp,
    hinv, W.subst_inverseSeries_uSeries, hdouble, inverseSeries]
  linear_combination (PowerSeries.X : PowerSeries O) * W.mul_invOfUnit_uSeries

/-- The addition series of the chord construction: `F(t₁, t₂) = ι(t₃(t₁, t₂))`, the
parameter of the sum of the points with parameters `t₁`, `t₂`. -/
noncomputable def addSeries : MvPowerSeries (Unit ⊕ Unit) O :=
  MvPowerSeries.subst (fun _ : Unit ↦ W.thirdRootSeries) W.inverseSeries

lemma hasSubst_thirdRootSeries :
    MvPowerSeries.HasSubst (fun _ : Unit ↦ W.thirdRootSeries) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ ↦ W.constantCoeff_thirdRootSeries

@[simp]
lemma constantCoeff_addSeries :
    MvPowerSeries.constantCoeff W.addSeries = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero W.hasSubst_thirdRootSeries
    (fun _ ↦ W.constantCoeff_thirdRootSeries) W.constantCoeff_inverseSeries

/-! Swap-invariance of the chord data, giving commutativity of the formal group law. -/

lemma rename_swap_slopeSeries :
    MvPowerSeries.rename Sum.swap W.slopeSeries = W.slopeSeries := by
  ext d
  have hd : d = Finsupp.embDomain (Equiv.sumComm Unit Unit).toEmbedding
      (Finsupp.mapDomain Sum.swap d) := by
    ext t
    rw [Finsupp.embDomain_eq_mapDomain, ← Finsupp.mapDomain_comp]
    have : (⇑(Equiv.sumComm Unit Unit).toEmbedding ∘ Sum.swap) = id := by
      ext s
      match s with
      | .inl () => rfl
      | .inr () => rfl
    rw [this, Finsupp.mapDomain_id]
  calc MvPowerSeries.coeff d (MvPowerSeries.rename Sum.swap W.slopeSeries)
      = MvPowerSeries.coeff (Finsupp.mapDomain Sum.swap d) W.slopeSeries := by
        conv_lhs => rw [hd]
        exact coeff_embDomain_rename _ _ _
    _ = MvPowerSeries.coeff d W.slopeSeries := by
        rw [W.coeff_slopeSeries, W.coeff_slopeSeries]
        have h1 : Finsupp.mapDomain Sum.swap d (Sum.inl ()) = d (Sum.inr ()) := by
          rw [show (Sum.inl () : Unit ⊕ Unit) = (Equiv.sumComm Unit Unit) (Sum.inr ()) from rfl]
          exact Finsupp.mapDomain_equiv_apply (f := Equiv.sumComm Unit Unit) d _ |>.trans (by rfl)
        have h2 : Finsupp.mapDomain Sum.swap d (Sum.inr ()) = d (Sum.inl ()) := by
          rw [show (Sum.inr () : Unit ⊕ Unit) = (Equiv.sumComm Unit Unit) (Sum.inl ()) from rfl]
          exact Finsupp.mapDomain_equiv_apply (f := Equiv.sumComm Unit Unit) d _ |>.trans (by rfl)
        rw [h1, h2, add_comm (d (Sum.inr ()))]

lemma rename_swap_interceptSeries :
    MvPowerSeries.rename Sum.swap W.interceptSeries = W.interceptSeries := by
  rw [interceptSeries, map_sub, map_mul, W.rename_swap_slopeSeries, rename_X, rename_rename]
  exact W.interceptSeries_eq.symm

private lemma rename_swap_invOfUnit {D : MvPowerSeries (Unit ⊕ Unit) O}
    (hD : MvPowerSeries.constantCoeff D = 1) :
    MvPowerSeries.rename Sum.swap (MvPowerSeries.invOfUnit D 1) =
      MvPowerSeries.invOfUnit (MvPowerSeries.rename Sum.swap D) 1 := by
  have h1 : MvPowerSeries.rename Sum.swap D *
      MvPowerSeries.rename Sum.swap (MvPowerSeries.invOfUnit D 1) = 1 := by
    rw [← map_mul, MvPowerSeries.mul_invOfUnit D 1 (by rw [hD]; rfl), map_one]
  have h2 : MvPowerSeries.rename Sum.swap D *
      MvPowerSeries.invOfUnit (MvPowerSeries.rename Sum.swap D) 1 =
      1 :=
    MvPowerSeries.mul_invOfUnit _ 1 (by rw [constantCoeff_rename, hD]; rfl)
  calc MvPowerSeries.rename Sum.swap (MvPowerSeries.invOfUnit D 1)
      = MvPowerSeries.rename Sum.swap (MvPowerSeries.invOfUnit D 1) *
        (MvPowerSeries.rename Sum.swap D *
          MvPowerSeries.invOfUnit (MvPowerSeries.rename Sum.swap D) 1) := by rw [h2, mul_one]
    _ = (MvPowerSeries.rename Sum.swap D *
          MvPowerSeries.rename Sum.swap (MvPowerSeries.invOfUnit D 1)) *
        MvPowerSeries.invOfUnit (MvPowerSeries.rename Sum.swap D) 1 := by ring
    _ = MvPowerSeries.invOfUnit (MvPowerSeries.rename Sum.swap D) 1 := by rw [h1, one_mul]

lemma rename_swap_thirdRootSeries :
    MvPowerSeries.rename Sum.swap W.thirdRootSeries = W.thirdRootSeries := by
  have hD : MvPowerSeries.constantCoeff (1 + MvPowerSeries.C W.a₂ * W.slopeSeries +
      MvPowerSeries.C W.a₄ * W.slopeSeries ^ 2 + MvPowerSeries.C W.a₆ * W.slopeSeries ^ 3) =
      1 := by
    simp
  rw [thirdRootSeries]
  simp only [map_sub, map_neg, map_add, map_mul, map_pow, map_one, map_ofNat, rename_X,
    MvPowerSeries.rename_C, W.rename_swap_slopeSeries, W.rename_swap_interceptSeries,
    rename_swap_invOfUnit hD]
  simp only [show Sum.swap (Sum.inl () : Unit ⊕ Unit) = Sum.inr () from rfl,
    show Sum.swap (Sum.inr () : Unit ⊕ Unit) = Sum.inl () from rfl]
  ring

lemma rename_swap_addSeries :
    MvPowerSeries.rename Sum.swap W.addSeries = W.addSeries := by
  rw [addSeries, rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply W.hasSubst_thirdRootSeries (HasSubst.X_comp _)]
  congr 1
  funext u
  rw [← rename_eq_subst, W.rename_swap_thirdRootSeries]

section AddZero

/-! Specialization of the chord data at `t₂ = 0`: the slope becomes `w(t)/t`, the intercept
vanishes, and the third root becomes the formal inverse `ι(t)`. -/

private lemma hasSubst_unitR :
    MvPowerSeries.HasSubst
      (Sum.elim MvPowerSeries.X (fun _ ↦ 0) : Unit ⊕ Unit → MvPowerSeries Unit O) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp)

/- Compatibility with the LeanPool mathlib pin, which predates the
zero-family substitution lemma. -/
lemma subst_zero_of_constantCoeff_zero_compat {σ τ : Type*}
    (f : MvPowerSeries σ O) (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.subst (0 : σ → MvPowerSeries τ O) f = 0 := by
  classical
  ext n
  change MvPowerSeries.coeff n
      (MvPowerSeries.subst (fun _ : σ ↦ (0 : MvPowerSeries τ O)) f) = 0
  rw [MvPowerSeries.coeff_subst MvPowerSeries.HasSubst.zero,
    finsum_eq_single _ 0]
  · by_cases hn : n = 0
    · subst n
      simp [hf]
    · simp [MvPowerSeries.coeff_one, hn]
  · intro d hd
    obtain ⟨i, hi⟩ : d.support.Nonempty := d.support_nonempty_iff.mpr hd
    simp [Finsupp.prod, Finset.prod_eq_zero hi, MvPowerSeries.coeff_zero,
      zero_pow <| d.mem_support_iff.mp hi]

private lemma subst_unitR_renameL :
    MvPowerSeries.subst (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O)
      (MvPowerSeries.rename (fun _ ↦ Sum.inl ()) W.wSeries) = W.wSeries := by
  rw [MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_comp _) hasSubst_unitR]
  have hX : (fun u : Unit ↦ MvPowerSeries.subst
      (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O)
      ((MvPowerSeries.X ∘ fun _ ↦ Sum.inl () : Unit → MvPowerSeries (Unit ⊕ Unit) O) u)) =
      MvPowerSeries.X := by
    funext u
    rw [Function.comp_apply, MvPowerSeries.subst_X hasSubst_unitR]
    rfl
  rw [hX, ← MvPowerSeries.map_algebraMap_eq_subst_X]
  have : algebraMap O O = RingHom.id O := rfl
  rw [this]
  exact congrFun (congrArg _ (MvPowerSeries.map_id)) W.wSeries

private lemma subst_unitR_renameR :
    MvPowerSeries.subst (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O)
      (MvPowerSeries.rename (fun _ ↦ Sum.inr ()) W.wSeries) = 0 := by
  rw [MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_comp _) hasSubst_unitR]
  have hX : (fun u : Unit ↦ MvPowerSeries.subst
      (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O)
      ((MvPowerSeries.X ∘ fun _ ↦ Sum.inr () : Unit → MvPowerSeries (Unit ⊕ Unit) O) u)) =
      fun _ ↦ 0 := by
    funext u
    rw [Function.comp_apply, MvPowerSeries.subst_X hasSubst_unitR]
    rfl
  rw [hX]
  exact subst_zero_of_constantCoeff_zero_compat W.wSeries W.constantCoeff_wSeries

private lemma X_mul_subst_unitR_slopeSeries :
    (PowerSeries.X : PowerSeries O) *
      MvPowerSeries.subst (Sum.elim MvPowerSeries.X fun _ ↦ 0) W.slopeSeries = W.wSeries := by
  have h := congrArg (MvPowerSeries.subst
    (Sum.elim MvPowerSeries.X (fun _ ↦ 0) : Unit ⊕ Unit → MvPowerSeries Unit O))
    W.slopeSeries_mul_sub
  rw [← MvPowerSeries.coe_substAlgHom hasSubst_unitR] at h
  simp only [map_mul, map_sub] at h
  simp only [MvPowerSeries.coe_substAlgHom hasSubst_unitR, W.subst_unitR_renameL,
    W.subst_unitR_renameR, MvPowerSeries.subst_X hasSubst_unitR] at h
  have h1 : (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O)
      (Sum.inr ()) = 0 := rfl
  have h2 : (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O)
      (Sum.inl ()) = PowerSeries.X := rfl
  rw [h1, h2] at h
  linear_combination -h

private lemma subst_unitR_interceptSeries :
    MvPowerSeries.subst (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O)
      W.interceptSeries = 0 := by
  rw [interceptSeries, ← MvPowerSeries.coe_substAlgHom hasSubst_unitR, map_sub, map_mul]
  simp only [MvPowerSeries.coe_substAlgHom hasSubst_unitR, W.subst_unitR_renameL,
    MvPowerSeries.subst_X hasSubst_unitR]
  have h2 : (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O)
      (Sum.inl ()) = PowerSeries.X := rfl
  rw [h2]
  linear_combination -W.X_mul_subst_unitR_slopeSeries

-- transport of `invOfUnit` along a ring homomorphism fixing the constant coefficient
private lemma ringHom_invOfUnit {O' : Type*} [CommRing O'] {σ' τ' : Type*} {F : Type*}
    [FunLike F (MvPowerSeries σ' O) (MvPowerSeries τ' O')]
    [RingHomClass F (MvPowerSeries σ' O) (MvPowerSeries τ' O')] (φ : F)
    {D : MvPowerSeries σ' O} (hD : MvPowerSeries.constantCoeff D = 1)
    (hD' : MvPowerSeries.constantCoeff (φ D) = 1) :
    φ (MvPowerSeries.invOfUnit D 1) = MvPowerSeries.invOfUnit (φ D) 1 := by
  have h1 : φ D * φ (MvPowerSeries.invOfUnit D 1) = 1 := by
    rw [← map_mul, MvPowerSeries.mul_invOfUnit D 1 (by rw [hD]; rfl), map_one]
  have h2 : φ D * MvPowerSeries.invOfUnit (φ D) 1 = 1 :=
    MvPowerSeries.mul_invOfUnit _ 1 (by rw [hD']; rfl)
  calc φ (MvPowerSeries.invOfUnit D 1)
      = φ (MvPowerSeries.invOfUnit D 1) * (φ D * MvPowerSeries.invOfUnit (φ D) 1) := by
        rw [h2, mul_one]
    _ = (φ D * φ (MvPowerSeries.invOfUnit D 1)) * MvPowerSeries.invOfUnit (φ D) 1 := by ring
    _ = MvPowerSeries.invOfUnit (φ D) 1 := by rw [h1, one_mul]

/-- Specializing the third-root series at `t₂ = 0` gives the formal inverse. -/
theorem subst_unitR_thirdRootSeries :
    MvPowerSeries.subst (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O)
      W.thirdRootSeries = W.inverseSeries := by
  set L : PowerSeries O :=
    MvPowerSeries.subst (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O)
      W.slopeSeries with hL
  have hXL : PowerSeries.X * L = W.wSeries := W.X_mul_subst_unitR_slopeSeries
  -- the specialized slope satisfies the `X`-cancelled Weierstrass equation
  have hLfix : L = PowerSeries.X ^ 2 + PowerSeries.C W.a₁ * PowerSeries.X * L +
      PowerSeries.C W.a₂ * PowerSeries.X ^ 2 * L + PowerSeries.C W.a₃ * PowerSeries.X * L ^ 2 +
      PowerSeries.C W.a₄ * PowerSeries.X ^ 2 * L ^ 2 +
      PowerSeries.C W.a₆ * PowerSeries.X ^ 2 * L ^ 3 := by
    refine PowerSeries.X_mul_cancel ?_
    rw [hXL]
    conv_lhs => rw [W.wSeries_eq]
    rw [← hXL]
    ring
  have hL0 : PowerSeries.constantCoeff L = 0 := by
    have := congrArg PowerSeries.constantCoeff hLfix
    simpa [pow_two] using this
  -- push the substitution through the definition of the third root
  set D : MvPowerSeries (Unit ⊕ Unit) O := 1 + MvPowerSeries.C W.a₂ * W.slopeSeries +
    MvPowerSeries.C W.a₄ * W.slopeSeries ^ 2 + MvPowerSeries.C W.a₆ * W.slopeSeries ^ 3 with hD
  have hDsub : MvPowerSeries.subst
      (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O) D =
      1 + PowerSeries.C W.a₂ * L + PowerSeries.C W.a₄ * L ^ 2 + PowerSeries.C W.a₆ * L ^ 3 := by
    rw [hD, ← MvPowerSeries.coe_substAlgHom hasSubst_unitR]
    simp only [map_add, map_mul, map_pow, map_one]
    rw [MvPowerSeries.coe_substAlgHom hasSubst_unitR]
    simp only [MvPowerSeries.subst_C,
      show (MvPowerSeries.C : O →+* MvPowerSeries Unit O) = PowerSeries.C from rfl]
    rfl
  have hD1 : MvPowerSeries.constantCoeff D = 1 := by simp [hD]
  have hD1' : PowerSeries.constantCoeff
      (1 + PowerSeries.C W.a₂ * L + PowerSeries.C W.a₄ * L ^ 2 +
        PowerSeries.C W.a₆ * L ^ 3) = 1 := by
    simp [hL0]
  have hInv : MvPowerSeries.subst
      (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O)
      (MvPowerSeries.invOfUnit D 1) =
      MvPowerSeries.invOfUnit (1 + PowerSeries.C W.a₂ * L + PowerSeries.C W.a₄ * L ^ 2 +
        PowerSeries.C W.a₆ * L ^ 3) 1 := by
    have h := ringHom_invOfUnit (O' := O) (MvPowerSeries.substAlgHom hasSubst_unitR) hD1
      (by rw [MvPowerSeries.coe_substAlgHom, hDsub]; exact hD1')
    rwa [MvPowerSeries.coe_substAlgHom, hDsub] at h
  -- expand the substituted third root
  have hexp : MvPowerSeries.subst
      (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O)
      W.thirdRootSeries = -PowerSeries.X -
      (PowerSeries.C W.a₁ * L + PowerSeries.C W.a₃ * L ^ 2) *
        MvPowerSeries.invOfUnit (1 + PowerSeries.C W.a₂ * L + PowerSeries.C W.a₄ * L ^ 2 +
          PowerSeries.C W.a₆ * L ^ 3) 1 := by
    rw [thirdRootSeries, ← hD, ← MvPowerSeries.coe_substAlgHom hasSubst_unitR]
    simp only [map_sub, map_neg, map_add, map_mul, map_pow, map_ofNat]
    rw [MvPowerSeries.coe_substAlgHom hasSubst_unitR]
    simp only [MvPowerSeries.subst_C, MvPowerSeries.subst_X hasSubst_unitR, hInv,
      W.subst_unitR_interceptSeries,
      show (MvPowerSeries.C : O →+* MvPowerSeries Unit O) = PowerSeries.C from rfl]
    have h1 : (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O)
        (Sum.inr ()) = 0 := rfl
    have h2 : (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O)
        (Sum.inl ()) = PowerSeries.X := rfl
    rw [h1, h2]
    ring
  rw [hexp]
  -- compare with `ι = -X·u⁻¹` after multiplying by the units `u` and `D̃`
  set d : PowerSeries O := MvPowerSeries.invOfUnit (1 + PowerSeries.C W.a₂ * L +
    PowerSeries.C W.a₄ * L ^ 2 + PowerSeries.C W.a₆ * L ^ 3) 1 with hd
  have hUnit2 : (1 + PowerSeries.C W.a₂ * L + PowerSeries.C W.a₄ * L ^ 2 +
      PowerSeries.C W.a₆ * L ^ 3) * d = 1 :=
    MvPowerSeries.mul_invOfUnit _ 1 (by exact_mod_cast hD1')
  have hUnit1 := W.mul_invOfUnit_uSeries
  clear_value L d
  refine (W.isUnit_uSeries.mul (IsUnit.of_mul_eq_one _ hUnit2)).mul_left_cancel ?_
  rw [inverseSeries]
  simp only [uSeries] at hUnit1 ⊢
  rw [← hXL] at hUnit1 ⊢
  linear_combination ((1 + PowerSeries.C W.a₂ * L + PowerSeries.C W.a₄ * L ^ 2 +
      PowerSeries.C W.a₆ * L ^ 3) * PowerSeries.X) * hUnit1 -
    ((1 - PowerSeries.C W.a₁ * PowerSeries.X - PowerSeries.C W.a₃ * (PowerSeries.X * L)) *
      (PowerSeries.C W.a₁ * L + PowerSeries.C W.a₃ * L ^ 2)) * hUnit2 -
    (PowerSeries.C W.a₁ + PowerSeries.C W.a₃ * L) * hLfix

/-- Adding the zero point does nothing: specialization of the addition series at `t₂ = 0`
is the identity. -/
theorem subst_unitR_addSeries :
    MvPowerSeries.subst (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O)
      W.addSeries = PowerSeries.X := by
  rw [addSeries, MvPowerSeries.subst_comp_subst_apply W.hasSubst_thirdRootSeries hasSubst_unitR]
  have h : (fun _ : Unit ↦ MvPowerSeries.subst
      (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O)
      W.thirdRootSeries) = fun _ : Unit ↦ (W.inverseSeries : MvPowerSeries Unit O) := by
    funext u
    exact W.subst_unitR_thirdRootSeries
  rw [h]
  exact W.subst_inverseSeries_self

private lemma hasSubst_unitL :
    MvPowerSeries.HasSubst
      (Sum.elim (fun _ ↦ 0) MvPowerSeries.X : Unit ⊕ Unit → MvPowerSeries Unit O) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp)

/-- Adding the zero point on the left does nothing either, by commutativity. -/
theorem subst_unitL_addSeries :
    MvPowerSeries.subst (Sum.elim (fun _ ↦ 0) MvPowerSeries.X : Unit ⊕ Unit → MvPowerSeries Unit O)
      W.addSeries = PowerSeries.X := by
  conv_lhs => rw [← W.rename_swap_addSeries]
  rw [MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_comp _) hasSubst_unitL]
  have h : (fun s : Unit ⊕ Unit ↦ MvPowerSeries.subst
      (Sum.elim (fun _ ↦ 0) MvPowerSeries.X : Unit ⊕ Unit → MvPowerSeries Unit O)
      ((MvPowerSeries.X ∘ Sum.swap : Unit ⊕ Unit → MvPowerSeries (Unit ⊕ Unit) O) s)) =
      (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O) := by
    funext s
    rw [Function.comp_apply, MvPowerSeries.subst_X hasSubst_unitL]
    match s with
    | .inl () => rfl
    | .inr () => rfl
  rw [h]
  exact W.subst_unitR_addSeries

/-- Extract a linear coefficient from an axis substitution: if substituting `X` at `s₀` and
`0` at the other variable turns `f` into `X`, the linear coefficient of `f` at `s₀` is `1`. -/
private lemma coeff_single_eq_one_of_subst_eq_X {f : MvPowerSeries (Unit ⊕ Unit) O}
    {s₀ : Unit ⊕ Unit} {fam : Unit ⊕ Unit → MvPowerSeries Unit O}
    (hfam₀ : fam s₀ = MvPowerSeries.X ()) (hfam : ∀ s ≠ s₀, fam s = 0)
    (hsubst : MvPowerSeries.subst fam f = PowerSeries.X) :
    MvPowerSeries.coeff (Finsupp.single s₀ 1) f = 1 := by
  have hS : MvPowerSeries.HasSubst fam := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun s ↦ ?_
    rcases eq_or_ne s s₀ with rfl | h
    · rw [hfam₀]
      exact MvPowerSeries.constantCoeff_X ()
    · rw [hfam s h, map_zero]
  have h := congrArg (MvPowerSeries.coeff (Finsupp.single () 1)) hsubst
  rw [MvPowerSeries.coeff_subst hS, show (PowerSeries.X : PowerSeries O) =
    MvPowerSeries.X () from rfl, MvPowerSeries.coeff_X, if_pos rfl] at h
  rw [finsum_eq_single _ (Finsupp.single s₀ 1) (fun d hd ↦ ?_)] at h
  · rwa [Finsupp.prod_single_index (h := fun s e ↦ fam s ^ e) (pow_zero _), hfam₀, pow_one,
      MvPowerSeries.coeff_X, if_pos rfl, smul_eq_mul, mul_one] at h
  · rcases Classical.em (∃ s ≠ s₀, d s ≠ 0) with ⟨s, hs, hds⟩ | hd0
    · rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hds)
        (by rw [hfam s hs, zero_pow hds]), map_zero, smul_zero]
    · push Not at hd0
      have hd' : d = Finsupp.single s₀ (d s₀) := Finsupp.ext fun u ↦ by
        rcases eq_or_ne u s₀ with rfl | hu
        · rw [Finsupp.single_eq_same]
        · simp [hd0 u hu, Ne.symm hu]
      have hne1 : d s₀ ≠ 1 := fun h1 ↦ hd (by rw [hd', h1])
      rw [hd', Finsupp.prod_single_index (h := fun s e ↦ fam s ^ e) (pow_zero _), hfam₀,
        MvPowerSeries.X_pow_eq () (d s₀), MvPowerSeries.coeff_monomial,
        if_neg (by simpa using fun h ↦ absurd h.symm hne1), smul_zero]

/-- The linear coefficient of the addition series in the first variable is `1`. -/
theorem coeff_single_inl_addSeries :
    MvPowerSeries.coeff (Finsupp.single (Sum.inl ()) 1) W.addSeries = 1 :=
  coeff_single_eq_one_of_subst_eq_X rfl
    (fun s h ↦ by
      rcases s with u | u
      · exact absurd rfl h
      · rfl)
    W.subst_unitR_addSeries

/-- The linear coefficient of the addition series in the second variable is `1`. -/
theorem coeff_single_inr_addSeries :
    MvPowerSeries.coeff (Finsupp.single (Sum.inr ()) 1) W.addSeries = 1 :=
  coeff_single_eq_one_of_subst_eq_X rfl
    (fun s h ↦ by
      rcases s with u | u
      · rfl
      · exact absurd rfl h)
    W.subst_unitL_addSeries

private lemma degree_two_var (d : Unit ⊕ Unit →₀ ℕ) :
    d.degree = d (Sum.inl ()) + d (Sum.inr ()) := by
  conv_lhs => rw [show d = Finsupp.single (Sum.inl ()) (d (Sum.inl ())) +
    Finsupp.single (Sum.inr ()) (d (Sum.inr ())) from Finsupp.ext fun s ↦ by
      rcases s with u | u <;> simp]
  rw [map_add, Finsupp.degree_single, Finsupp.degree_single]

/-- Below total degree `2`, the addition series agrees with `t₁ + t₂`: the formal group
law is `F(t₁, t₂) = t₁ + t₂ + (higher order)`. -/
theorem coeff_addSeries_sub_of_degree_lt {d : Unit ⊕ Unit →₀ ℕ} (hd : d.degree < 2) :
    MvPowerSeries.coeff d (W.addSeries - MvPowerSeries.X (Sum.inl ()) -
      MvPowerSeries.X (Sum.inr ())) = 0 := by
  rw [degree_two_var] at hd
  simp only [map_sub, MvPowerSeries.coeff_X]
  have hcase : d (Sum.inl ()) = 0 ∧ d (Sum.inr ()) = 0 ∨
      d (Sum.inl ()) = 1 ∧ d (Sum.inr ()) = 0 ∨
      d (Sum.inl ()) = 0 ∧ d (Sum.inr ()) = 1 := by lia
  have hext : ∀ a b, d (Sum.inl ()) = a → d (Sum.inr ()) = b →
      d = Finsupp.single (Sum.inl ()) a + Finsupp.single (Sum.inr ()) b := fun a b ha hb ↦
    Finsupp.ext fun s ↦ by rcases s with u | u <;> simp [← ha, ← hb]
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [show d = _ from hext _ _ h1 h2] <;>
    simp [show MvPowerSeries.coeff (0 : Unit ⊕ Unit →₀ ℕ) W.addSeries =
        MvPowerSeries.constantCoeff W.addSeries from rfl, W.constantCoeff_addSeries,
      W.coeff_single_inl_addSeries, W.coeff_single_inr_addSeries,
      Finsupp.single_eq_single_iff,
      (Ne.symm (Finsupp.single_ne_zero.mpr one_ne_zero) :
        (0 : Unit ⊕ Unit →₀ ℕ) ≠ Finsupp.single (Sum.inl ()) 1),
      (Ne.symm (Finsupp.single_ne_zero.mpr one_ne_zero) :
        (0 : Unit ⊕ Unit →₀ ℕ) ≠ Finsupp.single (Sum.inr ()) 1)]

end AddZero

section Naturality

/-! ### Naturality of the chord construction under coefficient ring maps

Every ingredient of the chord construction commutes with base change along a ring
homomorphism `φ : O →+* O'`. This is the reduction engine for associativity: it transports
identities from the universal Weierstrass curve over `ℤ[A₁, …, A₆]` to any curve.
-/

variable {O' : Type*} [CommRing O'] (φ : O →+* O')

theorem map_wSeries : PowerSeries.map φ W.wSeries = (W.map φ).wSeries := by
  refine (W.map φ).eq_of_wStepAt_fixed (q := X) dvd_rfl ?_ ?_ ?_ ((W.map φ).wSeries_eq_wStep)
  · rw [PowerSeries.X_dvd_iff, show PowerSeries.constantCoeff (PowerSeries.map φ W.wSeries) =
      φ (PowerSeries.constantCoeff W.wSeries) from rfl, W.constantCoeff_wSeries, map_zero]
  · exact PowerSeries.X_dvd_iff.mpr (W.map φ).constantCoeff_wSeries
  · conv_lhs => rw [W.wSeries_eq_wStep]
    simp only [wStep, wStepAt, map_add, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X,
      WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]

theorem map_slopeSeries :
    MvPowerSeries.map φ W.slopeSeries = (W.map φ).slopeSeries := by
  ext d
  rw [MvPowerSeries.coeff_map, W.coeff_slopeSeries, (W.map φ).coeff_slopeSeries,
    ← W.map_wSeries φ, PowerSeries.coeff_map]

theorem map_interceptSeries :
    MvPowerSeries.map φ W.interceptSeries = (W.map φ).interceptSeries := by
  simp only [interceptSeries, map_sub, map_mul, ← MvPowerSeries.rename_map,
    MvPowerSeries.map_X, W.map_slopeSeries φ]
  rw [show MvPowerSeries.map φ (W.wSeries : MvPowerSeries Unit O) =
    ((W.map φ).wSeries : MvPowerSeries Unit O') from W.map_wSeries φ]

theorem map_uSeries : PowerSeries.map φ W.uSeries = (W.map φ).uSeries := by
  simp only [uSeries, map_sub, map_one, map_mul, PowerSeries.map_C, PowerSeries.map_X,
    W.map_wSeries φ, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]

theorem map_thirdRootSeries :
    MvPowerSeries.map φ W.thirdRootSeries = (W.map φ).thirdRootSeries := by
  have hinv : MvPowerSeries.map φ (MvPowerSeries.invOfUnit
      (1 + MvPowerSeries.C W.a₂ * W.slopeSeries + MvPowerSeries.C W.a₄ * W.slopeSeries ^ 2 +
        MvPowerSeries.C W.a₆ * W.slopeSeries ^ 3) 1) =
      MvPowerSeries.invOfUnit
      (1 + MvPowerSeries.C (W.map φ).a₂ * (W.map φ).slopeSeries +
        MvPowerSeries.C (W.map φ).a₄ * (W.map φ).slopeSeries ^ 2 +
        MvPowerSeries.C (W.map φ).a₆ * (W.map φ).slopeSeries ^ 3) 1 := by
    have h := ringHom_invOfUnit (MvPowerSeries.map φ)
      (D := 1 + MvPowerSeries.C W.a₂ * W.slopeSeries + MvPowerSeries.C W.a₄ * W.slopeSeries ^ 2 +
        MvPowerSeries.C W.a₆ * W.slopeSeries ^ 3) (by simp) (by simp)
    rw [h]
    congr 1
    simp only [map_add, map_one, map_mul, map_pow, MvPowerSeries.map_C, W.map_slopeSeries φ,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  simp only [thirdRootSeries, map_sub, map_neg, map_add, map_mul, map_pow, map_ofNat,
    MvPowerSeries.map_X, MvPowerSeries.map_C, W.map_slopeSeries φ, W.map_interceptSeries φ,
    hinv, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]

theorem map_inverseSeries :
    PowerSeries.map φ W.inverseSeries = (W.map φ).inverseSeries := by
  simp only [inverseSeries, PowerSeries.invOfUnit]
  have hD' : MvPowerSeries.constantCoeff (PowerSeries.map φ W.uSeries) = 1 := by
    rw [show (PowerSeries.map φ W.uSeries : PowerSeries O') = (W.map φ).uSeries
      from W.map_uSeries φ]
    exact (W.map φ).constantCoeff_uSeries
  have h := ringHom_invOfUnit (PowerSeries.map φ) (σ' := Unit) (τ' := Unit) (D := W.uSeries)
    (by exact W.constantCoeff_uSeries) hD'
  rw [map_neg, map_mul, PowerSeries.map_X, h, W.map_uSeries φ]

theorem map_addSeries :
    MvPowerSeries.map φ W.addSeries = (W.map φ).addSeries := by
  rw [addSeries, MvPowerSeries.map_subst W.hasSubst_thirdRootSeries, addSeries]
  congr 1
  · funext u
    exact W.map_thirdRootSeries φ
  · exact W.map_inverseSeries φ

end Naturality

private lemma hasSubst_assocLeftFam_addSeries :
    MvPowerSeries.HasSubst (assocLeftFam (fun _ : Unit ↦ W.addSeries)) := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
  rintro (j | j)
  · exact MvPowerSeries.constantCoeff_subst_eq_zero (FormalGroupLaw.hasSubst_emb12 (O := O))
      (by rintro (j | j) <;> simp) W.constantCoeff_addSeries
  · simp [assocLeftFam]

private lemma hasSubst_assocRightFam_addSeries :
    MvPowerSeries.HasSubst (assocRightFam (fun _ : Unit ↦ W.addSeries)) := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
  rintro (j | j)
  · simp [assocRightFam]
  · exact MvPowerSeries.constantCoeff_subst_eq_zero (FormalGroupLaw.hasSubst_emb23 (O := O))
      (by rintro (j | j) <;> simp) W.constantCoeff_addSeries

section Naturality

variable {O' : Type*} [CommRing O'] (φ : O →+* O')

private lemma map_assocLeftFam_addSeries :
    (fun s ↦ MvPowerSeries.map φ (assocLeftFam (fun _ : Unit ↦ W.addSeries) s)) =
      assocLeftFam (fun _ : Unit ↦ (W.map φ).addSeries) := by
  funext s
  match s with
  | .inl j =>
    simp only [assocLeftFam, Sum.elim_inl,
      MvPowerSeries.map_subst (FormalGroupLaw.hasSubst_emb12 (O := O)), W.map_addSeries φ]
    congr 1
    funext t
    rcases t with t | t <;> simp [MvPowerSeries.map_X]
  | .inr j => simp [assocLeftFam, MvPowerSeries.map_X]

private lemma map_assocRightFam_addSeries :
    (fun s ↦ MvPowerSeries.map φ (assocRightFam (fun _ : Unit ↦ W.addSeries) s)) =
      assocRightFam (fun _ : Unit ↦ (W.map φ).addSeries) := by
  funext s
  match s with
  | .inl j => simp [assocRightFam, MvPowerSeries.map_X]
  | .inr j =>
    simp only [assocRightFam, Sum.elim_inr,
      MvPowerSeries.map_subst (FormalGroupLaw.hasSubst_emb23 (O := O)), W.map_addSeries φ]
    congr 1
    funext t
    rcases t with t | t <;> simp [MvPowerSeries.map_X]

end Naturality

end Chord
end wSeries
end WeierstrassCurve

end
