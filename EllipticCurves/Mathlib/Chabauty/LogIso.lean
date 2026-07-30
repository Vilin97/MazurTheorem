/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
-- Vendored from the Chabauty project (`Chabauty/Series/LogIso.lean`).

module

public import EllipticCurves.Mathlib.Chabauty.ExpConverge

@[expose] public section

/-!
# The logarithm isomorphism

The formal logarithm `Λ` of a formal group law is an injective homomorphism on `(pO)ⁿ`
when `p` is odd and `O` is unramified (`𝔪 = pO`). The `p`-scaled log `HL` (with
`f(coeff_d HL) = f(p)^{deg d}·coeff_d Λ`) has an injective evaluation map
`y ↦ (evalT y (HL i))ᵢ` (`ChabautyColeman.FormalGroupLaw.log_injective`), which turns the
`p`-scaled formal group sum `ChabautyColeman.FormalGroupLaw.scaledF` — `F(pX, pY)/p`,
integral with decaying coefficients, so convergent on all of `Oⁿ × Oⁿ` — into addition
(`ChabautyColeman.FormalGroupLaw.log_addHom`); `Λ(p·y) = f(evalT y (HL i))`.

Both halves descend a `K`-power-series identity to the `p`-scaled integral forms — via
`rescale`/`subst_comp_subst_apply`/`map_subst` and `f` injective — and then evaluate it
with `evalT_subst`: injectivity descends `Exp ∘ Λ = id` (`exp_comp_log`, through
`subst_descent`), additivity descends `Λ(F(X,Y)) = Λ(X) + Λ(Y)` (`log_subst_F`, through
`subst_scaledF_descent`). The scaled log is uniquely determined by its scaling relation
(`ChabautyColeman.FormalGroupLaw.scaled_log_unique`), so the two packages agree.

Blueprint node: `thm:log-iso`.
-/


open MvPowerSeries IsLocalRing Filter Topology ChabautyColeman.MvPSeries

namespace ChabautyColeman.FormalGroupLaw

section Helpers

variable {O : Type*} [CommRing O] {ι : Type*} {K : Type*} [CommRing K]
  {f : O →+* K} {p : ℕ}

theorem map_eq_rescale {H : MvPowerSeries ι O} {L : MvPowerSeries ι K}
    (hH : ∀ d, f (coeff d H) = f (p : O) ^ d.degree * coeff d L) :
    MvPowerSeries.map f H = rescale (fun _ ↦ (p : K)) L := by
  ext d
  rw [coeff_map, hH d, coeff_rescale, map_natCast]
  congr 1
  rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply]

theorem map_injective_of_injective (hf : Function.Injective f) :
    Function.Injective (MvPowerSeries.map (σ := ι) f) := fun φ ψ h ↦ by
  ext d; exact hf (by rw [← coeff_map, ← coeff_map, h])

theorem map_smul_natCast (n : ℕ) (h : MvPowerSeries ι O) :
    MvPowerSeries.map f ((n : O) • h) = (n : K) • MvPowerSeries.map f h := by
  rw [Nat.cast_smul_eq_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul K]

theorem rescale_const_eq_subst (c : K) (L : MvPowerSeries ι K) :
    rescale (fun _ ↦ c) L = subst (fun j ↦ c • X j) L := by
  rw [rescale_eq_subst]; rfl

end Helpers

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {K : Type*} [Field K] [CharZero K] {f : O →+* K} {p : ℕ}

omit [IsDomain O] [IsLocalRing O] [UniformSpace O] [Fact (IsAdic (maximalIdeal O))]
  [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [Fintype ι] [DecidableEq ι] [CharZero K] in
theorem subst_descent [Finite ι] (hf : Function.Injective f)
    {HL HE Hh : ι → MvPowerSeries ι O} {Lg : ι → MvPowerSeries ι K} {E : MvPowerSeries ι K} {i : ι}
    (hHL : ∀ j, MvPowerSeries.map f (HL j) = rescale (fun _ ↦ (p : K)) (Lg j))
    (hHE : MvPowerSeries.map f (HE i) = rescale (fun _ ↦ (p : K)) E)
    (hHh : ∀ j, (p : O) • Hh j = HL j) (hHh0 : ∀ j, constantCoeff (Hh j) = 0)
    (hLg : HasSubst Lg) (hcomp : subst Lg E = X i) :
    subst Hh (HE i) = (p : O) • X i := by
  letI := Fintype.ofFinite ι
  have hpX : HasSubst (fun j : ι ↦ (p : K) • (X j : MvPowerSeries ι K)) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by simp
  have hHhs : HasSubst Hh := hasSubst_of_constantCoeff_zero hHh0
  have hmHh : HasSubst (fun j ↦ MvPowerSeries.map f (Hh j)) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by rw [← coeff_zero_eq_constantCoeff_apply,
      coeff_map, coeff_zero_eq_constantCoeff_apply, hHh0, map_zero]
  apply map_injective_of_injective hf
  calc MvPowerSeries.map f (subst Hh (HE i))
      = subst (fun j ↦ MvPowerSeries.map f (Hh j)) (MvPowerSeries.map f (HE i)) :=
        map_subst hHhs (HE i)
    _ = subst (fun j ↦ MvPowerSeries.map f (Hh j)) (subst (fun j ↦ (p : K) • X j) E) := by
        rw [hHE, rescale_const_eq_subst]
    _ = subst (fun j ↦ (p : K) • MvPowerSeries.map f (Hh j)) E := by
        rw [subst_comp_subst_apply hpX hmHh]
        congr 1; funext j; rw [subst_smul hmHh, subst_X hmHh]
    _ = subst (fun j ↦ MvPowerSeries.map f (HL j)) E := by
        congr 1; funext j; rw [← map_smul_natCast, hHh]
    _ = subst (fun j ↦ subst (fun j ↦ (p : K) • X j) (Lg j)) E := by
        congr 1; funext j; rw [hHL, rescale_const_eq_subst]
    _ = subst (fun j ↦ (p : K) • X j) (subst Lg E) := (subst_comp_subst_apply hLg hpX E).symm
    _ = subst (fun j ↦ (p : K) • X j) (X i) := by rw [hcomp]
    _ = (p : K) • X i := by rw [subst_X hpX]
    _ = MvPowerSeries.map f ((p : O) • X i) := by rw [map_smul_natCast, MvPowerSeries.map_X]

omit [IsDomain O] [IsLocalRing O] [Fact (IsAdic (maximalIdeal O))]
  [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [Fintype ι] [DecidableEq ι] in
theorem decay_nsmul {h : MvPowerSeries ι O} (n : ℕ)
    (hh : Tendsto (fun d ↦ coeff d h) cofinite (𝓝 0)) :
    Tendsto (fun d ↦ coeff d (n • h)) cofinite (𝓝 0) := by
  simpa only [map_nsmul, smul_zero] using hh.const_smul n

omit [IsDomain O] [Fintype ι] [DecidableEq ι] in
theorem evalT_nsmul (z : ι → O) (n : ℕ) {h : MvPowerSeries ι O}
    (hh : Tendsto (fun d ↦ coeff d h) cofinite (𝓝 0)) :
    evalT z (n • h) = n • evalT z h := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, succ_nsmul, evalT_add z (decay_nsmul n hh) hh, ih]

omit [IsDomain O] [Fintype ι] [DecidableEq ι] in
theorem evalT_natCast_smul (z : ι → O) (n : ℕ) {h : MvPowerSeries ι O}
    (hh : Tendsto (fun d ↦ coeff d h) cofinite (𝓝 0)) :
    evalT z ((n : O) • h) = (n : O) • evalT z h := by
  rw [Nat.cast_smul_eq_nsmul, evalT_nsmul z n hh, Nat.cast_smul_eq_nsmul]

omit [IsDomain O] [IsLocalRing O] [Fact (IsAdic (maximalIdeal O))]
  [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [Fintype ι] [DecidableEq ι] in
theorem decay_X (i : ι) :
    Tendsto (fun d ↦ coeff d (X i : MvPowerSeries ι O)) cofinite (𝓝 0) := by
  classical
  refine tendsto_nhds_of_eventually_eq ?_
  rw [eventually_cofinite]
  refine (Set.finite_singleton (Finsupp.single i 1)).subset fun d hd ↦ ?_
  simp only [Set.mem_setOf_eq] at hd
  simp only [Set.mem_singleton_iff]
  by_contra hne; exact hd (by rw [coeff_X, if_neg hne])

omit [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [Fintype ι] [DecidableEq ι] in
theorem tendsto_cancel_smul {g : (ι →₀ ℕ) → O}
    (hpm : maximalIdeal O = Ideal.span {(p : O)}) (hp0 : (p : O) ≠ 0)
    (hg : Tendsto (fun d ↦ (p : O) * g d) cofinite (𝓝 0)) :
    Tendsto g cofinite (𝓝 0) := by
  rw [(Fact.out : IsAdic (maximalIdeal O)).hasBasis_nhds_zero.tendsto_right_iff] at hg ⊢
  intro k _
  filter_upwards [hg (k + 1) trivial] with d hd
  rw [hpm, Ideal.span_singleton_pow, SetLike.mem_coe, Ideal.mem_span_singleton] at hd ⊢
  obtain ⟨w, hw⟩ := hd
  exact ⟨w, mul_left_cancel₀ hp0 (by rw [hw, pow_succ]; ring)⟩

open scoped Classical in
/-- **Injectivity of the formal logarithm** on `(pO)ⁿ` (`p` odd, unramified `𝔪 = pO`).
The `p`-scaled log `HL` (with `f(coeff_d HL) = f(p)^{deg d} · coeff_d Λ`) has injective
evaluation map `y ↦ (evalT y (HL i))ᵢ`; hence `Λ` is injective on `(pO)ⁿ`. -/
theorem log_injective (hp : p.Prime) (hp2 : p ≠ 2)
    (hpm : maximalIdeal O = Ideal.span {(p : O)}) (hf : Function.Injective f)
    (Φ : FormalGroupLaw O ι) :
    ∃ HL : ι → MvPowerSeries ι O,
      (∀ i d, f (coeff d (HL i)) = f (p : O) ^ d.degree * coeff d ((Φ.map f).log i)) ∧
      Function.Injective fun y : ι → O ↦ (fun i ↦ evalT y (HL i)) := by
  have hpmem : (p : O) ∈ maximalIdeal O := hpm ▸ Ideal.mem_span_singleton_self _
  have hfp : f (p : O) ≠ 0 := by rw [map_natCast]; exact_mod_cast hp.pos.ne'
  have hp0 : (p : O) ≠ 0 := fun h ↦ hfp (by rw [h, map_zero])
  choose HL hHL_scale hHL_decay using fun i ↦ Φ.exists_integral_scaled_log hp hpmem f hfp i
  choose HE hHE_scale hHE_decay using fun i ↦ Φ.exp_converges hp hp2 hpmem hfp i
  refine ⟨HL, hHL_scale, ?_⟩
  -- each coefficient of `HL` is divisible by `p`
  have hdvd : ∀ i d, (p : O) ∣ coeff d (HL i) := by
    intro i d
    rw [← Ideal.mem_span_singleton, ← hpm]
    rcases eq_or_ne d 0 with rfl | hd0
    · have : coeff 0 (HL i) = 0 := hf (by
        rw [map_zero, hHL_scale i 0, map_zero Finsupp.degree, pow_zero, one_mul,
          coeff_zero_eq_constantCoeff_apply, (Φ.map f).constantCoeff_log])
      rw [this]; exact zero_mem _
    · obtain ⟨c, hc⟩ := Φ.coeff_log_map_scale hp hpmem f hfp i d
      have heq : coeff d (HL i) = (p : O) ^ (d.degree - padicValNat p d.degree) * c :=
        hf (by rw [hHL_scale i d, hc, map_mul, map_pow])
      have hpos : 0 < d.degree :=
        Nat.pos_of_ne_zero fun h ↦ hd0 ((Finsupp.degree_eq_zero_iff d).mp h)
      have hvp : 0 < d.degree - padicValNat p d.degree := by
        have h1 := ChabautyColeman.pred_mul_padicValNat_le hp (Nat.one_le_iff_ne_zero.mpr hpos.ne')
        have h2 : padicValNat p d.degree ≤ (p - 1) * padicValNat p d.degree :=
          Nat.le_mul_of_pos_left _ (by have := hp.two_le; lia)
        lia
      rw [heq]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hpmem _ hvp)
  choose c hc using fun i d ↦ hdvd i d
  set Hh : ι → MvPowerSeries ι O := fun i ↦ (c i : MvPowerSeries ι O) with hHhdef
  have hHh : ∀ i, (p : O) • Hh i = HL i := fun i ↦ by
    ext d; rw [hHhdef]; simp only [MvPowerSeries.coeff_smul]; exact (hc i d).symm
  have hHL0 : ∀ i, constantCoeff (HL i) = 0 := fun i ↦ hf (by
    rw [map_zero, ← coeff_zero_eq_constantCoeff_apply, hHL_scale i 0, map_zero Finsupp.degree,
      pow_zero, one_mul, coeff_zero_eq_constantCoeff_apply, (Φ.map f).constantCoeff_log])
  have hHh0 : ∀ i, constantCoeff (Hh i) = 0 := fun i ↦ by
    have h2 := congrArg (coeff 0) (hHh i)
    rw [MvPowerSeries.coeff_smul, coeff_zero_eq_constantCoeff_apply,
      coeff_zero_eq_constantCoeff_apply, hHL0 i] at h2
    exact (mul_eq_zero.mp h2).resolve_left hp0
  have hHh_decay : ∀ s, Tendsto (fun d ↦ coeff d (Hh s)) cofinite (𝓝 0) := fun s ↦ by
    refine tendsto_cancel_smul hpm hp0 ?_
    have heq : (fun d ↦ (p : O) * coeff d (Hh s)) = fun d ↦ coeff d (HL s) := by
      funext d; simp only [← hHh s, MvPowerSeries.coeff_smul]
    rw [heq]; exact hHL_decay s
  have hdescent : ∀ i, subst Hh (HE i) = (p : O) • X i := fun i ↦
    subst_descent hf (fun j ↦ map_eq_rescale (hHL_scale j)) (map_eq_rescale (hHE_scale i))
      hHh hHh0 (hasSubst_of_constantCoeff_zero fun s ↦ (Φ.map f).constantCoeff_log s)
      ((Φ.map f).exp_comp_log i)
  have hkey : ∀ (y : ι → O) (i), evalT (fun s ↦ evalT y (Hh s)) (HE i) = (p : O) • y i :=
    fun y i ↦ by
      rw [← evalT_subst y (hasSubst_of_constantCoeff_zero hHh0) (hHE_decay i) hHh_decay,
        hdescent i, evalT_natCast_smul y p (decay_X i), evalT_X]
  intro y y' hyy
  have hHh_eq : ∀ i, evalT y (Hh i) = evalT y' (Hh i) := fun i ↦ by
    have h := congrFun hyy i
    simp only [] at h
    rw [← hHh i, evalT_natCast_smul y p (hHh_decay i),
      evalT_natCast_smul y' p (hHh_decay i), smul_eq_mul, smul_eq_mul] at h
    exact mul_left_cancel₀ hp0 h
  funext i
  have hval : (p : O) • y i = (p : O) • y' i := by
    rw [← hkey y i, ← hkey y' i, funext hHh_eq]
  rw [smul_eq_mul, smul_eq_mul] at hval
  exact mul_left_cancel₀ hp0 hval

/-! ### The p-scaled formal group law -/

section ScaledF

variable {O : Type*} [CommRing O] {ι : Type*} (Φ : FormalGroupLaw O ι) (p : ℕ)

/-- The `p`-scaled formal group law: `F(pX, pY)/p`, integral because `F` has no constant
term. Its coefficients decay `p`-adically, so it evaluates on all of `Oⁿ × Oⁿ`. -/
noncomputable def scaledF (j : ι) : MvPowerSeries (ι ⊕ ι) O :=
  fun d ↦ (p : O) ^ (d.degree - 1) * coeff d (Φ.F j)

@[simp]
theorem coeff_scaledF (j : ι) (d : ι ⊕ ι →₀ ℕ) :
    coeff d (Φ.scaledF p j) = (p : O) ^ (d.degree - 1) * coeff d (Φ.F j) := rfl

theorem constantCoeff_scaledF (j : ι) : constantCoeff (Φ.scaledF p j) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_scaledF, map_zero Finsupp.degree,
    coeff_zero_eq_constantCoeff_apply, Φ.zero_constantCoeff, mul_zero]

variable [Finite ι] in
theorem hasSubst_scaledF : MvPowerSeries.HasSubst (Φ.scaledF p) :=
  hasSubst_of_constantCoeff_zero fun j ↦ Φ.constantCoeff_scaledF p j

end ScaledF

section ScaledFTop

variable {O : Type*} [CommRing O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] {ι : Type*} [Finite ι]
  (Φ : FormalGroupLaw O ι) {p : ℕ}

/-- The coefficients of the scaled group law tend to zero. -/
theorem decay_scaledF (hpm : maximalIdeal O = Ideal.span {(p : O)}) (j : ι) :
    Tendsto (fun d ↦ coeff d (Φ.scaledF p j)) cofinite (𝓝 0) := by
  have hpmem : (p : O) ∈ maximalIdeal O := hpm ▸ Ideal.mem_span_singleton_self _
  refine MvPSeries.tendsto_coeff_zero_of_mem_pow
    (fun d ↦ Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hpmem _)) ?_
  exact (tendsto_sub_atTop_nat 1).comp Finsupp.tendsto_degree_cofinite

end ScaledFTop

section Descent

variable {O : Type*} [CommRing O] {ι : Type*} [Finite ι] {K : Type*} [Field K]
  {f : O →+* K} {p : ℕ} (Φ : FormalGroupLaw O ι)

private lemma subst_smulX_subst_X_comp (e : ι → ι ⊕ ι) (L : MvPowerSeries ι K) :
    MvPowerSeries.subst (fun t : ι ⊕ ι ↦ (p : K) • (X t : MvPowerSeries (ι ⊕ ι) K))
        (MvPowerSeries.subst (fun s : ι ↦ (X (e s) : MvPowerSeries (ι ⊕ ι) K)) L)
      = MvPowerSeries.subst
          (fun s : ι ↦ (p : K) • (X (e s) : MvPowerSeries (ι ⊕ ι) K)) L := by
  have he : HasSubst fun s : ι ↦ (X (e s) : MvPowerSeries (ι ⊕ ι) K) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by simp
  have hpX2 : HasSubst fun t : ι ⊕ ι ↦ (p : K) • (X t : MvPowerSeries (ι ⊕ ι) K) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by simp
  rw [subst_comp_subst_apply he hpX2]
  congr 1
  funext s
  rw [subst_X hpX2]

private lemma map_subst_X_comp (e : ι → ι ⊕ ι) {H : MvPowerSeries ι O} {L : MvPowerSeries ι K}
    (hH : MvPowerSeries.map f H = rescale (fun _ ↦ (p : K)) L) :
    MvPowerSeries.map f
        (MvPowerSeries.subst (fun s : ι ↦ (X (e s) : MvPowerSeries (ι ⊕ ι) O)) H)
      = MvPowerSeries.subst
          (fun s : ι ↦ (p : K) • (X (e s) : MvPowerSeries (ι ⊕ ι) K)) L := by
  have heO : HasSubst fun s : ι ↦ (X (e s) : MvPowerSeries (ι ⊕ ι) O) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by simp
  have heK : HasSubst fun s : ι ↦ (X (e s) : MvPowerSeries (ι ⊕ ι) K) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by simp
  have hpX : HasSubst fun j : ι ↦ (p : K) • (X j : MvPowerSeries ι K) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by simp
  have hXe : (fun s : ι ↦ MvPowerSeries.map f (X (e s) : MvPowerSeries (ι ⊕ ι) O))
      = fun s : ι ↦ (X (e s) : MvPowerSeries (ι ⊕ ι) K) :=
    funext fun s ↦ MvPowerSeries.map_X f (e s)
  rw [map_subst heO, hXe, hH, rescale_const_eq_subst, subst_comp_subst_apply hpX heK]
  congr 1
  funext s
  rw [subst_smul heK, subst_X heK]

/-- The `p`-scaled formal group law is the `p`-rescaling of `F`, over the fraction
field. -/
theorem map_scaledF_smul (j : ι) :
    (p : K) • MvPowerSeries.map f (Φ.scaledF p j)
      = rescale (fun _ ↦ (p : K)) ((Φ.map f).F j) := by
  ext d
  rw [MvPowerSeries.coeff_smul, coeff_map, coeff_scaledF, coeff_rescale, map_mul, map_pow,
    map_natCast, Finsupp.prod, Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply]
  have hF : (Φ.map f).F j = MvPowerSeries.map f (Φ.F j) := rfl
  rcases Nat.eq_zero_or_pos d.degree with h0 | hpos
  · obtain rfl : d = 0 := (Finsupp.degree_eq_zero_iff d).mp h0
    simp [coeff_zero_eq_constantCoeff_apply, Φ.zero_constantCoeff j]
  · rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hpos, hF, coeff_map]

end Descent

section DescentLog

variable {O : Type*} [CommRing O] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {K : Type*} [Field K] {f : O →+* K} {p : ℕ} (Φ : FormalGroupLaw O ι)

/-- The `p`-scaled logarithms over `O` are uniquely determined by their scaling relation
(the base-change map `f` is injective), so the packages produced by
`ChabautyColeman.FormalGroupLaw.log_injective` and
`ChabautyColeman.FormalGroupLaw.log_addHom` contain the same series. -/
theorem scaled_log_unique (hf : Function.Injective f) {HL HL' : ι → MvPowerSeries ι O}
    (h : ∀ i d, f (coeff d (HL i)) = f (p : O) ^ d.degree * coeff d ((Φ.map f).log i))
    (h' : ∀ i d, f (coeff d (HL' i)) = f (p : O) ^ d.degree * coeff d ((Φ.map f).log i)) :
    HL = HL' :=
  funext fun i ↦ MvPowerSeries.ext fun d ↦ hf ((h i d).trans (h' i d).symm)

variable [CharZero K]

/-- The descended additivity identity: the `p`-scaled logarithm is additive for the
`p`-scaled formal group law, over `O`. -/
theorem subst_scaledF_descent (hf : Function.Injective f)
    {HL : ι → MvPowerSeries ι O}
    (hHL : ∀ j, MvPowerSeries.map f (HL j)
      = rescale (fun _ ↦ (p : K)) ((Φ.map f).log j)) (i : ι) :
    MvPowerSeries.subst (Φ.scaledF p) (HL i)
      = MvPowerSeries.subst
          (fun s : ι ↦ (X (Sum.inl s) : MvPowerSeries (ι ⊕ ι) O)) (HL i)
        + MvPowerSeries.subst
            (fun s : ι ↦ (X (Sum.inr s) : MvPowerSeries (ι ⊕ ι) O)) (HL i) := by
  have hpX : HasSubst (fun j : ι ↦ (p : K) • (X j : MvPowerSeries ι K)) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by simp
  have hpX2 : HasSubst (fun t : ι ⊕ ι ↦ (p : K) • (X t : MvPowerSeries (ι ⊕ ι) K)) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by simp
  have hmsF : HasSubst fun j ↦ MvPowerSeries.map f (Φ.scaledF p j) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
        Φ.constantCoeff_scaledF, map_zero]
  apply map_injective_of_injective hf
  rw [map_add, map_subst_X_comp Sum.inl (hHL i), map_subst_X_comp Sum.inr (hHL i)]
  calc MvPowerSeries.map f (MvPowerSeries.subst (Φ.scaledF p) (HL i))
      = MvPowerSeries.subst (fun j ↦ MvPowerSeries.map f (Φ.scaledF p j))
          (MvPowerSeries.map f (HL i)) := map_subst (Φ.hasSubst_scaledF p) (HL i)
    _ = MvPowerSeries.subst (fun j ↦ MvPowerSeries.map f (Φ.scaledF p j))
          (MvPowerSeries.subst (fun j ↦ (p : K) • X j) ((Φ.map f).log i)) := by
        rw [hHL, rescale_const_eq_subst]
    _ = MvPowerSeries.subst (fun j ↦ (p : K) • MvPowerSeries.map f (Φ.scaledF p j))
          ((Φ.map f).log i) := by
        rw [subst_comp_subst_apply hpX hmsF]
        congr 1
        funext j
        rw [subst_smul hmsF, subst_X hmsF]
    _ = MvPowerSeries.subst
          (fun j ↦ MvPowerSeries.subst (fun t : ι ⊕ ι ↦ (p : K) • X t) ((Φ.map f).F j))
          ((Φ.map f).log i) := by
        congr 1
        funext j
        rw [Φ.map_scaledF_smul j, rescale_const_eq_subst]
    _ = MvPowerSeries.subst (fun t : ι ⊕ ι ↦ (p : K) • X t)
          (MvPowerSeries.subst (fun j ↦ (Φ.map f).F j) ((Φ.map f).log i)) :=
        (subst_comp_subst_apply (Φ.map f).hasSubst_F hpX2 _).symm
    _ = MvPowerSeries.subst
          (fun s : ι ↦ (p : K) • (X (Sum.inl s) : MvPowerSeries (ι ⊕ ι) K))
          ((Φ.map f).log i)
        + MvPowerSeries.subst
            (fun s : ι ↦ (p : K) • (X (Sum.inr s) : MvPowerSeries (ι ⊕ ι) K))
            ((Φ.map f).log i) := by
        rw [(Φ.map f).log_subst_F i, ← coe_substAlgHom hpX2, map_add, coe_substAlgHom hpX2,
          subst_smulX_subst_X_comp Sum.inl, subst_smulX_subst_X_comp Sum.inr]

end DescentLog

/-! ### The homomorphism property of the logarithm -/

section AddHom

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {K : Type*} [Field K] [CharZero K] {f : O →+* K} {p : ℕ}

open MvPSeries in
omit [IsDomain O] in
/-- **The formal logarithm is a homomorphism** on `(pO)ⁿ` (`p` odd, unramified `𝔪 = pO`):
the `p`-scaled log `HL` turns the (everywhere-convergent) `p`-scaled formal group sum
into addition. Together with `ChabautyColeman.FormalGroupLaw.log_injective` this makes
`Λ` an injective group homomorphism on `(pO)ⁿ`. -/
theorem log_addHom (hp : p.Prime)
    (hpm : maximalIdeal O = Ideal.span {(p : O)}) (hf : Function.Injective f)
    (Φ : FormalGroupLaw O ι) :
    ∃ HL : ι → MvPowerSeries ι O,
      (∀ i d, f (coeff d (HL i)) = f (p : O) ^ d.degree * coeff d ((Φ.map f).log i)) ∧
      ∀ (y z : ι → O) (i : ι),
        evalT (fun j ↦ evalT (Sum.elim y z) (Φ.scaledF p j)) (HL i)
          = evalT y (HL i) + evalT z (HL i) := by
  have hpmem : (p : O) ∈ maximalIdeal O := hpm ▸ Ideal.mem_span_singleton_self _
  have hfp : f (p : O) ≠ 0 := by rw [map_natCast]; exact_mod_cast hp.pos.ne'
  choose HL hHL_scale hHL_decay using fun i ↦ Φ.exists_integral_scaled_log hp hpmem f hfp i
  refine ⟨HL, hHL_scale, fun y z i ↦ ?_⟩
  have hTCl : TendstoCofinite (Sum.inl : ι → ι ⊕ ι) :=
    tendstoCofinite_of_injective Sum.inl_injective
  have hTCr : TendstoCofinite (Sum.inr : ι → ι ⊕ ι) :=
    tendstoCofinite_of_injective Sum.inr_injective
  have hdXl : Tendsto (fun d ↦ coeff d (MvPowerSeries.subst
      (fun s : ι ↦ (X (Sum.inl s) : MvPowerSeries (ι ⊕ ι) O)) (HL i))) cofinite (𝓝 0) := by
    have h1 : (fun s : ι ↦ (X (Sum.inl s) : MvPowerSeries (ι ⊕ ι) O))
        = X ∘ Sum.inl := rfl
    rw [h1, ← rename_eq_subst]
    exact decay_rename Sum.inl_injective (hHL_decay i)
  have hdXr : Tendsto (fun d ↦ coeff d (MvPowerSeries.subst
      (fun s : ι ↦ (X (Sum.inr s) : MvPowerSeries (ι ⊕ ι) O)) (HL i))) cofinite (𝓝 0) := by
    have h1 : (fun s : ι ↦ (X (Sum.inr s) : MvPowerSeries (ι ⊕ ι) O))
        = X ∘ Sum.inr := rfl
    rw [h1, ← rename_eq_subst]
    exact decay_rename Sum.inr_injective (hHL_decay i)
  rw [← evalT_subst (Sum.elim y z) (Φ.hasSubst_scaledF p) (hHL_decay i)
      (Φ.decay_scaledF hpm),
    Φ.subst_scaledF_descent hf (fun j ↦ map_eq_rescale (hHL_scale j)) i,
    evalT_add _ hdXl hdXr,
    evalT_subst (Sum.elim y z) hasSubst_Xemb (hHL_decay i) fun s ↦ decay_X _,
    evalT_subst (Sum.elim y z) hasSubst_Yemb (hHL_decay i) fun s ↦ decay_X _]
  have hyl : (fun s ↦ MvPSeries.evalT (Sum.elim y z)
      (X (Sum.inl s) : MvPowerSeries (ι ⊕ ι) O)) = y :=
    funext fun s ↦ by rw [evalT_X, Sum.elim_inl]
  have hzr : (fun s ↦ MvPSeries.evalT (Sum.elim y z)
      (X (Sum.inr s) : MvPowerSeries (ι ⊕ ι) O)) = z :=
    funext fun s ↦ by rw [evalT_X, Sum.elim_inr]
  rw [hyl, hzr]

end AddHom

/-! ### The canonical scaled logarithm -/

section ScaledLogDef

variable {O : Type*} [CommRing O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {K : Type*} [Field K] {f : O →+* K} {p : ℕ} (Φ : FormalGroupLaw O ι)

/-- The `p`-scaled logarithm of a formal group law, as a power series over `O`: the
integral form of `Λ(pU)`, so that `y ↦ evalT y (scaledLog i)` represents `Λ(p·y)`. -/
noncomputable def scaledLog (hp : p.Prime) (hpmem : (p : O) ∈ maximalIdeal O)
    (f : O →+* K) (hfp : f (p : O) ≠ 0) (i : ι) : MvPowerSeries ι O :=
  (Φ.exists_integral_scaled_log hp hpmem f hfp i).choose

theorem coeff_scaledLog_map (hp : p.Prime) (hpmem : (p : O) ∈ maximalIdeal O)
    (hfp : f (p : O) ≠ 0) (i : ι) (d : ι →₀ ℕ) :
    f (coeff d (Φ.scaledLog hp hpmem f hfp i))
      = f (p : O) ^ d.degree * coeff d ((Φ.map f).log i) :=
  (Φ.exists_integral_scaled_log hp hpmem f hfp i).choose_spec.1 d

theorem decay_scaledLog (hp : p.Prime) (hpmem : (p : O) ∈ maximalIdeal O)
    (hfp : f (p : O) ≠ 0) (i : ι) :
    Tendsto (fun d ↦ coeff d (Φ.scaledLog hp hpmem f hfp i)) cofinite (𝓝 0) :=
  (Φ.exists_integral_scaled_log hp hpmem f hfp i).choose_spec.2

end ScaledLogDef

section ScaledLogEval

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {K : Type*} [Field K] [CharZero K] {f : O →+* K} {p : ℕ} (Φ : FormalGroupLaw O ι)

/-- **Injectivity of the formal logarithm**, for the canonical scaled log. -/
theorem evalT_scaledLog_injective (hp : p.Prime) (hp2 : p ≠ 2)
    (hpm : maximalIdeal O = Ideal.span {(p : O)}) (hf : Function.Injective f)
    (hpmem : (p : O) ∈ maximalIdeal O) (hfp : f (p : O) ≠ 0) :
    Function.Injective
      fun y : ι → O ↦ (fun i ↦ evalT y (Φ.scaledLog hp hpmem f hfp i)) := by
  obtain ⟨HL, hsc, hinj⟩ := Φ.log_injective hp hp2 hpm hf
  have hEq : Φ.scaledLog hp hpmem f hfp = HL :=
    Φ.scaled_log_unique hf (fun i d ↦ Φ.coeff_scaledLog_map hp hpmem hfp i d) hsc
  rw [hEq]
  exact hinj

omit [IsDomain O] in
/-- **Additivity of the formal logarithm**, for the canonical scaled log. -/
theorem evalT_scaledLog_add (hp : p.Prime)
    (hpm : maximalIdeal O = Ideal.span {(p : O)}) (hf : Function.Injective f)
    (hpmem : (p : O) ∈ maximalIdeal O) (hfp : f (p : O) ≠ 0) (y z : ι → O) (i : ι) :
    evalT (fun j ↦ evalT (Sum.elim y z) (Φ.scaledF p j))
        (Φ.scaledLog hp hpmem f hfp i)
      = evalT y (Φ.scaledLog hp hpmem f hfp i)
        + evalT z (Φ.scaledLog hp hpmem f hfp i) := by
  obtain ⟨HL, hsc, hadd⟩ := Φ.log_addHom hp hpm hf
  have hEq : Φ.scaledLog hp hpmem f hfp = HL :=
    Φ.scaled_log_unique hf (fun i d ↦ Φ.coeff_scaledLog_map hp hpmem hfp i d) hsc
  rw [hEq]
  exact hadd y z i

/-! ### Evaluation of the scaled group law at scaled points -/

omit [IsDomain O] [Fintype ι] [DecidableEq ι] in
/-- Evaluating the `p`-scaled group law and rescaling recovers the group law at the
`p`-scaled point: `p · (F(py, pz)/p) = F(py, pz)` at the level of `evalT`. -/
theorem natCast_mul_evalT_scaledF [Finite ι] {p : ℕ}
    (hpm : maximalIdeal O = Ideal.span {(p : O)}) (y : ι ⊕ ι → O) (j : ι) :
    (p : O) * evalT y (Φ.scaledF p j) = evalT (fun s ↦ (p : O) * y s) (Φ.F j) := by
  letI := Fintype.ofFinite ι
  rw [show (p : O) * evalT y (Φ.scaledF p j) = evalT y ((p : O) • Φ.scaledF p j) by
    rw [evalT_natCast_smul y p (Φ.decay_scaledF hpm j), smul_eq_mul]]
  rw [evalT_eq_tsum, evalT_eq_tsum]
  refine tsum_congr fun d ↦ ?_
  rw [MvPowerSeries.coeff_smul, coeff_scaledF]
  rcases Nat.eq_zero_or_pos d.degree with h0 | hpos
  · obtain rfl : d = 0 := (Finsupp.degree_eq_zero_iff d).mp h0
    simp [coeff_zero_eq_constantCoeff_apply, Φ.zero_constantCoeff j]
  · have hprod : (d.prod fun s k ↦ ((p : O) * y s) ^ k)
        = (p : O) ^ d.degree * d.prod fun s k ↦ y s ^ k := by
      rw [Finsupp.prod, Finsupp.prod,
        show (∏ s ∈ d.support, ((p : O) * y s) ^ d s)
            = ∏ s ∈ d.support, (p : O) ^ d s * y s ^ d s from
          Finset.prod_congr rfl fun s _ ↦ mul_pow _ _ _,
        Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply]
    have hpp : (p : O) * (p : O) ^ (d.degree - 1) = (p : O) ^ d.degree := by
      rw [← pow_succ', Nat.sub_add_cancel hpos]
    calc (p : O) * ((p : O) ^ (d.degree - 1) * coeff d (Φ.F j))
          * (d.prod fun s k ↦ y s ^ k)
        = (p : O) * (p : O) ^ (d.degree - 1) * coeff d (Φ.F j)
          * (d.prod fun s k ↦ y s ^ k) := by ring
      _ = coeff d (Φ.F j) * ((p : O) ^ d.degree * (d.prod fun s k ↦ y s ^ k)) := by
          rw [hpp]; ring
      _ = coeff d (Φ.F j) * (d.prod fun s k ↦ ((p : O) * y s) ^ k) := by rw [hprod]

end ScaledLogEval

end ChabautyColeman.FormalGroupLaw

end
