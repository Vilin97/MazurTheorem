/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
Source: MichaelStollBayreuth/EllipticCurves at commit 3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f.
-/
module

public import EllipticCurves.Mathlib.Chabauty.LogIso
public import EllipticCurves.Mathlib.AdicCompletionExtension

@[expose] public section

/-!
# The scaled formal logarithm of a formal group law

This file generalizes the `p`-scaling machinery of the vendored kit file
`EllipticCurves.Mathlib.Chabauty.LogIso` from the natural number `p` to an arbitrary ring
element `c` (for the application: a power `π^e` of a uniformizer of `𝒪_v`, where `e` is
the absolute ramification index).  The `c`-scaled formal group law
`ChabautyColeman.FormalGroupLaw.scaledFC` is `F(cX, cY)/c`; the additivity identity of the
formal logarithm descends along an injective base-change map `f : O →+* K` to the
`c`-scaled integral logarithm (`ChabautyColeman.FormalGroupLaw.subst_scaledFC_descent`).

The second part specializes to the valuation ring `𝒪_v` of the completion of a global
field at a finite place: for `c = π^e` the scaled logarithm has integral coefficients
(`WeierstrassCurve` is not needed here; this works for any formal group law over `𝒪_v`),
with linear coefficient `1`, so it has an integral compositional inverse
(`ChabautyColeman.invSubst`), and evaluation at points of the maximal ideal produces a
group isomorphism onto `(𝔪, +)`.
-/

open MvPowerSeries IsLocalRing

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

/-- The topology on `𝒪_v` is the `𝔪`-adic topology; this activates the vendored kit. -/
instance factIsAdic_adicCompletionIntegers :
    Fact (IsAdic (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))) :=
  ⟨v.isAdic_maximalIdeal_adicCompletionIntegers⟩

end IsDedekindDomain.HeightOneSpectrum

namespace ChabautyColeman

section Helpers

variable {O : Type*} [CommRing O] {ι : Type*} {K : Type*} [CommRing K] {f : O →+* K} {c : O}

/-- General-scale version of `ChabautyColeman.map_eq_rescale`: scaling by an arbitrary
ring element `c` instead of a natural number `p`. -/
theorem map_eq_rescale_of_forall_coeff {H : MvPowerSeries ι O} {L : MvPowerSeries ι K}
    (hH : ∀ d, f (coeff d H) = f c ^ d.degree * coeff d L) :
    MvPowerSeries.map f H = rescale (fun _ ↦ f c) L := by
  ext d
  rw [coeff_map, hH d, coeff_rescale]
  congr 1
  rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply]

end Helpers

namespace FormalGroupLaw

/-! ### The `c`-scaled formal group law -/

section ScaledFC

variable {O : Type*} [CommRing O] {ι : Type*} (Φ : FormalGroupLaw O ι) (c : O)

/-- The `c`-scaled formal group law: `F(cX, cY)/c`, integral because `F` has no constant
term. -/
noncomputable def scaledFC (j : ι) : MvPowerSeries (ι ⊕ ι) O :=
  fun d ↦ c ^ (d.degree - 1) * coeff d (Φ.F j)

@[simp]
theorem coeff_scaledFC (j : ι) (d : ι ⊕ ι →₀ ℕ) :
    coeff d (Φ.scaledFC c j) = c ^ (d.degree - 1) * coeff d (Φ.F j) := rfl

theorem constantCoeff_scaledFC (j : ι) : constantCoeff (Φ.scaledFC c j) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_scaledFC, map_zero Finsupp.degree,
    coeff_zero_eq_constantCoeff_apply, Φ.zero_constantCoeff, mul_zero]

variable [Finite ι] in
theorem hasSubst_scaledFC : MvPowerSeries.HasSubst (Φ.scaledFC c) :=
  hasSubst_of_constantCoeff_zero fun j ↦ Φ.constantCoeff_scaledFC c j

end ScaledFC

/-! ### Descent of the logarithm additivity to the `c`-scaled level -/

section Descent

variable {O : Type*} [CommRing O] {ι : Type*} [Finite ι] {K : Type*} [Field K]
  {f : O →+* K} {c : O} (Φ : FormalGroupLaw O ι)

private lemma subst_smulX_subst_X_comp (e : ι → ι ⊕ ι) (L : MvPowerSeries ι K) :
    MvPowerSeries.subst (fun t : ι ⊕ ι ↦ f c • (X t : MvPowerSeries (ι ⊕ ι) K))
        (MvPowerSeries.subst (fun s : ι ↦ (X (e s) : MvPowerSeries (ι ⊕ ι) K)) L)
      = MvPowerSeries.subst
          (fun s : ι ↦ f c • (X (e s) : MvPowerSeries (ι ⊕ ι) K)) L := by
  have he : HasSubst fun s : ι ↦ (X (e s) : MvPowerSeries (ι ⊕ ι) K) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by simp
  have hcX2 : HasSubst fun t : ι ⊕ ι ↦ f c • (X t : MvPowerSeries (ι ⊕ ι) K) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by simp
  rw [subst_comp_subst_apply he hcX2]
  congr 1
  funext s
  rw [subst_X hcX2]

private lemma map_subst_X_comp (e : ι → ι ⊕ ι) {H : MvPowerSeries ι O} {L : MvPowerSeries ι K}
    (hH : MvPowerSeries.map f H = rescale (fun _ ↦ f c) L) :
    MvPowerSeries.map f
        (MvPowerSeries.subst (fun s : ι ↦ (X (e s) : MvPowerSeries (ι ⊕ ι) O)) H)
      = MvPowerSeries.subst
          (fun s : ι ↦ f c • (X (e s) : MvPowerSeries (ι ⊕ ι) K)) L := by
  have heO : HasSubst fun s : ι ↦ (X (e s) : MvPowerSeries (ι ⊕ ι) O) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by simp
  have heK : HasSubst fun s : ι ↦ (X (e s) : MvPowerSeries (ι ⊕ ι) K) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by simp
  have hcX : HasSubst fun j : ι ↦ f c • (X j : MvPowerSeries ι K) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by simp
  have hXe : (fun s : ι ↦ MvPowerSeries.map f (X (e s) : MvPowerSeries (ι ⊕ ι) O))
      = fun s : ι ↦ (X (e s) : MvPowerSeries (ι ⊕ ι) K) :=
    funext fun s ↦ MvPowerSeries.map_X f (e s)
  rw [map_subst heO, hXe, hH, rescale_const_eq_subst, subst_comp_subst_apply hcX heK]
  congr 1
  funext s
  rw [subst_smul heK, subst_X heK]

/-- The `c`-scaled formal group law is the `c`-rescaling of `F`, over the fraction
field. -/
theorem map_scaledFC_smul (j : ι) :
    f c • MvPowerSeries.map f (Φ.scaledFC c j)
      = rescale (fun _ ↦ f c) ((Φ.map f).F j) := by
  ext d
  rw [MvPowerSeries.coeff_smul, coeff_map, coeff_scaledFC, coeff_rescale, map_mul, map_pow,
    Finsupp.prod, Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply]
  have hF : (Φ.map f).F j = MvPowerSeries.map f (Φ.F j) := rfl
  rcases Nat.eq_zero_or_pos d.degree with h0 | hpos
  · obtain rfl : d = 0 := (Finsupp.degree_eq_zero_iff d).mp h0
    simp [coeff_zero_eq_constantCoeff_apply, Φ.zero_constantCoeff j]
  · rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hpos, hF, coeff_map]

variable [Fintype ι] [DecidableEq ι] [CharZero K]

/-- The descended additivity identity: the `c`-scaled logarithm is additive for the
`c`-scaled formal group law, over `O`. -/
theorem subst_scaledFC_descent (hf : Function.Injective f)
    {HL : ι → MvPowerSeries ι O}
    (hHL : ∀ j, MvPowerSeries.map f (HL j)
      = rescale (fun _ ↦ f c) ((Φ.map f).log j)) (i : ι) :
    MvPowerSeries.subst (Φ.scaledFC c) (HL i)
      = MvPowerSeries.subst
          (fun s : ι ↦ (X (Sum.inl s) : MvPowerSeries (ι ⊕ ι) O)) (HL i)
        + MvPowerSeries.subst
            (fun s : ι ↦ (X (Sum.inr s) : MvPowerSeries (ι ⊕ ι) O)) (HL i) := by
  have hcX : HasSubst (fun j : ι ↦ f c • (X j : MvPowerSeries ι K)) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by simp
  have hcX2 : HasSubst (fun t : ι ⊕ ι ↦ f c • (X t : MvPowerSeries (ι ⊕ ι) K)) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by simp
  have hmsF : HasSubst fun j ↦ MvPowerSeries.map f (Φ.scaledFC c j) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
        Φ.constantCoeff_scaledFC, map_zero]
  apply map_injective_of_injective hf
  rw [map_add, map_subst_X_comp Sum.inl (hHL i), map_subst_X_comp Sum.inr (hHL i)]
  calc MvPowerSeries.map f (MvPowerSeries.subst (Φ.scaledFC c) (HL i))
      = MvPowerSeries.subst (fun j ↦ MvPowerSeries.map f (Φ.scaledFC c j))
          (MvPowerSeries.map f (HL i)) := map_subst (Φ.hasSubst_scaledFC c) (HL i)
    _ = MvPowerSeries.subst (fun j ↦ MvPowerSeries.map f (Φ.scaledFC c j))
          (MvPowerSeries.subst (fun j ↦ f c • X j) ((Φ.map f).log i)) := by
        rw [hHL, rescale_const_eq_subst]
    _ = MvPowerSeries.subst (fun j ↦ f c • MvPowerSeries.map f (Φ.scaledFC c j))
          ((Φ.map f).log i) := by
        rw [subst_comp_subst_apply hcX hmsF]
        congr 1
        funext j
        rw [subst_smul hmsF, subst_X hmsF]
    _ = MvPowerSeries.subst
          (fun j ↦ MvPowerSeries.subst (fun t : ι ⊕ ι ↦ f c • X t) ((Φ.map f).F j))
          ((Φ.map f).log i) := by
        congr 1
        funext j
        rw [Φ.map_scaledFC_smul j, rescale_const_eq_subst]
    _ = MvPowerSeries.subst (fun t : ι ⊕ ι ↦ f c • X t)
          (MvPowerSeries.subst (fun j ↦ (Φ.map f).F j) ((Φ.map f).log i)) :=
        (subst_comp_subst_apply (Φ.map f).hasSubst_F hcX2 _).symm
    _ = MvPowerSeries.subst
          (fun s : ι ↦ f c • (X (Sum.inl s) : MvPowerSeries (ι ⊕ ι) K))
          ((Φ.map f).log i)
        + MvPowerSeries.subst
            (fun s : ι ↦ f c • (X (Sum.inr s) : MvPowerSeries (ι ⊕ ι) K))
            ((Φ.map f).log i) := by
        rw [(Φ.map f).log_subst_F i, ← coe_substAlgHom hcX2, map_add, coe_substAlgHom hcX2,
          subst_smulX_subst_X_comp Sum.inl, subst_smulX_subst_X_comp Sum.inr]

end Descent

/-! ### The multiplication-by-`m` series -/

section MulSeries

variable {O : Type*} [CommRing O] (Φ : FormalGroupLaw O Unit)

/-- The multiplication-by-`m` series of a one-parameter formal group law:
`ψ_0 = 0` and `ψ_{m+1} = F(X, ψ_m)`. -/
noncomputable def mulSeries : ℕ → MvPowerSeries Unit O
  | 0 => 0
  | m + 1 => MvPowerSeries.subst
      (Sum.elim (fun _ : Unit ↦ (X () : MvPowerSeries Unit O)) fun _ : Unit ↦ mulSeries m)
      (Φ.F ())

theorem mulSeries_zero : Φ.mulSeries 0 = 0 := rfl

theorem mulSeries_succ (m : ℕ) : Φ.mulSeries (m + 1) = MvPowerSeries.subst
    (Sum.elim (fun _ : Unit ↦ (X () : MvPowerSeries Unit O)) fun _ : Unit ↦ Φ.mulSeries m)
    (Φ.F ()) := rfl

theorem constantCoeff_mulSeries (m : ℕ) : constantCoeff (Φ.mulSeries m) = 0 := by
  induction m with
  | zero => rw [mulSeries_zero, map_zero]
  | succ m ih =>
    have h0 : ∀ i : Unit ⊕ Unit, constantCoeff (Sum.elim (fun _ : Unit ↦
        (X () : MvPowerSeries Unit O)) (fun _ : Unit ↦ Φ.mulSeries m) i) = 0 := by
      rintro (u | u)
      · exact constantCoeff_X ()
      · exact ih
    rw [mulSeries_succ]
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h0) h0
      (Φ.zero_constantCoeff ())

theorem hasSubst_mulSeries_pair (m : ℕ) : MvPowerSeries.HasSubst
    (Sum.elim (fun _ : Unit ↦ (X () : MvPowerSeries Unit O)) fun _ : Unit ↦ Φ.mulSeries m) :=
  hasSubst_of_constantCoeff_zero (by
    rintro (u | u)
    · exact constantCoeff_X ()
    · exact Φ.constantCoeff_mulSeries m)

theorem hasSubst_mulSeries (m : ℕ) :
    MvPowerSeries.HasSubst (fun _ : Unit ↦ Φ.mulSeries m) :=
  hasSubst_of_constantCoeff_zero fun _ ↦ Φ.constantCoeff_mulSeries m

theorem map_mulSeries {O' : Type*} [CommRing O'] (f : O →+* O') (m : ℕ) :
    MvPowerSeries.map f (Φ.mulSeries m) = (Φ.map f).mulSeries m := by
  induction m with
  | zero => rw [mulSeries_zero, mulSeries_zero, map_zero]
  | succ m ih =>
    rw [mulSeries_succ, mulSeries_succ, map_subst (Φ.hasSubst_mulSeries_pair m)]
    congr 1
    funext i
    rcases i with u | u
    · exact MvPowerSeries.map_X f _
    · exact ih

end MulSeries

/-! ### The logarithm of the multiplication series and its derivative -/

section LogMul

private lemma subst_zero_fam {σ R : Type*} [Finite σ] [CommRing R] {f : MvPowerSeries σ R}
    (hf : constantCoeff f = 0) :
    MvPowerSeries.subst (fun _ : σ ↦ (0 : MvPowerSeries σ R)) f = 0 := by
  have h0 : MvPowerSeries.HasSubst (fun _ : σ ↦ (0 : MvPowerSeries σ R)) :=
    hasSubst_of_constantCoeff_zero fun _ ↦ map_zero _
  ext d
  rw [coeff_subst h0]
  refine (finsum_eq_zero_of_forall_eq_zero fun m ↦ ?_).trans (map_zero (coeff d)).symm
  rcases eq_or_ne m 0 with rfl | hm
  · rw [coeff_zero_eq_constantCoeff_apply, hf, zero_smul]
  · obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hm
    rw [Finsupp.prod, Finset.prod_eq_zero hi
      (zero_pow (Finsupp.mem_support_iff.mp hi)), map_zero, smul_zero]

variable {K : Type*} [Field K] [CharZero K] (Φ : FormalGroupLaw K Unit)

/-- The formal logarithm turns the multiplication-by-`m` series into `m • log`. -/
theorem subst_mulSeries_log (m : ℕ) :
    MvPowerSeries.subst (fun _ : Unit ↦ Φ.mulSeries m) (Φ.log ()) = m • Φ.log () := by
  induction m with
  | zero => rw [mulSeries_zero, zero_smul, subst_zero_fam (Φ.constantCoeff_log ())]
  | succ m ih =>
    have hpair := Φ.hasSubst_mulSeries_pair m
    have hXfam : (fun s : Unit ↦ MvPowerSeries.subst (Sum.elim (fun _ : Unit ↦ X ())
        (fun _ : Unit ↦ Φ.mulSeries m)) (X (Sum.inl s) : MvPowerSeries (Unit ⊕ Unit) K))
        = (X ∘ id : Unit → MvPowerSeries Unit K) :=
      funext fun s ↦ by cases s; rw [subst_X hpair]; rfl
    have hψfam : (fun s : Unit ↦ MvPowerSeries.subst (Sum.elim (fun _ : Unit ↦ X ())
        (fun _ : Unit ↦ Φ.mulSeries m)) (X (Sum.inr s) : MvPowerSeries (Unit ⊕ Unit) K))
        = fun _ : Unit ↦ Φ.mulSeries m :=
      funext fun s ↦ by rw [subst_X hpair]; rfl
    have hinl : MvPowerSeries.HasSubst fun s : Unit ↦ (X (Sum.inl s) :
        MvPowerSeries (Unit ⊕ Unit) K) := hasSubst_of_constantCoeff_zero fun s ↦ by simp
    have hinr : MvPowerSeries.HasSubst fun s : Unit ↦ (X (Sum.inr s) :
        MvPowerSeries (Unit ⊕ Unit) K) := hasSubst_of_constantCoeff_zero fun s ↦ by simp
    calc MvPowerSeries.subst (fun _ : Unit ↦ Φ.mulSeries (m + 1)) (Φ.log ())
        = MvPowerSeries.subst (Sum.elim (fun _ : Unit ↦ X ()) fun _ : Unit ↦ Φ.mulSeries m)
            (MvPowerSeries.subst (fun j : Unit ↦ Φ.F j) (Φ.log ())) := by
          rw [show (fun _ : Unit ↦ Φ.mulSeries (m + 1)) = fun j : Unit ↦ MvPowerSeries.subst
            (Sum.elim (fun _ : Unit ↦ X ()) fun _ : Unit ↦ Φ.mulSeries m) (Φ.F j) from
              funext fun j ↦ by cases j; rw [mulSeries_succ],
            subst_comp_subst_apply (hasSubst_F Φ) hpair]
      _ = MvPowerSeries.subst (Sum.elim (fun _ : Unit ↦ X ()) fun _ : Unit ↦ Φ.mulSeries m)
            (MvPowerSeries.subst (fun s : Unit ↦ (X (Sum.inl s) :
                MvPowerSeries (Unit ⊕ Unit) K)) (Φ.log ()))
          + MvPowerSeries.subst (Sum.elim (fun _ : Unit ↦ X ()) fun _ : Unit ↦ Φ.mulSeries m)
              (MvPowerSeries.subst (fun s : Unit ↦ (X (Sum.inr s) :
                  MvPowerSeries (Unit ⊕ Unit) K)) (Φ.log ())) := by
          rw [Φ.log_subst_F (), ← coe_substAlgHom hpair, map_add, coe_substAlgHom hpair]
      _ = Φ.log () + m • Φ.log () := by
          rw [subst_comp_subst_apply hinl hpair, subst_comp_subst_apply hinr hpair,
            hXfam, hψfam, ← rename_eq_subst, rename_id, ih]
          rfl
      _ = (m + 1) • Φ.log () := (succ_nsmul' _ _).symm

/-- Differentiating the logarithm identity: `(M⁻¹ ∘ ψ_m) · ψ_m′ = m • M⁻¹`. -/
theorem subst_mulSeries_diffInv_mul_pderiv (m : ℕ) :
    MvPowerSeries.subst (fun _ : Unit ↦ Φ.mulSeries m) (Φ.diffMatrix⁻¹ () ())
        * pderiv () (Φ.mulSeries m)
      = m • Φ.diffMatrix⁻¹ () () := by
  have h := congrArg (pderiv ()) (Φ.subst_mulSeries_log m)
  rw [map_nsmul, pderiv_subst (Φ.hasSubst_mulSeries m), Φ.pderiv_log] at h
  simp only [Finset.univ_unique, Finset.sum_singleton, Φ.pderiv_log] at h
  exact h

end LogMul

end FormalGroupLaw

/-! ### The scaled integral logarithm over the valuation ring of a completion -/

section AdicScaledLog

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {v : HeightOneSpectrum R}

private lemma coe_injective :
    Function.Injective
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) :=
  fun _ _ h ↦ Subtype.ext h

/-- The residue characteristic: a prime number lying in the maximal ideal of `𝒪_v`. -/
private lemma exists_prime_mem_maximalIdeal [Finite (R ⧸ v.asIdeal)] :
    ∃ p : ℕ, p.Prime ∧
      (p : v.adicCompletionIntegers K) ∈ maximalIdeal (v.adicCompletionIntegers K) := by
  have hfin : Finite (v.adicCompletionIntegers K ⧸ maximalIdeal (v.adicCompletionIntegers K)) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := K)).toEquiv
  have := Fintype.ofFinite (v.adicCompletionIntegers K ⧸ maximalIdeal (v.adicCompletionIntegers K))
  set p := ringChar (v.adicCompletionIntegers K ⧸ maximalIdeal (v.adicCompletionIntegers K))
  refine ⟨p, CharP.char_is_prime
    (v.adicCompletionIntegers K ⧸ maximalIdeal (v.adicCompletionIntegers K)) p, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact CharP.cast_eq_zero _ p

/-- The valuation of a nonzero element of the maximal ideal is `exp (-e)` for some
`e ≥ 1`. -/
theorem exists_valued_eq_exp_neg {x : v.adicCompletionIntegers K}
    (hx : x ∈ maximalIdeal (v.adicCompletionIntegers K)) (hx0 : x ≠ 0) :
    ∃ e : ℕ, 1 ≤ e ∧
      Valued.v ((x : v.adicCompletionIntegers K) : v.adicCompletion K) = exp (-(e : ℤ)) := by
  have hv0 : Valued.v ((x : v.adicCompletionIntegers K) : v.adicCompletion K) ≠ 0 := by
    simpa using hx0
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v ((x : v.adicCompletionIntegers K) : v.adicCompletion K)
      = exp m := ⟨_, (exp_log hv0).symm⟩
  have hle := (v.mem_maximalIdeal_pow_iff (K := K) (x := x) (n := 1)).mp (by rwa [pow_one])
  rw [hm, exp_le_exp] at hle
  push_cast at hle
  exact ⟨(-m).toNat, by lia, by rw [hm]; congr 1; lia⟩

variable [CharZero K] in
open FormalGroupLaw in
/-- The `π^e`-scaled logarithm has integral coefficients: `π^{e(n-1)} · λ_n` has
valuation at most `1`, since the only denominators of `λ_n` are `p`-powers with exponent
`v_p(n) ≤ n - 1` and `v(p) = exp (-e)`. -/
private lemma exists_integral_scaled_log {p e : ℕ} {π : v.adicCompletionIntegers K}
    (hp : p.Prime)
    (hpmem : (p : v.adicCompletionIntegers K) ∈ maximalIdeal (v.adicCompletionIntegers K))
    (hpe : Valued.v (((p : v.adicCompletionIntegers K) :
      v.adicCompletionIntegers K) : v.adicCompletion K) = exp (-(e : ℤ)))
    (hπe : Valued.v ((π : v.adicCompletionIntegers K) : v.adicCompletion K) = exp (-1 : ℤ))
    (Φ : FormalGroupLaw (v.adicCompletionIntegers K) Unit) :
    ∃ lhat : MvPowerSeries Unit (v.adicCompletionIntegers K), ∀ d : Unit →₀ ℕ,
      ((coeff d lhat : v.adicCompletionIntegers K) : v.adicCompletion K)
        = ((π : v.adicCompletionIntegers K) : v.adicCompletion K) ^ (e * (d.degree - 1)) *
          coeff d ((Φ.map (algebraMap (v.adicCompletionIntegers K)
            (v.adicCompletion K))).log ()) := by
  have hchar : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  have hfp : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
      (p : v.adicCompletionIntegers K) ≠ 0 := by
    rw [map_natCast]
    exact_mod_cast hp.pos.ne'
  have hint : ∀ d : Unit →₀ ℕ,
      Valued.v (((π : v.adicCompletionIntegers K) : v.adicCompletion K) ^ (e * (d.degree - 1)) *
        coeff d ((Φ.map (algebraMap (v.adicCompletionIntegers K)
          (v.adicCompletion K))).log ())) ≤ 1 := by
    intro d
    rcases Nat.eq_zero_or_pos d.degree with h0 | hpos
    · obtain rfl : d = 0 := (Finsupp.degree_eq_zero_iff d).mp h0
      rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_log, mul_zero, map_zero]
      exact zero_le_one
    · obtain ⟨b, hb⟩ := Φ.coeff_log_map_padic hp hpmem _ hfp () d
      have hvp : padicValNat p d.degree < d.degree :=
        lt_of_lt_of_le (Nat.lt_pow_self hp.one_lt)
          (Nat.le_of_dvd hpos pow_padicValNat_dvd)
      -- the coefficient of the logarithm has valuation at most `exp (e·v_p(n))`
      have h1 := congrArg Valued.v hb
      rw [map_mul, map_pow, show algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
          (p : v.adicCompletionIntegers K) = (((p : v.adicCompletionIntegers K) :
            v.adicCompletionIntegers K) : v.adicCompletion K) from rfl, hpe] at h1
      have hfb : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) b)
          ≤ 1 := b.2
      have h3 : Valued.v (coeff d ((Φ.map (algebraMap (v.adicCompletionIntegers K)
          (v.adicCompletion K))).log ())) ≤ exp ((e * padicValNat p d.degree : ℕ) : ℤ) := by
        have h4 := mul_le_mul_right (h1.le.trans hfb)
          (exp ((e * padicValNat p d.degree : ℕ) : ℤ))
        rwa [mul_one, ← mul_assoc, ← exp_nsmul, nsmul_eq_mul, ← exp_add,
          show ((e * padicValNat p d.degree : ℕ) : ℤ) + (padicValNat p d.degree : ℤ) *
            -(e : ℤ) = 0 by push_cast; ring, exp_zero, one_mul] at h4
      rw [map_mul, map_pow, hπe]
      refine le_trans (mul_le_mul_right h3 _) ?_
      rw [← exp_nsmul, nsmul_eq_mul, ← exp_add, ← exp_zero, exp_le_exp]
      have hmono := (Nat.cast_le (α := ℤ)).mpr
        (Nat.mul_le_mul_left e (show padicValNat p d.degree ≤ d.degree - 1 by lia))
      lia
  exact ⟨fun d ↦ ⟨_, hint d⟩, fun d ↦ rfl⟩

private lemma unit_finsupp_of_degree_le_one {d : Unit →₀ ℕ} (h : d.degree ≤ 1) :
    d = 0 ∨ d = Finsupp.single () 1 := by
  have hd : d = Finsupp.single () (d ()) := Finsupp.ext fun i ↦ by cases i; simp
  rw [hd, Finsupp.degree_single] at h
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h0 | h1
  · exact .inl (by rw [hd, h0, Finsupp.single_zero])
  · exact .inr (by rw [hd, h1])

/-- Cancellation of a nonzero scalar on multivariate power series over a domain. -/
private lemma smul_left_cancel {O : Type*} [CommRing O] [NoZeroDivisors O] {σ : Type*}
    {c : O} (hc : c ≠ 0) {A B : MvPowerSeries σ O} (h : c • A = c • B) : A = B := by
  ext d
  have h' := congrArg (coeff d) h
  rw [MvPowerSeries.coeff_smul, MvPowerSeries.coeff_smul] at h'
  exact mul_left_cancel₀ hc h'

section ScaledPackage

variable {e : ℕ} {π : v.adicCompletionIntegers K}
  {Φ : FormalGroupLaw (v.adicCompletionIntegers K) Unit}
  {lhat : MvPowerSeries Unit (v.adicCompletionIntegers K)}

/-- The scaled-coefficient property of the integral scaled logarithm `lhat`
(certificate hypothesis for the lemmas below). -/
private def IsScaledLog (e : ℕ) (π : v.adicCompletionIntegers K)
    (Φ : FormalGroupLaw (v.adicCompletionIntegers K) Unit)
    (lhat : MvPowerSeries Unit (v.adicCompletionIntegers K)) : Prop :=
  ∀ d : Unit →₀ ℕ, ((coeff d lhat : v.adicCompletionIntegers K) : v.adicCompletion K)
    = ((π : v.adicCompletionIntegers K) : v.adicCompletion K) ^ (e * (d.degree - 1)) *
      coeff d ((Φ.map (algebraMap (v.adicCompletionIntegers K)
        (v.adicCompletion K))).log ())

open FormalGroupLaw in
private lemma constantCoeff_of_isScaledLog (hl : IsScaledLog e π Φ lhat) :
    constantCoeff lhat = 0 := by
  have h := hl 0
  rw [map_zero Finsupp.degree, coeff_zero_eq_constantCoeff_apply,
    coeff_zero_eq_constantCoeff_apply, constantCoeff_log, mul_zero] at h
  exact Subtype.ext (by push_cast; exact h)

open FormalGroupLaw in
private lemma coeff_single_of_isScaledLog (hl : IsScaledLog e π Φ lhat) :
    coeff (Finsupp.single () 1) lhat = 1 := by
  have h := hl (Finsupp.single () 1)
  rw [Finsupp.degree_single, Nat.sub_self, mul_zero, pow_zero, one_mul,
    coeff_single_log] at h
  simp only [if_pos] at h
  exact Subtype.ext (by push_cast; exact h)

/-- The scaled logarithm has trivial coefficients in degrees `≤ 1` apart from the linear
term `X`; this is the hypothesis of the compositional-inverse machinery. -/
private lemma sub_X_of_isScaledLog (hl : IsScaledLog e π Φ lhat) (i : Unit)
    (d : Unit →₀ ℕ) (hd : d.degree ≤ 1) :
    coeff d ((fun _ : Unit ↦ lhat) i - X i) = 0 := by
  rcases unit_finsupp_of_degree_le_one hd with rfl | rfl
  · rw [map_sub, coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_of_isScaledLog hl, constantCoeff_X, sub_zero]
  · rw [map_sub, coeff_single_of_isScaledLog hl, MvPowerSeries.coeff_X,
      if_pos (by cases i; rfl), sub_self]

open FormalGroupLaw in
/-- The additivity of the divided scaled logarithm for the `π^e`-scaled formal group
law, obtained from the descended identity for `π^e • lhat` by cancelling `π^e`. -/
private lemma subst_scaledFC_of_isScaledLog [CharZero K] (hπ0 : π ≠ 0)
    (hl : IsScaledLog e π Φ lhat) :
    MvPowerSeries.subst (Φ.scaledFC (π ^ e)) lhat
      = MvPowerSeries.subst (fun s : Unit ↦ (X (Sum.inl s) :
          MvPowerSeries (Unit ⊕ Unit) (v.adicCompletionIntegers K))) lhat
        + MvPowerSeries.subst (fun s : Unit ↦ (X (Sum.inr s) :
            MvPowerSeries (Unit ⊕ Unit) (v.adicCompletionIntegers K))) lhat := by
  have : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  have hHL : ∀ j : Unit, MvPowerSeries.map
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) ((π ^ e) • lhat)
      = rescale (fun _ ↦ algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
          (π ^ e))
        ((Φ.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))).log j) := by
    intro j
    cases j
    refine map_eq_rescale_of_forall_coeff fun d ↦ ?_
    rw [MvPowerSeries.coeff_smul, map_mul, show algebraMap (v.adicCompletionIntegers K)
      (v.adicCompletion K) (coeff d lhat) = ((coeff d lhat : v.adicCompletionIntegers K) :
        v.adicCompletion K) from rfl, hl d, map_pow, show algebraMap
      (v.adicCompletionIntegers K) (v.adicCompletion K) π =
        ((π : v.adicCompletionIntegers K) : v.adicCompletion K) from rfl]
    rcases Nat.eq_zero_or_pos d.degree with h0 | hpos
    · obtain rfl : d = 0 := (Finsupp.degree_eq_zero_iff d).mp h0
      rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_log, mul_zero, mul_zero, mul_zero]
    · rw [← mul_assoc, ← pow_add, ← pow_mul]
      congr 2
      conv_rhs => rw [← Nat.succ_pred_eq_of_pos hpos]
      rw [Nat.mul_succ, Nat.pred_eq_sub_one]
      omega
  have hInl : HasSubst fun s : Unit ↦ (X (Sum.inl s) :
      MvPowerSeries (Unit ⊕ Unit) (v.adicCompletionIntegers K)) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by simp
  have hInr : HasSubst fun s : Unit ↦ (X (Sum.inr s) :
      MvPowerSeries (Unit ⊕ Unit) (v.adicCompletionIntegers K)) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by simp
  have h1 := Φ.subst_scaledFC_descent coe_injective hHL ()
  rw [subst_smul (Φ.hasSubst_scaledFC _), subst_smul hInl, subst_smul hInr, ← smul_add] at h1
  exact smul_left_cancel (pow_ne_zero e hπ0) h1

open FormalGroupLaw in
/-- The scaled-logarithm package over `𝒪_v`: a level `n ≥ 1`, a uniformizer `π`, and a
pair of integral power series `lhat`, `ehat` — the divided `π^n`-scaled logarithm and its
compositional inverse — with the composition identities and the additivity of `lhat` for
the `π^n`-scaled formal group law. -/
theorem exists_scaledLog [Finite (R ⧸ v.asIdeal)] [CharZero K]
    (Φ : FormalGroupLaw (v.adicCompletionIntegers K) Unit) :
    ∃ (n : ℕ) (π : v.adicCompletionIntegers K)
      (lhat ehat : MvPowerSeries Unit (v.adicCompletionIntegers K)),
      1 ≤ n ∧ π ≠ 0 ∧ maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {π} ∧
      constantCoeff lhat = 0 ∧ constantCoeff ehat = 0 ∧
      MvPowerSeries.subst (fun _ : Unit ↦ ehat) lhat = X () ∧
      MvPowerSeries.subst (fun _ : Unit ↦ lhat) ehat = X () ∧
      MvPowerSeries.subst (Φ.scaledFC (π ^ n)) lhat
        = MvPowerSeries.subst (fun s : Unit ↦ (X (Sum.inl s) :
            MvPowerSeries (Unit ⊕ Unit) (v.adicCompletionIntegers K))) lhat
          + MvPowerSeries.subst (fun s : Unit ↦ (X (Sum.inr s) :
              MvPowerSeries (Unit ⊕ Unit) (v.adicCompletionIntegers K))) lhat := by
  obtain ⟨p, hp, hpmem⟩ := exists_prime_mem_maximalIdeal (v := v) (K := K)
  have hchar : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  have hp0 : (p : v.adicCompletionIntegers K) ≠ 0 := fun h ↦ hp.ne_zero (by
    have h' := congrArg (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) h
    rw [map_natCast, map_zero] at h'
    exact_mod_cast h')
  obtain ⟨e, he1, hpe⟩ := exists_valued_eq_exp_neg hpmem hp0
  obtain ⟨π, hπirr⟩ :=
    IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  obtain ⟨lhat, hl⟩ := exists_integral_scaled_log hp hpmem hpe
    (v.valued_irreducible_adicCompletionIntegers hπirr) Φ
  have hl' : IsScaledLog e π Φ lhat := hl
  have ha := sub_X_of_isScaledLog hl'
  refine ⟨e, π, lhat, invSubst (fun _ ↦ lhat) (), he1, hπirr.ne_zero, hπirr.maximalIdeal_eq,
    constantCoeff_of_isScaledLog hl', constantCoeff_invSubst ha (), ?_, ?_,
    subst_scaledFC_of_isScaledLog hπirr.ne_zero hl'⟩
  · rw [show (fun _ : Unit ↦ invSubst (fun _ ↦ lhat) ()) = invSubst (fun _ ↦ lhat) from
      funext fun i ↦ by cases i; rfl]
    exact subst_invSubst ha ()
  · exact subst_a_invSubst ha ()

end ScaledPackage

end AdicScaledLog

/-! ### The evaluated scaled logarithm on the maximal ideal -/

section EvalLayer

open MvPSeries

variable {O : Type*} [CommRing O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))]

private lemma hasEval_pair {s₁ s₂ : O} (h₁ : s₁ ∈ maximalIdeal O) (h₂ : s₂ ∈ maximalIdeal O) :
    MvPowerSeries.HasEval (Sum.elim (fun _ : Unit ↦ s₁) fun _ : Unit ↦ s₂) :=
  hasEval_of_mem fun i ↦ by rcases i with u | u <;> simpa

variable [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]

/-- Evaluation of a one-variable series without constant term maps `𝔪` to `𝔪`. -/
theorem eval_unit_mem {t : O} (ht : t ∈ maximalIdeal O) {h : MvPowerSeries Unit O}
    (hcc : constantCoeff h = 0) : eval (fun _ : Unit ↦ t) h ∈ maximalIdeal O :=
  eval_mem_maximalIdeal (hasEval_of_mem fun _ ↦ ht) (fun _ ↦ ht) h (hcc ▸ zero_mem _)

/-- Evaluating a composition identity `h ∘ g = X`: the evaluations of `g` and `h` are
mutually inverse on `𝔪`. -/
theorem eval_eval_of_subst_eq_X {t : O} (ht : t ∈ maximalIdeal O)
    {g h : MvPowerSeries Unit O} (hg0 : constantCoeff g = 0)
    (hcomp : MvPowerSeries.subst (fun _ : Unit ↦ g) h = X ()) :
    eval (fun _ : Unit ↦ eval (fun _ : Unit ↦ t) g) h = t := by
  have hE : MvPowerSeries.HasEval (fun _ : Unit ↦ t) := hasEval_of_mem fun _ ↦ ht
  have hS : MvPowerSeries.HasSubst (fun _ : Unit ↦ g) :=
    hasSubst_of_constantCoeff_zero fun _ ↦ hg0
  have h1 := congrArg (eval (fun _ : Unit ↦ t)) hcomp
  rwa [eval_subst hE hS, eval_X] at h1

open FormalGroupLaw in
/-- Additivity of the evaluated scaled logarithm: evaluating the descended identity at a
pair of points of `𝔪`. -/
theorem eval_scaledFC_add (Φ : FormalGroupLaw O Unit) {c : O}
    {lhat : MvPowerSeries Unit O}
    (hadd : MvPowerSeries.subst (Φ.scaledFC c) lhat
      = MvPowerSeries.subst (fun s : Unit ↦ (X (Sum.inl s) :
          MvPowerSeries (Unit ⊕ Unit) O)) lhat
        + MvPowerSeries.subst (fun s : Unit ↦ (X (Sum.inr s) :
            MvPowerSeries (Unit ⊕ Unit) O)) lhat)
    {s₁ s₂ : O} (h₁ : s₁ ∈ maximalIdeal O) (h₂ : s₂ ∈ maximalIdeal O) :
    eval (fun _ : Unit ↦ eval (Sum.elim (fun _ : Unit ↦ s₁) fun _ : Unit ↦ s₂)
        (Φ.scaledFC c ())) lhat
      = eval (fun _ : Unit ↦ s₁) lhat + eval (fun _ : Unit ↦ s₂) lhat := by
  have hE := hasEval_pair h₁ h₂
  have hInl : MvPowerSeries.HasSubst fun s : Unit ↦ (X (Sum.inl s) :
      MvPowerSeries (Unit ⊕ Unit) O) := hasSubst_of_constantCoeff_zero fun s ↦ by simp
  have hInr : MvPowerSeries.HasSubst fun s : Unit ↦ (X (Sum.inr s) :
      MvPowerSeries (Unit ⊕ Unit) O) := hasSubst_of_constantCoeff_zero fun s ↦ by simp
  have h1 := congrArg (eval (Sum.elim (fun _ : Unit ↦ s₁) fun _ : Unit ↦ s₂)) hadd
  rw [eval_add hE, eval_subst hE (Φ.hasSubst_scaledFC c), eval_subst hE hInl,
    eval_subst hE hInr,
    show (fun s : Unit ↦ eval (Sum.elim (fun _ : Unit ↦ s₁) fun _ : Unit ↦ s₂)
      (X (Sum.inl s) : MvPowerSeries (Unit ⊕ Unit) O)) = fun _ : Unit ↦ s₁ from
      funext fun s ↦ by rw [eval_X, Sum.elim_inl],
    show (fun s : Unit ↦ eval (Sum.elim (fun _ : Unit ↦ s₁) fun _ : Unit ↦ s₂)
      (X (Sum.inr s) : MvPowerSeries (Unit ⊕ Unit) O)) = fun _ : Unit ↦ s₂ from
      funext fun s ↦ by rw [eval_X, Sum.elim_inr]] at h1
  exact h1

open FormalGroupLaw in
/-- Compatibility of the scaled formal group sum with the original one: evaluating `F` at
`(c·s₁, c·s₂)` is `c` times the evaluated scaled sum. -/
theorem eval_F_eq_mul_eval_scaledFC (Φ : FormalGroupLaw O Unit) (c : O)
    {s₁ s₂ : O} (h₁ : s₁ ∈ maximalIdeal O) (h₂ : s₂ ∈ maximalIdeal O) :
    eval (Sum.elim (fun _ : Unit ↦ c * s₁) fun _ : Unit ↦ c * s₂) (Φ.F ())
      = c * eval (Sum.elim (fun _ : Unit ↦ s₁) fun _ : Unit ↦ s₂) (Φ.scaledFC c ()) := by
  have hE := hasEval_pair h₁ h₂
  have hcX : MvPowerSeries.HasSubst fun t : Unit ⊕ Unit ↦ c • (X t :
      MvPowerSeries (Unit ⊕ Unit) O) := hasSubst_of_constantCoeff_zero fun s ↦ by simp
  have hform : MvPowerSeries.subst (fun t : Unit ⊕ Unit ↦ c • X t) (Φ.F ())
      = C c * Φ.scaledFC c () := by
    rw [← rescale_const_eq_subst]
    ext d
    rw [coeff_rescale, MvPowerSeries.coeff_C_mul, coeff_scaledFC, Finsupp.prod,
      Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply]
    rcases Nat.eq_zero_or_pos d.degree with h0 | hpos
    · obtain rfl : d = 0 := (Finsupp.degree_eq_zero_iff d).mp h0
      rw [coeff_zero_eq_constantCoeff_apply, Φ.zero_constantCoeff, mul_zero, mul_zero,
        mul_zero]
    · rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hpos]
  have h1 := congrArg (eval (Sum.elim (fun _ : Unit ↦ s₁) fun _ : Unit ↦ s₂)) hform
  rw [eval_subst hE hcX, eval_mul hE, eval_C,
    show (fun t : Unit ⊕ Unit ↦ eval (Sum.elim (fun _ : Unit ↦ s₁) fun _ : Unit ↦ s₂)
      (c • (X t : MvPowerSeries (Unit ⊕ Unit) O)))
      = Sum.elim (fun _ : Unit ↦ c * s₁) fun _ : Unit ↦ c * s₂ from funext fun t ↦ by
        rcases t with u | u <;>
          rw [smul_eq_C_mul, eval_mul hE, eval_C, eval_X] <;> simp] at h1
  exact h1

end EvalLayer

/-! ### Divisibility of the multiplication-by-`p` coefficients over `𝒪_v` -/

section AdicMulSeries

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FormalGroupLaw

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {v : HeightOneSpectrum R}
  (Φ : FormalGroupLaw (v.adicCompletionIntegers K) Unit)

private lemma constantCoeff_diffInv :
    constantCoeff (Φ.diffMatrix⁻¹ () ()) = 1 := by
  have h := congrArg (fun A ↦ A () ()) Φ.diffMatrixInv_map_constantCoeff
  simpa using h

variable [CharZero K]

/-- The derivative identity `(M⁻¹ ∘ ψ_m) · ψ_m′ = m • M⁻¹`, descended to `𝒪_v`. -/
private lemma subst_mulSeries_diffInv_mul_pderiv_int (m : ℕ) :
    MvPowerSeries.subst (fun _ : Unit ↦ Φ.mulSeries m) (Φ.diffMatrix⁻¹ () ())
        * pderiv () (Φ.mulSeries m)
      = m • Φ.diffMatrix⁻¹ () () := by
  have hchar : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  apply map_injective_of_injective coe_injective
  rw [map_mul, map_subst (Φ.hasSubst_mulSeries m), map_pderiv, map_nsmul,
    show (fun i : Unit ↦ MvPowerSeries.map (algebraMap (v.adicCompletionIntegers K)
        (v.adicCompletion K)) (Φ.mulSeries m))
      = fun _ : Unit ↦ (Φ.map (algebraMap (v.adicCompletionIntegers K)
          (v.adicCompletion K))).mulSeries m from
      funext fun _ ↦ Φ.map_mulSeries _ m,
    Φ.map_mulSeries _ m,
    show MvPowerSeries.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))
        (Φ.diffMatrix⁻¹ () ())
      = (Φ.map (algebraMap (v.adicCompletionIntegers K)
          (v.adicCompletion K))).diffMatrix⁻¹ () () from by
      rw [Φ.diffMatrixInv_map]
      rfl]
  exact (Φ.map _).subst_mulSeries_diffInv_mul_pderiv m

/-- The coefficients of the derivative of `ψ_m` are divisible by `m`. -/
private lemma coeff_pderiv_mulSeries_mem (m : ℕ) (e : Unit →₀ ℕ) :
    coeff e (pderiv () (Φ.mulSeries m)) ∈
      Ideal.span {(m : v.adicCompletionIntegers K)} := by
  have hU : IsUnit (MvPowerSeries.subst (fun _ : Unit ↦ Φ.mulSeries m)
      (Φ.diffMatrix⁻¹ () ())) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff,
      constantCoeff_subst_of_constantCoeff_zero (Φ.hasSubst_mulSeries m)
        (fun _ ↦ Φ.constantCoeff_mulSeries m), constantCoeff_diffInv Φ]
    exact isUnit_one
  obtain ⟨Uinv, hUinv⟩ := hU.exists_left_inv
  have hψ : pderiv () (Φ.mulSeries m) = Uinv * (m • Φ.diffMatrix⁻¹ () ()) := by
    rw [← subst_mulSeries_diffInv_mul_pderiv_int Φ m, ← mul_assoc, hUinv, one_mul]
  rw [hψ, MvPowerSeries.coeff_mul]
  refine Ideal.sum_mem _ fun x hx ↦ ?_
  rw [map_nsmul, nsmul_eq_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _
    (Ideal.mem_span_singleton_self _))

/-- The linear coefficient of the multiplication-by-`m` series is `m`. -/
theorem coeff_single_mulSeries (m : ℕ) :
    coeff (Finsupp.single () 1) (Φ.mulSeries m) = m := by
  have h := congrArg constantCoeff (subst_mulSeries_diffInv_mul_pderiv_int Φ m)
  rw [map_mul, constantCoeff_subst_of_constantCoeff_zero (Φ.hasSubst_mulSeries m)
      (fun _ ↦ Φ.constantCoeff_mulSeries m), constantCoeff_diffInv Φ, one_mul, map_nsmul,
    constantCoeff_diffInv, ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv] at h
  simpa using h

/-- The coefficients of `ψ_p` in degrees not divisible by `p` are divisible by `p`. -/
theorem coeff_mulSeries_mem_span {p : ℕ} (hp : p.Prime)
    (hpmem : (p : v.adicCompletionIntegers K) ∈ maximalIdeal (v.adicCompletionIntegers K))
    {d : Unit →₀ ℕ} (hd : ¬ p ∣ d ()) :
    coeff d (Φ.mulSeries p) ∈ Ideal.span {(p : v.adicCompletionIntegers K)} := by
  have hne : d () ≠ 0 := fun h ↦ hd (h ▸ dvd_zero p)
  have hstep := coeff_pderiv_mulSeries_mem Φ p (d - Finsupp.single () 1)
  rw [coeff_pderiv] at hstep
  have hd1 : (d - Finsupp.single () 1) + Finsupp.single () 1 = d :=
    Finsupp.ext fun i ↦ by
      cases i
      simp [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hne)]
  have hd2 : (d - Finsupp.single () 1 : Unit →₀ ℕ) () + 1 = d () := by
    simp [Finsupp.tsub_apply, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hne)]
  rw [hd1, hd2] at hstep
  obtain ⟨u, hu⟩ := (isUnit_natCast_of_not_dvd hp hpmem hd).exists_left_inv
  rw [show coeff d (Φ.mulSeries p)
      = u * ((d () : v.adicCompletionIntegers K) * coeff d (Φ.mulSeries p)) by
    rw [← mul_assoc, hu, one_mul]]
  exact Ideal.mul_mem_left _ _ hstep

end AdicMulSeries

end ChabautyColeman

end
