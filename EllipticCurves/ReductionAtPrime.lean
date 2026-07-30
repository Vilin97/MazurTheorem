/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
Source: MichaelStollBayreuth/EllipticCurves at commit 3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f.
Exact-pin changes are documented in PORTING.md.
-/
module

public import EllipticCurves.Mathlib.AdicValuation
public import EllipticCurves.Mathlib.EllipticCurvePoint
public import EllipticCurves.WeierstrassFormalGroup.Reduction

@[expose] public section

/-!
# Reduction of points modulo a prime of the base ring

Let `E` be an elliptic curve over the fraction field `K` of a Dedekind domain `R`, let `v` be a
maximal ideal (height-one prime) of `R`, and let `W₀` be an integral model of `E` over `R`
(`hE : W₀.map (algebraMap R K) = E`) whose reduction modulo `v` is again elliptic — *good
reduction* at `v`, the instance hypothesis `[(redCurve v W₀).IsElliptic]`.  This file defines the
reduced curve `redCurve v W₀` over the residue field `R ⧸ v.asIdeal` and the reduction
homomorphism `redHom v hE : E(K) →+ Ẽ(R ⧸ v.asIdeal)` — a point with `v`-integral coordinates
maps to their residues (via `residueHom v`), a point with a pole at `v` maps to `0` — with **no
completions in the definitions or statements**.

The completion `K_v` enters only through proofs: `adicRed_pointMap` identifies `red v hE` with
the reduction map `adicRed` of the base-changed curve over `K_v` (where the formal-group
machinery of `EllipticCurves.WeierstrassFormalGroup` lives), and additivity, injectivity on
torsion, and preservation of the order of torsion points are transported back along it.

## Main definitions and statements

* `WeierstrassCurve.Affine.redCurve`: the reduction `Ẽ` of `W₀` modulo `v`, a Weierstrass curve
  over `R ⧸ v.asIdeal`.
* `WeierstrassCurve.Affine.red`, `WeierstrassCurve.Affine.redHom`: the reduction map
  `E(K) →+ Ẽ(R ⧸ v.asIdeal)`.
* `WeierstrassCurve.Affine.nsmul_eq_zero_of_red_nsmul_eq_zero`: if the reduction of a torsion
  point is `m`-torsion, so is the point itself — under the standard ramification condition on
  the residue characteristic `p`, namely `(p : R) ∈ v.asIdeal` and `(p : R) ∉ v.asIdeal ^ (p - 1)`
  (that is, `e ≤ p - 2` for the ramification index `e`, e.g. `p` odd and `v` unramified).
* `WeierstrassCurve.Affine.addOrderOf_red`: under the same condition, reduction preserves the
  order of a torsion point.
* `WeierstrassCurve.Affine.addOrderOf_dvd_natCard_red`: consequently, the order of a torsion
  point divides the number of points of the reduction.
-/

open Function IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing WithZero

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R) {E : Affine K} {W₀ : WeierstrassCurve R}
  (hE : W₀.map (algebraMap R K) = E)

/-- The reduction `Ẽ` of the integral model `W₀` modulo the prime `v`, a Weierstrass curve over
the residue field `R ⧸ v.asIdeal`: the base change of `W₀` along
`algebraMap R (R ⧸ v.asIdeal) = Ideal.Quotient.mk v.asIdeal`.  *Good reduction* of `W₀` at `v`
is the instance hypothesis `[(redCurve v W₀).IsElliptic]`. -/
noncomputable abbrev redCurve (W₀ : WeierstrassCurve R) : Affine (R ⧸ v.asIdeal) :=
  ((W₀.toAffine ⁄ (R ⧸ v.asIdeal)) : WeierstrassCurve _).toAffine

/-! ### The reduction map, defined over `K`

The definition of `red` needs three facts about a point of `E(K)` with `v`-integral
`x`-coordinate: its `y`-coordinate is `v`-integral, the residues of its coordinates satisfy the
reduced Weierstrass equation, and (under good reduction) they are a nonsingular point of `Ẽ`.
The first is transported from the completion (`integral_of_not_mem`); the others are proved
directly from `residueHom`. -/

include hE in
/-- The base change to `𝒪_v` of an integral model of `E` over `R` is an integral model of the
base change of `E` to `K_v`. -/
lemma map_baseChange_adicCompletionIntegers :
    (W₀.map (algebraMap R (v.adicCompletionIntegers K))).map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))
      = ((E ⁄ (v.adicCompletion K)) : WeierstrassCurve _).toAffine := by
  rw [← hE]
  change _ = (W₀.map (algebraMap R K)).map (algebraMap K (v.adicCompletion K))
  rw [map_map, map_map, ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]

/-- The valuation of the image in the completion is the `v`-adic valuation (an unprimed form of
`valuedAdicCompletion_eq_valuation'` with the coercion spelled as `algebraMap`). -/
private lemma valued_algebraMap (x : K) :
    Valued.v (algebraMap K (v.adicCompletion K) x) = v.valuation K x :=
  v.valuedAdicCompletion_eq_valuation' x

/-- A `v`-integral element of `K` has no pole of order `≥ 2` in the completion. -/
private lemma not_exp_two_le {x : K} (hx : v.valuation K x ≤ 1) :
    ¬ exp (2 : ℤ) ≤ Valued.v (algebraMap K (v.adicCompletion K) x) := by
  rw [valued_algebraMap v]
  intro hc
  exact absurd (hx.trans_lt (lt_of_lt_of_le (by rw [← exp_zero]; exact exp_lt_exp.mpr (by lia))
    hc)) (lt_irrefl _)

/-- The ramification hypotheses on the residue characteristic transfer to the completion. -/
private lemma natCast_mem_maximalIdeal_pow_iff {p k : ℕ} :
    (p : v.adicCompletionIntegers K) ∈ maximalIdeal (v.adicCompletionIntegers K) ^ k ↔
      (p : R) ∈ v.asIdeal ^ k := by
  rw [show ((p : ℕ) : v.adicCompletionIntegers K)
      = algebraMap R (v.adicCompletionIntegers K) (p : R) from (map_natCast _ p).symm,
    algebraMap_mem_maximalIdeal_pow_iff]

private lemma natCast_mem_maximalIdeal {p : ℕ} (hpmem : (p : R) ∈ v.asIdeal) :
    (p : v.adicCompletionIntegers K) ∈ maximalIdeal (v.adicCompletionIntegers K) := by
  have h1 := (natCast_mem_maximalIdeal_pow_iff (K := K) v (p := p) (k := 1)).mpr
    (by rwa [pow_one])
  rwa [pow_one] at h1

include hE in
/-- The `y`-coordinate of a point of `E(K)` whose `x`-coordinate is `v`-integral is itself
`v`-integral. -/
lemma valuation_le_one_of_equation {x y : K} (hxy : E.Equation x y)
    (hx : v.valuation K x ≤ 1) : v.valuation K y ≤ 1 := by
  have hW := map_baseChange_adicCompletionIntegers v hE
  have hEq : (((E ⁄ (v.adicCompletion K)) : WeierstrassCurve _).toAffine).Equation
      (algebraMap K (v.adicCompletion K) x) (algebraMap K (v.adicCompletion K) y) :=
    Equation.map (algebraMap K (v.adicCompletion K)) hxy
  have h := (integral_of_not_mem hW hEq (not_exp_two_le v hx)).2
  rwa [valued_algebraMap v] at h

include hE in
/-- The residues of the coordinates of a `v`-integral point of `E(K)` satisfy the reduced
Weierstrass equation. -/
lemma equation_residueHom {x y : K} (hxy : E.Equation x y) (hx : v.valuation K x ≤ 1)
    (hy : v.valuation K y ≤ 1) :
    (redCurve v W₀).Equation (residueHom v ⟨x, hx⟩) (residueHom v ⟨y, hy⟩) := by
  -- the equation over the subring of `v`-integral elements of `K`
  have hinj : Function.Injective (algebraMap ((v.valuation K).integer) K) :=
    Subtype.val_injective
  have hcurveK : ((W₀.map (algebraMap R (v.valuation K).integer)).toAffine).map
      (algebraMap ((v.valuation K).integer) K) = E := by
    change (W₀.map (algebraMap R (v.valuation K).integer)).map
      (algebraMap ((v.valuation K).integer) K) = E
    rw [WeierstrassCurve.map_map, ← IsScalarTower.algebraMap_eq R ((v.valuation K).integer) K]
    exact hE
  have hOeq : ((W₀.map (algebraMap R (v.valuation K).integer)).toAffine).Equation
      (⟨x, hx⟩ : (v.valuation K).integer) ⟨y, hy⟩ := by
    refine ((W₀.map (algebraMap R (v.valuation K).integer)).toAffine.map_equation
      hinj _ _).mp ?_
    rw [hcurveK]
    exact hxy
  -- push the equation through the residue map
  have hcurveRes : ((W₀.map (algebraMap R (v.valuation K).integer)).toAffine).map
      (residueHom v) = redCurve v W₀ := by
    change (W₀.map (algebraMap R (v.valuation K).integer)).map (residueHom v)
      = W₀.map (algebraMap R (R ⧸ v.asIdeal))
    rw [WeierstrassCurve.map_map]
    exact congrArg W₀.map (RingHom.ext fun r ↦ v.residueHom_algebraMap r)
  have h := Equation.map (residueHom v) hOeq
  rwa [hcurveRes] at h

include hE in
/-- Under good reduction, the residues of the coordinates of a `v`-integral point of `E(K)` are
a nonsingular point of the reduced curve. -/
lemma nonsingular_residueHom [(redCurve v W₀).IsElliptic] {x y : K} (hxy : E.Equation x y)
    (hx : v.valuation K x ≤ 1) (hy : v.valuation K y ≤ 1) :
    (redCurve v W₀).Nonsingular (residueHom v ⟨x, hx⟩) (residueHom v ⟨y, hy⟩) :=
  (redCurve v W₀).equation_iff_nonsingular.mp (equation_residueHom v hE hxy hx hy)

section

variable [(redCurve v W₀).IsElliptic]

include hE in
/-- The reduction map `E(K) → Ẽ(R ⧸ v.asIdeal)` at the prime `v`, for an integral model `W₀`
of `E` over `R` with good reduction at `v`: a point with `v`-integral coordinates reduces
coordinatewise (via `residueHom v`), and a point with a pole at `v` (the kernel of reduction)
maps to the point at infinity. -/
noncomputable def red : E.Point → (redCurve v W₀).Point
  | .zero => 0
  | .some x y h =>
      if hx : v.valuation K x ≤ 1 then
        .some (residueHom v ⟨x, hx⟩)
          (residueHom v ⟨y, valuation_le_one_of_equation v hE h.left hx⟩)
          (nonsingular_residueHom v hE h.left hx (valuation_le_one_of_equation v hE h.left hx))
      else 0

@[simp] lemma red_zero : red v hE (0 : E.Point) = 0 := rfl

include hE in
/-- Unfolding lemma for `red` at a `v`-integral point. -/
lemma red_some_of_le {x y : K} {h : E.Nonsingular x y} (hx : v.valuation K x ≤ 1) :
    red v hE (.some x y h)
      = .some (residueHom v ⟨x, hx⟩)
          (residueHom v ⟨y, valuation_le_one_of_equation v hE h.left hx⟩)
          (nonsingular_residueHom v hE h.left hx (valuation_le_one_of_equation v hE h.left hx)) :=
  dif_pos hx

include hE in
/-- Unfolding lemma for `red` at a point with a pole at `v`. -/
lemma red_some_of_not_le {x y : K} {h : E.Nonsingular x y} (hx : ¬ v.valuation K x ≤ 1) :
    red v hE (.some x y h) = 0 :=
  dif_neg hx

end

/-! ### Transport from the completion

The following identifies `red v hE` with the reduction map `adicRed` of the base-changed curve
over the completion `K_v`, along the base change of points `E(K) → E(K_v)` and the residue field
isomorphism `R ⧸ v.asIdeal ≃+* 𝒪_v ⧸ 𝔪_v`.  All group-theoretic properties of `red` follow.
The group structures on the point sets require decidable equality of the base fields
(`[DecidableEq K]`, `[DecidableEq (R ⧸ v.asIdeal)]` in the public statements); the corresponding
instances on the completion and its residue field appear only in private lemmas and are
discharged with `classical` in the proofs of the public ones. -/

section Transport

/- `𝒪_v ⧸ 𝔪_v` as an algebra over `R` (via `𝒪_v`) and over `R ⧸ v.asIdeal` (via the residue
field isomorphism), used only in this section. -/
noncomputable local instance : Algebra R (ResidueField (v.adicCompletionIntegers K)) :=
  ((IsLocalRing.residue (v.adicCompletionIntegers K)).comp
    (algebraMap R (v.adicCompletionIntegers K))).toAlgebra

noncomputable local instance :
    Algebra (R ⧸ v.asIdeal) (ResidueField (v.adicCompletionIntegers K)) :=
  (v.residueFieldEquivAdicCompletionIntegers (K := K)).toRingHom.toAlgebra

local instance : IsScalarTower R (R ⧸ v.asIdeal) (ResidueField (v.adicCompletionIntegers K)) :=
  IsScalarTower.of_algebraMap_eq fun r ↦ (v.residueFieldEquivAdicCompletionIntegers_mk r).symm

local instance : IsScalarTower R R (ResidueField (v.adicCompletionIntegers K)) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- The residue field isomorphism as an `R`-algebra homomorphism. -/
private noncomputable def residueFieldAlgHom :
    (R ⧸ v.asIdeal) →ₐ[R] ResidueField (v.adicCompletionIntegers K) :=
  { (v.residueFieldEquivAdicCompletionIntegers (K := K)).toRingHom with
    commutes' := fun r ↦ v.residueFieldEquivAdicCompletionIntegers_mk r }

/-- The reduced curve over `R ⧸ v.asIdeal`, base changed to `𝒪_v ⧸ 𝔪_v`, is the reduction of the
base-changed integral model. -/
private lemma baseChange_redCurve :
    ((W₀.toAffine ⁄ (ResidueField (v.adicCompletionIntegers K))) : WeierstrassCurve _).toAffine
      = adicRedCurve (W₀.map (algebraMap R (v.adicCompletionIntegers K))) := by
  change W₀.map (algebraMap R (ResidueField (v.adicCompletionIntegers K)))
    = (W₀.map (algebraMap R (v.adicCompletionIntegers K))).map
        (IsLocalRing.residue (v.adicCompletionIntegers K))
  rw [map_map]
  rfl

/-- Valuation compatibility for the difference between a global integral element and a
global field element, viewed in the completed valuation ring. -/
private lemma valued_sub_algebraMap_eq (a : R) (x : K)
    (hx : Valued.v (algebraMap K (v.adicCompletion K) x) ≤ 1) :
    Valued.v ((algebraMap R (v.adicCompletionIntegers K) a
          - (⟨algebraMap K (v.adicCompletion K) x, hx⟩ : v.adicCompletionIntegers K) :
          v.adicCompletionIntegers K) : v.adicCompletion K) =
      v.valuation K (algebraMap R K a - x) := by
  calc
    Valued.v ((algebraMap R (v.adicCompletionIntegers K) a
          - (⟨algebraMap K (v.adicCompletion K) x, hx⟩ : v.adicCompletionIntegers K) :
          v.adicCompletionIntegers K) : v.adicCompletion K)
        = Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K a - x)) := by
            congr 1
            change algebraMap K (v.adicCompletion K) (algebraMap R K a)
              - algebraMap K (v.adicCompletion K) x = _
            rw [map_sub]
    _ = v.valuation K (algebraMap R K a - x) :=
      v.valuedAdicCompletion_eq_valuation' _

/-- Two integral elements of the completion with difference of valuation below one have the
same residue. -/
private lemma residue_algebraMap_eq_of_valuation_sub_lt (a : R) (x : K)
    (hx : Valued.v (algebraMap K (v.adicCompletion K) x) ≤ 1)
    (hax : v.valuation K (algebraMap R K a - x) < 1) :
    IsLocalRing.residue (v.adicCompletionIntegers K)
        (algebraMap R (v.adicCompletionIntegers K) a) =
      IsLocalRing.residue (v.adicCompletionIntegers K)
        ⟨algebraMap K (v.adicCompletion K) x, hx⟩ := by
  refine Ideal.Quotient.eq.mpr ?_
  refine (Valuation.mem_maximalIdeal_iff
    (v := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰))).mpr ?_
  rw [valued_sub_algebraMap_eq v a x hx]
  exact hax

/-- The residue field isomorphism intertwines the two residue maps: `residueHom v` over `K` and
the residue map of `𝒪_v` on the image of a `v`-integral element in the completion. -/
private lemma residueFieldAlgHom_residueHom {x : K} (hx : v.valuation K x ≤ 1)
    (hx' : Valued.v (algebraMap K (v.adicCompletion K) x) ≤ 1) :
    residueFieldAlgHom v (residueHom v ⟨x, hx⟩)
      = IsLocalRing.residue (v.adicCompletionIntegers K)
          ⟨algebraMap K (v.adicCompletion K) x, hx'⟩ := by
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer hx 1
  have ha1 : v.valuation K (algebraMap R K a - x) < 1 := lt_of_lt_of_eq ha Units.val_one
  calc
    residueFieldAlgHom v (residueHom v ⟨x, hx⟩) =
        residueFieldAlgHom v (Ideal.Quotient.mk v.asIdeal a) :=
      congrArg (residueFieldAlgHom v) (residueHom_eq v ha1)
    _ = IsLocalRing.residue (v.adicCompletionIntegers K)
        (algebraMap R (v.adicCompletionIntegers K) a) :=
      v.residueFieldEquivAdicCompletionIntegers_mk a
    _ = IsLocalRing.residue (v.adicCompletionIntegers K)
        ⟨algebraMap K (v.adicCompletion K) x, hx'⟩ :=
      residue_algebraMap_eq_of_valuation_sub_lt v a x hx' ha1

section

variable [DecidableEq (R ⧸ v.asIdeal)]

/-- The transport of points of the reduced curve along the residue field isomorphism. -/
private noncomputable def resPointHom
    [DecidableEq (ResidueField (v.adicCompletionIntegers K))] :
    (redCurve v W₀).Point →+
      (adicRedCurve (W₀.map (algebraMap R (v.adicCompletionIntegers K)))).Point :=
  (Point.congr (baseChange_redCurve v)).toAddMonoidHom.comp
    (Point.map (W' := W₀.toAffine) (residueFieldAlgHom (K := K) v))

private lemma resPointHom_injective
    [DecidableEq (ResidueField (v.adicCompletionIntegers K))] :
    Function.Injective (resPointHom (K := K) v (W₀ := W₀)) := fun a b h ↦ by
  have h' : (Point.congr (baseChange_redCurve v))
        ((Point.map (W' := W₀.toAffine) (residueFieldAlgHom (K := K) v)) a)
      = (Point.congr (baseChange_redCurve v))
        ((Point.map (W' := W₀.toAffine) (residueFieldAlgHom (K := K) v)) b) := h
  exact Point.map_injective (residueFieldAlgHom (K := K) v)
    ((Point.congr (baseChange_redCurve v)).injective h')

end

variable [(redCurve v W₀).IsElliptic]

/-- Good reduction transfers to the base-changed integral model over `𝒪_v`. -/
private local instance isElliptic_map_adicCompletionIntegers :
    (W₀.map (algebraMap R (v.adicCompletionIntegers K))).IsElliptic := by
  have hΔ : Ideal.Quotient.mk v.asIdeal W₀.Δ ≠ 0 := by
    have h1 : IsUnit ((W₀.map (algebraMap R (R ⧸ v.asIdeal))).Δ) := (redCurve v W₀).isUnit_Δ
    rw [map_Δ] at h1
    exact h1.ne_zero
  rw [isElliptic_iff, map_Δ]
  refine (residue_ne_zero_iff_isUnit _).mp fun h0 ↦ ?_
  exact hΔ ((v.residueFieldEquivAdicCompletionIntegers (K := K)).injective
    (by rw [v.residueFieldEquivAdicCompletionIntegers_mk, h0, map_zero]; rfl))

private lemma isElliptic_baseChange_adicCompletion [E.IsElliptic] :
    (((E ⁄ (v.adicCompletion K)) : WeierstrassCurve _).toAffine).IsElliptic :=
  inferInstanceAs ((E.map (algebraMap K (v.adicCompletion K))).IsElliptic)

variable [DecidableEq (R ⧸ v.asIdeal)] [DecidableEq K]

include hE in
/-- **Compatibility of the two reduction maps**: reducing over `K` and transporting to the
residue field of `𝒪_v` is reduction over `K_v` after base change of the point. -/
private lemma adicRed_pointMap [DecidableEq (v.adicCompletion K)]
    [DecidableEq (ResidueField (v.adicCompletionIntegers K))] (P : E.Point) :
    adicRed (map_baseChange_adicCompletionIntegers v hE)
        (E.pointMap (v.adicCompletion K) P)
      = resPointHom v (red v hE P) := by
  match P with
  | .zero =>
      change adicRed (map_baseChange_adicCompletionIntegers v hE)
        (E.pointMap (v.adicCompletion K) 0) = resPointHom v (red v hE 0)
      rw [red_zero, map_zero, map_zero, adicRed_zero]
  | .some x y h =>
      rw [pointMap_some]
      by_cases hx : v.valuation K x ≤ 1
      · -- integral point: both maps reduce coordinatewise
        rw [red_some_of_le v hE hx, adicRed_some_of_not_mem _ (not_exp_two_le v hx)]
        rw [resPointHom, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, Point.map_some,
          Point.congr_some, Point.some.injEq]
        exact ⟨(residueFieldAlgHom_residueHom v hx _).symm,
          (residueFieldAlgHom_residueHom v _ _).symm⟩
      · -- pole: both maps give the point at infinity
        have hx' : exp (2 : ℤ) ≤ Valued.v (algebraMap K (v.adicCompletion K) x) := by
          by_contra h2
          refine hx ?_
          have h1 := (integral_of_not_mem (map_baseChange_adicCompletionIntegers v hE)
            (Equation.map (algebraMap K (v.adicCompletion K)) h.left) h2).1
          rwa [valued_algebraMap v] at h1
        rw [red_some_of_not_le v hE hx, map_zero, adicRed_some_of_mem _ hx']

/-! ### The reduction homomorphism and its behaviour on torsion -/

variable [E.IsElliptic] [CharZero K]

include hE in
/-- **The reduction map is additive.** -/
lemma red_add (P Q : E.Point) : red v hE (P + Q) = red v hE P + red v hE Q := by
  classical
  have := isElliptic_baseChange_adicCompletion v (E := E)
  apply resPointHom_injective (K := K) v
  rw [map_add, ← adicRed_pointMap v hE, ← adicRed_pointMap v hE, ← adicRed_pointMap v hE,
    map_add, adicRed_add]

include hE in
/-- **The reduction homomorphism** `E(K) →+ Ẽ(R ⧸ v.asIdeal)` at a prime `v` of good
reduction. -/
noncomputable def redHom : E.Point →+ (redCurve v W₀).Point :=
  AddMonoidHom.mk' (red v hE) (red_add v hE)

@[simp] lemma coe_redHom : ⇑(redHom v hE) = red v hE := rfl

omit [DecidableEq (R ⧸ v.asIdeal)] in
include hE in
/-- **Reduction is injective on torsion**: a torsion point of `E(K)` reducing to `0` at a prime
`v` of good reduction is `0`, provided the residue characteristic `p` satisfies
`(p : R) ∈ v.asIdeal` and `(p : R) ∉ v.asIdeal ^ (p - 1)` — that is, `e ≤ p - 2` for the
ramification index `e` of `v` over `p` (e.g. `p` odd and `v` unramified). -/
lemma eq_zero_of_isOfFinAddOrder_of_red_eq_zero {p : ℕ} (hp : p.Prime)
    (hpmem : (p : R) ∈ v.asIdeal) (hpram : (p : R) ∉ v.asIdeal ^ (p - 1)) {P : E.Point}
    (hP : IsOfFinAddOrder P) (h0 : red v hE P = 0) : P = 0 := by
  classical
  have := isElliptic_baseChange_adicCompletion v (E := E)
  have h0' : adicRed (map_baseChange_adicCompletionIntegers v hE)
      (E.pointMap (v.adicCompletion K) P) = 0 := by
    rw [adicRed_pointMap v hE, h0, map_zero]
  have hmem := natCast_mem_maximalIdeal (K := K) v hpmem
  have hP0 := eq_zero_of_isOfFinAddOrder_of_adicRed_eq_zero
    (map_baseChange_adicCompletionIntegers v hE) hp hmem
    (fun hc ↦ hpram ((natCast_mem_maximalIdeal_pow_iff (K := K) v).mp hc))
    (AddMonoidHom.isOfFinAddOrder _ hP) h0'
  exact pointMap_injective E (v.adicCompletion K) (hP0.trans (map_zero _).symm)

include hE in
/-- If the reduction at a good prime `v` of a torsion point is annihilated by `m`, then so is
the point itself (hypotheses on the residue characteristic as in
`eq_zero_of_isOfFinAddOrder_of_red_eq_zero`). -/
lemma nsmul_eq_zero_of_red_nsmul_eq_zero {p : ℕ} (hp : p.Prime) (hpmem : (p : R) ∈ v.asIdeal)
    (hpram : (p : R) ∉ v.asIdeal ^ (p - 1)) {P : E.Point} (hP : IsOfFinAddOrder P) {m : ℕ}
    (h : m • red v hE P = 0) : m • P = 0 :=
  eq_zero_of_isOfFinAddOrder_of_red_eq_zero v hE hp hpmem hpram hP.nsmul
    (by simpa only [← coe_redHom v hE, map_nsmul] using h)

include hE in
/-- **Reduction preserves the order of a torsion point** (hypotheses on the residue
characteristic as in `eq_zero_of_isOfFinAddOrder_of_red_eq_zero`). -/
lemma addOrderOf_red {p : ℕ} (hp : p.Prime) (hpmem : (p : R) ∈ v.asIdeal)
    (hpram : (p : R) ∉ v.asIdeal ^ (p - 1)) {P : E.Point} (hP : IsOfFinAddOrder P) :
    addOrderOf (red v hE P) = addOrderOf P := by
  classical
  have := isElliptic_baseChange_adicCompletion v (E := E)
  have hmem := natCast_mem_maximalIdeal (K := K) v hpmem
  calc addOrderOf (red v hE P)
      = addOrderOf (resPointHom v (red v hE P)) :=
        (addOrderOf_injective _ (resPointHom_injective (K := K) v) _).symm
    _ = addOrderOf (adicRed (map_baseChange_adicCompletionIntegers v hE)
          (E.pointMap (v.adicCompletion K) P)) := by rw [adicRed_pointMap v hE]
    _ = addOrderOf (E.pointMap (v.adicCompletion K) P) :=
        addOrderOf_adicRed (map_baseChange_adicCompletionIntegers v hE) hp hmem
          (fun hc ↦ hpram ((natCast_mem_maximalIdeal_pow_iff (K := K) v).mp hc))
          (AddMonoidHom.isOfFinAddOrder _ hP)
    _ = addOrderOf P := addOrderOf_injective _ (pointMap_injective E (v.adicCompletion K)) P

omit [DecidableEq (R ⧸ v.asIdeal)] in
include hE in
/-- The order of a torsion point of `E(K)` divides the number of points of the reduction at a
good prime `v` (hypotheses on the residue characteristic as in
`eq_zero_of_isOfFinAddOrder_of_red_eq_zero`).  This is nontrivial only when the residue field
is finite, which makes `Ẽ(R ⧸ v.asIdeal)` a finite group. -/
lemma addOrderOf_dvd_natCard_red {p : ℕ} (hp : p.Prime) (hpmem : (p : R) ∈ v.asIdeal)
    (hpram : (p : R) ∉ v.asIdeal ^ (p - 1)) {P : E.Point} (hP : IsOfFinAddOrder P) :
    addOrderOf P ∣ Nat.card (redCurve v W₀).Point := by
  classical
  rw [← addOrderOf_red v hE hp hpmem hpram hP]
  exact addOrderOf_dvd_natCard _

end Transport

end WeierstrassCurve.Affine

end
