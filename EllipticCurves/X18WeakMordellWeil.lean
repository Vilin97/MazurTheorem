/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import EllipticCurves.Mathlib.Basic
public import EllipticCurves.Mathlib.EllipticCurvePoint
public import Mathlib

@[expose] public section

/-!
# The Weak Mordell-Weil Theorem

The goal of this file is to show that `E(K)/2E(K)` is finite, where `E` is an elliptic curve
given by a Weierstrass equation `y² = x³ + a₂x² + a₄x + a₆ =: f(x)` (so with `a₁ = a₃ = 0`,
which is always achievable when the characteristic is not `2`)
over the fraction field `K` of a Dedekind domain `R`, under finiteness hypotheses — finite
class group and finitely generated unit group for the rings of integers of the field factors
of `K[X]/⟨f⟩` — that are theorems when `K` is a number field.

We use the `x-T` map approach.

The general-purpose material developed along the way, which has nothing to do with elliptic
curves, lives in `EllipticCurves.Mathlib.Basic`.

1. Let `A := K[X]/⟨f(X)⟩` be the étale algebra defined by `f`.
   => done.
2. Define `M := Aˣ⧸squares` and the map `μ : E(K) → M` given by `μ 0 = 1`,
   `μ (x, y) = (x-θ) mod squares` if `f(x) ≠ 0`, else `f'(θ) mod squares`.
   => done (the bare map is defined as `μ₀`).
3. Show that `μ` is a group homomorphism.
   => done.
4. Show that `ker μ = 2E(K)`.
   => done.
5. Show that `im μ` is contained in the kernel of the norm map on square classes.
   => done, via `AdjoinRoot.norm_mk_eq_resultant`, which says that the norm of
   `AdjoinRoot.mk g p` for monic `g` is the resultant of `g` and `p`
   (in `EllipticCurves.Mathlib.Basic`).
   Note that this step is *not* needed for the finiteness result (Steps 6 and 7 do not use
   it); it is included because the norm condition cuts down the Selmer group in explicit
   computations.
6. Show that `im μ ⊆ A(S,2)` for a suitable finite set `S` of "bad" primes.
   => done, as `range_μ_le_selmerGroupA` at the end of the file, for `E` over the fraction field
   of a Dedekind domain and for *any* `S` outside which the coefficients of the cubic are
   integral and `disc f` is a unit. Such sets are provided by `badPrimes` (primes dividing `2`
   or `Δ`, or occurring in a coefficient denominator); the refined sets `discBadPrimes` and
   `badPrimes₂` defined alongside it feed the sharpened Selmer-group bound of
   `EllipticCurves.SelmerGroup`.
7. Show that `A(S,2)` is finite, and conclude that `E(K)/2E(K)` is finite.
   This generic finiteness step is deliberately omitted from this X18 slice. The explicit
   X18 certificate supplies the finite square-class calculation instead; this file stops at
   `range_μ_le_selmerGroupA`.
-/

/-!
### Two commutative-ring identities

These are used in Step 3 (`μ` is a homomorphism); they encode the multiplicativity of the
`x - T` map on the level of coordinates.
-/

section CommRing

variable {R : Type*} [CommRing R]

/-- If `a * b * c = 0`, then `a * b + a * c + b * c` is a square root of the product
of the `b * c - a` and its two analogues. -/
lemma sq_add_add_eq_mul_mul_of_mul_mul_eq_zero {a b c : R} (h : a * b * c = 0) :
    (a * b + a * c + b * c) ^ 2 = (b * c - a) * (a * c - b) * (a * b - c) := by
  linear_combination (a ^ 2 - a * b * c + 2 * a + b ^ 2 + 2 * b + c ^ 2 + 2 * c + 1) * h

/-- If `a * d = 0` and `b * c = d - e ^ 2 * a`, then `d + e * a` is a square root
of `(d - a) * b * c`. -/
lemma sq_add_mul_eq_mul_mul_of_mul_eq_zero {a b c d e : R} (had : a * d = 0)
    (h : b * c = d - e ^ 2 * a) : (d + e * a) ^ 2 = (d - a) * b * c := by
  grobner

end CommRing

namespace WeierstrassCurve.Affine

variable {K : Type*} [Field K] (W : Affine K)

lemma ringChar_ne_two [W.IsElliptic] [W.IsCharNeTwoNF] : ringChar K ≠ 2 := by
  have h := W.isUnit_Δ.ne_zero
  contrapose! h
  have h2 : (2 : K) = 0 := by
    have := ringChar.Nat.cast_ringChar (R := K)
    rw [h] at this
    exact_mod_cast this
  rw [Δ_of_isCharNeTwoNF W]
  linear_combination (-32 * W.a₂ ^ 3 * W.a₆ + 8 * W.a₂ ^ 2 * W.a₄ ^ 2 - 32 * W.a₄ ^ 3
    - 216 * W.a₆ ^ 2 + 144 * W.a₂ * W.a₄ * W.a₆) * h2

/-!
### Step 1: define `A`
-/

open Polynomial

/-- The polynomial on the right hand side of a Weierstrass equation with `a₁ = a₃ = 0`. -/
noncomputable abbrev f : K[X] := X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆

lemma natDegree_f : W.f.natDegree = 3 := by
  simp only [f]
  compute_degree!

lemma monic_f : W.f.Monic := by
  simp only [f]
  monicity!

lemma f_ne_zero : W.f ≠ 0 := W.monic_f.ne_zero

lemma degree_lt_degree_f {p : K[X]} (hp : p.natDegree ≤ 2) : p.degree < W.f.degree :=
  degree_lt_degree <| by rw [natDegree_f]; lia

lemma degree_f : W.f.degree = 3 := by
  rw [degree_eq_natDegree W.f_ne_zero, natDegree_f]; rfl

/-- The discriminant of the cubic `f`, in terms of the coefficients of `W`. -/
lemma discr_f : W.f.discr = W.a₂ ^ 2 * W.a₄ ^ 2 - 4 * W.a₄ ^ 3 - 4 * W.a₂ ^ 3 * W.a₆
    - 27 * W.a₆ ^ 2 + 18 * W.a₂ * W.a₄ * W.a₆ := by
  rw [Polynomial.discr_of_degree_eq_three W.degree_f]
  simp only [f, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

/-- In char ≠ 2 normal form, `Δ = 16 · disc f`; in particular the two agree up to a unit away
from `2`, but *not* at even places, where `disc f` is the finer invariant. -/
lemma Δ_eq_discr_f [W.IsCharNeTwoNF] : W.Δ = 16 * W.f.discr := by
  rw [Δ_of_isCharNeTwoNF W, W.discr_f]; ring

lemma discr_f_ne_zero [W.IsElliptic] [W.IsCharNeTwoNF] : W.f.discr ≠ 0 := fun h ↦
  W.isUnit_Δ.ne_zero (by rw [W.Δ_eq_discr_f, h, mul_zero])

lemma derivative_f : derivative W.f = C 3 * X ^ 2 + C (2 * W.a₂) * X + C W.a₄ := by
  simp [f, C_ofNat]
  ring

/-- The derivative of the cubic `f` is honestly quadratic when `3 ≠ 0` in `K`. -/
lemma natDegree_derivative_f (h3 : (3 : K) ≠ 0) : (derivative W.f).natDegree = 2 :=
  W.derivative_f ▸ natDegree_quadratic h3

lemma separable_f [W.IsElliptic] [W.IsCharNeTwoNF] : W.f.Separable := by
  have hΔ : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
  rw [separable_def', derivative_f, f]
  refine ⟨C (W.Δ)⁻¹ * (C (288 * W.a₄ - 96 * W.a₂ ^ 2) * X
      + C (240 * W.a₂ * W.a₄ - 64 * W.a₂ ^ 3 - 432 * W.a₆)),
    C (W.Δ)⁻¹ * (C (32 * W.a₂ ^ 2 - 96 * W.a₄) * X ^ 2
      + C (32 * W.a₂ ^ 3 - 112 * W.a₂ * W.a₄ + 144 * W.a₆) * X
      + C (16 * W.a₂ ^ 2 * W.a₄ - 64 * W.a₄ ^ 2 + 48 * W.a₂ * W.a₆)), ?_⟩
  rw [mul_assoc, mul_assoc (C (W.Δ)⁻¹), ← mul_add]
  refine mul_left_cancel₀ (C_ne_zero.mpr hΔ) ?_
  rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hΔ, Δ_of_isCharNeTwoNF]
  simp only [C_eq_algebraMap]
  algebra

lemma squarefree_f [W.IsElliptic] [W.IsCharNeTwoNF] : Squarefree W.f :=
  (separable_f W).squarefree

lemma eval_f (x : K) : W.f.eval x = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by simp [f]

lemma map_eval_f {L : Type*} [CommRing L] [Algebra K L] (x : K) :
    algebraMap K L (W.f.eval x) = algebraMap K L x ^ 3 +
      algebraMap K L W.a₂ * algebraMap K L x ^ 2 +
      algebraMap K L W.a₄ * algebraMap K L x + algebraMap K L W.a₆ := by
  simp [f]

lemma equation_iff_eval_f_eq_sq [W.IsCharNeTwoNF] (x y : K) :
    W.Equation x y ↔ W.f.eval x = y ^ 2 := by
  rw [equation_iff x y, eq_comm]
  simp [f]

@[simp]
lemma negY_of_isCharNeTwoNF [W.IsCharNeTwoNF] (x y : K) : W.negY x y = -y := by
  rw [negY, a₁_of_isCharNeTwoNF, a₃_of_isCharNeTwoNF]
  ring

/-- On a point of `W`, the value `f x` is a square, so it vanishes exactly when `y` does. -/
lemma ne_zero_of_eval_f_ne_zero [W.IsCharNeTwoNF] {x y : K} (h : W.Equation x y)
    (hx : W.f.eval x ≠ 0) : y ≠ 0 :=
  fun h0 ↦ hx <| by simp [(equation_iff_eval_f_eq_sq W x y).mp h, h0]

/-- The quotient of `f` by `X - x`. -/
noncomputable abbrev fCofactor (x : K) : K[X] :=
  X ^ 2 + C (x + W.a₂) * X + C (x ^ 2 + W.a₂ * x + W.a₄)

lemma natDegree_fCofactor (x : K) : (W.fCofactor x).natDegree = 2 := by
  simp only [fCofactor]
  compute_degree!

lemma monic_fCofactor (x : K) : (W.fCofactor x).Monic := by
  simp only [fCofactor]
  monicity!

lemma degree_lt_degree_fCofactor (x : K) {p : K[X]} (hp : p.natDegree ≤ 1) :
    p.degree < (W.fCofactor x).degree :=
  degree_lt_degree <| by rw [natDegree_fCofactor]; lia

lemma eval_fCofactor_self (x : K) :
    (W.fCofactor x).eval x = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ := by
  simp [fCofactor]
  ring

lemma fCofactor_mul_eq (x : K) : W.fCofactor x * (X - C x) = W.f - C (W.f.eval x) := by
  simp only [fCofactor, f, eval_add, eval_pow, eval_X, eval_mul, eval_C, map_add, map_pow,
    map_mul, add_sub_add_right_eq_sub]
  algebra

lemma f_eq_mul_of_eval_eq_zero {x : K} (hx : W.f.eval x = 0) :
    W.f = W.fCofactor x * (X - C x) := by
  simp [fCofactor_mul_eq, hx]

lemma discr_fCofactor (x : K) :
    (W.fCofactor x).discr = (x + W.a₂) ^ 2 - 4 * (x ^ 2 + W.a₂ * x + W.a₄) := by
  have hdeg : (W.fCofactor x).degree = 2 := by
    rw [degree_eq_natDegree (W.monic_fCofactor x).ne_zero, W.natDegree_fCofactor x]; rfl
  rw [discr_of_degree_eq_two hdeg]
  simp only [fCofactor, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

/-- If `x` is a root of `f`, splitting off the factor `X - x` writes `disc f` as
`(fCofactor x).discr * f'(x) ^ 2`. -/
lemma discr_f_eq_discr_fCofactor_mul_sq {x : K} (hx : W.f.eval x = 0) :
    W.f.discr = (W.fCofactor x).discr * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ^ 2 := by
  conv_lhs => rw [W.f_eq_mul_of_eval_eq_zero hx, mul_comm]
  rw [discr_X_sub_C_mul (W.monic_fCofactor x) (by rw [W.natDegree_fCofactor]; norm_num) x,
    W.eval_fCofactor_self x]

/- Dividing the relation `(r X + s)² ≡ x - X mod (fCofactor x)` by `r²` yields the polynomial
identity certifying that a point with `2`-torsion `x`-coordinate `x` is divisible by `2`
(used in Step 4). -/
private lemma f_dvd_of_fCofactor_dvd {x r s : K} (hx : W.f.eval x = 0) (hr : r ≠ 0)
    (hdvd : W.fCofactor x ∣ (C r * X + C s) ^ 2 - (C x - X)) :
    W.f ∣ (X - C (-s / r)) ^ 2 * (X - C x) - -(C (1 / r) * X + C (-x / r)) ^ 2 := by
  obtain ⟨q, hq⟩ := hdvd
  apply_fun (· * (X - C x)) at hq
  rw [mul_right_comm, ← f_eq_mul_of_eval_eq_zero _ hx] at hq
  replace hq : q * W.f = ((C r * X + C s) ^ 2 - (C x - X)) * (X - C x) := by
    rw [mul_comm]; exact hq.symm
  refine ⟨C (1 / r ^ 2) * q, ?_⟩
  rw [eq_comm, mul_comm W.f]
  apply_fun (C (r ^ 2) * ·) using mul_right_injective₀ <| by simp [hr]
  dsimp only
  rw [← mul_assoc, ← mul_assoc, ← map_mul]
  rw [mul_one_div_cancel <| pow_ne_zero 2 hr, map_one, one_mul, hq]
  conv_rhs =>
    rw [sub_neg_eq_add, mul_add, ← mul_assoc, map_pow, ← mul_pow, mul_sub (C r), ← map_mul,
      mul_div_cancel₀ _ hr]
    enter [2]
    rw [← mul_pow, mul_add, ← mul_assoc, ← map_mul, mul_one_div_cancel hr, map_one, one_mul,
      ← map_mul, mul_div_cancel₀ _ hr]
  simp only [C_eq_algebraMap]
  algebra

lemma fCofactor_eq_of_f_eq {xP xQ xR : K} (hf : W.f = (X - C xP) * (X - C xQ) * (X - C xR)) :
    W.fCofactor xP = (X - C xQ) * (X - C xR) ∧ W.fCofactor xQ = (X - C xP) * (X - C xR) ∧
      W.fCofactor xR = (X - C xP) * (X - C xQ) := by
  have key {u v w : K} (h : W.f = (X - C u) * ((X - C v) * (X - C w))) :
      W.fCofactor u = (X - C v) * (X - C w) := by
    have h₀ : W.f.eval u = 0 := by rw [h]; simp
    refine mul_left_cancel₀ (X_sub_C_ne_zero u) ?_
    rw [← h, W.f_eq_mul_of_eval_eq_zero h₀, mul_comm]
  exact ⟨key <| by rw [hf]; ring, key <| by rw [hf]; ring, key <| by rw [hf]; ring⟩

lemma deriv_f_ne_zero [W.IsElliptic] [W.IsCharNeTwoNF] {x : K} (hx : W.f.eval x = 0) :
    3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ ≠ 0 := by
  rw [eval_f] at hx
  have := W.Δ_of_isCharNeTwoNF ▸ W.isUnit_Δ |>.ne_zero
  contrapose! this
  linear_combination ((288 * W.a₄ - 96 * W.a₂ ^ 2) * x
      + (240 * W.a₂ * W.a₄ - 64 * W.a₂ ^ 3 - 432 * W.a₆)) * hx
    + ((32 * W.a₂ ^ 2 - 96 * W.a₄) * x ^ 2 + (32 * W.a₂ ^ 3 - 112 * W.a₂ * W.a₄ + 144 * W.a₆) * x
      + (16 * W.a₂ ^ 2 * W.a₄ - 64 * W.a₄ ^ 2 + 48 * W.a₂ * W.a₆)) * this

/-- The étale algebra associated to a Weierstrass curve with `a₁ = a₃ = 0`. -/
abbrev A : Type _ := AdjoinRoot W.f

lemma finrank_A : Module.finrank K W.A = 3 := by
  rw [(AdjoinRoot.powerBasis W.f_ne_zero).finrank, AdjoinRoot.powerBasis_dim, natDegree_f]

lemma exists_mk_eq (a : W.A) :
    ∃ r s t, a = AdjoinRoot.mk W.f (C r * X ^ 2 + C s * X + C t) := by
  obtain ⟨p, hp, rfl⟩ := AdjoinRoot.exists_degree_lt_mk_eq W.monic_f a
  rw [degree_eq_natDegree W.monic_f.ne_zero, natDegree_f] at hp
  exact ⟨_, _, _, congrArg (AdjoinRoot.mk W.f) <|
    eq_quadratic_of_degree_le_two <| Order.lt_succ_iff.mp hp⟩

lemma exists_X_sub_C_mul_eq (r s t : K) (hr : r ≠ 0) :
    ∃ ξ l m, AdjoinRoot.mk W.f (X - C ξ) * AdjoinRoot.mk W.f (C r * X ^ 2 + C s * X + C t) =
       AdjoinRoot.mk W.f (C l * X + C m) := by
  conv => enter [1, ξ, 1, l, 1, m]; rw [← map_mul, ← sub_eq_zero, ← map_sub]
  have H (ξ l m : K) : (X - C ξ) * (C r * X ^ 2 + C s * X + C t) - (C l * X + C m) =
      C r * W.f + (C (-ξ * r + s - W.a₂ * r) * X ^ 2 + C (-ξ * s - l - W.a₄ * r + t) * X
        + C (-ξ * t - m - W.a₆ * r)) := by
    simp only [f, C_eq_algebraMap]
    algebra
  conv =>
    enter [1, ξ, 1, l, 1, m]
    rw [H, map_add, map_mul]
    enter [1, 1, 2]
    rw [AdjoinRoot.mk_self]
  simp only [mul_zero, zero_add]
  suffices ∃ ξ l m, -ξ * r + s - W.a₂ * r = 0 ∧ -ξ * s - l - W.a₄ * r + t = 0 ∧
      -ξ * t - m - W.a₆ * r = 0 by
    obtain ⟨ξ, l, m, h₂, h₁, h₀⟩ := this
    refine ⟨ξ, l, m, ?_⟩
    rw [h₂, h₁, h₀]
    simp
  refine ⟨s / r - W.a₂, t - W.a₄ * r - s ^ 2 / r + W.a₂ * s,
    -W.a₆ * r - t * s / r + W.a₂ * t, ?_, ?_, ?_⟩ <;> field

/-- The étale algebra associated to the cofactor of `f`. -/
abbrev A' (x : K) : Type _ := AdjoinRoot (W.fCofactor x)

lemma exists_mk_eq' {x : K} (a : W.A' x) :
    ∃ r s, a = AdjoinRoot.mk (W.fCofactor x) (C r * X + C s) := by
  obtain ⟨p, hp, rfl⟩ := AdjoinRoot.exists_degree_lt_mk_eq (W.monic_fCofactor x) a
  rw [degree_eq_natDegree (W.monic_fCofactor x).ne_zero, natDegree_fCofactor] at hp
  exact ⟨_, _, congrArg (AdjoinRoot.mk (W.fCofactor x)) <|
    eq_X_add_C_of_natDegree_le_one <| natDegree_le_of_degree_le <| Order.lt_succ_iff.mp hp⟩

/-- The norm of `x - θ` is `f x`. -/
lemma norm_mk_C_sub_X (x : K) : Algebra.norm K (AdjoinRoot.mk W.f (C x - X)) = W.f.eval x := by
  have hd : (C x - X).natDegree = 1 := by compute_degree!
  rw [AdjoinRoot.norm_mk_eq_resultant W.monic_f, hd, resultant_C_sub_X _ _ _ le_rfl]

/-- If `x` is a root of `f`, then the norm of `x - θ + fCofactor x`, which is the element
representing `f' θ` in this case, is the square `(f' x)²`. -/
lemma norm_mk_C_sub_X_add_fCofactor {x : K} (hx : W.f.eval x = 0) :
    Algebra.norm K (AdjoinRoot.mk W.f (C x - X + W.fCofactor x))
      = (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ^ 2 := by
  have hq : (W.fCofactor x).natDegree = 2 := W.natDegree_fCofactor x
  have hqx : (W.fCofactor x).eval x = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ :=
    W.eval_fCofactor_self x
  have hp : (C x - X + W.fCofactor x).natDegree = 2 := by
    simp only [fCofactor]
    compute_degree!
  have hpx : (C x - X + W.fCofactor x).eval x = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ := by
    rw [eval_add, ← hqx]
    simp
  rw [AdjoinRoot.norm_mk_eq_resultant W.monic_f, hp, W.natDegree_f]
  conv_lhs => rw [W.f_eq_mul_of_eval_eq_zero hx]
  rw [show (3 : ℕ) = (W.fCofactor x).natDegree + (X - C x).natDegree by
        rw [hq, natDegree_X_sub_C],
    resultant_mul_left _ _ _ 2 hp.le, hq, natDegree_X_sub_C]
  -- the factor coming from `X - C x` is `p.eval x`
  rw [show (X - C x) = (X - C x) ^ 1 by rw [pow_one],
    resultant_X_sub_C_pow_left _ _ _ _ hp.le, pow_one, hpx]
  -- the factor coming from `fCofactor x` is `(C x - X).resultant`, since `fCofactor x ≡ 0`
  have hres : (W.fCofactor x).resultant (C x - X) 2 2 = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ := by
    have h := resultant_add_right_deg (W.fCofactor x) (C x - X) 2 1 1 (by compute_degree!)
    simp only [show (1 : ℕ) + 1 = 2 from rfl, pow_one] at h
    rw [h, show (W.fCofactor x).coeff 2 = 1 by
        rw [← hq]; exact (W.monic_fCofactor x).coeff_natDegree,
      one_mul, resultant_C_sub_X _ _ _ hq.le, hqx]
  rw [show C x - X + W.fCofactor x = (C x - X) + W.fCofactor x * 1 by ring,
    resultant_add_mul_right (W.fCofactor x) (C x - X) 1 2 2 (by simp) hq.le, hres]
  ring

/-- The class of `f'` in `K[X]/⟨g⟩`, for any modulus `g` (e.g. `f` itself or one of its
irreducible factors), is `3 θ² + 2 a₂ θ + a₄`, where `θ` is the image of `X`. -/
lemma mk_derivative_f (g : K[X]) : AdjoinRoot.mk g (derivative W.f) =
    3 * AdjoinRoot.root g ^ 2 + 2 * algebraMap K (AdjoinRoot g) W.a₂ * AdjoinRoot.root g
      + algebraMap K (AdjoinRoot g) W.a₄ := by
  rw [derivative_f]
  simp [AdjoinRoot.mk_C, map_ofNat, ← AdjoinRoot.algebraMap_eq]

/-- The norm of `f' θ` is `-disc f` (this needs `3 ≠ 0` in `K`, so that `f'` is honestly
quadratic). -/
lemma norm_mk_derivative_f (h3 : (3 : K) ≠ 0) :
    Algebra.norm K (AdjoinRoot.mk W.f (derivative W.f)) = -W.f.discr := by
  have h := Polynomial.resultant_deriv (f := W.f)
    (by rw [← natDegree_pos_iff_degree_pos, natDegree_f]; norm_num)
  rw [natDegree_f, W.monic_f.leadingCoeff, mul_one] at h
  norm_num at h
  rw [AdjoinRoot.norm_mk_eq_resultant W.monic_f, W.natDegree_derivative_f h3, natDegree_f, h]

/-- The Chinese Remainder Theorem isomorphism `K[X]⧸f ≃ K × K[X]/cf`, where `cf` is the cofactor
`f / (X - x)`. -/
noncomputable def equivProdA' [W.IsElliptic] [W.IsCharNeTwoNF] {x : K} (hx : W.f.eval x = 0) :
    W.A ≃+* K × W.A' x :=
  let eA : W.A ≃+* K[X] ⧸ (Ideal.span {X - C x} * Ideal.span {W.fCofactor x}) :=
    Ideal.quotEquivOfEq <| by
      rw [Ideal.span_singleton_mul_span_singleton, mul_comm, ← W.f_eq_mul_of_eval_eq_zero hx]
  have H : IsCoprime (Ideal.span {X - C x}) (Ideal.span {W.fCofactor x}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mpr <|
      (W.f_eq_mul_of_eval_eq_zero hx ▸ separable_f W).isCoprime.symm
  eA.trans <|
    (Ideal.quotientMulEquivQuotientProd (Ideal.span {X - C x}) (Ideal.span {W.fCofactor x})
      H).trans <|
    RingEquiv.prodCongr (Polynomial.quotientSpanXSubCAlgEquiv x |>.toRingEquiv) (RingEquiv.refl _)

lemma equivProdA'_apply [W.IsElliptic] [W.IsCharNeTwoNF] {x : K} (hx : W.f.eval x = 0) (p : K[X]) :
    W.equivProdA' hx (AdjoinRoot.mk W.f p) = (p.eval x, AdjoinRoot.mk (W.fCofactor x) p) :=
  rfl

lemma mk_eq_mk_iff [W.IsElliptic] [W.IsCharNeTwoNF] {x : K} (hx : W.f.eval x = 0) {p q : K[X]} :
    AdjoinRoot.mk W.f p = AdjoinRoot.mk W.f q ↔
      p.eval x = q.eval x ∧ AdjoinRoot.mk (W.fCofactor x) p = AdjoinRoot.mk (W.fCofactor x) q := by
  rw [← EquivLike.apply_eq_iff_eq <| W.equivProdA' hx]
  simpa only [equivProdA'_apply] using Prod.mk_inj

lemma isUnit_mk_iff [W.IsElliptic] [W.IsCharNeTwoNF] {x : K} (hx : W.f.eval x = 0) {p : K[X]} :
    IsUnit (AdjoinRoot.mk W.f p) ↔
      IsUnit (p.eval x) ∧ IsUnit (AdjoinRoot.mk (W.fCofactor x) p) := by
  let e := W.equivProdA' hx
  refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩
  · have : IsUnit (e _) := e.toRingHom.isUnit_map H
    rwa [W.equivProdA'_apply hx, Prod.isUnit_iff] at this
  · have : IsUnit (eval x p, AdjoinRoot.mk (W.fCofactor x) p) := by rwa [Prod.isUnit_iff]
    have : IsUnit (e.symm _) := e.symm.toRingHom.isUnit_map this
    convert this
    rw [RingEquiv.eq_symm_apply, W.equivProdA'_apply hx]

variable {W}

lemma isUnit_mk_sub_X_of_eval_f_ne_zero {x : K} (h : W.f.eval x ≠ 0) :
    IsUnit <| AdjoinRoot.mk W.f (C x - X) := by
  refine .of_mul_eq_one (AdjoinRoot.mk W.f (C (W.f.eval x)⁻¹ * W.fCofactor x)) ?_
  rw [← map_mul, mul_left_comm,
    show (1 : W.A) = AdjoinRoot.mk W.f (1 - C (eval x W.f)⁻¹ * W.f) by simp]
  congr 1
  have h1 : (C x - X) * W.fCofactor x = C (W.f.eval x) - W.f := by
    linear_combination -W.fCofactor_mul_eq x
  rw [h1, mul_sub, ← C_mul, inv_mul_cancel₀ h, map_one]

section

variable [W.IsCharNeTwoNF]

lemma y_eq_zero_of_eval_f_eq_zero {x y : K} (h : W.Equation x y) (hf : W.f.eval x = 0) :
    y = 0 := by
  rwa [equation_iff_eval_f_eq_sq, hf, eq_comm, sq_eq_zero_iff] at h

variable [W.IsElliptic]

lemma isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero {x : K} (h : W.f.eval x = 0) :
    IsUnit <| AdjoinRoot.mk W.f <| C x - X + W.fCofactor x := by
  rw [isUnit_mk_iff W h]
  have H₀ : 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ ≠ 0 := deriv_f_ne_zero W h
  have H₁ : eval x (C x - X + W.fCofactor x) = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ := by
    rw [eval_add, W.eval_fCofactor_self]; simp
  have H₂ : (AdjoinRoot.mk (W.fCofactor x)) (C x - X + W.fCofactor x) =
      AdjoinRoot.mk (W.fCofactor x) (C x - X) := by
    simp
  rw [H₁, H₂, isUnit_iff_ne_zero]
  refine ⟨H₀, ?_⟩
  let u := AdjoinRoot.mk (W.fCofactor x) <|
    C (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)⁻¹ * (X + C (2 * x + W.a₂))
  rw [isUnit_iff_exists_inv]
  refine ⟨u, ?_⟩
  rw [← map_mul]
  have : (C x - X) * (C (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)⁻¹ * (X + C (2 * x + W.a₂))) =
      C (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)⁻¹ * (-W.fCofactor x) + 1 := by
    rw [mul_left_comm]
    apply_fun (C (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) * ·) using
      mul_right_injective₀ <| C_ne_zero.mpr H₀
    dsimp only
    rw [mul_add _ _ 1]
    simp_rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ H₀, map_one, one_mul, mul_one]
    simp only [C_eq_algebraMap, fCofactor]
    algebra
  rw [this, map_add, map_one, map_mul, map_neg]
  simp


/-- The point `(x, 0)` at a root of `f` lies on the curve. -/
lemma nonsingular_of_eval_f_eq_zero {x : K} (hx : W.f.eval x = 0) :
    W.Nonsingular x 0 :=
  (equation_iff_nonsingular_of_Δ_ne_zero W.isUnit_Δ.ne_zero).mp
    (by rw [equation_iff_eval_f_eq_sq, hx]; ring)

end

/-!
### Step 2: define `M` and `μ` as a plain map `μ₀`
-/

/-- The group of square classes of units of `W.A`. -/
abbrev M : Type _ := Units.modPow W.A 2

/- `inferInstance` succeeds here, but instance search does not find this instance at the use
sites (e.g., for `mul_right_comm` below) unless it is declared. -/
noncomputable instance : CommGroup W.M := inferInstance

lemma M.sq_eq_one (m : W.M) : m ^ 2 = 1 := Units.modPow.pow_eq_one m

lemma M.mul_self (m : W.M) : m * m = 1 := by rw [← sq, sq_eq_one]

@[simp] lemma M.inv_eq_self (m : W.M) : m⁻¹ = m := inv_eq_of_mul_eq_one_right (M.mul_self m)

variable [DecidableEq K] [W.IsCharNeTwoNF]

section μ₀

variable [W.IsElliptic]

/-- The descent or `x - T` map on `x`-coordinates: it sends `x` to the square class of
`x - T` if `f x ≠ 0`, and to the square class of `f' T` otherwise. -/
noncomputable def μX (x : K) : W.M :=
  if hx : W.f.eval x = 0
    then (isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero hx).unit
    else (isUnit_mk_sub_X_of_eval_f_ne_zero hx).unit

@[simp] lemma μX_of_eval_f_eq_zero {x : K} (hx : W.f.eval x = 0) :
    W.μX x = (isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero hx).unit := by
  simp only [μX, dif_pos hx]

@[simp] lemma μX_of_eval_f_ne_zero {x : K} (hx : W.f.eval x ≠ 0) :
    W.μX x = (isUnit_mk_sub_X_of_eval_f_ne_zero hx).unit := by
  simp only [μX, dif_neg hx]

/-- The descent or `x - T` map `μ₀` on the group of points of an affine Weierstrass curve.
This is a plain map; it is upgraded to a group homomorphism `μ` below. -/
noncomputable def μ₀ : W.Point → W.M
  | 0 => 1
  | .some x _ _ => W.μX x

@[simp] lemma μ₀_zero : W.μ₀ 0 = 1 := rfl

@[simp] lemma μ₀_some {x y : K} (h : W.Nonsingular x y) : W.μ₀ (.some x y h) = W.μX x := rfl

end μ₀

/-!
### Step 3: show that `μ` is a homomorphism `Multiplicative W.Point → M`
-/

lemma Point.some_add_some_add_some_eq_zero {xP yP xQ yQ xR yR : K}
    (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ) (hR : W.Nonsingular xR yR)
    (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0) :
    ∃ pol, (X - C xP) * (X - C xQ) * (X - C xR) = W.f - pol ^ 2 ∧ pol.natDegree ≤ 1 := by
  refine ⟨linePolynomial xP yP <| W.slope xP xQ yP yQ, ?_, ?_⟩
  · have hgeneric : ¬(xP = xQ ∧ yP = W.negY xQ yQ) := by
      by_contra H
      simp [add_of_Y_eq H.1 H.2] at hPQR
    have := addPolynomial_slope hP.1 hQ.1 hgeneric |>.symm
    rw [neg_eq_iff_eq_neg] at this
    convert this using 1
    · congr
      rw [add_eq_zero_iff_eq_neg, neg_some, add_some hgeneric] at hPQR
      grind
    · simp [addPolynomial, polynomial]
  · simp only [linePolynomial, natDegree_add_C]
    compute_degree

open Point in
private lemma xQ_ne_xP_of_eval_f_eq_zero {xP yP xQ yQ xR yR : K} (hP : W.Nonsingular xP yP)
    (hQ : W.Nonsingular xQ yQ) (hR : W.Nonsingular xR yR)
    (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0) (h : W.f.eval xP = 0) :
    xQ ≠ xP := by
  contrapose! hPQR
  rw! [hPQR] at hQ ⊢
  rw! [y_eq_zero_of_eval_f_eq_zero hP.1 h, y_eq_zero_of_eval_f_eq_zero hQ.1 h]
  rw [add_self_of_Y_eq <| by simp, zero_add]
  exact some_ne_zero hR

open Point in
/- If two of three collinear points have distinct `2`-torsion `x`-coordinates, then the line
through them is horizontal, and `f` splits off all three `x`-coordinates. -/
private lemma f_eq_prod_of_eval_f_eq_zero {xP yP xQ yQ xR yR : K} (hP : W.Nonsingular xP yP)
    (hQ : W.Nonsingular xQ yQ) (hR : W.Nonsingular xR yR)
    (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0) (h₁ : W.f.eval xP = 0)
    (h₂ : W.f.eval xQ = 0) :
    W.f = (X - C xP) * (X - C xQ) * (X - C xR) := by
  have hPQ : xQ ≠ xP := xQ_ne_xP_of_eval_f_eq_zero hP hQ hR hPQR h₁
  obtain ⟨pol, hpol, hpol₁⟩ := Point.some_add_some_add_some_eq_zero hP hQ hR hPQR
  have hpol₀ : pol = 0 := by
    refine pol.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' {xP, xQ} (fun x hx ↦ ?_) ?_
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      apply_fun (·.eval x) at hpol
      rcases hx with rfl | rfl <;>
        rw [eval_sub, ‹eval x (f W) = 0›] at hpol <;>
        simpa using hpol
    · grind
  rwa [hpol₀, zero_pow two_ne_zero, sub_zero, eq_comm] at hpol

/- Forward direction of `exists_eq_two_smul_iff`: if `(x, y)` is divisible by `2`, then the
polynomial identity holds, with `ξ` the `x`-coordinate of a halving point. -/
private lemma exists_pol_of_eq_two_smul {x y : K} (h : W.Nonsingular x y) {P : W.Point}
    (hP : Point.some x y h = 2 • P) :
    ∃ ξ l m, (X - C ξ) ^ 2 * (X - C x) = W.f - (C l * X + C m) ^ 2 := by
  match P with
  | 0 => simp at hP -- cannot occur
  | .some ξ η h' =>
    rw [← sub_eq_zero, sub_eq_add_neg, two_smul, neg_add, ← add_assoc, add_rotate,
      Point.neg_some] at hP
    have H : W.Nonsingular ξ (W.negY ξ η) := (nonsingular_neg ξ η).mpr h'
    obtain ⟨pol, hpol, hpol₁⟩ := Point.some_add_some_add_some_eq_zero H H h hP
    rw [← sq] at hpol
    obtain ⟨l, m, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hpol₁
    exact ⟨_, _, _, hpol⟩

variable [W.IsElliptic]

section μ₀_helper_lemmas

open Point

lemma μ₀_mul_eq_one (P : W.Point) : W.μ₀ P * W.μ₀ (-P) = 1 := by
  match P with
  | 0 => simp
  | .some x y h => rw [Point.neg_some h, μ₀_some, μ₀_some, M.mul_self]

variable {xP yP xQ yQ xR yR : K} (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ)
  (hR : W.Nonsingular xR yR) (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0)

include hPQR

private lemma μX_mul_mul_eq_one_of_eval_f_eq_zero_of_eval_f_eq_zero (h₁ : W.f.eval xP = 0)
    (h₂ : W.f.eval xQ = 0) :
    W.μX xP * W.μX xQ * W.μX xR = 1 := by
  have hf := f_eq_prod_of_eval_f_eq_zero hP hQ hR hPQR h₁ h₂
  have h₃ : W.f.eval xR = 0 := by rw [hf]; simp
  obtain ⟨hfcP, hfcQ, hfcR⟩ := W.fCofactor_eq_of_f_eq hf
  rw [μX_of_eval_f_eq_zero h₁, μX_of_eval_f_eq_zero h₂, μX_of_eval_f_eq_zero h₃,
    Units.modPow.unit_mul_unit_mul_unit_eq_one_iff]
  simp only [hfcP, hfcQ, hfcR,
    show ∀ (a b c : K), C a - X + (X - C b) * (X - C c) =
      (X - C b) * (X - C c) - (X - C a) by intro a b c; ring]
  rw [map_sub, map_sub _ _ (X - C xQ), map_sub _ _ (X - C xR)]
  simp only [map_mul]
  rw [← sq_add_add_eq_mul_mul_of_mul_mul_eq_zero <| by rw [← map_mul, ← map_mul, ← hf]; simp]
  exact ⟨_, rfl⟩

/- The case where only `xP` is a `2`-torsion `x`-coordinate. -/
private lemma μX_mul_mul_eq_one_of_eval_f_eq_zero_of_ne_of_ne (h : W.f.eval xP = 0)
    (hQ₀ : W.f.eval xQ ≠ 0) (hR₀ : W.f.eval xR ≠ 0) :
    W.μX xP * W.μX xQ * W.μX xR = 1 := by
  rw [μX_of_eval_f_eq_zero h, μX_of_eval_f_ne_zero hQ₀, μX_of_eval_f_ne_zero hR₀,
    Units.modPow.unit_mul_unit_mul_unit_eq_one_iff]
  obtain ⟨pol, hpol, hpol₁⟩ := Point.some_add_some_add_some_eq_zero hP hQ hR hPQR
  obtain ⟨γ, rfl⟩ : ∃ γ, pol = C γ * (X - C xP) := by
    apply_fun (·.eval xP) at hpol
    rw [eval_sub, h] at hpol
    exact exists_eq_C_mul_X_sub_C_of_natDegree_le_one hpol₁ (by simpa using hpol)
  rw [W.f_eq_mul_of_eval_eq_zero h, mul_assoc, mul_comm (W.fCofactor _),
    show (C γ * (X - C xP)) ^ 2 = (X - C xP) * (C γ ^ 2 * (X - C xP)) by ring, ← mul_sub] at hpol
  replace hpol := mul_left_cancel₀ (X_sub_C_ne_zero xP) hpol
  simp only [← map_mul]
  rw [show (C xP - X + fCofactor W xP) * (C xQ - X) * (C xR - X) =
    (fCofactor W xP - (X - C xP)) * (X - C xQ) * (X - C xR) by ring, map_mul, map_mul, map_sub]
  rw [← sq_add_mul_eq_mul_mul_of_mul_eq_zero (e := AdjoinRoot.mk W.f (C γ)) ?H₁ ?H₂]
  case H₁ =>
    rw [← map_mul, mul_comm, ← f_eq_mul_of_eval_eq_zero W h]
    simp
  case H₂ => simp only [← map_mul, ← map_pow, ← map_sub, hpol]
  exact ⟨_, rfl⟩

private lemma μX_mul_mul_eq_one_of_eval_f_eq_zero (h : W.f.eval xP = 0) :
    W.μX xP * W.μX xQ * W.μX xR = 1 := by
  by_cases hQ₀ : W.f.eval xQ = 0
  · exact μX_mul_mul_eq_one_of_eval_f_eq_zero_of_eval_f_eq_zero hP hQ hR hPQR h hQ₀
  by_cases hR₀ : W.f.eval xR = 0
  · rw [mul_right_comm]
    rw [add_right_comm] at hPQR
    exact μX_mul_mul_eq_one_of_eval_f_eq_zero_of_eval_f_eq_zero hP hR hQ hPQR h hR₀
  exact μX_mul_mul_eq_one_of_eval_f_eq_zero_of_ne_of_ne hP hQ hR hPQR h hQ₀ hR₀

lemma μX_mul_mul_eq_one : W.μX xP * W.μX xQ * W.μX xR = 1 := by
  rcases eq_or_ne (W.f.eval xP) 0 with HP | HP
  · exact μX_mul_mul_eq_one_of_eval_f_eq_zero hP hQ hR hPQR HP
  rcases eq_or_ne (W.f.eval xQ) 0 with HQ | HQ
  · rw [mul_comm (W.μX xP)]
    rw [add_comm (Point.some xP ..)] at hPQR
    exact μX_mul_mul_eq_one_of_eval_f_eq_zero hQ hP hR hPQR HQ
  rcases eq_or_ne (W.f.eval xR) 0 with HR | HR
  · rw [mul_comm, ← mul_assoc]
    rw [add_comm, ← add_assoc] at hPQR
    exact μX_mul_mul_eq_one_of_eval_f_eq_zero hR hP hQ hPQR HR
  rw [μX_of_eval_f_ne_zero HP, μX_of_eval_f_ne_zero HQ, μX_of_eval_f_ne_zero HR,
    Units.modPow.unit_mul_unit_mul_unit_eq_one_iff]
  obtain ⟨pol, hpol, hpol₁⟩ := Point.some_add_some_add_some_eq_zero hP hQ hR hPQR
  simp only [← map_mul, hpol, neg_sub,
    show (C xP - X) * (C xQ - X) * (C xR - X) = -((X - C xP) * (X - C xQ) * (X - C xR))
      by algebra]
  simp

end μ₀_helper_lemmas

lemma μ₀_mul_mul_eq_one_of_add_add_eq_zero {P Q R : W.Point} (hPQR : P + Q + R = 0) :
    μ₀ P * μ₀ Q * μ₀ R = 1 := by
  match P, Q, R with
  | 0, _, _ =>
    rw [zero_add, add_eq_zero_iff_eq_neg'] at hPQR
    rw [μ₀_zero, one_mul, hPQR, μ₀_mul_eq_one]
  | .some .., 0, _
  | .some .., .some .., 0 =>
    rw [add_zero, add_eq_zero_iff_eq_neg'] at hPQR
    rw [μ₀_zero, mul_one, hPQR, μ₀_mul_eq_one]
  | .some xP yP hP, .some xQ yQ hQ, .some xR yR hR =>
    simp only [μ₀_some]
    exact μX_mul_mul_eq_one hP hQ hR hPQR

/-- The descent map as a group homomorphism. -/
noncomputable def μ : Multiplicative W.Point →* W.M :=
  .ofMapMulMulEqOne (f := μ₀ ∘ Multiplicative.toAdd) (by simp) fun P' Q' R' ↦ by
    simp_rw [← toAdd_eq_zero, toAdd_mul, Function.comp_apply]
    exact μ₀_mul_mul_eq_one_of_add_add_eq_zero

@[simp]
lemma μ_apply (P : W.Point) : μ (.ofAdd P) = μ₀ P := rfl

@[simp]
lemma μ₀_two_nsmul (P : W.Point) : W.μ₀ (2 • P) = 1 := by
  rw [← μ_apply, ofAdd_nsmul, map_pow, M.sq_eq_one]

/-!
### Step 4: show that `μ` has kernel `2 • W(K)`.
-/

/- Reverse direction of `exists_eq_two_smul_iff`, in terms of the coefficient identities of
the polynomial identity: the point `(ξ, lξ + m)` lies on `W` and doubles to `(x, ±y)`. -/
private lemma exists_eq_two_smul_of_identities {x y ξ l m : K} (h : W.Nonsingular x y)
    (H₂ : x + 2 * ξ = l ^ 2 - W.a₂) (H₁ : 2 * x * ξ + ξ ^ 2 = W.a₄ - 2 * l * m)
    (H₀ : x * ξ ^ 2 = -W.a₆ + m ^ 2) :
    ∃ P, Point.some x y h = 2 • P := by
  have h20 : (2 : K) ≠ 0 := Ring.two_ne_zero <| ringChar_ne_two W
  have hy₀ : l * ξ + m ≠ 0 := by
    have hΔ := W.isUnit_Δ.ne_zero
    rw [Δ_of_isCharNeTwoNF W] at hΔ
    contrapose! hΔ
    -- the Bézout certificate for `Δ`, evaluated at `ξ`, where `f ξ = (lξ+m)²` and
    -- `f' ξ = 2l(lξ+m)` vanish by `hΔ` and the coefficient identities
    linear_combination
      (((288 * W.a₄ - 96 * W.a₂ ^ 2) * ξ + (240 * W.a₂ * W.a₄ - 64 * W.a₂ ^ 3 - 432 * W.a₆)) *
          ((l * ξ + m) * hΔ + ξ ^ 2 * H₂ - ξ * H₁ + H₀))
        + (((32 * W.a₂ ^ 2 - 96 * W.a₄) * ξ ^ 2
            + (32 * W.a₂ ^ 3 - 112 * W.a₂ * W.a₄ + 144 * W.a₆) * ξ
            + (16 * W.a₂ ^ 2 * W.a₄ - 64 * W.a₄ ^ 2 + 48 * W.a₂ * W.a₆)) *
          (2 * l * hΔ + 2 * ξ * H₂ - H₁))
  have hy : l * ξ + m ≠ W.negY ξ (l * ξ + m) := by
    rw [negY_of_isCharNeTwoNF]
    grind
  have hsl : W.slope ξ ξ (l * ξ + m) (l * ξ + m) = l := by
    simp only [slope_of_Y_ne rfl hy, a₁_of_isCharNeTwoNF, zero_mul, sub_zero,
      negY_of_isCharNeTwoNF, sub_neg_eq_add, ← two_mul]
    rw [mul_comm] at hy₀ -- `field_simp` changes `l * ξ` to `ξ * l`
    field_simp
    grobner
  have heq : W.Equation ξ (l * ξ + m) := by
    rw [equation_iff_eval_f_eq_sq, eval_f]
    linear_combination ξ ^ 2 * H₂ - ξ * H₁ + H₀
  let P : W.Point := .some ξ (l * ξ + m) <| equation_iff_nonsingular.mp heq
  suffices .some x y h = 2 • P ∨ .some x y h = 2 • (-P) from this.casesOn (⟨_, ·⟩) (⟨_, ·⟩)
  simp only [smul_neg, P, two_smul, Point.add_self_of_Y_ne hy, ← Point.X_eq_iff, hsl, addX,
    a₁_of_isCharNeTwoNF, zero_mul, add_zero]
  linear_combination H₂

/-- A criterion for a nonsingular point in affine coordinates to be divisible by 2,
in terms of an identity of polynomials. -/
lemma exists_eq_two_smul_iff {x y : K} (h : W.Nonsingular x y) :
    (∃ P, Point.some x y h = 2 • P) ↔
      ∃ ξ l m, (X - C ξ) ^ 2 * (X - C x) = W.f - (C l * X + C m) ^ 2 := by
  refine ⟨fun ⟨P, hP⟩ ↦ exists_pol_of_eq_two_smul h hP, fun ⟨ξ, l, m, H⟩ ↦ ?_⟩
  have H' : X ^ 3 - C (x + 2 * ξ) * X ^ 2 + C (2 * x * ξ + ξ ^ 2) * X - C (x * ξ ^ 2) =
      X ^ 3 - C (l ^ 2 - W.a₂) * X ^ 2 + C (W.a₄ - 2 * l * m) * X - C (-W.a₆ + m ^ 2) := by
    simp only [f] at H
    convert H using 1 <;> { simp only [C_eq_algebraMap]; algebra }
  replace H' n := congrArg (fun p ↦ p.coeff n) H'
  simp only [coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C] at H'
  exact exists_eq_two_smul_of_identities h (by simpa using congrArg (-·) (H' 2))
    (by simpa using H' 1) (by simpa using congrArg (-·) (H' 0))

/-- A criterion for a nonsingular point in affine coordinates to be divisible by 2,
in terms of an identity in `W.A`. -/
lemma exists_eq_two_smul_iff' {x y : K} (h : W.Nonsingular x y) :
    (∃ P, Point.some x y h = 2 • P) ↔
      ∃ ξ l m, AdjoinRoot.mk W.f ((X - C ξ) ^ 2 * (X - C x)) =
        AdjoinRoot.mk W.f (-(C l * X + C m) ^ 2) := by
  rw [exists_eq_two_smul_iff]
  refine ⟨fun ⟨ξ, l, m, H⟩ ↦ ⟨ξ, l, m, ?_⟩, fun ⟨ξ, l, m, H⟩ ↦ ⟨ξ, l, m, ?_⟩⟩
  · rw [H, map_sub, sub_eq_add_neg, map_neg, add_eq_right]
    simp
  · rw [AdjoinRoot.mk_eq_mk, sub_neg_eq_add] at H
    have hmon : ((X - C ξ) ^ 2 * (X - C x) + (C l * X + C m) ^ 2).Monic := by monicity!
    have hf := eq_of_dvd_of_natDegree_le_of_leadingCoeff H
      (by rw [natDegree_f]; compute_degree!) (by rw [W.monic_f.leadingCoeff, hmon.leadingCoeff])
    linear_combination -hf

section kernel

variable {x y : K} (h : W.Nonsingular x y)

include h

private lemma eq_two_smul_of_μ_eq_one_of_ne (hμ : (μ <| .ofAdd <| .some x y h) = 1)
    (hx : W.f.eval x ≠ 0) : ∃ P : W.Point, .some x y h = 2 • P := by
  rw [exists_eq_two_smul_iff']
  rw [μ_apply, μ₀_some, μX_of_eval_f_ne_zero hx, Units.modPow.unit_eq_one_iff] at hμ
  obtain ⟨z, hz⟩ := hμ
  obtain ⟨r, s, t, hrst⟩ := W.exists_mk_eq z
  rw [hrst] at hz
  have hr : r ≠ 0 := by
    intro rfl
    simp only [map_zero, zero_mul, zero_add, ← map_pow] at hz
    rw [AdjoinRoot.mk_eq_mk_iff_of_degree_lt W.monic_f
      (W.degree_lt_degree_f (by compute_degree!))
      (W.degree_lt_degree_f (by compute_degree!))] at hz
    apply_fun natDegree at hz
    have hd : (C x - X).natDegree = 1 := by compute_degree!
    rw [natDegree_pow, hd] at hz
    lia
  obtain ⟨ξ, l, m, H⟩ := W.exists_X_sub_C_mul_eq r s t hr
  rw [← map_mul] at H
  refine ⟨ξ, l, m, ?_⟩
  apply_fun (fun p ↦ AdjoinRoot.mk W.f (X - C ξ) ^ 2 * p) at hz
  rw [← neg_inj, eq_comm, ← map_pow, ← map_mul, ← map_neg] at hz
  conv_rhs at hz => rw [← map_pow, ← map_mul, ← mul_pow, map_pow, H, ← map_pow, ← map_neg]
  convert hz
  ring

private lemma eq_two_smul_of_μ_eq_one_of_eq (hμ : (μ <| .ofAdd <| .some x y h) = 1)
    (hx : W.f.eval x = 0) : ∃ P : W.Point, .some x y h = 2 • P := by
  rw [exists_eq_two_smul_iff']
  rw [μ_apply, μ₀_some, μX_of_eval_f_eq_zero hx, Units.modPow.unit_eq_one_iff] at hμ
  obtain ⟨z, hz⟩ := hμ
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective z
  obtain ⟨r, s, hrs⟩ := W.exists_mk_eq' (AdjoinRoot.mk (W.fCofactor x) p)
  rw [← hp, ← map_pow, AdjoinRoot.mk_eq_mk] at hz
  have hdvd : W.fCofactor x ∣ W.f := ⟨X - C x, W.f_eq_mul_of_eval_eq_zero hx⟩
  have hz' : AdjoinRoot.mk (W.fCofactor x) (p ^ 2) =
      AdjoinRoot.mk (W.fCofactor x) (C x - X + W.fCofactor x) :=
    AdjoinRoot.mk_eq_mk.mpr <| hdvd.trans hz
  rw [map_pow, hrs, map_add _ _ (fCofactor ..), AdjoinRoot.mk_self, add_zero] at hz'
  have hr₀ : r ≠ 0 := by
    intro rfl
    rw [map_zero, zero_mul, zero_add, ← map_pow,
      AdjoinRoot.mk_eq_mk_iff_of_degree_lt (W.monic_fCofactor x)
        (W.degree_lt_degree_fCofactor x (by compute_degree!))
        (W.degree_lt_degree_fCofactor x (by compute_degree!))] at hz'
    apply_fun natDegree at hz'
    have hd : (C x - X).natDegree = 1 := by compute_degree!
    rw [natDegree_pow, hd] at hz'
    lia
  rw [← map_pow, AdjoinRoot.mk_eq_mk] at hz'
  exact ⟨-s / r, 1 / r, -x / r, AdjoinRoot.mk_eq_mk.mpr (W.f_dvd_of_fCofactor_dvd hx hr₀ hz')⟩

lemma eq_two_smul_of_μ_eq_one (hμ : (μ <| .ofAdd <| .some x y h) = 1) :
    ∃ P : W.Point, .some x y h = 2 • P := by
  rcases eq_or_ne (W.f.eval x) 0 with hx | hx
  · exact eq_two_smul_of_μ_eq_one_of_eq h hμ hx
  · exact eq_two_smul_of_μ_eq_one_of_ne h hμ hx

end kernel

/-- The kernel of `μ` is exactly `2 • W(K)`. -/
lemma ker_μ_eq : (μ (W := W)).ker = (nsmulAddMonoidHom 2).range.toSubgroup := by
  ext P'
  obtain ⟨P, rfl⟩ := Multiplicative.ofAdd.surjective P'
  rw [MonoidHom.mem_ker, μ_apply, Multiplicative.mem_toSubgroup, toAdd_ofAdd,
    AddMonoidHom.mem_range]
  simp only [nsmulAddMonoidHom_apply]
  constructor
  · match P with
    | 0 => exact fun _ ↦ ⟨0, by simp⟩
    | .some x y h => exact fun hμ ↦ (eq_two_smul_of_μ_eq_one h hμ).imp fun Q hQ ↦ hQ.symm
  · rintro ⟨Q, rfl⟩
    exact μ₀_two_nsmul Q

/-- A criterion for the validity of the weak Mordell-Weil Theorem. -/
lemma finite_index_range_nsmulAddMonoidHom_two_iff :
    (nsmulAddMonoidHom (α := W.Point) 2).range.FiniteIndex ↔ Finite (μ (W := W)).range := by
  rw [← AddSubgroup.finiteIndex_toSubgroup_iff, ← ker_μ_eq,
    Equiv.finite_iff (QuotientGroup.quotientKerEquivRange (μ (W := W))).symm.toEquiv]
  exact Subgroup.finiteIndex_iff_finite_quotient

/-!
### The `2`-torsion of the group of points

In our situation (`a₁ = a₃ = 0`, so `-(x, y) = (x, -y)`), the `2`-torsion consists of the
origin together with the points `(x, 0)` at the roots of `f`; in particular its order is
the number of roots of `f` in `K` plus one.
-/

lemma two_nsmul_some_eq_zero {x : K} (hx : W.f.eval x = 0) :
    (2 : ℕ) • (Point.some _ _ (W.nonsingular_of_eval_f_eq_zero hx) : W.Point) = 0 := by
  rw [two_nsmul, add_eq_zero_iff_eq_neg, Point.neg_some, Point.some.injEq]
  refine ⟨rfl, ?_⟩
  rw [negY_of_isCharNeTwoNF, neg_zero]

lemma y_eq_zero_of_two_nsmul_eq_zero {x y : K} (h : W.Nonsingular x y)
    (h2 : (2 : ℕ) • (Point.some _ _ h : W.Point) = 0) :
    y = 0 := by
  have h20 : (2 : K) ≠ 0 := Ring.two_ne_zero <| ringChar_ne_two W
  rw [two_nsmul, add_eq_zero_iff_eq_neg, Point.neg_some, Point.some.injEq] at h2
  have hy : 2 * y = 0 := by linear_combination h2.2.trans (negY_of_isCharNeTwoNF ..)
  rcases mul_eq_zero.mp hy with h' | h'
  · exact absurd h' h20
  · exact h'

/-- The `2`-torsion of the group of points consists of the origin and the points `(x, 0)`
at the roots of `f`. -/
theorem card_ker_nsmul_two :
    Nat.card (nsmulAddMonoidHom (α := W.Point) 2).ker =
      Nat.card {x : K // W.f.eval x = 0} + 1 := by
  have hfin : Finite {x : K | W.f.eval x = 0} :=
    Set.Finite.to_subtype (Polynomial.finite_setOf_isRoot W.f_ne_zero)
  set pt : {x : K | W.f.eval x = 0} → W.Point :=
    fun x ↦ Point.some _ _ (W.nonsingular_of_eval_f_eq_zero x.2)
  have hinj : Function.Injective pt := by
    intro a b hab
    exact Subtype.ext ((Point.some.injEq _ _ _ _ _ _).mp hab).1
  -- the kernel is the origin together with the image of the roots
  have hset : ((nsmulAddMonoidHom (α := W.Point) 2).ker : Set W.Point) =
      insert 0 (Set.range pt) := by
    ext P
    constructor
    · intro hP
      induction P with
      | zero => exact Set.mem_insert _ _
      | some x y h =>
        have hy := W.y_eq_zero_of_two_nsmul_eq_zero h hP
        subst hy
        have hx : W.f.eval x = 0 := by
          have := (W.equation_iff_eval_f_eq_sq x 0).mp h.1
          simpa using this
        exact Set.mem_insert_of_mem _ ⟨⟨x, hx⟩, rfl⟩
    · intro hP
      rcases Set.mem_insert_iff.mp hP with rfl | ⟨x, rfl⟩
      · exact zero_mem _
      · exact W.two_nsmul_some_eq_zero x.2
  calc Nat.card (nsmulAddMonoidHom (α := W.Point) 2).ker
      = ((nsmulAddMonoidHom (α := W.Point) 2).ker : Set W.Point).ncard :=
        Nat.card_coe_set_eq _
    _ = (insert 0 (Set.range pt)).ncard := by rw [hset]
    _ = (Set.range pt).ncard + 1 :=
        Set.ncard_insert_of_notMem (by intro ⟨x, hx⟩; exact Point.some_ne_zero _ hx)
    _ = Nat.card {x : K // W.f.eval x = 0} + 1 := by
        rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective hinj]
        rfl

/-!
### Step 5: show that `im μ` is contained in the kernel of the norm map.

The norm `Algebra.norm K : W.A →* K` sends units to units, hence induces a homomorphism
`normM : W.M →* Units.modPow K 2` on square classes. We must show `normM ∘ μ = 1`.

Writing `f = (X - θ₁) * (X - θ₂) * (X - θ₃)` over a splitting field, the two cases are:

* if `f x ≠ 0`, then `N (x - θ) = ∏ᵢ (x - θᵢ) = f x = y²`, a square;
* if `f x = 0`, then `N (f' θ) = (f' x)²`, again a square.

Both are instances of `AdjoinRoot.norm_mk_eq_resultant`: the norm of `AdjoinRoot.mk g p` for
monic `g` is the resultant of `g` and `p`. See `norm_mk_C_sub_X` and
`norm_mk_C_sub_X_add_fCofactor` in Step 1 above, which deduce them from it by resultant algebra;
in the second case the factorization `f = fCofactor x * (X - C x)` splits the resultant into two
factors, each equal to `(W.fCofactor x).eval x = f' x`.

`AdjoinRoot.norm_mk_eq_resultant` is proved in `EllipticCurves.Mathlib.Basic`; it is a general fact
about
`AdjoinRoot g` for monic `g` and looks worth upstreaming.
-/

section Step5

/-- The norm map on square classes, induced by `Algebra.norm K : W.A →* K`. -/
noncomputable def normM : W.M →* Units.modPow K 2 :=
  Units.modPow.map (Algebra.norm K) 2

/-- The image of `μX` lies in the kernel of the norm map on square classes. -/
lemma normM_μX_eq_one {x y : K} (h : W.Equation x y) : W.normM (W.μX x) = 1 := by
  rcases eq_or_ne (W.f.eval x) 0 with hx | hx
  · rw [μX_of_eval_f_eq_zero hx, normM, Units.modPow.map_unit, Units.modPow.unit_eq_one_iff]
    exact ⟨3 * x ^ 2 + 2 * W.a₂ * x + W.a₄, (W.norm_mk_C_sub_X_add_fCofactor hx).symm⟩
  · rw [μX_of_eval_f_ne_zero hx, normM, Units.modPow.map_unit, Units.modPow.unit_eq_one_iff]
    exact ⟨y, by rw [W.norm_mk_C_sub_X, (equation_iff_eval_f_eq_sq W x y).mp h]⟩

@[simp]
lemma normM_μ₀_eq_one (P : W.Point) : W.normM (W.μ₀ P) = 1 := by
  match P with
  | 0 => simp
  | .some x y h => exact normM_μX_eq_one h.1

/-- The image of `μ` is contained in the kernel of the norm map on square classes. -/
lemma range_μ_le_ker_normM : (μ (W := W)).range ≤ (normM (W := W)).ker := by
  rintro _ ⟨P, rfl⟩
  obtain ⟨P, rfl⟩ := Multiplicative.ofAdd.surjective P
  rw [MonoidHom.mem_ker, μ_apply]
  exact normM_μ₀_eq_one P

end Step5

end WeierstrassCurve.Affine

/-!
## Step 6: `im μ ⊆ A(S,2)`

The right level of generality is: `R` a Dedekind domain, `K = Frac R`, and `E/K` given by a
Weierstrass equation with `a₁ = a₃ = 0`. Everything Step 6 needs — a height-one spectrum,
the `v`-adic
valuations, and unique factorization of fractional ideals — is exactly the Dedekind package.
Number fields are *not* needed until Step 7.

`Mathlib.RingTheory.DedekindDomain.SelmerGroup` already defines, for a Dedekind domain `R` with
fraction field `K`, the group `IsDedekindDomain.selmerGroup : Subgroup (Units.modPow K n)`,
namely the classes whose valuation is `≡ 0 mod n` at every `v ∉ S`. Note that its ambient group
is literally our `Units.modPow K n` (that file has it only as a local notation). So the target
`A(S,2)` should be assembled out of `selmerGroup`s, not defined from scratch.

The obstruction is that `A = AdjoinRoot f` is an étale algebra, not a field, so it has no
`HeightOneSpectrum`. The way around this is the decomposition of `A` into a product of fields,
provided by `EllipticCurves.Mathlib.Basic`: as `f` is separable, `AdjoinRoot.equivPiFactors` gives
`A ≃ₐ[K] ((p : W.f.Factors) → AdjoinRoot p)`, a finite product of finite separable field
extensions of `K` indexed by the monic irreducible factors `p` of `f`, and correspondingly
`AdjoinRoot.modPowEquivPiFactors` gives
`W.M = Units.modPow A 2 ≃* ((p : W.f.Factors) → Units.modPow (AdjoinRoot p) 2)`.
Each factor carries `Field`, `Algebra K` and `FiniteDimensional K` instances, and
`Polynomial.Factors.separable` supplies separability.

With that in hand:

* for each factor, `ringOfIntegersFactor R p := integralClosure R (AdjoinRoot p)` is again a
  Dedekind domain (`IsIntegralClosure.isDedekindDomain`, applicable thanks to
  `AdjoinRoot.isSeparable_of_separable`) with fraction field `AdjoinRoot p`, so
  `IsDedekindDomain.selmerGroup` applies to it;
* `A(S,2)` (`selmerGroupA`) is the preimage under the above isomorphism of the product of the
  `selmerGroupFactor R p`, the `2`-Selmer groups relative to the primes above `S`;
* the containment `im μ ⊆ A(S,2)` is checked factor by factor: for `P = (x, y)` and `w` a prime
  of `ringOfIntegersFactor R p` not above `S`, the valuation `w (x - θ)` is even, where `θ` is
  the root of `p`. If `x` has a pole at `w`, the leading term of the cubic dominates and
  `w (x - θ) = w x = w (y / x) ^ 2`. If `x` is `w`-integral, one uses the factorization
  `y ^ 2 = (x - θ) * (x ^ 2 + θ x + θ ^ 2 + a₂ (x + θ) + a₄)` over the factor `K[X]/(p)`
  itself: the cofactor
  is congruent to `f' θ` modulo `x - θ`, and `f' θ` is a `w`-unit because `w ∤ Δ`. So either
  `x - θ` is a `w`-unit, or the cofactor is, and then `w (x - θ) = w y ^ 2`.

Step 7 (finiteness of `A(S,2)`) then reduces to finiteness of the `2`-Selmer group of each
factor, which needs the primes above `S` to be finite in number, the class group of
`ringOfIntegersFactor R p` to be finite, and its unit group to be finitely generated — i.e.
number fields. Mathlib lists finiteness of `selmerGroup` as a TODO.

Note that the valuation computation stays inside the single field factor `K[X]/(p)`; no
splitting field is needed. That `f' θ` is a unit at every good prime
(`valuation_deriv_root_eq_one`) needs exactly that the coefficients of the cubic are integral
and `disc f` is a unit there — which is what `Δ ∈ badPrimes` buys, via the Bézout identity
behind `separable_f`.

All of this is carried out below: `badPrimes` (`S`) and its finiteness,
`AdjoinRoot.isSeparable_of_separable` (so that `IsIntegralClosure.isDedekindDomain` applies to
each factor), `IsDedekindDomain.HeightOneSpectrum.primesAbove` (the `S i`),
`IsDedekindDomain.selmerGroupAbove`, `selmerGroupA` (`A(S,2)`, as a subgroup of `W.M`), and
finally `range_μ_le_selmerGroupA`.
-/

section Cubic

/- Specializations of `Valuation.map_eval_eq_of_one_lt` and `Valuation.le_one_of_root_monic`
from `EllipticCurves.Mathlib.Basic` to the monic cubic `t ^ 3 + a * t ^ 2 + b * t + c`. They are
specific to Weierstrass equations, so they live here rather than in the general-support file. -/

open Polynomial

variable {L Γ : Type*} [CommRing L] [Nontrivial L] [LinearOrderedCommGroupWithZero Γ]
  (ν : Valuation L Γ) {t a b c : L}

private lemma cubic_coeff_le_one (ha : ν a ≤ 1) (hb : ν b ≤ 1) (hc : ν c ≤ 1) :
    ∀ i < (X ^ 3 + C a * X ^ 2 + C b * X + C c).natDegree,
      ν ((X ^ 3 + C a * X ^ 2 + C b * X + C c).coeff i) ≤ 1 := by
  have hdeg : (X ^ 3 + C a * X ^ 2 + C b * X + C c).natDegree = 3 := by compute_degree!
  intro i hi
  rw [hdeg] at hi
  interval_cases i <;> simp [ha, hb, hc]

private lemma Valuation.map_cubic_of_one_lt (ha : ν a ≤ 1) (hb : ν b ≤ 1) (hc : ν c ≤ 1)
    (ht : 1 < ν t) :
    ν (t ^ 3 + a * t ^ 2 + b * t + c) = ν t ^ 3 := by
  have hp : (X ^ 3 + C a * X ^ 2 + C b * X + C c).Monic := by monicity!
  have hdeg : (X ^ 3 + C a * X ^ 2 + C b * X + C c).natDegree = 3 := by compute_degree!
  have h := ν.map_eval_eq_of_one_lt hp (cubic_coeff_le_one ν ha hb hc) ht
  rw [hdeg] at h
  simpa using h

private lemma Valuation.le_one_of_root_cubic (ha : ν a ≤ 1) (hb : ν b ≤ 1) (hc : ν c ≤ 1)
    (heq : t ^ 3 + a * t ^ 2 + b * t + c = 0) :
    ν t ≤ 1 := by
  have hp : (X ^ 3 + C a * X ^ 2 + C b * X + C c).Monic := by monicity!
  have hdeg : (X ^ 3 + C a * X ^ 2 + C b * X + C c).natDegree = 3 := by compute_degree!
  refine ν.le_one_of_root_monic hp (cubic_coeff_le_one ν ha hb hc) (by rw [hdeg]; norm_num) ?_
  simpa using heq

end Cubic

namespace WeierstrassCurve.Affine

open IsDedekindDomain Polynomial UniqueFactorizationMonoid

-- Step 6 needs neither `DecidableEq K` (except where the `x - T` map `μX` enters at the very
-- end) nor the group structure on points, so we re-declare the variables rather than
-- inheriting the ones used for Steps 2-5.
variable {K : Type*} [Field K] (W : Affine K)

/- Notation local to Step 6: for a monic irreducible factor `p` of `f`, `𝕃 p` is the field
factor `K[X]/(p)` of `W.A`, `ι p : K →+* 𝕃 p` is the canonical embedding, and `θ p` is the
image of the root `T` of `f` in `𝕃 p`. -/
local notation:max "𝕃" p:max => AdjoinRoot (p : K[X])
local notation:max "ι" p:max => algebraMap K (AdjoinRoot (p : K[X]))
local notation:max "θ" p:max => AdjoinRoot.root (p : K[X])

/-- The set of "bad" primes of `R`: those dividing `2` or the discriminant of `W`, and those
occurring in a denominator of `a₂`, `a₄` or `a₆` (the latter three are the supports of the
coefficients in the sense of `IsDedekindDomain.HeightOneSpectrum.Support`). Away from these,
the `x - T` map lands in the `2`-Selmer group. -/
def badPrimes (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K] :
    Set (HeightOneSpectrum R) :=
  {v | v.valuation K 2 ≠ 1} ∪ {v | v.valuation K W.Δ ≠ 1} ∪ HeightOneSpectrum.Support R W.a₂ ∪
    HeightOneSpectrum.Support R W.a₄ ∪ HeightOneSpectrum.Support R W.a₆

/-- There are only finitely many bad primes: `2` and `W.Δ` are nonzero, and the support of any
element of `K` is finite. -/
lemma finite_badPrimes (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K]
    [IsFractionRing R K] [W.IsElliptic] [W.IsCharNeTwoNF] : (W.badPrimes R).Finite :=
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two W)
  ((((HeightOneSpectrum.finite_setOf_valuation_ne_one h2).union
    (HeightOneSpectrum.finite_setOf_valuation_ne_one W.isUnit_Δ.ne_zero)).union
      (HeightOneSpectrum.Support.finite R W.a₂)).union
        (HeightOneSpectrum.Support.finite R W.a₄)).union
          (HeightOneSpectrum.Support.finite R W.a₆)

open WithZero in
/-- The places where the reduced cubic degenerates: `disc f` vanishes to order at least `2`,
or a coefficient has a pole. Away from these the local descent image consists of unramified
classes (in any residue characteristic). -/
def discBadPrimes (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K]
    [IsFractionRing R K] : Set (HeightOneSpectrum R) :=
  {v | ¬ exp (-1 : ℤ) ≤ v.valuation K W.f.discr} ∪ HeightOneSpectrum.Support R W.a₂ ∪
    HeightOneSpectrum.Support R W.a₄ ∪ HeightOneSpectrum.Support R W.a₆

/-- The places where the local condition genuinely constrains the 2-Selmer group: the
degenerate places of `discBadPrimes` together with all even places. -/
def badPrimes₂ (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K]
    [IsFractionRing R K] : Set (HeightOneSpectrum R) :=
  W.discBadPrimes R ∪ {v | v.valuation K 2 ≠ 1}

open WithZero in
/-- There are only finitely many places in `discBadPrimes`: where `exp (-1) ≤ v(disc f)`
fails, in particular `v(disc f) ≠ 1`, and `disc f` is nonzero. -/
lemma finite_discBadPrimes (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K]
    [IsFractionRing R K] [W.IsElliptic] [W.IsCharNeTwoNF] : (W.discBadPrimes R).Finite :=
  have h : {v : HeightOneSpectrum R | ¬ exp (-1 : ℤ) ≤ v.valuation K W.f.discr} ⊆
      {v | v.valuation K W.f.discr ≠ 1} := fun v hv he ↦
    hv ((le_of_le_of_eq (exp_le_exp.mpr (by lia)) exp_zero).trans he.ge)
  ((((HeightOneSpectrum.finite_setOf_valuation_ne_one W.discr_f_ne_zero).subset h).union
    (HeightOneSpectrum.Support.finite R W.a₂)).union
      (HeightOneSpectrum.Support.finite R W.a₄)).union
        (HeightOneSpectrum.Support.finite R W.a₆)

/-- There are only finitely many places in `badPrimes₂`. -/
lemma finite_badPrimes₂ (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K]
    [IsFractionRing R K] [W.IsElliptic] [W.IsCharNeTwoNF] : (W.badPrimes₂ R).Finite :=
  (W.finite_discBadPrimes R).union <|
    HeightOneSpectrum.finite_setOf_valuation_ne_one <| Ring.two_ne_zero (ringChar_ne_two W)

/-- The norm of the class of `-1` in the étale algebra is the class of `-1`: the algebra has
odd rank `3` over `K`. -/
lemma normM_neg_one : W.normM (QuotientGroup.mk (-1 : W.Aˣ)) = QuotientGroup.mk (-1 : Kˣ) := by
  have hnorm : Algebra.norm K (-1 : W.A) = -1 := by
    rw [show (-1 : W.A) = algebraMap K W.A (-1) by simp, Algebra.norm_algebraMap, W.finrank_A]
    norm_num
  rw [normM, Units.modPow.map_mk]
  congr 1
  ext
  rw [Units.coe_map]
  simpa using hnorm

/-- If `-1` is not a square in `K`, the class of `-1` in the étale algebra has nontrivial
norm class. -/
lemma normM_neg_one_ne_one (h : ¬ IsSquare (-1 : K)) :
    W.normM (QuotientGroup.mk (-1 : W.Aˣ)) ≠ 1 := by
  rw [W.normM_neg_one, Ne, Units.modPow.mk_eq_one_iff_isSquare]
  simpa using h

open WithZero in
/-- `discBadPrimes` is empty when the coefficients of the cubic are everywhere integral and
its discriminant vanishes at most to first order everywhere — e.g. for a global integral model
with squarefree `disc f` (`IsDedekindDomain.HeightOneSpectrum.notMem_pow_two_of_squarefree`). -/
lemma discBadPrimes_eq_empty (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K]
    [IsFractionRing R K] (ha₂ : ∀ v : HeightOneSpectrum R, v.valuation K W.a₂ ≤ 1)
    (ha₄ : ∀ v : HeightOneSpectrum R, v.valuation K W.a₄ ≤ 1)
    (ha₆ : ∀ v : HeightOneSpectrum R, v.valuation K W.a₆ ≤ 1)
    (hd : ∀ v : HeightOneSpectrum R, exp (-1 : ℤ) ≤ v.valuation K W.f.discr) :
    W.discBadPrimes R = ∅ := by
  rw [discBadPrimes, Set.eq_empty_iff_forall_notMem]
  rintro v (((hv | hv) | hv) | hv) <;>
    simp only [Set.mem_setOf_eq, HeightOneSpectrum.Support, Set.mem_setOf_eq] at hv
  exacts [hv (hd v), absurd hv (not_lt.mpr (ha₂ v)), absurd hv (not_lt.mpr (ha₄ v)),
    absurd hv (not_lt.mpr (ha₆ v))]

/-- `discBadPrimes R = ∅` when the coefficients of `W` are `R`-integral and the discriminant
of the cubic comes from a squarefree element of `R` (with `R` a principal ideal domain, so
that squarefreeness gives `δ ∉ v²` for every `v`). -/
lemma discBadPrimes_eq_empty_of_squarefree (R : Type*) [CommRing R] [IsDedekindDomain R]
    [Algebra R K] [IsFractionRing R K] [IsPrincipalIdealRing R]
    (ha₂ : W.a₂ ∈ (algebraMap R K).range) (ha₄ : W.a₄ ∈ (algebraMap R K).range)
    (ha₆ : W.a₆ ∈ (algebraMap R K).range) {δ : R} (hδ : algebraMap R K δ = W.f.discr)
    (hsq : Squarefree δ) :
    W.discBadPrimes R = ∅ := by
  obtain ⟨a₂, ha₂⟩ := ha₂
  obtain ⟨a₄, ha₄⟩ := ha₄
  obtain ⟨a₆, ha₆⟩ := ha₆
  refine W.discBadPrimes_eq_empty R (fun v ↦ ?_) (fun v ↦ ?_) (fun v ↦ ?_) (fun v ↦ ?_)
  · rw [← ha₂]; exact v.valuation_le_one a₂
  · rw [← ha₄]; exact v.valuation_le_one a₄
  · rw [← ha₆]; exact v.valuation_le_one a₆
  · rw [← hδ]
    exact v.exp_neg_one_le_valuation_algebraMap (v.notMem_pow_two_of_squarefree hsq)

section BadPrimes

variable (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
  {v : HeightOneSpectrum R}

lemma valuation_a₂_le_one_of_notMem_badPrimes (hv : v ∉ W.badPrimes R) :
    v.valuation K W.a₂ ≤ 1 :=
  not_lt.mp fun hlt ↦ hv (.inl (.inl (.inr hlt)))

lemma valuation_a₄_le_one_of_notMem_badPrimes (hv : v ∉ W.badPrimes R) :
    v.valuation K W.a₄ ≤ 1 :=
  not_lt.mp fun hlt ↦ hv (.inl (.inr hlt))

lemma valuation_a₆_le_one_of_notMem_badPrimes (hv : v ∉ W.badPrimes R) :
    v.valuation K W.a₆ ≤ 1 :=
  not_lt.mp fun hlt ↦ hv (.inr hlt)

lemma valuation_Δ_eq_one_of_notMem_badPrimes (hv : v ∉ W.badPrimes R) :
    v.valuation K W.Δ = 1 :=
  not_not.mp fun hne ↦ hv (.inl (.inl (.inl (.inr hne))))

lemma valuation_two_eq_one_of_notMem_badPrimes (hv : v ∉ W.badPrimes R) :
    v.valuation K 2 = 1 :=
  not_not.mp fun hne ↦ hv (.inl (.inl (.inl (.inl hne))))

/-- Away from the bad primes, `disc f` is a `v`-adic unit: `Δ = 16 · disc f`, and both `Δ`
and `2` are `v`-adic units. -/
lemma valuation_discr_eq_one_of_notMem_badPrimes [W.IsCharNeTwoNF] (hv : v ∉ W.badPrimes R) :
    v.valuation K W.f.discr = 1 := by
  have h16 : v.valuation K 16 = 1 := by
    rw [show (16 : K) = 2 ^ 4 by norm_num, map_pow,
      W.valuation_two_eq_one_of_notMem_badPrimes R hv, one_pow]
  have hΔ := W.valuation_Δ_eq_one_of_notMem_badPrimes R hv
  rwa [W.Δ_eq_discr_f, map_mul, h16, one_mul] at hΔ

open WithZero in
lemma exp_neg_one_le_valuation_discr_of_notMem_discBadPrimes (hv : v ∉ W.discBadPrimes R) :
    exp (-1 : ℤ) ≤ v.valuation K W.f.discr :=
  not_not.mp fun hne ↦ hv (.inl (.inl (.inl hne)))

lemma valuation_a₂_le_one_of_notMem_discBadPrimes (hv : v ∉ W.discBadPrimes R) :
    v.valuation K W.a₂ ≤ 1 :=
  not_lt.mp fun hlt ↦ hv (.inl (.inl (.inr hlt)))

lemma valuation_a₄_le_one_of_notMem_discBadPrimes (hv : v ∉ W.discBadPrimes R) :
    v.valuation K W.a₄ ≤ 1 :=
  not_lt.mp fun hlt ↦ hv (.inl (.inr hlt))

lemma valuation_a₆_le_one_of_notMem_discBadPrimes (hv : v ∉ W.discBadPrimes R) :
    v.valuation K W.a₆ ≤ 1 :=
  not_lt.mp fun hlt ↦ hv (.inr hlt)

lemma notMem_discBadPrimes_of_notMem_badPrimes₂ (hv : v ∉ W.badPrimes₂ R) :
    v ∉ W.discBadPrimes R :=
  fun h ↦ hv (.inl h)

lemma valuation_two_eq_one_of_notMem_badPrimes₂ (hv : v ∉ W.badPrimes₂ R) :
    v.valuation K 2 = 1 :=
  not_not.mp fun hne ↦ hv (.inr hne)

/-- Away from `badPrimes₂`, the residue characteristic is odd. -/
lemma two_notMem_asIdeal_of_notMem_badPrimes₂ (hv : v ∉ W.badPrimes₂ R) :
    (2 : R) ∉ v.asIdeal := by
  have h := W.valuation_two_eq_one_of_notMem_badPrimes₂ R hv
  rw [← map_ofNat (algebraMap R K) 2] at h
  exact v.valuation_eq_one_iff_notMem.mp h

lemma discBadPrimes_subset_badPrimes₂ : W.discBadPrimes R ⊆ W.badPrimes₂ R :=
  Set.subset_union_left

open WithZero in
/-- The refined bad set is contained in the old one: away from `badPrimes`, both `2` and
`disc f` are `v`-adic units and the coefficients are `v`-integral. -/
lemma badPrimes₂_subset_badPrimes [W.IsCharNeTwoNF] : W.badPrimes₂ R ⊆ W.badPrimes R := by
  refine fun v hv ↦ by_contra fun hb ↦ ?_
  rcases hv with (((hd | h) | h) | h) | h2
  · exact hd <| (le_of_le_of_eq (exp_le_exp.mpr (by lia)) exp_zero).trans
      (W.valuation_discr_eq_one_of_notMem_badPrimes R hb).ge
  · exact hb (.inl (.inl (.inr h)))
  · exact hb (.inl (.inr h))
  · exact hb (.inr h)
  · exact hb (.inl (.inl (.inl (.inl h2))))

end BadPrimes

section DerivativeUnit

/- `f'(x)` is a unit at a rational root `x` of `f` whenever the coefficients are integral and
the valuation of `disc f` is `1` or `exp (-1)`: this is the arithmetic input for the
`2`-torsion `x - T` representative, both at good primes and at primes with
`v(disc f) = exp (-1)`. -/

/-- The discriminant of `f` is a polynomial in the coefficients of `W`, so it is integral
wherever they are. -/
lemma valuation_discr_le_one {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (ν : Valuation K Γ)
    (ha₂ : ν W.a₂ ≤ 1) (ha₄ : ν W.a₄ ≤ 1) (ha₆ : ν W.a₆ ≤ 1) : ν W.f.discr ≤ 1 := by
  have h : W.a₂ ^ 2 * W.a₄ ^ 2 - 4 * W.a₄ ^ 3 - 4 * W.a₂ ^ 3 * W.a₆ - 27 * W.a₆ ^ 2
      + 18 * W.a₂ * W.a₄ * W.a₆ ∈ ν.integer :=
    add_mem (sub_mem (sub_mem (sub_mem (mul_mem (pow_mem ha₂ 2) (pow_mem ha₄ 2))
      (mul_mem (ofNat_mem _ 4) (pow_mem ha₄ 3))) (mul_mem (mul_mem (ofNat_mem _ 4)
        (pow_mem ha₂ 3)) ha₆)) (mul_mem (ofNat_mem _ 27) (pow_mem ha₆ 2)))
      (mul_mem (mul_mem (mul_mem (ofNat_mem _ 18) ha₂) ha₄) ha₆)
  rw [W.discr_f]
  exact h

open WithZero in
private lemma eq_one_of_le_one_of_exp_neg_one_le_sq {t : ℤᵐ⁰} (h1 : t ≤ 1)
    (h2 : exp (-1) ≤ t ^ 2) : t = 1 := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at h2
  rw [← exp_log ht0] at h1 h2 ⊢
  rw [← exp_nsmul, two_nsmul] at h2
  rw [← exp_zero] at h1
  rw [exp_eq_one]
  have h1' := exp_le_exp.mp h1
  have h2' := exp_le_exp.mp h2
  lia

open WithZero in
/-- If `x` is a rational root of `f` and the coefficients of the cubic are `ν`-integral with
`exp (-1) ≤ ν (disc f)`, then `f'(x)` is a `ν`-unit: `disc f = (fCofactor x).discr * f'(x)²`
with both factors integral, and the square `ν (f'(x))²` cannot equal `exp (-1)`. -/
lemma valuation_deriv_eval_eq_one (ν : Valuation K ℤᵐ⁰) {x : K} (hx : W.f.eval x = 0)
    (ha₂ : ν W.a₂ ≤ 1) (ha₄ : ν W.a₄ ≤ 1) (ha₆ : ν W.a₆ ≤ 1)
    (hd : exp (-1) ≤ ν W.f.discr) :
    ν (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 1 := by
  have hx1 : ν x ≤ 1 := by
    rw [eval_f] at hx
    exact ν.le_one_of_root_cubic ha₂ ha₄ ha₆ hx
  have hfx : 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ ∈ ν.integer :=
    add_mem (add_mem (mul_mem (ofNat_mem _ 3) (pow_mem hx1 2))
      (mul_mem (mul_mem (ofNat_mem _ 2) ha₂) hx1)) ha₄
  have hcd' : (x + W.a₂) ^ 2 - 4 * (x ^ 2 + W.a₂ * x + W.a₄) ∈ ν.integer :=
    sub_mem (pow_mem (add_mem hx1 ha₂) 2) (mul_mem (ofNat_mem _ 4)
      (add_mem (add_mem (pow_mem hx1 2) (mul_mem ha₂ hx1)) ha₄))
  have hcd : ν (W.fCofactor x).discr ≤ 1 := by rw [W.discr_fCofactor x]; exact hcd'
  rw [W.discr_f_eq_discr_fCofactor_mul_sq hx, map_mul, map_pow] at hd
  exact eq_one_of_le_one_of_exp_neg_one_le_sq hfx (hd.trans (mul_le_of_le_one_left' hcd))

end DerivativeUnit

section RingOfIntegers

variable (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K]
  [IsFractionRing R K]

/-- The ring of integers of the field factor `K[X]/(p)` over `R`. -/
noncomputable abbrev ringOfIntegersFactor (p : W.f.Factors) : Type _ :=
  integralClosure R (𝕃 p)

/-- The ring of integers of a field factor is a Dedekind domain: it is the integral closure
of `R` in a finite separable extension of the fraction field `K`. -/
instance isDedekindDomain_ringOfIntegersFactor [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors) :
    IsDedekindDomain (W.ringOfIntegersFactor R p) :=
  have := AdjoinRoot.isSeparable_of_separable (separable_f W) p
  IsIntegralClosure.isDedekindDomain R K (𝕃 p) _

/-- A field factor is the fraction field of its ring of integers. -/
instance isFractionRing_ringOfIntegersFactor [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors) :
    IsFractionRing (W.ringOfIntegersFactor R p) (𝕃 p) :=
  have := AdjoinRoot.isSeparable_of_separable (separable_f W) p
  IsIntegralClosure.isFractionRing_of_finite_extension R K (𝕃 p) _

/-- The ring of integers of a field factor is torsion-free over `R`, as `R` embeds into it. -/
instance instIsTorsionFreeRingOfIntegersFactor (p : W.f.Factors) :
    Module.IsTorsionFree R (W.ringOfIntegersFactor R p) := by
  rw [Module.isTorsionFree_iff_algebraMap_injective]
  have hinj : Function.Injective (algebraMap R (𝕃 p)) := by
    rw [IsScalarTower.algebraMap_eq R K (𝕃 p)]
    exact (ι p).injective.comp (IsFractionRing.injective R K)
  exact fun a b hab ↦ hinj (congrArg Subtype.val hab)

/-- The `w`-adic valuation of an element of `K` is the `v`-adic valuation of the prime `v`
below `w`, raised to the ramification index. -/
lemma valuation_algebraMap_eq [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor R p)) (z : K) :
    (w.below R).valuation K z ^ ((w.below R).asIdeal.ramificationIdx' w.asIdeal) =
      w.valuation (𝕃 p) (ι p z) :=
  HeightOneSpectrum.valuation_liesOver _ _ _ z

/-- If `z` is integral at the prime below `w`, then it is integral at `w`. -/
lemma valuation_algebraMap_le_one [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor R p)) {z : K}
    (hz : (w.below R).valuation K z ≤ 1) :
    w.valuation (𝕃 p) (ι p z) ≤ 1 := by
  rw [← W.valuation_algebraMap_eq R p w z]
  simpa using pow_le_pow_left' hz _

/-- A prime `w` of the ring of integers of a field factor that does not lie above `S` lies
over a prime of `R` outside `S`. -/
lemma below_notMem_of_notMem_primesAbove [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors)
    {S : Set (HeightOneSpectrum R)} {w : HeightOneSpectrum (W.ringOfIntegersFactor R p)}
    (hw : w ∉ HeightOneSpectrum.primesAbove R (W.ringOfIntegersFactor R p) S) : w.below R ∉ S :=
  fun hv ↦ hw ((HeightOneSpectrum.mem_primesAbove_iff R _ _ w).mpr hv)

/-- `θ` satisfies the Weierstrass cubic in the field factor `K[X]/(p)`. -/
lemma root_cubic_eq_zero (p : W.f.Factors) :
    θ p ^ 3 + ι p W.a₂ * θ p ^ 2 + ι p W.a₄ * θ p + ι p W.a₆ = 0 := by
  have hz : AdjoinRoot.mk (p : K[X]) W.f = 0 :=
    AdjoinRoot.mk_eq_zero.mpr p.dvd
  simpa [f, AdjoinRoot.algebraMap_eq] using hz

/-- The Bézout identity behind `separable_f` at the level of `disc f`, evaluated at `θ`:
`f′(θ)` times an explicit quadratic in `θ` with integral coefficients equals `disc f`.
(The classical identity with `Δ` on the right is `16` times this one; this version stays
useful at even places.) -/
lemma deriv_root_mul_eq_discr_f (p : W.f.Factors) :
    (3 * θ p ^ 2 + 2 * ι p W.a₂ * θ p + ι p W.a₄)
        * ((2 * ι p W.a₂ ^ 2 - 6 * ι p W.a₄) * θ p ^ 2
          + (2 * ι p W.a₂ ^ 3 - 7 * ι p W.a₂ * ι p W.a₄ + 9 * ι p W.a₆) * θ p
          + (ι p W.a₂ ^ 2 * ι p W.a₄ - 4 * ι p W.a₄ ^ 2 + 3 * ι p W.a₂ * ι p W.a₆)) =
      ι p W.f.discr := by
  have hd : ι p W.f.discr = ι p W.a₂ ^ 2 * ι p W.a₄ ^ 2 - 4 * ι p W.a₄ ^ 3
      - 4 * ι p W.a₂ ^ 3 * ι p W.a₆ - 27 * ι p W.a₆ ^ 2
      + 18 * ι p W.a₂ * ι p W.a₄ * ι p W.a₆ := by
    rw [W.discr_f]
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]
  rw [hd]
  linear_combination (-(18 * ι p W.a₄ - 6 * ι p W.a₂ ^ 2) * θ p
    - (15 * ι p W.a₂ * ι p W.a₄ - 4 * ι p W.a₂ ^ 3 - 27 * ι p W.a₆)) * W.root_cubic_eq_zero p

/-- The cofactor `f / (X - x)`, computed in the field factor `K[X]/(p)`. -/
lemma mk_fCofactor_eq (p : W.f.Factors) (x : K) :
    AdjoinRoot.mk (p : K[X]) (W.fCofactor x) =
      θ p ^ 2 + (ι p x + ι p W.a₂) * θ p + (ι p x ^ 2 + ι p W.a₂ * ι p x + ι p W.a₄) := by
  simp only [fCofactor, map_add, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
    ← AdjoinRoot.algebraMap_eq]

variable [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors)
  {w : HeightOneSpectrum (W.ringOfIntegersFactor R p)}
  (ha₂ : (w.below R).valuation K W.a₂ ≤ 1) (ha₄ : (w.below R).valuation K W.a₄ ≤ 1)
  (ha₆ : (w.below R).valuation K W.a₆ ≤ 1) (hd : (w.below R).valuation K W.f.discr = 1)
  -- (this is `w.valuation (𝕃 p) (3 * θ p ^ 2 + 2 * ι p W.a₂ * θ p + ι p W.a₄) = 1`;
  -- `variable` commands cannot use the local notation)
  (hderiv : w.valuation (AdjoinRoot (p : K[X]))
    (3 * AdjoinRoot.root (p : K[X]) ^ 2
      + 2 * algebraMap K (AdjoinRoot (p : K[X])) W.a₂ * AdjoinRoot.root (p : K[X])
      + algebraMap K (AdjoinRoot (p : K[X])) W.a₄) = 1)

include ha₂ ha₄ ha₆ in
/-- If the coefficients of the cubic are integral at the prime below `w`, then the root `θ` is
`w`-integral: it satisfies the monic cubic `f`, whose coefficients are integral at `w`. -/
lemma valuation_root_le_one : w.valuation (𝕃 p) (θ p) ≤ 1 :=
  Valuation.le_one_of_root_cubic _
    (W.valuation_algebraMap_le_one R p w ha₂)
    (W.valuation_algebraMap_le_one R p w ha₄)
    (W.valuation_algebraMap_le_one R p w ha₆)
    (W.root_cubic_eq_zero p)

/-- An element of `K` with trivial valuation at the prime below `w` has trivial valuation
at `w`. -/
lemma valuation_algebraMap_eq_one {z : K} (hz : (w.below R).valuation K z = 1) :
    w.valuation (𝕃 p) (ι p z) = 1 := by
  rw [← W.valuation_algebraMap_eq R p w z, hz, one_pow]

include ha₂ ha₄ ha₆ in
/-- If the coefficients of the cubic are integral at the prime below `w`, then `f' θ` is
`w`-integral. -/
lemma valuation_deriv_root_le_one :
    w.valuation (𝕃 p) (3 * θ p ^ 2 + 2 * ι p W.a₂ * θ p + ι p W.a₄) ≤ 1 := by
  have ht := W.valuation_root_le_one R p ha₂ ha₄ ha₆
  have h : 3 * θ p ^ 2 + 2 * ι p W.a₂ * θ p + ι p W.a₄ ∈ (w.valuation (𝕃 p)).integer :=
    add_mem (add_mem (mul_mem (ofNat_mem _ 3) (pow_mem ht 2))
      (mul_mem (mul_mem (ofNat_mem _ 2) (W.valuation_algebraMap_le_one R p w ha₂)) ht))
      (W.valuation_algebraMap_le_one R p w ha₄)
  exact h

include ha₂ ha₄ ha₆ hd in
/-- If the coefficients of the cubic are integral and `disc f` is a unit at the prime below
`w`, then `f' θ = 3 θ ^ 2 + 2 a₂ θ + a₄` is a `w`-unit.

Evaluating the Bézout identity behind `separable_f` at `θ` gives `f'(θ) * c(θ) = disc f`
(`deriv_root_mul_eq_discr_f`) for an explicit quadratic `c` with `w`-integral coefficients.
Both factors are integral at `w` and the product is a unit, so both are units. -/
lemma valuation_deriv_root_eq_one :
    w.valuation (𝕃 p) (3 * θ p ^ 2 + 2 * ι p W.a₂ * θ p + ι p W.a₄) = 1 := by
  set L := 𝕃 p
  set ν := w.valuation L
  set t := θ p
  set A₂ := algebraMap K L W.a₂
  set A := algebraMap K L W.a₄
  set B := algebraMap K L W.a₆
  have hA₂ : ν A₂ ≤ 1 := W.valuation_algebraMap_le_one R p w ha₂
  have hA : ν A ≤ 1 := W.valuation_algebraMap_le_one R p w ha₄
  have hB : ν B ≤ 1 := W.valuation_algebraMap_le_one R p w ha₆
  have ht : ν t ≤ 1 := W.valuation_root_le_one R p ha₂ ha₄ ha₆
  -- both factors in `deriv_root_mul_eq_discr_f` are integral, and their product is a unit
  have hD : ν (3 * t ^ 2 + 2 * A₂ * t + A) ≤ 1 :=
    W.valuation_deriv_root_le_one R p ha₂ ha₄ ha₆
  have hC : (2 * A₂ ^ 2 - 6 * A) * t ^ 2 + (2 * A₂ ^ 3 - 7 * A₂ * A + 9 * B) * t
      + (A₂ ^ 2 * A - 4 * A ^ 2 + 3 * A₂ * B) ∈ ν.integer := by
    refine add_mem (add_mem (mul_mem ?_ (pow_mem ht 2)) (mul_mem ?_ ht)) ?_
    · exact sub_mem (mul_mem (ofNat_mem _ 2) (pow_mem hA₂ 2)) (mul_mem (ofNat_mem _ 6) hA)
    · exact add_mem (sub_mem (mul_mem (ofNat_mem _ 2) (pow_mem hA₂ 3))
        (mul_mem (mul_mem (ofNat_mem _ 7) hA₂) hA)) (mul_mem (ofNat_mem _ 9) hB)
    · exact add_mem (sub_mem (mul_mem (pow_mem hA₂ 2) hA)
        (mul_mem (ofNat_mem _ 4) (pow_mem hA 2))) (mul_mem (mul_mem (ofNat_mem _ 3) hA₂) hB)
  refine ν.eq_one_of_mul_eq_one hD hC ?_
  rw [deriv_root_mul_eq_discr_f]
  exact W.valuation_algebraMap_eq_one R p hd

include ha₂ ha₄ ha₆ hderiv in
/-- If the coefficients of the cubic are integral at the prime below `w` and `f' θ` is a
`w`-unit, and if `x` is `w`-integral and `x - θ` is not a `w`-unit, then the cofactor
`x ^ 2 + θ x + θ ^ 2 + a₂ (x + θ) + a₄` is a `w`-unit: modulo `x - θ` it equals `f' θ`. -/
lemma valuation_cofactor_eq_one {x : K}
    (hx : w.valuation (𝕃 p) (ι p x) ≤ 1)
    (hlt : w.valuation (𝕃 p) (ι p x - θ p) < 1) :
    w.valuation (𝕃 p) (ι p x ^ 2 + θ p * ι p x + θ p ^ 2
      + ι p W.a₂ * (ι p x + θ p) + ι p W.a₄) = 1 := by
  set L := 𝕃 p
  set ν := w.valuation L
  set t := θ p
  set s := algebraMap K L x
  set A₂ := algebraMap K L W.a₂
  set A := algebraMap K L W.a₄
  have hA₂ : ν A₂ ≤ 1 := W.valuation_algebraMap_le_one R p w ha₂
  have ht : ν t ≤ 1 := W.valuation_root_le_one R p ha₂ ha₄ ha₆
  have h2t : s + 2 * t + A₂ ∈ ν.integer :=
    add_mem (add_mem hx (mul_mem (ofNat_mem _ 2) ht)) hA₂
  have hlt' : ν ((s - t) * (s + 2 * t + A₂)) < ν (3 * t ^ 2 + 2 * A₂ * t + A) := by
    rw [hderiv, map_mul]
    exact (mul_le_of_le_one_right' h2t).trans_lt hlt
  rw [show s ^ 2 + t * s + t ^ 2 + A₂ * (s + t) + A
      = (s - t) * (s + 2 * t + A₂) + (3 * t ^ 2 + 2 * A₂ * t + A) by ring,
    ν.map_add_eq_of_lt_right hlt', hderiv]

include ha₂ ha₄ ha₆ in
/-- If `x` is a root of `f`, then at a prime `w` at which (i.e. at the prime of `R` below
which) the coefficients of the cubic are integral and `f'(x)` is a unit, the `p`-component of
the `x - T` representative is a unit.

Both `x` and `θ` are roots of `f`, so `x - θ` times the cofactor is `0` and, `L` being a field,
one of the two factors vanishes. If `x = θ` the component is `f'(x)`; if the cofactor vanishes
the component is `x - θ` and `f'(x) = (x - θ)(2x + θ + a₂)`. Either way `hdx` makes it a unit.

At a good prime, `hdx` is supplied by `valuation_deriv_eval_eq_one`; at an odd prime with
`v(disc f) = exp (-1)` the same lemma applies, so the `2`-torsion representative is unramified
there as well. -/
lemma valuation_projFactor_torsion_eq_one {x : K} (hx : W.f.eval x = 0)
    (hdx : (w.below R).valuation K (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 1) :
    w.valuation (𝕃 p) (ι p x - θ p + AdjoinRoot.mk (p : K[X]) (W.fCofactor x)) = 1 := by
  rw [W.mk_fCofactor_eq p x]
  set L := 𝕃 p
  set ν := w.valuation L
  set t := θ p
  set s := algebraMap K L x with hsdef
  set A₂ := algebraMap K L W.a₂ with hA₂def
  set A := algebraMap K L W.a₄ with hAdef
  set B := algebraMap K L W.a₆ with hBdef
  have hA₂ : ν A₂ ≤ 1 := W.valuation_algebraMap_le_one R p w ha₂
  have hA : ν A ≤ 1 := W.valuation_algebraMap_le_one R p w ha₄
  have hB : ν B ≤ 1 := W.valuation_algebraMap_le_one R p w ha₆
  have ht : ν t ≤ 1 := W.valuation_root_le_one R p ha₂ ha₄ ha₆
  -- the `w`-unit `f'(x)`, transported to `L`
  have hderiv : ν (3 * s ^ 2 + 2 * A₂ * s + A) = 1 := by
    simpa only [map_add, map_mul, map_pow, map_ofNat]
      using W.valuation_algebraMap_eq_one R p (w := w) hdx
  -- `x` is a root of the cubic too, hence integral at `w`
  have hs : s ^ 3 + A₂ * s ^ 2 + A * s + B = 0 := by
    rw [hsdef, hA₂def, hAdef, hBdef, ← W.map_eval_f, hx, map_zero]
  have hs1 : ν s ≤ 1 := ν.le_one_of_root_cubic hA₂ hA hB hs
  have hprod : (s - t) * (t ^ 2 + (s + A₂) * t + (s ^ 2 + A₂ * s + A)) = 0 := by
    linear_combination hs - W.root_cubic_eq_zero p
  rcases mul_eq_zero.mp hprod with h0 | h0
  · -- `x = θ`: the component is `f'(x)`
    rw [h0, zero_add, show t ^ 2 + (s + A₂) * t + (s ^ 2 + A₂ * s + A)
        = 3 * s ^ 2 + 2 * A₂ * s + A by linear_combination -(t + 2 * s + A₂) * h0, hderiv]
  · -- the cofactor vanishes: the component is `x - θ`, and `f'(x) = (x - θ)(2x + θ + a₂)`
    rw [h0, add_zero]
    have hst : s - t ∈ ν.integer := sub_mem hs1 ht
    have h2t : 2 * s + t + A₂ ∈ ν.integer :=
      add_mem (add_mem (mul_mem (ofNat_mem _ 2) hs1) ht) hA₂
    refine ν.eq_one_of_mul_eq_one hst h2t ?_
    rw [show (s - t) * (2 * s + t + A₂) = 3 * s ^ 2 + 2 * A₂ * s + A by linear_combination -h0,
      hderiv]

end RingOfIntegers

section Core

variable [W.IsElliptic] [W.IsCharNeTwoNF]
  (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
  (p : W.f.Factors)
  {x y : K} (h : W.Equation x y) (hx : W.f.eval x ≠ 0)
  (u : (AdjoinRoot (p : K[X]))ˣ)
  (hu : (u : AdjoinRoot (p : K[X])) =
    algebraMap K (AdjoinRoot (p : K[X])) x - AdjoinRoot.root (p : K[X]))
  (w : HeightOneSpectrum (W.ringOfIntegersFactor R p))
  (ha₂ : (w.below R).valuation K W.a₂ ≤ 1) (ha₄ : (w.below R).valuation K W.a₄ ≤ 1)
  (ha₆ : (w.below R).valuation K W.a₆ ≤ 1)
  -- (this is `w.valuation (𝕃 p) (3 * θ p ^ 2 + 2 * ι p W.a₂ * θ p + ι p W.a₄) = 1`;
  -- `variable` commands cannot use the local notation)
  (hderiv : w.valuation (AdjoinRoot (p : K[X]))
    (3 * AdjoinRoot.root (p : K[X]) ^ 2
      + 2 * algebraMap K (AdjoinRoot (p : K[X])) W.a₂ * AdjoinRoot.root (p : K[X])
      + algebraMap K (AdjoinRoot (p : K[X])) W.a₄) = 1)

include h hx hu ha₂ ha₄ ha₆

/-- Non-integral case: `x` has a pole at the prime of `R` below `w`.

The coefficients `a₂`, `a₄`, `a₆` and the root `θ` are `w`-integral, so `1 < ν x` makes the
leading term of the cubic dominate: `ν (f x) = ν x ^ 3`, hence `ν y ^ 2 = ν x ^ 3`. Also
`ν θ ≤ 1 < ν x`
gives `ν (x - θ) = ν x`. Therefore `ν (x - θ) = ν (y / x) ^ 2` is an even power. -/
lemma even_valuationOfNeZero_sub_root_of_one_lt
    (hx' : 1 < w.valuation (𝕃 p) (ι p x)) :
    (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) := by
  set L := 𝕃 p
  set ν := w.valuation L
  have hx0 : algebraMap K L x ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hx'
    exact absurd hx' (by simp)
  have hx0' : ν (algebraMap K L x) ≠ 0 := ν.ne_zero_iff.mpr hx0
  have hy0 : algebraMap K L y ≠ 0 := (_root_.map_ne_zero _).mpr (W.ne_zero_of_eval_f_ne_zero h hx)
  -- the Weierstrass equation, transported to `L`
  have heq : (algebraMap K L y) ^ 2 = algebraMap K L x ^ 3 +
      algebraMap K L W.a₂ * algebraMap K L x ^ 2 +
      algebraMap K L W.a₄ * algebraMap K L x + algebraMap K L W.a₆ := by
    rw [← W.map_eval_f, (equation_iff_eval_f_eq_sq W x y).mp h, map_pow]
  have hval : ν (algebraMap K L y) ^ 2 = ν (algebraMap K L x) ^ 3 := by
    rw [← map_pow, heq, ν.map_cubic_of_one_lt (W.valuation_algebraMap_le_one R p w ha₂)
      (W.valuation_algebraMap_le_one R p w ha₄) (W.valuation_algebraMap_le_one R p w ha₆) hx']
  -- `ν (x - θ) = ν x`, since `θ` is integral and `x` is not
  have hu' : ν (u : L) = ν (algebraMap K L x) := by
    rw [hu]
    exact Valuation.map_sub_eq_of_lt_left _ ((W.valuation_root_le_one R p ha₂ ha₄ ha₆).trans_lt hx')
  have hkey : ν (u : L) = ν ((Units.mk0 _ (div_ne_zero hy0 hx0) : Lˣ) : L) ^ 2 := by
    rw [hu', Units.val_mk0, map_div₀, div_pow, hval, eq_div_iff (pow_ne_zero 2 hx0'), mul_comm]
    exact (pow_succ _ 2).symm
  simpa using w.dvd_toAdd_valuationOfNeZero hkey

include hderiv in
/-- Integral case: `x` is integral at the prime of `R` below `w`.

Over `L` the Weierstrass equation factors as `y ^ 2 = (x - θ) * c` with cofactor
`c = x ^ 2 + θ x + θ ^ 2 + a₂ (x + θ) + a₄`. If `x - θ` is a `w`-unit there is nothing to do.
Otherwise `ν (x - θ) < 1`, and since `c = (x - θ) * (x + 2 θ + a₂) + f' θ` with `f' θ` a
`w`-unit, the cofactor is a `w`-unit. Hence `ν (x - θ) = ν y ^ 2` is an even power. -/
lemma even_valuationOfNeZero_sub_root_of_le_one
    (hx' : w.valuation (𝕃 p) (ι p x) ≤ 1) :
    (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) := by
  set L := 𝕃 p
  set ν := w.valuation L
  set t := θ p
  set A₂ := algebraMap K L W.a₂ with hA₂def
  set A := algebraMap K L W.a₄ with hAdef
  have ht : ν t ≤ 1 := W.valuation_root_le_one R p ha₂ ha₄ ha₆
  -- `y ^ 2 = (x - θ) * (x ^ 2 + θ x + θ ^ 2 + a₂ (x + θ) + a₄)` over `L`
  have heqL : (algebraMap K L y) ^ 2 = algebraMap K L x ^ 3 + A₂ * algebraMap K L x ^ 2 +
      A * algebraMap K L x + algebraMap K L W.a₆ := by
    rw [hA₂def, hAdef, ← W.map_eval_f, (equation_iff_eval_f_eq_sq W x y).mp h, map_pow]
  have hfac : (u : L) * (algebraMap K L x ^ 2 + t * algebraMap K L x + t ^ 2
        + A₂ * (algebraMap K L x + t) + A) =
      (algebraMap K L y) ^ 2 := by
    rw [hu]
    linear_combination -W.root_cubic_eq_zero p - heqL
  have hu1 : ν (u : L) ≤ 1 := by rw [hu]; exact ν.map_sub_le hx' ht
  by_cases hlt : ν (u : L) = 1
  · -- `x - θ` is a unit, so its valuation is trivially even
    have hkey : ν (u : L) = ν ((1 : Lˣ) : L) ^ 2 := by rw [Units.val_one, map_one, one_pow, hlt]
    simpa using w.dvd_toAdd_valuationOfNeZero hkey
  -- otherwise `w` divides `x - θ`, and then it cannot divide the cofactor
  replace hlt : ν (u : L) < 1 := lt_of_le_of_ne hu1 hlt
  rw [hu] at hlt
  have hcof : ν (algebraMap K L x ^ 2 + t * algebraMap K L x + t ^ 2
      + A₂ * (algebraMap K L x + t) + A) = 1 :=
    W.valuation_cofactor_eq_one R p ha₂ ha₄ ha₆ hderiv hx' hlt
  have hy0 : algebraMap K L y ≠ 0 := (_root_.map_ne_zero _).mpr (W.ne_zero_of_eval_f_ne_zero h hx)
  have hkey : ν (u : L) = ν ((Units.mk0 _ hy0 : Lˣ) : L) ^ 2 := by
    rw [Units.val_mk0, ← map_pow, ← hfac, map_mul, hcof, mul_one]
  simpa using w.dvd_toAdd_valuationOfNeZero hkey

include hderiv in
/-- The arithmetic core of Step 6, generic case, with all the group theory stripped away:
for `(x, y)` on `W` with `f x ≠ 0`, and `w` a prime of the ring of integers of the field factor
`K[X]/(p)` such that the coefficients of the cubic are integral at the prime of `R` below `w`
and `f' θ` is a `w`-unit, the `w`-adic valuation of `x - θ` is even.

The proof splits on whether `x` has a pole at the prime of `R` below `w`. -/
lemma even_valuationOfNeZero_sub_root :
    (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) := by
  by_cases hx' : 1 < w.valuation (𝕃 p) (ι p x)
  · exact W.even_valuationOfNeZero_sub_root_of_one_lt R p h hx u hu w ha₂ ha₄ ha₆ hx'
  · exact W.even_valuationOfNeZero_sub_root_of_le_one R p h hx u hu w ha₂ ha₄ ha₆ hderiv
      (not_lt.mp hx')

end Core

section Selmer

/-- If `x` is a root of `f`, then every irreducible factor of `f` other than `X - x` divides
the cofactor `f / (X - x)`. -/
lemma dvd_fCofactor_of_ne {x : K} (hx : W.f.eval x = 0) (p : W.f.Factors)
    (hp : (p : K[X]) ≠ X - C x) : (p : K[X]) ∣ W.fCofactor x := by
  have hdvd : (p : K[X]) ∣ W.fCofactor x * (X - C x) := by
    rw [← W.f_eq_mul_of_eval_eq_zero hx]
    exact p.dvd
  refine (p.prime.2.2 _ _ hdvd).resolve_right fun h ↦ hp ?_
  exact eq_of_monic_of_associated p.monic (monic_X_sub_C x)
    (p.irreducible.associated_of_dvd (irreducible_X_sub_C x) h)

/-- Consequently the cofactor dies in every field factor except the one coming from `X - x`. -/
lemma mk_fCofactor_eq_zero {x : K} (hx : W.f.eval x = 0) (p : W.f.Factors)
    (hp : (p : K[X]) ≠ X - C x) : AdjoinRoot.mk (p : K[X]) (W.fCofactor x) = 0 :=
  AdjoinRoot.mk_eq_zero.mpr (W.dvd_fCofactor_of_ne hx p hp)

variable [W.IsElliptic] [W.IsCharNeTwoNF]

/-- The image of the generic `x - T` representative in the field factor `K[X]/(p)` is `x - θ`. -/
lemma projFactor_mk_C_sub_X (x : K) (p : W.f.Factors) :
    AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p (AdjoinRoot.mk W.f (C x - X)) =
      ι p x - θ p := by
  rw [AdjoinRoot.projFactor_mk, map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
    AdjoinRoot.algebraMap_eq]

/-- The image of the `2`-torsion `x - T` representative in the field factor `K[X]/(p)`. -/
lemma projFactor_mk_C_sub_X_add_fCofactor (x : K) (p : W.f.Factors) :
    AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p
        (AdjoinRoot.mk W.f (C x - X + W.fCofactor x)) =
      ι p x - θ p + AdjoinRoot.mk (p : K[X]) (W.fCofactor x) := by
  rw [AdjoinRoot.projFactor_mk, map_add, map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
    AdjoinRoot.algebraMap_eq]

variable (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
  (S : Set (HeightOneSpectrum R))

/-- The `2`-Selmer group of the field factor `AdjoinRoot p` of `W.A`, relative to the primes of
its ring of integers lying above the primes in `S`. -/
noncomputable def selmerGroupFactor (p : W.f.Factors) :
    Subgroup (Units.modPow (𝕃 p) 2) :=
  IsDedekindDomain.selmerGroupAbove R (W.ringOfIntegersFactor R p) (𝕃 p) S 2

/-- `A(S,2)` in the product decomposition: the product of the `2`-Selmer groups of the field
factors of `W.A`. -/
noncomputable def selmerGroupPi :
    Subgroup ((p : W.f.Factors) → Units.modPow (𝕃 p) 2) :=
  Subgroup.pi Set.univ (W.selmerGroupFactor R S)

/-- `A(S,2)`, as a subgroup of `W.M`: the classes whose image in each field factor lies in the
`2`-Selmer group of that factor. Step 6 asserts that `im μ ≤ A(S,2)` for `S` the bad primes. -/
noncomputable def selmerGroupA : Subgroup W.M :=
  (W.selmerGroupPi R S).comap
    (AdjoinRoot.modPowEquivPiFactors W.f_ne_zero W.squarefree_f 2).toMonoidHom

lemma mem_selmerGroupA_iff (m : W.M) :
    m ∈ W.selmerGroupA R S ↔ ∀ p : W.f.Factors,
      AdjoinRoot.modPowEquivPiFactors W.f_ne_zero W.squarefree_f 2 m p ∈
        W.selmerGroupFactor R S p := by
  simp [selmerGroupA, selmerGroupPi, Subgroup.mem_pi]

/-!
#### The arithmetic input

Write `θ` for `AdjoinRoot.root p`, the image of the root `T` in the field factor `K[X]/(p)`,
and `𝓞` for the integral closure of `R` in `K[X]/(p)`, a Dedekind domain by
`isDedekindDomain_ringOfIntegersFactor` (an instance, in the `RingOfIntegers` section above).

The `p`-component of `μX x` is the square class of the reduction mod `p` of the `x - T`
representative, computed by `projFactor_mk_C_sub_X` and
`projFactor_mk_C_sub_X_add_fCofactor` below: it is `x - θ` in the generic case and
`x - θ + fCofactor x` when `x` is a root of `f`.

What has to be shown is that this class lies in the `2`-Selmer group of `K[X]/(p)`, i.e. that
`w (x - θ)` is even for every prime `w` of `𝓞` not lying above a prime of `S`; away from `S`,
the coefficients of the cubic are integral and `disc f` is a unit, by hypothesis.
The two cases are split off as `mem_selmerGroupFactor_of_eval_f_ne_zero` and
`mem_selmerGroupFactor_of_eval_f_eq_zero`.
-/

/-- Membership of the class of a unit in the `2`-Selmer group of a field factor: its valuation
is even at every prime of the ring of integers not lying above `S`. -/
lemma mem_selmerGroupFactor_unit_iff (p : W.f.Factors) (u : (𝕃 p)ˣ) :
    (QuotientGroup.mk u : Units.modPow (𝕃 p) 2) ∈ W.selmerGroupFactor R S p ↔
      ∀ w : HeightOneSpectrum (W.ringOfIntegersFactor R p),
        w ∉ HeightOneSpectrum.primesAbove R (W.ringOfIntegersFactor R p) S →
          (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) :=
  forall₂_congr fun w _ ↦ HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff w 2 u

/-- Membership of the class of a unit of the étale algebra in `A(S,2)`, componentwise: the
valuation of each `projFactor`-component is even at every prime of the corresponding ring of
integers that does not lie above `S`. -/
lemma mem_selmerGroupA_unit_iff (a : W.Aˣ) :
    (QuotientGroup.mk a : W.M) ∈ W.selmerGroupA R S ↔
      ∀ (p : W.f.Factors) (w : HeightOneSpectrum (W.ringOfIntegersFactor R p)),
        w ∉ HeightOneSpectrum.primesAbove R (W.ringOfIntegersFactor R p) S →
          (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero
            (Units.map (AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p).toMonoidHom a)) := by
  rw [mem_selmerGroupA_iff]
  refine forall_congr' fun p ↦ ?_
  rw [AdjoinRoot.modPowEquivPiFactors_mk, mem_selmerGroupFactor_unit_iff]

/-- The class of `-1` lies in `A(S,2)` for every `S`: all its valuations vanish. -/
lemma neg_one_mem_selmerGroupA : (QuotientGroup.mk (-1 : W.Aˣ) : W.M) ∈ W.selmerGroupA R S := by
  rw [mem_selmerGroupA_unit_iff]
  intro p w hw
  set u := Units.map (AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p).toMonoidHom
    (-1 : W.Aˣ) with hu
  have hsq : u ^ 2 = 1 := by rw [hu, ← map_pow]; simp
  have h1 : w.valuationOfNeZero u = 1 := by
    have h := congrArg w.valuationOfNeZero hsq
    rw [map_pow, map_one] at h
    exact pow_eq_one_iff_left two_ne_zero |>.mp h
  rw [h1]
  simp

variable (hSa₂ : ∀ v ∉ S, v.valuation K W.a₂ ≤ 1) (hSa₄ : ∀ v ∉ S, v.valuation K W.a₄ ≤ 1)
  (hSa₆ : ∀ v ∉ S, v.valuation K W.a₆ ≤ 1) (hSd : ∀ v ∉ S, v.valuation K W.f.discr = 1)

include hSa₂ hSa₄ hSa₆ hSd in
/-- Generic case of the arithmetic input: `f x ≠ 0`, so the `p`-component of `μX x` is the class
of `x - θ`. -/
lemma mem_selmerGroupFactor_of_eval_f_ne_zero {x y : K} (h : W.Equation x y)
    (hx : W.f.eval x ≠ 0) (p : W.f.Factors) :
    (((isUnit_mk_sub_X_of_eval_f_ne_zero hx).map
      (AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p)).unit :
        Units.modPow (𝕃 p) 2) ∈ W.selmerGroupFactor R S p := by
  rw [W.mem_selmerGroupFactor_unit_iff R S p]
  intro w hw
  have hv := W.below_notMem_of_notMem_primesAbove R p hw
  refine W.even_valuationOfNeZero_sub_root R p h hx _ ?_ w (hSa₂ _ hv) (hSa₄ _ hv) (hSa₆ _ hv)
    (W.valuation_deriv_root_eq_one R p (hSa₂ _ hv) (hSa₄ _ hv) (hSa₆ _ hv) (hSd _ hv))
  exact W.projFactor_mk_C_sub_X x p

include hSa₂ hSa₄ hSa₆ hSd in
/-- `2`-torsion case of the arithmetic input: `f x = 0`.

By `projFactor_mk_C_sub_X_add_fCofactor` the `p`-component of `μX x` is `x - θ + fCofactor x`,
which by `valuation_projFactor_torsion_eq_one` is a unit at every prime `w` not lying above
`S`. Its valuation is therefore `0`, in particular even. -/
lemma mem_selmerGroupFactor_of_eval_f_eq_zero {x : K} (hx : W.f.eval x = 0)
    (p : W.f.Factors) :
    (((isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero hx).map
      (AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p)).unit :
        Units.modPow (𝕃 p) 2) ∈ W.selmerGroupFactor R S p := by
  rw [W.mem_selmerGroupFactor_unit_iff R S p]
  intro w hw
  have hv := W.below_notMem_of_notMem_primesAbove R p hw
  set u := ((isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero hx).map
    (AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p)).unit with hudef
  have hd1 : WithZero.exp (-1 : ℤ) ≤ (w.below R).valuation K W.f.discr := by
    rw [hSd _ hv]
    exact (WithZero.exp_le_exp.mpr (by lia)).trans_eq WithZero.exp_zero
  have hval : w.valuation (𝕃 p) (u : 𝕃 p) = 1 := by
    rw [hudef, IsUnit.unit_spec, W.projFactor_mk_C_sub_X_add_fCofactor x p]
    exact W.valuation_projFactor_torsion_eq_one R p (hSa₂ _ hv) (hSa₄ _ hv) (hSa₆ _ hv) hx
      (W.valuation_deriv_eval_eq_one _ hx (hSa₂ _ hv) (hSa₄ _ hv) (hSa₆ _ hv) hd1)
  simpa using w.dvd_toAdd_valuationOfNeZero (n := 2) (z := 1) (by simp [hval])

section

variable [DecidableEq K]

include hSa₂ hSa₄ hSa₆ hSd in
/-- The heart of Step 6: for a point `(x, y)` of `W` and a field factor `K[X]/(p)` of `W.A`,
the square class of the image of the `x - T` map lies in the `2`-Selmer group of that factor. -/
lemma μX_component_mem_selmerGroupFactor {x y : K} (h : W.Equation x y) (p : W.f.Factors) :
    AdjoinRoot.modPowEquivPiFactors W.f_ne_zero W.squarefree_f 2 (W.μX x) p ∈
      W.selmerGroupFactor R S p := by
  rcases eq_or_ne (W.f.eval x) 0 with hx | hx
  · rw [μX_of_eval_f_eq_zero hx, AdjoinRoot.modPowEquivPiFactors_unit]
    exact W.mem_selmerGroupFactor_of_eval_f_eq_zero R S hSa₂ hSa₄ hSa₆ hSd hx p
  · rw [μX_of_eval_f_ne_zero hx, AdjoinRoot.modPowEquivPiFactors_unit]
    exact W.mem_selmerGroupFactor_of_eval_f_ne_zero R S hSa₂ hSa₄ hSa₆ hSd h hx p

include hSa₂ hSa₄ hSa₆ hSd in
/-- **Step 6**: the image of `μ` is contained in `A(S,2)`, whenever the coefficients of the
cubic are integral and `disc f` is a unit away from `S`. -/
theorem range_μ_le_selmerGroupA : (μ (W := W)).range ≤ W.selmerGroupA R S := by
  rintro _ ⟨P, rfl⟩
  obtain ⟨P, rfl⟩ := Multiplicative.ofAdd.surjective P
  rw [μ_apply]
  match P with
  | 0 => rw [μ₀_zero]; exact one_mem _
  | .some x y h =>
    rw [μ₀_some, mem_selmerGroupA_iff]
    exact fun p ↦ W.μX_component_mem_selmerGroupFactor R S hSa₂ hSa₄ hSa₆ hSd h.1 p

end

end Selmer

end WeierstrassCurve.Affine

end
