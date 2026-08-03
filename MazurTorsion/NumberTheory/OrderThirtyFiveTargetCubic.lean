/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.OrderThirtyFiveThreeDescent

/-!
# The cyclic cubic fibre of the order-35 three-isogeny candidate

For a point `(X,Y)` on the candidate target, a source abscissa above it has
to be a root of

`t^3 - X*t^2 + 28*t + 49`.

This file makes that fibre calculation into a checked interface.  Its
discriminant is `49` times the completed-square equation of the target, so
at a rational target point it is the square `(7*(2Y+4X+7))^2`.  Conversely,
any rational root of the fibre gives an explicit source point mapping to
`(X,Y)`.  Thus the remaining target descent can be stated exactly as a
rational-root problem for this fixed family of cyclic cubics; no additivity
claim about the coordinate candidate is used.
-/

open WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.OrderThirtyFive

open WeierstrassCurve.Affine

/-- The cubic whose rational roots are source abscissae above target
abscissa `X`. -/
def targetCubicFibre (X t : ℚ) : ℚ :=
  t ^ 3 - X * t ^ 2 + 28 * t + 49

/-- The standard coefficient discriminant of a cubic
`a*t^3+b*t^2+c*t+d`. -/
def targetCubicDiscriminant (a b c d : ℚ) : ℚ :=
  b ^ 2 * c ^ 2 - 4 * a * c ^ 3 - 4 * b ^ 3 * d -
    27 * a ^ 2 * d ^ 2 + 18 * a * b * c * d

/-- The fibre discriminant is `49` times the target completed-square
polynomial. -/
theorem targetCubicFibre_discriminant (X : ℚ) :
    targetCubicDiscriminant 1 (-X) 28 49 =
      49 * (4 * X ^ 3 + 16 * X ^ 2 - 504 * X - 3115) := by
  simp only [targetCubicDiscriminant]
  ring

/-- The target equation in completed-ordinate coordinates. -/
theorem veluThreeCandidateTarget_completedEquation
    {X Y : ℚ}
    (hP : veluThreeCandidateTarget.toAffine.Nonsingular X Y) :
    (2 * Y + 4 * X + 7) ^ 2 =
      4 * X ^ 3 + 16 * X ^ 2 - 504 * X - 3115 := by
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  norm_num [veluThreeCandidateTarget] at hcurve
  linear_combination 4 * hcurve

/-- At a target point the fibre discriminant has the displayed rational
square root. -/
theorem targetCubicFibre_discriminant_eq_square
    {X Y : ℚ}
    (hP : veluThreeCandidateTarget.toAffine.Nonsingular X Y) :
    targetCubicDiscriminant 1 (-X) 28 49 =
      (7 * (2 * Y + 4 * X + 7)) ^ 2 := by
  rw [targetCubicFibre_discriminant,
    ← veluThreeCandidateTarget_completedEquation hP]
  ring

/-- The completed ordinate of an affine target point is nonzero.  A zero
would make the point rational two-torsion, whereas the checked target
torsion subgroup is trivial. -/
theorem veluThreeCandidateTarget_completedOrdinate_ne_zero
    {X Y : ℚ}
    (hP : veluThreeCandidateTarget.toAffine.Nonsingular X Y) :
    2 * Y + 4 * X + 7 ≠ 0 := by
  intro hcompleted
  let P : veluThreeCandidateTarget.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some X Y hP
  have hself : P = -P := by
    dsimp only [P]
    rw [WeierstrassCurve.Affine.Point.neg_some]
    apply WeierstrassCurve.Affine.Point.some_eq_some
      veluThreeCandidateTarget
    · rfl
    · norm_num [WeierstrassCurve.Affine.negY,
        veluThreeCandidateTarget]
      linarith
  have htwo : (2 : ℕ) • P = 0 := by
    rw [two_nsmul]
    exact (add_eq_zero_iff_eq_neg).2 hself
  have hfinite : IsOfFinAddOrder P :=
    isOfFinAddOrder_iff_nsmul_eq_zero.mpr
      ⟨2, by norm_num, htwo⟩
  have hzero := veluThreeCandidateTarget_torsion_eq_zero P hfinite
  exact WeierstrassCurve.Affine.Point.some_ne_zero hP hzero

/-- The fibre discriminant at an affine target point is nonzero. -/
theorem targetCubicFibre_discriminant_ne_zero
    {X Y : ℚ}
    (hP : veluThreeCandidateTarget.toAffine.Nonsingular X Y) :
    targetCubicDiscriminant 1 (-X) 28 49 ≠ 0 := by
  rw [targetCubicFibre_discriminant_eq_square hP]
  exact pow_ne_zero 2 (mul_ne_zero (by norm_num)
    (veluThreeCandidateTarget_completedOrdinate_ne_zero hP))

/-- A root of the fibre is nonzero, since its constant term is `49`. -/
theorem targetCubicFibre_root_ne_zero
    {X t : ℚ} (hroot : targetCubicFibre X t = 0) : t ≠ 0 := by
  intro ht
  subst t
  norm_num [targetCubicFibre] at hroot

/-- A fibre root recovers the target abscissa through the first candidate
formula. -/
theorem veluThreeCandidateX_eq_of_targetCubicFibre_root
    {X t : ℚ} (hroot : targetCubicFibre X t = 0) :
    veluThreeCandidateX t = X := by
  have ht := targetCubicFibre_root_ne_zero hroot
  simp only [targetCubicFibre, veluThreeCandidateX] at hroot ⊢
  field_simp [ht]
  linear_combination hroot

/-- The formal derivative of the fibre, written as a rational function at
a root.  This identity exhibits directly why the inverse ordinate
denominator is the nonvanishing derivative factor. -/
theorem targetCubicFibre_derivative_at_root
    {X t : ℚ} (hroot : targetCubicFibre X t = 0) :
    3 * t ^ 2 - 2 * X * t + 28 =
      (t ^ 3 - 28 * t - 98) / t := by
  have ht := targetCubicFibre_root_ne_zero hroot
  simp only [targetCubicFibre] at hroot
  field_simp [ht]
  linear_combination 2 * hroot

/-- The completed-square polynomial transforms by the square of the
completed-ordinate multiplier of the first candidate. -/
theorem targetCompletedPolynomial_candidateX
    {t : ℚ} (ht : t ≠ 0) :
    4 * veluThreeCandidateX t ^ 3 +
          16 * veluThreeCandidateX t ^ 2 -
          504 * veluThreeCandidateX t - 3115 =
      (4 * t ^ 3 + 16 * t ^ 2 + 56 * t + 49) *
        ((t ^ 3 - 28 * t - 98) / t ^ 3) ^ 2 := by
  simp only [veluThreeCandidateX]
  field_simp [ht]
  ring

/-- The ordinate multiplier cannot vanish above an affine target point. -/
theorem targetCubicFibre_multiplier_ne_zero
    {X Y t : ℚ}
    (hP : veluThreeCandidateTarget.toAffine.Nonsingular X Y)
    (hroot : targetCubicFibre X t = 0) :
    t ^ 3 - 28 * t - 98 ≠ 0 := by
  intro hmult
  have ht := targetCubicFibre_root_ne_zero hroot
  have hX := veluThreeCandidateX_eq_of_targetCubicFibre_root hroot
  have htarget := veluThreeCandidateTarget_completedEquation hP
  have htransform := targetCompletedPolynomial_candidateX ht
  rw [hX] at htransform
  rw [← htarget] at htransform
  have hzero : (2 * Y + 4 * X + 7) ^ 2 = 0 := by
    rw [htransform, hmult]
    norm_num
  exact veluThreeCandidateTarget_completedOrdinate_ne_zero hP
    (sq_eq_zero_iff.mp hzero)

/-- The explicit source ordinate associated to a target point and one
rational fibre root. -/
def targetCubicPreimageY (Y t : ℚ) : ℚ :=
  (Y * t ^ 3 + 112 * t ^ 2 + 392 * t + 343) /
    (t ^ 3 - 28 * t - 98)

/-- The explicit inverse ordinate evaluates under the first candidate to
the prescribed target ordinate. -/
theorem veluThreeCandidateY_targetCubicPreimageY
    {X Y t : ℚ}
    (hP : veluThreeCandidateTarget.toAffine.Nonsingular X Y)
    (hroot : targetCubicFibre X t = 0) :
    veluThreeCandidateY t (targetCubicPreimageY Y t) = Y := by
  have ht := targetCubicFibre_root_ne_zero hroot
  have hmult := targetCubicFibre_multiplier_ne_zero hP hroot
  simp only [veluThreeCandidateY]
  rw [div_eq_iff (pow_ne_zero 3 ht)]
  rw [show
      t ^ 3 * targetCubicPreimageY Y t -
            28 * t * targetCubicPreimageY Y t -
            98 * targetCubicPreimageY Y t =
        (t ^ 3 - 28 * t - 98) * targetCubicPreimageY Y t by
      ring]
  simp only [targetCubicPreimageY]
  rw [mul_div_cancel₀ _ hmult]
  ring

/-- The residual of the target equation at the candidate coordinates is
the source residual times the square of the ordinate multiplier. -/
theorem veluThreeCandidate_equation_residual
    {t y : ℚ} (ht : t ≠ 0) :
    veluThreeCandidateY t y ^ 2 +
          4 * veluThreeCandidateX t * veluThreeCandidateY t y +
          7 * veluThreeCandidateY t y -
          (veluThreeCandidateX t ^ 3 -
            140 * veluThreeCandidateX t - 791) =
      ((t ^ 3 - 28 * t - 98) / t ^ 3) ^ 2 *
        (y ^ 2 + 4 * t * y + 7 * y - t ^ 3) := by
  simp only [veluThreeCandidateX, veluThreeCandidateY]
  field_simp [ht]
  ring

/-- The point reconstructed from a rational fibre root lies on the source
curve. -/
theorem targetCubicPreimage_nonsingular
    {X Y t : ℚ}
    (hP : veluThreeCandidateTarget.toAffine.Nonsingular X Y)
    (hroot : targetCubicFibre X t = 0) :
    threeTorsionCurve.toAffine.Nonsingular t
      (targetCubicPreimageY Y t) := by
  apply threeTorsionCurve.toAffine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  norm_num [threeTorsionCurve]
  have ht := targetCubicFibre_root_ne_zero hroot
  have hmult := targetCubicFibre_multiplier_ne_zero hP hroot
  have hX := veluThreeCandidateX_eq_of_targetCubicFibre_root hroot
  have hY := veluThreeCandidateY_targetCubicPreimageY hP hroot
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  norm_num [veluThreeCandidateTarget] at hcurve
  have hresidual := veluThreeCandidate_equation_residual
    (y := targetCubicPreimageY Y t) ht
  rw [hX, hY] at hresidual
  have hfactor :
      ((t ^ 3 - 28 * t - 98) / t ^ 3) ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (div_ne_zero hmult (pow_ne_zero 3 ht))
  apply sub_eq_zero.mp
  apply mul_left_cancel₀ hfactor
  rw [← hresidual]
  linear_combination hcurve

/-- A rational root of the cubic fibre gives an explicit source point
mapping to the prescribed affine target point. -/
theorem exists_veluThreeCandidate_preimage_of_targetCubicFibre_root
    {X Y t : ℚ}
    (hP : veluThreeCandidateTarget.toAffine.Nonsingular X Y)
    (hroot : targetCubicFibre X t = 0) :
    ∃ Q : threeTorsionCurve.toAffine.Point,
      veluThreeCandidatePointFun Q =
        WeierstrassCurve.Affine.Point.some X Y hP := by
  have ht := targetCubicFibre_root_ne_zero hroot
  let hsource := targetCubicPreimage_nonsingular hP hroot
  refine ⟨WeierstrassCurve.Affine.Point.some t
    (targetCubicPreimageY Y t) hsource, ?_⟩
  simp only [veluThreeCandidatePointFun, ht]
  apply WeierstrassCurve.Affine.Point.some_eq_some
    veluThreeCandidateTarget
  · exact veluThreeCandidateX_eq_of_targetCubicFibre_root hroot
  · exact veluThreeCandidateY_targetCubicPreimageY hP hroot

/-- The exact rational-root input remaining in the target descent. -/
def TargetCubicFibreRoots : Prop :=
  ∀ {X Y : ℚ},
    veluThreeCandidateTarget.toAffine.Nonsingular X Y →
      ∃ t : ℚ, targetCubicFibre X t = 0

/-- Solving every affine cubic fibre proves surjectivity of the fixed point
function, including the point at infinity. -/
theorem targetThreeCandidateSurjective_of_cubicFibreRoots
    (hroots : TargetCubicFibreRoots) :
    TargetThreeCandidateSurjective := by
  intro P
  cases P with
  | zero =>
      exact ⟨0, veluThreeCandidatePointFun_zero⟩
  | some X Y hP =>
      obtain ⟨t, ht⟩ := hroots hP
      exact exists_veluThreeCandidate_preimage_of_targetCubicFibre_root
        hP ht

/-- Conversely, any candidate preimage exposes a rational root of the
cubic fibre. -/
theorem exists_targetCubicFibre_root_of_candidate_preimage
    {X Y : ℚ}
    (hP : veluThreeCandidateTarget.toAffine.Nonsingular X Y)
    (hpreimage : ∃ Q : threeTorsionCurve.toAffine.Point,
      veluThreeCandidatePointFun Q =
        WeierstrassCurve.Affine.Point.some X Y hP) :
    ∃ t : ℚ, targetCubicFibre X t = 0 := by
  obtain ⟨Q, hQ⟩ := hpreimage
  cases Q with
  | zero =>
      simp only [veluThreeCandidatePointFun] at hQ
      exact (WeierstrassCurve.Affine.Point.some_ne_zero hP hQ.symm).elim
  | some t y htPoint =>
      by_cases ht : t = 0
      · simp only [veluThreeCandidatePointFun, ht] at hQ
        exact (WeierstrassCurve.Affine.Point.some_ne_zero hP hQ.symm).elim
      · have hX : veluThreeCandidateX t = X := by
          simp only [veluThreeCandidatePointFun, ht] at hQ
          exact (WeierstrassCurve.Affine.Point.some.inj hQ).1
        refine ⟨t, ?_⟩
        simp only [targetCubicFibre, veluThreeCandidateX] at hX ⊢
        field_simp [ht] at hX
        linear_combination hX

/-- The cubic rational-root condition is exactly the target-surjectivity
condition already consumed by the order-35 rank boundary. -/
theorem targetCubicFibreRoots_iff_targetThreeCandidateSurjective :
    TargetCubicFibreRoots ↔ TargetThreeCandidateSurjective := by
  constructor
  · exact targetThreeCandidateSurjective_of_cubicFibreRoots
  · intro hsurj X Y hP
    exact exists_targetCubicFibre_root_of_candidate_preimage hP
      (hsurj (WeierstrassCurve.Affine.Point.some X Y hP))

/-! ## The nontrivial Eisenstein-unit cover

Putting the candidate target in Cohen--Pazuki form gives

`v² = u³ - 3(12u+1500)²`.

For either nontrivial unit cube-class in `ℤ[ζ₃]`, their homogeneous
three-descent cubic is, up to conjugating `Y`, the form below.  Modulo seven
it has only the zero solution, hence an integral solution would be divisible
by arbitrarily high powers of seven.  The minimal-size argument below
packages that infinite descent without any unproved unique-factorization
step.
-/

/-- The abscissa change from the checked candidate target to the integral
dual three-descent model. -/
def targetThreeDescentU (X : ℚ) : ℚ :=
  36 * X + 192

/-- The ordinate change to the integral dual three-descent model. -/
def targetThreeDescentV (X Y : ℚ) : ℚ :=
  108 * (2 * Y + 4 * X + 7)

/-- The candidate target is explicitly the dual three-descent model
`v² = u³ - 3(12u+1500)²`, with parameters
`D=-3`, `a=12`, and `b=1500`. -/
theorem targetThreeDescent_equation
    {X Y : ℚ}
    (hP : veluThreeCandidateTarget.toAffine.Nonsingular X Y) :
    targetThreeDescentV X Y ^ 2 =
      targetThreeDescentU X ^ 3 -
        3 * (12 * targetThreeDescentU X + 1500) ^ 2 := by
  simp only [targetThreeDescentV, targetThreeDescentU]
  linear_combination
    11664 * veluThreeCandidateTarget_completedEquation hP

/-- The fixed homogeneous cubic for a nontrivial Eisenstein-unit class in
the target three-descent. -/
def targetEisensteinUnitCover (X Y Z : ℤ) : ℤ :=
  X ^ 3 - 3 * Y ^ 3 + 3000 * Z ^ 3 + 3 * X ^ 2 * Y -
    9 * X * Y ^ 2 + 24 * X ^ 2 * Z + 72 * Y ^ 2 * Z

/-- The unit-cover cubic is homogeneous of degree three. -/
theorem targetEisensteinUnitCover_scale (r X Y Z : ℤ) :
    targetEisensteinUnitCover (r * X) (r * Y) (r * Z) =
      r ^ 3 * targetEisensteinUnitCover X Y Z := by
  simp only [targetEisensteinUnitCover]
  ring

private theorem targetEisensteinUnitCover_modSeven_only_zero :
    ∀ X Y Z : ZMod 7,
      X ^ 3 - 3 * Y ^ 3 + 3000 * Z ^ 3 + 3 * X ^ 2 * Y -
          9 * X * Y ^ 2 + 24 * X ^ 2 * Z + 72 * Y ^ 2 * Z = 0 →
        X = 0 ∧ Y = 0 ∧ Z = 0 := by
  decide

/-- Every integral zero of the nontrivial-unit cover is coordinatewise
divisible by seven. -/
theorem seven_dvd_targetEisensteinUnitCover_zero
    {X Y Z : ℤ}
    (hcover : targetEisensteinUnitCover X Y Z = 0) :
    (7 : ℤ) ∣ X ∧ (7 : ℤ) ∣ Y ∧ (7 : ℤ) ∣ Z := by
  have hcast := congrArg (fun n : ℤ ↦ (n : ZMod 7)) hcover
  have hmod :
      (X : ZMod 7) ^ 3 - 3 * (Y : ZMod 7) ^ 3 +
            3000 * (Z : ZMod 7) ^ 3 +
            3 * (X : ZMod 7) ^ 2 * (Y : ZMod 7) -
          9 * (X : ZMod 7) * (Y : ZMod 7) ^ 2 +
        24 * (X : ZMod 7) ^ 2 * (Z : ZMod 7) +
      72 * (Y : ZMod 7) ^ 2 * (Z : ZMod 7) = 0 := by
    simpa [targetEisensteinUnitCover] using hcast
  obtain ⟨hX, hY, hZ⟩ :=
    targetEisensteinUnitCover_modSeven_only_zero
      (X : ZMod 7) (Y : ZMod 7) (Z : ZMod 7) hmod
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd X 7).mp hX,
    (ZMod.intCast_zmod_eq_zero_iff_dvd Y 7).mp hY,
    (ZMod.intCast_zmod_eq_zero_iff_dvd Z 7).mp hZ⟩

/-- The nontrivial Eisenstein-unit cover has no nonzero integral point. -/
theorem targetEisensteinUnitCover_no_nonzero_integer_solution
    (X Y Z : ℤ)
    (hcover : targetEisensteinUnitCover X Y Z = 0) :
    X = 0 ∧ Y = 0 ∧ Z = 0 := by
  classical
  by_contra hnonzero
  let sizes : Set ℕ :=
    {n | ∃ x y z : ℤ,
      targetEisensteinUnitCover x y z = 0 ∧
        ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
        x.natAbs + y.natAbs + z.natAbs = n}
  have hsizes : sizes.Nonempty := by
    refine ⟨X.natAbs + Y.natAbs + Z.natAbs, X, Y, Z,
      hcover, hnonzero, rfl⟩
  let n : ℕ := Nat.find hsizes
  obtain ⟨x, y, z, hxyz, hxyz0, hsize⟩ := Nat.find_spec hsizes
  obtain ⟨⟨x', hx⟩, ⟨y', hy⟩, ⟨z', hz⟩⟩ :=
    seven_dvd_targetEisensteinUnitCover_zero hxyz
  have hscaled : targetEisensteinUnitCover x' y' z' = 0 := by
    have hhom := targetEisensteinUnitCover_scale (7 : ℤ) x' y' z'
    rw [← hx, ← hy, ← hz, hxyz] at hhom
    norm_num at hhom
    exact hhom
  have hscaled0 : ¬(x' = 0 ∧ y' = 0 ∧ z' = 0) := by
    rintro ⟨rfl, rfl, rfl⟩
    have hx0 : x = 0 := by simpa using hx
    have hy0 : y = 0 := by simpa using hy
    have hz0 : z = 0 := by simpa using hz
    exact hxyz0 ⟨hx0, hy0, hz0⟩
  have hnew : x'.natAbs + y'.natAbs + z'.natAbs ∈ sizes :=
    ⟨x', y', z', hscaled, hscaled0, rfl⟩
  have hpositive : 0 < x'.natAbs + y'.natAbs + z'.natAbs := by
    omega
  have hfactor :
      x.natAbs + y.natAbs + z.natAbs =
        7 * (x'.natAbs + y'.natAbs + z'.natAbs) := by
    rw [hx, hy, hz]
    simp only [Int.natAbs_mul]
    norm_num
    omega
  have hless : x'.natAbs + y'.natAbs + z'.natAbs < n := by
    change x'.natAbs + y'.natAbs + z'.natAbs < Nat.find hsizes
    rw [← hsize, hfactor]
    omega
  exact (Nat.not_lt_of_ge (Nat.find_min' hsizes hnew)) hless

/-- The homogeneous cubic for the conjugate nontrivial unit class. -/
def targetEisensteinConjugateUnitCover (X Y Z : ℤ) : ℤ :=
  -X ^ 3 - 3 * Y ^ 3 + 3000 * Z ^ 3 + 3 * X ^ 2 * Y +
    9 * X * Y ^ 2 + 24 * X ^ 2 * Z + 72 * Y ^ 2 * Z

/-- Conjugating the Eisenstein unit class changes the second and third
homogeneous coordinates by sign. -/
theorem targetEisensteinConjugateUnitCover_eq
    (X Y Z : ℤ) :
    targetEisensteinConjugateUnitCover X Y Z =
      -targetEisensteinUnitCover X (-Y) (-Z) := by
  simp only [targetEisensteinConjugateUnitCover,
    targetEisensteinUnitCover]
  ring

/-- The conjugate nontrivial unit cover also has no nonzero integral
point. -/
theorem targetEisensteinConjugateUnitCover_no_nonzero_integer_solution
    (X Y Z : ℤ)
    (hcover : targetEisensteinConjugateUnitCover X Y Z = 0) :
    X = 0 ∧ Y = 0 ∧ Z = 0 := by
  have hunit : targetEisensteinUnitCover X (-Y) (-Z) = 0 := by
    rw [targetEisensteinConjugateUnitCover_eq] at hcover
    linarith
  obtain ⟨hX, hY, hZ⟩ :=
    targetEisensteinUnitCover_no_nonzero_integer_solution
      X (-Y) (-Z) hunit
  exact ⟨hX, neg_eq_zero.mp hY, neg_eq_zero.mp hZ⟩

/-- The exact global-algebra output still required from the dual
three-descent.  It says that a target point either has a rational fibre
root (the trivial Eisenstein unit class), or supplies a nonzero integral
point on one of the two nontrivial unit covers.  The class-number-one and
prime-support argument over `ℤ[ζ₃]` is precisely the missing proof of this
proposition; the two local-obstruction branches are checked above. -/
def TargetEisensteinDescentReduction : Prop :=
  ∀ {X Y : ℚ},
    veluThreeCandidateTarget.toAffine.Nonsingular X Y →
      (∃ t : ℚ, targetCubicFibre X t = 0) ∨
      (∃ A B C : ℤ,
        targetEisensteinUnitCover A B C = 0 ∧
          ¬(A = 0 ∧ B = 0 ∧ C = 0)) ∨
      ∃ A B C : ℤ,
        targetEisensteinConjugateUnitCover A B C = 0 ∧
          ¬(A = 0 ∧ B = 0 ∧ C = 0)

/-- Once the global Eisenstein descent has reduced the target points to
the three unit classes, the two mod-seven infinite descents force every
target fibre to have a rational root. -/
theorem targetCubicFibreRoots_of_eisensteinDescentReduction
    (hdescent : TargetEisensteinDescentReduction) :
    TargetCubicFibreRoots := by
  intro X Y hP
  rcases hdescent hP with hroot | hunit | hconjugate
  · exact hroot
  · obtain ⟨A, B, C, hcover, hnonzero⟩ := hunit
    exact (hnonzero
      (targetEisensteinUnitCover_no_nonzero_integer_solution
        A B C hcover)).elim
  · obtain ⟨A, B, C, hcover, hnonzero⟩ := hconjugate
    exact (hnonzero
      (targetEisensteinConjugateUnitCover_no_nonzero_integer_solution
        A B C hcover)).elim

/-- The exact global Eisenstein reduction has a checked end-to-end
rank-zero consumer. -/
theorem optimalQuotientModel_rank_zero_of_eisensteinDescentReduction
    (hdescent : TargetEisensteinDescentReduction) :
    Module.finrank ℤ optimalQuotientModel.toAffine.Point = 0 :=
  optimalQuotientModel_rank_zero_of_targetCandidateSurjective
    (targetThreeCandidateSurjective_of_cubicFibreRoots
      (targetCubicFibreRoots_of_eisensteinDescentReduction hdescent))

/-- The cubic-fibre input has a checked end-to-end rank-zero consumer. -/
theorem optimalQuotientModel_rank_zero_of_targetCubicFibreRoots
    (hroots : TargetCubicFibreRoots) :
    Module.finrank ℤ optimalQuotientModel.toAffine.Point = 0 :=
  optimalQuotientModel_rank_zero_of_targetCandidateSurjective
    (targetThreeCandidateSurjective_of_cubicFibreRoots hroots)

/-- The cubic-fibre input has a checked end-to-end finiteness consumer. -/
theorem optimalQuotientModel_finite_of_targetCubicFibreRoots
    (hroots : TargetCubicFibreRoots) :
    Finite optimalQuotientModel.toAffine.Point :=
  optimalQuotientModel_finite_of_targetCandidateSurjective
    (targetThreeCandidateSurjective_of_cubicFibreRoots hroots)

end MazurTorsion.OrderThirtyFive
