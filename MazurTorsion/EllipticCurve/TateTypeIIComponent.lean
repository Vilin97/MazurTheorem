/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.EllipticCurve.NonsingularReductionAdditive
import MazurTorsion.EllipticCurve.TateFirstBlowup

/-!
# The identity component in the first tame Tate branch

For an integral short Weierstrass equation whose special fibre is the standard cusp, the first
case split in Tate's algorithm is whether `a₆` lies in the square of the maximal ideal.  If it
does not, the equation has Kodaira type II.  This file proves the exact pointwise consequence
needed by the torsion argument without naming a Kodaira symbol or constructing a Néron model:
every local point has nonsingular coordinate reduction, so the canonical nonsingular-reduction
subgroup is the whole point group.

The affine calculation is supplied by `TateFirstBlowup`.  Points in the formal kernel satisfy the
canonical reduction predicate by definition; every other point has integral coordinates, and the
order-one affine calculation shows that its specialization avoids the cusp.
-/

noncomputable section

open IsLocalRing

namespace MazurTorsion.EllipticCurve

open WeierstrassCurve WeierstrassCurve.Affine
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

universe u v

/-- In the order-one branch of the normalized tame equation, every local point belongs to the
canonical nonsingular-reduction domain. -/
theorem hasNonsingularReduction_of_firstBlowup_residue_b₆_ne_zero
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    [CharZero K]
    {v : HeightOneSpectrum R}
    {W : WeierstrassCurve.Affine (v.adicCompletion K)}
    {W₀ : WeierstrassCurve (v.adicCompletionIntegers K)}
    (hW : W₀.map
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) = W)
    [W.IsElliptic] [DecidableEq (v.adicCompletion K)]
    [W₀.IsShortNF]
    (B : FirstBlowupEquationCharts W₀)
    (h2 : (2 : ResidueField (v.adicCompletionIntegers K)) ≠ 0)
    (h3 : (3 : ResidueField (v.adicCompletionIntegers K)) ≠ 0)
    (hspecial : W₀.map (residue (v.adicCompletionIntegers K)) =
      cuspidalShortCurve (ResidueField (v.adicCompletionIntegers K)))
    (hb₆ : residue (v.adicCompletionIntegers K) B.coefficients.b₆ ≠ 0)
    (P : W.Point) : HasNonsingularReduction hW P := by
  rcases P with _ | ⟨x, y, h⟩
  · exact hasNonsingularReduction_zero hW
  · intro hx
    have hxy := integral_of_not_mem hW h.left hx
    exact B.nonsingular_reduction_of_equation_of_residue_b₆_ne_zero
      h2 h3 hspecial (equation_integral hW h.left hxy.1 hxy.2) hb₆

/-- In the order-one branch, canonical nonsingular reduction is defined on the entire local point
group.  This is the precise identity-component statement consumed by the marked torsion
argument. -/
theorem nonsingularReductionSubgroup_eq_top_of_firstBlowup_residue_b₆_ne_zero
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    [CharZero K]
    {v : HeightOneSpectrum R}
    {W : WeierstrassCurve.Affine (v.adicCompletion K)}
    {W₀ : WeierstrassCurve (v.adicCompletionIntegers K)}
    (hW : W₀.map
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) = W)
    [W.IsElliptic] [DecidableEq (v.adicCompletion K)]
    [W₀.IsShortNF]
    (B : FirstBlowupEquationCharts W₀)
    (h2 : (2 : ResidueField (v.adicCompletionIntegers K)) ≠ 0)
    (h3 : (3 : ResidueField (v.adicCompletionIntegers K)) ≠ 0)
    (hspecial : W₀.map (residue (v.adicCompletionIntegers K)) =
      cuspidalShortCurve (ResidueField (v.adicCompletionIntegers K)))
    (hb₆ : residue (v.adicCompletionIntegers K) B.coefficients.b₆ ≠ 0) :
    nonsingularReductionSubgroup hW (nonsingularReduction_isAdditive hW) = ⊤ := by
  ext P
  constructor
  · simp
  · intro _
    exact hasNonsingularReduction_of_firstBlowup_residue_b₆_ne_zero
      hW B h2 h3 hspecial hb₆ P

/-- Every multiplier of a local point, in particular the uniform tame exponent twelve, lies in
the canonical identity subgroup in the order-one branch. -/
theorem twelve_nsmul_mem_nonsingularReductionSubgroup_of_firstBlowup_residue_b₆_ne_zero
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    [CharZero K]
    {v : HeightOneSpectrum R}
    {W : WeierstrassCurve.Affine (v.adicCompletion K)}
    {W₀ : WeierstrassCurve (v.adicCompletionIntegers K)}
    (hW : W₀.map
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) = W)
    [W.IsElliptic] [DecidableEq (v.adicCompletion K)]
    [W₀.IsShortNF]
    (B : FirstBlowupEquationCharts W₀)
    (h2 : (2 : ResidueField (v.adicCompletionIntegers K)) ≠ 0)
    (h3 : (3 : ResidueField (v.adicCompletionIntegers K)) ≠ 0)
    (hspecial : W₀.map (residue (v.adicCompletionIntegers K)) =
      cuspidalShortCurve (ResidueField (v.adicCompletionIntegers K)))
    (hb₆ : residue (v.adicCompletionIntegers K) B.coefficients.b₆ ≠ 0)
    (P : W.Point) :
    12 • P ∈ nonsingularReductionSubgroup hW
      (nonsingularReduction_isAdditive hW) := by
  rw [nonsingularReductionSubgroup_eq_top_of_firstBlowup_residue_b₆_ne_zero
    hW B h2 h3 hspecial hb₆]
  simp

end MazurTorsion.EllipticCurve
