/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Arithmetic.ExceptionalProducts
import MazurTorsion.EllipticCurve.TwoIsogenyMultiples
import MazurTorsion.EllipticCurve.TwoTorsionNormalization

/-!
# Excluding rational points of orders twenty and twenty-four

For a point `Q` of exact order `2n`, its midpoint `nQ` has exact order
two.  Normalize that midpoint to `(0,0)` on

`y² = x(x² + ax + b)`.

The explicit two-isogeny then constructs on the target curve a point of
exact order `n` whose cyclic subgroup does not contain the visible target
two-torsion point.  These two independent generators embed
`ZMod 2 × ZMod n`.  The unconditional exceptional-product obstructions
rule this out for `n = 10` and `n = 12`.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

open TwoIsogeny
open TwoTorsionNormalization

private lemma targetOrigin_addOrderOf
    (a b : ℚ) [(sourceCurve a b).IsElliptic] :
    addOrderOf (targetOrigin a b) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  apply addOrderOf_eq_prime
  · simpa only [two_nsmul] using targetOrigin_add_self a b
  · exact targetOrigin_ne_zero a b

/-- No elliptic curve over `ℚ` has a rational point of exact order
twenty. -/
theorem no_rational_point_of_order_twenty
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : E.toAffine.Point) :
    addOrderOf Q ≠ 20 := by
  intro hQ
  let T : E.toAffine.Point := (10 : ℕ) • Q
  have hTorder : addOrderOf T = 2 := by
    dsimp only [T]
    rw [addOrderOf_nsmul' Q (by norm_num), hQ]
    norm_num
  obtain ⟨D⟩ :=
    TwoTorsionNormalization.exists_data_of_order_two E T hTorder
  letI := D.source_isElliptic
  let Q₀ := D.sourcePullback Q
  have hQ₀order : addOrderOf Q₀ = 20 := by
    dsimp only [Q₀]
    rw [D.addOrderOf_sourcePullback, hQ]
  have hmid :
      (10 : ℕ) • Q₀ = sourceOrigin D.a D.b := by
    dsimp only [Q₀]
    apply D.nsmul_sourcePullback_eq_sourceOrigin
    rfl
  obtain ⟨C, hCorder, hindependent⟩ :=
    exists_order_ten_image_independent Q₀ hQ₀order hmid
  obtain ⟨f, hf⟩ :=
    IndependentCyclicGenerators.exists_embedding
      (targetOrigin D.a D.b) C
      (targetOrigin_addOrderOf D.a D.b) 10 hCorder
      hindependent
  exact
    (forbidsEmbedding_zmod_two_prod_ten
      (targetCurve D.a D.b)) f hf

/-- No elliptic curve over `ℚ` has a rational point of exact order
twenty-four. -/
theorem no_rational_point_of_order_twenty_four
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : E.toAffine.Point) :
    addOrderOf Q ≠ 24 := by
  intro hQ
  let T : E.toAffine.Point := (12 : ℕ) • Q
  have hTorder : addOrderOf T = 2 := by
    dsimp only [T]
    rw [addOrderOf_nsmul' Q (by norm_num), hQ]
    norm_num
  obtain ⟨D⟩ :=
    TwoTorsionNormalization.exists_data_of_order_two E T hTorder
  letI := D.source_isElliptic
  let Q₀ := D.sourcePullback Q
  have hQ₀order : addOrderOf Q₀ = 24 := by
    dsimp only [Q₀]
    rw [D.addOrderOf_sourcePullback, hQ]
  have hmid :
      (12 : ℕ) • Q₀ = sourceOrigin D.a D.b := by
    dsimp only [Q₀]
    apply D.nsmul_sourcePullback_eq_sourceOrigin
    rfl
  obtain ⟨C, hCorder, hindependent⟩ :=
    exists_order_twelve_image_independent Q₀ hQ₀order hmid
  obtain ⟨f, hf⟩ :=
    IndependentCyclicGenerators.exists_embedding
      (targetOrigin D.a D.b) C
      (targetOrigin_addOrderOf D.a D.b) 12 hCorder
      hindependent
  exact
    (forbidsEmbedding_zmod_two_prod_twelve
      (targetCurve D.a D.b)) f hf

/-- The order-twenty obstruction on the canonical rational base change
used by `RationalTorsion`. -/
theorem rationalPoint_addOrderOf_ne_twenty
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) :
    addOrderOf Q ≠ 20 := by
  haveI : (E⁄ℚ).IsElliptic :=
    inferInstanceAs (E.map (algebraMap ℚ ℚ)).IsElliptic
  exact no_rational_point_of_order_twenty (E⁄ℚ) Q

/-- The order-twenty-four obstruction on the canonical rational base
change used by `RationalTorsion`. -/
theorem rationalPoint_addOrderOf_ne_twenty_four
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) :
    addOrderOf Q ≠ 24 := by
  haveI : (E⁄ℚ).IsElliptic :=
    inferInstanceAs (E.map (algebraMap ℚ ℚ)).IsElliptic
  exact no_rational_point_of_order_twenty_four (E⁄ℚ) Q

end MazurTorsion.Kubert
