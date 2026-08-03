/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.EllipticCurve.IntegerPrimeSpecialization

/-!
# Exact-order consumers for reduction at five and eleven

This file applies the integer-prime formal-kernel certificate to the actual global reduction map
at a prime of good reduction.  It supplies the exact-order statements needed after the Mazur
local argument has established good reduction, together with cardinality-divisibility consumers.

The suffix `of_goodReduction` is intentional.  Before good reduction has been proved, the
marked point specializes to a Neron special fibre rather than to the group of points of the
possibly singular Weierstrass reduction.  Constructing that special-fibre map and its component
quotient remains a separate geometric boundary; this module does not hide it behind an assumed
map.
-/

open WeierstrassCurve

namespace MazurTorsion.PrimeOrder

open WeierstrassCurve.Affine
open MazurTorsion.IntegerPrimeSpecialization

/-- The coefficientwise reduction of an integral Weierstrass equation over `ZMod 5`. -/
abbrev reductionCurveAtFive (W₀ : WeierstrassCurve ℤ) : Affine (ZMod 5) :=
  ((W₀.toAffine ⁄ (ZMod 5)) : WeierstrassCurve _).toAffine

/-- The coefficientwise reduction of an integral Weierstrass equation over `ZMod 11`. -/
abbrev reductionCurveAtEleven (W₀ : WeierstrassCurve ℤ) : Affine (ZMod 11) :=
  ((W₀.toAffine ⁄ (ZMod 11)) : WeierstrassCurve _).toAffine

/-- Identifying the residue field at five with `ZMod 5` carries the abstract
reduced equation to the concrete coefficientwise reduction. -/
theorem reductionCurveAtFive_eq_map (W₀ : WeierstrassCurve ℤ) :
    reductionCurveAtFive W₀ =
      (redCurve atFive W₀).map residueFiveAlgEquiv.toRingEquiv := by
  have hcomm (a : ℤ) :
      algebraMap ℤ (ZMod 5) a =
        residueFiveAlgEquiv (algebraMap ℤ _ a) :=
    (residueFiveAlgEquiv.commutes a).symm
  ext <;> exact hcomm _

/-- Identifying the residue field at eleven with `ZMod 11` carries the
abstract reduced equation to the concrete coefficientwise reduction. -/
theorem reductionCurveAtEleven_eq_map (W₀ : WeierstrassCurve ℤ) :
    reductionCurveAtEleven W₀ =
      (redCurve atEleven W₀).map residueElevenAlgEquiv.toRingEquiv := by
  have hcomm (a : ℤ) :
      algebraMap ℤ (ZMod 11) a =
        residueElevenAlgEquiv (algebraMap ℤ _ a) :=
    (residueElevenAlgEquiv.commutes a).symm
  ext <;> exact hcomm _

/-- Good reduction at the abstract residue field transfers to the concrete
`ZMod 5` equation. -/
theorem reductionCurveAtFive_isElliptic
    (W₀ : WeierstrassCurve ℤ) [(redCurve atFive W₀).IsElliptic] :
    (reductionCurveAtFive W₀).IsElliptic := by
  rw [reductionCurveAtFive_eq_map]
  infer_instance

/-- Good reduction at the abstract residue field transfers to the concrete
`ZMod 11` equation. -/
theorem reductionCurveAtEleven_isElliptic
    (W₀ : WeierstrassCurve ℤ) [(redCurve atEleven W₀).IsElliptic] :
    (reductionCurveAtEleven W₀).IsElliptic := by
  rw [reductionCurveAtEleven_eq_map]
  infer_instance

/-- Reduction at five followed by the canonical identification of the residue field with
`ZMod 5`. -/
noncomputable def reductionAtFiveToZMod
    {E : Affine ℚ} {W₀ : WeierstrassCurve ℤ}
    (hE : W₀.map (algebraMap ℤ ℚ) = E)
    [E.IsElliptic] [(redCurve atFive W₀).IsElliptic] :
    E.Point →+ (reductionCurveAtFive W₀).Point :=
  (Point.mapEquiv (W' := W₀.toAffine) residueFiveAlgEquiv).toAddMonoidHom.comp
    (redHom atFive hE)

/-- Reduction at eleven followed by the canonical identification of the residue field with
`ZMod 11`. -/
noncomputable def reductionAtElevenToZMod
    {E : Affine ℚ} {W₀ : WeierstrassCurve ℤ}
    (hE : W₀.map (algebraMap ℤ ℚ) = E)
    [E.IsElliptic] [(redCurve atEleven W₀).IsElliptic] :
    E.Point →+ (reductionCurveAtEleven W₀).Point :=
  (Point.mapEquiv (W' := W₀.toAffine) residueElevenAlgEquiv).toAddMonoidHom.comp
    (redHom atEleven hE)

/-- At good reduction over five, specialization preserves the exact additive order of every
torsion point. -/
theorem specializedPoint_addOrderOf_eq_atFive_of_goodReduction
    {E : Affine ℚ} {W₀ : WeierstrassCurve ℤ}
    (hE : W₀.map (algebraMap ℤ ℚ) = E)
    [E.IsElliptic] [(redCurve atFive W₀).IsElliptic]
    {P : E.Point} (hP : IsOfFinAddOrder P) :
    addOrderOf (red atFive hE P) = addOrderOf P := by
  exact addOrderOf_red atFive hE (by norm_num) five_mem_atFive
    five_not_mem_atFive_pow_four hP

/-- At good reduction over eleven, specialization preserves the exact additive order of every
torsion point. -/
theorem specializedPoint_addOrderOf_eq_atEleven_of_goodReduction
    {E : Affine ℚ} {W₀ : WeierstrassCurve ℤ}
    (hE : W₀.map (algebraMap ℤ ℚ) = E)
    [E.IsElliptic] [(redCurve atEleven W₀).IsElliptic]
    {P : E.Point} (hP : IsOfFinAddOrder P) :
    addOrderOf (red atEleven hE P) = addOrderOf P := by
  exact addOrderOf_red atEleven hE (by norm_num) eleven_mem_atEleven
    eleven_not_mem_atEleven_pow_ten hP

/-- Concrete `ZMod 5` specialization preserves exact additive order at good reduction. -/
theorem specializedPointZMod_addOrderOf_eq_atFive_of_goodReduction
    {E : Affine ℚ} {W₀ : WeierstrassCurve ℤ}
    (hE : W₀.map (algebraMap ℤ ℚ) = E)
    [E.IsElliptic] [(redCurve atFive W₀).IsElliptic]
    {P : E.Point} (hP : IsOfFinAddOrder P) :
    addOrderOf (reductionAtFiveToZMod hE P) = addOrderOf P := by
  rw [reductionAtFiveToZMod, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom, AddEquiv.addOrderOf_eq]
  exact specializedPoint_addOrderOf_eq_atFive_of_goodReduction hE hP

/-- Concrete `ZMod 11` specialization preserves exact additive order at good reduction. -/
theorem specializedPointZMod_addOrderOf_eq_atEleven_of_goodReduction
    {E : Affine ℚ} {W₀ : WeierstrassCurve ℤ}
    (hE : W₀.map (algebraMap ℤ ℚ) = E)
    [E.IsElliptic] [(redCurve atEleven W₀).IsElliptic]
    {P : E.Point} (hP : IsOfFinAddOrder P) :
    addOrderOf (reductionAtElevenToZMod hE P) = addOrderOf P := by
  rw [reductionAtElevenToZMod, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom, AddEquiv.addOrderOf_eq]
  exact specializedPoint_addOrderOf_eq_atEleven_of_goodReduction hE hP

/-- A point of exact order `N` at good reduction over five forces `N` to divide the cardinality
of the reduced point group.  This is a downstream consumer of exact-order preservation, not just
a restatement of the reduction map. -/
theorem exactOrder_dvd_reduction_card_atFive_of_goodReduction
    {E : Affine ℚ} {W₀ : WeierstrassCurve ℤ}
    (hE : W₀.map (algebraMap ℤ ℚ) = E)
    [E.IsElliptic] [(redCurve atFive W₀).IsElliptic]
    {P : E.Point} (hP : IsOfFinAddOrder P) {N : ℕ}
    (horder : addOrderOf P = N) :
    N ∣ Nat.card (reductionCurveAtFive W₀).Point := by
  rw [← horder, ← specializedPointZMod_addOrderOf_eq_atFive_of_goodReduction hE hP]
  exact addOrderOf_dvd_natCard _

/-- A point of exact order `N` at good reduction over eleven forces `N` to divide the
cardinality of the reduced point group. -/
theorem exactOrder_dvd_reduction_card_atEleven_of_goodReduction
    {E : Affine ℚ} {W₀ : WeierstrassCurve ℤ}
    (hE : W₀.map (algebraMap ℤ ℚ) = E)
    [E.IsElliptic] [(redCurve atEleven W₀).IsElliptic]
    {P : E.Point} (hP : IsOfFinAddOrder P) {N : ℕ}
    (horder : addOrderOf P = N) :
    N ∣ Nat.card (reductionCurveAtEleven W₀).Point := by
  rw [← horder, ← specializedPointZMod_addOrderOf_eq_atEleven_of_goodReduction hE hP]
  exact addOrderOf_dvd_natCard _

/-- A finite reduction at five cannot receive a torsion point whose exact order is larger than
the reduced point group. -/
theorem addOrderOf_ne_of_reduction_card_lt_atFive_of_goodReduction
    {E : Affine ℚ} {W₀ : WeierstrassCurve ℤ}
    (hE : W₀.map (algebraMap ℤ ℚ) = E)
    [E.IsElliptic] [(redCurve atFive W₀).IsElliptic]
    [Finite (reductionCurveAtFive W₀).Point]
    {P : E.Point} (hP : IsOfFinAddOrder P) {N : ℕ}
    (hcard : Nat.card (reductionCurveAtFive W₀).Point < N) :
    addOrderOf P ≠ N := by
  intro horder
  have hdvd := exactOrder_dvd_reduction_card_atFive_of_goodReduction hE hP horder
  have hle : N ≤ Nat.card (reductionCurveAtFive W₀).Point :=
    Nat.le_of_dvd Nat.card_pos hdvd
  omega

/-- A finite reduction at eleven cannot receive a torsion point whose exact order is larger than
the reduced point group. -/
theorem addOrderOf_ne_of_reduction_card_lt_atEleven_of_goodReduction
    {E : Affine ℚ} {W₀ : WeierstrassCurve ℤ}
    (hE : W₀.map (algebraMap ℤ ℚ) = E)
    [E.IsElliptic] [(redCurve atEleven W₀).IsElliptic]
    [Finite (reductionCurveAtEleven W₀).Point]
    {P : E.Point} (hP : IsOfFinAddOrder P) {N : ℕ}
    (hcard : Nat.card (reductionCurveAtEleven W₀).Point < N) :
    addOrderOf P ≠ N := by
  intro horder
  have hdvd := exactOrder_dvd_reduction_card_atEleven_of_goodReduction hE hP horder
  have hle : N ≤ Nat.card (reductionCurveAtEleven W₀).Point :=
    Nat.le_of_dvd Nat.card_pos hdvd
  omega

end MazurTorsion.PrimeOrder
