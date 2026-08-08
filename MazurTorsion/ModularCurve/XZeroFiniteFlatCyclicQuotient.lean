/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroCyclicQuotient
import MazurTorsion.ModularCurve.XZeroFiniteFlatModuli

/-!
# Rational points of the finite-flat cyclic quotient

The split `Gamma_0(N)` construction attaches an actual closed finite-flat
subgroup scheme to a `RationalDatum`.  This file compares its rational-point
quotient with the abstract coordinate-point quotient used by the existing
cyclic-quotient API.

For a supplied `WeierstrassGroupSchemeInterface`, the comparison proceeds in
three checked steps:

* all rational points of the constant subgroup carrier are distinguished
  sections indexed by the original cyclic group;
* the image of those sections under the actual closed subgroup immersion is
  exactly the image of the original rational cyclic subgroup;
* quotienting the represented rational point group by that image transports
  both the quotient projection and the descended multiplication-by-`N` map.

Thus the point-group quotient is compatible with the already represented
source group scheme and its genuine finite-flat subgroup.  No scheme
representing the quotient, elliptic-curve structure on such a scheme, or
base-change theorem for the quotient is asserted here.
-/

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli

universe u

open XZeroModuli

variable {K : Type u} [Field K] [DecidableEq K]
  {N : ℕ} [NeZero N]
  {W : WeierstrassCurve K} [W.IsElliptic]

namespace WeierstrassGroupSchemeInterface

noncomputable local instance rationalDatumSubgroupFintype
    (x : RationalDatum K N) : Fintype x.subgroup.carrier :=
  Fintype.ofFinite x.subgroup.carrier

/-- Rational points of the represented Weierstrass group scheme, written
additively to match Mathlib's coordinate point group. -/
abbrev RepresentedRationalPoint
    (M : WeierstrassGroupSchemeInterface W) :=
  Additive (CommGroupScheme.Point M.groupScheme
    (AffineCommGroupScheme.testObject (R := K) K))

/-- The supplied coordinate-to-scheme point comparison in additive
notation. -/
def rationalPointAddEquiv
    (M : WeierstrassGroupSchemeInterface W) :
    W.toAffine.Point ≃+ RepresentedRationalPoint M :=
  M.rationalPointEquiv.toAdditive

omit [W.IsElliptic] in
@[simp]
theorem rationalPointAddEquiv_apply
    (M : WeierstrassGroupSchemeInterface W) (P : W.toAffine.Point) :
    rationalPointAddEquiv M P =
      Additive.ofMul (M.rationalPointEquiv (Multiplicative.ofAdd P)) :=
  rfl

/-- Rational points of the actual finite-flat subgroup carrier attached to a
raw rational datum. -/
abbrev FiniteFlatSubgroupRationalPoint
    (x : RationalDatum K N)
    (M : WeierstrassGroupSchemeInterface x.curve) :=
  Additive
    ((splitGammaZeroDatumOfRationalDatum x M).subgroup.carrier.Point
      (AffineCommGroupScheme.testObject (R := K) K))

/-- The map on rational points induced by the genuine closed finite-flat
subgroup immersion. -/
def finiteFlatSubgroupPointHom
    (x : RationalDatum K N)
    (M : WeierstrassGroupSchemeInterface x.curve) :
    FiniteFlatSubgroupRationalPoint x M →+
      RepresentedRationalPoint M :=
  (CommGroupScheme.mapPoint
      (splitGammaZeroDatumOfRationalDatum x M).subgroup.inclusion
      (AffineCommGroupScheme.testObject (R := K) K)).toAdditive

/-- Over the field `K`, the points of the constant subgroup carrier are
exactly the elements of the original cyclic subgroup. -/
def finiteFlatSubgroupConstantPointEquiv
    (x : RationalDatum K N)
    (M : WeierstrassGroupSchemeInterface x.curve) :
    x.subgroup.carrier ≃+ FiniteFlatSubgroupRationalPoint x M :=
  (FiniteFlatCommGroupScheme.constantPointMulEquiv_of_noZeroDivisors
    K (Multiplicative x.subgroup.carrier)).toAdditive

/-- The constant-point equivalence sends an element to its distinguished
section of the constant finite-flat carrier. -/
@[simp]
theorem finiteFlatSubgroupConstantPointEquiv_apply
    (x : RationalDatum K N)
    (M : WeierstrassGroupSchemeInterface x.curve)
    (z : x.subgroup.carrier) :
    finiteFlatSubgroupConstantPointEquiv x M z =
      Additive.ofMul
        (AlgebraicGeometry.FiniteFlatCommGroupScheme.constantGeometricPoint K
          (Multiplicative x.subgroup.carrier) (Multiplicative.ofAdd z)) :=
  rfl

/-- The actual closed subgroup immersion agrees, on every rational point of
its carrier, with the original coordinate subgroup inclusion. -/
theorem finiteFlatSubgroupPointHom_constantPointEquiv_apply
    (x : RationalDatum K N)
    (M : WeierstrassGroupSchemeInterface x.curve)
    (z : x.subgroup.carrier) :
    finiteFlatSubgroupPointHom x M
        (finiteFlatSubgroupConstantPointEquiv x M z) =
      rationalPointAddEquiv M z := by
  change CommGroupScheme.mapPoint
      (splitGammaZeroDatumOfRationalCyclicSubgroup
        x.curve M x.subgroup).subgroup.inclusion
      (AffineCommGroupScheme.testObject (R := K) K)
      (AlgebraicGeometry.FiniteFlatCommGroupScheme.constantGeometricPoint K
        (Multiplicative x.subgroup.carrier) (Multiplicative.ofAdd z)) =
    M.rationalPointEquiv (Multiplicative.ofAdd (z : x.curve.toAffine.Point))
  simpa [rationalCyclicSubgroupParameterization] using
    splitGammaZeroDatumOfRationalCyclicSubgroup_map_constantPoint
      x.curve M x.subgroup (Multiplicative.ofAdd z)

/-- Homomorphism form of compatibility between the actual finite-flat
subgroup points and the coordinate subgroup. -/
theorem finiteFlatSubgroupPointHom_comp_constantPointEquiv
    (x : RationalDatum K N)
    (M : WeierstrassGroupSchemeInterface x.curve) :
    (finiteFlatSubgroupPointHom x M).comp
        (finiteFlatSubgroupConstantPointEquiv x M).toAddMonoidHom =
      (rationalPointAddEquiv M).toAddMonoidHom.comp
        (AddSubgroup.subtype x.subgroup.carrier) := by
  apply AddMonoidHom.ext
  exact finiteFlatSubgroupPointHom_constantPointEquiv_apply x M

/-- The rational-point image of the genuine finite-flat subgroup
immersion. -/
def finiteFlatSubgroupPointRange
    (x : RationalDatum K N)
    (M : WeierstrassGroupSchemeInterface x.curve) :
    AddSubgroup (RepresentedRationalPoint M) :=
  (finiteFlatSubgroupPointHom x M).range

/-- The image of the actual finite-flat subgroup immersion is precisely the
coordinate cyclic subgroup transported into represented rational points. -/
theorem finiteFlatSubgroupPointRange_eq_map
    (x : RationalDatum K N)
    (M : WeierstrassGroupSchemeInterface x.curve) :
    finiteFlatSubgroupPointRange x M =
      x.subgroup.carrier.map
        (rationalPointAddEquiv M).toAddMonoidHom := by
  have htop :
      (finiteFlatSubgroupConstantPointEquiv x M).toAddMonoidHom.range = ⊤ :=
    AddMonoidHom.range_eq_top.mpr
      (finiteFlatSubgroupConstantPointEquiv x M).surjective
  rw [finiteFlatSubgroupPointRange,
    ← AddSubgroup.range_subtype x.subgroup.carrier,
    ← AddMonoidHom.range_comp,
    ← finiteFlatSubgroupPointHom_comp_constantPointEquiv x M,
    AddMonoidHom.range_comp,
    htop]
  exact AddMonoidHom.range_eq_map (finiteFlatSubgroupPointHom x M)

/-- The quotient of represented rational points by the image of the actual
closed finite-flat subgroup.  This is a point group, not a quotient scheme. -/
abbrev RepresentedPointQuotient
    (x : RationalDatum K N)
    (M : WeierstrassGroupSchemeInterface x.curve) :=
  RepresentedRationalPoint M ⧸ finiteFlatSubgroupPointRange x M

/-- The canonical projection to the quotient of represented rational
points. -/
def representedPointQuotientMap
    (x : RationalDatum K N)
    (M : WeierstrassGroupSchemeInterface x.curve) :
    RepresentedRationalPoint M →+ RepresentedPointQuotient x M :=
  QuotientAddGroup.mk' (finiteFlatSubgroupPointRange x M)

/-- The represented rational-point quotient projection is surjective. -/
theorem representedPointQuotientMap_surjective
    (x : RationalDatum K N)
    (M : WeierstrassGroupSchemeInterface x.curve) :
    Function.Surjective (representedPointQuotientMap x M) :=
  QuotientAddGroup.mk'_surjective (finiteFlatSubgroupPointRange x M)

/-- The kernel of the represented rational-point quotient is exactly the
image of the actual finite-flat subgroup immersion. -/
@[simp]
theorem representedPointQuotientMap_ker
    (x : RationalDatum K N)
    (M : WeierstrassGroupSchemeInterface x.curve) :
    (representedPointQuotientMap x M).ker =
      finiteFlatSubgroupPointRange x M :=
  QuotientAddGroup.ker_mk' (finiteFlatSubgroupPointRange x M)

/-- The quotient projection kills the rational points coming from the
actual closed finite-flat subgroup. -/
theorem representedPointQuotientMap_comp_finiteFlatSubgroupPointHom
    (x : RationalDatum K N)
    (M : WeierstrassGroupSchemeInterface x.curve) :
    (representedPointQuotientMap x M).comp
        (finiteFlatSubgroupPointHom x M) = 0 := by
  apply AddMonoidHom.ext
  intro P
  change (↑(finiteFlatSubgroupPointHom x M P) :
    RepresentedPointQuotient x M) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact ⟨P, rfl⟩

/-- The coordinate-point quotient attached to `x` is canonically equivalent
to the quotient by the image of its genuine finite-flat subgroup. -/
def representedPointQuotientEquiv
    (x : RationalDatum K N)
    (M : WeierstrassGroupSchemeInterface x.curve) :
    x.PointQuotient ≃+ RepresentedPointQuotient x M :=
  QuotientAddGroup.congr x.subgroup.carrier
    (finiteFlatSubgroupPointRange x M)
    (rationalPointAddEquiv M)
    (finiteFlatSubgroupPointRange_eq_map x M).symm

/-- The quotient equivalence commutes with the two canonical quotient
projections. -/
@[simp]
theorem representedPointQuotientEquiv_pointQuotientMap
    (x : RationalDatum K N)
    (M : WeierstrassGroupSchemeInterface x.curve)
    (P : x.curve.toAffine.Point) :
    representedPointQuotientEquiv x M (x.pointQuotientMap P) =
      representedPointQuotientMap x M (rationalPointAddEquiv M P) :=
  rfl

/-- The rational-point image of the finite-flat cyclic subgroup is killed by
multiplication by its order. -/
theorem finiteFlatSubgroupPointRange_le_nsmul_ker
    (x : RationalDatum K N)
    (M : WeierstrassGroupSchemeInterface x.curve) :
    finiteFlatSubgroupPointRange x M ≤
      (nsmulAddMonoidHom N : RepresentedRationalPoint M →+
        RepresentedRationalPoint M).ker := by
  rw [finiteFlatSubgroupPointRange_eq_map]
  rintro Q ⟨P, hP, rfl⟩
  rw [AddMonoidHom.mem_ker]
  change N • rationalPointAddEquiv M P = 0
  have hNP := x.subgroup.carrier_le_nsmul_ker hP
  change N • P = 0 at hNP
  calc
    N • rationalPointAddEquiv M P =
        rationalPointAddEquiv M (N • P) :=
      (map_nsmul (rationalPointAddEquiv M) N P).symm
    _ = rationalPointAddEquiv M 0 :=
      congrArg (rationalPointAddEquiv M) hNP
    _ = 0 := map_zero (rationalPointAddEquiv M)

/-- Multiplication by `N` descended through the quotient of represented
rational points. -/
def representedPointQuotientDualMap
    (x : RationalDatum K N)
    (M : WeierstrassGroupSchemeInterface x.curve) :
    RepresentedPointQuotient x M →+ RepresentedRationalPoint M :=
  QuotientAddGroup.lift (finiteFlatSubgroupPointRange x M)
    (nsmulAddMonoidHom N)
    (finiteFlatSubgroupPointRange_le_nsmul_ker x M)

/-- The descended map sends the class of a represented point to its
`N`-fold multiple. -/
@[simp]
theorem representedPointQuotientDualMap_mk
    (x : RationalDatum K N)
    (M : WeierstrassGroupSchemeInterface x.curve)
    (P : RepresentedRationalPoint M) :
    representedPointQuotientDualMap x M
        (representedPointQuotientMap x M P) = N • P :=
  rfl

/-- Descended multiplication after the quotient projection is
multiplication by `N`. -/
theorem representedPointQuotientDualMap_comp_quotientMap
    (x : RationalDatum K N)
    (M : WeierstrassGroupSchemeInterface x.curve) :
    (representedPointQuotientDualMap x M).comp
        (representedPointQuotientMap x M) =
      nsmulAddMonoidHom N := by
  apply AddMonoidHom.ext
  intro P
  exact representedPointQuotientDualMap_mk x M P

/-- Quotient projection after the descended map is multiplication by `N` on
the represented rational-point quotient. -/
theorem representedPointQuotientMap_comp_dualMap
    (x : RationalDatum K N)
    (M : WeierstrassGroupSchemeInterface x.curve) :
    (representedPointQuotientMap x M).comp
        (representedPointQuotientDualMap x M) =
      nsmulAddMonoidHom N := by
  apply AddMonoidHom.ext
  intro Q
  induction Q using QuotientAddGroup.induction_on with
  | H P => simp [representedPointQuotientMap,
      representedPointQuotientDualMap]

/-- The kernel of the descended map is the image of the full represented
`N`-torsion subgroup in the point quotient. -/
theorem representedPointQuotientDualMap_ker
    (x : RationalDatum K N)
    (M : WeierstrassGroupSchemeInterface x.curve) :
    (representedPointQuotientDualMap x M).ker =
      (nsmulAddMonoidHom N : RepresentedRationalPoint M →+
        RepresentedRationalPoint M).ker.map
          (representedPointQuotientMap x M) :=
  QuotientAddGroup.ker_lift
    (N := finiteFlatSubgroupPointRange x M) (nsmulAddMonoidHom N)
    (finiteFlatSubgroupPointRange_le_nsmul_ker x M)

/-- The quotient equivalence intertwines the abstract descended dual map
with descended multiplication on represented rational points. -/
theorem representedPointQuotientEquiv_dualMap
    (x : RationalDatum K N)
    (M : WeierstrassGroupSchemeInterface x.curve)
    (Q : x.PointQuotient) :
    representedPointQuotientDualMap x M
        (representedPointQuotientEquiv x M Q) =
      rationalPointAddEquiv M (x.pointQuotientDualMap Q) := by
  induction Q using QuotientAddGroup.induction_on with
  | H P =>
      change N • rationalPointAddEquiv M P =
        rationalPointAddEquiv M (N • P)
      exact (map_nsmul (rationalPointAddEquiv M) N P).symm

end WeierstrassGroupSchemeInterface
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
