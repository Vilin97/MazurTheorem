/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import TauCeti.AlgebraicGeometry.AbelianVariety.Basic

/-!
# Supplying the Weierstrass group-scheme interface from an abelian variety

Tau Ceti's pinned abelian-variety API contains an actual proper geometrically
integral group scheme over a field.  Its rigidity theorem supplies
commutativity.  This file checks that such an abelian variety, together with
the remaining comparison on rational points, supplies the exact
`WeierstrassGroupSchemeInterface` consumed by the finite-flat `X₀(N)` layer.

This separates two genuinely different tasks.  The group-scheme packaging is
now discharged by the checked abelian-variety API.  What remains for a
Weierstrass equation is to construct its projective cubic as an abelian
variety and identify its scheme-valued rational points with Mathlib's
coordinate point group.
-/

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli

universe u

open XZeroModuli

variable {K : Type u} [Field K] [DecidableEq K]
  {N : ℕ} [NeZero N]
  (W : WeierstrassCurve K) [W.IsElliptic]

/-- The rational points of an abelian variety, expressed using the same test
object as `WeierstrassGroupSchemeInterface`. -/
abbrev AbelianVarietyRationalPoint
    (A : TauCeti.AlgebraicGeometry.AbelianVariety K) :=
  CommGroupScheme.Point (CommGrp.mk A.toOver)
    (AlgebraicGeometry.AffineCommGroupScheme.testObject (R := K) K)

/-- A comparison between a Weierstrass coordinate group and the rational
points of a supplied abelian variety.

The abelian variety already carries all scheme-theoretic group laws.  Thus
this is the only additional datum needed to feed it to the finite-flat
`X₀(N)` construction. -/
structure WeierstrassAbelianVarietyComparison where
  /-- The projective abelian variety associated to the Weierstrass equation. -/
  abelianVariety : TauCeti.AlgebraicGeometry.AbelianVariety K
  /-- The checked multiplicative equivalence on rational points. -/
  rationalPointEquiv :
    Multiplicative W.toAffine.Point ≃*
      AbelianVarietyRationalPoint abelianVariety

namespace WeierstrassAbelianVarietyComparison

/-- Build the comparison from the projective coordinate-point type naturally
associated to the cubic equation.  Mathlib's checked projective-to-affine
additive equivalence supplies the change of point model. -/
def ofProjectivePointEquiv
    (A : TauCeti.AlgebraicGeometry.AbelianVariety K)
    (e : Multiplicative W.toProjective.Point ≃*
      AbelianVarietyRationalPoint A) :
    WeierstrassAbelianVarietyComparison W where
  abelianVariety := A
  rationalPointEquiv :=
    (WeierstrassCurve.Projective.Point.toAffineAddEquiv W).toMultiplicative.symm.trans e

omit [W.IsElliptic] in
@[simp]
theorem ofProjectivePointEquiv_rationalPointEquiv_apply
    (A : TauCeti.AlgebraicGeometry.AbelianVariety K)
    (e : Multiplicative W.toProjective.Point ≃*
      AbelianVarietyRationalPoint A)
    (P : Multiplicative W.toAffine.Point) :
    (ofProjectivePointEquiv W A e).rationalPointEquiv P =
      e ((WeierstrassCurve.Projective.Point.toAffineAddEquiv W).symm P.toAdd) :=
  rfl

/-- An abelian-variety comparison supplies the exact Weierstrass group-scheme
interface.  Commutativity comes from Tau Ceti's rigidity theorem for proper
geometrically integral group schemes. -/
def toGroupSchemeInterface
    (M : WeierstrassAbelianVarietyComparison W) :
    WeierstrassGroupSchemeInterface W where
  groupScheme := CommGrp.mk M.abelianVariety.toOver
  rationalPointEquiv := M.rationalPointEquiv

omit [W.IsElliptic] in
@[simp]
theorem toGroupSchemeInterface_groupScheme
    (M : WeierstrassAbelianVarietyComparison W) :
    M.toGroupSchemeInterface.groupScheme = CommGrp.mk M.abelianVariety.toOver :=
  rfl

omit [W.IsElliptic] in
@[simp]
theorem toGroupSchemeInterface_rationalPointEquiv
    (M : WeierstrassAbelianVarietyComparison W) :
    M.toGroupSchemeInterface.rationalPointEquiv = M.rationalPointEquiv :=
  rfl

/-- A marked point of exact order `N` produces the checked finite-flat split
`Gamma₀(N)` datum directly from an abelian-variety comparison.  This is the
downstream consumer validating `toGroupSchemeInterface`. -/
def splitGammaZeroDatumOfTorsion
    (M : WeierstrassAbelianVarietyComparison W)
    (P : W.toAffine.Point) (hP : addOrderOf P = N) :
    WeierstrassGroupSchemeInterface.SplitGammaZeroDatum
      (N := N) W M.toGroupSchemeInterface :=
  WeierstrassGroupSchemeInterface.splitGammaZeroDatumOfTorsion
    W M.toGroupSchemeInterface P hP

/-- Direct projective-point consumer: once the projective cubic is packaged
as an abelian variety and its `K`-points are identified with Mathlib's
projective coordinate points, exact torsion gives the finite-flat split
`Gamma₀(N)` datum. -/
def splitGammaZeroDatumOfProjectivePointComparison
    (A : TauCeti.AlgebraicGeometry.AbelianVariety K)
    (e : Multiplicative W.toProjective.Point ≃*
      AbelianVarietyRationalPoint A)
    (P : W.toAffine.Point) (hP : addOrderOf P = N) :
    WeierstrassGroupSchemeInterface.SplitGammaZeroDatum
      (N := N) W (ofProjectivePointEquiv W A e).toGroupSchemeInterface :=
  splitGammaZeroDatumOfTorsion W (ofProjectivePointEquiv W A e) P hP

omit [W.IsElliptic] in
/-- The abelian-variety-backed cyclic subgroup has constant geometric order
`N`. -/
theorem splitGammaZeroDatumOfTorsion_hasConstantOrder
    (M : WeierstrassAbelianVarietyComparison W)
    (P : W.toAffine.Point) (hP : addOrderOf P = N) :
    (splitGammaZeroDatumOfTorsion W M P hP).subgroup.carrier.HasConstantOrder N :=
  WeierstrassGroupSchemeInterface.splitGammaZeroDatumOfTorsion_hasConstantOrder
    W M.toGroupSchemeInterface P hP

omit [W.IsElliptic] in
/-- Pulling the scheme-theoretic subgroup points back through the supplied
abelian-variety comparison recovers exactly the cyclic subgroup generated by
the marked Weierstrass point. -/
theorem splitGammaZeroDatumPointHom_range
    (M : WeierstrassAbelianVarietyComparison W)
    (P : W.toAffine.Point) (hP : addOrderOf P = N) :
    (WeierstrassGroupSchemeInterface.splitGammaZeroDatumPointHom
        W M.toGroupSchemeInterface P hP).range =
      (RationalCyclicSubgroup.ofPoint P hP).carrier :=
  WeierstrassGroupSchemeInterface.splitGammaZeroDatumPointHom_range
    W M.toGroupSchemeInterface P hP

end WeierstrassAbelianVarietyComparison

end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
