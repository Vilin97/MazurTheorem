/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.AINTLIB.ForMathlib.CartierDual
import MazurTorsion.Upstream.AINTLIB.Picard.Pic
import MazurTorsion.Upstream.AffineDivisorTensorBaseChange
import MazurTorsion.Upstream.CurveAffineChart
import MazurTorsion.Upstream.CurveCohomologyGrothendieckVanishing
import MazurTorsion.Upstream.CurveDivisorDescent
import MazurTorsion.Upstream.CurveDivisorPicardDescent
import MazurTorsion.Upstream.CurveDivisorRationalBoundary
import MazurTorsion.Upstream.CurveDivisorTensorAddRestriction
import MazurTorsion.Upstream.CurveDivisorTensorAddOverlap
import MazurTorsion.Upstream.CurveDivisorTensorAddChosenOverlap
import MazurTorsion.Upstream.CurveDivisorTensorAddFactorwiseChosenOverlap
import MazurTorsion.Upstream.CurveDivisorTensorAddDescent
import MazurTorsion.Upstream.CurveDivisorTensorAddFactorwiseDescent
import MazurTorsion.Upstream.CurveDivisorTensorAddTildeRestriction
import MazurTorsion.Upstream.CurveLineBundleDescent
import MazurTorsion.Upstream.CurveLineBundleLocality
import MazurTorsion.Upstream.CurveLineBundleTripleIntersection
import MazurTorsion.Upstream.CurveLineBundleTripleNaturality
import MazurTorsion.Upstream.CurveLineBundleTripleTower
import MazurTorsion.Upstream.CurveLineBundleTransitionCocycle
import MazurTorsion.Upstream.CurveLineBundleTripleProjectionCocycle
import MazurTorsion.Upstream.CurveLineBundleNormalizedTransition
import MazurTorsion.Upstream.CurveLineBundleNamedTripleCocycle
import MazurTorsion.Upstream.CurveLineBundleRawCocyclePrime
import MazurTorsion.Upstream.CurveLineBundleCompatibleFamilies
import MazurTorsion.Upstream.ProperCurveCechLowDegreeFinite
import MazurTorsion.Upstream.ProperCurveCohomologyFinite
import MazurTorsion.Upstream.ProperCurveFiniteSupport
import MazurTorsion.Upstream.ProperCurveFiniteSupportCech
import MazurTorsion.Upstream.SchemeModuleBaseCechHZeroFinite
import TauCeti.AlgebraicGeometry.LineBundle.Basic
import TauCeti.AlgebraicGeometry.WeilDivisor.AbelJacobi.Basic

/-!
# Shared upstream geometry

This module is the checked dependency boundary between Mazur's theorem and
the reusable algebraic-geometry developments in AINTLIB, LeanPool, and Tau Ceti.

Only file-level Apache-2.0, placeholder-free AINTLIB material is imported:
the Picard group of a scheme; the divisor-line-bundle, affine-chart, chartwise divisor, and
descent bridges; and the Hopf-algebraic form of Deligne's order theorem. Tau Ceti supplies the
maintained line-bundle and abstract Abel--Jacobi APIs on the project's exact
Lean/Mathlib pin. The LeanPool Grothendieck-vanishing port is consumed through
the actual underlying additive sheaf of a smooth proper integral curve module.
For degree one, a private DVR uniformizer at a supplied codimension-one point
constructs the finite map to `P¹` consumed by the genuine sheaf-cohomology
finite-dimensionality theorem.
Properness also makes the global-function ring finite over the ground field;
the resulting canonical degree-zero theorem and its arbitrary-cover Cech
comparison certify finite free sheaves as low-degree-good ordered Cech
targets. An affine-open pullback presentation from finite local generators,
together with the strict-support exact-sequence transfers, now proves canonical
degree-zero cohomology finite-dimensional for every coherent module on the
pointed proper curve. The exact low-degree base-change comparison remains the
open boundary of this package.
-/
