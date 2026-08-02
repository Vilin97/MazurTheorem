/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.AINTLIB.ForMathlib.CartierDual
import MazurTorsion.Upstream.AINTLIB.Picard.Pic
import MazurTorsion.Upstream.CurveAffineChart
import MazurTorsion.Upstream.CurveLineBundleDescent
import TauCeti.AlgebraicGeometry.LineBundle.Basic
import TauCeti.AlgebraicGeometry.WeilDivisor.AbelJacobi.Basic

/-!
# Shared upstream geometry

This module is the checked dependency boundary between Mazur's theorem and
the reusable algebraic-geometry developments in AINTLIB and Tau Ceti.

Only file-level Apache-2.0, placeholder-free AINTLIB material is imported:
the Picard group of a scheme, the divisor-line-bundle, affine-chart, and descent bridges, and the
Hopf-algebraic form of Deligne's order theorem. Tau Ceti supplies the
maintained line-bundle and abstract Abel--Jacobi APIs on the project's exact
Lean/Mathlib pin.
-/
