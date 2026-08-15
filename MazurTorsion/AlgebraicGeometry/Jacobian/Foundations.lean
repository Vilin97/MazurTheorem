/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.Genus
import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteGroupQuotient
import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteMapToProjectiveLine
import MazurTorsion.AlgebraicGeometry.Jacobian.PermutationPower
import MazurTorsion.AlgebraicGeometry.Jacobian.SymmetricPower
import MazurTorsion.AlgebraicGeometry.Jacobian.PicardIdentityComponent

/-!
# Foundations for the Jacobian and Albanese construction

This module is the narrow import boundary for the checked cohomological and
relative-Picard foundations of the Jacobian construction.  It does not claim
Picard representability, the geometry of the identity component, or the
Albanese universal property.

The named downstream consumer is
`MazurTorsion.AlgebraicGeometry.Jacobian.LeanEval`.
-/
