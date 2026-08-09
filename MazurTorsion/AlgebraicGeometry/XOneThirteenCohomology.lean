/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.XOneThirteenHyperellipticMap
import MazurTorsion.Upstream.ProjectiveLineCechHOneFinite

/-!
# Coherent degree-one cohomology on the order-thirteen curve

This file applies the projective-line finite-map theorem to the checked
hyperelliptic map from the glued order-thirteen curve.
-/

noncomputable section

open CategoryTheory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules

namespace MazurTorsion.XOneThirteenProjectiveCurve

universe u

open _root_.MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

/-- Genuine degree-one sheaf cohomology of a finite-type quasicoherent module
on the glued order-thirteen curve is finite over the base field. -/
theorem genuineSheafHOne_finite_of_hyperellipticMap
    (K : Type u) [Field K] (M : (curveScheme K).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    letI :=
      AlgebraicGeometry.ProjectiveLineCohomology.genuineSheafHOneBaseModuleOfFiniteToProjectiveLine
        K (hyperellipticMap K) M
    Module.Finite Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens))
      (GenuineSheafHOne M) := by
  exact
    AlgebraicGeometry.ProjectiveLineCohomology.genuineSheafHOne_finite_of_finite_to_projectiveLine
      K (hyperellipticMap K) M

end MazurTorsion.XOneThirteenProjectiveCurve
