/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde
import MazurTorsion.Upstream.SchemeModuleCohomologyHZero

/-!
# Degree-zero cohomology of affine tilde modules

This file is a concrete downstream consumer of
`SchemeModuleCohomology.hZeroEquivGlobalSections`.  Mathlib's affine
global-sections equivalence for a tilde module then recovers the original
coefficient module.

No positive-degree affine acyclicity statement is made here.
-/

noncomputable section

universe u

open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

/-- On an affine scheme, the degree-zero cohomology of the tilde sheaf of a
module is the original module. -/
noncomputable def affineTildeHZeroEquiv {R : CommRingCat.{u}}
    (M : ModuleCat R) : H (tilde M) 0 ≃+ M :=
  (hZeroEquivGlobalSections (tilde M)).trans
    (tilde.isoTop M).symm.toLinearEquiv.toAddEquiv

end MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology
