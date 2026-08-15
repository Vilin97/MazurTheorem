/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import MazurTorsion.AlgebraicGeometry.Jacobian.RelativePicardFunctor

/-!
# Fppf sheafification of the relative Picard functor

The Picard functor used in representability is the fppf sheaf associated to
the unpointed quotient presheaf.  This file packages that sheaf and its
canonical map from the presheaf.  Since the Picard groups in the upstream API
use multiplicative notation, we pass through the standard equivalence
`CommGrpCat ≌ AddCommGrpCat` before sheafification.

No representability statement is made here.  The named downstream consumer
is `PicardRepresentability`.
-/

noncomputable section

open CategoryTheory
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.RelativePicard

universe u

variable {S X : Scheme.{u}}

/-- The unpointed relative Picard presheaf in additive notation. -/
noncomputable def additivePresheaf (p : X ⟶ S) :
    (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  functor p ⋙ CommGrpCat.toAddCommGrp

/-- The fppf relative Picard sheaf.  Sheafification is part of the definition,
so this object exists before any representability or rational-point theorem. -/
noncomputable def fppfSheaf (p : X ⟶ S) :
    Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1} :=
  (presheafToSheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).obj
    (additivePresheaf p)

/-- The canonical morphism from the relative Picard presheaf to its fppf
sheafification. -/
noncomputable def toFppfSheaf (p : X ⟶ S) :
    additivePresheaf p ⟶
      (sheafToPresheaf (Scheme.fppfTopology.over S)
        AddCommGrpCat.{u + 1}).obj (fppfSheaf p) :=
  (sheafificationAdjunction (Scheme.fppfTopology.over S)
    AddCommGrpCat.{u + 1}).unit.app (additivePresheaf p)

/-- Evaluation of the sheafification map at a test scheme. -/
noncomputable def classToFppfSheaf (p : X ⟶ S) (T : Over S) :
    (additivePresheaf p).obj (Opposite.op T) ⟶
      (fppfSheaf p).obj.obj (Opposite.op T) :=
  (toFppfSheaf p).app (Opposite.op T)

/-- The sheafification map is natural in the test scheme. -/
theorem classToFppfSheaf_naturality
    (p : X ⟶ S) {T T' : Over S} (g : T' ⟶ T) :
    (additivePresheaf p).map g.op ≫ classToFppfSheaf p T' =
      classToFppfSheaf p T ≫ (fppfSheaf p).obj.map g.op := by
  exact (toFppfSheaf p).naturality g.op

end MazurTorsion.AlgebraicGeometry.Jacobian.RelativePicard
