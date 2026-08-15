/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Extracting a chain resolution from an augmentation

An augmentation `K ⟶ A[0]` which is a quasi-isomorphism contains exactly
the two pieces of source-resolution data used by the Ext comparison:
the zeroth cokernel of `K` is `A`, and `K` is exact in every positive
degree.
-/

open CategoryTheory

namespace ChainComplex

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

noncomputable section

/-- A quasi-isomorphic augmentation to a complex concentrated in degree
zero identifies the zeroth opcycles with its target. -/
noncomputable def opcyclesZeroIsoOfQuasiIsoToSingle
    {K : ChainComplex C ℕ} {A : C}
    (ε : K ⟶ (single₀ C).obj A) [QuasiIso ε] :
    K.opcycles 0 ≅ A :=
  K.isoHomologyι₀.symm ≪≫
    isoOfQuasiIsoAt ε 0 ≪≫
      HomologicalComplex.singleObjHomologySelfIso
        (ComplexShape.down ℕ) 0 A

/-- A chain complex quasi-isomorphic to an object concentrated in degree
zero is exact in every positive degree. -/
theorem exactAtSuccOfQuasiIsoToSingle
    {K : ChainComplex C ℕ} {A : C}
    (ε : K ⟶ (single₀ C).obj A) [QuasiIso ε]
    (n : ℕ) :
    K.ExactAt (n + 1) :=
  (quasiIsoAt_iff_exactAt' ε (n + 1)
    (ChainComplex.exactAt_succ_single_obj A n)).mp inferInstance

end

end ChainComplex
