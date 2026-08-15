/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Lifting opens along inducing scheme morphisms

The topology on the source of an inducing morphism is induced from the
target.  Consequently every source open is the inverse image of a chosen
target open.  We package one such choice for use with closed support
thickenings.
-/


open AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

universe u

variable {X Y : Scheme.{u}}

/-- A chosen target open whose inverse image is `U`. -/
noncomputable def targetOpenOfIsInducing
    (f : X ⟶ Y) (hf : Topology.IsInducing f)
    (U : X.Opens) : Y.Opens :=
  ⟨Classical.choose (hf.isOpen_iff.mp U.2),
    (Classical.choose_spec
      (hf.isOpen_iff.mp U.2)).1⟩

/-- The chosen target open pulls back to the original source open. -/
@[simp]
theorem preimage_targetOpenOfIsInducing
    (f : X ⟶ Y) (hf : Topology.IsInducing f)
    (U : X.Opens) :
    f ⁻¹ᵁ targetOpenOfIsInducing f hf U = U := by
  apply Opens.ext
  exact
    (Classical.choose_spec
      (hf.isOpen_iff.mp U.2)).2

/-- Membership in the lifted open is preserved by the inducing map. -/
theorem mem_targetOpenOfIsInducing
    (f : X ⟶ Y) (hf : Topology.IsInducing f)
    (U : X.Opens) (x : X) (hx : x ∈ U) :
    f x ∈ targetOpenOfIsInducing f hf U := by
  have :
      x ∈ f ⁻¹ᵁ targetOpenOfIsInducing f hf U := by
    simpa using hx
  exact this

/-- The target-open choice specialized to a closed immersion. -/
noncomputable def closedImmersionTargetOpen
    (i : X ⟶ Y) [IsClosedImmersion i]
    (U : X.Opens) : Y.Opens :=
  targetOpenOfIsInducing
    i i.isClosedEmbedding.isInducing U

/-- A closed-immersion target open has the prescribed inverse image. -/
@[simp]
theorem preimage_closedImmersionTargetOpen
    (i : X ⟶ Y) [IsClosedImmersion i]
    (U : X.Opens) :
    i ⁻¹ᵁ closedImmersionTargetOpen i U = U :=
  preimage_targetOpenOfIsInducing
    i i.isClosedEmbedding.isInducing U

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
