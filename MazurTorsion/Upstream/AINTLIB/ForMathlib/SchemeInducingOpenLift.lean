/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

Adapted from the Apache-licensed `SchemeInducingOpenLift.lean` in
Vilin97/Clawristotle.
-/
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Lifting opens along inducing scheme morphisms

Every open in the source of an inducing scheme morphism is the inverse
image of a chosen target open.
-/

open AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A chosen target open whose inverse image is the given source open. -/
noncomputable def targetOpenOfIsInducing
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : Topology.IsInducing f) (U : X.Opens) : Y.Opens :=
  ⟨Classical.choose (hf.isOpen_iff.mp U.2),
    (Classical.choose_spec (hf.isOpen_iff.mp U.2)).1⟩

/-- The chosen target open pulls back to the given source open. -/
@[simp]
theorem preimage_targetOpenOfIsInducing
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : Topology.IsInducing f) (U : X.Opens) :
    f ⁻¹ᵁ f.targetOpenOfIsInducing hf U = U := by
  apply Opens.ext
  exact (Classical.choose_spec (hf.isOpen_iff.mp U.2)).2

/-- Membership in the lifted open is preserved by the inducing map. -/
theorem mem_targetOpenOfIsInducing
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : Topology.IsInducing f) (U : X.Opens)
    (x : X) (hx : x ∈ U) :
    f x ∈ f.targetOpenOfIsInducing hf U := by
  have hx' : x ∈ f ⁻¹ᵁ f.targetOpenOfIsInducing hf U := by
    simpa using hx
  exact hx'

/-- A chosen target open for a source open under a closed immersion. -/
noncomputable def closedImmersionTargetOpen
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    (U : X.Opens) : Y.Opens :=
  i.targetOpenOfIsInducing i.isClosedEmbedding.isInducing U

/-- A closed-immersion target open has the prescribed inverse image. -/
@[simp]
theorem preimage_closedImmersionTargetOpen
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    (U : X.Opens) :
    i ⁻¹ᵁ i.closedImmersionTargetOpen U = U :=
  i.preimage_targetOpenOfIsInducing
    i.isClosedEmbedding.isInducing U

end AlgebraicGeometry.Scheme.Hom
