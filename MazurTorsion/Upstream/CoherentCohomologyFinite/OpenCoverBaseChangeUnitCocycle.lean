/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverBaseChangeOverlap
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleScalarTwistedCoverDescent

/-!
# Unit cocycles under base change of an open cover

A unit on an overlap of an open cover pulls back along the canonical map
from the corresponding overlap of a base-changed cover.  Functoriality on
the three routes out of a triple overlap shows that diagonal-one families
and multiplicative cover cocycles remain so after base change.
-/


open CategoryTheory Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Pullback of global units is contravariantly functorial in the scheme
morphism. -/
lemma pullbackGlobalUnit_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : Γ(Z, ⊤)ˣ) :
    pullbackGlobalUnit f (pullbackGlobalUnit g a) =
      pullbackGlobalUnit (f ≫ g) a := by
  apply Units.ext
  rfl

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Cover

open AlgebraicGeometry.Scheme.Modules

variable {S T : Scheme.{u}} (𝒰 : S.OpenCover) (f : T ⟶ S)

/-- Pull a family of units on the overlaps of an open cover to the
overlaps of its base change. -/
def baseChangeCoverUnit
    (a : ∀ i j : 𝒰.I₀,
      Γ(𝒰.gluedCover.V (i, j), ⊤)ˣ) :
    ∀ i j : 𝒰.I₀,
      Γ((gluedCover (𝒰.pullback₁ f)).V (i, j), ⊤)ˣ :=
  fun i j =>
    pullbackGlobalUnit
      (baseChangeOverlapMap 𝒰 f i j) (a i j)

/-- Base change preserves the diagonal-one law for overlap units. -/
theorem baseChangeCoverUnit_self
    (a : ∀ i j : 𝒰.I₀,
      Γ(𝒰.gluedCover.V (i, j), ⊤)ˣ)
    (hself : ∀ i : 𝒰.I₀, a i i = 1) :
    ∀ i, baseChangeCoverUnit 𝒰 f a i i = 1 := by
  intro i
  rw [baseChangeCoverUnit, hself i]
  exact map_one
    (pullbackGlobalUnit (baseChangeOverlapMap 𝒰 f i i))

/-- The first pulled-back cocycle factor is obtained by pulling the
original first factor along the canonical triple-overlap map. -/
theorem baseChangeCoverUnit_pullback₁₂
    (a : ∀ i j : 𝒰.I₀,
      Γ(𝒰.gluedCover.V (i, j), ⊤)ˣ)
    (i j k : 𝒰.I₀) :
    coverUnitPullback₁₂
        (gluedCover (𝒰.pullback₁ f))
        (baseChangeCoverUnit 𝒰 f a) i j k =
      pullbackGlobalUnit
        (baseChangeTripleOverlapMap 𝒰 f i j k)
        (coverUnitPullback₁₂
          𝒰.gluedCover a i j k) := by
  unfold coverUnitPullback₁₂ baseChangeCoverUnit
  rw [pullbackGlobalUnit_comp, pullbackGlobalUnit_comp,
    baseChangeTripleOverlapMap_fst]

/-- The second pulled-back cocycle factor is obtained by pulling the
original second factor along the canonical triple-overlap map. -/
theorem baseChangeCoverUnit_pullback₂₃
    (a : ∀ i j : 𝒰.I₀,
      Γ(𝒰.gluedCover.V (i, j), ⊤)ˣ)
    (i j k : 𝒰.I₀) :
    coverUnitPullback₂₃
        (gluedCover (𝒰.pullback₁ f))
        (baseChangeCoverUnit 𝒰 f a) i j k =
      pullbackGlobalUnit
        (baseChangeTripleOverlapMap 𝒰 f i j k)
        (coverUnitPullback₂₃
          𝒰.gluedCover a i j k) := by
  unfold coverUnitPullback₂₃ baseChangeCoverUnit
  rw [pullbackGlobalUnit_comp, pullbackGlobalUnit_comp,
    baseChangeTripleOverlapMap_to₂₃]

/-- The third pulled-back cocycle factor is obtained by pulling the
original third factor along the canonical triple-overlap map. -/
theorem baseChangeCoverUnit_pullback₁₃
    (a : ∀ i j : 𝒰.I₀,
      Γ(𝒰.gluedCover.V (i, j), ⊤)ˣ)
    (i j k : 𝒰.I₀) :
    coverUnitPullback₁₃
        (gluedCover (𝒰.pullback₁ f))
        (baseChangeCoverUnit 𝒰 f a) i j k =
      pullbackGlobalUnit
        (baseChangeTripleOverlapMap 𝒰 f i j k)
        (coverUnitPullback₁₃
          𝒰.gluedCover a i j k) := by
  unfold coverUnitPullback₁₃ baseChangeCoverUnit
  rw [pullbackGlobalUnit_comp, pullbackGlobalUnit_comp,
    baseChangeTripleOverlapMap_snd]

/-- Base change of an open cover preserves the unit-valued
triple-overlap cocycle. -/
theorem baseChangeCoverUnit_cocycle
    (a : ∀ i j : 𝒰.I₀,
      Γ(𝒰.gluedCover.V (i, j), ⊤)ˣ)
    (hcocycle : CoverUnitCocycleCondition
      𝒰.gluedCover a) :
    CoverUnitCocycleCondition
      (gluedCover (𝒰.pullback₁ f))
      (baseChangeCoverUnit 𝒰 f a) := by
  change ∀ (i j k : 𝒰.I₀),
    coverUnitPullback₁₂
          (gluedCover (𝒰.pullback₁ f))
          (baseChangeCoverUnit 𝒰 f a) i j k *
        coverUnitPullback₂₃
          (gluedCover (𝒰.pullback₁ f))
          (baseChangeCoverUnit 𝒰 f a) i j k =
      coverUnitPullback₁₃
        (gluedCover (𝒰.pullback₁ f))
        (baseChangeCoverUnit 𝒰 f a) i j k
  intro i j k
  rw [baseChangeCoverUnit_pullback₁₂,
    baseChangeCoverUnit_pullback₂₃,
    baseChangeCoverUnit_pullback₁₃,
    ← map_mul]
  exact congrArg
    (pullbackGlobalUnit
      (baseChangeTripleOverlapMap 𝒰 f i j k))
    (hcocycle i j k)

end AlgebraicGeometry.Scheme.Cover
