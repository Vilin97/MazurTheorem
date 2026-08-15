/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverBaseChangeUnitCocycle
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleScalarTwistNaturalTransformation

/-!
# Compatible scalar sections under base change of an open cover

A compatible family of chart functions pulls back to a compatible
family on the base-changed cover.
-/


open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Cover

open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.CoverDescentData

variable {S T : Scheme.{0}} (𝒰 : S.OpenCover) (f : T ⟶ S)

/-- Pull chart functions to the corresponding charts of a base-changed
open cover. -/
def baseChangeCoverSection
    (b : ∀ i, Γ(𝒰.X i, ⊤)) :
    ∀ i, Γ((𝒰.pullback₁ f).X i, ⊤) :=
  fun i => (𝒰.pullbackHom f i).appTop (b i)

/-- The canonical pair-overlap base-change map commutes with the route
to the second chart. -/
theorem baseChangeOverlapMap_gluedCover_second
    (i j : 𝒰.I₀) :
    baseChangeOverlapMap 𝒰 f i j ≫
        (𝒰.gluedCover.t i j ≫
          𝒰.gluedCover.f j i) =
      ((gluedCover (𝒰.pullback₁ f)).t i j ≫
          (gluedCover (𝒰.pullback₁ f)).f j i) ≫
        𝒰.pullbackHom f j := by
  have hold :
      𝒰.gluedCover.t i j ≫
          𝒰.gluedCover.f j i =
        pullback.snd (𝒰.f i) (𝒰.f j) := by
    change
      (pullbackSymmetry
          (𝒰.f i) (𝒰.f j)).hom ≫
          pullback.fst (𝒰.f j) (𝒰.f i) =
        _
    exact pullbackSymmetry_hom_comp_fst _ _
  have hnew :
      (gluedCover (𝒰.pullback₁ f)).t i j ≫
          (gluedCover (𝒰.pullback₁ f)).f j i =
        pullback.snd
          ((𝒰.pullback₁ f).f i)
          ((𝒰.pullback₁ f).f j) := by
    change
      (pullbackSymmetry
          ((𝒰.pullback₁ f).f i)
          ((𝒰.pullback₁ f).f j)).hom ≫
          pullback.fst
            ((𝒰.pullback₁ f).f j)
            ((𝒰.pullback₁ f).f i) =
        _
    exact pullbackSymmetry_hom_comp_fst _ _
  rw [hold, hnew]
  exact baseChangeOverlapMap_snd 𝒰 f i j

/-- Base change preserves the compatibility equation between a cover
unit cocycle and chart functions. -/
theorem baseChangeCoverSection_compatible
    (a : ∀ i j, Γ(𝒰.gluedCover.V (i, j), ⊤)ˣ)
    (b : ∀ i, Γ(𝒰.gluedCover.U i, ⊤))
    (hb : CoverScalarSectionCompatibility
      (D := 𝒰.gluedCover) a b) :
    CoverScalarSectionCompatibility
      (D := gluedCover (𝒰.pullback₁ f))
      (baseChangeCoverUnit 𝒰 f a)
      (baseChangeCoverSection 𝒰 f b) := by
  intro i j
  have h :=
    congrArg
      (fun z =>
        (baseChangeOverlapMap 𝒰 f i j).appTop z)
      (hb i j)
  rw [map_mul] at h
  have hfirst :
      (baseChangeOverlapMap 𝒰 f i j).appTop
          ((𝒰.gluedCover.f i j).appTop (b i)) =
        ((gluedCover
            (𝒰.pullback₁ f)).f i j).appTop
          ((𝒰.pullbackHom f i).appTop (b i)) := by
    have hmap :=
      congrArg
        (fun p :
          (gluedCover (𝒰.pullback₁ f)).V (i, j) ⟶
            𝒰.gluedCover.U i =>
          p.appTop (b i))
        (baseChangeOverlapMap_gluedCover_f
          𝒰 f i j)
    simp only [Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply] at hmap
    exact hmap
  have hsecond :
      (baseChangeOverlapMap 𝒰 f i j).appTop
          ((𝒰.gluedCover.t i j ≫
            𝒰.gluedCover.f j i).appTop (b j)) =
        ((gluedCover (𝒰.pullback₁ f)).t i j ≫
          (gluedCover (𝒰.pullback₁ f)).f j i).appTop
            ((𝒰.pullbackHom f j).appTop (b j)) := by
    have hmap :=
      congrArg
        (fun p :
          (gluedCover (𝒰.pullback₁ f)).V (i, j) ⟶
            𝒰.gluedCover.U j =>
          p.appTop (b j))
        (baseChangeOverlapMap_gluedCover_second
          𝒰 f i j)
    simp only [Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply] at hmap
    exact hmap
  change
    ((gluedCover (𝒰.pullback₁ f)).f i j).appTop
          ((𝒰.pullbackHom f i).appTop (b i)) *
        (baseChangeOverlapMap 𝒰 f i j).appTop
          (a i j).val =
      ((gluedCover (𝒰.pullback₁ f)).t i j ≫
        (gluedCover (𝒰.pullback₁ f)).f j i).appTop
          ((𝒰.pullbackHom f j).appTop (b j))
  rw [← hfirst, ← hsecond]
  exact h

end AlgebraicGeometry.Scheme.Cover
