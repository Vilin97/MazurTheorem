/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverIsoOverlap

/-!
# Glued schemes associated to isomorphic open covers

An isomorphism between two open covers of the same scheme induces an
isomorphism between the schemes reconstructed from their glue data.  Its
restriction to every chart is the corresponding component of the cover
isomorphism.
-/


open CategoryTheory

noncomputable section

namespace AlgebraicGeometry.Scheme.Cover

variable {X : Scheme.{0}} {𝒰 𝒱 : X.OpenCover}

/-- The chart inclusion of a glued open cover, with its source index
exposed in the public type. -/
abbrev gluedCoverChartMap (𝒰 : X.OpenCover) (i : 𝒰.I₀) :
    𝒰.X i ⟶ 𝒰.gluedCover.glued :=
  𝒰.gluedCover.ι i

@[simp, reassoc]
theorem gluedCoverChartMap_fromGlued
    (𝒰 : X.OpenCover) (i : 𝒰.I₀) :
    gluedCoverChartMap 𝒰 i ≫ 𝒰.fromGlued = 𝒰.f i :=
  𝒰.ι_fromGlued i

/-- The comparison between the schemes glued from two isomorphic open
covers, obtained through their common ambient scheme. -/
def coverIsoGluedIso (_e : 𝒰 ≅ 𝒱) :
    𝒰.gluedCover.glued ≅ 𝒱.gluedCover.glued :=
  asIso 𝒰.fromGlued ≪≫ (asIso 𝒱.fromGlued).symm

/-- The comparison followed by the target reconstruction map is the
source reconstruction map. -/
@[simp, reassoc]
theorem coverIsoGluedIso_hom_fromGlued
    (e : 𝒰 ≅ 𝒱) :
    (coverIsoGluedIso e).hom ≫ 𝒱.fromGlued =
      𝒰.fromGlued := by
  simp [coverIsoGluedIso, Category.assoc]

/-- On every chart, the glued-scheme comparison restricts to the
corresponding component of the cover isomorphism. -/
@[reassoc]
theorem gluedCover_ι_coverIsoGluedIso_hom
    (e : 𝒰 ≅ 𝒱) (i : 𝒰.I₀) :
    gluedCoverChartMap 𝒰 i ≫ (coverIsoGluedIso e).hom =
      e.hom.h₀ i ≫
        gluedCoverChartMap 𝒱 (e.hom.s₀ i) := by
  apply (cancel_mono 𝒱.fromGlued).1
  simp only [Category.assoc, coverIsoGluedIso_hom_fromGlued,
    gluedCoverChartMap_fromGlued]
  exact (e.hom.w₀ i).symm

end AlgebraicGeometry.Scheme.Cover
