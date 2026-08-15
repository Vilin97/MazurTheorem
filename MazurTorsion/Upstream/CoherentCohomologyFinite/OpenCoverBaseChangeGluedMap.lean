/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverBaseChangeOverlap

/-!
# The map between glued schemes induced by base change

For an open cover `𝒰` of `S` and a morphism `f : T ⟶ S`, the glued
scheme of the pulled-back cover maps canonically to the glued scheme of
`𝒰`.  Since both glued-cover comparison maps are isomorphisms, the map
can be written directly by conjugating `f`.
-/


open CategoryTheory

noncomputable section

namespace AlgebraicGeometry.Scheme.Cover

variable {S T : Scheme.{0}} (𝒰 : S.OpenCover) (f : T ⟶ S)

/-- The canonical map from the glued base-changed cover to the glued
original cover. -/
noncomputable def baseChangeGluedMap :
  (gluedCover (𝒰.pullback₁ f)).glued ⟶
      𝒰.gluedCover.glued :=
  fromGlued (𝒰.pullback₁ f) ≫
    f ≫ inv 𝒰.fromGlued

/-- The glued base-change map lies over the original morphism. -/
@[reassoc]
theorem baseChangeGluedMap_fromGlued :
    baseChangeGluedMap 𝒰 f ≫ 𝒰.fromGlued =
      fromGlued (𝒰.pullback₁ f) ≫ f := by
  simp [baseChangeGluedMap, Category.assoc]

/-- Conjugating the glued base-change map by the inverse comparison
maps recovers the original morphism. -/
@[reassoc]
theorem inv_fromGlued_baseChangeGluedMap :
    inv (fromGlued (𝒰.pullback₁ f)) ≫
      baseChangeGluedMap 𝒰 f =
      f ≫ inv 𝒰.fromGlued := by
  simp [baseChangeGluedMap]

/-- On each member of the pulled-back cover, the glued base-change map
is induced by the canonical map to the corresponding original member. -/
@[reassoc]
theorem gluedCover_ι_baseChangeGluedMap (i : 𝒰.I₀) :
    (gluedCover (𝒰.pullback₁ f)).ι i ≫
        baseChangeGluedMap 𝒰 f =
      𝒰.pullbackHom f i ≫
        𝒰.gluedCover.ι i := by
  apply (cancel_mono 𝒰.fromGlued).1
  refine (Category.assoc _ _ _).trans ?_
  refine (CategoryTheory.whisker_eq _ (baseChangeGluedMap_fromGlued 𝒰 f)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (CategoryTheory.eq_whisker (ι_fromGlued (𝒰.pullback₁ f) i) f).trans ?_
  refine (𝒰.pullbackHom_map f i).symm.trans ?_
  refine (CategoryTheory.whisker_eq _ (𝒰.ι_fromGlued i).symm).trans ?_
  exact (Category.assoc _ _ _).symm

end AlgebraicGeometry.Scheme.Cover
