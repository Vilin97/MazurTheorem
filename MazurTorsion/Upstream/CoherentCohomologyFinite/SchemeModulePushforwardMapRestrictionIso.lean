/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemePushforwardRestriction

/-!
# Detecting pushforward isomorphisms after open restriction

Restriction of a pushforward map to an open is canonically conjugate to
the pushforward, along the restricted morphism, of the corresponding
restricted source map.  Thus an isomorphism after source restriction
remains an isomorphism after pushforward and target restriction.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X Y : Scheme.{u}}

/--
If a module morphism is invertible over the inverse image of an open,
then its pushforward is invertible after restriction to that open.
-/
theorem isIso_restrict_pushforward_map_of_restrict
    (f : X ⟶ Y) (U : Y.Opens)
    {M N : X.Modules} (α : M ⟶ N)
    [IsIso
      ((restrictFunctor (f ⁻¹ᵁ U).ι).map α)] :
    IsIso
      ((restrictFunctor U.ι).map
        ((pushforward f).map α)) := by
  let e := pushforwardRestrictIso f U
  haveI hRight :
      IsIso
        ((pushforward (f ∣_ U)).map
          ((restrictFunctor (f ⁻¹ᵁ U).ι).map α)) :=
    inferInstance
  haveI hConjugate :
      IsIso
        (e.hom.app M ≫
          ((pushforward (f ∣_ U)).map
            ((restrictFunctor (f ⁻¹ᵁ U).ι).map α))) :=
    IsIso.comp_isIso'
      (e.app M).isIso_hom hRight
  haveI hComposite :
      IsIso
        ((restrictFunctor U.ι).map
            ((pushforward f).map α) ≫
          e.hom.app N) := by
    change
      IsIso
        ((pushforward f ⋙ restrictFunctor U.ι).map α ≫
          e.hom.app N)
    rw [e.hom.naturality α]
    exact hConjugate
  exact
    @IsIso.of_isIso_comp_right _ _ _ _ _
      ((restrictFunctor U.ι).map
        ((pushforward f).map α))
      (e.hom.app N)
      (e.app N).isIso_hom
      hComposite

end AlgebraicGeometry.Scheme.Modules
