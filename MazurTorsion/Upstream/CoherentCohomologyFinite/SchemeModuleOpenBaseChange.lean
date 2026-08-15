/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemePushforwardRestriction
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleRestrictionPullbackComposition

/-!
# Base change for scheme modules along a target open

For a scheme morphism `f : X ⟶ Y` and an open subscheme `U ⊆ Y`, the
restriction square is cartesian.  This file records both the canonical
pullback comparison for that square and the formal unit identity obtained
by taking mates of the pushforward comparison.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/--
Pullback commutes with restriction to an open of the target.

This is assembled only from the pseudofunctoriality of module pullback,
the equality defining `morphismRestrict`, and the canonical comparison
between open restriction and pullback.
-/
noncomputable def pullbackRestrictBaseChangeIso
    (f : X ⟶ Y) (U : Y.Opens) :
    restrictFunctor U.ι ⋙ pullback (f ∣_ U) ≅
      pullback f ⋙ restrictFunctor (f ⁻¹ᵁ U).ι :=
  Functor.isoWhiskerRight
      (restrictFunctorIsoPullback U.ι)
      (pullback (f ∣_ U)) ≪≫
    pullbackComp (f ∣_ U) U.ι ≪≫
    pullbackCongr (morphismRestrict_ι f U) ≪≫
    (pullbackComp (f ⁻¹ᵁ U).ι f).symm ≪≫
    Functor.isoWhiskerLeft
      (pullback f)
      (restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).symm

/--
The left Beck--Chevalley morphism obtained as the mate of the concrete
pushforward/restriction comparison.
-/
noncomputable def pullbackRestrictMate
    (f : X ⟶ Y) (U : Y.Opens) :
    restrictFunctor U.ι ⋙ pullback (f ∣_ U) ⟶
      pullback f ⋙ restrictFunctor (f ⁻¹ᵁ U).ι :=
  (mateEquiv
      (pullbackPushforwardAdjunction f)
      (pullbackPushforwardAdjunction (f ∣_ U))).symm
    (TwoSquare.mk _ _ _ _
      (pushforwardRestrictIso f U).hom)

/--
Restricting the pullback--pushforward unit and then applying open base
change equals the unit of the restricted morphism followed by the mate
comparison on pullbacks.
-/
@[reassoc]
theorem restrict_pullbackPushforward_unit_baseChange
    (f : X ⟶ Y) (U : Y.Opens) (M : Y.Modules) :
    (restrictFunctor U.ι).map
          ((pullbackPushforwardAdjunction f).unit.app M) ≫
        (pushforwardRestrictIso f U).hom.app
          ((pullback f).obj M) =
      (pullbackPushforwardAdjunction (f ∣_ U)).unit.app
          ((restrictFunctor U.ι).obj M) ≫
        (pushforward (f ∣_ U)).map
          ((pullbackRestrictMate f U).app M) := by
  exact
    unit_mateEquiv_symm
      (pullbackPushforwardAdjunction f)
      (pullbackPushforwardAdjunction (f ∣_ U))
      (TwoSquare.mk _ _ _ _
        (pushforwardRestrictIso f U).hom)
      M

end AlgebraicGeometry.Scheme.Modules
