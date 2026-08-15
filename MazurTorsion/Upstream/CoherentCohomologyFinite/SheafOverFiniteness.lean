/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafFiniteTypeLocal
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafFiniteTypeRestriction
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafOverEquivalence

/-!
# Finiteness on slice sites of opens

The equivalence between modules on an open subscheme and modules on the
corresponding slice site preserves quasicoherence and finite type.  It
follows that both properties pass from an ambient scheme module to its
ordinary slice-site restriction.
-/


open CategoryTheory Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (U : X.Opens)

/-- Cocontinuity of the forward open-slice equivalence. -/
instance overEquivalenceFunctorIsCocontinuous :
    (TopologicalSpace.Opens.overEquivalence U).functor.IsCocontinuous
      ((Opens.grothendieckTopology ↥X).over U)
      (Opens.grothendieckTopology ↥(↑U : Scheme)) :=
  ((TopologicalSpace.Opens.overEquivalence U).toAdjunction
    |>.isCocontinuous_iff_coverPreserving
      ((Opens.grothendieckTopology ↥X).over U)
      (Opens.grothendieckTopology ↥(↑U : Scheme))).2
    (CoverPreserving.of_isContinuous
      (TopologicalSpace.Opens.overEquivalence U).inverse
      (Opens.grothendieckTopology ↥(↑U : Scheme))
      ((Opens.grothendieckTopology ↥X).over U))

/-- Continuity on over-sites induced by the open-slice equivalence. -/
instance overPostOverEquivalenceFunctorIsContinuous
    (V : Over U) :
    (Over.post
      (X := V)
      (TopologicalSpace.Opens.overEquivalence U).functor)
        |>.IsContinuous
          (((Opens.grothendieckTopology ↥X).over U).over V)
          ((Opens.grothendieckTopology ↥(↑U : Scheme)).over
            ((TopologicalSpace.Opens.overEquivalence U).functor.obj V)) :=
  (Functor.isContinuous_iff_coverPreserving
    (F := Over.post
      (X := V)
      (TopologicalSpace.Opens.overEquivalence U).functor)
    (J := ((Opens.grothendieckTopology ↥X).over U).over V)
    (K := (Opens.grothendieckTopology ↥(↑U : Scheme)).over
      ((TopologicalSpace.Opens.overEquivalence U).functor.obj V))).2
    ((CoverPreserving.of_isContinuous
      (TopologicalSpace.Opens.overEquivalence U).functor
      ((Opens.grothendieckTopology ↥X).over U)
      (Opens.grothendieckTopology ↥(↑U : Scheme))).overPost V)

/--
The structure-ring comparison underlying the functor from modules on an
open subscheme to modules on the corresponding slice site.
-/
noncomputable def overEquivalenceRingHom :
    X.ringCatSheaf.over U ⟶
      ((TopologicalSpace.Opens.overEquivalence U).functor
        |>.sheafPushforwardContinuous RingCat
          ((Opens.grothendieckTopology ↥X).over U)
          (Opens.grothendieckTopology ↥(↑U : Scheme))).obj
        (↑U : Scheme).ringCatSheaf :=
  ⟨
    { app := fun V =>
        X.ringCatSheaf.obj.map
          (eqToHom
            (overEquivalence_image_functor_obj
              U V.unop)).op
      naturality := by
        intro A B f
        simp only
          [Functor.sheafPushforwardContinuous_obj_obj_map]
        erw [← Functor.map_comp, ← Functor.map_comp]
        congr 1 }⟩

/-- The open-slice structure-ring comparison is an isomorphism. -/
instance overEquivalenceRingHom_isIso :
    IsIso (overEquivalenceRingHom U) := by
  letI (V : (Over U)ᵒᵖ) :
      IsIso ((overEquivalenceRingHom U).hom.app V) := by
    change
      IsIso
        (X.ringCatSheaf.obj.map
          (eqToHom
            (overEquivalence_image_functor_obj
              U V.unop)).op)
    infer_instance
  rw [← isIso_iff_of_reflects_iso _
    (ObjectProperty.ι _)]
  exact NatIso.isIso_of_isIso_app
    (overEquivalenceRingHom U).hom

/-- The open-slice equivalence preserves quasicoherence. -/
instance overEquivalenceFunctor_isQuasicoherent
    (M : (↑U : Scheme).Modules) [M.IsQuasicoherent] :
    ((overEquivalence U).functor.obj M).IsQuasicoherent := by
  letI :
      (TopologicalSpace.Opens.overEquivalence U).functor.IsContinuous
        ((Opens.grothendieckTopology ↥X).over U)
        (Opens.grothendieckTopology ↥(↑U : Scheme)) :=
    overEquivFunctorIsContinuous U
  let hOver :
      ∀ V : Over U,
        (Over.post
          (TopologicalSpace.Opens.overEquivalence U).functor)
            |>.IsContinuous
              (((Opens.grothendieckTopology ↥X).over U).over V)
              ((Opens.grothendieckTopology ↥(↑U : Scheme)).over
                ((TopologicalSpace.Opens.overEquivalence U).functor.obj V)) :=
    fun V =>
      overPostOverEquivalenceFunctorIsContinuous U V
  letI (V : Over U) :
      (Over.post
        (X := V)
        (TopologicalSpace.Opens.overEquivalence U).functor)
          |>.IsContinuous
            (((Opens.grothendieckTopology ↥X).over U).over V)
            ((Opens.grothendieckTopology ↥(↑U : Scheme)).over
              ((TopologicalSpace.Opens.overEquivalence U).functor.obj V)) :=
    overPostOverEquivalenceFunctorIsContinuous U V
  exact
    @SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint
      _ _ _ _ _ _ _ _ _ _ _ _ _
      (TopologicalSpace.Opens.overEquivalence U).functor
      inferInstance inferInstance
      (overEquivalenceRingHom U) (unitOverIso U)
      inferInstance inferInstance hOver inferInstance inferInstance
      M (by exact ‹M.IsQuasicoherent›)

/-- The open-slice equivalence preserves finite type. -/
instance overEquivalenceFunctor_isFiniteType
    (M : (↑U : Scheme).Modules) [M.IsFiniteType] :
    ((overEquivalence U).functor.obj M).IsFiniteType := by
  letI :
      (TopologicalSpace.Opens.overEquivalence U).functor.IsContinuous
        ((Opens.grothendieckTopology ↥X).over U)
        (Opens.grothendieckTopology ↥(↑U : Scheme)) :=
    overEquivFunctorIsContinuous U
  let hOver :
      ∀ V : Over U,
        (Over.post
          (X := V)
          (TopologicalSpace.Opens.overEquivalence U).functor)
            |>.IsContinuous
              (((Opens.grothendieckTopology ↥X).over U).over V)
              ((Opens.grothendieckTopology ↥(↑U : Scheme)).over
                ((TopologicalSpace.Opens.overEquivalence U).functor.obj V)) :=
    fun V =>
      overPostOverEquivalenceFunctorIsContinuous U V
  letI (V : Over U) :
      (Over.post
        (X := V)
        (TopologicalSpace.Opens.overEquivalence U).functor)
          |>.IsContinuous
            (((Opens.grothendieckTopology ↥X).over U).over V)
            ((Opens.grothendieckTopology ↥(↑U : Scheme)).over
              ((TopologicalSpace.Opens.overEquivalence U).functor.obj V)) :=
    overPostOverEquivalenceFunctorIsContinuous U V
  exact
    @SheafOfModules.isFiniteType_pushforwardOnSameUniverseSites_of_isLeftAdjoint
      _ _ _ _ _ _ (TopologicalSpace.Opens.overEquivalence U).functor _ _
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance
      (overEquivalenceRingHom U) (unitOverIso U)
      inferInstance inferInstance hOver inferInstance inferInstance
      M (by exact ‹M.IsFiniteType›)

/-- Slice-site restriction of a quasicoherent scheme module is
quasicoherent. -/
instance over_isQuasicoherent
    (M : X.Modules) [M.IsQuasicoherent] :
    (M.over U).IsQuasicoherent := by
  letI : (M.restrict U.ι).IsQuasicoherent :=
    inferInstance
  exact
    (SheafOfModules.isQuasicoherent
      (X.ringCatSheaf.over U)).prop_of_iso
        (restrictOverIso U M)
        (by infer_instance)

/-- Slice-site restriction of a finite-type scheme module is finite
type. -/
instance over_isFiniteType
    (M : X.Modules) [M.IsFiniteType] :
    (M.over U).IsFiniteType := by
  letI : (M.restrict U.ι).IsFiniteType :=
    inferInstance
  exact
    SheafOfModules.isFiniteType_of_iso
      (R := X.ringCatSheaf.over U)
      (restrictOverIso U M)

end AlgebraicGeometry.Scheme.Modules
