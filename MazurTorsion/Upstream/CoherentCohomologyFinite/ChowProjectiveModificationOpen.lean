/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ChowProjectiveModification
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveGraphClosureDenseOpen
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeModuleOpenUnitIso

/-!
# The canonical Chow modification over its common open

The projective modification produced by Chow's graph construction is an
isomorphism over the open on which the original rational projective map
is defined.  Consequently, the pullback--pushforward unit for any module
becomes invertible after restriction to that open.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

open ProjectiveSpace

namespace ChowGraphEmbeddingData

/--
The modification morphism obtained from an embedded Chow graph is an
isomorphism over the range of the graph domain.
-/
theorem isIso_toProjectiveModification_restrict_opensRange
    {k : Type u} [CommRing k] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)}
    (D : ChowGraphEmbeddingData f) :
    letI : IsOpenImmersion D.toOriginalOpen :=
      D.isOpenImmersion_toOriginalOpen
    letI : QuasiCompact D.toOriginalOpen :=
      D.quasiCompact_toOriginalOpen
    IsIso
      ((projectiveModificationOfChowGraph D).toOriginal ∣_
        D.toOriginalOpen.opensRange) := by
  letI : IsOpenImmersion D.toOriginalOpen :=
    D.isOpenImmersion_toOriginalOpen
  letI : QuasiCompact D.toOriginalOpen :=
    D.quasiCompact_toOriginalOpen
  change
    IsIso
      (projectiveGraphClosureToBase
          f D.dimension D.toOriginalOpen
            D.toProjective D.overBase ∣_
        D.toOriginalOpen.opensRange)
  exact
    isIso_projectiveGraphClosureToBase_restrict_opensRange
      f D.toOriginalOpen D.toProjective D.overBase

end ChowGraphEmbeddingData

namespace ChowGraphMonomorphismData

/--
The same common-open comparison for the monomorphism form of Chow graph
data over a proper scheme.
-/
theorem isIso_toProjectiveModification_restrict_opensRange
    {k : Type u} [CommRing k] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)} [IsProper f]
    (D : ChowGraphMonomorphismData f) :
    letI : IsOpenImmersion D.toOriginalOpen :=
      D.isOpenImmersion_toOriginalOpen
    letI : QuasiCompact D.toOriginalOpen :=
      D.quasiCompact_toOriginalOpen
    IsIso
      (D.toProjectiveModification.toOriginal ∣_
        D.toOriginalOpen.opensRange) := by
  letI : IsOpenImmersion D.toOriginalOpen :=
    D.isOpenImmersion_toOriginalOpen
  letI : QuasiCompact D.toOriginalOpen :=
    D.quasiCompact_toOriginalOpen
  change
    IsIso
      (projectiveGraphClosureToBase
          f D.dimension D.toOriginalOpen
            D.toProjective D.overBase ∣_
        D.toOriginalOpen.opensRange)
  exact
    isIso_projectiveGraphClosureToBase_restrict_opensRange
      f D.toOriginalOpen D.toProjective D.overBase

end ChowGraphMonomorphismData

/--
The canonical Chow modification of a proper scheme over a field is an
isomorphism over its specified common open.
-/
theorem isIso_projectiveModificationOfProperToField_restrict_commonOpen
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] :
    let P := projectiveModificationOfProperToField k f
    letI : IsOpenImmersion P.toOriginalOpen :=
      P.isOpenImmersion_toOriginalOpen
    IsIso
      (P.toOriginal ∣_ P.toOriginalOpen.opensRange) := by
  dsimp only
  letI : IsNoetherian X :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.isNoetherian_of_isProper_to_field f
  let c :=
    Chow.properCommonDenseRelativeAffineCoverData k f
  let D := c.toRationalProjectiveMapData
  have hmono :
      Mono
        (projectiveGraphClosureToProjective
          f D.dimension D.toOriginalOpen
            D.toProjective D.overBase) :=
    c.mono_graphClosureToProjective
  exact
    (D.toGraphMonomorphismData hmono).isIso_toProjectiveModification_restrict_opensRange

/--
For every module on the original proper scheme, the pullback--pushforward
unit along the canonical Chow modification is invertible after
restriction to the specified common open.
-/
theorem isIso_restrict_chowPullbackPushforward_unit
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (M : X.Modules) :
    let P := projectiveModificationOfProperToField k f
    letI : IsOpenImmersion P.toOriginalOpen :=
      P.isOpenImmersion_toOriginalOpen
    IsIso
      ((Scheme.Modules.restrictFunctor
          P.toOriginalOpen.opensRange.ι).map
        ((Scheme.Modules.pullbackPushforwardAdjunction
          P.toOriginal).unit.app M)) := by
  dsimp only
  let P := projectiveModificationOfProperToField k f
  letI : IsOpenImmersion P.toOriginalOpen :=
    P.isOpenImmersion_toOriginalOpen
  letI :
      IsIso
        (P.toOriginal ∣_ P.toOriginalOpen.opensRange) :=
    isIso_projectiveModificationOfProperToField_restrict_commonOpen
      k f
  exact
    Scheme.Modules.isIso_restrict_pullbackPushforward_unit_of_isIso_morphismRestrict
      P.toOriginal P.toOriginalOpen.opensRange M

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
