/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.CanonicalSupportThickening
import MazurTorsion.Upstream.CoherentCohomologyFinite.ChowProjectiveModificationOpen

/-!
# Chow reduction on the canonical support thickening

A coherent module on a proper scheme is first recovered exactly from a
module on a canonical closed thickening of its support.  That thickening
is proper, so Chow's graph construction supplies a projective
modification of it.  On the common open of that modification, the
pullback--pushforward unit for the support module is invertible.

This is an unconditional bridge from the support-annihilation reduction
to the projective-modification open comparison.  It intentionally makes
no unsupported claim that arbitrary pullback preserves coherence.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology
namespace CanonicalSupportThickening

variable {k : Type} [Field k] {X : Scheme.{0}}
  {f : X ⟶ Spec (CommRingCat.of k)} [IsProper f]
  {F : X.Modules}

/-- The canonical closed support thickening remains proper over the
ground field. -/
theorem isProper_supportScheme_toField
    (A : CanonicalSupportThickening F) :
    IsProper (A.inclusion ≫ f) :=
  inferInstance

/--
The canonical Chow projective modification of the closed support
thickening.
-/
def chowModification
    (A : CanonicalSupportThickening F) :
    ProjectiveModification (A.inclusion ≫ f) :=
  projectiveModificationOfProperToField k (A.inclusion ≫ f)

/--
The Chow modification of the support thickening is an isomorphism over
its specified common open.
-/
theorem isIso_chowModification_restrict_commonOpen
    (A : CanonicalSupportThickening F) :
    let P := A.chowModification (k := k) (f := f)
    letI : IsOpenImmersion P.toOriginalOpen :=
      P.isOpenImmersion_toOriginalOpen
    IsIso
      (P.toOriginal ∣_ P.toOriginalOpen.opensRange) :=
  isIso_projectiveModificationOfProperToField_restrict_commonOpen
    k (A.inclusion ≫ f)

/--
For every module on the support thickening, the Chow
pullback--pushforward unit is invertible after restriction to the
canonical common open.
-/
theorem isIso_restrict_chowPullbackPushforward_unit
    (A : CanonicalSupportThickening F)
    (M : A.supportScheme.Modules) :
    let P := A.chowModification (k := k) (f := f)
    letI : IsOpenImmersion P.toOriginalOpen :=
      P.isOpenImmersion_toOriginalOpen
    IsIso
      ((Scheme.Modules.restrictFunctor
          P.toOriginalOpen.opensRange.ι).map
        ((Scheme.Modules.pullbackPushforwardAdjunction
          P.toOriginal).unit.app M)) :=
  MazurTorsion.AlgebraicGeometry.CoherentCohomology.isIso_restrict_chowPullbackPushforward_unit
    k (A.inclusion ≫ f) M

/--
In particular, the common-open unit comparison applies to the module
whose closed-immersion pushforward recovers `F`.
-/
theorem isIso_restrict_chowPullbackPushforward_unit_modelModule
    (A : CanonicalSupportThickening F) :
    let P := A.chowModification (k := k) (f := f)
    letI : IsOpenImmersion P.toOriginalOpen :=
      P.isOpenImmersion_toOriginalOpen
    IsIso
      ((Scheme.Modules.restrictFunctor
          P.toOriginalOpen.opensRange.ι).map
        ((Scheme.Modules.pullbackPushforwardAdjunction
          P.toOriginal).unit.app A.modelModule)) :=
  A.isIso_restrict_chowPullbackPushforward_unit A.modelModule

/--
For a finite-type quasicoherent module on a proper scheme over a field,
choose its canonical support thickening.  Properness supplies the
Noetherian hypothesis needed by the annihilation theorem.
-/
def ofProperToField
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] :
    CanonicalSupportThickening F := by
  letI : IsNoetherian X :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.isNoetherian_of_isProper_to_field f
  exact ofFiniteType F

/--
The projective modification obtained after the canonical support
reduction of a coherent module on a proper scheme.
-/
def chowModificationOfFiniteType
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] :
    ProjectiveModification
      ((ofProperToField (k := k) (f := f) F).inclusion ≫ f) :=
  (ofProperToField (k := k) (f := f) F).chowModification

/--
The exact cohomology comparison from the support module to the original
coherent module, accompanying the canonical Chow modification.
-/
noncomputable abbrev cohomologyIsoOfProperToField
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (n : ℕ) :=
  (ofProperToField (k := k) (f := f) F).cohomologyIso n

end CanonicalSupportThickening
end MazurTorsion.AlgebraicGeometry.CoherentCohomology
