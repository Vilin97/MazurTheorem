/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Christian Merten, Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# `IsStableUnderBaseChangeAlong` / `RespectsIso` for the standard morphism properties

**v4.33 bump compatibility.** Mathlib derives both

* `[P.IsStableUnderBaseChange] → P.IsStableUnderBaseChangeAlong f`
  (`CategoryTheory/MorphismProperty/Limits.lean`), and
* `[P.IsStableUnderBaseChange] → P.RespectsIso` (priority 900, same file),

but neither derivation fires by unification for the `AlgebraicGeometry` properties on this
pin, even with the relevant `IsStableUnderBaseChange` instance in scope — this was checked
in isolation for `@Surjective`. Supplying the instances at each concrete property makes them
fire; this file does that once so the ~20 affected call sites across `ModularCurves` need
only an import.

Delete this file when the derivations fire again upstream.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace ModularCurves.BumpCompat

instance stableAlong_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@Surjective) f :=
  ⟨fun pb hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩

instance stableAlong_flat {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@Flat) f :=
  ⟨fun pb hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩

instance stableAlong_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@IsFinite) f :=
  ⟨fun pb hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩

instance stableAlong_isProper {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@IsProper) f :=
  ⟨fun pb hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩

instance stableAlong_isClosedImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@IsClosedImmersion) f :=
  ⟨fun pb hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩

instance stableAlong_isSeparated {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@IsSeparated) f :=
  ⟨fun pb hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩

instance stableAlong_smoothOfRelativeDimension (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@SmoothOfRelativeDimension n) f :=
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange n
  ⟨fun pb hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩

instance respectsIso_isFinite : MorphismProperty.RespectsIso (@IsFinite) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

instance respectsIso_flat : MorphismProperty.RespectsIso (@Flat) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

instance respectsIso_isProper : MorphismProperty.RespectsIso (@IsProper) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

instance respectsIso_isClosedImmersion : MorphismProperty.RespectsIso (@IsClosedImmersion) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

/-- The affine-target property underlying `IsFinite`, kept named because the 4.33
instance synthesizer does not assign the anonymous function to the `outParam`. -/
def isFiniteAffineProperty : AffineTargetMorphismProperty :=
  fun X _ f _ ↦ IsAffine X ∧ RingHom.Finite (Scheme.Hom.appTop f).hom

instance hasAffineProperty_isFinite :
    HasAffineProperty (@IsFinite) isFiniteAffineProperty := by
  change HasAffineProperty @IsFinite (affineAnd RingHom.Finite)
  exact (HasAffineProperty.affineAnd_iff (@IsFinite) RingHom.finite_respectsIso
    RingHom.finite_localizationPreserves.away RingHom.finite_ofLocalizationSpan).mpr
      (fun f ↦ isFinite_iff f)

instance zariskiLocalAtTarget_isFinite : IsZariskiLocalAtTarget (@IsFinite) :=
  @HasAffineProperty.instIsZariskiLocalAtTarget (@IsFinite)
    isFiniteAffineProperty hasAffineProperty_isFinite

instance zariskiLocalAtTarget_etale : IsZariskiLocalAtTarget (@Etale) :=
  HasRingHomProperty.instIsZariskiLocalAtTarget @Etale

instance respectsIso_etale : MorphismProperty.RespectsIso (@Etale) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

instance zariskiLocalAtTarget_flat : IsZariskiLocalAtTarget (@Flat) :=
  HasRingHomProperty.instIsZariskiLocalAtTarget @Flat

instance respectsIso_formallyUnramified :
    MorphismProperty.RespectsIso (@FormallyUnramified) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

instance stableAlong_formallyUnramified {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@FormallyUnramified) f :=
  ⟨fun pb hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩

instance stableAlong_quasiCompact {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@QuasiCompact) f :=
  ⟨fun pb hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩

instance stableAlong_etale {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@Etale) f :=
  ⟨fun pb hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩

instance zariskiLocalAtSource_flat : IsZariskiLocalAtSource (@Flat) :=
  HasRingHomProperty.instIsZariskiLocalAtSource

instance zariskiLocalAtSource_locallyOfFinitePresentation :
    IsZariskiLocalAtSource (@LocallyOfFinitePresentation) :=
  HasRingHomProperty.instIsZariskiLocalAtSource

instance descendsAlong_etale_fppf :
    MorphismProperty.DescendsAlong (@Etale)
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) := by
  letI : MorphismProperty.IsStableUnderBaseChange (@Surjective ⊓ @Flat) :=
    MorphismProperty.IsStableUnderBaseChange.inf
  letI : MorphismProperty.IsStableUnderBaseChange
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
    MorphismProperty.IsStableUnderBaseChange.inf
  apply IsZariskiLocalAtTarget.descendsAlong
  rintro R X Y f g ⟨⟨h₁, h₂⟩, h₃⟩ H
  obtain ⟨V : X.Opens, hV, e⟩ := f.isOpenMap.exists_opens_image_eq_of_prespectralSpace
    f.continuous (by simp) isOpen_univ isCompact_univ
  refine MorphismProperty.of_isPullback_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (.paste_vert (.of_hasPullback V.ι _) (.of_hasPullback f g)) ⟨⟨?_, inferInstance⟩,
      (quasiCompact_iff_compactSpace _).mpr (isCompact_iff_compactSpace.mp hV)⟩ ?_
  · exact ⟨fun x ↦ have ⟨y, hyV, ey⟩ := e.ge (Set.mem_univ x); ⟨⟨y, hyV⟩, ey⟩⟩
  · exact IsZariskiLocalAtTarget.of_isPullback (.flip <| .of_hasPullback _ _) H

instance zariskiLocalAtTarget_smoothOfRelativeDimension (n : ℕ) :
    IsZariskiLocalAtTarget (@SmoothOfRelativeDimension n) :=
  letI :=
    instHasRingHomPropertySmoothOfRelativeDimensionLocallyIsStandardSmoothOfRelativeDimension n
  HasRingHomProperty.instIsZariskiLocalAtTarget (@SmoothOfRelativeDimension n)

instance zariskiLocalAtTarget_isAffineHom : IsZariskiLocalAtTarget (@IsAffineHom) :=
  @HasAffineProperty.instIsZariskiLocalAtTarget (@IsAffineHom) (fun X _ _ _ ↦ IsAffine X)
    AlgebraicGeometry.instHasAffinePropertyIsAffineHomIsAffine

instance stableUnderComposition_etale :
    MorphismProperty.IsStableUnderComposition (@Etale) :=
  MorphismProperty.IsMultiplicative.toIsStableUnderComposition

end ModularCurves.BumpCompat
