/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

Adapted from the Apache-licensed `CanonicalSupportThickening.lean` in
Vilin97/Clawristotle.
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.FiniteSupportIdealSheafPullbackUnit

/-!
# Canonical closed thickenings of scheme-module support

For a finite-type quasicoherent module on a Noetherian scheme, a positive
power of the vanishing ideal of its closed stalk support annihilates the
module scheme-theoretically. This file packages the resulting closed
thickening and the pullback-pushforward comparison isomorphism.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A positive power of the vanishing ideal of `F` whose associated
closed subscheme recovers `F` by pullback followed by pushforward. -/
structure CanonicalSupportThickening {X : Scheme.{u}} (F : X.Modules) where
  exponent : ℕ
  unitIsIso :
    IsIso
      ((pullbackPushforwardAdjunction
        (((Scheme.IdealSheafData.vanishingIdeal
          (closedStalkSupport F)) ^ (exponent + 1)).subschemeι)).unit.app F)

namespace CanonicalSupportThickening

variable {X : Scheme.{u}} {F : X.Modules}

/-- The positive power of the vanishing ideal defining the thickening. -/
def idealSheaf (A : CanonicalSupportThickening F) : X.IdealSheafData :=
  (Scheme.IdealSheafData.vanishingIdeal (closedStalkSupport F)) ^
    (A.exponent + 1)

/-- The canonical closed support thickening. -/
abbrev supportScheme (A : CanonicalSupportThickening F) : Scheme.{u} :=
  A.idealSheaf.subscheme

/-- The canonical closed immersion of the support thickening. -/
def inclusion (A : CanonicalSupportThickening F) : A.supportScheme ⟶ X :=
  A.idealSheaf.subschemeι

/-- The pullback of the original module to its support thickening. -/
def modelModule (A : CanonicalSupportThickening F) : A.supportScheme.Modules :=
  (pullback A.inclusion).obj F

instance inclusion_isClosedImmersion (A : CanonicalSupportThickening F) :
    IsClosedImmersion A.inclusion := by
  change IsClosedImmersion A.idealSheaf.subschemeι
  infer_instance

instance unit_isIso (A : CanonicalSupportThickening F) :
    IsIso ((pullbackPushforwardAdjunction A.inclusion).unit.app F) := by
  change
    IsIso
      ((pullbackPushforwardAdjunction
        (((Scheme.IdealSheafData.vanishingIdeal
          (closedStalkSupport F)) ^ (A.exponent + 1)).subschemeι)).unit.app F)
  exact A.unitIsIso

/-- The original module is the pushforward of its canonical model. -/
def comparisonIso (A : CanonicalSupportThickening F) :
    F ≅ (pushforward A.inclusion).obj A.modelModule := by
  change F ≅ (pushforward A.inclusion).obj ((pullback A.inclusion).obj F)
  exact asIso ((pullbackPushforwardAdjunction A.inclusion).unit.app F)

/-- The range of the support thickening is the closed stalk support of
the original module. -/
theorem range_inclusion (A : CanonicalSupportThickening F) :
    Set.range A.inclusion = (closedStalkSupport F : Set X) := by
  change
    Set.range
        (((Scheme.IdealSheafData.vanishingIdeal
          (closedStalkSupport F)) ^ (A.exponent + 1)).subschemeι) =
      _
  rw [Scheme.IdealSheafData.range_positivePower_subschemeι]
  exact Scheme.IdealSheafData.coe_support_vanishingIdeal
    (closedStalkSupport F)

/-- Every finite-type quasicoherent module on a Noetherian scheme admits
its canonical support thickening. -/
theorem nonempty [IsNoetherian X]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] :
    Nonempty (CanonicalSupportThickening F) := by
  obtain ⟨n, hn⟩ :=
    exists_positivePower_isIso_pullbackPushforward_unit F
      (Scheme.IdealSheafData.vanishingIdeal (closedStalkSupport F))
      (by
        intro x hx
        change x ∈
          ((Scheme.IdealSheafData.vanishingIdeal
            (closedStalkSupport F)).support : Set X)
        rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
        exact hx)
  exact ⟨⟨n, hn⟩⟩

/-- A chosen canonical support thickening. -/
def ofFiniteType [IsNoetherian X]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] :
    CanonicalSupportThickening F :=
  Classical.choice (nonempty F)

end CanonicalSupportThickening
end AlgebraicGeometry.Scheme.Modules
