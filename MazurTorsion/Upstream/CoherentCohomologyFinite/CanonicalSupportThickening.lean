/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteSupportIdealSheafPullbackUnit
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemePushforwardCohomology

/-!
# The canonical closed thickening of a module support

For a coherent module on a Noetherian scheme, take the vanishing ideal
sheaf of its closed stalk support.  A positive power of that ideal
annihilates the module scheme-theoretically.  Consequently the module is
canonically isomorphic to the pushforward of its pullback to the
corresponding closed thickening.

This file packages that unconditional reduction, including the exact
cohomology comparison across the closed immersion.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace TensorProduct

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

/--
The data of a positive power of the vanishing ideal of `F` for which the
canonical pullback--pushforward unit is invertible.
-/
structure CanonicalSupportThickening
    {X : Scheme.{0}} (F : X.Modules) where
  exponent : ℕ
  unitIsIso :
    IsIso
      ((Scheme.Modules.pullbackPushforwardAdjunction
        (((Scheme.IdealSheafData.vanishingIdeal
          (Scheme.Modules.closedStalkSupport F)) ^
            (exponent + 1)).subschemeι)).unit.app F)

namespace CanonicalSupportThickening

variable {X : Scheme.{0}} {F : X.Modules}

noncomputable local instance canonicalSupportCohomologyAddCommGroup
    {Z : TopCat.{0}}
    (G : TopCat.Sheaf AddCommGrpCat.{0} Z) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H G n) := by
  dsimp only [CategoryTheory.Sheaf.H]
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

/-- The positive power of the vanishing ideal defining the thickening. -/
def idealSheaf (A : CanonicalSupportThickening F) :
    X.IdealSheafData :=
  (Scheme.IdealSheafData.vanishingIdeal
    (Scheme.Modules.closedStalkSupport F)) ^
      (A.exponent + 1)

/-- The closed support thickening. -/
abbrev supportScheme (A : CanonicalSupportThickening F) :
    Scheme.{0} :=
  A.idealSheaf.subscheme

/-- Its canonical closed immersion into the ambient scheme. -/
def inclusion (A : CanonicalSupportThickening F) :
    A.supportScheme ⟶ X :=
  A.idealSheaf.subschemeι

/-- The canonical module on the closed support thickening. -/
def modelModule (A : CanonicalSupportThickening F) :
    A.supportScheme.Modules :=
  (Scheme.Modules.pullback A.inclusion).obj F

instance inclusion_isClosedImmersion
    (A : CanonicalSupportThickening F) :
    IsClosedImmersion A.inclusion :=
  by
    change IsClosedImmersion A.idealSheaf.subschemeι
    infer_instance

instance unit_isIso
    (A : CanonicalSupportThickening F) :
    IsIso
      ((Scheme.Modules.pullbackPushforwardAdjunction
        A.inclusion).unit.app F) := by
  change
    IsIso
      ((Scheme.Modules.pullbackPushforwardAdjunction
        (((Scheme.IdealSheafData.vanishingIdeal
          (Scheme.Modules.closedStalkSupport F)) ^
            (A.exponent + 1)).subschemeι)).unit.app F)
  exact A.unitIsIso

/--
The module is canonically the pushforward of its pullback to the closed
support thickening.
-/
noncomputable def comparisonIso
    (A : CanonicalSupportThickening F) :
    F ≅
      (Scheme.Modules.pushforward A.inclusion).obj
        A.modelModule := by
  change
    F ≅
      (Scheme.Modules.pushforward A.inclusion).obj
        ((Scheme.Modules.pullback A.inclusion).obj F)
  exact
    @asIso _ _ _ _
      ((Scheme.Modules.pullbackPushforwardAdjunction
        A.inclusion).unit.app F)
      (unit_isIso A)

/--
The underlying range of the thickening is exactly the closed stalk
support of the original module.
-/
theorem range_inclusion
    (A : CanonicalSupportThickening F) :
    Set.range A.inclusion =
      (Scheme.Modules.closedStalkSupport F : Set X) := by
  change
    Set.range
        (((Scheme.IdealSheafData.vanishingIdeal
          (Scheme.Modules.closedStalkSupport F)) ^
            (A.exponent + 1)).subschemeι) =
      _
  rw [Scheme.IdealSheafData.range_positivePower_subschemeι]
  exact
    Scheme.IdealSheafData.coe_support_vanishingIdeal
      (Scheme.Modules.closedStalkSupport F)

/--
Every finite-type quasicoherent module on a Noetherian scheme has a
canonical support thickening.
-/
theorem nonempty
    [IsNoetherian X]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] :
    Nonempty (CanonicalSupportThickening F) := by
  obtain ⟨n, hn⟩ :=
    Scheme.Modules.exists_positivePower_isIso_pullbackPushforward_unit
      F
      (Scheme.IdealSheafData.vanishingIdeal
        (Scheme.Modules.closedStalkSupport F))
      (by
        intro x hx
        change
          x ∈
            ((Scheme.IdealSheafData.vanishingIdeal
              (Scheme.Modules.closedStalkSupport F)).support : Set X)
        rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
        exact hx)
  exact ⟨⟨n, hn⟩⟩

/-- A chosen canonical support thickening. -/
def ofFiniteType
    [IsNoetherian X]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] :
    CanonicalSupportThickening F :=
  Classical.choice (nonempty F)

/--
Closed-immersion cohomology and the comparison isomorphism identify the
cohomology of the model module with that of the original module.
-/
noncomputable def cohomologyIso
    (A : CanonicalSupportThickening F) (n : ℕ) :
    AddCommGrpCat.of (A.modelModule.sheaf.H n) ≅
      AddCommGrpCat.of (F.sheaf.H n) :=
  MazurTorsion.AlgebraicGeometry.CoherentCohomology.closedImmersionPushforwardHIso
      A.inclusion A.modelModule n ≪≫
    ((sheafCohomologyFunctor X n).mapIso
      ((Scheme.Modules.toUnderlyingSheaf X).mapIso
        A.comparisonIso)).symm

/-- The induced rational linear equivalence on cohomology. -/
noncomputable def rationalizedCohomologyLinearEquiv
    (A : CanonicalSupportThickening F) (n : ℕ) :
  ℚ ⊗[ℤ] A.modelModule.sheaf.H n ≃ₗ[ℚ]
      ℚ ⊗[ℤ] F.sheaf.H n :=
  MazurTorsion.AlgebraicGeometry.CoherentCohomology.rationalizationMapAddEquiv
    (A.cohomologyIso n).addCommGroupIsoToAddEquiv

/--
Rationalized cohomology is finite for the original module exactly when
it is finite for its canonical module on the support thickening.
-/
theorem rationalizedCohomology_finite_iff
    (A : CanonicalSupportThickening F) (n : ℕ) :
    Module.Finite ℚ
        (ℚ ⊗[ℤ] A.modelModule.sheaf.H n) ↔
      Module.Finite ℚ
        (ℚ ⊗[ℤ] F.sheaf.H n) :=
  MazurTorsion.AlgebraicGeometry.CoherentCohomology.rationalization_finite_congr
    (A.cohomologyIso n).addCommGroupIsoToAddEquiv

end CanonicalSupportThickening

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
