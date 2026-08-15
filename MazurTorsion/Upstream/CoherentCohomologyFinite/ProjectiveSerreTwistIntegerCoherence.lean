/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistInteger
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafFiniteFreePresentation
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafOverEquivalence

/-!
# Coherence of integer Serre twists

Every integer Serre twist is trivial on the finite standard affine cover.
Transporting the one-generator presentation of the unit module across those
trivializations proves finite presentation, hence finite type and
quasicoherence.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafFinitePresentation

variable (k : Type) [CommRing k] (d : ℕ)

/-- The pullback trivialization of an integer twist, expressed using
restriction to the corresponding standard open subscheme. -/
def integerRestrictionChartIso (m : ℤ)
    (i : Fin (d + 1)) :
    (OInt k d m).restrict (standardChart k i).ι ≅
      SheafOfModules.unit
        (standardChart k i).toScheme.ringCatSheaf :=
  (Scheme.Modules.restrictFunctorIsoPullback
      (standardChart k i).ι).app (OInt k d m) ≪≫
    integerChartIso k d m i

/-- Slice-site form of the standard-chart trivialization. -/
def integerOverChartIso (m : ℤ)
    (i : Fin (d + 1)) :
    (OInt k d m).over (standardChart k i) ≅
      SheafOfModules.unit
        ((scheme k d).ringCatSheaf.over
          (standardChart k i)) :=
  Scheme.Modules.chartOverIso (standardChart k i)
    (OInt k d m) (integerRestrictionChartIso k d m i)

/-- The finite one-generator presentation of an integer twist on a standard
chart. -/
def integerChartPresentation (m : ℤ)
    (i : Fin (d + 1)) :
    ((OInt k d m).over
      (standardChart k i)).Presentation :=
  SheafOfModules.Presentation.ofIsIso
    (integerOverChartIso k d m i).inv
    (unitPresentation
      ((scheme k d).ringCatSheaf.over
        (standardChart k i)))

instance integerChartPresentation_isFinite (m : ℤ)
    (i : Fin (d + 1)) :
    (integerChartPresentation k d m i).IsFinite := by
  dsimp only [integerChartPresentation]
  infer_instance

/-- Finite-presentation data for an integer twist on the standard affine
cover. -/
def integerQuasicoherentData (m : ℤ) :
    (OInt k d m).QuasicoherentData where
  I := Fin (d + 1)
  X := standardChart k
  coversTop := by
    intro W x hxW
    have hx :
        x ∈ ⨆ i : Fin (d + 1), standardChart k i := by
      rw [iSup_standardChart k d]
      trivial
    rw [Opens.mem_iSup] at hx
    obtain ⟨i, hi⟩ := hx
    exact
      ⟨standardChart k i ⊓ W, homOfLE inf_le_right,
        ⟨i, ⟨homOfLE inf_le_left⟩⟩, hi, hxW⟩
  presentation i := integerChartPresentation k d m i

/-- Every integer Serre twist is finitely presented. -/
instance integerModule_isFinitePresentation (m : ℤ) :
    (OInt k d m).IsFinitePresentation where
  exists_quasicoherentData :=
    ⟨integerQuasicoherentData k d m, by
      apply
        SheafOfModules.QuasicoherentData.IsFinitePresentation.mk
      intro i
      exact integerChartPresentation_isFinite k d m i⟩

/-- Every integer Serre twist is of finite type. -/
theorem OInt_isFiniteType (m : ℤ) :
    (OInt k d m).IsFiniteType := by
  letI : (OInt k d m).IsFinitePresentation :=
    integerModule_isFinitePresentation k d m
  exact SheafOfModules.instIsFiniteTypeOfIsFinitePresentation
    (OInt k d m)

/-- Every integer Serre twist is quasicoherent. -/
theorem OInt_isQuasicoherent (m : ℤ) :
    (OInt k d m).IsQuasicoherent := by
  letI : (OInt k d m).IsFinitePresentation :=
    integerModule_isFinitePresentation k d m
  exact SheafOfModules.instIsQuasicoherentOfIsFinitePresentation
    (OInt k d m)

/-- Every negative Serre twist is finitely presented. -/
theorem ONeg_isFinitePresentation (n : ℕ) :
    (ONeg k d n).IsFinitePresentation := by
  exact integerModule_isFinitePresentation k d (-(n : ℤ))

/-- Every negative Serre twist is of finite type. -/
theorem ONeg_isFiniteType (n : ℕ) :
    (ONeg k d n).IsFiniteType := by
  letI : (ONeg k d n).IsFinitePresentation :=
    integerModule_isFinitePresentation k d (-(n : ℤ))
  exact SheafOfModules.instIsFiniteTypeOfIsFinitePresentation
    (ONeg k d n)

/-- Every negative Serre twist is quasicoherent. -/
theorem ONeg_isQuasicoherent (n : ℕ) :
    (ONeg k d n).IsQuasicoherent := by
  letI : (ONeg k d n).IsFinitePresentation :=
    integerModule_isFinitePresentation k d (-(n : ℤ))
  exact SheafOfModules.instIsQuasicoherentOfIsFinitePresentation
    (ONeg k d n)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
