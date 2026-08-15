/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ChainResolutionFromQuasiIso
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverCoversTop
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverNerve
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafTerminalCohomology
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Topology.Sheaves.Abelian

/-!
# The sheafified open-cover nerve

The objectwise-contractible free-abelian nerve of an open family resolves
its support presheaf.  If the family covers the whole space, the
sheafification of that support is the constant free-abelian sheaf on one
generator.  Since abelian sheafification is exact, sheafifying the nerve
therefore gives a chain resolution of the constant sheaf.
-/

open CategoryTheory Limits Opposite TopologicalSpace

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.OpenCoverSheafResolution

variable {T : TopCat.{u}} {ι : Type u}

abbrev opensTopology (T : TopCat.{u}) :=
  Opens.grothendieckTopology T

/-- The terminal type-valued presheaf on the opens of `T`. -/
def terminalTypePresheaf :
    (Opens T)ᵒᵖ ⥤ Type u :=
  (Functor.const (Opens T)ᵒᵖ).obj (ULift.{u} PUnit)

/-- Forget the proof that an open lies in a member of the family. -/
def supportToTerminal (U : ι → Opens T) :
    OpenCoverNerve.supportPresheaf U ⟶ terminalTypePresheaf :=
  { app := fun _ => ↾fun x => x.1 }

/-- The support-to-terminal map is objectwise injective. -/
theorem supportToTerminal_isLocallyInjective
    (U : ι → Opens T) :
    Presheaf.IsLocallyInjective (opensTopology T)
      (supportToTerminal U) :=
  Presheaf.isLocallyInjective_of_injective
    (opensTopology T) (supportToTerminal U) fun _ x y h =>
      Subtype.ext h

/-- If the open family covers `T`, every terminal section locally lifts
to the support presheaf. -/
theorem supportToTerminal_isLocallySurjective
    (U : ι → Opens T) (hU : ⨆ i, U i = ⊤) :
    Presheaf.IsLocallySurjective (opensTopology T)
      (supportToTerminal U) := by
  constructor
  intro V s x hx
  have hxTop : x ∈ (⊤ : Opens T) := trivial
  rw [← hU, Opens.mem_iSup] at hxTop
  obtain ⟨i, hxi⟩ := hxTop
  refine ⟨V ⊓ U i, homOfLE inf_le_left, ?_, hx, hxi⟩
  refine ⟨⟨ULift.up PUnit.unit, ⟨⟨i, inf_le_right⟩⟩⟩, ?_⟩
  rfl

/-- Apply the free-abelian-group functor to the support-to-terminal map. -/
def freeAbelianSupportToTerminal (U : ι → Opens T) :
    (OpenCoverNerve.supportPresheaf U ⋙ AddCommGrpCat.free) ⟶
      (terminalTypePresheaf ⋙ AddCommGrpCat.free) :=
  Functor.whiskerRight (supportToTerminal U) AddCommGrpCat.free

/-- For a covering family, free abelian support becomes isomorphic to
the constant free-abelian sheaf after sheafification. -/
noncomputable def supportFreeSheafIsoConstant
    (U : ι → Opens T) (hU : ⨆ i, U i = ⊤) :
    (presheafToSheaf (opensTopology T) AddCommGrpCat.{u}).obj
        (OpenCoverNerve.supportPresheaf U ⋙ AddCommGrpCat.free) ≅
      (constantSheaf (opensTopology T) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) := by
  letI : Presheaf.IsLocallyInjective (opensTopology T)
      (supportToTerminal U) :=
    supportToTerminal_isLocallyInjective U
  letI : Presheaf.IsLocallySurjective (opensTopology T)
      (supportToTerminal U) :=
    supportToTerminal_isLocallySurjective U hU
  have hW :
      (opensTopology T).W (supportToTerminal U) :=
    (opensTopology T).W_of_isLocallyBijective
      (supportToTerminal U)
  letI :
      (opensTopology T).PreservesSheafification
        AddCommGrpCat.free :=
    CategoryTheory.Sheaf.preservesSheafification_of_adjunction
      (opensTopology T) AddCommGrpCat.adj
  have hWfree :
      (opensTopology T).W (freeAbelianSupportToTerminal U) :=
    (opensTopology T).W_of_preservesSheafification
      AddCommGrpCat.free (supportToTerminal U) hW
  haveI :
      IsIso ((presheafToSheaf (opensTopology T) AddCommGrpCat.{u}).map
        (freeAbelianSupportToTerminal U)) :=
    ((opensTopology T).W_iff (freeAbelianSupportToTerminal U)).mp hWfree
  exact
    asIso ((presheafToSheaf (opensTopology T) AddCommGrpCat.{u}).map
      (freeAbelianSupportToTerminal U)) ≪≫
      (presheafToSheaf (opensTopology T) AddCommGrpCat.{u}).mapIso
        (Functor.constComp (Opens T)ᵒᵖ
          (ULift.{u} PUnit) AddCommGrpCat.free) ≪≫
      (presheafToSheaf (opensTopology T) AddCommGrpCat.{u}).mapIso
        ((Functor.const (Opens T)ᵒᵖ).mapIso
          (AddCommGrpCat.free.mapIso
              (Equiv.ulift.toIso :
                ULift.{u} PUnit ≅ PUnit) ≪≫
            CategoryTheory.Sheaf.freePUnitIsoULiftZ))

/-- Sheafify the free-abelian alternating chain complex of the open-cover
nerve degreewise. -/
noncomputable def sheafifiedFreeAbelianCechComplex
    (U : ι → Opens T) :
    ChainComplex
      (Sheaf (opensTopology T) AddCommGrpCat.{u}) ℕ :=
  ((presheafToSheaf (opensTopology T) AddCommGrpCat.{u}).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj
      (AlgebraicTopology.AlternatingFaceMapComplex.obj
        (OpenCoverNerve.freeAbelianAugmentedNerve U).left)

/-- The sheafified augmentation, with target the constant free-abelian
sheaf on one generator. -/
noncomputable def sheafifiedFreeAbelianAugmentation
    (U : ι → Opens T) (hU : ⨆ i, U i = ⊤) :
    sheafifiedFreeAbelianCechComplex U ⟶
      (ChainComplex.single₀
        (Sheaf (opensTopology T) AddCommGrpCat.{u})).obj
          ((constantSheaf (opensTopology T) AddCommGrpCat.{u}).obj
            (AddCommGrpCat.of (ULift.{u} ℤ))) :=
  ((presheafToSheaf (opensTopology T) AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.down ℕ)).map
        (OpenCoverNerve.freeAbelianAugmentation U) ≫
    ((HomologicalComplex.singleMapHomologicalComplex
      (presheafToSheaf (opensTopology T) AddCommGrpCat.{u})
      (ComplexShape.down ℕ) 0).app
        (OpenCoverNerve.freeAbelianAugmentedNerve U).right).hom ≫
    (ChainComplex.single₀
      (Sheaf (opensTopology T) AddCommGrpCat.{u})).map
        (supportFreeSheafIsoConstant U hU).hom

/-- The sheafified free-abelian Čech augmentation is a
quasi-isomorphism. -/
theorem sheafifiedFreeAbelianAugmentation_quasiIso
    (U : ι → Opens T) (hU : ⨆ i, U i = ⊤) :
    QuasiIso (sheafifiedFreeAbelianAugmentation U hU) := by
  haveI :
      QuasiIso (OpenCoverNerve.freeAbelianAugmentation U) :=
    OpenCoverNerve.freeAbelianAugmentation_quasiIso U
  let m₁ :=
    ((presheafToSheaf
          (opensTopology T) AddCommGrpCat.{u}).mapHomologicalComplex
            (ComplexShape.down ℕ)).map
              (OpenCoverNerve.freeAbelianAugmentation U)
  let m₂ :=
    ((HomologicalComplex.singleMapHomologicalComplex
          (presheafToSheaf
            (opensTopology T) AddCommGrpCat.{u})
          (ComplexShape.down ℕ) 0).app
            (OpenCoverNerve.freeAbelianAugmentedNerve U).right).hom
  let m₃ :=
    (ChainComplex.single₀
          (Sheaf (opensTopology T) AddCommGrpCat.{u})).map
            (supportFreeSheafIsoConstant U hU).hom
  haveI hmap : QuasiIso m₁ := inferInstance
  haveI hsingle : QuasiIso m₂ := inferInstance
  haveI htarget : QuasiIso m₃ := inferInstance
  dsimp only [sheafifiedFreeAbelianAugmentation]
  change QuasiIso (m₁ ≫ m₂ ≫ m₃)
  let h₂₃ : QuasiIso (m₂ ≫ m₃) :=
    quasiIso_comp (hφ := hsingle) (hφ' := htarget) m₂ m₃
  exact quasiIso_comp (hφ := hmap) (hφ' := h₂₃) m₁ (m₂ ≫ m₃)

/-- The zeroth opcycles of the sheafified Čech complex are the constant
free-abelian sheaf. -/
noncomputable def sheafifiedFreeAbelianCechOpcyclesZeroIso
    (U : ι → Opens T) (hU : ⨆ i, U i = ⊤) :
    (sheafifiedFreeAbelianCechComplex U).opcycles 0 ≅
      (constantSheaf (opensTopology T) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) := by
  letI :
      QuasiIso (sheafifiedFreeAbelianAugmentation U hU) :=
    sheafifiedFreeAbelianAugmentation_quasiIso U hU
  exact
    ChainComplex.opcyclesZeroIsoOfQuasiIsoToSingle
      (sheafifiedFreeAbelianAugmentation U hU)

/-- The sheafified Čech complex is exact in all positive degrees. -/
theorem sheafifiedFreeAbelianCechExactAtSucc
    (U : ι → Opens T) (hU : ⨆ i, U i = ⊤)
    (n : ℕ) :
    (sheafifiedFreeAbelianCechComplex U).ExactAt (n + 1) := by
  letI :
      QuasiIso (sheafifiedFreeAbelianAugmentation U hU) :=
    sheafifiedFreeAbelianAugmentation_quasiIso U hU
  exact
    ChainComplex.exactAtSuccOfQuasiIsoToSingle
      (sheafifiedFreeAbelianAugmentation U hU) n

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.OpenCoverSheafResolution
