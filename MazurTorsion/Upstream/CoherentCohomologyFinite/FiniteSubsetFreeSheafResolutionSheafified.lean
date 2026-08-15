/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteSubsetFreeSheafResolutionExact
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverSheafResolution
import Mathlib.Topology.Sheaves.Abelian

/-!
# Sheafification of the ordered-cover resolution

The normalized ordered-cover resolution is objectwise exact as a
presheaf complex.  Sheafification of module-valued presheaves is exact,
so its image is a quasi-isomorphic complex of sheaves.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace


noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf

variable {R : Type u} [CommRing R]
variable {T : TopCat.{u}}
variable {ι : Type u} [Fintype ι] [LinearOrder ι]

/-- Module-valued sheafification on the opens of `T`. -/
abbrev moduleSheafification :
    ((Opens T)ᵒᵖ ⥤ ModuleCat.{u} R) ⥤
      ModuleSheaf (R := R) T :=
  presheafToSheaf
    (Opens.grothendieckTopology T) (ModuleCat.{u} R)

/-- The sheafified normalized ordered-cover complex. -/
noncomputable def sheafifiedOrderedCoverComplex
    (U : ι → Opens T) :
    ChainComplex (ModuleSheaf (R := R) T) ℕ :=
  ((moduleSheafification (R := R) (T := T)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj
      (orderedCoverNormalizedPresheafComplex (R := R) U)

/-- The sheafified support concentrated in degree zero. -/
noncomputable def sheafifiedOrderedCoverSupportSingleComplex
    (U : ι → Opens T) :
    ChainComplex (ModuleSheaf (R := R) T) ℕ :=
  ((moduleSheafification (R := R) (T := T)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj
      (orderedCoverSupportSingleComplex (R := R) U)

/-- Sheafification of the normalized ordered-cover augmentation. -/
noncomputable def sheafifiedOrderedCoverAugmentation
    (U : ι → Opens T) :
    sheafifiedOrderedCoverComplex (R := R) U ⟶
      sheafifiedOrderedCoverSupportSingleComplex (R := R) U :=
  ((moduleSheafification (R := R) (T := T)).mapHomologicalComplex
    (ComplexShape.down ℕ)).map
      (orderedCoverNormalizedPresheafAugmentation (R := R) U)

/-- Apply the module coproduct functor to the support-to-terminal map. -/
noncomputable def moduleSupportToTerminal
    (U : ι → Opens T) :
    orderedCoverSupportModulePresheaf (R := R) U ⟶
      MazurTorsion.AlgebraicGeometry.CoherentCohomology.OpenCoverSheafResolution.terminalTypePresheaf
          (T := T) ⋙ sigmaConst.obj (ModuleCat.of R R) :=
  Functor.whiskerRight
    (MazurTorsion.AlgebraicGeometry.CoherentCohomology.OpenCoverSheafResolution.supportToTerminal U)
    (sigmaConst.obj (ModuleCat.of R R))

/-- If `U` covers the whole space, its sheafified support module is the
constant rank-one module sheaf. -/
noncomputable def sheafifiedOrderedCoverSupportIsoConstant
    (U : ι → Opens T) (hU : ⨆ i, U i = ⊤) :
    (moduleSheafification (R := R) (T := T)).obj
        (orderedCoverSupportModulePresheaf (R := R) U) ≅
      constantRankOneSheaf (R := R) T := by
  let J := Opens.grothendieckTopology T
  let supportMap :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.OpenCoverSheafResolution.supportToTerminal U
  letI : Presheaf.IsLocallyInjective J supportMap :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.OpenCoverSheafResolution.supportToTerminal_isLocallyInjective U
  letI : Presheaf.IsLocallySurjective J supportMap :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.OpenCoverSheafResolution.supportToTerminal_isLocallySurjective U hU
  have hW : J.W supportMap :=
    J.W_of_isLocallyBijective supportMap
  letI : J.PreservesSheafification
      (sigmaConst.obj (ModuleCat.of R R)) :=
    CategoryTheory.Sheaf.preservesSheafification_of_adjunction
      J (sigmaConstAdj (ModuleCat.of R R))
  have hWmodule :
      J.W (moduleSupportToTerminal (R := R) U) :=
    J.W_of_preservesSheafification
      (sigmaConst.obj (ModuleCat.of R R)) supportMap hW
  haveI :
      IsIso ((moduleSheafification (R := R) (T := T)).map
        (moduleSupportToTerminal (R := R) U)) :=
    (J.W_iff (moduleSupportToTerminal (R := R) U)).mp hWmodule
  exact
    asIso ((moduleSheafification (R := R) (T := T)).map
      (moduleSupportToTerminal (R := R) U)) ≪≫
      (moduleSheafification (R := R) (T := T)).mapIso
        (Functor.constComp (Opens T)ᵒᵖ
          (ULift.{u} PUnit)
          (sigmaConst.obj (ModuleCat.of R R))) ≪≫
      (moduleSheafification (R := R) (T := T)).mapIso
        ((Functor.const (Opens T)ᵒᵖ).mapIso
          (coproductUniqueIso
            (fun _ : ULift.{u} PUnit => ModuleCat.of R R)))

/-- For a covering family, compose the sheafified support augmentation
with the canonical identification of the support with the constant
rank-one sheaf. -/
noncomputable def sheafifiedOrderedCoverAugmentationToConstant
    (U : ι → Opens T) (hU : ⨆ i, U i = ⊤) :
    sheafifiedOrderedCoverComplex (R := R) U ⟶
      (ChainComplex.single₀ (ModuleSheaf (R := R) T)).obj
        (constantRankOneSheaf (R := R) T) :=
  sheafifiedOrderedCoverAugmentation (R := R) U ≫
    ((moduleSheafification (R := R) (T := T)).mapHomologicalComplex
      (ComplexShape.down ℕ)).map
        (orderedCoverSupportSingleComplexIso (R := R) U).hom ≫
    ((HomologicalComplex.singleMapHomologicalComplex
      (moduleSheafification (R := R) (T := T))
      (ComplexShape.down ℕ) 0).app
        (orderedCoverSupportModulePresheaf (R := R) U)).hom ≫
    (ChainComplex.single₀ (ModuleSheaf (R := R) T)).map
      (sheafifiedOrderedCoverSupportIsoConstant
        (R := R) U hU).hom

/-- Exact sheafification preserves the ordered-cover
quasi-isomorphism. -/
theorem sheafifiedOrderedCoverAugmentation_quasiIso
    (U : ι → Opens T) :
    QuasiIso (sheafifiedOrderedCoverAugmentation (R := R) U) := by
  letI :
      (moduleSheafification (R := R) (T := T)).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels
      (moduleSheafification (R := R) (T := T))
  letI : QuasiIso
      (orderedCoverNormalizedPresheafAugmentation (R := R) U) :=
    orderedCoverNormalizedPresheafAugmentation_quasiIso
      (R := R) U
  exact HomologicalComplex.quasiIso_map_of_preservesHomology
    (orderedCoverNormalizedPresheafAugmentation (R := R) U)
    (moduleSheafification (R := R) (T := T))

/-- The sheafified ordered-cover complex resolves the constant
rank-one sheaf. -/
theorem sheafifiedOrderedCoverAugmentationToConstant_quasiIso
    (U : ι → Opens T) (hU : ⨆ i, U i = ⊤) :
    QuasiIso
      (sheafifiedOrderedCoverAugmentationToConstant
        (R := R) U hU) := by
  let h₁ : QuasiIso
      (sheafifiedOrderedCoverAugmentation (R := R) U) :=
    sheafifiedOrderedCoverAugmentation_quasiIso (R := R) U
  let h₂ : QuasiIso
      (((moduleSheafification (R := R) (T := T)).mapHomologicalComplex
        (ComplexShape.down ℕ)).map
          (orderedCoverSupportSingleComplexIso (R := R) U).hom) :=
    inferInstance
  let h₃ : QuasiIso
      (((HomologicalComplex.singleMapHomologicalComplex
        (moduleSheafification (R := R) (T := T))
        (ComplexShape.down ℕ) 0).app
          (orderedCoverSupportModulePresheaf (R := R) U)).hom) :=
    inferInstance
  let h₄ : QuasiIso
      ((ChainComplex.single₀ (ModuleSheaf (R := R) T)).map
        (sheafifiedOrderedCoverSupportIsoConstant
          (R := R) U hU).hom) :=
    inferInstance
  dsimp [sheafifiedOrderedCoverAugmentationToConstant]
  exact quasiIso_comp _ _
    (hφ := h₁)
    (hφ' := quasiIso_comp _ _ (hφ := h₂)
      (hφ' := quasiIso_comp _ _ (hφ := h₃) (hφ' := h₄)))

/-- Positive-degree exactness of the sheafified ordered-cover
resolution. -/
theorem sheafifiedOrderedCoverComplex_exactAt_succ
    (U : ι → Opens T) (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    (sheafifiedOrderedCoverComplex (R := R) U).ExactAt (n + 1) := by
  letI : QuasiIso
      (sheafifiedOrderedCoverAugmentationToConstant
        (R := R) U hU) :=
    sheafifiedOrderedCoverAugmentationToConstant_quasiIso
      (R := R) U hU
  exact ChainComplex.exactAtSuccOfQuasiIsoToSingle
    (sheafifiedOrderedCoverAugmentationToConstant
      (R := R) U hU) n

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf
