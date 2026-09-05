/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleOrderedBaseCechHomologyRetract
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleComparisonCoherent
import MazurTorsion.Upstream.ProperHZeroFinite
import MazurTorsion.Upstream.SchemeModuleBaseCechHOneComparison

/-!
# Low-degree Cech finiteness on a pointed proper curve

This file turns genuine cohomology finiteness back into ordered Cech
finiteness.  Its design boundary is an explicit finiteness proof for global
sections over the source global-function ring; degree zero uses that input,
while degree one uses the finite map to `P¹` supplied by a rational section.

The named downstream consumer is a finite free sheaf.  It provides the
low-degree-good target required by the future support-decreasing coherent
comodel construction.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules

namespace MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

private theorem free_isFiniteType
    (X : Scheme.{u}) (J : Type u) [Finite J] :
    (SheafOfModules.free J (R := X.ringCatSheaf)).IsFiniteType := by
  let G := SheafOfModules.free.generatingSections
    (R := X.ringCatSheaf) J
  letI : G.IsFiniteType := by
    constructor
    change Finite J
    infer_instance
  have hGlocal : G.localGeneratorsData.IsFiniteType := by
    constructor
    intro i
    constructor
    change Finite J
    infer_instance
  exact
    { exists_localGeneratorsData :=
        ⟨G.localGeneratorsData, hGlocal⟩ }

/-- On a pointed smooth proper integral curve, a coherent sheaf with finite
global sections over the global-function ring has finite ordered base-Cech
homology in degrees zero and one for every linearly ordered affine cover. -/
theorem orderedBaseCechLowDegreeFinite_of_rationalSection_of_globalSections_module_finite
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (s : SmoothCurveRationalSection K X f)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    {I : Type u} [LinearOrder I] (U : I → X.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (hM : Module.Finite Γ(X, ⊤) Γ(M, ⊤)) :
    OrderedBaseCechLowDegreeFinite f U M := by
  constructor
  · letI : Module Γ(Spec (.of K), ⊤) (H M 0) :=
      baseSectionsHZeroModule f M
    letI : Module.Finite Γ(Spec (.of K), ⊤) (H M 0) :=
      hZeroBaseSections_finite_of_globalSections_module_finite f M
        (finite_appTop_of_universallyClosed K f) hM
    letI : Module.Finite Γ(Spec (.of K), ⊤)
        ((baseCechComplex f M U).homology 0) :=
      Module.Finite.equiv
        (nativeBaseCechHZeroLinearEquivCanonicalOfOpenCover
          f M U hU).symm
    exact orderedBaseCechComplex_homology_module_finite_of_baseCechComplex
      f M U 0
  · letI : Module Γ(Spec (.of K), ⊤) (H M 1) :=
      baseSectionsHOneModule f M
    letI : Module.Finite Γ(Spec (.of K), ⊤) (H M 1) :=
      genuineSheafHOneCanonicalBase_finite_of_rationalSection K X f s M
    letI : Module.Finite Γ(Spec (.of K), ⊤)
        ((baseCechComplex f M U).homology 1) :=
      Module.Finite.equiv
        (nativeBaseCechHOneLinearEquivCanonicalOfAffineOpenCover
          f M U hU hUaff).symm
    exact orderedBaseCechComplex_homology_module_finite_of_baseCechComplex
      f M U 1

/-- On a pointed proper curve, an open-local comparison to a coherent sheaf
with finite global sections supplies the exact support comodel consumed by
closed-support codévissage. -/
theorem isCoherentLowDegreeSupportComodel_of_rationalSection_of_globalSections_module_finite
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (s : SmoothCurveRationalSection K X f)
    {I : Type u} [LinearOrder I] (U : I → X.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    {M E : X.Modules} [M.IsFiniteType] [M.IsQuasicoherent]
    [E.IsFiniteType] [E.IsQuasicoherent]
    (g : M ⟶ E) {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    [IsIso ((restrictFunctor j).map g)]
    (hEM : closedStalkSupport E ≤ closedStalkSupport M)
    (x : Y) (hxM : j x ∈ closedStalkSupport M)
    (hE : Module.Finite Γ(X, ⊤) Γ(E, ⊤)) :
    IsCoherentLowDegreeSupportComodel f U M E g := by
  letI : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian f
  exact
    IsCoherentLowDegreeSupportComodel.of_isIso_restrict f U
      (orderedBaseCechLowDegreeFinite_of_rationalSection_of_globalSections_module_finite
        K X f s E U hU hUaff hE)
      g j hEM x hxM

/-- Finite free sheaves have finite ordered base-Cech homology in degrees
zero and one on a pointed smooth proper integral curve.  This is the first
low-degree-good comodel target. -/
theorem free_orderedBaseCechLowDegreeFinite_of_rationalSection
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (s : SmoothCurveRationalSection K X f)
    (J : Type u) [Finite J]
    {I : Type u} [LinearOrder I] (U : I → X.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i)) :
    OrderedBaseCechLowDegreeFinite f U
      (SheafOfModules.free J (R := X.ringCatSheaf)) := by
  let M : X.Modules := SheafOfModules.free J
  letI : M.IsFiniteType := free_isFiniteType X J
  letI : M.IsQuasicoherent := inferInstance
  exact
    orderedBaseCechLowDegreeFinite_of_rationalSection_of_globalSections_module_finite
      K X f s M U hU hUaff
        (Scheme.Modules.free_globalSections_module_finite X J)

/-- A comparison to a finite free sheaf which is invertible on a
support-meeting open and does not enlarge support is a coherent low-degree
support comodel.  This is the concrete finite-free comparison boundary left
for the proper-curve producer. -/
theorem finiteFreeTarget_isCoherentLowDegreeSupportComodel_of_isIso_restrict
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (s : SmoothCurveRationalSection K X f)
    {I : Type u} [LinearOrder I] (U : I → X.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent]
    (J : Type u) [Finite J]
    (g : M ⟶ SheafOfModules.free J)
    {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    [IsIso ((restrictFunctor j).map g)]
    (hEM : closedStalkSupport (SheafOfModules.free J) ≤
      closedStalkSupport M)
    (x : Y) (hxM : j x ∈ closedStalkSupport M) :
    IsCoherentLowDegreeSupportComodel f U M
      (SheafOfModules.free J) g := by
  let E : X.Modules := SheafOfModules.free J
  letI : E.IsFiniteType := free_isFiniteType X J
  letI : E.IsQuasicoherent := inferInstance
  exact
    isCoherentLowDegreeSupportComodel_of_rationalSection_of_globalSections_module_finite
      K X f s U hU hUaff g j hEM x hxM
        (Scheme.Modules.free_globalSections_module_finite X J)

/-- A finite free sheaf is an actual coherent low-degree support comodel of
itself.  Both residuals are zero; this packages the finite-free target against
the exact interface consumed by closed-support codévissage. -/
theorem free_isCoherentLowDegreeSupportComodel_identity
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (s : SmoothCurveRationalSection K X f)
    (J : Type u) [Finite J]
    {I : Type u} [LinearOrder I] (U : I → X.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i)) :
    let M := SheafOfModules.free J (R := X.ringCatSheaf)
    IsCoherentLowDegreeSupportComodel f U M M (𝟙 M) := by
  let M : X.Modules := SheafOfModules.free J
  letI : M.IsFiniteType := free_isFiniteType X J
  letI : M.IsQuasicoherent := inferInstance
  letI : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian f
  have hresidual :=
    Scheme.Modules.comparisonResidual_isFiniteType_and_isQuasicoherent
      (𝟙 M)
  letI : (Abelian.image (𝟙 M)).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_image (𝟙 M)
  have hfac :
      Abelian.factorThruImage (𝟙 M) ≫ Abelian.image.ι (𝟙 M) =
        𝟙 M :=
    Abelian.image.fac (𝟙 M)
  letI : Mono (Abelian.factorThruImage (𝟙 M)) :=
    mono_of_mono_fac hfac
  letI : Epi (Abelian.image.ι (𝟙 M)) :=
    epi_of_epi_fac hfac
  have hkernel : IsZero
      (kernel (Abelian.factorThruImage (𝟙 M))) :=
    isZero_kernel_of_mono _
  have hcokernel : IsZero
      (cokernel (Abelian.image.ι (𝟙 M))) :=
    isZero_cokernel_of_epi _
  exact
    ⟨inferInstance, inferInstance,
      free_orderedBaseCechLowDegreeFinite_of_rationalSection
        K X f s J U hU hUaff,
      inferInstance,
      hresidual.1.1, hresidual.1.2,
      hresidual.2.1, hresidual.2.2,
      Or.inl hkernel, Or.inl hcokernel⟩

end MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology
