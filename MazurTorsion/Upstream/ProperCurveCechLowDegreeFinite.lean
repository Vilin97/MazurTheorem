/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleOrderedBaseCechHomologyRetract
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

open CategoryTheory TopologicalSpace
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules

namespace MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

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
  letI : M.IsFiniteType :=
    { exists_localGeneratorsData :=
        ⟨G.localGeneratorsData, hGlocal⟩ }
  letI : M.IsQuasicoherent := inferInstance
  exact
    orderedBaseCechLowDegreeFinite_of_rationalSection_of_globalSections_module_finite
      K X f s M U hU hUaff
        (Scheme.Modules.free_globalSections_module_finite X J)

end MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology
