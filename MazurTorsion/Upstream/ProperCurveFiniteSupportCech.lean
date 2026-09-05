/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Upstream.ProperCurveCechLowDegreeFinite
import MazurTorsion.Upstream.ProperCurveFiniteSupport
import MazurTorsion.Upstream.ProperHZeroFinite
import MazurTorsion.Upstream.SchemeModuleBaseCechHZeroFinite
import MazurTorsion.Upstream.SchemeModuleComparisonSupportEpi

/-!
# Cohomology of strict support on a proper curve

This file is the cohomological consumer of the finite canonical-support
model. It turns finite global sections for strict support into canonical
degree-zero finiteness and, on a pointed curve, ordered degree-zero and
degree-one Cech finiteness.

The design boundary remains strict support. The missing full-support
comparison producer must reduce support before the closed-support induction
can use these declarations for an arbitrary coherent module.

There is also a direct presentation boundary: a coherent map `E ⟶ M` whose
source has finite `H⁰` and whose cokernel has strict support already forces
finite `H⁰` of `M`.  Its named downstream consumer is the future geometric
extension of generic generators; unlike the comodel route, it needs no map
from `M` into a low-degree-good target.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules

namespace MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology
namespace CanonicalSupportThickening

/-- Canonical `H⁰` of a coherent strict-support module on a smooth proper
integral curve is finite-dimensional over the ground field. -/
theorem hZeroCanonical_finiteDimensional_of_closedStalkSupport_lt_top
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent]
    (A : CanonicalSupportThickening M)
    (hM : closedStalkSupport M < ⊤) :
    letI := hZeroCanonicalFieldModule K X f M
    FiniteDimensional K (H M 0) := by
  exact hZeroCanonical_finiteDimensional_of_globalSections_module_finite
    K X f M
      (globalSections_module_finite_of_closedStalkSupport_lt_top
        K X f M A hM)

/-- A coherent strict-support module on a pointed smooth proper integral
curve has finite ordered base-Cech homology in degrees zero and one for every
linearly ordered affine cover. -/
theorem orderedBaseCechLowDegreeFinite_of_rationalSection_of_closedStalkSupport_lt_top
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (s : SmoothCurveRationalSection K X f)
    (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent]
    (A : CanonicalSupportThickening M)
    (hM : closedStalkSupport M < ⊤)
    {I : Type u} [LinearOrder I] (U : I → X.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i)) :
    OrderedBaseCechLowDegreeFinite f U M := by
  exact
    orderedBaseCechLowDegreeFinite_of_rationalSection_of_globalSections_module_finite
      K X f s M U hU hUaff
        (globalSections_module_finite_of_closedStalkSupport_lt_top
          K X f M A hM)

end CanonicalSupportThickening

open CanonicalSupportThickening

/-- Let `E ⟶ M` be a morphism of coherent modules on a pointed smooth
proper integral curve.  If canonical `H⁰(E)` is finite-dimensional and the
cokernel of the image inclusion has strict support, then canonical `H⁰(M)`
is finite-dimensional.

The proof factors through the image.  The first short exact sequence uses
finite `H⁰(E)` and finite `H¹` of its coherent kernel; the second uses finite
`H⁰` of the image and the strict-support theorem for the coherent cokernel.
This is the direct consumer boundary for a future generically surjective
extension of finitely many generic generators. -/
theorem hZeroCanonical_finiteDimensional_of_strictCokernel
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (s : SmoothCurveRationalSection K X f)
    (E M : X.Modules) [E.IsFiniteType] [E.IsQuasicoherent]
    [M.IsFiniteType] [M.IsQuasicoherent]
    (g : E ⟶ M)
    (hE : letI := hZeroCanonicalFieldModule K X f E
      FiniteDimensional K (H E 0))
    (hQ : closedStalkSupport
        (cokernel (Abelian.image.ι g)) < ⊤) :
    letI := hZeroCanonicalFieldModule K X f M
    FiniteDimensional K (H M 0) := by
  letI : IsNoetherian X :=
    isNoetherian_of_proper_smoothRelativeDimension_one K X f
  let K₀ := kernel (Abelian.factorThruImage g)
  let I₀ := Abelian.image g
  let Q₀ := cokernel (Abelian.image.ι g)
  have hresidual :=
    Scheme.Modules.comparisonResidual_isFiniteType_and_isQuasicoherent g
  letI : K₀.IsFiniteType := by
    change (kernel (Abelian.factorThruImage g)).IsFiniteType
    exact hresidual.1.1
  letI : K₀.IsQuasicoherent := by
    change (kernel (Abelian.factorThruImage g)).IsQuasicoherent
    exact hresidual.1.2
  letI : I₀.IsQuasicoherent := by
    change (Abelian.image g).IsQuasicoherent
    exact Scheme.Modules.isQuasicoherent_image g
  letI : Q₀.IsFiniteType := by
    change (cokernel (Abelian.image.ι g)).IsFiniteType
    exact hresidual.2.1
  letI : Q₀.IsQuasicoherent := by
    change (cokernel (Abelian.image.ι g)).IsQuasicoherent
    exact hresidual.2.2
  let S₁ := ShortComplex.kernelSequence (Abelian.factorThruImage g)
  haveI : Epi S₁.g := by
    dsimp [S₁, ShortComplex.kernelSequence]
    infer_instance
  have hS₁ : S₁.ShortExact :=
    { exact :=
        ShortComplex.kernelSequence_exact
          (Abelian.factorThruImage g) }
  have hI₀ :
      letI := hZeroCanonicalFieldModule K X f I₀
      FiniteDimensional K (H I₀ 0) := by
    apply hZeroCanonical_finiteDimensional_X3_of_shortExact
      K X f hS₁
    · change
        letI := hZeroCanonicalFieldModule K X f E
        FiniteDimensional K (H E 0)
      exact hE
    · change
        letI := hOneCanonicalFieldModule K X f K₀
        FiniteDimensional K (H K₀ 1)
      exact
        genuineSheafHOneCanonical_finiteDimensional_of_rationalSection
          K X f s K₀
  have hQ₀ :
      letI := hZeroCanonicalFieldModule K X f Q₀
      FiniteDimensional K (H Q₀ 0) := by
    let A : CanonicalSupportThickening Q₀ :=
      CanonicalSupportThickening.ofFiniteType Q₀
    apply hZeroCanonical_finiteDimensional_of_closedStalkSupport_lt_top
      K X f Q₀ A
    change closedStalkSupport
        (cokernel (Abelian.image.ι g)) < ⊤
    exact hQ
  let S₂ := ShortComplex.cokernelSequence (Abelian.image.ι g)
  haveI : Mono S₂.f := by
    dsimp [S₂, ShortComplex.cokernelSequence]
    infer_instance
  have hS₂ : S₂.ShortExact :=
    { exact :=
        ShortComplex.cokernelSequence_exact
          (Abelian.image.ι g) }
  apply hZeroCanonical_finiteDimensional_X2_of_shortExact K X f hS₂
  · change
      letI := hZeroCanonicalFieldModule K X f I₀
      FiniteDimensional K (H I₀ 0)
    exact hI₀
  · change
      letI := hZeroCanonicalFieldModule K X f Q₀
      FiniteDimensional K (H Q₀ 0)
    exact hQ₀

/-- A coherent full-support source which surjects onto `M` on any nonempty
open gives finite-dimensional canonical `H⁰(M)`, provided its own canonical
`H⁰` is finite-dimensional.  Full support makes the support containment and
support-meeting point needed for strict cokernel support automatic.

This is the exact consumer for a future finite family of generic generators:
their extension only has to be epic on one nonempty open, not invertible
there and not oriented from `M` toward a comodel. -/
theorem hZeroCanonical_finiteDimensional_of_fullSupportSource_of_epi_restrict
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (s : SmoothCurveRationalSection K X f)
    (E M : X.Modules) [E.IsFiniteType] [E.IsQuasicoherent]
    [M.IsFiniteType] [M.IsQuasicoherent]
    (g : E ⟶ M) {Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] [Nonempty Y]
    [Epi ((restrictFunctor j).map g)]
    (hEtop : closedStalkSupport E = ⊤)
    (hE : letI := hZeroCanonicalFieldModule K X f E
      FiniteDimensional K (H E 0)) :
    letI := hZeroCanonicalFieldModule K X f M
    FiniteDimensional K (H M 0) := by
  letI : IsNoetherian X :=
    isNoetherian_of_proper_smoothRelativeDimension_one K X f
  have hresidual :=
    Scheme.Modules.comparisonResidual_isFiniteType_and_isQuasicoherent g
  letI : (cokernel (Abelian.image.ι g)).IsFiniteType :=
    hresidual.2.1
  letI : (cokernel (Abelian.image.ι g)).IsQuasicoherent :=
    hresidual.2.2
  let x : Y := Classical.choice (inferInstance : Nonempty Y)
  have hQ : closedStalkSupport
      (cokernel (Abelian.image.ι g)) < ⊤ := by
    rw [← hEtop]
    exact
      Scheme.Modules.closedStalkSupport_cokernel_image_ι_lt_of_epi_map
        j g (by rw [hEtop]; exact le_top) x
          (by rw [hEtop]; trivial)
  exact hZeroCanonical_finiteDimensional_of_strictCokernel
    K X f s E M g hE hQ

/-- A coherent full-support sublattice of a finite free sheaf which
surjects onto `M` after restriction to one nonempty open forces finite
canonical `H⁰(M)`.  The finite-free monomorphism supplies `H⁰` finiteness of
the source, while the open-local epimorphism supplies strict support of the
cokernel.

This is the exact design boundary for the remaining pole-clearing producer:
it only has to place finitely many extended generic generators in one
coherent full-support submodule of a finite free sheaf. -/
theorem hZeroCanonical_finiteDimensional_of_fullSupportLattice_of_epi_restrict
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (s : SmoothCurveRationalSection K X f)
    (E M : X.Modules) [E.IsFiniteType] [E.IsQuasicoherent]
    [M.IsFiniteType] [M.IsQuasicoherent]
    (g : E ⟶ M) {Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] [Nonempty Y]
    [Epi ((restrictFunctor j).map g)]
    (I : Type u) [Finite I]
    (e : E ⟶ SheafOfModules.free I (R := X.ringCatSheaf)) [Mono e]
    (hEtop : closedStalkSupport E = ⊤) :
    letI := hZeroCanonicalFieldModule K X f M
    FiniteDimensional K (H M 0) := by
  apply hZeroCanonical_finiteDimensional_of_fullSupportSource_of_epi_restrict
    K X f s E M g j hEtop
  exact hZeroCanonical_finiteDimensional_of_mono_to_free K X f E I e

/-- On a pointed smooth proper integral curve, it is enough to construct
support comodels for coherent modules whose closed stalk support is the whole
curve.  Strict support is discharged by the canonical finite thickening and
the identity comodel.  This is the exact design boundary for the remaining
full-support geometric producer. -/
theorem orderedBaseCechLowDegreeFinite_of_fullSupportComodels
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (s : SmoothCurveRationalSection K X f)
    {I : Type u} [LinearOrder I] (U : I → X.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (hfull : ∀ (N : X.Modules),
      N.IsFiniteType → N.IsQuasicoherent →
        closedStalkSupport N = ⊤ →
          ∃ (E : X.Modules) (g : N ⟶ E),
            IsCoherentLowDegreeSupportComodel f U N E g)
    (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent] :
    OrderedBaseCechLowDegreeFinite f U M := by
  letI : IsNoetherian X :=
    isNoetherian_of_proper_smoothRelativeDimension_one K X f
  letI : X.IsSeparated :=
    ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  apply orderedBaseCechLowDegreeFinite_of_coherentSupportComodels
    f U hUaff _ M
  intro N hNfinite hNqc
  letI : N.IsFiniteType := hNfinite
  letI : N.IsQuasicoherent := hNqc
  by_cases hNtop : closedStalkSupport N = ⊤
  · exact hfull N hNfinite hNqc hNtop
  · have hNstrict : closedStalkSupport N < ⊤ :=
      lt_top_iff_ne_top.mpr hNtop
    let A : CanonicalSupportThickening N :=
      CanonicalSupportThickening.ofFiniteType N
    have hNlow : OrderedBaseCechLowDegreeFinite f U N :=
      orderedBaseCechLowDegreeFinite_of_rationalSection_of_closedStalkSupport_lt_top
        K X f s N A hNstrict U hU hUaff
    exact
      ⟨N, 𝟙 N,
        IsCoherentLowDegreeSupportComodel.identity f U N hNlow⟩

/-- The full-support-only comodel boundary implies finite-dimensional
canonical `H⁰` for every coherent module on the pointed proper curve.  The
named downstream consumer is the coherent-cohomology facade; no comparison
producer is hidden in this reduction theorem. -/
theorem hZeroCanonical_finiteDimensional_of_fullSupportComodels
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (s : SmoothCurveRationalSection K X f)
    {I : Type u} [LinearOrder I] (U : I → X.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (hfull : ∀ (N : X.Modules),
      N.IsFiniteType → N.IsQuasicoherent →
        closedStalkSupport N = ⊤ →
          ∃ (E : X.Modules) (g : N ⟶ E),
            IsCoherentLowDegreeSupportComodel f U N E g)
    (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent] :
    letI := hZeroCanonicalFieldModule K X f M
    FiniteDimensional K (H M 0) := by
  let S := Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens))
  letI : Algebra K S := (Scheme.ΓSpecIso (.of K)).inv.hom.toAlgebra
  letI : Module S (H M 0) := baseSectionsHZeroModule f M
  letI : Module.Finite S (H M 0) := by
    letI : Module.Finite S
        ((orderedBaseCechComplex f M U).homology 0) :=
      (orderedBaseCechLowDegreeFinite_of_fullSupportComodels
        K X f s U hU hUaff hfull M).1
    exact hZero_finite_of_orderedBaseCechComplex f M U hU
  letI := hZeroCanonicalFieldModule K X f M
  letI : IsScalarTower K S (H M 0) :=
    IsScalarTower.of_compHom K S (H M 0)
  have hS : RingHom.Finite (algebraMap K S) := by
    change RingHom.Finite (Scheme.ΓSpecIso (.of K)).inv.hom
    exact (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv.finite
  letI : Module.Finite K S := RingHom.finite_algebraMap.mp hS
  exact Module.Finite.trans S (H M 0)

end MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology
