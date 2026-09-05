/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleOrderedBaseCechLowDegreeFinite
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleComparisonCoherent
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleComparisonSupport

/-!
# A coherent-support interface for low-degree Cech finiteness

This project-facing interface packages exactly the support-decreasing
comodel input consumed by the checked low-degree AINTLIB codévissage. It
keeps quasicoherence of the comparison image explicit, avoiding a dependency
on AINTLIB's much larger general quasicoherent-closure module.

The proper Chow construction is a downstream producer of this interface; no
properness assertion is made here.

`IsCoherentLowDegreeSupportComodel.of_isIso_restrict` is the assembly
boundary: a coherent low-degree-good target which agrees with the source on
one support-meeting open automatically has the required coherent,
support-decreasing residuals. Its named proper-curve consumer is in
`ProperCurveCechLowDegreeFinite`.
-/

noncomputable section

universe u

open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules

namespace MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

/-- A coherent comparison target with low-degree-finite ordered base-Cech
homology, coherent residuals, an explicitly quasicoherent image, and strict
closed-support decrease for both residuals (unless they are zero). -/
def IsCoherentLowDegreeSupportComodel
    {X S : Scheme.{u}} (π : X ⟶ S)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (M E : X.Modules) (f : M ⟶ E) : Prop :=
  E.IsFiniteType ∧ E.IsQuasicoherent ∧
    OrderedBaseCechLowDegreeFinite π U E ∧
    (Abelian.image f).IsQuasicoherent ∧
    (kernel (Abelian.factorThruImage f)).IsFiniteType ∧
    (kernel (Abelian.factorThruImage f)).IsQuasicoherent ∧
    (cokernel (Abelian.image.ι f)).IsFiniteType ∧
    (cokernel (Abelian.image.ι f)).IsQuasicoherent ∧
    (IsZero (kernel (Abelian.factorThruImage f)) ∨
      closedStalkSupport (kernel (Abelian.factorThruImage f)) <
        closedStalkSupport M) ∧
    (IsZero (cokernel (Abelian.image.ι f)) ∨
      closedStalkSupport (cokernel (Abelian.image.ι f)) <
        closedStalkSupport M)

namespace IsCoherentLowDegreeSupportComodel

/-- Assemble the coherent support-comodel interface from a comparison which
is invertible on an open meeting the source support and whose target support
is contained in the source support. -/
theorem of_isIso_restrict
    {X S Y : Scheme.{u}} (π : X ⟶ S)
    [IsLocallyNoetherian X]
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    {M E : X.Modules} [M.IsFiniteType] [M.IsQuasicoherent]
    [E.IsFiniteType] [E.IsQuasicoherent]
    (hE : OrderedBaseCechLowDegreeFinite π U E)
    (f : M ⟶ E) (j : Y ⟶ X) [IsOpenImmersion j]
    [IsIso ((restrictFunctor j).map f)]
    (hEM : closedStalkSupport E ≤ closedStalkSupport M)
    (x : Y) (hxM : j x ∈ closedStalkSupport M) :
    IsCoherentLowDegreeSupportComodel π U M E f := by
  letI : (Abelian.image f).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_image f
  have hresidual :=
    Scheme.Modules.comparisonResidual_isFiniteType_and_isQuasicoherent f
  letI : (kernel (Abelian.factorThruImage f)).IsFiniteType :=
    hresidual.1.1
  letI : (kernel (Abelian.factorThruImage f)).IsQuasicoherent :=
    hresidual.1.2
  letI : (cokernel (Abelian.image.ι f)).IsFiniteType :=
    hresidual.2.1
  letI : (cokernel (Abelian.image.ι f)).IsQuasicoherent :=
    hresidual.2.2
  have hdrop :=
    Scheme.Modules.comparisonResidual_closedStalkSupport_lt
      j f hEM x hxM
  exact
    ⟨inferInstance, inferInstance, hE, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance,
      Or.inr hdrop.1, Or.inr hdrop.2⟩

/-- A coherent module which is already low-degree finite is its own support
comodel via the identity comparison.  The strict-support branch of
`ProperCurveFiniteSupportCech` is the named downstream consumer. -/
theorem identity
    {X S : Scheme.{u}} (π : X ⟶ S) [IsLocallyNoetherian X]
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent]
    (hM : OrderedBaseCechLowDegreeFinite π U M) :
    IsCoherentLowDegreeSupportComodel π U M M (𝟙 M) := by
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
    ⟨inferInstance, inferInstance, hM, inferInstance,
      hresidual.1.1, hresidual.1.2,
      hresidual.2.1, hresidual.2.2,
      Or.inl hkernel, Or.inl hcokernel⟩

end IsCoherentLowDegreeSupportComodel

private def CoherentPredicate
    {X : Scheme.{u}} (M : X.Modules) : Prop :=
  M.IsFiniteType ∧ M.IsQuasicoherent

private def LowDegreeGood
    {X S : Scheme.{u}} (π : X ⟶ S)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (E : X.Modules) : Prop :=
  E.IsFiniteType ∧ E.IsQuasicoherent ∧
    OrderedBaseCechLowDegreeFinite π U E

/-- Closed-support codévissage turns coherent low-degree support comodels
into low-degree ordered base-Cech finiteness. -/
theorem orderedBaseCechLowDegreeFinite_of_coherentSupportComodels
    {X S : Scheme.{u}} (π : X ⟶ S)
    [X.IsSeparated] [NoetherianSpace X]
    [IsNoetherianRing Γ(S, (⊤ : S.Opens))]
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (hUaff : ∀ i, IsAffineOpen (U i))
    (hcomodel : ∀ (M : X.Modules),
      M.IsFiniteType → M.IsQuasicoherent →
        ∃ (E : X.Modules) (f : M ⟶ E),
          IsCoherentLowDegreeSupportComodel π U M E f)
    (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent] :
    OrderedBaseCechLowDegreeFinite π U M := by
  refine OrderedBaseCechLowDegreeFinite.of_closedStalkSupport_comodels
    π U hUaff CoherentPredicate (LowDegreeGood π U)
    ?_ ?_ ?_ ?_ M ⟨inferInstance, inferInstance⟩
  · intro N hN
    exact hN.2
  · intro E hE
    exact hE.2.1
  · intro N hN
    obtain ⟨E, f, hEfinite, hEqc, hEcech, hIqc,
      hKfinite, hKqc, hQfinite, hQqc, hKdrop, hQdrop⟩ :=
      hcomodel N hN.1 hN.2
    exact ⟨E, f, ⟨hEfinite, hEqc, hEcech⟩, hIqc,
      ⟨hKfinite, hKqc⟩, ⟨hQfinite, hQqc⟩,
      hKdrop, hQdrop⟩
  · intro E hE
    exact hE.2.2

/-- The degree-one component of coherent closed-support codévissage. This
is the ordered-Cech finiteness input consumed by the genuine sheaf `H¹`
facade. -/
theorem orderedBaseCechHOne_finite_of_coherentSupportComodels
    {X S : Scheme.{u}} (π : X ⟶ S)
    [X.IsSeparated] [NoetherianSpace X]
    [IsNoetherianRing Γ(S, (⊤ : S.Opens))]
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (hUaff : ∀ i, IsAffineOpen (U i))
    (hcomodel : ∀ (M : X.Modules),
      M.IsFiniteType → M.IsQuasicoherent →
        ∃ (E : X.Modules) (f : M ⟶ E),
          IsCoherentLowDegreeSupportComodel π U M E f)
    (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent] :
    Module.Finite Γ(S, (⊤ : S.Opens))
      ((orderedBaseCechComplex π M U).homology 1) :=
  (orderedBaseCechLowDegreeFinite_of_coherentSupportComodels
    π U hUaff hcomodel M).2

end MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology
