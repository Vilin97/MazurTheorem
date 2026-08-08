/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleOrderedBaseCechLowDegreeFinite

/-!
# A coherent-support interface for low-degree Cech finiteness

This project-facing interface packages exactly the support-decreasing
comodel input consumed by the checked low-degree AINTLIB codévissage. It
keeps quasicoherence of the comparison image explicit, avoiding a dependency
on AINTLIB's much larger general quasicoherent-closure module.

The proper Chow construction is a downstream producer of this interface; no
properness assertion is made here.
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
