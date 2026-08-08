/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project, Vasily Ilin, Codex

The low-degree comparison is adapted from the Apache-licensed
`SchemeModuleOrderedBaseCechPushforwardFinite.lean` in AINTLIB.
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleOrderedBaseCechLowDegreeFinite
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleOrderedBaseCechPushforward
import MazurTorsion.Upstream.SchemeModuleFinitePushforward

/-!
# Low-degree Cech finiteness under finite pushforward

The canonical pushforward comparison transports finite generation in
degrees zero and one.  In particular, a low-degree finiteness theorem for
finite-type quasicoherent modules on the target descends along a finite
morphism.
-/

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules
namespace OrderedBaseCechLowDegreeFinite

/-- Finite ordered base-Cech homology in degrees zero and one is invariant
under the canonical pushforward comparison with the inverse-image cover. -/
theorem pushforward_iff
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (π : Y ⟶ S)
    (M : X.Modules) {ι : Type u} [LinearOrder ι]
    (U : ι → Y.Opens) :
    OrderedBaseCechLowDegreeFinite (f ≫ π)
        (fun i ↦ f ⁻¹ᵁ U i) M ↔
      OrderedBaseCechLowDegreeFinite π U
        ((pushforward f).obj M) := by
  constructor
  · rintro ⟨hzero, hone⟩
    constructor
    · letI : Module.Finite Γ(S, (⊤ : S.Opens))
          ((orderedBaseCechComplex (f ≫ π) M
            (fun i ↦ f ⁻¹ᵁ U i)).homology 0) :=
        hzero
      let e := HomologicalComplex.homologyMapIso
        (orderedBaseCechComplexPushforwardIso f π M U) 0
      exact Module.Finite.equiv e.toLinearEquiv
    · letI : Module.Finite Γ(S, (⊤ : S.Opens))
          ((orderedBaseCechComplex (f ≫ π) M
            (fun i ↦ f ⁻¹ᵁ U i)).homology 1) :=
        hone
      let e := HomologicalComplex.homologyMapIso
        (orderedBaseCechComplexPushforwardIso f π M U) 1
      exact Module.Finite.equiv e.toLinearEquiv
  · rintro ⟨hzero, hone⟩
    constructor
    · letI : Module.Finite Γ(S, (⊤ : S.Opens))
          ((orderedBaseCechComplex π
            ((pushforward f).obj M) U).homology 0) :=
        hzero
      let e := HomologicalComplex.homologyMapIso
        (orderedBaseCechComplexPushforwardIso f π M U) 0
      exact Module.Finite.equiv e.symm.toLinearEquiv
    · letI : Module.Finite Γ(S, (⊤ : S.Opens))
          ((orderedBaseCechComplex π
            ((pushforward f).obj M) U).homology 1) :=
        hone
      let e := HomologicalComplex.homologyMapIso
        (orderedBaseCechComplexPushforwardIso f π M U) 1
      exact Module.Finite.equiv e.symm.toLinearEquiv

/-- A low-degree finiteness theorem for finite-type quasicoherent modules on
the target descends to inverse-image covers along finite morphisms. -/
theorem of_finite_pushforward
    {X Y S : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (π : Y ⟶ S) (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType]
    {ι : Type u} [LinearOrder ι] (U : ι → Y.Opens)
    (hY : ∀ N : Y.Modules,
      N.IsQuasicoherent → N.IsFiniteType →
        OrderedBaseCechLowDegreeFinite π U N) :
    OrderedBaseCechLowDegreeFinite (f ≫ π)
      (fun i ↦ f ⁻¹ᵁ U i) M := by
  let N := (pushforward f).obj M
  let hNqc : N.IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffineHom f
  letI : N.IsQuasicoherent := hNqc
  have hNft : N.IsFiniteType :=
    isFiniteType_pushforward_of_isFinite f
  exact (pushforward_iff f π M U).2 (hY N hNqc hNft)

end OrderedBaseCechLowDegreeFinite
end AlgebraicGeometry.Scheme.Modules
