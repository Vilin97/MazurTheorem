/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineHomPushforward
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteSectionsCoherence

/-!
# Coherence of finite pushforwards

A finite morphism is affine.  Pushforward therefore preserves
quasicoherence.  On every affine open of the target, the source ring is
finite over the target ring, while a finite-type quasicoherent module
has finite sections on the affine preimage.  Transitivity of module
finiteness and the finite-section coherence criterion then show that
the pushforward is finitely presented.
-/


open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/--
Sections of the pushforward of a finite-type quasicoherent module along
a finite morphism are finite over every affine open of the target.
-/
theorem finiteSections_pushforward_of_finite
    (f : X ⟶ Y) [IsFinite f]
    (M : X.Modules) [M.IsFiniteType]
    [M.IsQuasicoherent]
    {U : Y.Opens} (hU : IsAffineOpen U) :
    Module.Finite Γ(Y, U)
      Γ((pushforward f).obj M, U) := by
  letI : Algebra Γ(Y, U)
      Γ(X, f ⁻¹ᵁ U) :=
    (f.app U).hom.toAlgebra
  haveI hRing :
      Module.Finite Γ(Y, U)
        Γ(X, f ⁻¹ᵁ U) :=
    f.finite_app U hU
  haveI hModule :
      Module.Finite Γ(X, f ⁻¹ᵁ U)
        Γ(M, f ⁻¹ᵁ U) :=
    finiteSections_of_isAffineOpen M
      (hU.preimage f)
  letI : Module Γ(Y, U)
      Γ(M, f ⁻¹ᵁ U) :=
    Module.compHom _
      (f.app U).hom
  haveI : IsScalarTower
      Γ(Y, U) Γ(X, f ⁻¹ᵁ U)
        Γ(M, f ⁻¹ᵁ U) :=
    IsScalarTower.of_algebraMap_smul
      fun _ _ => rfl
  have h :
      Module.Finite Γ(Y, U)
        Γ(M, f ⁻¹ᵁ U) :=
    Module.Finite.trans
      Γ(X, f ⁻¹ᵁ U)
      Γ(M, f ⁻¹ᵁ U)
  exact h

/--
Pushforward along a finite morphism into a locally Noetherian scheme
sends finite-type quasicoherent modules to finitely presented modules.
-/
theorem isFinitePresentation_pushforward_finite
    [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f]
    (M : X.Modules) [M.IsFiniteType]
    [M.IsQuasicoherent] :
    ((pushforward f).obj M).IsFinitePresentation := by
  letI :
      ((pushforward f).obj M).IsQuasicoherent :=
    isQuasicoherent_pushforward_affineHom f M
  apply
    isFinitePresentation_of_finiteAffineSections
      ((pushforward f).obj M)
  intro U hU
  exact
    finiteSections_pushforward_of_finite
      f M hU

/--
Under the same hypotheses, the finite pushforward is in particular of
finite type.
-/
theorem isFiniteType_pushforward_finite
    [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f]
    (M : X.Modules) [M.IsFiniteType]
    [M.IsQuasicoherent] :
    ((pushforward f).obj M).IsFiniteType := by
  letI :
      ((pushforward f).obj M).IsFinitePresentation :=
    isFinitePresentation_pushforward_finite f M
  exact
    SheafOfModules.instIsFiniteTypeOfIsFinitePresentation
      ((pushforward f).obj M)

/--
Closed-immersion pushforward preserves finite presentation over a
locally Noetherian target.
-/
theorem isFinitePresentation_pushforward_closedImmersion
    [IsLocallyNoetherian Y]
    (i : X ⟶ Y) [IsClosedImmersion i]
    (M : X.Modules) [M.IsFiniteType]
    [M.IsQuasicoherent] :
    ((pushforward i).obj M).IsFinitePresentation :=
  isFinitePresentation_pushforward_finite i M

/--
Closed-immersion pushforward preserves finite type over a locally
Noetherian target.
-/
theorem isFiniteType_pushforward_closedImmersion
    [IsLocallyNoetherian Y]
    (i : X ⟶ Y) [IsClosedImmersion i]
    (M : X.Modules) [M.IsFiniteType]
    [M.IsQuasicoherent] :
    ((pushforward i).obj M).IsFiniteType :=
  isFiniteType_pushforward_finite i M

end AlgebraicGeometry.Scheme.Modules
