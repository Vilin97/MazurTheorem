/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.CoherentComparisonResiduals
import MazurTorsion.Upstream.CoherentCohomologyFinite.NoetherianReduction
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveModificationOpenComparison
import MazurTorsion.Upstream.CoherentCohomologyFinite.VariableProjectiveModificationDevissage

/-!
# Acyclic extensions on support-adapted projective modifications

The useful model on a projective modification is not generally the raw
pullback of a coherent module.  Geometrically one first extends the module
from an isomorphism open to a coherent module `N₀` upstairs, compensates the
restriction by a relative twist, and then replaces `N₀` by a sufficiently
positive twist `N₀(t)`.  Relative Serre vanishing makes that twist acyclic
for the modification.

This file packages the exact output of that construction.  It does not
postulate a relative twisting functor that is absent at the current
Mathlib pin.  Once the coherent acyclic extension, its comparison map, and
support control are supplied, all kernel/cokernel coherence, support
decrease, and projective-model cohomology finiteness are automatic.
-/


open CategoryTheory Limits AlgebraicGeometry TensorProduct
open TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

open ProjectiveSpace

noncomputable local instance modificationExtensionCohomologyAddCommGroup
    {Z : TopCat.{0}}
    (G : Z.Sheaf AddCommGrpCat.{0}) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H G n) := by
  dsimp only [CategoryTheory.Sheaf.H]
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

/--
A coherent modification model obtained by extension and a sufficiently
positive relative twist.

The `cohomologyComparison` field is the output of relative acyclicity and
Leray; `pushforwardSupport_le` records that the chosen extension introduces
no support component outside the closure of the source support.
-/
structure AcyclicExtensionModificationInput
    {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of ℚ)}
    (P : ProjectiveModification f)
    (M : X.Modules) where
  /-- The coherent, sufficiently positive extension upstairs. -/
  modelModule : P.model.Modules
  /-- Coherence of the extension/twist. -/
  modelCoherent : CoherentModule modelModule
  /-- The global comparison with its direct image. -/
  comparison :
    M ⟶
      (Scheme.Modules.pushforward P.toOriginal).obj
        modelModule
  /-- Proper direct-image coherence for this model. -/
  pushforwardCoherent :
    CoherentModule
      ((Scheme.Modules.pushforward P.toOriginal).obj
        modelModule)
  /-- The cohomology comparison furnished by relative acyclicity. -/
  cohomologyComparison :
    ∀ n : ℕ,
      ((Scheme.Modules.pushforward P.toOriginal).obj
          modelModule).sheaf.H n ≃+
        modelModule.sheaf.H n
  /-- An open over which the projective modification is unchanged. -/
  isomorphismOpen : X.Opens
  /-- The modification is an isomorphism over the chosen open. -/
  restrictedMorphismIsIso :
    IsIso (P.toOriginal ∣_ isomorphismOpen)
  /-- The comparison is the intended extension of `M` on that open. -/
  comparisonIsIsoOnOpen :
    IsIso
      ((Scheme.Modules.restrictFunctor
        isomorphismOpen.ι).map comparison)
  /-- The direct image has no support outside the source support. -/
  pushforwardSupport_le :
    Scheme.Modules.closedStalkSupport
        ((Scheme.Modules.pushforward P.toOriginal).obj
          modelModule) ≤
      Scheme.Modules.closedStalkSupport M
  /-- The isomorphism open is adapted to the current support. -/
  sourceZeroOrSupportPoint :
    IsZero M ∨
      ∃ x : isomorphismOpen,
        isomorphismOpen.ι x ∈
          Scheme.Modules.closedStalkSupport M

namespace AcyclicExtensionModificationInput

variable
    {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of ℚ)}
    {P : ProjectiveModification f}
    {M : X.Modules}

/--
An acyclic extension input supplies the open comparison needed by support
dévissage.  The two residual coherence proofs are derived internally.
-/
noncomputable def toModificationOpenComparison
    [IsLocallyNoetherian X]
    [M.IsFiniteType] [M.IsQuasicoherent]
    (A : AcyclicExtensionModificationInput P M) :
    ModificationOpenComparison P M := by
  let E :=
    (Scheme.Modules.pushforward P.toOriginal).obj
      A.modelModule
  letI : E.IsFiniteType :=
    A.pushforwardCoherent.1
  letI : E.IsQuasicoherent :=
    A.pushforwardCoherent.2
  have hresidual :
      ((kernel
            (Abelian.factorThruImage A.comparison)).IsFiniteType ∧
          (kernel
            (Abelian.factorThruImage A.comparison)).IsQuasicoherent) ∧
        ((cokernel
            (Abelian.image.ι A.comparison)).IsFiniteType ∧
          (cokernel
            (Abelian.image.ι A.comparison)).IsQuasicoherent) :=
    Scheme.Modules.comparisonResidual_isFiniteType_and_isQuasicoherent
      A.comparison
  exact
    { modelModule := A.modelModule
      modelCoherent := A.modelCoherent
      comparison := A.comparison
      pushforwardCoherent := A.pushforwardCoherent
      cohomologyComparison := A.cohomologyComparison
      kernelCoherent := hresidual.1
      cokernelCoherent := hresidual.2
      openSubscheme := A.isomorphismOpen
      openMap := A.isomorphismOpen.ι
      isOpenImmersion_openMap := inferInstance
      comparison_isIso_on_open :=
        A.comparisonIsIsoOnOpen
      pushforwardSupport_le :=
        A.pushforwardSupport_le
      sourceZeroOrSupportPoint :=
        A.sourceZeroOrSupportPoint }

/--
Projective-space finiteness turns the coherent acyclic extension into a
modification acyclic model.
-/
noncomputable def toModificationAcyclicModel
    [IsLocallyNoetherian X]
    [M.IsFiniteType] [M.IsQuasicoherent]
    (A : AcyclicExtensionModificationInput P M)
    (hprojectiveSpace :
      ∀ (d : ℕ) (N : (scheme ℚ d).Modules)
        [N.IsFiniteType] [N.IsQuasicoherent] (q : ℕ),
        Module.Finite ℚ (ℚ ⊗[ℤ] N.sheaf.H q)) :
    ModificationAcyclicModel P M := by
  letI : A.modelModule.IsFiniteType :=
    A.modelCoherent.1
  letI : A.modelModule.IsQuasicoherent :=
    A.modelCoherent.2
  have hmodel :
      RationalSheafHFinite A.modelModule := by
    intro q
    exact
      coherentCohomologyFinite_of_projectiveFactorization
        hprojectiveSpace P.projectiveOverBase
          A.modelModule q
  exact
    ModificationOpenComparison.toModificationAcyclicModel
      (A.toModificationOpenComparison) hmodel

end AcyclicExtensionModificationInput

/--
Every coherent module has a positive, acyclic extension on some
support-adapted projective modification.
-/
def HasVariableAcyclicExtensionModificationInputs
    {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of ℚ)) : Prop :=
  ∀ (M : X.Modules), CoherentModule M →
    ∃ P : ProjectiveModification f,
      Nonempty (AcyclicExtensionModificationInput P M)

/--
Support-adapted acyclic extensions feed the exact variable-model interface
used by support dévissage.
-/
theorem hasVariableProjectiveAcyclicModels_of_acyclicExtensionInputs
    {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of ℚ))
    [IsProper f]
    (hprojectiveSpace :
      ∀ (d : ℕ) (N : (scheme ℚ d).Modules)
        [N.IsFiniteType] [N.IsQuasicoherent] (q : ℕ),
        Module.Finite ℚ (ℚ ⊗[ℤ] N.sheaf.H q))
    (hinputs : HasVariableAcyclicExtensionModificationInputs f) :
    HasVariableProjectiveAcyclicModels f := by
  letI : IsNoetherian X :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.isNoetherian_of_isProper_to_field f
  intro M hM
  letI : M.IsFiniteType :=
    hM.1
  letI : M.IsQuasicoherent :=
    hM.2
  obtain ⟨P, ⟨A⟩⟩ :=
    hinputs M hM
  exact
    ⟨P, ⟨A.toModificationAcyclicModel hprojectiveSpace⟩⟩

/--
The acyclic-extension input gives the exact rationalized cohomology
conclusion for every coherent module on the proper scheme.
-/
theorem rationalSheafHFinite_of_acyclicExtensionInputs
    {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of ℚ))
    [IsProper f]
    (hprojectiveSpace :
      ∀ (d : ℕ) (N : (scheme ℚ d).Modules)
        [N.IsFiniteType] [N.IsQuasicoherent] (q : ℕ),
        Module.Finite ℚ (ℚ ⊗[ℤ] N.sheaf.H q))
    (hinputs : HasVariableAcyclicExtensionModificationInputs f)
    (M : X.Modules)
    [M.IsFiniteType] [M.IsQuasicoherent] :
    RationalSheafHFinite M :=
  rationalSheafHFinite_of_variableProjectiveAcyclicModels
    f
    (hasVariableProjectiveAcyclicModels_of_acyclicExtensionInputs
      f hprojectiveSpace hinputs)
    M

/--
Degreewise form of `rationalSheafHFinite_of_acyclicExtensionInputs`.
-/
theorem coherentCohomologyFinite_of_acyclicExtensionInputs
    {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of ℚ))
    [IsProper f]
    (hprojectiveSpace :
      ∀ (d : ℕ) (N : (scheme ℚ d).Modules)
        [N.IsFiniteType] [N.IsQuasicoherent] (q : ℕ),
        Module.Finite ℚ (ℚ ⊗[ℤ] N.sheaf.H q))
    (hinputs : HasVariableAcyclicExtensionModificationInputs f)
    (M : X.Modules)
    [M.IsFiniteType] [M.IsQuasicoherent]
    (n : ℕ) :
    Module.Finite ℚ (ℚ ⊗[ℤ] M.sheaf.H n) :=
  rationalSheafHFinite_of_acyclicExtensionInputs
    f hprojectiveSpace hinputs M n

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
