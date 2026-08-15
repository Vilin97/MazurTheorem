/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveModification
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProperCohomologyDevissage
import MazurTorsion.Upstream.CoherentCohomologyFinite.WellFoundedSheafCohomologyCodesvissage

/-!
# Acyclic models on a projective modification

This file packages the precise sheaf-theoretic input needed to turn a
projective modification into a proof of coherent-cohomology finiteness.
For a coherent module `M` downstairs, an acyclic model consists of a
coherent module `N` upstairs and a comparison

`M ⟶ π_* N`.

Two points are kept explicit:

* the cohomology comparison between `π_* N` and `N` is data.  It is not
  asserted for an arbitrary morphism; geometrically it is supplied by a
  suitable relative-acyclicity/Leray theorem;
* the kernel and cokernel of the comparison must vanish or have strictly
  smaller closed stalk support.  This is the exact common-open
  compatibility needed by support induction.

Thus the theorem below does not conceal either of the two remaining
geometric obligations.
-/


open CategoryTheory Limits AlgebraicGeometry TensorProduct
open TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

noncomputable local instance modificationCohomologyAddCommGroup
    {Z : TopCat.{0}}
    (G : Z.Sheaf AddCommGrpCat.{0}) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H G n) := by
  dsimp only [CategoryTheory.Sheaf.H]
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

/--
A coherent, cohomologically acyclic model for `M` on a fixed projective
modification.

The additive equivalences in `cohomologyComparison` are the usable output
of a Leray-degeneration or relative-acyclicity argument.
-/
structure ModificationAcyclicModel
    {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of ℚ)}
    (P : ProjectiveModification f)
    (M : X.Modules) where
  /-- The coherent module on the projective model. -/
  modelModule : P.model.Modules
  /-- Coherence of the module upstairs. -/
  modelCoherent : CoherentModule modelModule
  /-- The comparison used for support codévissage. -/
  comparison :
    M ⟶
      (Scheme.Modules.pushforward P.toOriginal).obj
        modelModule
  /-- Coherence of the direct image. -/
  pushforwardCoherent :
    CoherentModule
      ((Scheme.Modules.pushforward P.toOriginal).obj
        modelModule)
  /-- Finiteness of cohomology on the projective model. -/
  modelCohomologyFinite :
    RationalSheafHFinite modelModule
  /--
  The cohomological comparison supplied by relative acyclicity and Leray.
  -/
  cohomologyComparison :
    ∀ n : ℕ,
      ((Scheme.Modules.pushforward P.toOriginal).obj
          modelModule).sheaf.H n ≃+
        modelModule.sheaf.H n
  /-- Coherence of the kernel residual. -/
  kernelCoherent :
    CoherentModule
      (kernel (Abelian.factorThruImage comparison))
  /-- Coherence of the cokernel residual. -/
  cokernelCoherent :
    CoherentModule
      (cokernel (Abelian.image.ι comparison))
  /-- The kernel vanishes or has strictly smaller closed support. -/
  kernelSupportDrops :
    IsZero (kernel (Abelian.factorThruImage comparison)) ∨
      Scheme.Modules.closedStalkSupport
          (kernel (Abelian.factorThruImage comparison)) <
        Scheme.Modules.closedStalkSupport M
  /-- The cokernel vanishes or has strictly smaller closed support. -/
  cokernelSupportDrops :
    IsZero (cokernel (Abelian.image.ι comparison)) ∨
      Scheme.Modules.closedStalkSupport
          (cokernel (Abelian.image.ι comparison)) <
        Scheme.Modules.closedStalkSupport M

namespace ModificationAcyclicModel

variable
    {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of ℚ)}
    {P : ProjectiveModification f}
    {M : X.Modules}

/-- The direct image of an acyclic model has finite rationalized
cohomology. -/
theorem pushforwardCohomologyFinite
    (A : ModificationAcyclicModel P M) :
    RationalSheafHFinite
      ((Scheme.Modules.pushforward P.toOriginal).obj
        A.modelModule) := by
  intro n
  exact
    (MazurTorsion.AlgebraicGeometry.CoherentCohomology.rationalization_finite_congr
      (A.cohomologyComparison n)).mpr
      (A.modelCohomologyFinite n)

end ModificationAcyclicModel

/--
Every coherent module admits an acyclic model on the fixed
modification.
-/
def HasModificationAcyclicModels
    {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of ℚ)}
    (P : ProjectiveModification f) : Prop :=
  ∀ (M : X.Modules), CoherentModule M →
    Nonempty (ModificationAcyclicModel P M)

/--
Support codévissage from acyclic models proves finite rationalized
cohomology for every coherent module on a proper scheme.
-/
theorem rationalSheafHFinite_of_modificationAcyclicModels
    {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of ℚ))
    [IsProper f]
    (P : ProjectiveModification f)
    (hmodels : HasModificationAcyclicModels P)
    (M : X.Modules)
    [M.IsFiniteType] [M.IsQuasicoherent] :
    RationalSheafHFinite M := by
  letI : IsNoetherian X :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.isNoetherian_of_isProper_to_field f
  apply
    rationalSheafHFinite_of_closedStalkSupport_comodels
      CoherentModule RationalSheafHFinite
  · intro Y hY
    obtain ⟨A⟩ := hmodels Y hY
    exact
      ⟨(Scheme.Modules.pushforward P.toOriginal).obj
          A.modelModule,
        A.comparison,
        A.pushforwardCohomologyFinite,
        A.kernelCoherent,
        A.cokernelCoherent,
        A.kernelSupportDrops,
        A.cokernelSupportDrops⟩
  · intro E hE
    exact hE
  · exact ⟨inferInstance, inferInstance⟩

/--
The degreewise form of
`rationalSheafHFinite_of_modificationAcyclicModels`.
-/
theorem coherentCohomologyFinite_of_modificationAcyclicModels
    {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of ℚ))
    [IsProper f]
    (P : ProjectiveModification f)
    (hmodels : HasModificationAcyclicModels P)
    (M : X.Modules)
    [M.IsFiniteType] [M.IsQuasicoherent]
    (n : ℕ) :
    Module.Finite ℚ (ℚ ⊗[ℤ] M.sheaf.H n) :=
  rationalSheafHFinite_of_modificationAcyclicModels
    f P hmodels M n

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
