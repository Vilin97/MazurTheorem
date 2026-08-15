/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenRestrictionComparisonSupport
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveModificationAcyclicModel
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSpaceCohomologyDevissage

/-!
# Open-local comparisons on a projective modification

This file connects the projective-space theorem to the support
codévissage for a proper scheme.

An `ModificationOpenComparison` contains the coherent module upstairs,
the comparison to its direct image, and the Leray-type cohomology
comparison.  Instead of asking separately for strict support decrease of
the kernel and cokernel, it records geometric open-local data:

* the comparison is an isomorphism on an open subscheme;
* that open contains a point of the source support;
* the direct-image support is contained in the source support.

The lemmas in `OpenRestrictionComparisonSupport` then prove both strict
support drops automatically.  The final theorems show precisely how the
projective-space finiteness theorem and a Chow projective modification
would finish the Brian Nugent benchmark.
-/


open CategoryTheory Limits AlgebraicGeometry TensorProduct
open TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

open ProjectiveSpace

noncomputable local instance modificationOpenCohomologyAddCommGroup
    {Z : TopCat.{0}}
    (G : Z.Sheaf AddCommGrpCat.{0}) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H G n) := by
  dsimp only [CategoryTheory.Sheaf.H]
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

/--
A comparison with a coherent module on a projective modification whose
support decrease is witnessed on an open subscheme.
-/
structure ModificationOpenComparison
    {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of ℚ)}
    (P : ProjectiveModification f)
    (M : X.Modules) where
  modelModule : P.model.Modules
  modelCoherent : CoherentModule modelModule
  comparison :
    M ⟶
      (Scheme.Modules.pushforward P.toOriginal).obj
        modelModule
  pushforwardCoherent :
    CoherentModule
      ((Scheme.Modules.pushforward P.toOriginal).obj
        modelModule)
  cohomologyComparison :
    ∀ n : ℕ,
      ((Scheme.Modules.pushforward P.toOriginal).obj
          modelModule).sheaf.H n ≃+
        modelModule.sheaf.H n
  kernelCoherent :
    CoherentModule
      (kernel (Abelian.factorThruImage comparison))
  cokernelCoherent :
    CoherentModule
      (cokernel (Abelian.image.ι comparison))
  openSubscheme : Scheme.{0}
  openMap : openSubscheme ⟶ X
  isOpenImmersion_openMap : IsOpenImmersion openMap
  comparison_isIso_on_open :
    IsIso
      ((Scheme.Modules.restrictFunctor openMap).map
        comparison)
  pushforwardSupport_le :
    Scheme.Modules.closedStalkSupport
        ((Scheme.Modules.pushforward P.toOriginal).obj
          modelModule) ≤
      Scheme.Modules.closedStalkSupport M
  sourceZeroOrSupportPoint :
    IsZero M ∨
      ∃ x : openSubscheme,
        openMap x ∈
          Scheme.Modules.closedStalkSupport M

namespace ModificationOpenComparison

variable
    {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of ℚ)}
    {P : ProjectiveModification f}
    {M : X.Modules}

/--
An open-local comparison, together with finiteness upstairs, is an
acyclic model in the sense required by support codévissage.
-/
noncomputable def toModificationAcyclicModel
    (A : ModificationOpenComparison P M)
    (hmodel : RationalSheafHFinite A.modelModule) :
    ModificationAcyclicModel P M := by
  letI : IsOpenImmersion A.openMap :=
    A.isOpenImmersion_openMap
  letI :
      IsIso
        ((Scheme.Modules.restrictFunctor A.openMap).map
          A.comparison) :=
    A.comparison_isIso_on_open
  letI :
      (kernel
        (Abelian.factorThruImage
          A.comparison)).IsFiniteType :=
    A.kernelCoherent.1
  letI :
      (kernel
        (Abelian.factorThruImage
          A.comparison)).IsQuasicoherent :=
    A.kernelCoherent.2
  letI :
      (cokernel
        (Abelian.image.ι
          A.comparison)).IsFiniteType :=
    A.cokernelCoherent.1
  letI :
      (cokernel
        (Abelian.image.ι
          A.comparison)).IsQuasicoherent :=
    A.cokernelCoherent.2
  have hdrops :
      (IsZero
          (kernel
            (Abelian.factorThruImage A.comparison)) ∨
        Scheme.Modules.closedStalkSupport
            (kernel
              (Abelian.factorThruImage A.comparison)) <
          Scheme.Modules.closedStalkSupport M) ∧
      (IsZero
          (cokernel
            (Abelian.image.ι A.comparison)) ∨
        Scheme.Modules.closedStalkSupport
            (cokernel
              (Abelian.image.ι A.comparison)) <
          Scheme.Modules.closedStalkSupport M) := by
    rcases A.sourceZeroOrSupportPoint with hMzero | ⟨x, hx⟩
    · have hMbot :=
        Scheme.Modules.closedStalkSupport_eq_bot_of_isZero
          M hMzero
      have hKle :
          Scheme.Modules.closedStalkSupport
              (kernel
                (Abelian.factorThruImage A.comparison)) ≤
            Scheme.Modules.closedStalkSupport M :=
        Scheme.Modules.closedStalkSupport_le_of_mono
          (kernel.ι
            (Abelian.factorThruImage A.comparison))
      have hKbot :
          Scheme.Modules.closedStalkSupport
              (kernel
                (Abelian.factorThruImage A.comparison)) =
            ⊥ := by
        apply le_antisymm
        · rw [← hMbot]
          exact hKle
        · exact bot_le
      have hQle :
          Scheme.Modules.closedStalkSupport
              (cokernel
                (Abelian.image.ι A.comparison)) ≤
            Scheme.Modules.closedStalkSupport M :=
        (Scheme.Modules.closedStalkSupport_le_of_epi
          (cokernel.π
            (Abelian.image.ι A.comparison))).trans
              A.pushforwardSupport_le
      have hQbot :
          Scheme.Modules.closedStalkSupport
              (cokernel
                (Abelian.image.ι A.comparison)) =
            ⊥ := by
        apply le_antisymm
        · rw [← hMbot]
          exact hQle
        · exact bot_le
      exact
        ⟨Or.inl
            ((Scheme.Modules.isZero_iff_closedStalkSupport_eq_bot
              (kernel
                (Abelian.factorThruImage A.comparison))).mpr
                hKbot),
          Or.inl
            ((Scheme.Modules.isZero_iff_closedStalkSupport_eq_bot
              (cokernel
                (Abelian.image.ι A.comparison))).mpr
                hQbot)⟩
    · have hlt :=
        Scheme.Modules.comparisonResidual_closedStalkSupport_lt
          A.openMap A.comparison
          A.pushforwardSupport_le x hx
      exact ⟨Or.inr hlt.1, Or.inr hlt.2⟩
  exact
    {
      modelModule := A.modelModule
      modelCoherent := A.modelCoherent
      comparison := A.comparison
      pushforwardCoherent := A.pushforwardCoherent
      modelCohomologyFinite := hmodel
      cohomologyComparison := A.cohomologyComparison
      kernelCoherent := A.kernelCoherent
      cokernelCoherent := A.cokernelCoherent
      kernelSupportDrops := hdrops.1
      cokernelSupportDrops := hdrops.2
    }

end ModificationOpenComparison

/--
Every coherent module admits an open-local comparison on the fixed
projective modification.
-/
def HasModificationOpenComparisons
    {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of ℚ)}
    (P : ProjectiveModification f) : Prop :=
  ∀ (M : X.Modules), CoherentModule M →
    Nonempty (ModificationOpenComparison P M)

/--
If coherent cohomology is finite on standard projective spaces, every
open-local comparison supplies an acyclic model on the projective
modification.
-/
theorem hasModificationAcyclicModels_of_openComparisons
    {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of ℚ)}
    (hprojectiveSpace :
      ∀ (d : ℕ) (N : (scheme ℚ d).Modules)
        [N.IsFiniteType] [N.IsQuasicoherent] (q : ℕ),
        Module.Finite ℚ (ℚ ⊗[ℤ] N.sheaf.H q))
    (P : ProjectiveModification f)
    (hcomparisons : HasModificationOpenComparisons P) :
    HasModificationAcyclicModels P := by
  intro M hM
  obtain ⟨A⟩ := hcomparisons M hM
  letI : A.modelModule.IsFiniteType :=
    A.modelCoherent.1
  letI : A.modelModule.IsQuasicoherent :=
    A.modelCoherent.2
  have hmodel : RationalSheafHFinite A.modelModule := by
    intro q
    exact
      coherentCohomologyFinite_of_projectiveFactorization
        hprojectiveSpace P.projectiveOverBase
        A.modelModule q
  exact
    ⟨A.toModificationAcyclicModel hmodel⟩

/--
Projective-space finiteness and open-local comparisons on one projective
modification imply coherent-cohomology finiteness on the original proper
scheme.
-/
theorem coherentCohomologyFinite_of_projectiveSpace_and_openComparisons
    {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of ℚ)) [IsProper f]
    (hprojectiveSpace :
      ∀ (d : ℕ) (N : (scheme ℚ d).Modules)
        [N.IsFiniteType] [N.IsQuasicoherent] (q : ℕ),
        Module.Finite ℚ (ℚ ⊗[ℤ] N.sheaf.H q))
    (P : ProjectiveModification f)
    (hcomparisons : HasModificationOpenComparisons P)
    (M : X.Modules)
    [M.IsFiniteType] [M.IsQuasicoherent]
    (n : ℕ) :
    Module.Finite ℚ (ℚ ⊗[ℤ] M.sheaf.H n) :=
  coherentCohomologyFinite_of_modificationAcyclicModels
    f P
    (hasModificationAcyclicModels_of_openComparisons
      hprojectiveSpace P hcomparisons)
    M n

/--
The same reduction with the Chow assembly interface made explicit.  This
is the full proper-to-projective bridge: after the assembly produces a
projective modification, only its open-local coherent comparisons remain.
-/
theorem coherentCohomologyFinite_of_chowAssembly_and_openComparisons
    {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of ℚ)) [IsProper f]
    (hasAssembly : FiniteAffineCoverProjectiveAssembly ℚ)
    (hprojectiveSpace :
      ∀ (d : ℕ) (N : (scheme ℚ d).Modules)
        [N.IsFiniteType] [N.IsQuasicoherent] (q : ℕ),
        Module.Finite ℚ (ℚ ⊗[ℤ] N.sheaf.H q))
    (hcomparisons :
      ∀ P : ProjectiveModification f,
        HasModificationOpenComparisons P)
    (M : X.Modules)
    [M.IsFiniteType] [M.IsQuasicoherent]
    (n : ℕ) :
    Module.Finite ℚ (ℚ ⊗[ℤ] M.sheaf.H n) := by
  obtain ⟨P⟩ :=
    exists_projectiveModification_of_proper
      ℚ hasAssembly f
  exact
    coherentCohomologyFinite_of_projectiveSpace_and_openComparisons
      f hprojectiveSpace P (hcomparisons P) M n

/--
The proper-scheme conclusion expressed directly in terms of the two
projective-space inputs developed in this repository: finiteness for all
integer Serre twists and finite twisted-free generation.  Together with
Chow assembly and the open-local comparison data, these assumptions imply
the exact rationalized sheaf-cohomology conclusion of the benchmark.
-/
theorem coherentCohomologyFinite_of_chowAssembly_twists_generation_and_openComparisons
    {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of ℚ)) [IsProper f]
    (hasAssembly : FiniteAffineCoverProjectiveAssembly ℚ)
    (htwist :
      ∀ (d : ℕ) (m : ℤ) (q : ℕ),
        Module.Finite ℚ
          (ℚ ⊗[ℤ] (SerreTwist.OInt ℚ d m).sheaf.H q))
    (hgeneration :
      ∀ (d : ℕ) (Y : (scheme ℚ d).Modules)
        [Y.IsFiniteType] [Y.IsQuasicoherent],
        ∃ (E : (scheme ℚ d).Modules) (e : E ⟶ Y),
          Epi e ∧
            CoherentModule E ∧
            IsFiniteIntegerTwistSum d E)
    (hcomparisons :
      ∀ P : ProjectiveModification f,
        HasModificationOpenComparisons P)
    (M : X.Modules)
    [M.IsFiniteType] [M.IsQuasicoherent]
    (n : ℕ) :
    Module.Finite ℚ (ℚ ⊗[ℤ] M.sheaf.H n) := by
  apply
    coherentCohomologyFinite_of_chowAssembly_and_openComparisons
      f hasAssembly
  · intro d N _ _ q
    exact
      coherentCohomologyFinite_of_twists_and_generation
        d (htwist d) (hgeneration d) N q
  · exact hcomparisons

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
