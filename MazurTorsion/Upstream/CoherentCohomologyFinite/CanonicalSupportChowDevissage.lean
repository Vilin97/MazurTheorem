/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.CanonicalSupportChowComodel

/-!
# Proper coherent cohomology from canonical Chow extensions

For each coherent module, pass to its canonical support thickening and
choose an acyclic positive-twist extension on the corresponding Chow
modification.  Pushing that extension back to the original scheme gives
the finite comodel required by well-founded closed-support codévissage.
-/


open CategoryTheory AlgebraicGeometry TensorProduct

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

variable {X : Scheme.{0}}

noncomputable local instance canonicalSupportChowSheafHAddCommGroup
    {Z : TopCat.{0}}
    (G : TopCat.Sheaf AddCommGrpCat.{0} Z) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H G n) := by
  dsimp only [CategoryTheory.Sheaf.H]
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

/--
Every coherent module has an acyclic extension on the Chow modification
of its canonical support thickening.
-/
def HasCanonicalSupportChowAcyclicExtensions
    (f : X ⟶ Spec (CommRingCat.of ℚ)) [IsProper f] : Prop :=
  ∀ (F : X.Modules) (hF : CoherentModule F),
    letI : F.IsFiniteType := hF.1
    letI : F.IsQuasicoherent := hF.2
    let A :=
      CanonicalSupportThickening.ofProperToField
        (k := ℚ) (f := f) F
    Nonempty
      (AcyclicExtensionModificationInput
        (A.chowModification (k := ℚ) (f := f))
        A.modelModule)

/--
Canonical support-Chow acyclic extensions imply finite rationalized
cohomology for every coherent module on the proper scheme.
-/
theorem rationalSheafHFinite_of_canonicalSupportChowAcyclicExtensions
    (f : X ⟶ Spec (CommRingCat.of ℚ)) [IsProper f]
    (hinputs : HasCanonicalSupportChowAcyclicExtensions f)
    (M : X.Modules)
    [M.IsFiniteType] [M.IsQuasicoherent] :
    RationalSheafHFinite M := by
  letI : IsNoetherian X :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.isNoetherian_of_isProper_to_field f
  apply
    rationalSheafHFinite_of_closedStalkSupport_comodels
      CoherentModule RationalSheafHFinite
  · intro F hF
    letI : F.IsFiniteType := hF.1
    letI : F.IsQuasicoherent := hF.2
    let A :=
      CanonicalSupportThickening.ofProperToField
        (k := ℚ) (f := f) F
    obtain ⟨B⟩ := hinputs F hF
    exact A.exists_chowComodel_of_acyclicExtensionInput B
  · intro E hE
    exact hE
  · exact ⟨inferInstance, inferInstance⟩

/-- Degreewise form of the canonical support-Chow reduction. -/
theorem coherentCohomologyFinite_of_canonicalSupportChowAcyclicExtensions
    (f : X ⟶ Spec (CommRingCat.of ℚ)) [IsProper f]
    (hinputs : HasCanonicalSupportChowAcyclicExtensions f)
    (M : X.Modules)
    [M.IsFiniteType] [M.IsQuasicoherent]
    (n : ℕ) :
    Module.Finite ℚ (ℚ ⊗[ℤ] M.sheaf.H n) :=
  rationalSheafHFinite_of_canonicalSupportChowAcyclicExtensions
    f hinputs M n

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
