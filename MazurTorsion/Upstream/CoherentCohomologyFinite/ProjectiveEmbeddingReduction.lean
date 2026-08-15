/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FinitePushforwardCoherence
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveFactorization
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemePushforwardCohomology

/-!
# Reduction along a closed embedding into projective space

A concrete projective factorization embeds the source as a closed
subscheme of finite-dimensional standard projective space.  Pushforward
along that embedding is finitely presented and quasicoherent, and its
rationalized cohomology agrees with the original module in every degree.

Thus the proper-cohomology problem reduces, for schemes carrying such a
factorization, to the corresponding theorem on the standard projective
space used by the Čech development.
-/


open CategoryTheory AlgebraicGeometry TensorProduct

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

noncomputable local instance projectiveEmbeddingCohomologyAddCommGroup
    {Z : TopCat.{0}} (G : Z.Sheaf AddCommGrpCat.{0}) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H G n) := by
  dsimp only [CategoryTheory.Sheaf.H]
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

variable {X : Scheme.{0}}
variable {f : X ⟶ Spec (CommRingCat.of ℚ)}
variable {M : X.Modules}

/--
A concrete projective factorization produces a closed embedding and a
coherent pushforward on standard projective space, with rationalized
cohomology unchanged in every degree.
-/
theorem exists_closedImmersion_coherentPushforward_of_projectiveFactorization
    (hproj : IsProjectiveFactorization f)
    [M.IsFiniteType] [M.IsQuasicoherent] :
    ∃ (d : ℕ) (i : X ⟶ scheme ℚ d),
      IsClosedImmersion i ∧
      i ≫ toSpec ℚ d = f ∧
      ((Scheme.Modules.pushforward i).obj M).IsFinitePresentation ∧
      ((Scheme.Modules.pushforward i).obj M).IsQuasicoherent ∧
      ∀ n : ℕ,
        Module.Finite ℚ
            (ℚ ⊗[ℤ] M.sheaf.H n) ↔
          Module.Finite ℚ
            (ℚ ⊗[ℤ]
              ((Scheme.Modules.pushforward i).obj M).sheaf.H n) := by
  obtain ⟨d, i, hi, hif⟩ := hproj
  letI : IsClosedImmersion i := hi
  letI : IsLocallyNoetherian
      (scheme ℚ d) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (toSpec ℚ d)
  have hfp :
      ((Scheme.Modules.pushforward i).obj M).IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pushforward_closedImmersion
      i M
  have hqc :
      ((Scheme.Modules.pushforward i).obj M).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_pushforward_affineHom
      i M
  exact
    ⟨d, i, hi, hif, hfp, hqc,
      fun n =>
        MazurTorsion.AlgebraicGeometry.CoherentCohomology.closedImmersion_rationalizedCohomology_finite_iff
          i M n⟩

/--
Equivalently, a projective factorization produces a finitely presented
quasicoherent module on some standard projective space whose
rationalized cohomology has exactly the same finiteness behavior.
-/
theorem exists_projectiveSpace_coherentModule_of_projectiveFactorization
    (hproj : IsProjectiveFactorization f)
    [M.IsFiniteType] [M.IsQuasicoherent] :
    ∃ (d : ℕ) (N : (scheme ℚ d).Modules),
      N.IsFinitePresentation ∧
      N.IsQuasicoherent ∧
      ∀ n : ℕ,
        Module.Finite ℚ
            (ℚ ⊗[ℤ] M.sheaf.H n) ↔
          Module.Finite ℚ
            (ℚ ⊗[ℤ] N.sheaf.H n) := by
  obtain ⟨d, i, _, _, hfp, hqc, hH⟩ :=
    exists_closedImmersion_coherentPushforward_of_projectiveFactorization
      (f := f) (M := M) hproj
  exact
    ⟨d, (Scheme.Modules.pushforward i).obj M,
      hfp, hqc, hH⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
