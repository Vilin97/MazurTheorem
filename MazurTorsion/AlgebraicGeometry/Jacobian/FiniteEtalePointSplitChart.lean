/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.AffineFiniteEtaleSplitChart
import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteFlatConstantRankNeighborhood

/-!
# Pointwise split charts for finite étale morphisms

Around every base point of a finite étale morphism, shrink first to the
clopen constant-rank locus and then to an affine neighborhood.  The inverse
image remains affine and the restricted morphism satisfies the hypotheses of
the affine fpqc splitting theorem.

The named downstream consumer is the finite family of curve-coordinate
components used in `PointedIncidenceDescent`.
-/

noncomputable section

universe u

open scoped TensorProduct
open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.FiniteEtalePointSplitChart

open FiniteFlatConstantRankNeighborhood

/-- A finite étale morphism is fpqc-locally a split finite set on an affine
neighborhood of every chosen base point. -/
theorem exists_affineOpen_fpqc_splitCover
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [IsFinite f] (y : Y) :
    ∃ (V : Y.Opens) (hV : IsAffineOpen V), y ∈ V ∧
      let fV := f ∣_ V
      letI : IsAffine V.toScheme := hV
      letI : IsAffine (f ⁻¹ᵁ V).toScheme := isAffine_of_isAffineHom fV
      letI : Algebra Γ(V, ⊤) Γ(f ⁻¹ᵁ V, ⊤) := fV.appTop.hom.toAlgebra
      ∃ (T : Type u) (_ : CommRing T)
        (_ : Algebra Γ(V, ⊤) T)
        (_ : Module.FaithfullyFlat Γ(V, ⊤) T)
        (_ : Module.Finite Γ(V, ⊤) T)
        (_ : Algebra.Etale Γ(V, ⊤) T) (m : ℕ)
        (_e : T ⊗[Γ(V, ⊤)] Γ(f ⁻¹ᵁ V, ⊤) ≃ₐ[T] (Fin m → T))
        (q : Spec (.of T) ⟶ V.toScheme)
        (_E : pullback fV q ≅ Spec (.of (Fin m → T))),
        _E.hom ≫ EtaleSplitChart.splitProjection T m = pullback.snd fV q ∧
          Flat q ∧ Surjective q ∧ QuasiCompact q := by
  letI : Flat f := inferInstance
  letI : LocallyOfFinitePresentation f := inferInstance
  obtain ⟨_, ⟨V : Y.Opens, hV, rfl⟩, hyV, hVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open
      (mem_rankOpen f y) (rankOpen f y).2
  refine ⟨V, hV, hyV, ?_⟩
  let fV := f ∣_ V
  letI : IsAffine V.toScheme := hV
  letI : Etale fV := inferInstance
  letI : IsFinite fV := inferInstance
  letI : IsAffine (f ⁻¹ᵁ V).toScheme := isAffine_of_isAffineHom fV
  have hRank : fV.finrank = fun _ ↦ f.finrank y := by
    funext z
    rw [Scheme.Hom.finrank_of_isPullback
      (f ⁻¹ᵁ V).ι fV f V.ι (isPullback_morphismRestrict f V).flip]
    exact hVU z.2
  exact AffineFiniteEtaleSplitChart.exists_fpqc_splitCover
    fV (f.finrank y) hRank

end MazurTorsion.AlgebraicGeometry.Jacobian.FiniteEtalePointSplitChart
