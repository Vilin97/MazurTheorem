/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.AffineFiniteEtaleFamilySplitChart
import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteFlatConstantRankNeighborhood

/-!
# Pointwise common split charts for finite families

For finitely many finite étale morphisms over one scheme and a chosen base
point, intersect their clopen constant-rank loci and choose an affine
subneighborhood.  One finite étale fpqc cover of that affine neighborhood
then splits every restricted morphism simultaneously.

The named downstream consumer is the common curve-coordinate neighborhood
for the finite support of a divisor in `PointedIncidenceDescent`.
-/

noncomputable section

universe u

open scoped TensorProduct
open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.FiniteEtaleFamilyPointSplitChart

open FiniteFlatConstantRankNeighborhood

/-- Around a chosen base point, a finite family of finite étale morphisms
has one affine constant-rank neighborhood and one common split fpqc cover. -/
theorem exists_affineOpen_fpqc_common_splitCover
    {Y : Scheme.{u}} (n : ℕ) (X : Fin n → Scheme.{u})
    (f : ∀ i, X i ⟶ Y) [∀ i, Etale (f i)] [∀ i, IsFinite (f i)]
    (y : Y) :
    ∃ (V : Y.Opens) (hV : IsAffineOpen V), y ∈ V ∧
      let fV : ∀ i, (f i ⁻¹ᵁ V).toScheme ⟶ V.toScheme :=
        fun i ↦ f i ∣_ V
      letI : IsAffine V.toScheme := hV
      letI (i : Fin n) : IsAffine (f i ⁻¹ᵁ V).toScheme :=
        isAffine_of_isAffineHom (fV i)
      letI (i : Fin n) : Algebra Γ(V, ⊤) Γ(f i ⁻¹ᵁ V, ⊤) :=
        (fV i).appTop.hom.toAlgebra
      ∃ (T : Type u) (_ : CommRing T) (_ : Algebra Γ(V, ⊤) T)
        (_ : Module.FaithfullyFlat Γ(V, ⊤) T)
        (_ : Module.Finite Γ(V, ⊤) T)
        (_ : Algebra.Etale Γ(V, ⊤) T)
        (q : Spec (.of T) ⟶ V.toScheme),
        Flat q ∧ Surjective q ∧ QuasiCompact q ∧
          ∀ i, ∃ (m : ℕ)
            (_e : T ⊗[Γ(V, ⊤)] Γ(f i ⁻¹ᵁ V, ⊤) ≃ₐ[T] (Fin m → T)),
            ∃ E : pullback (fV i) q ≅ Spec (.of (Fin m → T)),
              E.hom ≫ EtaleSplitChart.splitProjection T m =
                pullback.snd (fV i) q := by
  letI (i : Fin n) : Flat (f i) := inferInstance
  letI (i : Fin n) : LocallyOfFinitePresentation (f i) := inferInstance
  let U : Y.Opens := ⨅ i, rankOpen (f i) y
  have hUset : (U : Set Y) = ⋂ i, (rankOpen (f i) y : Set Y) := by
    dsimp only [U]
    exact TopologicalSpace.Opens.coe_iInf _
  have hyU : y ∈ U := by
    change y ∈ (U : Set Y)
    rw [hUset, Set.mem_iInter]
    exact fun i ↦ mem_rankOpen (f i) y
  obtain ⟨_, ⟨V : Y.Opens, hV, rfl⟩, hyV, hVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hyU U.2
  refine ⟨V, hV, hyV, ?_⟩
  let fV : ∀ i, (f i ⁻¹ᵁ V).toScheme ⟶ V.toScheme :=
    fun i ↦ f i ∣_ V
  letI : IsAffine V.toScheme := hV
  letI (i : Fin n) : Etale (fV i) := inferInstance
  letI (i : Fin n) : IsFinite (fV i) := inferInstance
  letI (i : Fin n) : IsAffine (f i ⁻¹ᵁ V).toScheme :=
    isAffine_of_isAffineHom (fV i)
  have hRank : ∀ i, (fV i).finrank = fun _ ↦ (f i).finrank y := by
    intro i
    funext z
    rw [Scheme.Hom.finrank_of_isPullback
      (f i ⁻¹ᵁ V).ι (fV i) (f i) V.ι
        (isPullback_morphismRestrict (f i) V).flip]
    have hzU : V.ι z ∈ (U : Set Y) := hVU z.2
    have hzAll : ∀ i, V.ι z ∈ rankOpen (f i) y := by
      rw [hUset, Set.mem_iInter] at hzU
      exact hzU
    have hzRank : V.ι z ∈ rankOpen (f i) y := hzAll i
    exact hzRank
  exact AffineFiniteEtaleFamilySplitChart.exists_fpqc_common_splitCover
    n (fun i ↦ (f i ⁻¹ᵁ V).toScheme) fV
      (fun i ↦ (f i).finrank y) hRank

end MazurTorsion.AlgebraicGeometry.Jacobian.FiniteEtaleFamilyPointSplitChart
