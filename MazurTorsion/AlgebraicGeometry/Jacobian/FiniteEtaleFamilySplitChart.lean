/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.EtaleSplitChart

/-!
# Simultaneous splitting of a finite family of finite étale algebras

A finite family of constant-rank finite étale algebras becomes split over
one finite étale fpqc extension.  The construction successively splits one
member after base-changing the remaining family; earlier splittings survive
each later extension.

The named downstream consumer is the finite-support curve-coordinate chart
used in `PointedIncidenceDescent`.
-/

noncomputable section

universe u

open scoped TensorProduct

namespace MazurTorsion.AlgebraicGeometry.Jacobian.FiniteEtaleFamilySplitChart

/-- A finite family of constant-rank finite étale algebras has a common
finite étale faithfully flat splitting extension. -/
theorem exists_common_splitCover
    (R : Type u) [CommRing R]
    (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Algebra.Etale R (A i)] [∀ i, Module.Finite R (A i)]
    (rank : Fin n → ℕ)
    (hRank : ∀ i, Module.rankAtStalk (R := R) (A i) = rank i) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T)
      (_ : Module.FaithfullyFlat R T) (_ : Module.Finite R T)
      (_ : Algebra.Etale R T),
      ∀ i, Algebra.IsFiniteSplit T (T ⊗[R] A i) := by
  induction n with
  | zero =>
      refine ⟨R, inferInstance, inferInstance, inferInstance, inferInstance,
        inferInstance, ?_⟩
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      have hTailRank : ∀ i : Fin n,
          Module.rankAtStalk (R := R) (A i.succ) = rank i.succ :=
        fun i ↦ hRank i.succ
      obtain ⟨S, _, _, _, _, _, hTailSplit⟩ :=
        ih (fun i ↦ A i.succ) (fun i ↦ rank i.succ) hTailRank
      have hHeadRank :
          Module.rankAtStalk (R := S) (S ⊗[R] A 0) = rank 0 := by
        funext p
        rw [Module.rankAtStalk_baseChange]
        exact congrFun (hRank 0) (p.comap (algebraMap R S))
      obtain ⟨T, _, _, _, _, _, hHeadSplit⟩ :=
        Algebra.IsFiniteSplit.exists_tensorProduct_of_etale hHeadRank
      algebraize [(algebraMap S T).comp (algebraMap R S)]
      have hFaithfullyFlat : Module.FaithfullyFlat R T :=
        Module.FaithfullyFlat.trans R S T
      have hFinite : Module.Finite R T := Module.Finite.trans S T
      have hEtale : Algebra.Etale R T := Algebra.Etale.comp R S T
      refine ⟨T, inferInstance, inferInstance, hFaithfullyFlat, hFinite, hEtale, ?_⟩
      intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · letI : Algebra.IsFiniteSplit T (T ⊗[S] (S ⊗[R] A 0)) :=
          hHeadSplit
        exact Algebra.IsFiniteSplit.of_algEquiv
          (Algebra.TensorProduct.cancelBaseChange R S T T (A 0))
      · letI : Algebra.IsFiniteSplit S (S ⊗[R] A j.succ) :=
          hTailSplit j
        exact Algebra.IsFiniteSplit.of_algEquiv
          (Algebra.TensorProduct.cancelBaseChange R S T T (A j.succ))

end MazurTorsion.AlgebraicGeometry.Jacobian.FiniteEtaleFamilySplitChart
