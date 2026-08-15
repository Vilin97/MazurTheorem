/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.RingTheory.TotallySplit

/-!
# Splitting finite étale charts fpqc-locally

A finite étale affine morphism becomes a disjoint union of copies of its
base after a finite faithfully flat étale extension.  This file packages the
commutative-algebra splitting theorem as the exact scheme-level fpqc chart
needed for the local symmetric-power calculation.

The named downstream consumer is the higher-degree monic-root comparison in
`PointedIncidenceDescent`.
-/

noncomputable section

universe u

open scoped TensorProduct
open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.EtaleSplitChart

/-- A finite étale algebra of constant rank becomes a finite disjoint union
of the base after a finite fpqc étale extension. -/
theorem exists_fpqc_splitCover
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.Etale R A] [Module.Finite R A]
    (n : ℕ) (hn : Module.rankAtStalk (R := R) A = n) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T)
      (_ : Module.FaithfullyFlat R T) (_ : Module.Finite R T)
      (_ : Algebra.Etale R T) (m : ℕ)
      (_e : T ⊗[R] A ≃ₐ[T] (Fin m → T)),
      let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
      let q := Spec.map (CommRingCat.ofHom (algebraMap R T))
      ∃ _E : pullback f q ≅ Spec (.of (Fin m → T)),
        Flat q ∧ Surjective q ∧ QuasiCompact q := by
  obtain ⟨T, _, _, _, _, _, hsplit⟩ :=
    Algebra.IsFiniteSplit.exists_tensorProduct_of_etale hn
  letI : Algebra.IsFiniteSplit T (T ⊗[R] A) := hsplit
  obtain ⟨m, ⟨e⟩⟩ :=
    Algebra.IsFiniteSplit.nonempty_algEquiv_fun T (T ⊗[R] A)
  let e' : A ⊗[R] T ≃ₐ[R] (Fin m → T) :=
    (Algebra.TensorProduct.comm R A T).trans (e.restrictScalars R)
  let eSpec : Spec (.of (A ⊗[R] T)) ≅ Spec (.of (Fin m → T)) :=
    (Scheme.Spec.mapIso e'.toRingEquiv.toCommRingCatIso.op).symm
  let E : pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom (algebraMap R T))) ≅
      Spec (.of (Fin m → T)) :=
    pullbackSpecIso R A T ≪≫ eSpec
  refine ⟨T, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, m, e, E, ?_⟩
  have hq : Flat
        (Spec.map (CommRingCat.ofHom (algebraMap R T))) ∧
      Surjective (Spec.map (CommRingCat.ofHom (algebraMap R T))) := by
    apply (flat_and_surjective_SpecMap_iff
      (CommRingCat.ofHom (algebraMap R T))).mpr
    change (algebraMap R T).FaithfullyFlat
    rw [RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  exact ⟨hq.1, hq.2, inferInstance⟩

end MazurTorsion.AlgebraicGeometry.Jacobian.EtaleSplitChart
