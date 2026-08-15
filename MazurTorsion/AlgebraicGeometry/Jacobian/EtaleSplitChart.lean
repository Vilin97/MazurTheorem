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

/-- The structure morphism of a split finite scheme: the spectrum of a
finite product of copies of `T` maps to `Spec T` through the diagonal
`T`-algebra structure. -/
noncomputable def splitProjection (T : Type u) [CommRing T] (m : ℕ) :
    Spec (.of (Fin m → T)) ⟶ Spec (.of T) :=
  Spec.map (CommRingCat.ofHom (algebraMap T (Fin m → T)))

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
        _E.hom ≫ splitProjection T m = pullback.snd f q ∧
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
    inferInstance, m, e, E, ?_, ?_⟩
  · dsimp only [E]
    simp only [Iso.trans_hom, Category.assoc]
    rw [show eSpec.hom ≫ splitProjection T m =
        Spec.map (CommRingCat.ofHom
          ((Algebra.TensorProduct.includeRight :
            T →ₐ[R] A ⊗[R] T).toRingHom)) by
      dsimp only [eSpec, splitProjection]
      change Spec.map e'.symm.toRingEquiv.toCommRingCatIso.hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap T (Fin m → T))) =
        Spec.map (CommRingCat.ofHom
          ((Algebra.TensorProduct.includeRight :
            T →ₐ[R] A ⊗[R] T).toRingHom))
      rw [← Spec.map_comp, Spec.map_inj]
      apply CommRingCat.hom_ext
      apply RingHom.ext fun t ↦ ?_
      simp [e']]
    exact pullbackSpecIso_hom_snd R A T
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
