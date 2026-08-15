/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteEtaleFamilySplitChart
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# One split fpqc chart for a finite family of affine finite étale morphisms

A finite family of affine finite étale morphisms of constant rank over one
affine scheme becomes a family of split finite sets after one affine finite
étale fpqc cover.  This is the scheme-level finite-support assembly needed
before comparing curve incidence with the explicit split monic-root model.

The named downstream consumer is the split ordered-incidence chart in
`PointedIncidenceDescent`.
-/

noncomputable section

universe u

open scoped TensorProduct
open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.AffineFiniteEtaleFamilySplitChart

/-- A finite family of affine constant-rank finite étale morphisms splits
after one affine finite étale fpqc cover of the common target. -/
theorem exists_fpqc_common_splitCover
    {Y : Scheme.{u}} [IsAffine Y]
    (n : ℕ) (X : Fin n → Scheme.{u}) [∀ i, IsAffine (X i)]
    (f : ∀ i, X i ⟶ Y) [∀ i, Etale (f i)] [∀ i, IsFinite (f i)]
    (rank : Fin n → ℕ)
    (hRank : ∀ i, (f i).finrank = fun _ ↦ rank i) :
    letI (i : Fin n) : Algebra Γ(Y, ⊤) Γ(X i, ⊤) :=
      (f i).appTop.hom.toAlgebra
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra Γ(Y, ⊤) T)
      (_ : Module.FaithfullyFlat Γ(Y, ⊤) T)
      (_ : Module.Finite Γ(Y, ⊤) T)
      (_ : Algebra.Etale Γ(Y, ⊤) T)
      (q : Spec (.of T) ⟶ Y),
      Flat q ∧ Surjective q ∧ QuasiCompact q ∧
        ∀ i, ∃ (m : ℕ)
          (_e : T ⊗[Γ(Y, ⊤)] Γ(X i, ⊤) ≃ₐ[T] (Fin m → T)),
          Nonempty (pullback (f i) q ≅ Spec (.of (Fin m → T))) := by
  letI (i : Fin n) : Algebra Γ(Y, ⊤) Γ(X i, ⊤) :=
    (f i).appTop.hom.toAlgebra
  letI (i : Fin n) : Algebra.Etale Γ(Y, ⊤) Γ(X i, ⊤) :=
    (HasRingHomProperty.appTop (P := @Etale) (Q := RingHom.Etale)
      (f i) (inferInstance : Etale (f i))).toAlgebra
  letI (i : Fin n) : Module.Finite Γ(Y, ⊤) Γ(X i, ⊤) := by
    rw [← RingHom.finite_algebraMap]
    simpa only [RingHom.algebraMap_toAlgebra] using (f i).finite_appTop
  have hSectionRank : ∀ i,
      Module.rankAtStalk (R := Γ(Y, ⊤)) Γ(X i, ⊤) = rank i := by
    intro i
    have hfEtale : (f i).appTop.hom.Etale :=
      HasRingHomProperty.appTop (P := @Etale) (Q := RingHom.Etale)
        (f i) (inferInstance : Etale (f i))
    have hfFinite : (f i).appTop.hom.Finite := (f i).finite_appTop
    letI : Etale (Spec.map (f i).appTop) :=
      HasRingHomProperty.Spec_iff.mpr hfEtale
    letI : IsFinite (Spec.map (f i).appTop) :=
      (IsFinite.SpecMap_iff (f i).appTop).mpr hfFinite
    have hsquare : IsPullback (X i).isoSpec.hom (f i)
        (Spec.map (f i).appTop) Y.isoSpec.hom :=
      IsPullback.of_horiz_isIso ⟨Scheme.isoSpec_hom_naturality (f i)⟩
    funext p
    rw [← Scheme.Hom.finrank_SpecMap_algebraMap Γ(Y, ⊤) Γ(X i, ⊤) p]
    change (Spec.map (f i).appTop).finrank p = rank i
    calc
      _ = (f i).finrank (Y.isoSpec.inv p) := by
        symm
        have h := Scheme.Hom.finrank_of_isPullback
          (X i).isoSpec.hom (f i) (Spec.map (f i).appTop) Y.isoSpec.hom
          hsquare (Y.isoSpec.inv p)
        have hp : Y.isoSpec.hom (Y.isoSpec.inv p) = p := by
          have hp' :=
            congrArg
              (fun h : Spec (.of Γ(Y, ⊤)) ⟶ Spec (.of Γ(Y, ⊤)) ↦ h p)
              Y.isoSpec.inv_hom_id
          change Y.isoSpec.hom (Y.isoSpec.inv p) = p at hp'
          exact hp'
        simpa only [hp] using h
      _ = rank i := congrFun (hRank i) (Y.isoSpec.inv p)
  obtain ⟨T, _, _, _, _, _, hSplit⟩ :=
    FiniteEtaleFamilySplitChart.exists_common_splitCover
      Γ(Y, ⊤) n (fun i ↦ Γ(X i, ⊤)) rank hSectionRank
  let qΓ : Spec (.of T) ⟶ Spec (.of Γ(Y, ⊤)) :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) T))
  let q : Spec (.of T) ⟶ Y := qΓ ≫ Y.isoSpec.inv
  have hqΓ : Flat qΓ ∧ Surjective qΓ := by
    apply (flat_and_surjective_SpecMap_iff
      (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) T))).mpr
    change (algebraMap Γ(Y, ⊤) T).FaithfullyFlat
    rw [RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  letI : Flat qΓ := hqΓ.1
  letI : Surjective qΓ := hqΓ.2
  refine ⟨T, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, q, ?_, ?_, ?_, ?_⟩
  · dsimp only [q]
    infer_instance
  · dsimp only [q]
    infer_instance
  · dsimp only [q]
    infer_instance
  · intro i
    obtain ⟨m, ⟨e⟩⟩ := (hSplit i).nonempty_algEquiv_fun
    let e' : Γ(X i, ⊤) ⊗[Γ(Y, ⊤)] T ≃ₐ[Γ(Y, ⊤)] (Fin m → T) :=
      (Algebra.TensorProduct.comm Γ(Y, ⊤) Γ(X i, ⊤) T).trans
        (e.restrictScalars Γ(Y, ⊤))
    let eSpec : Spec (.of (Γ(X i, ⊤) ⊗[Γ(Y, ⊤)] T)) ≅
        Spec (.of (Fin m → T)) :=
      (Scheme.Spec.mapIso e'.toRingEquiv.toCommRingCatIso.op).symm
    let EΓ : pullback (Spec.map (f i).appTop) qΓ ≅
        Spec (.of (Fin m → T)) :=
      pullbackSpecIso Γ(Y, ⊤) Γ(X i, ⊤) T ≪≫ eSpec
    let compare : pullback (f i) q ⟶
        pullback (Spec.map (f i).appTop) qΓ :=
      pullback.map (f i) q (Spec.map (f i).appTop) qΓ
        (X i).isoSpec.hom (𝟙 _) Y.isoSpec.hom
        (Scheme.isoSpec_hom_naturality (f i)).symm (by simp [q])
    haveI : IsIso compare := by
      dsimp only [compare]
      infer_instance
    exact ⟨m, e, ⟨asIso compare ≪≫ EΓ⟩⟩

end MazurTorsion.AlgebraicGeometry.Jacobian.AffineFiniteEtaleFamilySplitChart
