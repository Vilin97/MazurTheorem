/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.EtaleSplitChart
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# Fpqc splitting of affine finite étale morphisms

For an affine finite étale morphism of constant rank, pass to global
sections, apply finite-étale splitting, and transport the resulting pullback
isomorphism back through the canonical affine `isoSpec` squares.  The output
is an fpqc affine cover of the original target on which the original scheme
morphism is a finite disjoint union of copies of the cover.

The named downstream consumer is the split ordered-incidence chart in
`PointedIncidenceDescent`.
-/

noncomputable section

universe u

open scoped TensorProduct
open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.AffineFiniteEtaleSplitChart

/-- An affine finite étale morphism of constant rank splits after an affine
fpqc finite étale cover of its target. -/
theorem exists_fpqc_splitCover
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [Etale f] [IsFinite f]
    (n : ℕ) (hn : f.finrank = fun _ ↦ n) :
    letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    ∃ (T : Type u) (_ : CommRing T)
      (_ : Algebra Γ(Y, ⊤) T)
      (_ : Module.FaithfullyFlat Γ(Y, ⊤) T)
      (_ : Module.Finite Γ(Y, ⊤) T)
      (_ : Algebra.Etale Γ(Y, ⊤) T) (m : ℕ)
      (_e : T ⊗[Γ(Y, ⊤)] Γ(X, ⊤) ≃ₐ[T] (Fin m → T))
      (q : Spec (.of T) ⟶ Y)
      (_E : pullback f q ≅ Spec (.of (Fin m → T))),
      _E.hom ≫ EtaleSplitChart.splitProjection T m = pullback.snd f q ∧
        Flat q ∧ Surjective q ∧ QuasiCompact q := by
  letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  have hfEtale : f.appTop.hom.Etale :=
    HasRingHomProperty.appTop (P := @Etale) (Q := RingHom.Etale)
      f (inferInstance : Etale f)
  letI : Algebra.Etale Γ(Y, ⊤) Γ(X, ⊤) := hfEtale.toAlgebra
  have hfFinite : f.appTop.hom.Finite := f.finite_appTop
  letI : Module.Finite Γ(Y, ⊤) Γ(X, ⊤) := by
    rw [← RingHom.finite_algebraMap]
    simpa only [RingHom.algebraMap_toAlgebra] using hfFinite
  letI : Etale (Spec.map f.appTop) :=
    HasRingHomProperty.Spec_iff.mpr hfEtale
  letI : IsFinite (Spec.map f.appTop) :=
    (IsFinite.SpecMap_iff f.appTop).mpr hfFinite
  have hsquare : IsPullback X.isoSpec.hom f
      (Spec.map f.appTop) Y.isoSpec.hom :=
    IsPullback.of_horiz_isIso ⟨Scheme.isoSpec_hom_naturality f⟩
  have hRank : Module.rankAtStalk (R := Γ(Y, ⊤)) Γ(X, ⊤) = n := by
    funext p
    rw [← Scheme.Hom.finrank_SpecMap_algebraMap Γ(Y, ⊤) Γ(X, ⊤) p]
    change (Spec.map f.appTop).finrank p = n
    calc
      _ = f.finrank (Y.isoSpec.inv p) := by
        symm
        have h := Scheme.Hom.finrank_of_isPullback
          X.isoSpec.hom f (Spec.map f.appTop) Y.isoSpec.hom
          hsquare (Y.isoSpec.inv p)
        have hp : Y.isoSpec.hom (Y.isoSpec.inv p) = p := by
          have hp' :=
            congrArg (fun h : Spec (.of Γ(Y, ⊤)) ⟶ Spec (.of Γ(Y, ⊤)) ↦ h p)
              Y.isoSpec.inv_hom_id
          change Y.isoSpec.hom (Y.isoSpec.inv p) = p at hp'
          exact hp'
        simpa only [hp] using h
      _ = n := congrFun hn (Y.isoSpec.inv p)
  obtain ⟨T, _, _, _, _, _, m, e, EΓ, hEΓ, hflat, hsurjective, hqc⟩ :=
    EtaleSplitChart.exists_fpqc_splitCover
      Γ(Y, ⊤) Γ(X, ⊤) n hRank
  let fΓ : Spec (.of Γ(X, ⊤)) ⟶ Spec (.of Γ(Y, ⊤)) :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) Γ(X, ⊤)))
  let qΓ : Spec (.of T) ⟶ Spec (.of Γ(Y, ⊤)) :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) T))
  let q : Spec (.of T) ⟶ Y := qΓ ≫ Y.isoSpec.inv
  change EΓ.hom ≫ EtaleSplitChart.splitProjection T m =
    pullback.snd fΓ qΓ at hEΓ
  let compare : pullback f q ⟶
      pullback fΓ qΓ :=
    pullback.map f q fΓ qΓ
      X.isoSpec.hom (𝟙 _) Y.isoSpec.hom
      (by
        dsimp only [fΓ]
        exact (Scheme.isoSpec_hom_naturality f).symm)
      (by simp [q])
  haveI : IsIso compare := by
    dsimp only [compare]
    infer_instance
  let E' : pullback f q ≅ Spec (.of (Fin m → T)) :=
    asIso compare ≪≫ EΓ
  refine ⟨T, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, m, e, q, E', ?_, ?_, ?_, ?_⟩
  · calc
      E'.hom ≫ EtaleSplitChart.splitProjection T m =
          compare ≫ EΓ.hom ≫ EtaleSplitChart.splitProjection T m := by
            rfl
      _ = compare ≫ pullback.snd fΓ qΓ := by
        rw [hEΓ]
      _ = pullback.snd f q := by
        dsimp only [compare]
        simp only [pullback.map, pullback.lift_snd, Category.comp_id]
  · dsimp only [q]
    infer_instance
  · dsimp only [q]
    infer_instance
  · dsimp only [q]
    infer_instance

end MazurTorsion.AlgebraicGeometry.Jacobian.AffineFiniteEtaleSplitChart
