/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.SplitFiniteBaseChange

/-!
# Affine presentation of a split finite family

Over an affine scheme, the intrinsic coproduct presentation of a split
finite object is the spectrum of a finite product of global sections.  The
isomorphism below records the exact square with the base's canonical
`isoSpec` map.

The named downstream consumer is the tuple-orbit component chart for the
coherent support family in `FiniteSupportEtaleCoordinates`.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.SplitFiniteAffinePresentation

open SplitFiniteBaseChange

/-- The underlying scheme of a split finite object over an affine scheme is
the standard product-ring spectrum. -/
noncomputable def splitFiniteAffineSchemeIso
    (S : Scheme.{u}) [IsAffine S] (m : ℕ) :
    (splitFinite S m).left ≅ Spec (.of (Fin m → Γ(S, ⊤))) :=
  Sigma.mapIso (fun _ : ULift.{u} (Fin m) ↦ S.isoSpec) ≪≫
    ((Over.forget (Spec (.of Γ(S, ⊤)))).mapIso
      (splitFiniteStandardSpecIso Γ(S, ⊤) m))

/-- The affine split presentation lies over the canonical affine
presentation of the base. -/
theorem splitFiniteAffineSchemeIso_hom_comp_projection
    (S : Scheme.{u}) [IsAffine S] (m : ℕ) :
    (splitFiniteAffineSchemeIso S m).hom ≫
        EtaleSplitChart.splitProjection Γ(S, ⊤) m =
      (splitFinite S m).hom ≫ S.isoSpec.hom := by
  let eBase : (∐ fun _ : ULift.{u} (Fin m) ↦ S) ≅
      (∐ fun _ : ULift.{u} (Fin m) ↦ Spec (.of Γ(S, ⊤))) :=
    Sigma.mapIso (fun _ : ULift.{u} (Fin m) ↦ S.isoSpec)
  let eSplit : (∐ fun _ : ULift.{u} (Fin m) ↦ Spec (.of Γ(S, ⊤))) ≅
      Spec (.of (Fin m → Γ(S, ⊤))) :=
    (Over.forget (Spec (.of Γ(S, ⊤)))).mapIso
      (splitFiniteStandardSpecIso Γ(S, ⊤) m)
  have hBase (i : ULift.{u} (Fin m)) :
      Sigma.ι (fun _ : ULift.{u} (Fin m) ↦ S) i ≫ eBase.hom =
        S.isoSpec.hom ≫
          Sigma.ι (fun _ : ULift.{u} (Fin m) ↦ Spec (.of Γ(S, ⊤))) i :=
    Sigma.ι_mapIso_hom (fun _ : ULift.{u} (Fin m) ↦ S.isoSpec) i
  have hSplit : eSplit.hom ≫
        EtaleSplitChart.splitProjection Γ(S, ⊤) m =
      (splitFinite (Spec (.of Γ(S, ⊤))) m).hom := by
    change (splitFiniteStandardSpecIso Γ(S, ⊤) m).hom.left ≫
        EtaleSplitChart.splitProjection Γ(S, ⊤) m =
      (splitFinite (Spec (.of Γ(S, ⊤))) m).hom
    exact splitFiniteStandardSpecIso_hom_comp_projection Γ(S, ⊤) m
  change (eBase ≪≫ eSplit).hom ≫
      EtaleSplitChart.splitProjection Γ(S, ⊤) m =
    (splitFinite S m).hom ≫ S.isoSpec.hom
  apply Sigma.hom_ext
  intro i
  calc
    Sigma.ι (fun _ : ULift.{u} (Fin m) ↦ S) i ≫
          (eBase ≪≫ eSplit).hom ≫
            EtaleSplitChart.splitProjection Γ(S, ⊤) m =
        (Sigma.ι (fun _ : ULift.{u} (Fin m) ↦ S) i ≫ eBase.hom) ≫
          eSplit.hom ≫ EtaleSplitChart.splitProjection Γ(S, ⊤) m := by
            simp only [Iso.trans_hom, Category.assoc]
    _ = (S.isoSpec.hom ≫
          Sigma.ι (fun _ : ULift.{u} (Fin m) ↦ Spec (.of Γ(S, ⊤))) i) ≫
        eSplit.hom ≫ EtaleSplitChart.splitProjection Γ(S, ⊤) m := by
          rw [hBase]
    _ = S.isoSpec.hom ≫
        Sigma.ι (fun _ : ULift.{u} (Fin m) ↦ Spec (.of Γ(S, ⊤))) i ≫
          (splitFinite (Spec (.of Γ(S, ⊤))) m).hom := by
            simp only [Category.assoc, hSplit]
    _ = S.isoSpec.hom := by
      change (S.isoSpec.hom ≫
          Sigma.ι (fun _ : ULift.{u} (Fin m) ↦ Spec (.of Γ(S, ⊤))) i) ≫
        Sigma.desc (fun _ : ULift.{u} (Fin m) ↦
          𝟙 (Spec (.of Γ(S, ⊤)))) = S.isoSpec.hom
      simp only [Category.assoc, Sigma.ι_desc]
      exact Category.comp_id _
    _ = Sigma.ι (fun _ : ULift.{u} (Fin m) ↦ S) i ≫
        (splitFinite S m).hom ≫ S.isoSpec.hom := by
          change S.isoSpec.hom =
            (Sigma.ι (fun _ : ULift.{u} (Fin m) ↦ S) i ≫
              Sigma.desc (fun _ : ULift.{u} (Fin m) ↦ 𝟙 S)) ≫
                S.isoSpec.hom
          simp only [Sigma.ι_desc, Category.id_comp]

/-- Package the affine presentation as an isomorphism over
`Spec Γ(S, O_S)`, after composing the split object's structure map with the
canonical affine-base isomorphism. -/
noncomputable def splitFiniteAffineOverIso
    (S : Scheme.{u}) [IsAffine S] (m : ℕ) :
    Over.mk ((splitFinite S m).hom ≫ S.isoSpec.hom) ≅
      Over.mk (EtaleSplitChart.splitProjection Γ(S, ⊤) m) :=
  Over.isoMk (splitFiniteAffineSchemeIso S m)
    (splitFiniteAffineSchemeIso_hom_comp_projection S m)

end MazurTorsion.AlgebraicGeometry.Jacobian.SplitFiniteAffinePresentation
