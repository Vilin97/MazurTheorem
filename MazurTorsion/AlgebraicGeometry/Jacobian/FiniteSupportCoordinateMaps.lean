/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteSupportEtaleCoordinates

/-!
# Coordinate maps on coherent finite-support charts

Every selected finite étale support component comes from an étale chart over
the affine line.  This file follows that coordinate through the common-base
pullback, restriction, fpqc cover, and coherent product-base construction.
The resulting equation says that the coordinate of every point on a coherent
component is pulled back from the matching coordinate of the coherent base.

The named downstream consumer is the curve-level split incidence comparison
in `PointedIncidenceDescent`.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.FiniteSupportCoordinateMaps

open FiniteSupportEtaleCoordinates
open SmoothCurveEtaleCoordinate
open SplitFiniteBaseChange

variable (K : Type u) [Field K]
variable (C : Over (Spec (.of K)))
variable [SmoothOfRelativeDimension 1 C.hom]

/-- The `i`-th affine-line coordinate on the common product base. -/
noncomputable def commonBaseToCoordinateLine
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) (i : Fin d) :
    (commonBase K C d z c n).left ⟶ Spec (.of (coordinateRing K)) :=
  (Pi.π (fun j : Fin d ↦ (n j).baseOver) i).left ≫ (n i).baseMap

/-- The coordinate of the `i`-th pulled component, obtained by returning to
its affine curve chart and then applying the chosen étale coordinate. -/
noncomputable def pulledComponentToCoordinateLine
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) (i : Fin d) :
    (pulledComponentOverCommonBase K C d z c n i).left ⟶
      Spec (.of (coordinateRing K)) :=
  pullback.fst (n i).componentToBase.left
      (Pi.π (fun j : Fin d ↦ (n j).baseOver) i).left ≫
    (n i).componentToChart ≫ (c i).schemeMap

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- On a pulled support component, the affine-line coordinate is exactly the
matching coordinate pulled back from the common product base. -/
theorem pulledComponentToCoordinateLine_eq
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) (i : Fin d) :
    pulledComponentToCoordinateLine K C d z c n i =
      (pulledComponentOverCommonBase K C d z c n i).hom ≫
        commonBaseToCoordinateLine K C d z c n i := by
  let f := (n i).componentToBase.left
  let π := (Pi.π (fun j : Fin d ↦ (n j).baseOver) i).left
  have hComponent : (n i).componentToChart ≫ (c i).schemeMap =
      f ≫ (n i).baseMap :=
    (n i).componentToChart_comp_schemeMap
  have hPullback : pullback.fst f π ≫ f =
      pullback.snd f π ≫ π := pullback.condition
  have hOuter : pullback.fst f π ≫ (f ≫ (n i).baseMap) =
      pullback.snd f π ≫ (π ≫ (n i).baseMap) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun a ↦ a ≫ (n i).baseMap) hPullback).trans
        (Category.assoc _ _ _))
  change pullback.fst f π ≫
      ((n i).componentToChart ≫ (c i).schemeMap) =
    pullback.snd f π ≫ (π ≫ (n i).baseMap)
  exact (congrArg (fun a ↦ pullback.fst f π ≫ a) hComponent).trans hOuter

/-- The `i`-th coordinate restricted to a common-base open. -/
noncomputable def restrictedBaseToCoordinateLine
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens) (i : Fin d) :
    V.toScheme ⟶ Spec (.of (coordinateRing K)) :=
  V.ι ≫ commonBaseToCoordinateLine K C d z c n i

/-- The affine-line coordinate on the restriction of one pulled component. -/
noncomputable def restrictedPulledComponentToCoordinateLine
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens) (i : Fin d) :
    ((pulledComponentOverCommonBase K C d z c n i).hom ⁻¹ᵁ V).toScheme ⟶
      Spec (.of (coordinateRing K)) :=
  ((pulledComponentOverCommonBase K C d z c n i).hom ⁻¹ᵁ V).ι ≫
    pulledComponentToCoordinateLine K C d z c n i

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- Restriction preserves the equation saying that the component coordinate
comes from its base coordinate. -/
theorem restrictedPulledComponentToCoordinateLine_eq
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens) (i : Fin d) :
    restrictedPulledComponentToCoordinateLine K C d z c n V i =
      restrictedPulledComponentToBase K C d z c n V i ≫
        restrictedBaseToCoordinateLine K C d z c n V i := by
  let j := ((pulledComponentOverCommonBase
    K C d z c n i).hom ⁻¹ᵁ V).ι
  let f := (pulledComponentOverCommonBase K C d z c n i).hom
  let r := restrictedPulledComponentToBase K C d z c n V i
  let v := V.ι
  let t := commonBaseToCoordinateLine K C d z c n i
  have hCoordinate := pulledComponentToCoordinateLine_eq K C d z c n i
  have hRestrict : r ≫ v = j ≫ f := by
    exact morphismRestrict_ι f V
  have hTail : j ≫ (f ≫ t) = r ≫ (v ≫ t) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun a ↦ a ≫ t) hRestrict.symm).trans
        (Category.assoc _ _ _))
  change j ≫ pulledComponentToCoordinateLine K C d z c n i =
    r ≫ (v ≫ t)
  exact (congrArg (fun a ↦ j ≫ a) hCoordinate).trans hTail

/-- The `i`-th affine-line coordinate on a further common fpqc cover. -/
noncomputable def fpqcBaseToCoordinateLine
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :
    (commonCoverOverGround K C d z c n V T q).left ⟶
      Spec (.of (coordinateRing K)) :=
  q ≫ restrictedBaseToCoordinateLine K C d z c n V i

/-- The coordinate on the `i`-th component after the common fpqc base
change. -/
noncomputable def fpqcPulledComponentToCoordinateLine
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :
    (fpqcPulledComponentOverGround K C d z c n V T q i).left ⟶
      Spec (.of (coordinateRing K)) :=
  (fpqcPulledComponentToRestrictedOverGround
      K C d z c n V T q i).left ≫
    restrictedPulledComponentToCoordinateLine K C d z c n V i

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- After the common fpqc base change, the component coordinate is still
pulled back from the matching coordinate of the cover. -/
theorem fpqcPulledComponentToCoordinateLine_eq
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :
    fpqcPulledComponentToCoordinateLine K C d z c n V T q i =
      (fpqcPulledComponentToCoverOverGround
        K C d z c n V T q i).left ≫
        fpqcBaseToCoordinateLine K C d z c n V T q i := by
  let a := (fpqcPulledComponentToRestrictedOverGround
    K C d z c n V T q i).left
  let b := (fpqcPulledComponentToCoverOverGround
    K C d z c n V T q i).left
  let f := restrictedPulledComponentToBase K C d z c n V i
  let r := restrictedBaseToCoordinateLine K C d z c n V i
  have hCoordinate := restrictedPulledComponentToCoordinateLine_eq
    K C d z c n V i
  have hPullback : a ≫ f = b ≫ q := by
    exact pullback.condition
  have hTail : a ≫ (f ≫ r) = b ≫ (q ≫ r) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun x ↦ x ≫ r) hPullback).trans
        (Category.assoc _ _ _))
  change a ≫ restrictedPulledComponentToCoordinateLine
      K C d z c n V i = b ≫ (q ≫ r)
  exact (congrArg (fun x ↦ a ≫ x) hCoordinate).trans hTail

/-- The matching affine-line coordinate on the coherent product of all
copies of the common fpqc cover. -/
noncomputable def coherentBaseToCoordinateLine
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :
    coherentFpqcBase K C d z c n V T q ⟶
      Spec (.of (coordinateRing K)) :=
  (Pi.π (commonCoverFamily K C d z c n V T q) i).left ≫
    fpqcBaseToCoordinateLine K C d z c n V T q i

/-- The affine-line coordinate on one component over the coherent product
base. -/
noncomputable def coherentPulledComponentToCoordinateLine
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :
    (coherentFpqcPulledComponent K C d z c n V T q i).left ⟶
      Spec (.of (coordinateRing K)) :=
  pullback.fst
      (fpqcPulledComponentToCoverOverGround K C d z c n V T q i).left
      (Pi.π (commonCoverFamily K C d z c n V T q) i).left ≫
    fpqcPulledComponentToCoordinateLine K C d z c n V T q i

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- On every coherent component, the curve coordinate is exactly the
matching coordinate pulled back from the coherent product base. -/
theorem coherentPulledComponentToCoordinateLine_eq
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :
    coherentPulledComponentToCoordinateLine K C d z c n V T q i =
      (coherentFpqcPulledComponent K C d z c n V T q i).hom ≫
        coherentBaseToCoordinateLine K C d z c n V T q i := by
  let f := (fpqcPulledComponentToCoverOverGround
    K C d z c n V T q i).left
  let π := (Pi.π (commonCoverFamily K C d z c n V T q) i).left
  let a := pullback.fst f π
  let b := (coherentFpqcPulledComponent K C d z c n V T q i).hom
  let r := fpqcBaseToCoordinateLine K C d z c n V T q i
  have hCoordinate := fpqcPulledComponentToCoordinateLine_eq
    K C d z c n V T q i
  have hPullback : a ≫ f = b ≫ π := by
    exact pullback.condition
  have hTail : a ≫ (f ≫ r) = b ≫ (π ≫ r) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun x ↦ x ≫ r) hPullback).trans
        (Category.assoc _ _ _))
  change a ≫ fpqcPulledComponentToCoordinateLine
      K C d z c n V T q i = b ≫ (π ≫ r)
  exact (congrArg (fun x ↦ a ≫ x) hCoordinate).trans hTail

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- Under any split presentation of a coherent component, every sheet has
exactly the affine-line coordinate pulled back from the coherent base. -/
theorem coherentSplitSheetToCoordinateLine
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d)
    (m : ℕ)
    (E : coherentFpqcPulledComponent K C d z c n V T q i ≅
      splitFinite (coherentFpqcBase K C d z c n V T q) m)
    (j : Fin m) :
    (sheetInclusion (coherentFpqcBase K C d z c n V T q) m j).left ≫
        E.inv.left ≫
          coherentPulledComponentToCoordinateLine K C d z c n V T q i =
      coherentBaseToCoordinateLine K C d z c n V T q i := by
  let B := coherentFpqcBase K C d z c n V T q
  let X := coherentFpqcPulledComponent K C d z c n V T q i
  let a := (sheetInclusion B m j).left
  let e := E.inv.left
  let f := X.hom
  let r := coherentBaseToCoordinateLine K C d z c n V T q i
  have hCoordinate := coherentPulledComponentToCoordinateLine_eq
    K C d z c n V T q i
  have hIso : e ≫ f = (splitFinite B m).hom := E.inv.w
  have hSheet : a ≫ (splitFinite B m).hom = 𝟙 B :=
    (sheetInclusion B m j).w
  have hTail : (a ≫ e) ≫ (f ≫ r) = r := by
    calc
      (a ≫ e) ≫ (f ≫ r) = (a ≫ (e ≫ f)) ≫ r := by
        simp only [Category.assoc]
      _ = (a ≫ (splitFinite B m).hom) ≫ r := by rw [hIso]
      _ = (𝟙 B) ≫ r := by rw [hSheet]
      _ = r := Category.id_comp r
  change (a ≫ e) ≫
      coherentPulledComponentToCoordinateLine K C d z c n V T q i = r
  exact (congrArg (fun x ↦ (a ≫ e) ≫ x) hCoordinate).trans hTail

end MazurTorsion.AlgebraicGeometry.Jacobian.FiniteSupportCoordinateMaps
