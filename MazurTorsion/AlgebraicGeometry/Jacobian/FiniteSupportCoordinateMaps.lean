/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteSupportEtaleCoordinates
import MazurTorsion.AlgebraicGeometry.Jacobian.EtaleGraphCoproduct

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

/-- The map from a pulled component to its original affine curve chart. -/
noncomputable def pulledComponentToChart
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) (i : Fin d) :
    (pulledComponentOverCommonBase K C d z c n i).left ⟶
      ((c i).V : C.left.Opens).toScheme :=
  pullback.fst (n i).componentToBase.left
      (Pi.π (fun j : Fin d ↦ (n j).baseOver) i).left ≫
    (n i).componentToChart

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- Returning a pulled component to the curve chart and applying the chart
coordinate recovers its tracked affine-line coordinate. -/
theorem pulledComponentToChart_comp_schemeMap
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) (i : Fin d) :
    pulledComponentToChart K C d z c n i ≫ (c i).schemeMap =
      pulledComponentToCoordinateLine K C d z c n i := by
  exact Category.assoc _ _ _

/-- The selected finite component, after passage to the common base, as an
open-and-closed subspace of the base-changed étale curve chart. -/
noncomputable def pulledComponentToCoordinatePullback
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) (i : Fin d) :
    (pulledComponentOverCommonBase K C d z c n i).left ⟶
      pullback (c i).schemeMap (commonBaseToCoordinateLine K C d z c n i) := by
  let f : ((c i).V : C.left.Opens).toScheme ⟶
      Spec (.of (coordinateRing K)) :=
    (c i).schemeMap
  let g : (n i).base ⟶ Spec (.of (coordinateRing K)) := (n i).baseMap
  let π := (Pi.π (fun j : Fin d ↦ (n j).baseOver) i).left
  let j := (n i).selectedOpen.ι
  exact EtaleGraphCoproduct.baseChangedComponentInclusion f g π j

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- The open-and-closed component inclusion retains the actual map back to
the affine curve chart. -/
theorem pulledComponentToCoordinatePullback_fst
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) (i : Fin d) :
    pulledComponentToCoordinatePullback K C d z c n i ≫
      pullback.fst (c i).schemeMap
          (commonBaseToCoordinateLine K C d z c n i) =
      pulledComponentToChart K C d z c n i := by
  let f : ((c i).V : C.left.Opens).toScheme ⟶
      Spec (.of (coordinateRing K)) :=
    (c i).schemeMap
  let g : (n i).base ⟶ Spec (.of (coordinateRing K)) := (n i).baseMap
  let π := (Pi.π (fun j : Fin d ↦ (n j).baseOver) i).left
  let j := (n i).selectedOpen.ι
  change EtaleGraphCoproduct.baseChangedComponentInclusion f g π j ≫
      pullback.fst f (π ≫ g) =
    pullback.fst (j ≫ pullback.snd f g) π ≫
      j ≫ pullback.fst f g
  exact EtaleGraphCoproduct.baseChangedComponentInclusion_fst f g π j

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- The open-and-closed component inclusion retains the projection to the
common support base. -/
theorem pulledComponentToCoordinatePullback_snd
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) (i : Fin d) :
    pulledComponentToCoordinatePullback K C d z c n i ≫
      pullback.snd (c i).schemeMap
          (commonBaseToCoordinateLine K C d z c n i) =
      (pulledComponentOverCommonBase K C d z c n i).hom := by
  let f : ((c i).V : C.left.Opens).toScheme ⟶
      Spec (.of (coordinateRing K)) :=
    (c i).schemeMap
  let g : (n i).base ⟶ Spec (.of (coordinateRing K)) := (n i).baseMap
  let π := (Pi.π (fun j : Fin d ↦ (n j).baseOver) i).left
  let j := (n i).selectedOpen.ι
  change EtaleGraphCoproduct.baseChangedComponentInclusion f g π j ≫
      pullback.snd f (π ≫ g) =
    pullback.snd (j ≫ pullback.snd f g) π
  exact EtaleGraphCoproduct.baseChangedComponentInclusion_snd f g π j

omit [SmoothOfRelativeDimension 1 C.hom] in
instance pulledComponentToCoordinatePullback_isOpenImmersion
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) (i : Fin d) :
    IsOpenImmersion
      (pulledComponentToCoordinatePullback K C d z c n i) := by
  let f : ((c i).V : C.left.Opens).toScheme ⟶
      Spec (.of (coordinateRing K)) := (c i).schemeMap
  let g : (n i).base ⟶ Spec (.of (coordinateRing K)) := (n i).baseMap
  let π := (Pi.π (fun j : Fin d ↦ (n j).baseOver) i).left
  let j := (n i).selectedOpen.ι
  change IsOpenImmersion
    (EtaleGraphCoproduct.baseChangedComponentInclusion f g π j)
  exact @EtaleGraphCoproduct.baseChangedComponentInclusion_isOpenImmersion
    _ _ _ _ _ f g π j (show IsOpenImmersion j from inferInstance)

omit [SmoothOfRelativeDimension 1 C.hom] in
instance pulledComponentToCoordinatePullback_isClosedImmersion
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) (i : Fin d) :
    IsClosedImmersion
      (pulledComponentToCoordinatePullback K C d z c n i) := by
  let f : ((c i).V : C.left.Opens).toScheme ⟶
      Spec (.of (coordinateRing K)) := (c i).schemeMap
  let g : (n i).base ⟶ Spec (.of (coordinateRing K)) := (n i).baseMap
  let π := (Pi.π (fun j : Fin d ↦ (n j).baseOver) i).left
  let j := (n i).selectedOpen.ι
  let P : Scheme.{u} := pullback (c i).schemeMap (n i).baseMap
  have hSelected : ((n i).selectedOpen : Set P) =
      ((n i).otherOpen : Set P)ᶜ :=
    ((n i).isCompl.map TopologicalSpace.Opens.frameHom).eq_compl
  let hj : IsClosedImmersion j :=
    .of_isPreimmersion _ (by simp [j, hSelected, (n i).otherOpen.isOpen])
  change IsClosedImmersion
    (EtaleGraphCoproduct.baseChangedComponentInclusion f g π j)
  exact @EtaleGraphCoproduct.baseChangedComponentInclusion_isClosedImmersion
    _ _ _ _ _ f g π j hj

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- The entire selected finite component, not just one split sheet, is a
coproduct summand of the curve chart after base change to the common support
base. -/
theorem pulledComponent_exists_coordinatePullbackCoproduct
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) (i : Fin d) :
    ∃ (W : Scheme.{u})
      (E : pullback (c i).schemeMap
          (commonBaseToCoordinateLine K C d z c n i) ≅
        (pulledComponentOverCommonBase K C d z c n i).left ⨿ W),
      pulledComponentToCoordinatePullback K C d z c n i ≫ E.hom =
        coprod.inl :=
  EtaleGraphCoproduct.exists_coproduct_of_isOpenImmersion_isClosedImmersion
    (pulledComponentToCoordinatePullback K C d z c n i)

/-- The map from a restricted pulled component to its original affine curve
chart. -/
noncomputable def restrictedPulledComponentToChart
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens) (i : Fin d) :
    ((pulledComponentOverCommonBase K C d z c n i).hom ⁻¹ᵁ V).toScheme ⟶
      ((c i).V : C.left.Opens).toScheme :=
  ((pulledComponentOverCommonBase K C d z c n i).hom ⁻¹ᵁ V).ι ≫
    pulledComponentToChart K C d z c n i

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- The chart-coordinate factorization persists after restricting the common
base. -/
theorem restrictedPulledComponentToChart_comp_schemeMap
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens) (i : Fin d) :
    restrictedPulledComponentToChart K C d z c n V i ≫ (c i).schemeMap =
      restrictedPulledComponentToCoordinateLine K C d z c n V i := by
  calc
    restrictedPulledComponentToChart K C d z c n V i ≫ (c i).schemeMap =
        ((pulledComponentOverCommonBase K C d z c n i).hom ⁻¹ᵁ V).ι ≫
          (pulledComponentToChart K C d z c n i ≫ (c i).schemeMap) :=
      Category.assoc _ _ _
    _ = ((pulledComponentOverCommonBase K C d z c n i).hom ⁻¹ᵁ V).ι ≫
          pulledComponentToCoordinateLine K C d z c n i := by
      rw [pulledComponentToChart_comp_schemeMap]
    _ = restrictedPulledComponentToCoordinateLine K C d z c n V i := rfl

/-- The map from an fpqc-pulled component to its original affine curve
chart. -/
noncomputable def fpqcPulledComponentToChart
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :
    (fpqcPulledComponentOverGround K C d z c n V T q i).left ⟶
      ((c i).V : C.left.Opens).toScheme :=
  (fpqcPulledComponentToRestrictedOverGround
      K C d z c n V T q i).left ≫
    restrictedPulledComponentToChart K C d z c n V i

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- The chart-coordinate factorization persists after the common fpqc base
change. -/
theorem fpqcPulledComponentToChart_comp_schemeMap
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :
    fpqcPulledComponentToChart K C d z c n V T q i ≫ (c i).schemeMap =
      fpqcPulledComponentToCoordinateLine K C d z c n V T q i := by
  calc
    fpqcPulledComponentToChart K C d z c n V T q i ≫ (c i).schemeMap =
        (fpqcPulledComponentToRestrictedOverGround
            K C d z c n V T q i).left ≫
          (restrictedPulledComponentToChart K C d z c n V i ≫
            (c i).schemeMap) := Category.assoc _ _ _
    _ = (fpqcPulledComponentToRestrictedOverGround
            K C d z c n V T q i).left ≫
          restrictedPulledComponentToCoordinateLine K C d z c n V i := by
      exact congrArg
        (fun g ↦ (fpqcPulledComponentToRestrictedOverGround
          K C d z c n V T q i).left ≫ g)
        (restrictedPulledComponentToChart_comp_schemeMap
          K C d z c n V i)
    _ = fpqcPulledComponentToCoordinateLine K C d z c n V T q i := rfl

/-- The map from a coherent pulled component to its original affine curve
chart. -/
noncomputable def coherentPulledComponentToChart
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :
    (coherentFpqcPulledComponent K C d z c n V T q i).left ⟶
      ((c i).V : C.left.Opens).toScheme :=
  pullback.fst
      (fpqcPulledComponentToCoverOverGround K C d z c n V T q i).left
      (Pi.π (commonCoverFamily K C d z c n V T q) i).left ≫
    fpqcPulledComponentToChart K C d z c n V T q i

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- The chart-coordinate factorization persists after passage to the single
coherent product base. -/
theorem coherentPulledComponentToChart_comp_schemeMap
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :
    coherentPulledComponentToChart K C d z c n V T q i ≫
        (c i).schemeMap =
      coherentPulledComponentToCoordinateLine K C d z c n V T q i := by
  calc
    coherentPulledComponentToChart K C d z c n V T q i ≫
          (c i).schemeMap =
        pullback.fst
            (fpqcPulledComponentToCoverOverGround
              K C d z c n V T q i).left
            (Pi.π (commonCoverFamily K C d z c n V T q) i).left ≫
          (fpqcPulledComponentToChart K C d z c n V T q i ≫
            (c i).schemeMap) := Category.assoc _ _ _
    _ = pullback.fst
            (fpqcPulledComponentToCoverOverGround
              K C d z c n V T q i).left
            (Pi.π (commonCoverFamily K C d z c n V T q) i).left ≫
          fpqcPulledComponentToCoordinateLine K C d z c n V T q i := by
      exact congrArg
        (fun g ↦ pullback.fst
          (fpqcPulledComponentToCoverOverGround
            K C d z c n V T q i).left
          (Pi.π (commonCoverFamily K C d z c n V T q) i).left ≫ g)
        (fpqcPulledComponentToChart_comp_schemeMap
          K C d z c n V T q i)
    _ = coherentPulledComponentToCoordinateLine K C d z c n V T q i := rfl

/-- The map from a selected split sheet back to the original affine curve
chart.  Its composite with the chart coordinate is the matching coordinate
on the coherent support base. -/
noncomputable def coherentSplitSheetToChart
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d)
    (m : ℕ)
    (E : coherentFpqcPulledComponent K C d z c n V T q i ≅
      splitFinite (coherentFpqcBase K C d z c n V T q) m)
    (j : Fin m) :
    coherentFpqcBase K C d z c n V T q ⟶
      ((c i).V : C.left.Opens).toScheme :=
  ((sheetInclusion (coherentFpqcBase K C d z c n V T q) m j).left ≫
    E.inv.left) ≫ coherentPulledComponentToChart K C d z c n V T q i

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- The selected sheet-to-chart map has exactly the coordinate prescribed by
the corresponding factor of the coherent support base. -/
theorem coherentSplitSheetToChart_comp_schemeMap
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d)
    (m : ℕ)
    (E : coherentFpqcPulledComponent K C d z c n V T q i ≅
      splitFinite (coherentFpqcBase K C d z c n V T q) m)
    (j : Fin m) :
    coherentSplitSheetToChart K C d z c n V T q i m E j ≫
        (c i).schemeMap =
      coherentBaseToCoordinateLine K C d z c n V T q i := by
  calc
    coherentSplitSheetToChart K C d z c n V T q i m E j ≫
          (c i).schemeMap =
        ((sheetInclusion
              (coherentFpqcBase K C d z c n V T q) m j).left ≫
            E.inv.left) ≫
          (coherentPulledComponentToChart K C d z c n V T q i ≫
            (c i).schemeMap) := Category.assoc _ _ _
    _ = ((sheetInclusion
              (coherentFpqcBase K C d z c n V T q) m j).left ≫
            E.inv.left) ≫
          coherentPulledComponentToCoordinateLine
            K C d z c n V T q i := by
      rw [coherentPulledComponentToChart_comp_schemeMap]
    _ = coherentBaseToCoordinateLine K C d z c n V T q i :=
      coherentSplitSheetToCoordinateLine K C d z c n V T q i m E j

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- A chosen split sheet determines the genuine graph component of the
curve's étale coordinate chart after base change to the coherent support
base.  Thus the equal-coordinate locus separates into the actual curve
sheet and a complementary open subscheme. -/
theorem coherentSplitSheet_exists_graphCoproduct
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d)
    (m : ℕ)
    (E : coherentFpqcPulledComponent K C d z c n V T q i ≅
      splitFinite (coherentFpqcBase K C d z c n V T q) m)
    (j : Fin m) :
    let B := coherentFpqcBase K C d z c n V T q
    let f := (c i).schemeMap
    let baseCoordinate := coherentBaseToCoordinateLine K C d z c n V T q i
    let sheetToChart := coherentSplitSheetToChart
      K C d z c n V T q i m E j
    let graph : B ⟶ pullback f baseCoordinate :=
      pullback.lift sheetToChart (𝟙 B) (by
        simpa only [Category.id_comp] using
          coherentSplitSheetToChart_comp_schemeMap
            K C d z c n V T q i m E j)
    ∃ (W : Scheme.{u}) (G : pullback f baseCoordinate ≅ B ⨿ W),
      graph ≫ G.hom = coprod.inl := by
  dsimp only
  exact EtaleGraphCoproduct.exists_graphCoproduct_of_etale
    (c i).schemeMap
    (coherentBaseToCoordinateLine K C d z c n V T q i)
    (coherentSplitSheetToChart K C d z c n V T q i m E j)
    (coherentSplitSheetToChart_comp_schemeMap
      K C d z c n V T q i m E j)

end MazurTorsion.AlgebraicGeometry.Jacobian.FiniteSupportCoordinateMaps
