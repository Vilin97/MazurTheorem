/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.EtaleSplitChart
import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteEtaleCoproductPower

/-!
# Split finite families and base change

The split finite object with `m` sheets over a scheme is the disjoint union
of `m` copies of that scheme.  Over an affine base this agrees, over the
base, with the spectrum of the product ring used by `EtaleSplitChart`.

The named downstream consumer is the coherent support coproduct in
`FiniteSupportEtaleCoordinates`, where simultaneous split charts are pulled
to the product of their coordinate bases and assembled into one finite
split family.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.SplitFiniteBaseChange

open FiniteEtaleCoproductPower

/-- The disjoint union of `m` copies of a base scheme, as an object over
that base. -/
noncomputable abbrev splitFinite (S : Scheme.{u}) (m : ℕ) : Over S :=
  Over.mk (Sigma.desc fun _ : ULift.{u} (Fin m) ↦ 𝟙 S)

/-- The `j`-th sheet inclusion. -/
noncomputable def sheetInclusion (S : Scheme.{u}) (m : ℕ) (j : Fin m) :
    Over.mk (𝟙 S) ⟶ splitFinite S m :=
  Over.homMk (Sigma.ι (fun _ : ULift.{u} (Fin m) ↦ S) (ULift.up j)) (by
    exact Sigma.ι_desc (fun _ : ULift.{u} (Fin m) ↦ 𝟙 S) (ULift.up j))

/-- The finite coproduct presentation and the product-ring presentation of
a split affine finite scheme agree over the affine base. -/
noncomputable def liftedSplitProjection
    (R : Type u) [CommRing R] (m : ℕ) :
    Spec (.of (ULift.{u} (Fin m) → R)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap R (ULift.{u} (Fin m) → R)))

/-- The finite coproduct presentation and its same-universe product-ring
presentation agree over the affine base. -/
noncomputable def splitFiniteSpecIso
    (R : Type u) [CommRing R] (m : ℕ) :
    splitFinite (Spec (.of R)) m ≅
      Over.mk (liftedSplitProjection R m) := by
  letI : IsIso (sigmaSpec
      (fun _ : ULift.{u} (Fin m) ↦ CommRingCat.of R)) :=
    AlgebraicGeometry.instIsIsoSchemeSigmaSpecOfFinite _
  exact Over.isoMk
    (asIso (sigmaSpec
      (fun _ : ULift.{u} (Fin m) ↦ CommRingCat.of R))) (by
      apply Sigma.hom_ext
      intro j
      change Sigma.ι (fun _ : ULift.{u} (Fin m) ↦ Spec (.of R)) j ≫
          sigmaSpec (fun _ : ULift.{u} (Fin m) ↦ CommRingCat.of R) ≫
            liftedSplitProjection R m =
        Sigma.ι (fun _ : ULift.{u} (Fin m) ↦ Spec (.of R)) j ≫
          Sigma.desc (fun _ : ULift.{u} (Fin m) ↦ 𝟙 (Spec (.of R)))
      rw [← Category.assoc, ι_sigmaSpec, Sigma.ι_desc]
      unfold liftedSplitProjection
      rw [← Spec.map_comp]
      rw [← Spec.map_id, Spec.map_inj]
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro r
      rfl)

@[reassoc]
theorem splitFiniteSpecIso_hom_comp_projection
    (R : Type u) [CommRing R] (m : ℕ) :
    (splitFiniteSpecIso R m).hom.left ≫
        liftedSplitProjection R m =
      (splitFinite (Spec (.of R)) m).hom :=
  (splitFiniteSpecIso R m).hom.w

/-- Reindex the same-universe sheet type by the original `Fin m`. -/
noncomputable def splitIndexAlgEquiv
    (R : Type u) [CommRing R] (m : ℕ) :
    (Fin m → R) ≃ₐ[R] (ULift.{u} (Fin m) → R) :=
  AlgEquiv.piCongrLeft' R (fun _ : Fin m ↦ R) Equiv.ulift.symm

/-- The lifted-index and ordinary `Fin m` product-ring presentations agree
over the affine base. -/
noncomputable def liftedSplitProjectionIso
    (R : Type u) [CommRing R] (m : ℕ) :
    Over.mk (liftedSplitProjection R m) ≅
      Over.mk (EtaleSplitChart.splitProjection R m) :=
  Over.isoMk
    (Scheme.Spec.mapIso
      (splitIndexAlgEquiv R m).toRingEquiv.toCommRingCatIso.op) (by
        change Spec.map
              (splitIndexAlgEquiv R m).toRingEquiv.toCommRingCatIso.hom ≫
              Spec.map (CommRingCat.ofHom
                (algebraMap R (Fin m → R))) =
            Spec.map (CommRingCat.ofHom
              (algebraMap R (ULift.{u} (Fin m) → R)))
        rw [← Spec.map_comp, Spec.map_inj]
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro r
        rfl)

/-- The finite coproduct is the standard `Fin m` split affine scheme over
the base. -/
noncomputable def splitFiniteStandardSpecIso
    (R : Type u) [CommRing R] (m : ℕ) :
    splitFinite (Spec (.of R)) m ≅
      Over.mk (EtaleSplitChart.splitProjection R m) :=
  splitFiniteSpecIso R m ≪≫ liftedSplitProjectionIso R m

@[reassoc]
theorem splitFiniteStandardSpecIso_hom_comp_projection
    (R : Type u) [CommRing R] (m : ℕ) :
    (splitFiniteStandardSpecIso R m).hom.left ≫
        EtaleSplitChart.splitProjection R m =
      (splitFinite (Spec (.of R)) m).hom :=
  (splitFiniteStandardSpecIso R m).hom.w

/-- Add a contractible auxiliary coordinate without changing the sheet
index. -/
private def sheetUnitEquiv (m : ℕ) :
    ULift.{u} (Fin m) ≃
      ULift.{u} (Fin m) × ULift.{u} PUnit where
  toFun i := (i, ULift.up PUnit.unit)
  invFun p := p.1
  left_inv _ := rfl
  right_inv p := by
    apply Prod.ext
    · rfl
    · exact Subsingleton.elim _ _

/-- Pulling a split finite scheme to a new base gives the split finite
scheme with the same sheets over that base. -/
noncomputable def splitFinitePullbackIso
    (S B : Scheme.{u}) (q : B ⟶ S) (m : ℕ) :
    splitFinite B m ≅ (Over.pullback q).obj (splitFinite S m) := by
  let I := ULift.{u} (Fin m)
  let J := ULift.{u} PUnit
  let f : I → Scheme.{u} := fun _ ↦ S
  let g : J → Scheme.{u} := fun _ ↦ B
  let φ : ∀ _ : I, S ⟶ S := fun _ ↦ 𝟙 S
  let ψ : ∀ _ : J, B ⟶ S := fun _ ↦ q
  let pairPullback : I × J → Scheme.{u} :=
    fun p ↦ pullback (φ p.1) (ψ p.2)
  let componentIso : ∀ i : I, B ≅ pullback (φ i) q :=
    fun i ↦ (asIso (pullback.snd (φ i) q)).symm
  let eComponents : (∐ fun _ : I ↦ B) ≅
      (∐ fun i : I ↦ pullback (φ i) q) :=
    Sigma.mapIso componentIso
  let eReindex : (∐ fun i : I ↦ pullback (φ i) q) ≅
      (∐ pairPullback) := by
    change (∐ pairPullback ∘ sheetUnitEquiv m) ≅ (∐ pairPullback)
    exact Sigma.reindex (sheetUnitEquiv m) pairPullback
  let hpbSnd : (∐ pairPullback) ⟶ (∐ g) :=
    Sigma.desc fun p ↦
      pullback.snd (φ p.1) (ψ p.2) ≫ Sigma.ι g p.2
  have hpb := FinitaryPreExtensive.isPullback_sigmaDesc φ ψ
  let ePullback : (∐ pairPullback) ≅
      pullback (Sigma.desc φ) (Sigma.desc ψ) :=
    hpb.isoIsPullback
      (∐ f) (∐ g)
      (IsPullback.of_hasPullback (Sigma.desc φ) (Sigma.desc ψ))
  let eSingle : (∐ fun _ : J ↦ B) ≅ B :=
    coproductUniqueIso (fun _ : J ↦ B)
  have hSingle : eSingle.hom ≫ q = Sigma.desc ψ := by
    apply Sigma.hom_ext
    intro j
    calc
      Sigma.ι (fun _ : J ↦ B) j ≫ eSingle.hom ≫ q = q := by
        rw [← Category.assoc, ι_coproductUniqueIso_hom]
        simp
      _ = Sigma.ι (fun _ : J ↦ B) j ≫ Sigma.desc ψ := by
        rw [Sigma.ι_desc]
  let compare : pullback (Sigma.desc φ) (Sigma.desc ψ) ⟶
      pullback (Sigma.desc φ) q :=
    pullback.map (Sigma.desc φ) (Sigma.desc ψ)
      (Sigma.desc φ) q (𝟙 _) eSingle.hom (𝟙 _)
      (by simp) (by simpa using hSingle.symm)
  letI : IsIso compare := by
    dsimp only [compare]
    infer_instance
  let e : (∐ fun _ : I ↦ B) ≅
      pullback (Sigma.desc φ) q :=
    eComponents ≪≫ eReindex ≪≫ ePullback ≪≫ asIso compare
  refine Over.isoMk e ?_
  apply Sigma.hom_ext
  intro i
  change Sigma.ι (fun _ : I ↦ B) i ≫ e.hom ≫
      pullback.snd (Sigma.desc φ) q =
    Sigma.ι (fun _ : I ↦ B) i ≫ Sigma.desc (fun _ : I ↦ 𝟙 B)
  rw [Sigma.ι_desc]
  have hComponents : Sigma.ι (fun _ : I ↦ B) i ≫ eComponents.hom =
      (componentIso i).hom ≫
        Sigma.ι (fun j : I ↦ pullback (φ j) q) i := by
    exact Sigma.ι_mapIso_hom componentIso i
  have hReindex :
      Sigma.ι (fun j : I ↦ pullback (φ j) q) i ≫ eReindex.hom =
        Sigma.ι pairPullback (sheetUnitEquiv m i) := by
    change Sigma.ι (pairPullback ∘ sheetUnitEquiv m) i ≫
        (Sigma.reindex (sheetUnitEquiv m) pairPullback).hom = _
    exact Sigma.ι_reindex_hom (sheetUnitEquiv m) pairPullback i
  have hCompare : compare ≫ pullback.snd (Sigma.desc φ) q =
      pullback.snd (Sigma.desc φ) (Sigma.desc ψ) ≫ eSingle.hom := by
    dsimp only [compare]
    simp only [pullback.map, pullback.lift_snd]
  have hPullback : ePullback.hom ≫
      pullback.snd (Sigma.desc φ) (Sigma.desc ψ) =
        hpbSnd :=
    hpb.isoIsPullback_hom_snd (∐ f) (∐ g)
      (IsPullback.of_hasPullback (Sigma.desc φ) (Sigma.desc ψ))
  have hSheet : Sigma.ι pairPullback (sheetUnitEquiv m i) ≫ hpbSnd =
      pullback.snd (φ i) q ≫
        Sigma.ι (fun _ : J ↦ B) (ULift.up PUnit.unit) := by
    dsimp only [hpbSnd]
    rw [Sigma.ι_desc]
  calc
    Sigma.ι (fun _ : I ↦ B) i ≫ e.hom ≫
          pullback.snd (Sigma.desc φ) q =
        (Sigma.ι (fun _ : I ↦ B) i ≫ eComponents.hom) ≫
          eReindex.hom ≫ ePullback.hom ≫ compare ≫
            pullback.snd (Sigma.desc φ) q := by
              simp only [e, Iso.trans_hom, asIso_hom, Category.assoc]
    _ = (componentIso i).hom ≫
          (Sigma.ι (fun j : I ↦ pullback (φ j) q) i ≫
            eReindex.hom) ≫ ePullback.hom ≫ compare ≫
              pullback.snd (Sigma.desc φ) q := by
                simp only [Category.assoc, hComponents]
    _ = (componentIso i).hom ≫
          Sigma.ι pairPullback (sheetUnitEquiv m i) ≫
            ePullback.hom ≫ compare ≫
              pullback.snd (Sigma.desc φ) q := by
                simp only [hReindex]
    _ = (componentIso i).hom ≫
          Sigma.ι pairPullback (sheetUnitEquiv m i) ≫
            ePullback.hom ≫
              pullback.snd (Sigma.desc φ) (Sigma.desc ψ) ≫
                eSingle.hom := by simp only [hCompare]
    _ = (componentIso i).hom ≫
          Sigma.ι pairPullback (sheetUnitEquiv m i) ≫ hpbSnd ≫
            eSingle.hom := by
              rw [← Category.assoc ePullback.hom, hPullback]
    _ = (componentIso i).hom ≫ pullback.snd (φ i) q ≫
          Sigma.ι (fun _ : J ↦ B) (ULift.up PUnit.unit) ≫
            eSingle.hom := by
              rw [← Category.assoc (Sigma.ι pairPullback (sheetUnitEquiv m i)), hSheet]
              simp only [Category.assoc]
    _ = (componentIso i).hom ≫ pullback.snd (φ i) q := by
      rw [ι_coproductUniqueIso_hom]
      simp
    _ = 𝟙 B := by
      dsimp only [componentIso]
      simp

/-- A standard affine split chart remains a split finite object after any
further base change.  The structural-map equation is the datum that turns
the underlying scheme isomorphism into an isomorphism in the slice. -/
noncomputable def baseChangeSplitChartIso
    (R : Type u) [CommRing R] (B : Scheme.{u})
    (q : B ⟶ Spec (.of R)) (m : ℕ)
    (X : Over (Spec (.of R)))
    (E : X.left ≅ Spec (.of (Fin m → R)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection R m = X.hom) :
    (Over.pullback q).obj X ≅ splitFinite B m :=
  (Over.pullback q).mapIso
      (Over.isoMk E hE ≪≫ (splitFiniteStandardSpecIso R m).symm) ≪≫
    (splitFinitePullbackIso (Spec (.of R)) B q m).symm

@[reassoc]
theorem baseChangeSplitChartIso_hom_comp_projection
    (R : Type u) [CommRing R] (B : Scheme.{u})
    (q : B ⟶ Spec (.of R)) (m : ℕ)
    (X : Over (Spec (.of R)))
    (E : X.left ≅ Spec (.of (Fin m → R)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection R m = X.hom) :
    (baseChangeSplitChartIso R B q m X E hE).hom.left ≫
        (splitFinite B m).hom =
      ((Over.pullback q).obj X).hom :=
  (baseChangeSplitChartIso R B q m X E hE).hom.w

/-- The total number of sheets in a finite family of split finite objects. -/
def totalSheets (d : ℕ) (m : Fin d → ℕ) : ℕ :=
  Fintype.card (Σ i : Fin d, Fin (m i))

/-- Reindex the sheets of a finite family by one finite ordinal. -/
noncomputable def splitFamilyIndexEquiv (d : ℕ) (m : Fin d → ℕ) :
    ULift.{u} (Fin (totalSheets d m)) ≃
      Σ i : Fin d, ULift.{u} (Fin (m i)) :=
  Equiv.ulift.trans
    ((Fintype.equivFin (Σ i : Fin d, Fin (m i))).symm.trans
      (Equiv.sigmaCongrRight fun _ ↦ Equiv.ulift.symm))

/-- A coordinatewise isomorphism of finite families induces an isomorphism
of their disjoint unions over the common base. -/
noncomputable def familyCoproductIsoOfFamilyIso
    (S : Scheme.{u}) (d : ℕ) (X Y : Fin d → Over S)
    (E : ∀ i, X i ≅ Y i) :
    familyCoproduct S d X ≅ familyCoproduct S d Y := by
  let p : ∀ i, (X i).left ≅ (Y i).left :=
    fun i ↦ (Over.forget S).mapIso (E i)
  let e : (∐ fun i ↦ (X i).left) ≅ (∐ fun i ↦ (Y i).left) :=
    Sigma.mapIso p
  refine Over.isoMk e ?_
  apply Sigma.hom_ext
  intro i
  change Sigma.ι (fun j ↦ (X j).left) i ≫ e.hom ≫
      Sigma.desc (fun j ↦ (Y j).hom) =
    Sigma.ι (fun j ↦ (X j).left) i ≫
      Sigma.desc (fun j ↦ (X j).hom)
  have hMap : Sigma.ι (fun j ↦ (X j).left) i ≫ e.hom =
      (p i).hom ≫ Sigma.ι (fun j ↦ (Y j).left) i :=
    Sigma.ι_mapIso_hom p i
  rw [← Category.assoc, hMap]
  dsimp only [p]
  simp only [Category.assoc, Sigma.ι_desc]
  change (E i).hom.left ≫ (Y i).hom = (X i).hom
  exact (E i).hom.w

/-- Flatten an iterated coproduct of copies of a scheme to a coproduct over
the corresponding sigma type. -/
noncomputable def splitFamilyFlattenIso
    (S : Scheme.{u}) (d : ℕ) (m : Fin d → ℕ) :
    familyCoproduct S d (fun i ↦ splitFinite S (m i)) ≅
      Over.mk (Sigma.desc
        (fun _ : Σ i : Fin d, ULift.{u} (Fin (m i)) ↦ 𝟙 S)) := by
  let e := Limits.sigmaSigmaIso
    (fun i : Fin d ↦ ULift.{u} (Fin (m i)))
    (fun _ _ ↦ S)
  refine Over.isoMk e ?_
  apply Sigma.hom_ext
  intro i
  apply Sigma.hom_ext
  intro j
  change Sigma.ι (fun _ : ULift.{u} (Fin (m i)) ↦ S) j ≫
        Sigma.ι (fun i : Fin d ↦
          ∐ fun _ : ULift.{u} (Fin (m i)) ↦ S) i ≫
        e.hom ≫
        Sigma.desc
          (fun _ : Σ i : Fin d, ULift.{u} (Fin (m i)) ↦ 𝟙 S) =
      Sigma.ι (fun _ : ULift.{u} (Fin (m i)) ↦ S) j ≫
        Sigma.ι (fun i : Fin d ↦
          ∐ fun _ : ULift.{u} (Fin (m i)) ↦ S) i ≫
        Sigma.desc (fun i ↦
          Sigma.desc (fun _ : ULift.{u} (Fin (m i)) ↦ 𝟙 S))
  dsimp only [e, Limits.sigmaSigmaIso]
  simp only [← Category.assoc, Sigma.ι_desc]

/-- A coproduct indexed by all component sheets is the single split finite
object with the total number of sheets. -/
noncomputable def splitFamilyReindexIso
    (S : Scheme.{u}) (d : ℕ) (m : Fin d → ℕ) :
    Over.mk (Sigma.desc
        (fun _ : Σ i : Fin d, ULift.{u} (Fin (m i)) ↦ 𝟙 S)) ≅
      splitFinite S (totalSheets d m) := by
  let ε := splitFamilyIndexEquiv d m
  let f : (Σ i : Fin d, ULift.{u} (Fin (m i))) → Scheme.{u} := fun _ ↦ S
  let e : (∐ f) ≅
      (∐ fun _ : ULift.{u} (Fin (totalSheets d m)) ↦ S) :=
    (Sigma.reindex ε f).symm
  refine Over.isoMk e ?_
  apply Sigma.hom_ext
  intro p
  let b := ε.symm p
  change Sigma.ι f p ≫ e.hom ≫
      Sigma.desc
        (fun _ : ULift.{u} (Fin (totalSheets d m)) ↦ 𝟙 S) =
    Sigma.ι f p ≫ Sigma.desc (fun _ ↦ 𝟙 S)
  rw [show p = ε b by exact (ε.apply_symm_apply p).symm]
  change Sigma.ι f (ε b) ≫ (Sigma.reindex ε f).inv ≫
      Sigma.desc
        (fun _ : ULift.{u} (Fin (totalSheets d m)) ↦ 𝟙 S) =
    Sigma.ι f (ε b) ≫ Sigma.desc (fun _ ↦ 𝟙 S)
  rw [← Category.assoc, Sigma.ι_reindex_inv]
  simp only [Sigma.ι_desc]

/-- A finite family of split finite objects is one split finite object with
the total sheet count. -/
noncomputable def splitFiniteFamilyCoproductIso
    (S : Scheme.{u}) (d : ℕ) (m : Fin d → ℕ) :
    familyCoproduct S d (fun i ↦ splitFinite S (m i)) ≅
      splitFinite S (totalSheets d m) :=
  splitFamilyFlattenIso S d m ≪≫ splitFamilyReindexIso S d m

/-- A family whose members have chosen split presentations has a single
split presentation after taking their disjoint union. -/
noncomputable def familyCoproductSplitIso
    (S : Scheme.{u}) (d : ℕ) (X : Fin d → Over S)
    (m : Fin d → ℕ) (E : ∀ i, X i ≅ splitFinite S (m i)) :
    familyCoproduct S d X ≅ splitFinite S (totalSheets d m) :=
  familyCoproductIsoOfFamilyIso S d X (fun i ↦ splitFinite S (m i)) E ≪≫
    splitFiniteFamilyCoproductIso S d m

end MazurTorsion.AlgebraicGeometry.Jacobian.SplitFiniteBaseChange
