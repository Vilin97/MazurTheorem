/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeActionFree
import MazurTorsion.Upstream.AINTLIB.ForMathlib.TorsorMap
/-!
# The quotient projection is a geometric `G`-torsor ([B3-g3a], T-Q2 torsor part)

`isIso_torsorCompare_quotientπ`: for a **free** finite group action, the map
`(γ, x) ↦ (γ·x, x)` identifies `∐_G X` with `X ×_{X/G} X` — i.e. `X ⟶ X/G` is a `G`-torsor.
Built from the ring-level torsor identity `torsorMul_bijective_of_free` over the cartesian atlas
square (`isPullback_quotientπ_quotientChart`) via `IsIso` being Zariski-local at the target.
The helper lemmas (`isIso_torsorCompare_spec` over an affine, `isPullback_torsorCompare_baseChange`)
are general T-Q2 infrastructure.
-/

open AlgebraicGeometry CategoryTheory Limits
universe u

namespace AlgebraicGeometry.SchemeAction

open scoped TensorProduct
open ModularCurves

/-- **Affine base case.** On `Spec B` with a `G`-action whose torsor multiplication is bijective,
the quotient projection `Spec B ⟶ Spec Bᴳ` is a geometric `G`-torsor: the comparison
`torsorCompare` is `Spec` of the (bijective) ring-level `torsorMul`, up to the affine
identifications `∐_G Spec B ≅ Spec (∏_G B)` (`sigmaSpec`) and
`Spec B ×_{Spec Bᴳ} Spec B ≅ Spec (B ⊗_{Bᴳ} B)` (`pullbackSpecIso`). -/
private theorem isIso_torsorCompare_spec {G : Type u} [Group G] [Finite G]
    (B : Type u) [CommRing B] [MulSemiringAction G B] [SMulCommClass G ℤ B]
    (hbij : Function.Bijective (MulSemiringAction.torsorMul G ℤ B)) :
    IsIso (ModularCurves.torsorCompare (invariantsπ G B ℤ) (SchemeAction.spec G B)
      (fun g => specSMul_invariantsπ G B ℤ g)) := by
  let hover : ∀ g, (SchemeAction.spec G B).hom g ≫ invariantsπ G B ℤ = invariantsπ G B ℤ :=
    fun g => by simpa only [SchemeAction.spec_hom] using specSMul_invariantsπ G B ℤ g
  change IsIso (ModularCurves.torsorCompare (invariantsπ G B ℤ) (SchemeAction.spec G B) hover)
  haveI hbijIso : IsIso (CommRingCat.ofHom (MulSemiringAction.torsorMul G ℤ B).toRingHom) := by
    rw [ConcreteCategory.isIso_iff_bijective]; exact hbij
  haveI : IsIso (Spec.map (CommRingCat.ofHom (MulSemiringAction.torsorMul G ℤ B).toRingHom)) :=
    inferInstance
  have hkey : ModularCurves.torsorCompare (invariantsπ G B ℤ) (SchemeAction.spec G B) hover
      = sigmaSpec (fun _ : G => CommRingCat.of B)
          ≫ Spec.map (CommRingCat.ofHom (MulSemiringAction.torsorMul G ℤ B).toRingHom)
          ≫ (pullbackSpecIso (FixedPoints.subalgebra ℤ B G) B B).inv
          ≫ (pullbackSymmetry (invariantsπ G B ℤ) (invariantsπ G B ℤ)).hom := by
    refine Sigma.hom_ext _ _ (fun γ => ?_)
    rw [← Category.assoc, ModularCurves.ι_torsorCompare, ι_sigmaSpec]
    have hγ : specSMul γ ≫
        Spec.map (CommRingCat.ofHom (algebraMap (FixedPoints.subalgebra ℤ B G) B)) =
          𝟙 _ ≫ Spec.map
            (CommRingCat.ofHom (algebraMap (FixedPoints.subalgebra ℤ B G) B)) := by
      rw [Category.id_comp]
      simpa only [invariantsπ] using specSMul_invariantsπ G B ℤ γ
    change pullback.lift (specSMul γ) (𝟙 _) hγ =
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : G => B) γ)) ≫
        Spec.map (CommRingCat.ofHom (MulSemiringAction.torsorMul G ℤ B).toRingHom) ≫
          (pullbackSpecIso (FixedPoints.subalgebra ℤ B G) B B).inv ≫
            (pullbackSymmetry
              (Spec.map (CommRingCat.ofHom (algebraMap (FixedPoints.subalgebra ℤ B G) B)))
              (Spec.map (CommRingCat.ofHom (algebraMap (FixedPoints.subalgebra ℤ B G) B)))).hom
    apply pullback.hom_ext
      (f := Spec.map (CommRingCat.ofHom (algebraMap (FixedPoints.subalgebra ℤ B G) B)))
      (g := Spec.map (CommRingCat.ofHom (algebraMap (FixedPoints.subalgebra ℤ B G) B)))
    · simp only [Category.assoc, pullback.lift_fst,
        pullbackSymmetry_hom_comp_fst, pullbackSpecIso_inv_snd, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, specSMul]
      rw [Spec.map_injective.eq_iff]
      ext y
      simp [MulSemiringAction.torsorMul_tmul]
    · simp only [Category.assoc, pullback.lift_snd,
        pullbackSymmetry_hom_comp_snd, pullbackSpecIso_inv_fst, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp]
      rw [← Spec.map_id, ← CommRingCat.ofHom_id, Spec.map_injective.eq_iff]
      ext x
      simp [MulSemiringAction.torsorMul_tmul]
  rw [hkey]
  change IsIso (sigmaSpec (fun _ : G => CommRingCat.of B) ≫
    Spec.map (CommRingCat.ofHom (MulSemiringAction.torsorMul G ℤ B).toRingHom) ≫
      (pullbackSpecIso (FixedPoints.subalgebra ℤ B G) B B).inv ≫
        (pullbackSymmetry
          (Spec.map (CommRingCat.ofHom (algebraMap (FixedPoints.subalgebra ℤ B G) B)))
          (Spec.map (CommRingCat.ofHom (algebraMap (FixedPoints.subalgebra ℤ B G) B)))).hom)
  infer_instance

/-- **Transport of the torsor property** across compatible isos of total space and base:
if `eZ : Z ≅ Z'` and `eS : S ≅ S'` intertwine the structure maps (`hcomm`) and the actions
(`hact`), then `torsorCompare fZ σZ` iso implies `torsorCompare fZ' σZ'` iso. -/
private theorem isIso_torsorCompare_of_iso {G : Type u} [Group G] [Finite G]
    {S Z S' Z' : Scheme.{u}}
    {fZ : Z ⟶ S} (σZ : SchemeAction G Z) (hZ : ∀ γ, σZ.hom γ ≫ fZ = fZ)
    {fZ' : Z' ⟶ S'} (σZ' : SchemeAction G Z') (hZ' : ∀ γ, σZ'.hom γ ≫ fZ' = fZ')
    (eZ : Z ≅ Z') (eS : S ≅ S')
    (hcomm : fZ ≫ eS.hom = eZ.hom ≫ fZ')
    (hact : ∀ γ, σZ.hom γ ≫ eZ.hom = eZ.hom ≫ σZ'.hom γ)
    (h : IsIso (ModularCurves.torsorCompare fZ σZ hZ)) :
    IsIso (ModularCurves.torsorCompare fZ' σZ' hZ') := by
  haveI := h
  have key : ModularCurves.torsorCompare fZ σZ hZ ≫
        pullback.map fZ fZ fZ' fZ' eZ.hom eZ.hom eS.hom hcomm hcomm
      = (Sigma.mapIso (fun _ : G => eZ)).hom ≫ ModularCurves.torsorCompare fZ' σZ' hZ' := by
    refine Sigma.hom_ext _ _ (fun γ => ?_)
    rw [← Category.assoc, ModularCurves.ι_torsorCompare, ← Category.assoc,
      Sigma.ι_mapIso_hom, Category.assoc, ModularCurves.ι_torsorCompare]
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst_assoc, pullback.lift_fst]
      exact hact γ
    · simp only [Category.assoc, pullback.lift_snd_assoc, pullback.lift_snd, Category.id_comp,
        Category.comp_id]
  have heq : ModularCurves.torsorCompare fZ' σZ' hZ' =
      inv (Sigma.mapIso (fun _ : G => eZ)).hom ≫ ModularCurves.torsorCompare fZ σZ hZ ≫
        pullback.map fZ fZ fZ' fZ' eZ.hom eZ.hom eS.hom hcomm hcomm := by
    rw [key, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  rw [heq]
  infer_instance

open ModularCurves in
/-- **Base change of `torsorCompare` is a pullback square** (the local-to-global engine).
Base-changing the `G`-torsor `fW : W ⟶ S'` along `f₀ : S ⟶ S'` turns `torsorCompare fW` into
`torsorCompare` of the pulled-back action, cartesianly: the componentwise pullback squares of
`isIso_torsorCompare_pullback` assemble (pullbacks distribute over the finite coproduct `∐_G`). -/
private theorem isPullback_torsorCompare_baseChange {S S' W : Scheme.{u}} {G : Type u} [Group G]
    [Finite G] {fW : W ⟶ S'} (σW : SchemeAction G W) (hWover : ∀ γ, σW.hom γ ≫ fW = fW)
    (f₀ : S ⟶ S') :
    IsPullback
      (Sigma.desc fun γ : G => pullback.fst fW f₀ ≫ Sigma.ι (fun _ : G => W) γ)
      (torsorCompare (pullback.snd fW f₀) (pullbackTorsorAction σW hWover f₀)
        (pullbackTorsorAction_over σW hWover f₀))
      (torsorCompare fW σW hWover)
      (pullback.map (pullback.snd fW f₀) (pullback.snd fW f₀) fW fW
        (pullback.fst fW f₀) (pullback.fst fW f₀) f₀ pullback.condition.symm
        pullback.condition.symm) := by
  have hq : pullback.snd fW f₀ ≫ f₀ = pullback.fst fW f₀ ≫ fW := pullback.condition.symm
  have hsq : ∀ γ : G,
      IsPullback
        (pullback.lift ((pullbackTorsorAction σW hWover f₀).hom γ) (𝟙 (pullback fW f₀))
          (by rw [Category.id_comp]; exact pullbackTorsorAction_over σW hWover f₀ γ))
        (pullback.fst fW f₀)
        (pullback.map (pullback.snd fW f₀) (pullback.snd fW f₀) fW fW
          (pullback.fst fW f₀) (pullback.fst fW f₀) f₀ hq hq)
        (Sigma.ι (fun _ : G => W) γ ≫ torsorCompare fW σW hWover) := by
    intro γ
    rw [ι_torsorCompare]
    have t : IsPullback (pullback.snd (pullback.snd fW f₀) (pullback.snd fW f₀))
        (pullback.map (pullback.snd fW f₀) (pullback.snd fW f₀) fW fW
          (pullback.fst fW f₀) (pullback.fst fW f₀) f₀ hq hq)
        (pullback.fst fW f₀) (pullback.snd fW fW) := by
      apply IsPullback.of_bot _ _ ((IsPullback.of_hasPullback fW fW).flip)
      · rw [show pullback.map (pullback.snd fW f₀) (pullback.snd fW f₀) fW fW
              (pullback.fst fW f₀) (pullback.fst fW f₀) f₀ hq hq ≫ pullback.fst fW fW =
            pullback.fst (pullback.snd fW f₀) (pullback.snd fW f₀) ≫ pullback.fst fW f₀ from
            pullback.lift_fst _ _ _,
          show pullback.fst fW f₀ ≫ fW = pullback.snd fW f₀ ≫ f₀ from pullback.condition]
        exact (IsPullback.of_hasPullback (pullback.snd fW f₀) (pullback.snd fW f₀)).flip.paste_vert
          (IsPullback.of_hasPullback fW f₀).flip
      · simp [pullback.map, pullback.lift_snd]
    apply IsPullback.of_right _ _ t
    · rw [pullback.lift_snd, pullback.lift_snd]
      exact IsPullback.of_id_fst
    · apply pullback.hom_ext <;>
        simp [pullback.map, pullback.lift_fst, pullback.lift_snd,
          pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  exact IsUniversalColimit.isPullback_of_isColimit_right
    (hau := FinitaryPreExtensive.isUniversal_finiteCoproducts
      (coproductIsCoproduct (fun _ : G => W)))
    (f := fun i => Sigma.ι (fun _ : G => W) i ≫ torsorCompare fW σW hWover)
    (u := torsorCompare fW σW hWover)
    (v := pullback.map (pullback.snd fW f₀) (pullback.snd fW f₀) fW fW (pullback.fst fW f₀)
      (pullback.fst fW f₀) f₀ hq hq)
    (q₁ := fun _ => pullback.fst fW f₀)
    (q₂ := fun γ => pullback.lift ((pullbackTorsorAction σW hWover f₀).hom γ)
      (𝟙 (pullback fW f₀)) (by
        rw [Category.id_comp]
        exact pullbackTorsorAction_over σW hWover f₀ γ))
    (hP := fun γ => (hsq γ).flip)
    (hd := coproductIsCoproduct (fun _ : G => pullback fW f₀))

section Main
variable {G : Type u} [Group G] {X : Scheme.{u}} (σ : SchemeAction G X)
variable [Finite G] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
  (V : X → X.Opens) (hVs : ∀ x, σ.IsStableOpen (V x)) (hVa : ∀ x, IsAffineOpen (V x))
  (hVmem : ∀ x, x ∈ V x)
  (hfree : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X), t ≫ σ.hom γ = t → IsEmpty T)

include hfree in
/-- Over the `x`-th quotient chart, the base-changed torsor comparison is an isomorphism.
By the cartesian atlas square (`isPullback_quotientπ_quotientChart`) the chart-restricted
projection is `localQuotientπ : V x ⟶ Spec Γ(X,V x)ᴳ`, so this transports the affine base case
`isIso_torsorCompare_spec` (via `isIso_torsorCompare_of_iso`, intertwining `specSMul` with the
pulled-back action through `isoSpec` and the atlas iso). -/
private theorem isIso_torsorCompare_local (x : X) :
    IsIso (torsorCompare
      (pullback.snd (σ.quotientπ V hVs hVa hVmem) (σ.quotientChart V hVs hVa x).ι)
      (pullbackTorsorAction σ (fun γ => σ.hom_quotientπ V hVs hVa hVmem γ)
        (σ.quotientChart V hVs hVa x).ι)
      (pullbackTorsorAction_over σ (fun γ => σ.hom_quotientπ V hVs hVa hVmem γ)
        (σ.quotientChart V hVs hVa x).ι)) := by
  letI := σ.gammaMulSemiringAction (hVs x)
  have hpb := σ.isPullback_quotientπ_quotientChart V hVs hVa hVmem x
  have step2 : ∀ γ : G, (σ.hom γ).resLE (V x) (V x) ((hVs x).le_preimage γ) ≫ hpb.isoPullback.hom
      = hpb.isoPullback.hom ≫ (pullbackTorsorAction σ (fun γ => σ.hom_quotientπ V hVs hVa hVmem γ)
          (σ.quotientChart V hVs hVa x).ι).hom γ := by
    intro γ
    apply pullback.hom_ext
    · rw [Category.assoc, hpb.isoPullback_hom_fst, Scheme.Hom.resLE_comp_ι, Category.assoc,
        pullbackTorsorAction_hom, pullback.lift_fst, ← Category.assoc, hpb.isoPullback_hom_fst]
    · rw [Category.assoc, hpb.isoPullback_hom_snd, ← Category.assoc, resLE_localQuotientπ,
        Category.assoc, pullbackTorsorAction_over, hpb.isoPullback_hom_snd]
  refine isIso_torsorCompare_of_iso (SchemeAction.spec G ↑Γ(X, V x))
    (fun g => specSMul_invariantsπ G ↑Γ(X, V x) ℤ g)
    (pullbackTorsorAction σ (fun γ => σ.hom_quotientπ V hVs hVa hVmem γ)
      (σ.quotientChart V hVs hVa x).ι)
    (pullbackTorsorAction_over σ (fun γ => σ.hom_quotientπ V hVs hVa hVmem γ)
      (σ.quotientChart V hVs hVa x).ι)
    ((hVa x).isoSpec.symm ≪≫ hpb.isoPullback) (σ.quotientChartIso V hVs hVa x) ?_ ?_
    (isIso_torsorCompare_spec ↑Γ(X, V x) (σ.torsorMul_bijective_of_free (hVs x) (hVa x) hfree))
  · rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, hpb.isoPullback_hom_snd,
      σ.localQuotientπ_eq (hVs x) (hVa x), ← Category.assoc, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp]
  · intro γ
    have e1 : ((hVa x).isoSpec.symm ≪≫ hpb.isoPullback).hom
        = (hVa x).isoSpec.inv ≫ hpb.isoPullback.hom := by
      rw [Iso.trans_hom, Iso.symm_hom]
    rw [SchemeAction.spec_hom, e1, ← Category.assoc, specSMul_isoSpec_inv σ (hVs x) (hVa x) γ,
      Category.assoc, step2 γ, ← Category.assoc]

include hfree in
/-- **([B3-g3a], T-Q2 geometric) The quotient projection is a `G`-torsor**: `(γ, x) ↦ (γ·x, x)`
identifies `∐_G X` with `X ×_{X/G} X`.

`IsIso` is Zariski-local at the target `X ×_{X/G} X`; the atlas covers `X/G`, so the pullbacks of
the quotient charts cover the target. Over each chart the projection `X ⟶ X/G` restricts to the
local quotient `V x ⟶ Spec Γ(X,V x)ᴳ`, where `torsorCompare` becomes the base-changed torsor
comparison (`isPullback_torsorCompare_baseChange`), an isomorphism by the affine, ring-level torsor
identity `torsorMul_bijective_of_free` (`isIso_torsorCompare_local`). -/
theorem isIso_torsorCompare_quotientπ :
    IsIso (ModularCurves.torsorCompare (σ.quotientπ V hVs hVa hVmem) σ
      (fun γ => σ.hom_quotientπ V hVs hVa hVmem γ)) := by
  rw [← MorphismProperty.isomorphisms.iff]
  refine (IsZariskiLocalAtTarget.iff_of_openCover (P := MorphismProperty.isomorphisms Scheme.{u})
    (Scheme.Pullback.openCoverOfBase
      ((σ.quotient V hVs hVa).openCoverOfIsOpenCover (σ.quotientChart V hVs hVa)
        (σ.iSup_quotientChart_eq_top V hVs hVa))
      (σ.quotientπ V hVs hVa hVmem) (σ.quotientπ V hVs hVa hVmem))).mpr ?_
  intro x
  rw [MorphismProperty.isomorphisms.iff]
  haveI hlocal := isIso_torsorCompare_local σ V hVs hVa hVmem hfree x
  have hA := isPullback_torsorCompare_baseChange σ (fun γ => σ.hom_quotientπ V hVs hVa hVmem γ)
    (σ.quotientChart V hVs hVa x).ι
  rw [← hA.isoPullback_hom_snd] at hlocal
  exact IsIso.of_isIso_comp_left hA.isoPullback.hom
    (pullback.snd (ModularCurves.torsorCompare (σ.quotientπ V hVs hVa hVmem) σ
      (fun γ => σ.hom_quotientπ V hVs hVa hVmem γ))
      (pullback.map (pullback.snd (σ.quotientπ V hVs hVa hVmem) (σ.quotientChart V hVs hVa x).ι)
        (pullback.snd (σ.quotientπ V hVs hVa hVmem) (σ.quotientChart V hVs hVa x).ι)
        (σ.quotientπ V hVs hVa hVmem) (σ.quotientπ V hVs hVa hVmem)
        (pullback.fst (σ.quotientπ V hVs hVa hVmem) (σ.quotientChart V hVs hVa x).ι)
        (pullback.fst (σ.quotientπ V hVs hVa hVmem) (σ.quotientChart V hVs hVa x).ι)
        (σ.quotientChart V hVs hVa x).ι pullback.condition.symm pullback.condition.symm))

end Main

end AlgebraicGeometry.SchemeAction
