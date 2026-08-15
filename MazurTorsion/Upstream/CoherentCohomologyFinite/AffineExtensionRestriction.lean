/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineExtensionLocalization

/-!
# Extension data transported from an away localization

The standard identification `D(g) ≅ Spec R_g` transports the
existence-and-power-uniqueness conditions for sections back to `D(g)`.
-/

open CategoryTheory

universe u

noncomputable section

namespace AlgebraicGeometry.QuasicoherentTilde

variable {R : CommRingCat.{u}}

/-- Extension data on `Spec R_g` pulls back to extension data on the
distinguished open `D(g) ⊆ Spec R`. -/
theorem basicOpenExtensionData_of_restrictAway
    (M : (Spec R).Modules) (g : R)
    (h : BasicOpenExtensionData
      (M.restrict
        (Spec.map
          (CommRingCat.ofHom
            (algebraMap R (Localization.Away g))))) ⊤) :
    BasicOpenExtensionData M (PrimeSpectrum.basicOpen g) := by
  let a : R ⟶ CommRingCat.of (Localization.Away g) :=
    CommRingCat.ofHom (algebraMap R _)
  let ψ : Spec (CommRingCat.of (Localization.Away g)) ⟶ Spec R :=
    Spec.map a
  let M' : (Spec (CommRingCat.of (Localization.Away g))).Modules :=
    M.restrict ψ
  letI (U : (Spec (CommRingCat.of
      (Localization.Away g))).Opens) :
      Module (CommRingCat.of (Localization.Away g)) Γ(M', U) :=
    inferInstanceAs
      (Module (CommRingCat.of (Localization.Away g))
        ((modulesSpecToSheaf.obj M').obj.obj (.op U)))
  have hRange :
      ψ.opensRange = PrimeSpectrum.basicOpen g := by
    dsimp [ψ, a]
    apply TopologicalSpace.Opens.ext
    exact
      PrimeSpectrum.localization_away_comap_range
        (Localization.Away g) g
  have hImageTop :
      ψ ''ᵁ (⊤ : (Spec (CommRingCat.of
        (Localization.Away g))).Opens) =
        PrimeSpectrum.basicOpen g :=
    ψ.image_top_eq_opensRange.trans hRange
  have heq (f : R)
      (hf : PrimeSpectrum.basicOpen f ≤
        PrimeSpectrum.basicOpen g) :
      PrimeSpectrum.basicOpen f =
        ψ ''ᵁ PrimeSpectrum.basicOpen (a f) := by
    have hpre :
        ψ ⁻¹ᵁ (PrimeSpectrum.basicOpen f : (Spec R).Opens) =
          PrimeSpectrum.basicOpen (a f) := by
      exact SpecMap_preimage_basicOpen a f
    have himage :
        ψ ''ᵁ PrimeSpectrum.basicOpen (a f) =
          ψ.opensRange ⊓ PrimeSpectrum.basicOpen f :=
      (congrArg (fun U => ψ ''ᵁ U) hpre.symm).trans
        (ψ.image_preimage_eq_opensRange_inf
          (PrimeSpectrum.basicOpen f : (Spec R).Opens))
    have hinf :
        ψ.opensRange ⊓ PrimeSpectrum.basicOpen f =
          PrimeSpectrum.basicOpen f := by
      exact (congrArg
        (fun U => U ⊓ PrimeSpectrum.basicOpen f) hRange).trans
          (inf_eq_right.mpr hf)
    exact hinf.symm.trans himage.symm
  let iso : Γ(M.restrict ψ, ⊤) ≅
      Γ(M, PrimeSpectrum.basicOpen g) :=
    M.restrictAppIso _ _ ≪≫
      M.presheaf.mapIso
        (eqToIso hImageTop.symm).op
  let e (f : R)
      (hf : PrimeSpectrum.basicOpen f ≤
        PrimeSpectrum.basicOpen g) :
      Γ(M', PrimeSpectrum.basicOpen (a f)) ≅
        Γ(M, PrimeSpectrum.basicOpen f) :=
    M.restrictAppIso ψ (PrimeSpectrum.basicOpen (a f)) ≪≫
      M.presheaf.mapIso (eqToIso (heq f hf)).op
  have restrictionSquare (f : R)
      (hf : PrimeSpectrum.basicOpen f ≤
        PrimeSpectrum.basicOpen g) :
      M'.presheaf.map
          (homOfLE
            (show PrimeSpectrum.basicOpen (a f) ≤
              (⊤ : (Spec (CommRingCat.of
                (Localization.Away g))).Opens)
              from le_top)).op ≫
            (e f hf).hom =
        iso.hom ≫ M.presheaf.map (homOfLE hf).op := by
    let hUV :
        Opposite.op (⊤ : (Spec (CommRingCat.of
          (Localization.Away g))).Opens) ⟶
          Opposite.op
            (PrimeSpectrum.basicOpen (a f)) :=
      (homOfLE le_top).op
    let qf :=
      (eqToIso (heq f hf)).op.hom
    let qtop :=
      (eqToIso hImageTop.symm).op.hom
    let himage :
        ψ ''ᵁ PrimeSpectrum.basicOpen (a f) ≤
          ψ ''ᵁ (⊤ : (Spec (CommRingCat.of
            (Localization.Away g))).Opens) :=
      ψ.image_mono le_top
    let r := (homOfLE himage).op
    have hopen :
        r ≫ qf = qtop ≫ (homOfLE hf).op :=
      Subsingleton.elim _ _
    have hmap :
        M.presheaf.map r ≫ M.presheaf.map qf =
          M.presheaf.map qtop ≫
            M.presheaf.map (homOfLE hf).op := by
      calc
        M.presheaf.map r ≫ M.presheaf.map qf =
            M.presheaf.map (r ≫ qf) :=
          (M.presheaf.map_comp r qf).symm
        _ = M.presheaf.map
            (qtop ≫ (homOfLE hf).op) :=
          congrArg M.presheaf.map hopen
        _ = M.presheaf.map qtop ≫
            M.presheaf.map (homOfLE hf).op :=
          M.presheaf.map_comp qtop (homOfLE hf).op
    dsimp [M', e, iso]
    simp only [Iso.trans_hom, Functor.mapIso_hom]
    change
      (M.restrict ψ).presheaf.map hUV ≫
          (M.restrictAppIso ψ
            (PrimeSpectrum.basicOpen (a f))).hom ≫
            M.presheaf.map qf =
        ((M.restrictAppIso ψ ⊤).hom ≫
          M.presheaf.map qtop) ≫
            M.presheaf.map (homOfLE hf).op
    calc
      (M.restrict ψ).presheaf.map hUV ≫
          (M.restrictAppIso ψ
            (PrimeSpectrum.basicOpen (a f))).hom ≫
            M.presheaf.map qf =
          ((M.restrict ψ).presheaf.map hUV ≫
            (M.restrictAppIso ψ
              (PrimeSpectrum.basicOpen (a f))).hom) ≫
                M.presheaf.map qf :=
        (Category.assoc _ _ _).symm
      _ = ((M.restrictAppIso ψ ⊤).hom ≫
            M.presheaf.map r) ≫
              M.presheaf.map qf := by
        exact congrArg (fun k => k ≫ M.presheaf.map qf)
          (Scheme.Modules.map_restrictAppIso_hom ψ M hUV)
      _ = (M.restrictAppIso ψ ⊤).hom ≫
            (M.presheaf.map r ≫
              M.presheaf.map qf) :=
        Category.assoc _ _ _
      _ = (M.restrictAppIso ψ ⊤).hom ≫
            (M.presheaf.map qtop ≫
              M.presheaf.map (homOfLE hf).op) :=
        congrArg
          (fun k => (M.restrictAppIso ψ ⊤).hom ≫ k)
          hmap
      _ = ((M.restrictAppIso ψ ⊤).hom ≫
            M.presheaf.map qtop) ≫
              M.presheaf.map (homOfLE hf).op :=
        (Category.assoc _ _ _).symm
  have restrictionSquareInv (f : R)
      (hf : PrimeSpectrum.basicOpen f ≤
        PrimeSpectrum.basicOpen g) :
      iso.inv ≫
          M'.presheaf.map
            (homOfLE
              (show PrimeSpectrum.basicOpen (a f) ≤
                (⊤ : (Spec (CommRingCat.of
                  (Localization.Away g))).Opens)
                from le_top)).op =
        M.presheaf.map (homOfLE hf).op ≫
          (e f hf).inv := by
    let res :=
      M'.presheaf.map
        (homOfLE
          (show PrimeSpectrum.basicOpen (a f) ≤
            (⊤ : (Spec (CommRingCat.of
              (Localization.Away g))).Opens)
            from le_top)).op
    let target :=
      M.presheaf.map (homOfLE hf).op
    apply ((e f hf).eq_comp_inv).2
    have hsquare :
        res ≫ (e f hf).hom = iso.hom ≫ target :=
      restrictionSquare f hf
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun q => iso.inv ≫ q) hsquare).trans
        (Iso.inv_hom_id_assoc iso target))
  have e_smul (f r : R)
      (hf : PrimeSpectrum.basicOpen f ≤
        PrimeSpectrum.basicOpen g)
      (x : Γ(M', PrimeSpectrum.basicOpen (a f))) :
      (e f hf).hom (sectionSmul (M := M') (a r) x) =
        sectionSmul (M := M) r ((e f hf).hom x) := by
    have hrestrict :=
      restrictAppIso_sectionSmul_Spec (M := M) a r x
    dsimp [M', ψ] at hrestrict
    dsimp [e]
    simp only [Iso.trans_hom, Functor.mapIso_hom,
      Iso.op_hom, eqToIso.hom, eqToHom_op,
      AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp,
      Function.comp_apply]
    calc
      M.presheaf.map _ ((M.restrictAppIso ψ
          (PrimeSpectrum.basicOpen (a f))).hom
            (sectionSmul (M := M') (a r) x)) =
          M.presheaf.map _ (sectionSmul (M := M) r
            ((M.restrictAppIso ψ
              (PrimeSpectrum.basicOpen (a f))).hom x)) :=
        congrArg (fun y => M.presheaf.map _ y) hrestrict
      _ = sectionSmul (M := M) r (M.presheaf.map _
            ((M.restrictAppIso ψ
              (PrimeSpectrum.basicOpen (a f))).hom x)) :=
        map_sectionSmul_Spec (M := M) _ r _
  have iso_smul (r : R)
      (x : Γ(M', ⊤)) :
      iso.hom (sectionSmul (M := M') (a r) x) =
        sectionSmul (M := M) r (iso.hom x) := by
    have hrestrict :=
      restrictAppIso_sectionSmul_Spec (M := M) a r x
    dsimp [M', ψ] at hrestrict
    dsimp [iso]
    simp only [Iso.trans_hom, Functor.mapIso_hom,
      Iso.op_hom, eqToIso.hom, eqToHom_op,
      AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp,
      Function.comp_apply]
    calc
      M.presheaf.map _ ((M.restrictAppIso ψ ⊤).hom
          (sectionSmul (M := M') (a r) x)) =
          M.presheaf.map _ (sectionSmul (M := M) r
            ((M.restrictAppIso ψ ⊤).hom x)) :=
        congrArg (fun y => M.presheaf.map _ y) hrestrict
      _ = sectionSmul (M := M) r (M.presheaf.map _
            ((M.restrictAppIso ψ ⊤).hom x)) :=
        map_sectionSmul_Spec (M := M) _ r _
  refine ⟨fun f hf s => ?_, fun f hf t ht => ?_⟩
  · obtain ⟨n, t, ht⟩ :=
      h.existence (a f) le_top ((e _ hf).inv s)
    refine ⟨n, iso.hom t, ?_⟩
    have hsquareApply :
        (e f hf).hom
            (M'.presheaf.map
              (homOfLE
                (show PrimeSpectrum.basicOpen (a f) ≤
                  (⊤ : (Spec (CommRingCat.of
                    (Localization.Away g))).Opens)
                  from le_top)).op t) =
          M.presheaf.map (homOfLE hf).op (iso.hom t) := by
      have happ := congrArg
        (fun q :
            M'.presheaf.obj
                (Opposite.op (⊤ : (Spec (CommRingCat.of
                  (Localization.Away g))).Opens)) ⟶
              M.presheaf.obj
                (Opposite.op
                  (PrimeSpectrum.basicOpen f)) =>
            ConcreteCategory.hom q t)
        (restrictionSquare f hf)
      exact
        (AddCommGrpCat.comp_apply _ _ t).symm.trans
          (happ.trans (AddCommGrpCat.comp_apply _ _ t))
    have hscalar :
        (e f hf).hom
            (sectionSmul (M := M') ((a f) ^ n) ((e f hf).inv s)) =
          sectionSmul (M := M) (f ^ n) s := by
      calc
        (e f hf).hom
            (sectionSmul (M := M') ((a f) ^ n) ((e f hf).inv s)) =
            (e f hf).hom
              (sectionSmul (M := M') (a (f ^ n)) ((e f hf).inv s)) :=
          congrArg
            (fun r => (e f hf).hom
              (sectionSmul (M := M') r ((e f hf).inv s)))
            (map_pow (ConcreteCategory.hom a) f n).symm
        _ = sectionSmul (M := M) (f ^ n)
              ((e f hf).hom ((e f hf).inv s)) :=
          e_smul f (f ^ n) hf _
        _ = sectionSmul (M := M) (f ^ n) s :=
          congrArg (fun x => sectionSmul (M := M) (f ^ n) x)
            ((e f hf).inv_hom_id_apply s)
    have htransport :
        (e f hf).hom
            (M'.presheaf.map
              (homOfLE
                (show PrimeSpectrum.basicOpen (a f) ≤
                  (⊤ : (Spec (CommRingCat.of
                    (Localization.Away g))).Opens)
                  from le_top)).op t) =
          (e f hf).hom
            (sectionSmul (M := M') ((a f) ^ n)
              ((e f hf).inv s)) :=
      congrArg (fun x => (e f hf).hom x) ht
    exact hsquareApply.symm.trans (htransport.trans hscalar)
  · obtain ⟨n, hn⟩ :=
      h.uniqueness (a f) le_top (iso.inv t) (by
        have hsquareApply :
            M'.presheaf.map
                (homOfLE
                  (show PrimeSpectrum.basicOpen (a f) ≤
                    (⊤ : (Spec (CommRingCat.of
                      (Localization.Away g))).Opens)
                    from le_top)).op (iso.inv t) =
              (e f hf).inv
                (M.presheaf.map (homOfLE hf).op t) := by
          have happ := congrArg
            (fun q :
                M.presheaf.obj
                    (Opposite.op
                      (PrimeSpectrum.basicOpen g)) ⟶
                  M'.presheaf.obj
                    (Opposite.op
                      (PrimeSpectrum.basicOpen (a f))) =>
                ConcreteCategory.hom q t)
            (restrictionSquareInv f hf)
          exact
            (AddCommGrpCat.comp_apply _ _ t).symm.trans
              (happ.trans (AddCommGrpCat.comp_apply _ _ t))
        exact hsquareApply.trans
          ((congrArg (fun x => (e f hf).inv x) ht).trans
            (map_zero (e f hf).inv.hom)))
    refine ⟨n, ?_⟩
    calc
      sectionSmul (M := M) (f ^ n) t =
          sectionSmul (M := M) (f ^ n) (iso.hom (iso.inv t)) :=
        congrArg (fun x => sectionSmul (M := M) (f ^ n) x)
          (iso.inv_hom_id_apply t).symm
      _ = iso.hom
          (sectionSmul (M := M') (a (f ^ n)) (iso.inv t)) :=
        (iso_smul (f ^ n) (iso.inv t)).symm
      _ = iso.hom
          (sectionSmul (M := M') ((a f) ^ n) (iso.inv t)) :=
        congrArg
          (fun r => iso.hom
            (sectionSmul (M := M') r (iso.inv t)))
          (map_pow (ConcreteCategory.hom a) f n)
      _ = iso.hom 0 :=
        congrArg (fun x => iso.hom x) hn
      _ = 0 := map_zero iso.hom.hom

end AlgebraicGeometry.QuasicoherentTilde
