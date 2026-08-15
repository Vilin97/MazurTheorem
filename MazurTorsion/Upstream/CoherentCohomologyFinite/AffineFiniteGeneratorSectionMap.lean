/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineFiniteGeneratorMap
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleTopSectionHom

/-!
# The finite generator map as a coproduct of section maps

The affine finite-generator map built through the tilde equivalence is the
categorical coproduct of the maps from the unit sheaf determined by the
chosen top sections.  This identifies the concrete spanning-family
epimorphism with the form needed by the projective construction.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleTopSectionHom

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}}

/-- The inverse tilde/free comparison carries a free-sheaf inclusion to
the tilde of the corresponding `Finsupp` inclusion. -/
lemma ιFree_tildeFinsupp_inv {ι : Type u} (i : ι) :
    SheafOfModules.ιFree
          (R := (Spec R).ringCatSheaf) i ≫
        (tildeFinsupp (R := R) ι).inv =
      (tilde.functor R).map
        (ModuleCat.ofHom
          (Finsupp.lsingle i
            (R := R) (M := ModuleCat.of R R))) := by
  let H : IsColimit <|
      (tilde.functor R).mapCocone
        (ModuleCat.finsuppCocone R R ι) :=
    isColimitOfPreserves
      (tilde.functor R)
      (ModuleCat.finsuppCoconeIsColimit R R ι)
  let e :
      (Discrete.functor
          fun (_ : ι) => ModuleCat.of R R) ⋙
          tilde.functor R ≅
        Discrete.functor
          fun _ =>
            SheafOfModules.unit
              (Spec R).ringCatSheaf :=
    Discrete.natIso (fun _ => tildeSelf)
  let P :=
    (IsColimit.precomposeHomEquiv e.symm _).symm H
  let Q :=
    coproductIsCoproduct
      (fun _ : ι =>
        SheafOfModules.unit (Spec R).ringCatSheaf)
  have h :=
    P.comp_coconePointUniqueUpToIso_inv
      Q (Discrete.mk i)
  change
    SheafOfModules.ιFree
          (R := (Spec R).ringCatSheaf) i ≫
        (tildeFinsupp (R := R) ι).inv =
      𝟙 _ ≫
        (tilde.functor R).map
          (ModuleCat.ofHom
            (Finsupp.lsingle i
              (R := R) (M := ModuleCat.of R R))) at h
  simpa only [Category.id_comp] using h

/-- The tilde-based affine generator map is the free morphism associated
to restriction of the given top sections. -/
theorem freeToModuleOfTopSections_eq_freeHomEquiv
    (M : (Spec R).Modules) {ι : Type u}
    (s : ι → Γ(M, ⊤)) :
    freeToModuleOfTopSections M s =
      M.freeHomEquiv.symm
        (fun a => sectionsOfTop M (s a)) := by
  apply M.freeHomEquiv.injective
  funext i
  rw [Equiv.apply_symm_apply]
  apply PresheafOfModules.sections_ext
  intro X
  rw [← PresheafOfModules.sections_property
    (M.freeHomEquiv (freeToModuleOfTopSections M s) i)
    (homOfLE le_top).op]
  change
    M.val.map (homOfLE le_top).op
        ((M.freeHomEquiv
          (freeToModuleOfTopSections M s) i).val
            (Opposite.op (⊤ : (Spec R).Opens))) =
      M.val.map (homOfLE le_top).op (s i)
  congr 1
  change
    ((SheafOfModules.ιFree
        (R := (Spec R).ringCatSheaf) i ≫
      freeToModuleOfTopSections M s).val.app
        (Opposite.op (⊤ : (Spec R).Opens)))
      (1 : (Spec R).ringCatSheaf.obj.obj
        (Opposite.op (⊤ : (Spec R).Opens))) = s i
  simp only [freeToModuleOfTopSections]
  let l :
      ModuleCat.of R R ⟶
        ModuleCat.of R (ι →₀ R) :=
    ModuleCat.ofHom
      (Finsupp.lsingle i
        (R := R) (M := ModuleCat.of R R))
  let q :
      ModuleCat.of R (ι →₀ R) ⟶
        ModuleCat.of R Γ(M, ⊤) :=
    ModuleCat.ofHom
      (Finsupp.linearCombination R s)
  have hmor :
      SheafOfModules.ιFree
            (R := (Spec R).ringCatSheaf) i ≫
          (tildeFinsupp (R := R) ι).inv ≫
          (tilde.functor R).map q ≫
          M.fromTildeΓ =
        (tilde.functor R).map (l ≫ q) ≫
          M.fromTildeΓ := by
    have hp :
        SheafOfModules.ιFree
              (R := (Spec R).ringCatSheaf) i ≫
            (tildeFinsupp (R := R) ι).inv =
          (tilde.functor R).map l :=
      ιFree_tildeFinsupp_inv i
    let a := SheafOfModules.ιFree
      (R := (Spec R).ringCatSheaf) i
    let b := (tildeFinsupp (R := R) ι).inv
    let c := (tilde.functor R).map q
    let d := M.fromTildeΓ
    have hab : a ≫ b = (tilde.functor R).map l := hp
    have hmap :
        (tilde.functor R).map (l ≫ q) =
          (tilde.functor R).map l ≫ c :=
      (tilde.functor R).map_comp l q
    change a ≫ b ≫ c ≫ d = _
    exact
      (Category.assoc a b (c ≫ d)).symm |>.trans <|
        (congrArg (fun z => z ≫ (c ≫ d)) hab) |>.trans <|
          (Category.assoc _ c d).symm |>.trans <|
            congrArg (fun z => z ≫ d) hmap.symm
  rw [hmor]
  let p :
      ModuleCat.of R R ⟶
        ModuleCat.of R Γ(M, ⊤) :=
    l ≫ q
  have htotal :
      tilde.toOpen (ModuleCat.of R R) ⊤ ≫
          (modulesSpecToSheaf.map
            ((tilde.functor R).map p ≫
              M.fromTildeΓ)).1.app
                (Opposite.op
                  (⊤ : (Spec R).Opens)) =
        p ≫
          (modulesSpecToSheaf.obj M).1.map
            (homOfLE le_top).op := by
    let a := tilde.toOpen (ModuleCat.of R R) ⊤
    let b :=
      (modulesSpecToSheaf.map
        ((tilde.functor R).map p)).1.app
          (Opposite.op
            (⊤ : (Spec R).Opens))
    let c :=
      (modulesSpecToSheaf.map
        M.fromTildeΓ).1.app
          (Opposite.op
            (⊤ : (Spec R).Opens))
    let r := (modulesSpecToSheaf.obj M).1.map
      (homOfLE (le_rfl : (⊤ : (Spec R).Opens) ≤ ⊤)).op
    have hbc :
        (modulesSpecToSheaf.map
          ((tilde.functor R).map p ≫ M.fromTildeΓ)).1.app
            (Opposite.op (⊤ : (Spec R).Opens)) = b ≫ c := by
      exact congrArg
        (fun z => z.1.app (Opposite.op (⊤ : (Spec R).Opens)))
        (modulesSpecToSheaf.map_comp
          ((tilde.functor R).map p) M.fromTildeΓ)
    have hb :
        a ≫ b =
          p ≫
            tilde.toOpen
              (ModuleCat.of R Γ(M, ⊤)) ⊤ :=
      tilde.toOpen_map_app p ⊤
    have hc :
        tilde.toOpen
              (ModuleCat.of R Γ(M, ⊤)) ⊤ ≫ c =
          r :=
      Scheme.Modules.toOpen_fromTildeΓ_app M ⊤
    change a ≫ _ = p ≫ r
    exact
      (congrArg (fun z => a ≫ z) hbc) |>.trans <|
        (Category.assoc a b c).symm |>.trans <|
          (congrArg (fun z => z ≫ c) hb) |>.trans <|
            (Category.assoc _ _ c) |>.trans <|
              congrArg (fun z => p ≫ z) hc
  have happ :=
    ConcreteCategory.congr_hom htotal (1 : R)
  have hone :
      (tilde.toOpen
        (ModuleCat.of R R) ⊤).hom (1 : R) =
        (show
          (modulesSpecToSheaf.obj
              (tilde (ModuleCat.of R R))).presheaf.obj
                (Opposite.op
                  (⊤ : (Spec R).Opens))
          from
            (1 : (Spec R).ringCatSheaf.obj.obj
              (Opposite.op
                (⊤ : (Spec R).Opens)))) := by
    change
      ((tilde.modulesSpecToSheafIso
        (ModuleCat.of R R)).app
          (Opposite.op (⊤ : (Spec R).Opens))).inv.hom
        (StructureSheaf.toOpenₗ R R ⊤ 1) =
          (show
            (modulesSpecToSheaf.obj
              (tilde (ModuleCat.of R R))).presheaf.obj
                (Opposite.op (⊤ : (Spec R).Opens))
            from
              (1 : (Spec R).ringCatSheaf.obj.obj
                (Opposite.op (⊤ : (Spec R).Opens))))
    rw [StructureSheaf.toOpenₗ_eq_const]
    change
      StructureSheaf.const (1 : R) (1 : R) ⊤
          (le_of_eq PrimeSpectrum.basicOpen_one.symm) =
        (1 : (Spec R).ringCatSheaf.obj.obj
          (Opposite.op (⊤ : (Spec R).Opens)))
    exact StructureSheaf.const_one ⊤
  change
    (modulesSpecToSheaf.map
      ((tilde.functor R).map p ≫
        M.fromTildeΓ)).1.app
          (Opposite.op
            (⊤ : (Spec R).Opens))
      ((tilde.toOpen
        (ModuleCat.of R R) ⊤).hom (1 : R)) =
      (modulesSpecToSheaf.obj M).1.map
          (homOfLE le_top).op
        (p.hom (1 : R)) at happ
  rw [hone] at happ
  simp [p, l, q,
    Finsupp.linearCombination_single] at happ
  change
    (modulesSpecToSheaf.map
      ((tilde.functor R).map p ≫
        M.fromTildeΓ)).1.app
          (Opposite.op
            (⊤ : (Spec R).Opens))
      (show
        (modulesSpecToSheaf.obj
          ((tilde.functor R).obj
            (ModuleCat.of R R))).presheaf.obj
            (Opposite.op
              (⊤ : (Spec R).Opens))
        from
          (1 : (Spec R).ringCatSheaf.obj.obj
            (Opposite.op
              (⊤ : (Spec R).Opens)))) =
      s i
  dsimp only [p, l, q]
  rw [Functor.map_comp (tilde.functor R)]
  exact @Eq.trans _ _ (id (s i)) _ happ (by rfl)

/-- The coproduct of the unit maps attached to top sections is the free
morphism associated to their compatible restrictions. -/
theorem sigmaDesc_homOfTopSection_eq_freeHomEquiv
    (M : (Spec R).Modules) {ι : Type u}
    (s : ι → Γ(M, ⊤)) :
    Limits.Sigma.desc
        (fun a => homOfTopSection M (s a)) =
      M.freeHomEquiv.symm
        (fun a => sectionsOfTop M (s a)) := by
  apply M.freeHomEquiv.injective
  funext i
  rw [Equiv.apply_symm_apply]
  apply M.unitHomEquiv.symm.injective
  calc
    _ =
        SheafOfModules.ιFree
            (R := (Spec R).ringCatSheaf) i ≫
          Limits.Sigma.desc
            (fun a => homOfTopSection M (s a)) :=
      SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply
        (Limits.Sigma.desc
          (fun a => homOfTopSection M (s a))) i
    _ = homOfTopSection M (s i) :=
      Limits.Sigma.ι_desc
        (fun a => homOfTopSection M (s a)) i
    _ = _ := rfl

/-- The coproduct of section maps agrees with the tilde-based affine
generator map. -/
theorem sigmaDesc_homOfTopSection_eq_freeToModuleOfTopSections
    (M : (Spec R).Modules) {ι : Type u}
    (s : ι → Γ(M, ⊤)) :
    Limits.Sigma.desc
        (fun a => homOfTopSection M (s a)) =
      freeToModuleOfTopSections M s :=
  (sigmaDesc_homOfTopSection_eq_freeHomEquiv M s).trans
    (freeToModuleOfTopSections_eq_freeHomEquiv M s).symm

/-- A spanning finite or infinite family of affine top sections gives an
epimorphic coproduct of its associated unit maps. -/
theorem sigmaDesc_homOfTopSection_epi
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    {ι : Type u} (s : ι → Γ(M, ⊤))
    (hs : Submodule.span R (Set.range s) = ⊤) :
    Epi
      (Limits.Sigma.desc
        (fun a => homOfTopSection M (s a))) := by
  rw [sigmaDesc_homOfTopSection_eq_freeToModuleOfTopSections]
  exact freeToModuleOfTopSections_epi M s hs

end AlgebraicGeometry.Scheme.Modules
