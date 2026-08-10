/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.DivisorLineBundle

/-!
# Naturality of the affine tilde tensor comparison

The affine comparison between the tensor product of two tilde sheaves and the tilde sheaf of
the module tensor product is natural in both module variables.  The proof first checks the
claim on arbitrary localized fractions, lifts it to the underlying presheaf comparison, and
then uses the monoidality of sheafification.

Only the hom and inverse naturality statements are public.  The localization and
sheafification implementation remains private.
-/

namespace MazurTorsion.AlgebraicGeometry.AffineTilde

open CategoryTheory MonoidalCategory TopologicalSpace
open _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

noncomputable section

/-- The standard monoidal structure on sheaves of modules over a scheme. -/
private noncomputable local instance affineTildeNaturalitySchemeModulesMonoidal
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private noncomputable local instance affineTildeNaturalityPresheafModulesMonoidalStruct
    (R : Type u) [CommRing R] :
    MonoidalCategoryStruct (Spec (CommRingCat.of R)).PresheafOfModules :=
  inferInstanceAs (MonoidalCategoryStruct
    (PresheafOfModules
      ((Spec (CommRingCat.of R)).sheaf.obj ⋙ forget₂ CommRingCat RingCat)))

private noncomputable local instance affineTildeNaturalityPresheafModulesMonoidal
    (R : Type u) [CommRing R] :
    MonoidalCategory (Spec (CommRingCat.of R)).PresheafOfModules :=
  inferInstanceAs (MonoidalCategory
    (PresheafOfModules
      ((Spec (CommRingCat.of R)).sheaf.obj ⋙ forget₂ CommRingCat RingCat)))

private noncomputable abbrev affineTildeNaturalityRingSheaf
    (R : Type u) [CommRing R] :=
  (⟨(Spec (CommRingCat.of R)).sheaf.obj ⋙ forget₂ CommRingCat RingCat,
    (Spec (CommRingCat.of R)).ringCatSheaf.property⟩ : Sheaf _ RingCat.{u})

private noncomputable local instance affineTildeNaturalitySheafModulesMonoidal
    (R : Type u) [CommRing R] :
    MonoidalCategory
      (SheafOfModules (affineTildeNaturalityRingSheaf R)) := by
  change MonoidalCategory (Spec (CommRingCat.of R)).Modules
  exact Scheme.Modules.monoidalCategory (Spec (CommRingCat.of R))

private noncomputable abbrev affineTildeNaturalityRingSheafId
    (R : Type u) [CommRing R] :=
  𝟙 (affineTildeNaturalityRingSheaf R).obj

private noncomputable abbrev affineTildeNaturalitySheafification
    (R : Type u) [CommRing R] :=
  PresheafOfModules.sheafification (affineTildeNaturalityRingSheafId R)

private noncomputable abbrev affineTildeNaturalitySheafificationW
    (R : Type u) [CommRing R] :=
  PresheafOfModules.sheafificationW (affineTildeNaturalityRingSheafId R)

private noncomputable local instance affineTildeNaturalitySheafificationIsLocalization
    (R : Type u) [CommRing R] :
    (affineTildeNaturalitySheafification R).IsLocalization
      (affineTildeNaturalitySheafificationW R) :=
  PresheafOfModules.sheafificationW_isLocalization _

private noncomputable local instance affineTildeNaturalitySheafificationWIsMonoidal
    (R : Type u) [CommRing R] :
    (affineTildeNaturalitySheafificationW R).IsMonoidal :=
  PresheafOfModules.sheafificationW_isMonoidal _

private noncomputable abbrev affineTildeNaturalityLocalizedSheafification
    (R : Type u) [CommRing R] :=
  Localization.Monoidal.toMonoidalCategory
    (affineTildeNaturalitySheafification R)
    (affineTildeNaturalitySheafificationW R) (Iso.refl _)

private noncomputable local instance affineTildeNaturalitySheafificationMonoidal
    (R : Type u) [CommRing R] :
    (affineTildeNaturalityLocalizedSheafification R).Monoidal := by
  change (Localization.Monoidal.toMonoidalCategory
    (affineTildeNaturalitySheafification R)
    (affineTildeNaturalitySheafificationW R) (Iso.refl _)).Monoidal
  infer_instance

/-- The localization tensor equivalence commutes with maps in both module variables. -/
private lemma localizedTensorEquiv_naturality
    (R : Type u) [CommRing R]
    {M₁ M₂ N₁ N₂ : ModuleCat.{u} R}
    (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂)
    (S : Submonoid R) (a : LocalizedModule S M₁) (b : LocalizedModule S N₁) :
    localizedTensorEquiv R M₂ N₂ S
        (IsLocalizedModule.map S
            (LocalizedModule.mkLinearMap S M₁)
            (LocalizedModule.mkLinearMap S M₂) f.hom a ⊗ₜ[Localization S]
          IsLocalizedModule.map S
            (LocalizedModule.mkLinearMap S N₁)
            (LocalizedModule.mkLinearMap S N₂) g.hom b) =
      IsLocalizedModule.map S
        (LocalizedModule.mkLinearMap S (M₁ ⊗[R] N₁))
        (LocalizedModule.mkLinearMap S (M₂ ⊗[R] N₂)) (f ⊗ₘ g).hom
        (localizedTensorEquiv R M₁ N₁ S
          (a ⊗ₜ[Localization S] b)) := by
  induction a using LocalizedModule.induction_on with
  | h m s =>
    induction b using LocalizedModule.induction_on with
    | h n t =>
      simp only [IsLocalizedModule.map_LocalizedModules,
        localizedTensorEquiv_mk]
      exact congrArg (fun z => LocalizedModule.mk z (s * t))
        (ModuleCat.MonoidalCategory.tensorHom_tmul f g m n).symm

/-- The sectionwise pure-tensor pairing commutes with tilde maps. -/
private lemma sectionsTensorPure_naturality
    (R : Type u) [CommRing R]
    {M₁ M₂ N₁ N₂ : ModuleCat.{u} R}
    (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂)
    (U : Opens (PrimeSpectrum.Top R))
    (a : (structureSheafInType R M₁).obj.obj (.op U))
    (b : (structureSheafInType R N₁).obj.obj (.op U)) :
    sectionsTensorPure R M₂ N₂ U
        ((_root_.AlgebraicGeometry.tilde.map
          (R := CommRingCat.of R) f).val.app (.op U) a)
        ((_root_.AlgebraicGeometry.tilde.map
          (R := CommRingCat.of R) g).val.app (.op U) b) =
      (_root_.AlgebraicGeometry.tilde.map
        (R := CommRingCat.of R) (f ⊗ₘ g)).val.app (.op U)
        (sectionsTensorPure R M₁ N₁ U a b) := by
  apply Subtype.ext
  funext x
  letI := x.1.isPrime
  change localizedTensorEquiv R M₂ N₂ x.1.asIdeal.primeCompl
      (IsLocalizedModule.map x.1.asIdeal.primeCompl
          (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl M₁)
          (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl M₂) f.hom (a.1 x) ⊗ₜ[
            StructureSheaf.Localizations R x.1]
        IsLocalizedModule.map x.1.asIdeal.primeCompl
          (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl N₁)
          (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl N₂) g.hom (b.1 x)) =
    IsLocalizedModule.map x.1.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl (M₁ ⊗[R] N₁))
      (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl (M₂ ⊗[R] N₂))
      (f ⊗ₘ g).hom
      (localizedTensorEquiv R M₁ N₁ x.1.asIdeal.primeCompl
        (a.1 x ⊗ₜ[StructureSheaf.Localizations R x.1] b.1 x))
  exact localizedTensorEquiv_naturality R f g x.1.asIdeal.primeCompl (a.1 x) (b.1 x)

/-- The presheaf morphism underlying the affine tilde tensor comparison is natural. -/
private theorem tildeTensorUnderlyingHom_naturality
    (R : Type u) [CommRing R]
    {M₁ M₂ N₁ N₂ : ModuleCat.{u} R}
    (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂) :
    (((_root_.AlgebraicGeometry.tilde.map
          (R := CommRingCat.of R) f).val ⊗ₘ
        (_root_.AlgebraicGeometry.tilde.map
          (R := CommRingCat.of R) g).val) ≫
        tildeTensorUnderlyingHom R M₂ N₂) =
      tildeTensorUnderlyingHom R M₁ N₁ ≫
        (_root_.AlgebraicGeometry.tilde.map
          (R := CommRingCat.of R) (f ⊗ₘ g)).val := by
  ext1 U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro a b
  change sectionsTensorPure R M₂ N₂ U.unop
      ((_root_.AlgebraicGeometry.tilde.map
        (R := CommRingCat.of R) f).val.app U a)
      ((_root_.AlgebraicGeometry.tilde.map
        (R := CommRingCat.of R) g).val.app U b) =
    (_root_.AlgebraicGeometry.tilde.map
      (R := CommRingCat.of R) (f ⊗ₘ g)).val.app U
      (sectionsTensorPure R M₁ N₁ U.unop a b)
  exact sectionsTensorPure_naturality R f g U.unop a b

/-- Naturality of the reflective sheafification counit in its hom orientation. -/
private theorem sheafifyValIso_hom_naturality
    (R : Type u) [CommRing R]
    {P Q : (Spec (CommRingCat.of R)).Modules} (f : P ⟶ Q) :
    (affineTildeNaturalitySheafification R).map f.val ≫
        (sheafifyValIso R Q).hom =
      (sheafifyValIso R P).hom ≫ f := by
  exact (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Spec (CommRingCat.of R)).ringCatSheaf.obj)).counit.naturality f

/-- Naturality of the inverse reflective sheafification counit. -/
private theorem sheafifyValIso_inv_naturality
    (R : Type u) [CommRing R]
    {P Q : (Spec (CommRingCat.of R)).Modules} (f : P ⟶ Q) :
    f ≫ (sheafifyValIso R Q).inv =
      (sheafifyValIso R P).inv ≫
        (affineTildeNaturalitySheafification R).map f.val := by
  let L := affineTildeNaturalitySheafification R
  let cP : L.obj P.val ≅ P := sheafifyValIso R P
  let cQ : L.obj Q.val ≅ Q := sheafifyValIso R Q
  have hhom := sheafifyValIso_hom_naturality R f
  change L.map f.val ≫ cQ.hom = cP.hom ≫ f at hhom
  change f ≫ cQ.inv = cP.inv ≫ L.map f.val
  have hright :
      f = cP.inv ≫ (L.map f.val ≫ cQ.hom) :=
    cP.eq_inv_comp.mpr hhom.symm
  have hassoc :
      (cP.inv ≫ L.map f.val) ≫ cQ.hom =
        cP.inv ≫ (L.map f.val ≫ cQ.hom) :=
    Category.assoc _ _ _
  exact cQ.comp_inv_eq.mpr (hright.trans hassoc.symm)

/-- Naturality of the comparison from the tensor of two sheaves to the sheafification of their
underlying presheaf tensor. -/
private theorem tensorAsSheafification_hom_naturality
    (R : Type u) [CommRing R]
    {M₁ M₂ N₁ N₂ : ModuleCat.{u} R}
    (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂) :
    (_root_.AlgebraicGeometry.tilde.map
        (R := CommRingCat.of R) f ⊗ₘ
      _root_.AlgebraicGeometry.tilde.map
        (R := CommRingCat.of R) g) ≫
        (tensorAsSheafification R M₂ N₂).hom =
      (tensorAsSheafification R M₁ N₁).hom ≫
        (affineTildeNaturalitySheafification R).map
          ((_root_.AlgebraicGeometry.tilde.map
              (R := CommRingCat.of R) f).val ⊗ₘ
            (_root_.AlgebraicGeometry.tilde.map
              (R := CommRingCat.of R) g).val) := by
  let L := affineTildeNaturalitySheafification R
  let W := affineTildeNaturalitySheafificationW R
  let F := affineTildeNaturalityLocalizedSheafification R
  let TM₁ := _root_.AlgebraicGeometry.tilde (R := CommRingCat.of R) M₁
  let TM₂ := _root_.AlgebraicGeometry.tilde (R := CommRingCat.of R) M₂
  let TN₁ := _root_.AlgebraicGeometry.tilde (R := CommRingCat.of R) N₁
  let TN₂ := _root_.AlgebraicGeometry.tilde (R := CommRingCat.of R) N₂
  let cM₁ := sheafifyValIso R TM₁
  let cM₂ := sheafifyValIso R TM₂
  let cN₁ := sheafifyValIso R TN₁
  let cN₂ := sheafifyValIso R TN₂
  let tf := _root_.AlgebraicGeometry.tilde.map (R := CommRingCat.of R) f
  let tg := _root_.AlgebraicGeometry.tilde.map (R := CommRingCat.of R) g
  let lf := L.map tf.val
  let lg := L.map tg.val
  let a := tf ⊗ₘ tg
  let p := tf.val ⊗ₘ tg.val
  let e₁ := cM₁.inv ⊗ₘ cN₁.inv
  let e₂ := cM₂.inv ⊗ₘ cN₂.inv
  let μ₁ := (Localization.Monoidal.μ L W (Iso.refl _) TM₁.val TN₁.val).hom
  let μ₂ := (Localization.Monoidal.μ L W (Iso.refl _) TM₂.val TN₂.val).hom
  have hf := sheafifyValIso_inv_naturality R tf
  have hg := sheafifyValIso_inv_naturality R tg
  change tf ≫ cM₂.inv = cM₁.inv ≫ lf at hf
  change tg ≫ cN₂.inv = cN₁.inv ≫ lg at hg
  have hfront : a ≫ e₂ = e₁ ≫ (lf ⊗ₘ lg) := by
    have hleft :
        a ≫ e₂ = (tf ≫ cM₂.inv) ⊗ₘ (tg ≫ cN₂.inv) :=
      MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _
    have hmiddle :
        (tf ≫ cM₂.inv) ⊗ₘ (tg ≫ cN₂.inv) =
          (cM₁.inv ≫ lf) ⊗ₘ (cN₁.inv ≫ lg) :=
      congrArg₂ (fun x y ↦ x ⊗ₘ y) hf hg
    have hright :
        e₁ ≫ (lf ⊗ₘ lg) =
          (cM₁.inv ≫ lf) ⊗ₘ (cN₁.inv ≫ lg) :=
      MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _
    exact hleft.trans (hmiddle.trans hright.symm)
  have hμ := Functor.LaxMonoidal.μ_natural F tf.val tg.val
  change (lf ⊗ₘ lg) ≫ μ₂ = μ₁ ≫ L.map p at hμ
  change a ≫ (e₂ ≫ μ₂) = (e₁ ≫ μ₁) ≫ L.map p
  have h₁ : a ≫ (e₂ ≫ μ₂) = (a ≫ e₂) ≫ μ₂ :=
    (Category.assoc _ _ _).symm
  have h₂ : (a ≫ e₂) ≫ μ₂ = (e₁ ≫ (lf ⊗ₘ lg)) ≫ μ₂ :=
    congrArg (fun k ↦ k ≫ μ₂) hfront
  have h₃ : (e₁ ≫ (lf ⊗ₘ lg)) ≫ μ₂ =
      e₁ ≫ ((lf ⊗ₘ lg) ≫ μ₂) :=
    Category.assoc _ _ _
  have h₄ : e₁ ≫ ((lf ⊗ₘ lg) ≫ μ₂) =
      e₁ ≫ (μ₁ ≫ L.map p) :=
    congrArg (e₁ ≫ ·) hμ
  have h₅ : e₁ ≫ (μ₁ ≫ L.map p) = (e₁ ≫ μ₁) ≫ L.map p :=
    (Category.assoc _ _ _).symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

/-- Hom expansion of the affine tilde tensor comparison. -/
private theorem tildeTensorIso_hom_eq
    (R : Type u) [CommRing R] (M N : ModuleCat.{u} R) :
    (tildeTensorIso R M N).hom =
      (tensorAsSheafification R M N).hom ≫
        (affineTildeNaturalitySheafification R).map
          (tildeTensorUnderlyingHom R M N) ≫
        (sheafifyValIso R
          (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of R)
            (ModuleCat.of R (M ⊗[R] N)))).hom := by
  rfl

/-- The affine tilde tensor comparison is natural in both module variables. -/
theorem tildeTensorIso_hom_naturality
    (R : Type u) [CommRing R]
    {M₁ M₂ N₁ N₂ : ModuleCat.{u} R}
    (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂) :
    (_root_.AlgebraicGeometry.tilde.map
        (R := CommRingCat.of R) f ⊗ₘ
      _root_.AlgebraicGeometry.tilde.map
        (R := CommRingCat.of R) g) ≫
        (tildeTensorIso R M₂ N₂).hom =
      (tildeTensorIso R M₁ N₁).hom ≫
        _root_.AlgebraicGeometry.tilde.map
          (R := CommRingCat.of R) (f ⊗ₘ g) := by
  rw [tildeTensorIso_hom_eq R M₂ N₂, tildeTensorIso_hom_eq R M₁ N₁]
  let L := affineTildeNaturalitySheafification R
  let A := _root_.AlgebraicGeometry.tilde.map (R := CommRingCat.of R) f ⊗ₘ
    _root_.AlgebraicGeometry.tilde.map (R := CommRingCat.of R) g
  let B := _root_.AlgebraicGeometry.tilde.map (R := CommRingCat.of R) (f ⊗ₘ g)
  let p := (_root_.AlgebraicGeometry.tilde.map
      (R := CommRingCat.of R) f).val ⊗ₘ
    (_root_.AlgebraicGeometry.tilde.map (R := CommRingCat.of R) g).val
  let t₁ := tildeTensorUnderlyingHom R M₁ N₁
  let t₂ := tildeTensorUnderlyingHom R M₂ N₂
  let e₁ := (tensorAsSheafification R M₁ N₁).hom
  let e₂ := (tensorAsSheafification R M₂ N₂).hom
  let c₁ := (sheafifyValIso R
    (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of R)
      (ModuleCat.of R (M₁ ⊗[R] N₁)))).hom
  let c₂ := (sheafifyValIso R
    (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of R)
      (ModuleCat.of R (M₂ ⊗[R] N₂)))).hom
  have he := tensorAsSheafification_hom_naturality R f g
  change A ≫ e₂ = e₁ ≫ L.map p at he
  have ht := tildeTensorUnderlyingHom_naturality R f g
  change p ≫ t₂ = t₁ ≫ B.val at ht
  have hc := sheafifyValIso_hom_naturality R B
  change L.map B.val ≫ c₂ = c₁ ≫ B at hc
  have hmap : L.map p ≫ L.map t₂ = L.map t₁ ≫ L.map B.val := by
    have hleft : L.map p ≫ L.map t₂ = L.map (p ≫ t₂) :=
      (L.map_comp p t₂).symm
    have hmiddle : L.map (p ≫ t₂) = L.map (t₁ ≫ B.val) :=
      congrArg (fun q ↦ L.map q) ht
    have hright : L.map (t₁ ≫ B.val) = L.map t₁ ≫ L.map B.val :=
      L.map_comp t₁ B.val
    exact hleft.trans (hmiddle.trans hright)
  have htail :
      L.map p ≫ (L.map t₂ ≫ c₂) =
        (L.map t₁ ≫ c₁) ≫ B := by
    have h₁ : L.map p ≫ (L.map t₂ ≫ c₂) =
        (L.map p ≫ L.map t₂) ≫ c₂ :=
      (Category.assoc _ _ _).symm
    have h₂ : (L.map p ≫ L.map t₂) ≫ c₂ =
        (L.map t₁ ≫ L.map B.val) ≫ c₂ :=
      congrArg (fun k ↦ k ≫ c₂) hmap
    have h₃ : (L.map t₁ ≫ L.map B.val) ≫ c₂ =
        L.map t₁ ≫ (L.map B.val ≫ c₂) :=
      Category.assoc _ _ _
    have h₄ : L.map t₁ ≫ (L.map B.val ≫ c₂) =
        L.map t₁ ≫ (c₁ ≫ B) :=
      congrArg (L.map t₁ ≫ ·) hc
    have h₅ : L.map t₁ ≫ (c₁ ≫ B) = (L.map t₁ ≫ c₁) ≫ B :=
      (Category.assoc _ _ _).symm
    exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))
  change A ≫ (e₂ ≫ (L.map t₂ ≫ c₂)) =
    (e₁ ≫ (L.map t₁ ≫ c₁)) ≫ B
  calc
    A ≫ (e₂ ≫ (L.map t₂ ≫ c₂)) =
        (A ≫ e₂) ≫ (L.map t₂ ≫ c₂) :=
      (Category.assoc _ _ _).symm
    _ = (e₁ ≫ L.map p) ≫ (L.map t₂ ≫ c₂) :=
      congrArg (fun k ↦ k ≫ (L.map t₂ ≫ c₂)) he
    _ = e₁ ≫ (L.map p ≫ (L.map t₂ ≫ c₂)) := Category.assoc _ _ _
    _ = e₁ ≫ ((L.map t₁ ≫ c₁) ≫ B) := congrArg (e₁ ≫ ·) htail
    _ = (e₁ ≫ (L.map t₁ ≫ c₁)) ≫ B :=
      (Category.assoc _ _ _).symm

/-- Inverse naturality of the affine tilde tensor comparison. -/
theorem tildeTensorIso_inv_naturality
    (R : Type u) [CommRing R]
    {M₁ M₂ N₁ N₂ : ModuleCat.{u} R}
    (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂) :
    _root_.AlgebraicGeometry.tilde.map
        (R := CommRingCat.of R) (f ⊗ₘ g) ≫
        (tildeTensorIso R M₂ N₂).inv =
      (tildeTensorIso R M₁ N₁).inv ≫
        (_root_.AlgebraicGeometry.tilde.map
            (R := CommRingCat.of R) f ⊗ₘ
          _root_.AlgebraicGeometry.tilde.map
            (R := CommRingCat.of R) g) := by
  rw [(tildeTensorIso R M₂ N₂).comp_inv_eq, Category.assoc,
    (tildeTensorIso R M₁ N₁).eq_inv_comp]
  exact (tildeTensorIso_hom_naturality R f g).symm

end

end MazurTorsion.AlgebraicGeometry.AffineTilde
