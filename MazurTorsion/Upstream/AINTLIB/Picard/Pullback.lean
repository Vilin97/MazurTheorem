/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Localization.Monoidal.Functor
import Mathlib.LinearAlgebra.Finsupp.Pi
import MazurTorsion.Upstream.AINTLIB.Picard.Pic

/-!
# General pullback–tensor compatibility — decomposition skeleton (Route G)

This is an option-free selective port of
[`PullbackTensorGeneral.lean`](https://github.com/CBirkbeck/AINTLIB/blob/7ecbba9dbb7fee076a1b77a6cd516fc6de46d684/projects/ModularCurves/ModularCurves/ForMathlib/PullbackTensorGeneral.lean)
from AINTLIB commit `7ecbba9dbb7fee076a1b77a6cd516fc6de46d684`.  The unused
`PullbackTensorMonoidal` import is deliberately omitted.  In particular, this file does not
import AINTLIB's option-heavy Picard or invertible-sheaf closure.
The small `sheafifyValIso` comparison needed at the sheaf boundary is selectively retained
from AINTLIB's `Picard/InvertibleSheaf.lean` at the same commit.

`/develop --decompose` skeleton for **D-PresPB′-general** (board v10.98/v10.99): the general-`f`
pullback–tensor gate of the GME (2.16) Picard-functoriality chain. Route G (construction-grain):
give the presheaf pushforward its lax monoidal structure, get the oplax comparison `δ` on the
pullback by doctrinal adjunction, show `δ` is an iso on free-yoneda generators (on an Opens-site
the tensor of free-yonedas is the free-yoneda of the meet — the lattice miracle — and
`freeFunctorCompPullbackIso` matches the pullback side), and extend along free presentations by
two single-variable five-lemma passes in the abelian target. Payoff:
`functorMonoidalOfComp` ⟹ `(Modules.pullback f).Monoidal` ⟹ `Skeleton.monoidHom` ⟹
`Pic(f) : Pic X →* Pic Y`.

All leaves are stated `Nonempty`-wrapped (`Prop`s, so the monoidal data carry no proof
assumptions under the v10.8 discipline; the data is built at execution time, each structure
landing only when its leaf is fully checked). Full route adjudication, verbatim anchors and
attack logs:
`.mathlib-quality/decomposition-pullback-monoidal-general.md`.
-/

universe v₁ v₂ v₃ u₁ u₂ u₃ u w w'

open CategoryTheory MonoidalCategory Functor

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D]
  {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}

/-- Taking the mate of a monoidal natural transformation between right adjoints
produces a monoidal natural transformation between the corresponding left adjoints. -/
theorem conjugateEquiv_symm_isMonoidal
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    [L₁.Monoidal] [L₂.Monoidal] [R₁.LaxMonoidal] [R₂.LaxMonoidal]
    (hadj₁ : adj₁.IsMonoidal) (hadj₂ : adj₂.IsMonoidal)
    (α : R₁ ⟶ R₂) (hα : α.IsMonoidal) :
    ((conjugateEquiv adj₁ adj₂).symm α).IsMonoidal := by
  letI := hadj₁
  letI := hadj₂
  letI := hα
  let β : L₂ ⟶ L₁ :=
    L₂.leftUnitor.inv ≫
      Functor.whiskerRight adj₁.unit L₂ ≫
      (Functor.associator L₁ R₁ L₂).hom ≫
      Functor.whiskerLeft L₁ (Functor.whiskerRight α L₂) ≫
      Functor.whiskerLeft L₁ adj₂.counit ≫
      L₁.rightUnitor.hom
  have hβ : β.IsMonoidal := by
    dsimp only [β]
    infer_instance
  rw [show (conjugateEquiv adj₁ adj₂).symm α = β by
    ext X
    rw [conjugateEquiv_symm_apply_app]
    simp only [β, NatTrans.comp_app, Functor.leftUnitor_inv_app,
      Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
    erw [Category.id_comp, Category.id_comp, Category.comp_id]]
  exact hβ

variable {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]

/-- Monoidality of a natural transformation can be checked after precomposition
with a monoidal localization functor. -/
theorem NatTrans.IsMonoidal.of_whiskerLeft_localization
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    [W.ContainsIdentities] [L.Monoidal]
    {F G : D ⥤ E} [F.Monoidal] [G.Monoidal]
    (τ : F ⟶ G) (h : (Functor.whiskerLeft L τ).IsMonoidal) :
    τ.IsMonoidal := by
  letI := h
  refine { unit := ?_, tensor := fun X Y ↦ ?_ }
  · have hu := NatTrans.IsMonoidal.unit
      (τ := Functor.whiskerLeft L τ)
    change (Functor.LaxMonoidal.ε F ≫
        F.map (Functor.LaxMonoidal.ε L)) ≫
      τ.app (L.obj (𝟙_ C)) =
        Functor.LaxMonoidal.ε G ≫
          G.map (Functor.LaxMonoidal.ε L) at hu
    apply (cancel_mono (G.map (Functor.LaxMonoidal.ε L))).1
    rw [Category.assoc, ← τ.naturality]
    simpa only [Category.assoc] using hu
  · let lhs : MonoidalCategory.curriedTensorPre F ⟶
        MonoidalCategory.curriedTensorPost G :=
      (Functor.curriedTensorPreIsoPost F).hom ≫
        MonoidalCategory.curriedTensorPostFunctor.map τ
    let rhs : MonoidalCategory.curriedTensorPre F ⟶
        MonoidalCategory.curriedTensorPost G :=
      MonoidalCategory.curriedTensorPreFunctor.map τ ≫
        (Functor.curriedTensorPreIsoPost G).hom
    have hcurried : lhs = rhs := by
      apply Localization.natTrans₂_ext L L W W
      intro A B
      change Functor.LaxMonoidal.μ F (L.obj A) (L.obj B) ≫
          τ.app (L.obj A ⊗ L.obj B) =
        (τ.app (L.obj A) ⊗ₘ τ.app (L.obj B)) ≫
          Functor.LaxMonoidal.μ G (L.obj A) (L.obj B)
      apply (cancel_mono (G.map (Functor.LaxMonoidal.μ L A B))).1
      rw [Category.assoc, ← τ.naturality]
      have ht := NatTrans.IsMonoidal.tensor
        (τ := Functor.whiskerLeft L τ) A B
      simp only [Functor.LaxMonoidal.comp_μ,
        Functor.whiskerLeft_app] at ht
      rw [Category.assoc] at ht
      conv_rhs at ht => rw [← Category.assoc]
      change @Eq (F.obj (L.obj A) ⊗ F.obj (L.obj B) ⟶
        G.obj (L.obj (A ⊗ B))) _ _ at ht
      exact ht
    exact NatTrans.congr_app (NatTrans.congr_app hcurried X) Y

end CategoryTheory

namespace PresheafOfModules

section RestrictScalarsLax

variable {C : Type u₁} [Category.{v₁} C] {T₁ T₂ : Cᵒᵖ ⥤ CommRingCat.{u}}
  (ψ : T₁ ⋙ forget₂ CommRingCat RingCat ⟶ T₂ ⋙ forget₂ CommRingCat RingCat)

/-- **[D-PresPB′-general], leaf B1a (unit component).** The unit comparison of the lax
monoidal structure on presheaf-level restriction of scalars, at a section: the ring map
`ψ.app U` itself, as a linear map into the restricted module. -/
noncomputable def restrictScalarsLaxεApp (U : Cᵒᵖ) :
    ((𝟙_ (PresheafOfModules.{u} (T₁ ⋙ forget₂ CommRingCat RingCat))).obj U) ⟶
      ((restrictScalars ψ).obj
        (𝟙_ (PresheafOfModules.{u} (T₂ ⋙ forget₂ CommRingCat RingCat)))).obj U :=
  ModuleCat.ofHom
    (X := (𝟙_ (PresheafOfModules.{u} (T₁ ⋙ forget₂ CommRingCat RingCat))).obj U)
    (Y := ((restrictScalars ψ).obj
      (𝟙_ (PresheafOfModules.{u} (T₂ ⋙ forget₂ CommRingCat RingCat)))).obj U)
    { toFun := fun x => (ψ.app U).hom x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x => (ψ.app U).hom.map_mul r x }

@[simp]
lemma restrictScalarsLaxεApp_apply (U : Cᵒᵖ)
    (x : ((𝟙_ (PresheafOfModules.{u} (T₁ ⋙ forget₂ CommRingCat RingCat))).obj U)) :
    restrictScalarsLaxεApp ψ U x = (ψ.app U).hom x :=
  rfl

/-- **[D-PresPB′-general], leaf B1a (tensorator component).** The tensorator of the lax
monoidal structure on presheaf-level restriction of scalars, at a section:
`x ⊗ₜ y ↦ x ⊗ₜ y` from the tensor over the downstairs ring to the (restricted) tensor over
the upstairs ring (`TensorProduct.mapOfCompatibleSMul` — the lax direction needs no
bijectivity: the downstairs action slides in the upstairs tensor because it factors
through `ψ`). -/
noncomputable def restrictScalarsLaxμApp
    (P Q : PresheafOfModules.{u} (T₂ ⋙ forget₂ CommRingCat RingCat)) (U : Cᵒᵖ) :
    (((restrictScalars ψ).obj P ⊗ (restrictScalars ψ).obj Q).obj U) ⟶
      (((restrictScalars ψ).obj (P ⊗ Q)).obj U) := by
  letI : Module ↑((T₁ ⋙ forget₂ CommRingCat RingCat).obj U) ↑(P.obj U) :=
    Module.compHom _ ((ψ.app U).hom)
  letI : Module ↑((T₁ ⋙ forget₂ CommRingCat RingCat).obj U) ↑(Q.obj U) :=
    Module.compHom _ ((ψ.app U).hom)
  letI : Algebra ↑((T₁ ⋙ forget₂ CommRingCat RingCat).obj U)
      ↑((T₂ ⋙ forget₂ CommRingCat RingCat).obj U) := ((ψ.app U).hom).toAlgebra
  haveI : IsScalarTower ↑((T₁ ⋙ forget₂ CommRingCat RingCat).obj U)
      ↑((T₂ ⋙ forget₂ CommRingCat RingCat).obj U) ↑(P.obj U) :=
    ⟨fun r s m => mul_smul ((ψ.app U).hom r) s m⟩
  haveI : IsScalarTower ↑((T₁ ⋙ forget₂ CommRingCat RingCat).obj U)
      ↑((T₂ ⋙ forget₂ CommRingCat RingCat).obj U) ↑(Q.obj U) :=
    ⟨fun r s n => mul_smul ((ψ.app U).hom r) s n⟩
  haveI : SMulCommClass ↑((T₂ ⋙ forget₂ CommRingCat RingCat).obj U)
      ↑((T₁ ⋙ forget₂ CommRingCat RingCat).obj U) ↑(P.obj U) :=
    ⟨fun s r m => by
      change s • (ψ.app U).hom r • m = (ψ.app U).hom r • s • m
      rw [smul_comm]⟩
  haveI : SMulCommClass ↑((T₁ ⋙ forget₂ CommRingCat RingCat).obj U)
      ↑((T₁ ⋙ forget₂ CommRingCat RingCat).obj U) ↑(P.obj U) :=
    ⟨fun r r' m => by
      change (ψ.app U).hom r • (ψ.app U).hom r' • m =
        (ψ.app U).hom r' • (ψ.app U).hom r • m
      rw [smul_comm]⟩
  exact ModuleCat.ofHom
    (X := (((restrictScalars ψ).obj P ⊗ (restrictScalars ψ).obj Q).obj U))
    (Y := (((restrictScalars ψ).obj (P ⊗ Q)).obj U))
    (TensorProduct.mapOfCompatibleSMul ↑((T₂ ⋙ forget₂ CommRingCat RingCat).obj U)
      ↑((T₁ ⋙ forget₂ CommRingCat RingCat).obj U)
      ↑((T₁ ⋙ forget₂ CommRingCat RingCat).obj U) ↑(P.obj U) ↑(Q.obj U))

@[simp]
lemma restrictScalarsLaxμApp_tmul
    (P Q : PresheafOfModules.{u} (T₂ ⋙ forget₂ CommRingCat RingCat)) (U : Cᵒᵖ)
    (p : ↑(((restrictScalars ψ).obj P).obj U)) (q : ↑(((restrictScalars ψ).obj Q).obj U)) :
    restrictScalarsLaxμApp ψ P Q U (p ⊗ₜ q) =
      (p ⊗ₜ q : ↑(((restrictScalars ψ).obj (P ⊗ Q)).obj U)) :=
  rfl

private lemma restrictScalars_map_app_apply
    {P Q : PresheafOfModules.{u} (T₂ ⋙ forget₂ CommRingCat RingCat)}
    (g : P ⟶ Q) (U : Cᵒᵖ) (p : ((restrictScalars ψ).obj P).obj U) :
    ((restrictScalars ψ).map g).app U p = g.app U p :=
  rfl

/-- **[D-PresPB′-general], leaf B1a (unit).** The unit comparison as a morphism of presheaves
of modules; naturality is the naturality of `ψ`. -/
noncomputable def restrictScalarsLaxε :
    (𝟙_ (PresheafOfModules.{u} (T₁ ⋙ forget₂ CommRingCat RingCat))) ⟶
      (restrictScalars ψ).obj
        (𝟙_ (PresheafOfModules.{u} (T₂ ⋙ forget₂ CommRingCat RingCat))) where
  app U := restrictScalarsLaxεApp ψ U
  naturality {U V} f := by
    ext
    simp only [Functor.comp_obj, CommRingCat.forgetToRingCat_obj, Functor.comp_map,
      CommRingCat.forgetToRingCat_map_hom, ModuleCat.hom_comp]
    have h := RingHom.congr_fun (congrArg RingCat.Hom.hom (ψ.naturality f)) 1
    simp only [RingCat.hom_comp, RingHom.comp_apply] at h
    exact h

/-- **[D-PresPB′-general], leaf B1a (tensorator).** The tensorator as a morphism of
presheaves of modules; naturality is a `tmul`-chase (all components are `x ⊗ₜ y ↦ x ⊗ₜ y`). -/
noncomputable def restrictScalarsLaxμ
    (P Q : PresheafOfModules.{u} (T₂ ⋙ forget₂ CommRingCat RingCat)) :
    (restrictScalars ψ).obj P ⊗ (restrictScalars ψ).obj Q ⟶
      (restrictScalars ψ).obj (P ⊗ Q) where
  app U := restrictScalarsLaxμApp ψ P Q U
  naturality {U V} f := ModuleCat.MonoidalCategory.tensor_ext (fun p q => by
    erw [Monoidal.tensorObj_map_tmul])

/-- **[D-PresPB′-general], leaf B1a.** Presheaf-level restriction of scalars along an
arbitrary morphism of `CommRingCat`-valued ring presheaves is lax monoidal (sectionwise
`x ⊗ₜ y ↦ x ⊗ₜ y`; no iso hypothesis). -/
@[implicit_reducible]
noncomputable def restrictScalarsLaxMonoidal : (restrictScalars ψ).LaxMonoidal where
  ε := restrictScalarsLaxε ψ
  μ P Q := restrictScalarsLaxμ ψ P Q
  μ_natural_left {P P'} f Q := by
    ext1 U
    refine ModuleCat.MonoidalCategory.tensor_ext (fun p q => ?_)
    rfl
  μ_natural_right {Q Q'} P f := by
    ext1 U
    refine ModuleCat.MonoidalCategory.tensor_ext (fun p q => ?_)
    rfl
  associativity P Q R' := by
    ext1 U
    refine ModuleCat.MonoidalCategory.tensor_ext₃' (fun p q r => ?_)
    rfl
  left_unitality P := by
    ext1 U
    refine ModuleCat.MonoidalCategory.tensor_ext (fun r p => ?_)
    rfl
  right_unitality P := by
    ext1 U
    refine ModuleCat.MonoidalCategory.tensor_ext (fun p r => ?_)
    rfl

private lemma restrictScalarsLaxμ_app_tmul
    (P Q : PresheafOfModules.{u} (T₂ ⋙ forget₂ CommRingCat RingCat)) (U : Cᵒᵖ)
    (p : ((restrictScalars ψ).obj P).obj U) (q : ((restrictScalars ψ).obj Q).obj U) :
    letI := restrictScalarsLaxMonoidal ψ
    (Functor.LaxMonoidal.μ (restrictScalars ψ) P Q).app U (p ⊗ₜ q) =
      (p ⊗ₜ q : ((restrictScalars ψ).obj (P ⊗ Q)).obj U) :=
  rfl

end RestrictScalarsLax

section LaxPushforward

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}}
  (φ : S ⋙ forget₂ CommRingCat RingCat ⟶
    F.op ⋙ (R ⋙ forget₂ CommRingCat RingCat))

private lemma pushforward₀μ_app_tmul
    (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) (V : Cᵒᵖ)
    (x : ((pushforward₀OfCommRingCat F R).obj M).obj V)
    (y : ((pushforward₀OfCommRingCat F R).obj N).obj V) :
    (Functor.LaxMonoidal.μ (pushforward₀OfCommRingCat F R) M N).app V (x ⊗ₜ y) =
      (x ⊗ₜ y : ((pushforward₀OfCommRingCat F R).obj (M ⊗ N)).obj V) :=
  rfl

/-- The pushforward, spelled as its definitional factorization `pushforward₀ ⋙
restrictScalars` (the spelling at which both factors carry their lax monoidal structures
natively — mathlib's `pushforward₀OfCommRingCat.Monoidal` and our
`restrictScalarsLaxMonoidal`). Componentwise-identity isomorphic to `pushforward φ`. -/
noncomputable abbrev pushforwardFactored :
    PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) ⥤
      PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat) :=
  pushforward₀OfCommRingCat F R ⋙
    restrictScalars (R' := (F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat) φ

/-- The comparison of the pushforward with its factored spelling (componentwise the
identity). -/
noncomputable def pushforwardIsoFactored :
    pushforward.{u} φ ≅ pushforwardFactored φ :=
  NatIso.ofComponents (fun P => Iso.refl _) (fun f => by simp; rfl)

/-- The comparison with the factored pushforward is the identity natural
isomorphism after unfolding the definition of `pushforward`. -/
lemma pushforwardIsoFactored_eq_refl :
    pushforwardIsoFactored φ = Iso.refl (pushforward φ) := by
  ext P
  rfl

/-- **[D-PresPB′-general], leaf B1 (lax structure on the factored pushforward).** -/
@[implicit_reducible]
noncomputable def pushforwardFactoredLaxMonoidal : (pushforwardFactored φ).LaxMonoidal :=
  letI : (restrictScalars (R' := (F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat) φ).LaxMonoidal :=
    restrictScalarsLaxMonoidal (T₂ := F.op ⋙ R) φ
  inferInstanceAs ((pushforward₀OfCommRingCat F R ⋙
    restrictScalars (R' := (F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat) φ).LaxMonoidal)

private lemma pushforwardFactoredμ_expanded_app_tmul
    (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) (V : Cᵒᵖ)
    (x : ((pushforwardFactored φ).obj M).obj V)
    (y : ((pushforwardFactored φ).obj N).obj V) :
    letI := restrictScalarsLaxMonoidal (T₂ := F.op ⋙ R) φ
    letI := pushforwardFactoredLaxMonoidal φ
    (((restrictScalars φ).map
      (Functor.LaxMonoidal.μ (pushforward₀OfCommRingCat F R) M N)).app V)
        ((Functor.LaxMonoidal.μ (restrictScalars φ)
          ((pushforward₀OfCommRingCat F R).obj M)
          ((pushforward₀OfCommRingCat F R).obj N)).app V (x ⊗ₜ y)) =
      (x ⊗ₜ y : ((pushforwardFactored φ).obj (M ⊗ N)).obj V) :=
  rfl

/-- The comparison to the factored pushforward is the identity on elements. -/
lemma pushforwardIsoFactored_hom_app_app
    (P : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) (V : Cᵒᵖ)
    (x : ((pushforward.{u} φ).obj P).obj V) :
    ((pushforwardIsoFactored φ).hom.app P).app V x = x :=
  rfl

/-- The transported pullback–pushforward adjunction, against the factored spelling of the
pushforward (at which the lax monoidal structure lives natively). All doctrinal structure
maps of `pullbackOplaxMonoidal` are `homEquiv`-images under *this* adjunction. -/
noncomputable def pullbackPushforwardFactoredAdjunction
    [(pushforward.{u} φ).IsRightAdjoint] :
    pullback.{u} φ ⊣ pushforwardFactored φ :=
  (pullbackPushforwardAdjunction.{u} φ).ofNatIsoRight (pushforwardIsoFactored φ)

/-- Transporting the pullback--pushforward adjunction along the componentwise
identity factored comparison recovers the original adjunction. -/
lemma pullbackPushforwardFactoredAdjunction_eq
    [(pushforward.{u} φ).IsRightAdjoint] :
    pullbackPushforwardFactoredAdjunction φ =
      pullbackPushforwardAdjunction φ := by
  unfold pullbackPushforwardFactoredAdjunction
  rw [pushforwardIsoFactored_eq_refl]
  cases pullbackPushforwardAdjunction φ
  ext
  rfl

/-- The unit of the transported adjunction agrees elementwise with the unit of the
original pullback–pushforward adjunction (the comparison is componentwise the
identity). -/
lemma factoredAdjunction_unit_app_app [(pushforward.{u} φ).IsRightAdjoint]
    (P : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)) (V : Cᵒᵖ)
    (z : P.obj V) :
    ((((pullbackPushforwardAdjunction.{u} φ).ofNatIsoRight
        (pushforwardIsoFactored φ)).unit.app P).app V) z =
      (((pullbackPushforwardAdjunction.{u} φ).unit.app P).app V) z :=
  rfl

/-- **[D-PresPB′-general], leaves B1+B2 (data form).** The oplax monoidal structure on the
presheaf pullback along an arbitrary morphism of `CommRingCat`-derived ring presheaves:
doctrinal adjunction (`Adjunction.leftAdjointOplaxMonoidal`) applied to the transported
adjunction. Its `δ_{P,Q} : f^*ᵖ(P⊗Q) ⟶ f^*ᵖP ⊗ f^*ᵖQ` is the comparison map whose
invertibility is the remaining content (leaves G1/G3). -/
@[implicit_reducible]
noncomputable def pullbackOplaxMonoidal [(pushforward.{u} φ).IsRightAdjoint] :
    (pullback.{u} φ).OplaxMonoidal :=
  letI := pushforwardFactoredLaxMonoidal φ
  (pullbackPushforwardFactoredAdjunction φ).leftAdjointOplaxMonoidal

/-- The unit comparison of the factored pushforward is the ring comparison `φ` on
elements (the `pushforward₀` unit is the identity and the `restrictScalars` one is
`φ.app` itself). -/
lemma pushforwardFactored_ε_app_apply (V : Cᵒᵖ)
    (r : (𝟙_ (PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat))).obj V) :
    letI := pushforwardFactoredLaxMonoidal φ
    (Functor.LaxMonoidal.ε (pushforwardFactored φ)).app V r =
      ((φ.app V).hom r :
        ((pushforwardFactored φ).obj
          (𝟙_ (PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)))).obj V) :=
  rfl

/-- The tensorator of the factored pushforward is `x ⊗ₜ y ↦ x ⊗ₜ y` on elements (the
`pushforward₀` tensorator is the identity and the `restrictScalars` one is
`mapOfCompatibleSMul`). -/
lemma pushforwardFactored_μ_app_tmul
    (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) (V : Cᵒᵖ)
    (x : ((pushforwardFactored φ).obj M).obj V) (y : ((pushforwardFactored φ).obj N).obj V) :
    letI := pushforwardFactoredLaxMonoidal φ
    (Functor.LaxMonoidal.μ (pushforwardFactored φ) M N).app V (x ⊗ₜ y) =
      (x ⊗ₜ y : ((pushforwardFactored φ).obj (M ⊗ N)).obj V) :=
  rfl

/-- After applying the factored pushforward, the doctrinal pullback tensor comparison
sends the adjunction-unit image of a pure tensor to the pure tensor of the two
adjunction-unit images. -/
theorem pushforwardFactored_map_pullback_δ_unit_tmul
    [(pushforward.{u} φ).IsRightAdjoint]
    (P Q : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat))
    (V : Cᵒᵖ) (x : P.obj V) (y : Q.obj V) :
    let PB := pullback.{u} φ
    let PF := pushforwardFactored φ
    let adj := pullbackPushforwardFactoredAdjunction φ
    letI : PF.LaxMonoidal := pushforwardFactoredLaxMonoidal φ
    letI : PB.OplaxMonoidal := pullbackOplaxMonoidal φ
    ((PF.map (Functor.OplaxMonoidal.δ PB P Q)).app V)
        ((adj.unit.app (P ⊗ Q)).app V (x ⊗ₜ y)) =
      ((adj.unit.app P).app V x ⊗ₜ (adj.unit.app Q).app V y :
        (PF.obj (PB.obj P ⊗ PB.obj Q)).obj V) := by
  dsimp only
  let PB := pullback.{u} φ
  let PF := pushforwardFactored φ
  let adj := pullbackPushforwardFactoredAdjunction φ
  letI : PF.LaxMonoidal := pushforwardFactoredLaxMonoidal φ
  letI : PB.OplaxMonoidal := pullbackOplaxMonoidal φ
  letI : adj.IsMonoidal := inferInstance
  have h := adj.unit_app_tensor_comp_map_δ P Q
  have hV :
      (adj.unit.app (P ⊗ Q)).app V ≫
          ((PF.map (Functor.OplaxMonoidal.δ PB P Q)).app V) =
        ((adj.unit.app P ⊗ₘ adj.unit.app Q).app V) ≫
          ((Functor.LaxMonoidal.μ PF (PB.obj P) (PB.obj Q)).app V) := by
    simpa only [comp_app] using congrArg (fun a => a.app V) h
  have happ := congrArg (fun k => k (x ⊗ₜ y)) hV
  change
    ((PF.map (Functor.OplaxMonoidal.δ PB P Q)).app V)
        ((adj.unit.app (P ⊗ Q)).app V (x ⊗ₜ y)) =
      ((Functor.LaxMonoidal.μ PF (PB.obj P) (PB.obj Q)).app V)
        ((adj.unit.app P ⊗ₘ adj.unit.app Q).app V (x ⊗ₜ y)) at happ
  have htensor :
      (adj.unit.app P ⊗ₘ adj.unit.app Q).app V (x ⊗ₜ y) =
        ((adj.unit.app P).app V x ⊗ₜ (adj.unit.app Q).app V y :
          (PF.obj (PB.obj P) ⊗ PF.obj (PB.obj Q)).obj V) :=
    ModuleCat.MonoidalCategory.tensorHom_tmul
      ((adj.unit.app P).app V) ((adj.unit.app Q).app V) x y
  rw [htensor] at happ
  rw [pushforwardFactored_μ_app_tmul] at happ
  exact happ

/-- At an object mapped by the site functor, the doctrinal pullback tensor comparison
sends the adjunction-unit image of a pure tensor to the pure tensor of the two unit
images. -/
theorem pullback_δ_unit_tmul
    [(pushforward.{u} φ).IsRightAdjoint]
    (P Q : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat))
    (V : Cᵒᵖ) (x : P.obj V) (y : Q.obj V) :
    let PB := pullback.{u} φ
    let adj := pullbackPushforwardFactoredAdjunction φ
    letI : (pushforwardFactored φ).LaxMonoidal :=
      pushforwardFactoredLaxMonoidal φ
    letI : PB.OplaxMonoidal := pullbackOplaxMonoidal φ
    (Functor.OplaxMonoidal.δ PB P Q).app (F.op.obj V)
        (show (PB.obj (P ⊗ Q)).obj (F.op.obj V) from
          (adj.unit.app (P ⊗ Q)).app V (x ⊗ₜ y)) =
      ((show (PB.obj P).obj (F.op.obj V) from
          (adj.unit.app P).app V x) ⊗ₜ
        (show (PB.obj Q).obj (F.op.obj V) from
          (adj.unit.app Q).app V y) :
        (PB.obj P ⊗ PB.obj Q).obj (F.op.obj V)) := by
  dsimp only
  exact pushforwardFactored_map_pullback_δ_unit_tmul φ P Q V x y

/-- After module sheafification, the doctrinal presheaf-pullback tensor comparison
sends the sheafification-unit image of an adjunction-unit pure tensor to the
sheafification-unit image of the pure tensor of the two unit images. -/
theorem sheafification_map_pullback_δ_unit_tmul
    {K : GrothendieckTopology D}
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify K AddCommGrpCat.{u}]
    (hR : Presheaf.IsSheaf K (R ⋙ forget₂ CommRingCat RingCat))
    [(pushforward.{u} φ).IsRightAdjoint]
    (P Q : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat))
    (V : Cᵒᵖ) (x : P.obj V) (y : Q.obj V) :
    let PB := pullback.{u} φ
    let Rsh : Sheaf K RingCat.{u} := ⟨R ⋙ forget₂ CommRingCat RingCat, hR⟩
    let L := sheafification.{u} (R₀ := Rsh.obj) (𝟙 Rsh.obj)
    let adj := pullbackPushforwardFactoredAdjunction φ
    let shAdj := sheafificationAdjunction.{u} (R₀ := Rsh.obj) (𝟙 Rsh.obj)
    letI : (pushforwardFactored φ).LaxMonoidal :=
      pushforwardFactoredLaxMonoidal φ
    letI : PB.OplaxMonoidal := pullbackOplaxMonoidal φ
    ((L.map (Functor.OplaxMonoidal.δ PB P Q)).val.app (F.op.obj V))
        ((shAdj.unit.app (PB.obj (P ⊗ Q))).app (F.op.obj V)
          (show (PB.obj (P ⊗ Q)).obj (F.op.obj V) from
            (adj.unit.app (P ⊗ Q)).app V (x ⊗ₜ y))) =
      (shAdj.unit.app (PB.obj P ⊗ PB.obj Q)).app (F.op.obj V)
        ((show (PB.obj P).obj (F.op.obj V) from
            (adj.unit.app P).app V x) ⊗ₜ
          (show (PB.obj Q).obj (F.op.obj V) from
            (adj.unit.app Q).app V y)) := by
  dsimp only
  let PB := pullback.{u} φ
  let Rsh : Sheaf K RingCat.{u} := ⟨R ⋙ forget₂ CommRingCat RingCat, hR⟩
  let L := sheafification.{u} (R₀ := Rsh.obj) (𝟙 Rsh.obj)
  let adj := pullbackPushforwardFactoredAdjunction φ
  let shAdj := sheafificationAdjunction.{u} (R₀ := Rsh.obj) (𝟙 Rsh.obj)
  letI : (pushforwardFactored φ).LaxMonoidal :=
    pushforwardFactoredLaxMonoidal φ
  letI : PB.OplaxMonoidal := pullbackOplaxMonoidal φ
  have hδ := pullback_δ_unit_tmul φ P Q V x y
  dsimp only at hδ
  have hnat := shAdj.unit.naturality (Functor.OplaxMonoidal.δ PB P Q)
  have happ := congrArg
    (fun q => q.app (F.op.obj V)
      (show (PB.obj (P ⊗ Q)).obj (F.op.obj V) from
        (adj.unit.app (P ⊗ Q)).app V (x ⊗ₜ y))) hnat
  conv_lhs at happ => erw [comp_app, ModuleCat.comp_apply]
  conv_rhs at happ => erw [comp_app, ModuleCat.comp_apply]
  change
    (shAdj.unit.app (PB.obj P ⊗ PB.obj Q)).app (F.op.obj V)
        ((Functor.OplaxMonoidal.δ PB P Q).app (F.op.obj V)
          (show (PB.obj (P ⊗ Q)).obj (F.op.obj V) from
            (adj.unit.app (P ⊗ Q)).app V (x ⊗ₜ y))) =
      ((L.map (Functor.OplaxMonoidal.δ PB P Q)).val.app (F.op.obj V))
        ((shAdj.unit.app (PB.obj (P ⊗ Q))).app (F.op.obj V)
          (show (PB.obj (P ⊗ Q)).obj (F.op.obj V) from
            (adj.unit.app (P ⊗ Q)).app V (x ⊗ₜ y))) at happ
  exact happ.symm.trans (congrArg
    (fun z => (shAdj.unit.app (PB.obj P ⊗ PB.obj Q)).app (F.op.obj V) z) hδ)

/-- **[D-PresPB′-general], leaves B1+B2 (fused milestone).** The presheaf pullback along an
arbitrary ring comparison carries an oplax monoidal structure: transport the
pullback–pushforward adjunction to the factored spelling of the pushforward
(`Adjunction.ofNatIsoRight` along the componentwise-identity iso), where the lax structure
lives natively, and apply doctrinal adjunction (`Adjunction.leftAdjointOplaxMonoidal`).
Its `δ_{P,Q} : f^*ᵖ(P⊗Q) ⟶ f^*ᵖP ⊗ f^*ᵖQ` is the comparison map whose sheafified
invertibility is the remaining content (leaves G1/G3). -/
theorem nonempty_pullback_oplaxMonoidal [(pushforward.{u} φ).IsRightAdjoint] :
    Nonempty ((pullback.{u} φ).OplaxMonoidal) :=
  ⟨pullbackOplaxMonoidal φ⟩

end LaxPushforward

section FreeYonedaTensor

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- The meet equivalence of hom-types in a meet-semilattice category (all four types are
subsingletons). -/
def meetHomEquiv (U₁ U₂ V : X.Opens) :
    ((V ⟶ U₁) × (V ⟶ U₂)) ≃ (V ⟶ U₁ ⊓ U₂) where
  toFun p := homOfLE (le_inf (leOfHom p.1) (leOfHom p.2))
  invFun h := (homOfLE ((leOfHom h).trans inf_le_left),
    homOfLE ((leOfHom h).trans inf_le_right))
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- **[D-PresPB′-general], leaf G1 (meet half).** On the Opens-site, the pointwise product of
two representables is represented by the meet: `Hom(V,U₁) × Hom(V,U₂) ≅ Hom(V, U₁ ⊓ U₂)`. -/
noncomputable def yonedaMeetIso (U₁ U₂ : X.Opens) :
    (yoneda.obj U₁ ⊗ yoneda.obj U₂ : (X.Opens)ᵒᵖ ⥤ Type u) ≅ yoneda.obj (U₁ ⊓ U₂) :=
  NatIso.ofComponents
    (fun V => Equiv.toIso (meetHomEquiv U₁ U₂ V.unop))
    (fun {V W} f => by
      haveI : Subsingleton ((yoneda.obj (U₁ ⊓ U₂)).obj W) :=
        inferInstanceAs (Subsingleton (W.unop ⟶ U₁ ⊓ U₂))
      ext p
      exact Subsingleton.elim _ _)

section FreeTensorGeneric

variable {C : Type u₁} [Category.{v₁} C] (T : Cᵒᵖ ⥤ CommRingCat.{u})

/-- The pointwise component of the free–tensor comparison, hint-typed at the presheaf
carriers (`finsuppTensorFinsupp'`; both directions send generators to generators). -/
noncomputable def freeTensorμ (F G : Cᵒᵖ ⥤ Type u) (V : Cᵒᵖ) :
    (((free (T ⋙ forget₂ CommRingCat RingCat)).obj F ⊗
        (free (T ⋙ forget₂ CommRingCat RingCat)).obj G).obj V) ≅
      (((free (T ⋙ forget₂ CommRingCat RingCat)).obj (F ⊗ G)).obj V) :=
  LinearEquiv.toModuleIso
    (X₁ := ((free (T ⋙ forget₂ CommRingCat RingCat)).obj F ⊗
        (free (T ⋙ forget₂ CommRingCat RingCat)).obj G).obj V)
    (X₂ := ((free (T ⋙ forget₂ CommRingCat RingCat)).obj (F ⊗ G)).obj V)
    (finsuppTensorFinsupp' (↑((T ⋙ forget₂ CommRingCat RingCat).obj V)) (F.obj V) (G.obj V))

@[simp]
lemma freeTensorμ_hom_freeMk_tmul (F G : Cᵒᵖ ⥤ Type u) (V : Cᵒᵖ)
    (x : F.obj V) (y : G.obj V) :
    (freeTensorμ T F G V).hom (ModuleCat.freeMk x ⊗ₜ ModuleCat.freeMk y) =
      (ModuleCat.freeMk ((x, y) : (F ⊗ G).obj V) :
        ((free (T ⋙ forget₂ CommRingCat RingCat)).obj (F ⊗ G)).obj V) := by
  dsimp [freeTensorμ, ModuleCat.freeMk]
  erw [finsuppTensorFinsupp'_single_tmul_single]
  rw [mul_one]

@[simp]
lemma freeTensorμ_inv_freeMk (F G : Cᵒᵖ ⥤ Type u) (V : Cᵒᵖ) (z : (F ⊗ G).obj V) :
    (freeTensorμ T F G V).inv (ModuleCat.freeMk z) =
      (ModuleCat.freeMk z.1 ⊗ₜ ModuleCat.freeMk z.2 :
        (((free (T ⋙ forget₂ CommRingCat RingCat)).obj F ⊗
          (free (T ⋙ forget₂ CommRingCat RingCat)).obj G).obj V)) := by
  dsimp [freeTensorμ, ModuleCat.freeMk]
  erw [finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]
  rfl

/-- The free presheaf's restriction on generators: `freeMk x ↦ freeMk (F.map f x)`. -/
@[simp]
lemma freeObj_map_freeMk {H : Cᵒᵖ ⥤ Type u} {V W : Cᵒᵖ} (f : V ⟶ W) (x : H.obj V) :
    ((free (T ⋙ forget₂ CommRingCat RingCat)).obj H).map f (ModuleCat.freeMk x) =
      (ModuleCat.freeMk (H.map f x) :
        ((free (T ⋙ forget₂ CommRingCat RingCat)).obj H).obj W) := by
  erw [ModuleCat.freeDesc_apply]
  rfl

/-- Elementwise form of the tensor product of morphisms of presheaves of modules. -/
lemma tensorHom_app_tmul {M₁ M₂ M₃ M₄ :
      PresheafOfModules.{u} (T ⋙ forget₂ CommRingCat RingCat)}
    (g₁ : M₁ ⟶ M₂) (g₂ : M₃ ⟶ M₄) (V : Cᵒᵖ) (x : M₁.obj V) (y : M₃.obj V) :
    (g₁ ⊗ₘ g₂).app V (x ⊗ₜ y) = (g₁.app V x ⊗ₜ g₂.app V y : (M₂ ⊗ M₄).obj V) :=
  ModuleCat.MonoidalCategory.tensorHom_tmul (g₁.app V) (g₂.app V) x y

/-- The free presheaf functor on morphisms, on generators:
`(free R).map g` sends `freeMk x` to `freeMk (g.app x)`. -/
@[simp]
lemma free_map_app_freeMk {F G : Cᵒᵖ ⥤ Type u} (g : F ⟶ G) (V : Cᵒᵖ) (x : F.obj V) :
    (((free (T ⋙ forget₂ CommRingCat RingCat)).map g).app V) (ModuleCat.freeMk x) =
      (ModuleCat.freeMk (g.app V x) :
        ((free (T ⋙ forget₂ CommRingCat RingCat)).obj G).obj V) := by
  erw [ModuleCat.free_map_apply]

/-- `ModuleCat.free_hom_ext`, restated at the presheaf-of-modules clothing of the free
objects (the mathlib form's `(ModuleCat.free R).obj`-spelling reframes goals and poisons
`kabstract`; the defeq crossing happens once, here, at elaboration). -/
lemma clothedFree_hom_ext {H : Cᵒᵖ ⥤ Type u} {V : Cᵒᵖ}
    {M : ModuleCat ↑((T ⋙ forget₂ CommRingCat RingCat).obj V)}
    {f g : ((free (T ⋙ forget₂ CommRingCat RingCat)).obj H).obj V ⟶ M}
    (h : ∀ x : H.obj V, f (ModuleCat.freeMk x) = g (ModuleCat.freeMk x)) : f = g :=
  ModuleCat.free_hom_ext h

/-- The types-level pairing `(x, y) ↦ freeMk x ⊗ₜ freeMk y`, the adjunct of the free–tensor
comparison. Naturality is an elementwise Types-square. -/
noncomputable def freeTensorPair (F G : Cᵒᵖ ⥤ Type u) :
    (F ⊗ G) ⟶
      ((free (T ⋙ forget₂ CommRingCat RingCat)).obj F ⊗
        (free (T ⋙ forget₂ CommRingCat RingCat)).obj G).presheaf ⋙ forget _ where
  app V := ↾fun z =>
    ((ModuleCat.freeMk z.1 ⊗ₜ ModuleCat.freeMk z.2 :
      (((free (T ⋙ forget₂ CommRingCat RingCat)).obj F ⊗
        (free (T ⋙ forget₂ CommRingCat RingCat)).obj G).obj V)))
  naturality {V W} f := by
    ext z
    change (ModuleCat.freeMk (((F ⊗ G).map f) z).1 ⊗ₜ
        ModuleCat.freeMk (((F ⊗ G).map f) z).2 :
        (((free (T ⋙ forget₂ CommRingCat RingCat)).obj F ⊗
          (free (T ⋙ forget₂ CommRingCat RingCat)).obj G).obj W)) =
      (((free (T ⋙ forget₂ CommRingCat RingCat)).obj F ⊗
        (free (T ⋙ forget₂ CommRingCat RingCat)).obj G).map f)
        (ModuleCat.freeMk z.1 ⊗ₜ ModuleCat.freeMk z.2)
    erw [Monoidal.tensorObj_map_tmul]
    rw [freeObj_map_freeMk T f z.1, freeObj_map_freeMk T f z.2]
    erw [CategoryTheory.tensor_apply]
    rfl

/-- The free–tensor comparison out of the free presheaf, by the universal property
(naturality supplied by `freeObjDesc`). -/
noncomputable def freeTensorDesc (F G : Cᵒᵖ ⥤ Type u) :
    (free (T ⋙ forget₂ CommRingCat RingCat)).obj (F ⊗ G) ⟶
      ((free (T ⋙ forget₂ CommRingCat RingCat)).obj F ⊗
        (free (T ⋙ forget₂ CommRingCat RingCat)).obj G) :=
  freeObjDesc (freeTensorPair T F G)

/-- The free–tensor comparison agrees componentwise with the pointwise
`finsuppTensorFinsupp'` isomorphism (both send generators to generators). -/
lemma freeTensorDesc_app (F G : Cᵒᵖ ⥤ Type u) (V : Cᵒᵖ) :
    (freeTensorDesc T F G).app V = (freeTensorμ T F G V).inv := by
  refine clothedFree_hom_ext T (fun z => ?_)
  rw [freeTensorμ_inv_freeMk T F G V z]
  simp only [freeTensorDesc, freeObjDesc_app, freeTensorPair]
  erw [ModuleCat.freeDesc_apply]
  rfl

instance (F G : Cᵒᵖ ⥤ Type u) : IsIso (freeTensorDesc T F G) := by
  haveI : ∀ V : Cᵒᵖ, IsIso ((freeTensorDesc T F G).app V) := fun V => by
    rw [freeTensorDesc_app T F G V]; infer_instance
  haveI : IsIso ((toPresheaf _).map (freeTensorDesc T F G)) := by
    haveI : ∀ V : Cᵒᵖ, IsIso (((toPresheaf _).map (freeTensorDesc T F G)).app V) := fun V =>
      inferInstanceAs (IsIso ((forget₂ _ AddCommGrpCat).map ((freeTensorDesc T F G).app V)))
    exact NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso _ (toPresheaf (T ⋙ forget₂ CommRingCat RingCat))

/-- **[D-PresPB′-general], leaf G1-NAT (data form).** The free presheaf of modules functor
is monoidal on tensor products: `free(F ⊗ G) ≅ free(F) ⊗ free(G)`, with hom sending the
generator `freeMk (x, y)` to `freeMk x ⊗ₜ freeMk y` (see `freeTensorDesc_app` /
`freeTensorμ_inv_freeMk`). -/
noncomputable def freeTensorIso (F G : Cᵒᵖ ⥤ Type u) :
    ((free (T ⋙ forget₂ CommRingCat RingCat)).obj (F ⊗ G) :
        PresheafOfModules.{u} (T ⋙ forget₂ CommRingCat RingCat)) ≅
      (free (T ⋙ forget₂ CommRingCat RingCat)).obj F ⊗
        (free (T ⋙ forget₂ CommRingCat RingCat)).obj G :=
  asIso (freeTensorDesc T F G)

/-- **[D-PresPB′-general], leaf G1-NAT (closed via the adjunction route).** The pointwise
components `freeTensorμ` assemble: `free(F) ⊗ free(G) ≅ free(F ⊗ G)`. The comparison is
`freeTensorDesc` (naturality from the universal property); each component agrees with
`(freeTensorμ).inv` on generators, hence is an isomorphism; isomorphy reflects along
`toPresheaf`. -/
theorem nonempty_freeTensorIsoGeneric (F G : Cᵒᵖ ⥤ Type u) :
    Nonempty
      (((free (T ⋙ forget₂ CommRingCat RingCat)).obj F ⊗
          (free (T ⋙ forget₂ CommRingCat RingCat)).obj G :
        PresheafOfModules.{u} (T ⋙ forget₂ CommRingCat RingCat)) ≅
        (free (T ⋙ forget₂ CommRingCat RingCat)).obj (F ⊗ G)) :=
  ⟨(freeTensorIso T F G).symm⟩

end FreeTensorGeneric

/-- **[D-PresPB′-general], leaf G1 (the lattice miracle).** On the Opens-site of a scheme, the
presheaf tensor of two free-yoneda presheaves of modules is the free-yoneda of the meet:
pointwise, `Hom(V,U₁) × Hom(V,U₂) = [V ≤ U₁ ⊓ U₂]` (a meet-semilattice has representable
products of representables), and the free-module functor sends products of types to tensor
products of free modules (`finsuppTensorFinsupp`-style). Together with mathlib's
`freeFunctorCompPullbackIso` this makes the oplax comparison `δ` an isomorphism on free-yoneda
pairs — before sheafifying. -/
noncomputable def freeYonedaTensorIso (U₁ U₂ : X.Opens) :
    ((free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₁) ⊗
        (free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₂) :
          PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) ≅
      (free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj (U₁ ⊓ U₂)) :=
  (freeTensorIso X.sheaf.obj (yoneda.obj U₁) (yoneda.obj U₂)).symm ≪≫
    (free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).mapIso (yonedaMeetIso U₁ U₂)

/-- The types-level collapse of the terminal representable: every section maps to `1`.
The adjunct of the unit–free-yoneda comparison. -/
noncomputable def unitDescPair :
    (yoneda.obj (⊤ : X.Opens) : (X.Opens)ᵒᵖ ⥤ Type u) ⟶
      (𝟙_ (PresheafOfModules.{u}
        (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat))).presheaf ⋙ forget _ where
  app V := ↾fun _ =>
    (1 : ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj V))
  naturality {V W} i := by
    ext h
    change (1 : ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj W)) =
      (unit (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).map i
        (1 : ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj V))
    exact (unit_map_one _ i).symm

/-- The unit–free-yoneda comparison on the terminal open, by the universal property. -/
noncomputable def unitDesc :
    ((free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj (⊤ : X.Opens)) :
      PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) ⟶
      𝟙_ (PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) :=
  freeObjDesc (unitDescPair (X := X))

@[simp]
lemma unitDesc_app_freeMk {V : (X.Opens)ᵒᵖ} (h : V.unop ⟶ (⊤ : X.Opens)) :
    (unitDesc (X := X)).app V (ModuleCat.freeMk h) =
      (1 : ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj V)) := by
  simp only [unitDesc, freeObjDesc_app]
  erw [ModuleCat.freeDesc_apply]
  rfl

instance : IsIso (unitDesc (X := X)) := by
  haveI : ∀ V : (X.Opens)ᵒᵖ, IsIso ((unitDesc (X := X)).app V) := by
    intro V
    haveI : Unique (V.unop ⟶ (⊤ : X.Opens)) :=
      { default := homOfLE le_top, uniq := fun _ => Subsingleton.elim _ _ }
    have happ : (unitDesc (X := X)).app V = (LinearEquiv.toModuleIso
        (X₁ := ((free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj
          (yoneda.obj (⊤ : X.Opens))).obj V)
        (X₂ := (𝟙_ (PresheafOfModules.{u}
          (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat))).obj V)
        (Finsupp.uniqueLinearEquiv
          (↑((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj V))
          (↑((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj V))
          (homOfLE le_top))).hom := by
      refine clothedFree_hom_ext X.sheaf.obj (fun h => ?_)
      rw [unitDesc_app_freeMk]
      change _ = Finsupp.uniqueLinearEquiv
        (↑((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj V))
        (↑((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj V))
        (homOfLE le_top) (ModuleCat.freeMk h)
      change (1 : (↑((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj V))) =
        Finsupp.uniqueLinearEquiv
          (↑((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj V))
          (↑((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj V))
          (homOfLE le_top) (Finsupp.single h 1)
      rw [Finsupp.uniqueLinearEquiv_apply]
      change (1 : (↑((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj V))) =
        Finsupp.single h
          (1 : (↑((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj V)))
          (homOfLE le_top)
      rw [show (homOfLE le_top : V.unop ⟶ (⊤ : X.Opens)) = h from Subsingleton.elim _ _]
      exact (Finsupp.single_eq_same).symm
    rw [happ]
    exact Iso.isIso_hom _
  haveI : IsIso ((toPresheaf _).map (unitDesc (X := X))) := by
    haveI : ∀ V : (X.Opens)ᵒᵖ, IsIso (((toPresheaf _).map (unitDesc (X := X))).app V) :=
      fun V => inferInstanceAs
        (IsIso ((forget₂ _ AddCommGrpCat).map ((unitDesc (X := X)).app V)))
    exact NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso _ (toPresheaf (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat))

/-- **The monoidal unit is the free-yoneda module on the terminal open**: sections of the
structure presheaf are the free rank-1 module on `Hom(V, ⊤) = {*}`. -/
noncomputable def unitFreeYonedaIso :
    ((free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj (⊤ : X.Opens)) :
      PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) ≅
      𝟙_ (PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) :=
  asIso (unitDesc (X := X))

/-- **[D-PresPB′-general], leaf G1 (the lattice miracle, existence form).** -/
theorem nonempty_freeYoneda_tensor_iso' (U₁ U₂ : X.Opens) :
    Nonempty (((free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₁) ⊗
        (free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₂) :
          PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) ≅
      (free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj (U₁ ⊓ U₂))) :=
  ⟨freeYonedaTensorIso U₁ U₂⟩

/-- **[D-PresPB′-general], leaf G1 (the lattice miracle).** On the Opens-site of a scheme, the
presheaf tensor of two free-yoneda presheaves of modules is the free-yoneda of the meet:
pointwise, `Hom(V,U₁) × Hom(V,U₂) = [V ≤ U₁ ⊓ U₂]` (a meet-semilattice has representable
products of representables), and the free-module functor sends products of types to tensor
products of free modules (`finsuppTensorFinsupp`-style). Together with mathlib's
`freeFunctorCompPullbackIso` this makes the oplax comparison `δ` an isomorphism on free-yoneda
pairs — before sheafifying. -/
theorem nonempty_freeYoneda_tensor_iso (U₁ U₂ : X.Opens) :
    Nonempty (((free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₁) ⊗
        (free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₂) :
          PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) ≅
      (free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj (U₁ ⊓ U₂))) :=
  nonempty_freeYoneda_tensor_iso' U₁ U₂

end FreeYonedaTensor

section IsoAtColimit

open CategoryTheory.Limits

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]

/-- **[D-PresPB′-general], leaf G3-EXT.** A natural transformation that is an isomorphism
on the objects of a diagram is an isomorphism at any colimit point of the diagram, provided
both functors preserve the colimit: the component at the point is the induced comparison of
colimits of isomorphic diagrams. -/
lemma isIso_app_of_isColimit {F G : C₁ ⥤ C₂} (α : F ⟶ G) {J : Type u₃} [Category.{v₃} J]
    {K : J ⥤ C₁} {c : Cocone K}
    (h₁ : IsColimit (F.mapCocone c)) (h₂ : IsColimit (G.mapCocone c))
    [∀ j, IsIso (α.app (K.obj j))] : IsIso (α.app c.pt) := by
  let e : K ⋙ F ≅ K ⋙ G :=
    NatIso.ofComponents (fun j => asIso (α.app (K.obj j)))
      (fun {j j'} g => α.naturality (K.map g))
  let eColim := IsColimit.coconePointsIsoOfNatIso h₁ h₂ e
  have key : α.app c.pt = eColim.hom := by
    refine h₁.hom_ext (fun j => ?_)
    change F.map (c.ι.app j) ≫ α.app c.pt =
      F.map (c.ι.app j) ≫ eColim.hom
    exact (α.naturality (c.ι.app j)).trans
      (IsColimit.comp_coconePointsIsoOfNatIso_hom h₁ h₂ e j).symm
  rw [key]
  exact eColim.isIso_hom

end IsoAtColimit

section TensorColimits

open CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {T : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- **[D-PresPB′-general], leaf G3-TC (right half).** Tensoring with a fixed presheaf of
modules preserves colimits (pointwise: evaluation jointly reflects, evaluation preserves,
and `ModuleCat` tensoring is a left adjoint by monoidal-closedness). -/
lemma preservesColimitsOfShape_tensorRight
    (Q : PresheafOfModules.{u} (T ⋙ forget₂ CommRingCat RingCat))
    (J : Type w) [Category.{w'} J] [HasColimitsOfShape J AddCommGrpCat.{u}] :
    PreservesColimitsOfShape J (MonoidalCategory.tensorRight Q) where
  preservesColimit {K} := {
    preserves {c} hc := by
      refine ⟨evaluationJointlyReflectsColimits _ _ (fun V => ?_)⟩
      have h1 : IsColimit ((evaluation
          (T ⋙ forget₂ CommRingCat RingCat) V).mapCocone c) :=
        isColimitOfPreserves _ hc
      have h2 := isColimitOfPreserves (MonoidalCategory.tensorRight (Q.obj V)) h1
      exact h2.ofIsoColimit (Cocone.ext (Iso.refl _) (fun j => by
        change _ ≫ 𝟙 _ = _
        rw [Category.comp_id]
        rfl)) }

/-- **[D-PresPB′-general], leaf G3-TC (left half).** Symmetric to the right half, by the
braiding. -/
lemma preservesColimitsOfShape_tensorLeft
    (Q : PresheafOfModules.{u} (T ⋙ forget₂ CommRingCat RingCat))
    (J : Type w) [Category.{w'} J] [HasColimitsOfShape J AddCommGrpCat.{u}] :
    PreservesColimitsOfShape J (MonoidalCategory.tensorLeft Q) :=
  letI := preservesColimitsOfShape_tensorRight Q J
  preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight Q).symm

/-- Size-`u` packaging of `preservesColimitsOfShape_tensorRight`. -/
lemma preservesColimitsOfSize_tensorRight_aux
    (Q : PresheafOfModules.{u} (T ⋙ forget₂ CommRingCat RingCat)) :
    PreservesColimitsOfSize.{u, u} (MonoidalCategory.tensorRight Q) :=
  ⟨fun {J} _ => preservesColimitsOfShape_tensorRight Q J⟩

/-- Size-`u` packaging of `preservesColimitsOfShape_tensorLeft`. -/
lemma preservesColimitsOfSize_tensorLeft_aux
    (Q : PresheafOfModules.{u} (T ⋙ forget₂ CommRingCat RingCat)) :
    PreservesColimitsOfSize.{u, u} (MonoidalCategory.tensorLeft Q) :=
  ⟨fun {J} _ => preservesColimitsOfShape_tensorLeft Q J⟩

end TensorColimits

section PullbackFreeYoneda

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)

/-- **[D-PresPB′-general], corepresentability workhorse.** The presheaf pullback of a
free-yoneda module is the free-yoneda module of the image object: both corepresent the
functor `M ↦ ((push M).obj X ≃ M.obj (F X))`, by the adjunction and by mathlib's
`pushforwardCompCoyonedaFreeYonedaCorepresentableBy` respectively. -/
noncomputable def pullbackFreeYonedaIso (X : C) :
    (pullback.{u} φ).obj ((free S).obj (yoneda.obj X)) ≅
      (free R).obj (yoneda.obj (F.obj X)) where
  hom := ((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _).symm
    ((pushforwardCompCoyonedaFreeYonedaCorepresentableBy φ X).homEquiv (𝟙 _))
  inv := (pushforwardCompCoyonedaFreeYonedaCorepresentableBy φ X).homEquiv.symm
    ((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _ (𝟙 _))
  hom_inv_id := ((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _).injective (by
    rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
    change ((pushforward φ ⋙ coyoneda.obj (Opposite.op ((free S).obj (yoneda.obj X)))).map
      ((pushforwardCompCoyonedaFreeYonedaCorepresentableBy φ X).homEquiv.symm
        ((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _ (𝟙 _)))
      ((pushforwardCompCoyonedaFreeYonedaCorepresentableBy φ X).homEquiv (𝟙 _))) = _
    rw [← Functor.CorepresentableBy.homEquiv_eq, Equiv.apply_symm_apply])
  inv_hom_id := (pushforwardCompCoyonedaFreeYonedaCorepresentableBy φ X).homEquiv.injective (by
    rw [Functor.CorepresentableBy.homEquiv_comp, Equiv.apply_symm_apply]
    change (pullbackPushforwardAdjunction.{u} φ).homEquiv _ _ (𝟙 _) ≫
      (pushforward φ).map (((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _).symm
        ((pushforwardCompCoyonedaFreeYonedaCorepresentableBy φ X).homEquiv (𝟙 _))) = _
    rw [← Adjunction.homEquiv_naturality_right, Category.id_comp, Equiv.apply_symm_apply])

/-- Characterization of `pullbackFreeYonedaIso`: postcomposition with a map `g` out of the
corepresenting free-yoneda corresponds, under the adjunction, to the generator image of
`g` viewed in the pushforward. This is the compute rule for the [G3-pre] δ-chase. -/
lemma homEquiv_pullbackFreeYonedaIso_hom_comp {X : C} {N : PresheafOfModules.{u} R}
    (g : (free R).obj (yoneda.obj (F.obj X)) ⟶ N) :
    (pullbackPushforwardAdjunction.{u} φ).homEquiv _ _
        ((pullbackFreeYonedaIso φ X).hom ≫ g) =
      (pushforwardCompCoyonedaFreeYonedaCorepresentableBy φ X).homEquiv g := by
  rw [Adjunction.homEquiv_naturality_right]
  change ((pushforward φ ⋙ coyoneda.obj (Opposite.op ((free S).obj (yoneda.obj X)))).map g
    ((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _ (pullbackFreeYonedaIso φ X).hom)) = _
  rw [show (pullbackPushforwardAdjunction.{u} φ).homEquiv _ _ (pullbackFreeYonedaIso φ X).hom =
      (pushforwardCompCoyonedaFreeYonedaCorepresentableBy φ X).homEquiv (𝟙 _) from
    Equiv.apply_symm_apply _ _]
  rw [← Functor.CorepresentableBy.homEquiv_eq]

/-- Evaluation form of `freeYonedaEquiv`: the value of a map out of a free-yoneda module is
its value on the generator `freeMk (𝟙 X)`. -/
lemma freeYonedaEquiv_apply {M : PresheafOfModules.{u} S} {X : C}
    (g : (free S).obj (yoneda.obj X) ⟶ M) :
    freeYonedaEquiv g = g.app (Opposite.op X) (ModuleCat.freeMk (𝟙 X)) := by
  obtain ⟨x, rfl⟩ := freeYonedaEquiv.symm.surjective g
  rw [Equiv.apply_symm_apply, freeYonedaEquiv_symm_app]

/-- Generator evaluation of the corepresentability equivalence: the transposed morphism,
evaluated on the upstairs generator, is the generator image of the original morphism. -/
lemma corepresentableBy_homEquiv_app_generator {X : C} {N : PresheafOfModules.{u} R}
    (g : (free R).obj (yoneda.obj (F.obj X)) ⟶ N) :
    (((pushforwardCompCoyonedaFreeYonedaCorepresentableBy φ X).homEquiv g :
        (free S).obj (yoneda.obj X) ⟶ (pushforward.{u} φ).obj N)).app
        (Opposite.op X) (ModuleCat.freeMk (𝟙 X)) =
      (freeYonedaEquiv g : N.obj (Opposite.op (F.obj X))) := by
  rw [← freeYonedaEquiv_apply]
  exact Equiv.apply_symm_apply _ _

/-- The adjunction unit at a free-yoneda module, through the corepresentability of the
pullback: the `homEquiv`-transposed inverse of `pullbackFreeYonedaIso`. This is the compute
rule for units in the [G3-pre]/[G3-η] generator chases. -/
lemma unit_app_freeYoneda (X : C) :
    (pullbackPushforwardAdjunction.{u} φ).unit.app ((free S).obj (yoneda.obj X)) =
      (pushforwardCompCoyonedaFreeYonedaCorepresentableBy φ X).homEquiv
        ((pullbackFreeYonedaIso φ X).inv) := by
  rw [← Adjunction.homEquiv_id, ← Iso.hom_inv_id (pullbackFreeYonedaIso φ X),
    homEquiv_pullbackFreeYonedaIso_hom_comp]

/-- The free presheaf's restriction on generators, over an arbitrary `RingCat`-valued
ring presheaf. -/
lemma freeObj_map_freeMk' {R' : Cᵒᵖ ⥤ RingCat.{u}} {H : Cᵒᵖ ⥤ Type u} {V W : Cᵒᵖ}
    (i : V ⟶ W) (x : H.obj V) :
    ((free R').obj H).map i (ModuleCat.freeMk x) =
      (ModuleCat.freeMk (H.map i x) : ((free R').obj H).obj W) := by
  erw [ModuleCat.freeDesc_apply]
  rfl

/-- Evaluation of a morphism out of a free-yoneda module on an arbitrary generator
`freeMk h`: the restriction of its generator image along `h`. The one compute rule for
both sides of the [G3-pre] δ-chase. -/
lemma app_freeMk {R' : Cᵒᵖ ⥤ RingCat.{u}} {U : C} {N : PresheafOfModules.{u} R'}
    (g : (free R').obj (yoneda.obj U) ⟶ N) {W : C} (h : W ⟶ U) :
    g.app (Opposite.op W) (ModuleCat.freeMk h) =
      N.map h.op (freeYonedaEquiv g) := by
  let idU : (yoneda.obj U).obj (Opposite.op U) := 𝟙 U
  let genU : ((free R').obj (yoneda.obj U)).obj (Opposite.op U) :=
    ModuleCat.freeMk idU
  have hh : (ModuleCat.freeMk h : ((free R').obj (yoneda.obj U)).obj (Opposite.op W)) =
      ((free R').obj (yoneda.obj U)).map h.op genU := by
    rw [freeObj_map_freeMk']
    change ModuleCat.freeMk h = ModuleCat.freeMk ((yoneda.obj U).map h.op idU)
    exact congrArg ModuleCat.freeMk (by simp [idU])
  rw [hh, naturality_apply]
  congr 1

/-- The generator image of the adjunction unit at a free-yoneda module is the generator
image of the corepresentability comparison. -/
lemma freeYonedaEquiv_unit_app (X : C) :
    freeYonedaEquiv ((pullbackPushforwardAdjunction.{u} φ).unit.app
        ((free S).obj (yoneda.obj X))) =
      freeYonedaEquiv ((pullbackFreeYonedaIso φ X).inv) := by
  rw [unit_app_freeYoneda, freeYonedaEquiv_apply]
  exact corepresentableBy_homEquiv_app_generator φ ((pullbackFreeYonedaIso φ X).inv)

end PullbackFreeYoneda

section PullbackFreeYonedaMonoidal

open CategoryTheory.Limits

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}}
  (φ : S ⋙ forget₂ CommRingCat RingCat ⟶
    F.op ⋙ (R ⋙ forget₂ CommRingCat RingCat))

/-- Full evaluation of the transported adjunction unit at a free-yoneda module on an
arbitrary generator: the restriction along `h` of the corepresentability comparison's
generator image. -/
lemma factoredUnit_app_freeMk (U : C) {W : C} (h : W ⟶ U) :
    ((((pullbackPushforwardAdjunction.{u} φ).ofNatIsoRight
        (pushforwardIsoFactored φ)).unit.app
          ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U))).app
          (Opposite.op W)) (ModuleCat.freeMk h) =
      ((pushforwardFactored φ).obj ((pullback.{u} φ).obj
          ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U)))).map h.op
        (freeYonedaEquiv (X := F.obj U)
          (M := (pullback.{u} φ).obj
            ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U)))
          ((pullbackFreeYonedaIso φ U).inv)) := by
  let η := ((pullbackPushforwardAdjunction.{u} φ).ofNatIsoRight
    (pushforwardIsoFactored φ)).unit.app
      ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U))
  have hgen : freeYonedaEquiv η =
      freeYonedaEquiv ((pullbackFreeYonedaIso φ U).inv) := by
    rw [freeYonedaEquiv_apply, freeYonedaEquiv_apply]
    have hη := factoredAdjunction_unit_app_app φ
      ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U))
      (Opposite.op U) (ModuleCat.freeMk (𝟙 U))
    have hfree := freeYonedaEquiv_unit_app φ U
    rw [freeYonedaEquiv_apply, freeYonedaEquiv_apply] at hfree
    exact hη.trans hfree
  exact (app_freeMk η h).trans (congrArg _ hgen)

/-- The reusable presentation-extension core: a natural transformation out of the category
of presheaves of modules over a small site that is invertible on free-yoneda modules is
invertible everywhere, provided both functors preserve colimits (coproduct layer over the
elements, then the cokernel-cofork layer of the canonical presentation). -/
lemma isIso_app_of_isIso_app_freeYoneda {E : Type u₃} [Category.{v₃} E]
    {F₁ F₂ : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat) ⥤ E} (α : F₁ ⟶ F₂)
    [PreservesColimitsOfSize.{u, u} F₁] [PreservesColimitsOfSize.{u, u} F₂]
    [PreservesColimitsOfShape WalkingParallelPair F₁]
    [PreservesColimitsOfShape WalkingParallelPair F₂]
    (hfree : ∀ X : C, IsIso (α.app
      ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj X))))
    (M : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)) :
    IsIso (α.app M) := by
  have h₀ : ∀ (N : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)),
      IsIso (α.app N.freeYonedaCoproduct) := by
    intro N
    haveI : ∀ j, IsIso (α.app ((Discrete.functor
        (Elements.freeYoneda (M := N))).obj j)) := fun j => hfree _
    exact isIso_app_of_isColimit α
      (isColimitOfPreserves F₁ (colimit.isColimit _))
      (isColimitOfPreserves F₂ (colimit.isColimit _))
  haveI : ∀ j, IsIso (α.app ((parallelPair M.toFreeYonedaCoproduct 0).obj j)) := by
    rintro (_ | _) <;> exact h₀ _
  exact isIso_app_of_isColimit α
    (isColimitOfPreserves F₁ M.isColimitFreeYonedaCoproductsCokernelCofork)
    (isColimitOfPreserves F₂ M.isColimitFreeYonedaCoproductsCokernelCofork)

/-- The doctrinal tensor comparison in the first variable, as a natural transformation. -/
noncomputable def δRightNat [(pushforward.{u} φ).IsRightAdjoint]
    (Q : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)) :
    (MonoidalCategory.tensorRight Q ⋙ pullback.{u} φ) ⟶
      pullback.{u} φ ⋙ MonoidalCategory.tensorRight ((pullback.{u} φ).obj Q) :=
  letI := pullbackOplaxMonoidal φ
  { app := fun P => Functor.OplaxMonoidal.δ (pullback.{u} φ) P Q
    naturality := fun {_P _P'} g =>
      (Functor.OplaxMonoidal.δ_natural_left (pullback.{u} φ) g Q).symm }

/-- The doctrinal tensor comparison in the second variable, as a natural transformation. -/
noncomputable def δLeftNat [(pushforward.{u} φ).IsRightAdjoint]
    (P : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)) :
    (MonoidalCategory.tensorLeft P ⋙ pullback.{u} φ) ⟶
      pullback.{u} φ ⋙ MonoidalCategory.tensorLeft ((pullback.{u} φ).obj P) :=
  letI := pullbackOplaxMonoidal φ
  { app := fun Q => Functor.OplaxMonoidal.δ (pullback.{u} φ) P Q
    naturality := fun {_Q _Q'} g =>
      (Functor.OplaxMonoidal.δ_natural_right (pullback.{u} φ) P g).symm }

/-- **[D-PresPB′-general], leaf G3 (generic extension).** If the doctrinal tensor
comparison of the presheaf pullback is invertible on free-yoneda pairs, it is invertible
on all pairs: extend along the canonical free-yoneda presentation in each variable in
turn, using that both sides are compositions of colimit-preserving functors
(`pullback` is a left adjoint; tensoring preserves colimits pointwise). -/
theorem isIso_pullback_δ_of_freeYoneda [(pushforward.{u} φ).IsRightAdjoint]
    (hbase : ∀ X₁ X₂ : C,
      letI := pullbackOplaxMonoidal φ
      IsIso (Functor.OplaxMonoidal.δ (pullback.{u} φ)
        ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj X₁))
        ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj X₂))))
    (P Q : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)) :
    letI := pullbackOplaxMonoidal φ
    IsIso (Functor.OplaxMonoidal.δ (pullback.{u} φ) P Q) := by
  letI := pullbackOplaxMonoidal φ
  haveI hpb : PreservesColimitsOfSize.{u, u} (pullback.{u} φ) :=
    (pullbackPushforwardAdjunction.{u} φ).leftAdjoint_preservesColimits
  haveI hpb0 : PreservesColimitsOfShape WalkingParallelPair (pullback.{u} φ) :=
    ((pullbackPushforwardAdjunction.{u} φ).leftAdjoint_preservesColimits :
      PreservesColimitsOfSize.{0, 0} (pullback.{u} φ)).preservesColimitsOfShape
  have pass1 : ∀ (P' : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)) (X₂ : C),
      IsIso (Functor.OplaxMonoidal.δ (pullback.{u} φ) P'
        ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj X₂))) := by
    intro P' X₂
    haveI := preservesColimitsOfSize_tensorRight_aux
      ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj X₂))
    haveI := preservesColimitsOfSize_tensorRight_aux
      ((pullback.{u} φ).obj ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj X₂)))
    haveI := preservesColimitsOfShape_tensorRight
      ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj X₂))
      WalkingParallelPair
    haveI := preservesColimitsOfShape_tensorRight
      ((pullback.{u} φ).obj ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj X₂)))
      WalkingParallelPair
    exact isIso_app_of_isIso_app_freeYoneda (δRightNat φ
      ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj X₂)))
      (fun X₁ => hbase X₁ X₂) P'
  haveI := preservesColimitsOfSize_tensorLeft_aux P
  haveI := preservesColimitsOfSize_tensorLeft_aux ((pullback.{u} φ).obj P)
  haveI := preservesColimitsOfShape_tensorLeft P WalkingParallelPair
  haveI := preservesColimitsOfShape_tensorLeft ((pullback.{u} φ).obj P)
    WalkingParallelPair
  exact isIso_app_of_isIso_app_freeYoneda (δLeftNat φ P) (fun X₂ => pass1 P X₂) Q

end PullbackFreeYonedaMonoidal

section SchemePullbackMonoidal

open AlgebraicGeometry TopologicalSpace

variable {X Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X)

/-- The comparison morphism of `RingCat`-valued structure presheaves induced by a scheme
morphism `f : Y ⟶ X`, spelled at the `CommRingCat`-derived clothing
`X.sheaf.obj ⋙ forget₂ CommRingCat RingCat ⟶ (Opens.map f.base).op ⋙ (Y.sheaf.obj ⋙ …)`
at which the presheaf-of-modules monoidal structures are found by instance search on both
sides of the pullback. -/
noncomputable def schemeRingPresheafHom :
    (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat :
        (Opens ↥X)ᵒᵖ ⥤ RingCat.{u}) ⟶
      (Opens.map f.base).op ⋙ (Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat) :=
  Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)

/-- Generator evaluation of the lattice-miracle isomorphism: the inverse sends the
generator of `freeY (U₁ ⊓ U₂)` to the tensor of the two restricted generators. -/
lemma freeYonedaTensorIso_inv_app_generator (U₁ U₂ : X.Opens) :
    (freeYonedaTensorIso U₁ U₂).inv.app (Opposite.op (U₁ ⊓ U₂))
        (ModuleCat.freeMk (𝟙 (U₁ ⊓ U₂))) =
      (ModuleCat.freeMk (homOfLE inf_le_left) ⊗ₜ ModuleCat.freeMk (homOfLE inf_le_right) :
        (((free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₁) ⊗
          (free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₂)).obj
            (Opposite.op (U₁ ⊓ U₂)))) := by
  change ((freeTensorIso X.sheaf.obj (yoneda.obj U₁) (yoneda.obj U₂)).hom.app _
    (((free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).map
      (yonedaMeetIso U₁ U₂).inv).app _ (ModuleCat.freeMk (𝟙 (U₁ ⊓ U₂))))) = _
  rw [free_map_app_freeMk]
  change (freeTensorDesc X.sheaf.obj (yoneda.obj U₁) (yoneda.obj U₂)).app _ _ = _
  rw [freeTensorDesc_app]
  erw [freeTensorμ_inv_freeMk]
  rfl

/-- **[D-PresPB′-general], leaf G3-η.** The unit comparison
`η : f^*ᵖ(𝒪_X) ⟶ 𝒪_Y` of the doctrinal oplax structure on the presheaf pullback of a
scheme morphism is an isomorphism *before sheafification*: the presheaf unit is the
free-yoneda on the terminal open `⊤`, `f⁻¹(⊤) = ⊤`, and maps out of a pulled-back
free-yoneda are computed by one generator (`pullbackFreeYonedaIso`). -/
theorem isIso_pullback_η :
    letI := pullbackOplaxMonoidal (schemeRingPresheafHom f)
    IsIso (Functor.OplaxMonoidal.η (pullback.{u} (schemeRingPresheafHom f))) := by
  letI := pullbackOplaxMonoidal (schemeRingPresheafHom f)
  letI := pushforwardFactoredLaxMonoidal (schemeRingPresheafHom f)
  have key : Functor.OplaxMonoidal.η (pullback.{u} (schemeRingPresheafHom f)) =
      ((pullback.{u} (schemeRingPresheafHom f)).mapIso
        (unitFreeYonedaIso (X := X)).symm).hom ≫
        (pullbackFreeYonedaIso (schemeRingPresheafHom f) (⊤ : X.Opens)).hom ≫
        (unitFreeYonedaIso (X := Y)).hom := by
    apply ((pullbackPushforwardFactoredAdjunction
      (schemeRingPresheafHom f)).homEquiv _ _).injective
    rw [show Functor.OplaxMonoidal.η (pullback.{u} (schemeRingPresheafHom f)) =
      ((pullbackPushforwardFactoredAdjunction (schemeRingPresheafHom f)).homEquiv
        (𝟙_ (PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)))
        (𝟙_ (PresheafOfModules.{u} (Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat)))).symm
        (Functor.LaxMonoidal.ε (pushforwardFactored (schemeRingPresheafHom f)))
      from rfl]
    rw [Equiv.apply_symm_apply, Functor.mapIso_hom,
      Adjunction.homEquiv_naturality_left, ← Iso.inv_comp_eq]
    dsimp only [pullbackPushforwardFactoredAdjunction]
    erw [Adjunction.homEquiv_ofNatIsoRight_apply,
      homEquiv_pullbackFreeYonedaIso_hom_comp]
    apply freeYonedaEquiv.injective
    rw [freeYonedaEquiv_apply, freeYonedaEquiv_apply]
    conv_lhs => erw [ModuleCat.comp_apply]
    conv_rhs => erw [ModuleCat.comp_apply]
    have hcore := corepresentableBy_homEquiv_app_generator
      (X := (⊤ : X.Opens)) (schemeRingPresheafHom f)
      (unitFreeYonedaIso (X := Y)).hom
    erw [hcore]
    erw [pushforwardIsoFactored_hom_app_app]
    erw [freeYonedaEquiv_apply]
    rw [Iso.symm_inv]
    have h1X : (unitFreeYonedaIso (X := X)).hom.app (Opposite.op (⊤ : X.Opens))
        (ModuleCat.freeMk (𝟙 (⊤ : X.Opens))) =
        (1 : ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj
          (Opposite.op (⊤ : X.Opens)))) :=
      unitDesc_app_freeMk (X := X) (𝟙 (⊤ : X.Opens))
    have h1Y : (unitFreeYonedaIso (X := Y)).hom.app (Opposite.op (⊤ : Y.Opens))
        (ModuleCat.freeMk (𝟙 (⊤ : Y.Opens))) =
        (1 : ((Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj
          (Opposite.op (⊤ : Y.Opens)))) :=
      unitDesc_app_freeMk (X := Y) (𝟙 (⊤ : Y.Opens))
    erw [h1X, h1Y]
    have hε := pushforwardFactored_ε_app_apply (schemeRingPresheafHom f)
      (Opposite.op (⊤ : X.Opens))
      (1 : ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj
        (Opposite.op (⊤ : X.Opens))))
    erw [hε]
    exact map_one ((schemeRingPresheafHom f).app (Opposite.op (⊤ : X.Opens))).hom
  rw [key]
  let e := ((pullback.{u} (schemeRingPresheafHom f)).mapIso
    (unitFreeYonedaIso (X := X)).symm).trans
      (pullbackFreeYonedaIso (schemeRingPresheafHom f) (⊤ : X.Opens)) |>.trans
        (unitFreeYonedaIso (X := Y))
  change IsIso e.hom
  exact e.isIso_hom

private theorem freeYonedaEquiv_pullbackδ_canonical (U₁ U₂ : X.Opens) :
    letI := pushforwardFactoredLaxMonoidal (schemeRingPresheafHom f)
    freeYonedaEquiv
      ((freeYonedaTensorIso U₁ U₂).inv ≫
        (((pullbackPushforwardFactoredAdjunction
              (schemeRingPresheafHom f)).unit.app
            ((free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj
              (yoneda.obj U₁)) ⊗ₘ
          (pullbackPushforwardFactoredAdjunction
              (schemeRingPresheafHom f)).unit.app
            ((free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj
              (yoneda.obj U₂))) ≫
        Functor.LaxMonoidal.μ (pushforwardFactored (schemeRingPresheafHom f))
          ((pullback (schemeRingPresheafHom f)).obj
            ((free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj
              (yoneda.obj U₁)))
          ((pullback (schemeRingPresheafHom f)).obj
            ((free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj
              (yoneda.obj U₂))))) =
      freeYonedaEquiv
        ((pushforwardCompCoyonedaFreeYonedaCorepresentableBy
            (schemeRingPresheafHom f) (U₁ ⊓ U₂)).homEquiv
          (((freeYonedaTensorIso ((Opens.map f.base).obj U₁)
              ((Opens.map f.base).obj U₂)).symm.trans
            (MonoidalCategory.tensorIso
              (pullbackFreeYonedaIso (schemeRingPresheafHom f) U₁).symm
              (pullbackFreeYonedaIso (schemeRingPresheafHom f) U₂).symm)).hom) ≫
        (pushforwardIsoFactored (schemeRingPresheafHom f)).hom.app
          ((pullback (schemeRingPresheafHom f)).obj
              ((free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj
                (yoneda.obj U₁)) ⊗
            (pullback (schemeRingPresheafHom f)).obj
              ((free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj
                (yoneda.obj U₂)))) := by
  letI := pushforwardFactoredLaxMonoidal (schemeRingPresheafHom f)
  rw [freeYonedaEquiv_apply, freeYonedaEquiv_apply]
  erw [comp_app, comp_app, ModuleCat.comp_apply, ModuleCat.comp_apply,
    freeYonedaTensorIso_inv_app_generator]
  erw [comp_app, ModuleCat.comp_apply, corepresentableBy_homEquiv_app_generator]
  erw [freeYonedaEquiv_apply]
  conv_rhs => erw [comp_app, ModuleCat.comp_apply]
  rw [Iso.symm_hom, tensorIso_hom, Iso.symm_hom, Iso.symm_hom]
  have hgen : (freeYonedaTensorIso (X := Y) ((Opens.map f.base).obj U₁)
      ((Opens.map f.base).obj U₂)).inv.app
        (Opposite.op ((Opens.map f.base).obj (U₁ ⊓ U₂)))
        (ModuleCat.freeMk (𝟙 ((Opens.map f.base).obj (U₁ ⊓ U₂)))) =
      (ModuleCat.freeMk ((Opens.map f.base).map
          (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁))) ⊗ₜ
        ModuleCat.freeMk ((Opens.map f.base).map
          (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂))) :
        (((free (Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj
            (yoneda.obj ((Opens.map f.base).obj U₁)) ⊗
          (free (Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj
            (yoneda.obj ((Opens.map f.base).obj U₂))).obj
              (Opposite.op ((Opens.map f.base).obj (U₁ ⊓ U₂))))) :=
    freeYonedaTensorIso_inv_app_generator (X := Y)
      ((Opens.map f.base).obj U₁) ((Opens.map f.base).obj U₂)
  erw [hgen]
  have htUnits := tensorHom_app_tmul (T := X.sheaf.obj)
    ((pullbackPushforwardFactoredAdjunction (schemeRingPresheafHom f)).unit.app
      ((free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₁)))
    ((pullbackPushforwardFactoredAdjunction (schemeRingPresheafHom f)).unit.app
      ((free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₂)))
    (Opposite.op (U₁ ⊓ U₂))
    (ModuleCat.freeMk (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)))
    (ModuleCat.freeMk (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)))
  have htPullback := tensorHom_app_tmul (T := Y.sheaf.obj)
    ((pullbackFreeYonedaIso (schemeRingPresheafHom f) U₁).inv)
    ((pullbackFreeYonedaIso (schemeRingPresheafHom f) U₂).inv)
    (Opposite.op ((Opens.map f.base).obj (U₁ ⊓ U₂)))
    (ModuleCat.freeMk ((Opens.map f.base).map
      (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁))))
    (ModuleCat.freeMk ((Opens.map f.base).map
      (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂))))
  refine Eq.trans (congrArg _ (congrArg _ htUnits)) ?_
  have hu₁ := factoredUnit_app_freeMk (schemeRingPresheafHom f) U₁
    (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁))
  have hu₂ := factoredUnit_app_freeMk (schemeRingPresheafHom f) U₂
    (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂))
  have hι₁ := app_freeMk ((pullbackFreeYonedaIso (schemeRingPresheafHom f) U₁).inv)
    ((Opens.map f.base).map (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)))
  have hι₂ := app_freeMk ((pullbackFreeYonedaIso (schemeRingPresheafHom f) U₂).inv)
    ((Opens.map f.base).map (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)))
  let M₁ := (pullback.{u} (schemeRingPresheafHom f)).obj
    ((free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₁))
  let M₂ := (pullback.{u} (schemeRingPresheafHom f)).obj
    ((free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₂))
  let x₁ := ((pushforwardFactored (schemeRingPresheafHom f)).obj M₁).map
    (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).op
    (freeYonedaEquiv (X := (Opens.map f.base).obj U₁) (M := M₁)
      ((pullbackFreeYonedaIso (schemeRingPresheafHom f) U₁).inv))
  let x₂ := ((pushforwardFactored (schemeRingPresheafHom f)).obj M₂).map
    (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).op
    (freeYonedaEquiv (X := (Opens.map f.base).obj U₂) (M := M₂)
      ((pullbackFreeYonedaIso (schemeRingPresheafHom f) U₂).inv))
  refine Eq.trans (congrArg _ (congrArg₂ (fun a b => a ⊗ₜ b) hu₁ hu₂)) ?_
  refine Eq.trans (pushforwardFactoredμ_expanded_app_tmul
    (C := X.Opens) (D := Y.Opens) (F := Opens.map f.base)
    (R := Y.sheaf.obj) (S := X.sheaf.obj) (φ := schemeRingPresheafHom f)
    (M := M₁) (N := M₂) (V := Opposite.op (U₁ ⊓ U₂))
    (x := x₁) (y := x₂)) ?_
  exact (congrArg₂ (fun a b => a ⊗ₜ b) hι₁.symm hι₂.symm).trans htPullback.symm

/-- **[D-PresPB′-general], leaf G3-pre (δ on free-yoneda pairs).** The tensor comparison
`δ : f^*ᵖ(P ⊗ Q) ⟶ f^*ᵖP ⊗ f^*ᵖQ` of the doctrinal oplax structure on the presheaf
pullback of a scheme morphism is an isomorphism on free-yoneda pairs, *before
sheafification*: both sides are the free-yoneda on `f⁻¹(U₁ ⊓ U₂) = f⁻¹U₁ ⊓ f⁻¹U₂`
(the lattice miracle `freeYonedaTensorIso` upstairs and downstairs +
`pullbackFreeYonedaIso`), and `δ` matches the canonical isomorphism on the one
generator that determines it. -/
theorem isIso_pullback_δ_freeYoneda (U₁ U₂ : X.Opens) :
    letI := pullbackOplaxMonoidal (schemeRingPresheafHom f)
    IsIso (Functor.OplaxMonoidal.δ (pullback.{u} (schemeRingPresheafHom f))
      ((free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₁))
      ((free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₂))) := by
  letI := pullbackOplaxMonoidal (schemeRingPresheafHom f)
  letI := pushforwardFactoredLaxMonoidal (schemeRingPresheafHom f)
  let e := ((pullback.{u} (schemeRingPresheafHom f)).mapIso
    (freeYonedaTensorIso U₁ U₂)).trans
      ((pullbackFreeYonedaIso (schemeRingPresheafHom f) (U₁ ⊓ U₂)).trans
        ((freeYonedaTensorIso ((Opens.map f.base).obj U₁)
          ((Opens.map f.base).obj U₂)).symm.trans
            (MonoidalCategory.tensorIso
              (pullbackFreeYonedaIso (schemeRingPresheafHom f) U₁).symm
              (pullbackFreeYonedaIso (schemeRingPresheafHom f) U₂).symm)))
  have key : Functor.OplaxMonoidal.δ (pullback.{u} (schemeRingPresheafHom f))
      ((free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₁))
      ((free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₂)) =
      e.hom := by
    dsimp only [e]
    apply ((pullbackPushforwardFactoredAdjunction (schemeRingPresheafHom f)).homEquiv
      _ _).injective
    rw [show Functor.OplaxMonoidal.δ (pullback.{u} (schemeRingPresheafHom f))
        ((free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₁))
        ((free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₂)) =
      ((pullbackPushforwardFactoredAdjunction (schemeRingPresheafHom f)).homEquiv
        ((free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₁) ⊗
          (free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₂))
        ((pullback.{u} (schemeRingPresheafHom f)).obj
            ((free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₁)) ⊗
          (pullback.{u} (schemeRingPresheafHom f)).obj
            ((free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₂)))).symm
        (((pullbackPushforwardFactoredAdjunction (schemeRingPresheafHom f)).unit.app
            ((free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₁)) ⊗ₘ
          (pullbackPushforwardFactoredAdjunction (schemeRingPresheafHom f)).unit.app
            ((free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₂))) ≫
          Functor.LaxMonoidal.μ (pushforwardFactored (schemeRingPresheafHom f))
            ((pullback.{u} (schemeRingPresheafHom f)).obj
              ((free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₁)))
            ((pullback.{u} (schemeRingPresheafHom f)).obj
              ((free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₂))))
      from rfl]
    rw [Equiv.apply_symm_apply, Iso.trans_hom, Functor.mapIso_hom,
      Adjunction.homEquiv_naturality_left, ← Iso.inv_comp_eq]
    dsimp only [pullbackPushforwardFactoredAdjunction]
    erw [Adjunction.homEquiv_ofNatIsoRight_apply, Iso.trans_hom,
      homEquiv_pullbackFreeYonedaIso_hom_comp]
    apply freeYonedaEquiv.injective
    exact freeYonedaEquiv_pullbackδ_canonical f U₁ U₂
  refine ⟨e.inv, ?_, ?_⟩
  · rw [key]
    exact e.hom_inv_id
  · rw [key]
    exact e.inv_hom_id

/-- **[D-PresPB′-general], leaf G3 (scheme form, all pairs).** The doctrinal tensor
comparison of the presheaf pullback of a scheme morphism is an isomorphism on all pairs:
the free-yoneda base case is the lattice miracle (`isIso_pullback_δ_freeYoneda`), extended
along the canonical presentation by `isIso_pullback_δ_of_freeYoneda`. -/
theorem isIso_pullback_δ
    (P Q : PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) :
    letI := pullbackOplaxMonoidal (schemeRingPresheafHom f)
    IsIso (Functor.OplaxMonoidal.δ (pullback.{u} (schemeRingPresheafHom f)) P Q) :=
  isIso_pullback_δ_of_freeYoneda (schemeRingPresheafHom f)
    (fun U₁ U₂ => isIso_pullback_δ_freeYoneda f U₁ U₂) P Q

/-- **[D-PresPB′-general], leaf A (presheaf-level payoff): the presheaf pullback of a
scheme morphism is a monoidal functor** — `f^*ᵖ(P ⊗ Q) ≅ f^*ᵖP ⊗ f^*ᵖQ` and
`f^*ᵖ(𝒪_X) ≅ 𝒪_Y`, before sheafification: the doctrinal oplax structure has invertible
structure maps ([G3-pre] + [G3-η] + the presentation extension). -/
@[implicit_reducible]
noncomputable def pullbackMonoidal :
    (pullback.{u} (schemeRingPresheafHom f)).Monoidal :=
  letI := pullbackOplaxMonoidal (schemeRingPresheafHom f)
  haveI : IsIso (Functor.OplaxMonoidal.η (pullback.{u} (schemeRingPresheafHom f))) :=
    isIso_pullback_η f
  haveI : ∀ P Q, IsIso
      (Functor.OplaxMonoidal.δ (pullback.{u} (schemeRingPresheafHom f)) P Q) :=
    fun P Q => isIso_pullback_δ f P Q
  Functor.Monoidal.ofOplaxMonoidal _

end SchemePullbackMonoidal

section SheafDescent

variable {C' D' : Type u} [SmallCategory C'] [SmallCategory D']
  {J : GrothendieckTopology C'} {K : GrothendieckTopology D'}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
  {F : C' ⥤ D'} [F.IsContinuous J K]
  (S : C'ᵒᵖ ⥤ CommRingCat.{u}) (hS : Presheaf.IsSheaf J (S ⋙ forget₂ CommRingCat RingCat))
  (R : D'ᵒᵖ ⥤ CommRingCat.{u}) (hR : Presheaf.IsSheaf K (R ⋙ forget₂ CommRingCat RingCat))
  (φ₀ : (S ⋙ forget₂ CommRingCat RingCat) ⟶
    F.op ⋙ (R ⋙ forget₂ CommRingCat RingCat))

/-- **[D-PresPB′-general], leaf A (descent).** If the presheaf-level pullback along `φ₀` is
monoidal, then the sheaf-level pullback is monoidal for the localized monoidal structures:
`functorMonoidalOfComp` along the sheafification localization, with the lifting supplied by
mathlib's `sheafificationCompPullback`. -/
@[implicit_reducible]
noncomputable def sheafPullbackMonoidal
    (hmono : (PresheafOfModules.pullback.{u} φ₀).Monoidal) :
    letI := PresheafOfModules.sheafOfModulesMonoidalCategory S hS
    letI := PresheafOfModules.sheafOfModulesMonoidalCategory R hR
    (SheafOfModules.pullback.{u}
      (⟨φ₀⟩ : (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}) ⟶
        (F.sheafPushforwardContinuous RingCat.{u} J K).obj
          ⟨R ⋙ forget₂ CommRingCat RingCat, hR⟩)).Monoidal := by
  letI := PresheafOfModules.sheafOfModulesMonoidalCategory S hS
  letI := PresheafOfModules.sheafOfModulesMonoidalCategory R hR
  letI pullbackMonoidal : (PresheafOfModules.pullback.{u} φ₀).Monoidal := hmono
  letI : (Localization.Monoidal.toMonoidalCategory
      (L := PresheafOfModules.sheafification.{u}
        (𝟙 (⟨R ⋙ forget₂ CommRingCat RingCat, hR⟩ : Sheaf K RingCat.{u}).obj))
      (W := PresheafOfModules.sheafificationW.{u}
        (𝟙 (⟨R ⋙ forget₂ CommRingCat RingCat, hR⟩ : Sheaf K RingCat.{u}).obj))
      (Iso.refl _)).Monoidal := inferInstance
  letI compositeMonoidal : (PresheafOfModules.pullback.{u} φ₀ ⋙
      Localization.Monoidal.toMonoidalCategory
        (L := PresheafOfModules.sheafification.{u}
          (𝟙 (⟨R ⋙ forget₂ CommRingCat RingCat, hR⟩ : Sheaf K RingCat.{u}).obj))
        (W := PresheafOfModules.sheafificationW.{u}
          (𝟙 (⟨R ⋙ forget₂ CommRingCat RingCat, hR⟩ : Sheaf K RingCat.{u}).obj))
        (Iso.refl _)).Monoidal := inferInstance
  letI lifting : Localization.Lifting
      (Localization.Monoidal.toMonoidalCategory
        (L := PresheafOfModules.sheafification.{u}
          (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).obj))
        (W := PresheafOfModules.sheafificationW.{u}
          (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).obj))
        (Iso.refl _))
      (PresheafOfModules.sheafificationW.{u}
        (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).obj))
      (PresheafOfModules.pullback.{u} φ₀ ⋙
        Localization.Monoidal.toMonoidalCategory
          (L := PresheafOfModules.sheafification.{u}
            (𝟙 (⟨R ⋙ forget₂ CommRingCat RingCat, hR⟩ : Sheaf K RingCat.{u}).obj))
          (W := PresheafOfModules.sheafificationW.{u}
            (𝟙 (⟨R ⋙ forget₂ CommRingCat RingCat, hR⟩ : Sheaf K RingCat.{u}).obj))
          (Iso.refl _))
      (SheafOfModules.pullback.{u}
        (⟨φ₀⟩ : (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}) ⟶
          (F.sheafPushforwardContinuous RingCat.{u} J K).obj
            ⟨R ⋙ forget₂ CommRingCat RingCat, hR⟩)) :=
    ⟨(SheafOfModules.sheafificationCompPullback.{u}
      (⟨φ₀⟩ : (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}) ⟶
        (F.sheafPushforwardContinuous RingCat.{u} J K).obj
          ⟨R ⋙ forget₂ CommRingCat RingCat, hR⟩))⟩
  exact @Localization.Monoidal.functorMonoidalOfComp
    _ _ _ _ _ _ _ _ _
    (Localization.Monoidal.toMonoidalCategory
      (L := PresheafOfModules.sheafification.{u}
        (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).obj))
      (W := PresheafOfModules.sheafificationW.{u}
        (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).obj))
      (Iso.refl _))
    (PresheafOfModules.sheafificationW.{u}
      (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).obj))
    _ _
    (SheafOfModules.pullback.{u}
      (⟨φ₀⟩ : (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}) ⟶
        (F.sheafPushforwardContinuous RingCat.{u} J K).obj
          ⟨R ⋙ forget₂ CommRingCat RingCat, hR⟩))
    (PresheafOfModules.pullback.{u} φ₀ ⋙
      Localization.Monoidal.toMonoidalCategory
        (L := PresheafOfModules.sheafification.{u}
          (𝟙 (⟨R ⋙ forget₂ CommRingCat RingCat, hR⟩ : Sheaf K RingCat.{u}).obj))
        (W := PresheafOfModules.sheafificationW.{u}
          (𝟙 (⟨R ⋙ forget₂ CommRingCat RingCat, hR⟩ : Sheaf K RingCat.{u}).obj))
        (Iso.refl _)) compositeMonoidal _ lifting

/-- The sheaf-level pullback monoidal structure exists. -/
theorem nonempty_sheafPullback_monoidal
    (hmono : (PresheafOfModules.pullback.{u} φ₀).Monoidal) :
    letI := PresheafOfModules.sheafOfModulesMonoidalCategory S hS
    letI := PresheafOfModules.sheafOfModulesMonoidalCategory R hR
    Nonempty ((SheafOfModules.pullback.{u}
      (⟨φ₀⟩ : (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}) ⟶
        (F.sheafPushforwardContinuous RingCat.{u} J K).obj
          ⟨R ⋙ forget₂ CommRingCat RingCat, hR⟩)).Monoidal) :=
  ⟨sheafPullbackMonoidal S hS R hR φ₀ hmono⟩

end SheafDescent

end PresheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- Sheafifying the underlying presheaf of a sheaf of modules returns that sheaf.  This small
comparison is selectively retained from AINTLIB's `Picard/InvertibleSheaf.lean`; none of that
file's cover-local invertibility API is needed by the Picard pullback construction. -/
noncomputable def sheafifyValIso (M : SheafOfModules X.ringCatSheaf) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj M.val ≅ M :=
  (asIso (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).counit).app M

noncomputable local instance pullbackTensorPresheafPushforwardIsRightAdjoint
    (f : Y ⟶ X) :
    (PresheafOfModules.pushforward.{u} f.toRingCatSheafHom.hom).IsRightAdjoint := by
  change (PresheafOfModules.pushforward.{u}
    (_root_.PresheafOfModules.schemeRingPresheafHom f)).IsRightAdjoint
  exact PresheafOfModules.instIsRightAdjointPushforward
    (_root_.PresheafOfModules.schemeRingPresheafHom f)

noncomputable local instance pullbackTensorSheafPushforwardIsRightAdjoint
    (f : Y ⟶ X) :
    (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint := by
  change (Scheme.Modules.pushforward f).IsRightAdjoint
  infer_instance

/-- The inverse of the canonical comparison from sheafification of the underlying
presheaf to a sheaf is the sheafification-adjunction unit on sections. -/
theorem sheafifyValIso_inv_app_apply
    (M : X.Modules) (U : X.Opens) (x : M.val.obj (.op U)) :
    (sheafifyValIso M).inv.val.app (.op U) x =
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app M.val).app (.op U) x := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let c := sheafifyValIso M
  have htri := adj.right_triangle_components M
  change adj.unit.app M.val ≫ c.hom.val = 𝟙 M.val at htri
  have htriApply := congrArg (fun q => q.app (.op U) x) htri
  conv_lhs at htriApply =>
    erw [PresheafOfModules.comp_app, ModuleCat.comp_apply]
  change c.hom.val.app (.op U)
      ((adj.unit.app M.val).app (.op U) x) = x at htriApply
  have hcancel := congrArg (fun q => q.val.app (.op U) x) c.inv_hom_id
  conv_lhs at hcancel =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  change c.hom.val.app (.op U) (c.inv.val.app (.op U) x) = x at hcancel
  have hinj : Function.Injective (c.hom.val.app (.op U)) := by
    refine Function.LeftInverse.injective (g := c.inv.val.app (.op U)) ?_
    intro y
    have hleft := congrArg (fun q => q.val.app (.op U) y) c.hom_inv_id
    conv_lhs at hleft =>
      erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
        ModuleCat.comp_apply]
    exact hleft
  exact hinj (hcancel.trans htriApply.symm)

/-- The canonical presentation of sheaf pullback as sheafified presheaf pullback sends
the pullback-adjunction unit of a section to the sheafification-unit image of the
corresponding presheaf-pullback-adjunction unit. -/
theorem pullbackIso_hom_unit_app_apply
    (f : Y ⟶ X) (M : X.Modules) (U : X.Opens) (x : M.val.obj (.op U)) :
    ((SheafOfModules.pullbackIso f.toRingCatSheafHom).hom.app M).val.app
        (.op (f ⁻¹ᵁ U))
        (((pullbackPushforwardAdjunction f).unit.app M).val.app (.op U) x) =
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 Y.ringCatSheaf.obj)).unit.app
          ((PresheafOfModules.pullback
            (_root_.PresheafOfModules.schemeRingPresheafHom f)).obj M.val)).app
        (.op (f ⁻¹ᵁ U))
          (((PresheafOfModules.pullbackPushforwardAdjunction
            (_root_.PresheafOfModules.schemeRingPresheafHom f)).unit.app M.val).app
              (.op U) x) := by
  let adj₁ := SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom
  let adj₂ := SheafOfModules.PullbackConstruction.adjunction f.toRingCatSheafHom
  let e := SheafOfModules.pullbackIso f.toRingCatSheafHom
  have he := Adjunction.homEquiv_leftAdjointUniq_hom_app adj₁ adj₂ M
  change (adj₁.homEquiv _ _) (e.hom.app M) = adj₂.unit.app M at he
  change adj₁.unit.app M ≫
    (SheafOfModules.pushforward f.toRingCatSheafHom).map (e.hom.app M) =
      adj₂.unit.app M at he
  have happ := congrArg (fun q => q.val.app (.op U) x) he
  conv_lhs at happ =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  exact happ

/-- The comparison between pullback after sheafification and sheafification after
presheaf pullback sends the unit of the first composite adjunction to the unit of the
second, on elements. -/
theorem sheafificationCompPullback_hom_unit_app_apply
    (f : Y ⟶ X) (P : X.PresheafOfModules) (U : X.Opens)
    (x : P.obj (.op U)) :
    let LX := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
    let PB := PresheafOfModules.pullback
      (_root_.PresheafOfModules.schemeRingPresheafHom f)
    let shAdjX := PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)
    let shAdjY := PresheafOfModules.sheafificationAdjunction
      (𝟙 Y.ringCatSheaf.obj)
    let preAdj := PresheafOfModules.pullbackPushforwardAdjunction
      (_root_.PresheafOfModules.schemeRingPresheafHom f)
    ((SheafOfModules.sheafificationCompPullback
      f.toRingCatSheafHom).hom.app P).val.app (.op (f ⁻¹ᵁ U))
        (((pullbackPushforwardAdjunction f).unit.app (LX.obj P)).val.app
          (.op U) ((shAdjX.unit.app P).app (.op U) x)) =
      (shAdjY.unit.app (PB.obj P)).app (.op (f ⁻¹ᵁ U))
        ((preAdj.unit.app P).app (.op U) x) := by
  dsimp only
  let shAdjX := PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let shAdjY := PresheafOfModules.sheafificationAdjunction
    (𝟙 Y.ringCatSheaf.obj)
  let pbAdj := SheafOfModules.pullbackPushforwardAdjunction
    f.toRingCatSheafHom
  let preAdj := PresheafOfModules.pullbackPushforwardAdjunction
    (_root_.PresheafOfModules.schemeRingPresheafHom f)
  let adj₁ := shAdjX.comp pbAdj
  let adj₂ := preAdj.comp shAdjY
  let e := SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom
  have he := Adjunction.homEquiv_leftAdjointUniq_hom_app adj₁ adj₂ P
  change (adj₁.homEquiv _ _) (e.hom.app P) = adj₂.unit.app P at he
  rw [Adjunction.homEquiv_unit] at he
  have happ := congrArg (fun q => q.app (.op U) x) he
  conv_lhs at happ =>
    erw [PresheafOfModules.comp_app, ModuleCat.comp_apply]
  exact happ

/-- **[D-PresPB′-general], payoff packaging (leaves G3 + A).** The pullback of sheaves of
modules along an arbitrary morphism of schemes is a monoidal functor for the (v10.97)
localized-monoidal structures: the objectwise content is the general-`f` sheafified
pullback–tensor comparison (`nonempty_sheafify_presheafPullback_tensor`, extended from the
free-yoneda generators by two single-variable presentation passes in the abelian
`SheafOfModules`), packaged through `functorMonoidalOfComp` with the `Lifting` instance
`sheafificationCompPullback`. Consumer: `Skeleton.monoidHom` then gives
`Pic(f) : Pic X →* Pic Y` — the GME (2.16) Picard functor. -/
@[implicit_reducible]
noncomputable def pullbackMonoidal (f : Y ⟶ X) :
    letI := Modules.monoidalCategory X
    letI := Modules.monoidalCategory Y
    (Modules.pullback f).Monoidal := by
  letI := Modules.monoidalCategory X
  letI := Modules.monoidalCategory Y
  exact _root_.PresheafOfModules.sheafPullbackMonoidal
    (F := TopologicalSpace.Opens.map f.base)
    X.sheaf.obj X.ringCatSheaf.property Y.sheaf.obj Y.ringCatSheaf.property
    (_root_.PresheafOfModules.schemeRingPresheafHom f)
    (_root_.PresheafOfModules.pullbackMonoidal f)

/-- Pullback of sheaves of modules admits the canonical monoidal structure constructed
through presheaf pullback and sheafification. -/
theorem nonempty_pullback_monoidal (f : Y ⟶ X) :
    letI := Modules.monoidalCategory X
    letI := Modules.monoidalCategory Y
    Nonempty ((Modules.pullback f).Monoidal) :=
  ⟨pullbackMonoidal f⟩

/-- **[PIC-P1b-MONO], leaf D-PresPB′ (general `f`), relocated from
`PullbackTensorMonoidal` and closed** (respelled at the `CommRingCat`-derived clothing of
this file; the original `ringCatSheaf`-spelled statement is definitionally the same). The
presheaf pullback commutes with the presheaf tensor *after sheafification* — in fact
already before sheafification (`PresheafOfModules.pullbackMonoidal`): apply the
sheafification to the (inverse of the) tensorator of the monoidal presheaf pullback. -/
theorem nonempty_sheafify_presheafPullback_tensor (f : Y ⟶ X)
    (P Q : _root_.PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) :
    Nonempty ((PresheafOfModules.sheafification.{u}
        (𝟙 (⟨Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat, Y.ringCatSheaf.property⟩ :
          Sheaf _ RingCat.{u}).obj)).obj
        ((PresheafOfModules.pullback.{u}
          (_root_.PresheafOfModules.schemeRingPresheafHom f)).obj (P ⊗ Q)) ≅
      (PresheafOfModules.sheafification.{u}
        (𝟙 (⟨Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat, Y.ringCatSheaf.property⟩ :
          Sheaf _ RingCat.{u}).obj)).obj
        ((PresheafOfModules.pullback.{u}
            (_root_.PresheafOfModules.schemeRingPresheafHom f)).obj P ⊗
          (PresheafOfModules.pullback.{u}
            (_root_.PresheafOfModules.schemeRingPresheafHom f)).obj Q)) := by
  letI := _root_.PresheafOfModules.pullbackMonoidal f
  exact ⟨(PresheafOfModules.sheafification.{u}
      (𝟙 (⟨Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat, Y.ringCatSheaf.property⟩ :
        Sheaf _ RingCat.{u}).obj)).mapIso
    (Functor.Monoidal.μIso (PresheafOfModules.pullback.{u}
      (_root_.PresheafOfModules.schemeRingPresheafHom f)) P Q).symm⟩

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

/-- **The Picard functor on morphisms** (GME 2.2.2 (2.16), p. 108): pullback of invertible
sheaves along `f : Y ⟶ X` induces a group homomorphism `Pic X →* Pic Y` — the underlying
monoidal functor is `Modules.pullback f` (`nonempty_pullback_monoidal`), inducing a monoid
homomorphism on the skeleton of iso-classes and hence a group homomorphism on units. -/
noncomputable def Pic.map {X Y : Scheme.{u}} (f : Y ⟶ X) : Pic X →* Pic Y :=
  letI := Modules.monoidalCategory X
  letI := Modules.monoidalCategory Y
  letI : (Modules.pullback f).Monoidal := (Modules.nonempty_pullback_monoidal f).some
  Units.map (Skeleton.monoidHom (F := Modules.pullback f))

/-- The Picard functor preserves identities. -/
theorem Pic.map_id (X : Scheme.{u}) : Pic.map (𝟙 X) = MonoidHom.id (Pic X) := by
  letI := Modules.monoidalCategory X
  refine MonoidHom.ext (fun u => Units.ext ?_)
  change (Modules.pullback (𝟙 X)).mapSkeleton.obj u.val = u.val
  exact Quotient.inductionOn u.val (fun M =>
    (Functor.mapSkeleton_obj_toSkeleton (Modules.pullback (𝟙 X)) M).trans
      (Quotient.sound ⟨(Modules.pullbackId X).app M⟩))

/-- Value form of the Picard functor: the underlying iso-class map is the skeleton map of
the pullback. -/
lemma Pic.map_val {X Y : Scheme.{u}} (f : Y ⟶ X) (u : Pic X) :
    letI := Modules.monoidalCategory X
    letI := Modules.monoidalCategory Y
    (Pic.map f u).val = (Modules.pullback f).mapSkeleton.obj u.val :=
  rfl

/-- The skeleton maps of pullbacks compose (pure skeleton statement — no Picard group,
no choice of monoidal structures). -/
lemma mapSkeleton_pullback_comp {X Y Z : Scheme.{u}} (g : Z ⟶ Y) (f : Y ⟶ X)
    (q : Skeleton X.Modules) :
    (Modules.pullback (g ≫ f)).mapSkeleton.obj q =
      (Modules.pullback g).mapSkeleton.obj ((Modules.pullback f).mapSkeleton.obj q) :=
  Quotient.inductionOn q (fun M =>
    ((Functor.mapSkeleton_obj_toSkeleton (Modules.pullback (g ≫ f)) M).trans
      (Quotient.sound ⟨((Modules.pullbackComp (f := g) (g := f)).app M).symm⟩)).trans
      ((Functor.mapSkeleton_obj_toSkeleton (Modules.pullback g)
        ((Modules.pullback f).obj M)).symm.trans
        (congrArg (Modules.pullback g).mapSkeleton.obj
          (Functor.mapSkeleton_obj_toSkeleton (Modules.pullback f) M).symm)))

/-- The Picard functor preserves composition (contravariantly). -/
theorem Pic.map_comp {X Y Z : Scheme.{u}} (g : Z ⟶ Y) (f : Y ⟶ X) :
    Pic.map (g ≫ f) = (Pic.map g).comp (Pic.map f) := by
  letI := Modules.monoidalCategory X
  letI := Modules.monoidalCategory Y
  letI := Modules.monoidalCategory Z
  refine MonoidHom.ext (fun u => Units.ext ?_)
  change (Modules.pullback (g ≫ f)).mapSkeleton.obj u.val =
    (Modules.pullback g).mapSkeleton.obj ((Pic.map f u).val)
  rw [Pic.map_val]
  exact mapSkeleton_pullback_comp g f u.val

end AlgebraicGeometry.Scheme
