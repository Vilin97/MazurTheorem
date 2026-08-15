/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Coproduct epimorphisms and naturally isomorphic functors

An equivalence reflects an epimorphic coproduct family after comparison
with a naturally isomorphic composite functor.
-/

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃ w

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]

/-- A natural isomorphism transports an epimorphic coproduct family
backwards.  Applying this theorem to the inverse natural isomorphism
gives the forward direction. -/
theorem sigmaDesc_map_epi_of_natIso
    {ι : Type w}
    (F G : C ⥤ D) (α : F ≅ G)
    (A : ι → C) (M : C)
    (component : ∀ a, A a ⟶ M)
    [HasCoproduct (fun a => F.obj (A a))]
    [HasCoproduct (fun a => G.obj (A a))]
    (h :
      Epi
        (Sigma.desc
          (fun a => G.map (component a)))) :
    Epi
      (Sigma.desc
        (fun a => F.map (component a))) := by
  let mappedMap :=
    Sigma.desc (fun a => F.map (component a))
  let transportedMap :=
    Sigma.desc (fun a => G.map (component a))
  let familyIso :
      Discrete.functor (fun a => F.obj (A a)) ≅
        Discrete.functor (fun a => G.obj (A a)) :=
    Discrete.natIso (fun a => α.app (A a.as))
  let sourceIso :
      (∐ fun a => F.obj (A a)) ≅
        (∐ fun a => G.obj (A a)) :=
    HasColimit.isoOfNatIso familyIso
  let transported :=
    (sourceIso.hom ≫ transportedMap) ≫
      (α.app M).inv
  have htransported : transported = mappedMap := by
    apply Sigma.hom_ext
    intro a
    have hsource :
        Sigma.ι (fun b => F.obj (A b)) a ≫
            sourceIso.hom =
          (α.app (A a)).hom ≫
            Sigma.ι (fun b => G.obj (A b)) a := by
      dsimp only [sourceIso]
      exact HasColimit.isoOfNatIso_ι_hom
        familyIso (Discrete.mk a)
    have hα :
        F.map (component a) ≫
            (α.app M).hom =
          (α.app (A a)).hom ≫
            G.map (component a) := by
      exact α.hom.naturality (component a)
    have hnaturality :
        (α.app (A a)).hom ≫
              G.map (component a) ≫
              (α.app M).inv =
            F.map (component a) := by
      calc
        (α.app (A a)).hom ≫
              G.map (component a) ≫
              (α.app M).inv =
            (F.map (component a) ≫
              (α.app M).hom) ≫
              (α.app M).inv := by
                rw [hα]
                simp only [Category.assoc]
        _ = F.map (component a) := by
          simp only [Category.assoc,
            Iso.hom_inv_id, Category.comp_id]
    calc
      Sigma.ι (fun b => F.obj (A b)) a ≫
          transported =
        ((Sigma.ι (fun b => F.obj (A b)) a ≫
            sourceIso.hom) ≫ transportedMap) ≫
          (α.app M).inv := by
            simp only [transported, Category.assoc]
      _ =
        (((α.app (A a)).hom ≫
            Sigma.ι (fun b => G.obj (A b)) a) ≫
          transportedMap) ≫
          (α.app M).inv := by
            exact congrArg
              (fun z =>
                (z ≫ transportedMap) ≫
                  (α.app M).inv)
              hsource
      _ =
        (α.app (A a)).hom ≫
          G.map (component a) ≫
          (α.app M).inv := by
            simp only [transportedMap,
              Category.assoc, Sigma.ι_desc]
      _ = F.map (component a) := hnaturality
      _ =
        Sigma.ι (fun b => F.obj (A b)) a ≫
          mappedMap := by
            exact
              (Sigma.ι_desc
                (fun b => F.map (component b)) a).symm
  have htransportedEpi : Epi transported := by
    dsimp only [transported]
    letI : Epi transportedMap := by
      dsimp only [transportedMap]
      exact h
    infer_instance
  have hmapped : Epi mappedMap :=
    (congrArg Epi htransported).mp htransportedEpi
  dsimp only [mappedMap] at hmapped
  exact hmapped

/-- If `R ⋙ F` is naturally isomorphic to `G`, with `F` an equivalence,
then an epimorphic coproduct of the `G`-images of a family implies the
corresponding coproduct of the `R`-images is epimorphic. -/
theorem sigmaDesc_map_epi_of_comp_equivalence
    {ι : Type w}
    (R : C ⥤ D) (F : D ⥤ E) [F.IsEquivalence]
    (G : C ⥤ E) (α : R ⋙ F ≅ G)
    (A : ι → C) (M : C)
    (component : ∀ a, A a ⟶ M)
    [HasCoproduct (fun a => R.obj (A a))]
    [HasCoproduct (fun a => G.obj (A a))]
    [HasCoproduct
      (fun a => F.obj (R.obj (A a)))]
    (h :
      Epi
        (Sigma.desc
          (fun a => G.map (component a)))) :
    Epi
      (Sigma.desc
        (fun a => R.map (component a))) := by
  let restrictedMap :=
    Sigma.desc (fun a => R.map (component a))
  let mappedMap :=
    Sigma.desc
      (fun a => F.map (R.map (component a)))
  let transportedMap :=
    Sigma.desc (fun a => G.map (component a))
  let familyIso :
      Discrete.functor
          (fun a => F.obj (R.obj (A a))) ≅
        Discrete.functor
          (fun a => G.obj (A a)) :=
    Discrete.natIso
      (fun a => α.app (A a.as))
  let sourceIso :
      (∐ fun a => F.obj (R.obj (A a))) ≅
        (∐ fun a => G.obj (A a)) :=
    HasColimit.isoOfNatIso familyIso
  let transported :=
    (sourceIso.hom ≫ transportedMap) ≫
      (α.app M).inv
  have htransported : transported = mappedMap := by
    apply Sigma.hom_ext
    intro a
    have hsource :
        Sigma.ι
              (fun b => F.obj (R.obj (A b))) a ≫
            sourceIso.hom =
          (α.app (A a)).hom ≫
            Sigma.ι
              (fun b => G.obj (A b)) a := by
      dsimp only [sourceIso]
      exact HasColimit.isoOfNatIso_ι_hom
        familyIso (Discrete.mk a)
    have hnaturality :
        (α.app (A a)).hom ≫
              G.map (component a) ≫
              (α.app M).inv =
            (R ⋙ F).map (component a) := by
      have hα :
          (R ⋙ F).map (component a) ≫
              (α.app M).hom =
            (α.app (A a)).hom ≫
              G.map (component a) := by
        exact α.hom.naturality (component a)
      calc
        (α.app (A a)).hom ≫
              G.map (component a) ≫
              (α.app M).inv =
            ((R ⋙ F).map (component a) ≫
              (α.app M).hom) ≫
              (α.app M).inv := by
                rw [hα]
                simp only [Category.assoc]
        _ = (R ⋙ F).map (component a) := by
          simp only [Category.assoc,
            Iso.hom_inv_id, Category.comp_id]
    calc
      Sigma.ι
            (fun b => F.obj (R.obj (A b))) a ≫
          transported =
        ((Sigma.ι
              (fun b => F.obj (R.obj (A b))) a ≫
            sourceIso.hom) ≫ transportedMap) ≫
          (α.app M).inv := by
            simp only [transported, Category.assoc]
      _ =
        (((α.app (A a)).hom ≫
            Sigma.ι (fun b => G.obj (A b)) a) ≫
          transportedMap) ≫
          (α.app M).inv := by
            exact congrArg
              (fun z =>
                (z ≫ transportedMap) ≫
                  (α.app M).inv)
              hsource
      _ =
        (α.app (A a)).hom ≫
          G.map (component a) ≫
          (α.app M).inv := by
            simp only [transportedMap,
              Category.assoc, Sigma.ι_desc]
      _ = (R ⋙ F).map (component a) :=
        hnaturality
      _ = F.map (R.map (component a)) := by
        exact Functor.comp_map R F (component a)
      _ =
        Sigma.ι
              (fun b => F.obj (R.obj (A b))) a ≫
          mappedMap := by
            exact
              (Sigma.ι_desc
                (fun b =>
                  F.map (R.map (component b))) a).symm
  have htransportedEpi : Epi transported := by
    dsimp only [transported]
    letI : Epi transportedMap := by
      dsimp only [transportedMap]
      exact h
    infer_instance
  have hmapped : Epi mappedMap :=
    (congrArg Epi htransported).mp htransportedEpi
  have hcomparison :
      sigmaComparison F
          (fun a => R.obj (A a)) ≫
        F.map restrictedMap = mappedMap := by
    dsimp only [restrictedMap, mappedMap]
    exact sigmaComparison_map_desc F
      (fun a => R.obj (A a)) (R.obj M)
      (fun a => R.map (component a))
  have hFmap : Epi (F.map restrictedMap) := by
    apply epi_of_epi_fac
      (f := sigmaComparison F
        (fun a => R.obj (A a)))
      (h := mappedMap)
    exact hcomparison
  have hrestricted : Epi restrictedMap :=
    F.epi_of_epi_map hFmap
  dsimp only [restrictedMap] at hrestricted
  exact hrestricted

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
