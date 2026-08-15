/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.CategoryTheory.Equivalence

/-!
# Naturality after conjugating autoequivalences

An autoequivalence transported across an equivalence is functorial with
respect to a functor between the original categories whenever the
corresponding functor between the equivalent categories commutes with the
untransported autoequivalences.
-/


open CategoryTheory

noncomputable section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

/--
A naturality square written using the forward sides of two equivalences
also determines its inverse-coordinate form.
-/
noncomputable def equivalenceInverseNaturalityIso
    {C : Type u₁} [Category.{v₁} C]
    {C' : Type u₂} [Category.{v₂} C']
    {D : Type u₃} [Category.{v₃} D]
    {D' : Type u₄} [Category.{v₄} D']
    (EC : C ≌ C') (ED : D ≌ D')
    (F : C ⥤ D) (G : C' ⥤ D')
    (hforward :
      F ⋙ ED.functor ≅ EC.functor ⋙ G) :
    EC.inverse ⋙ F ≅ G ⋙ ED.inverse :=
  (EC.inverse ⋙ F).rightUnitor.symm ≪≫
    Functor.isoWhiskerLeft
      (EC.inverse ⋙ F) ED.unitIso ≪≫
    (Functor.associator
      (EC.inverse ⋙ F) ED.functor ED.inverse).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.associator EC.inverse F ED.functor)
      ED.inverse ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft EC.inverse hforward)
      ED.inverse ≪≫
    Functor.isoWhiskerRight
      (Functor.associator
        EC.inverse EC.functor G).symm
      ED.inverse ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight EC.counitIso G)
      ED.inverse ≪≫
    Functor.isoWhiskerRight G.leftUnitor ED.inverse

/--
Transport a commuting square of endofunctors across equivalences of the
source and target categories.
-/
noncomputable def conjugatedEndofunctorNaturality
    {C : Type u₁} [Category.{v₁} C]
    {C' : Type u₂} [Category.{v₂} C']
    {D : Type u₃} [Category.{v₃} D]
    {D' : Type u₄} [Category.{v₄} D']
    (EC : C ≌ C') (ED : D ≌ D')
    (F : C ⥤ D) (G : C' ⥤ D')
    (A : C' ⥤ C') (B : D' ⥤ D')
    (hleft : EC.inverse ⋙ F ≅ G ⋙ ED.inverse)
    (hright : F ⋙ ED.functor ≅ EC.functor ⋙ G)
    (hmiddle : A ⋙ G ≅ G ⋙ B) :
    ((EC.functor ⋙ A) ⋙ EC.inverse) ⋙ F ≅
      F ⋙ ((ED.functor ⋙ B) ⋙ ED.inverse) :=
  Functor.associator
      (EC.functor ⋙ A) EC.inverse F ≪≫
    Functor.isoWhiskerLeft
      (EC.functor ⋙ A) hleft ≪≫
    (Functor.associator
      (EC.functor ⋙ A) G ED.inverse).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.associator EC.functor A G)
      ED.inverse ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft EC.functor hmiddle)
      ED.inverse ≪≫
    Functor.isoWhiskerRight
      (Functor.associator EC.functor G B).symm
      ED.inverse ≪≫
    Functor.associator
      (EC.functor ⋙ G) B ED.inverse ≪≫
    Functor.isoWhiskerRight
      hright.symm (B ⋙ ED.inverse) ≪≫
    Functor.associator
      F ED.functor (B ⋙ ED.inverse) ≪≫
    Functor.isoWhiskerLeft F
      (Functor.associator
        ED.functor B ED.inverse).symm

/--
Forward-square version of
`conjugatedEndofunctorNaturality`.
-/
noncomputable def conjugatedEndofunctorNaturalityOfForward
    {C : Type u₁} [Category.{v₁} C]
    {C' : Type u₂} [Category.{v₂} C']
    {D : Type u₃} [Category.{v₃} D]
    {D' : Type u₄} [Category.{v₄} D']
    (EC : C ≌ C') (ED : D ≌ D')
    (F : C ⥤ D) (G : C' ⥤ D')
    (A : C' ⥤ C') (B : D' ⥤ D')
    (hforward :
      F ⋙ ED.functor ≅ EC.functor ⋙ G)
    (hmiddle : A ⋙ G ≅ G ⋙ B) :
    ((EC.functor ⋙ A) ⋙ EC.inverse) ⋙ F ≅
      F ⋙ ((ED.functor ⋙ B) ⋙ ED.inverse) :=
  conjugatedEndofunctorNaturality
    EC ED F G A B
    (equivalenceInverseNaturalityIso
      EC ED F G hforward)
    hforward hmiddle

/--
Transport a commuting square of autoequivalences across equivalences of
the source and target categories.

The two outer isomorphisms identify a functor `F` with a functor `G` after
changing coordinates by `EC` and `ED`.  The middle isomorphism says that
`G` commutes with the autoequivalences before transport.
-/
noncomputable def conjugatedAutoequivalenceNaturality
    {C : Type u₁} [Category.{v₁} C]
    {C' : Type u₂} [Category.{v₂} C']
    {D : Type u₃} [Category.{v₃} D]
    {D' : Type u₄} [Category.{v₄} D']
    (EC : C ≌ C') (ED : D ≌ D')
    (F : C ⥤ D) (G : C' ⥤ D')
    (A : C' ≌ C') (B : D' ≌ D')
    (hleft : EC.inverse ⋙ F ≅ G ⋙ ED.inverse)
    (hright : F ⋙ ED.functor ≅ EC.functor ⋙ G)
    (hmiddle : A.functor ⋙ G ≅ G ⋙ B.functor) :
    ((EC.functor ⋙ A.functor) ⋙ EC.inverse) ⋙ F ≅
      F ⋙ ((ED.functor ⋙ B.functor) ⋙ ED.inverse) :=
  Functor.associator
      (EC.functor ⋙ A.functor) EC.inverse F ≪≫
    Functor.isoWhiskerLeft
      (EC.functor ⋙ A.functor) hleft ≪≫
    (Functor.associator
      (EC.functor ⋙ A.functor) G ED.inverse).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.associator EC.functor A.functor G)
      ED.inverse ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft EC.functor hmiddle)
      ED.inverse ≪≫
    Functor.isoWhiskerRight
      (Functor.associator EC.functor G B.functor).symm
      ED.inverse ≪≫
    Functor.associator
      (EC.functor ⋙ G) B.functor ED.inverse ≪≫
    Functor.isoWhiskerRight
      hright.symm (B.functor ⋙ ED.inverse) ≪≫
    Functor.associator
      F ED.functor (B.functor ⋙ ED.inverse) ≪≫
    Functor.isoWhiskerLeft F
      (Functor.associator
        ED.functor B.functor ED.inverse).symm

/--
Version of `conjugatedAutoequivalenceNaturality` in which only the
forward-coordinate naturality square is supplied.
-/
noncomputable def conjugatedAutoequivalenceNaturalityOfForward
    {C : Type u₁} [Category.{v₁} C]
    {C' : Type u₂} [Category.{v₂} C']
    {D : Type u₃} [Category.{v₃} D]
    {D' : Type u₄} [Category.{v₄} D']
    (EC : C ≌ C') (ED : D ≌ D')
    (F : C ⥤ D) (G : C' ⥤ D')
    (A : C' ≌ C') (B : D' ≌ D')
    (hforward :
      F ⋙ ED.functor ≅ EC.functor ⋙ G)
    (hmiddle : A.functor ⋙ G ≅ G ⋙ B.functor) :
    ((EC.functor ⋙ A.functor) ⋙ EC.inverse) ⋙ F ≅
      F ⋙ ((ED.functor ⋙ B.functor) ⋙ ED.inverse) :=
  conjugatedAutoequivalenceNaturality
    EC ED F G A B
    (equivalenceInverseNaturalityIso
      EC ED F G hforward)
    hforward hmiddle

end CategoryTheory
