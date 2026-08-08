/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Additivity of formal coproduct evaluation

The extension of a presheaf to formal coproducts by products is additive when its target is
preadditive.
-/

open CategoryTheory Opposite

universe v w v' u u'

namespace CategoryTheory.Limits.FormalCoproduct

noncomputable section

instance evalOp_additive
    {C : Type u} [Category.{v} C]
    {A : Type u'} [Category.{v'} A] [Preadditive A]
    [HasProducts.{w} A] :
    (evalOp.{w} C A).Additive where
  map_add := by
    intro F G α β
    apply NatTrans.ext
    funext Z
    change Pi.map (fun i : Z.unop.I ↦
        (α + β).app (op (Z.unop.obj i))) =
      Pi.map (fun i : Z.unop.I ↦ α.app (op (Z.unop.obj i))) +
        Pi.map (fun i : Z.unop.I ↦ β.app (op (Z.unop.obj i)))
    apply Pi.hom_ext
    intro i
    rw [Pi.map_π, Preadditive.add_comp, Pi.map_π, Pi.map_π]
    exact Preadditive.comp_add
      (∏ᶜ fun i : Z.unop.I ↦ F.obj (op (Z.unop.obj i)))
      (F.obj (op (Z.unop.obj i))) (G.obj (op (Z.unop.obj i)))
      (Pi.π (fun i : Z.unop.I ↦ F.obj (op (Z.unop.obj i))) i)
      (α.app (op (Z.unop.obj i))) (β.app (op (Z.unop.obj i)))

end

end CategoryTheory.Limits.FormalCoproduct
