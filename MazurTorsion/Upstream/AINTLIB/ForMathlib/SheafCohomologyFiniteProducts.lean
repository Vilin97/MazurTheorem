/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SheafCechSheafResolution
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SheafCohomologyCompat

/-!
# Sheaf cohomology of finite products

This file identifies genuine sheaf cohomology of a finite product with the product of
the cohomology groups, then applies the result to the finite products occurring in the
sheaf-level Cech resolution.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace CategoryTheory.Sheaf.H

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]

/-- Genuine sheaf cohomology commutes with finite products. -/
private noncomputable def addEquivPi {ι : Type u} [Finite ι]
    (F : ι → Sheaf J AddCommGrpCat.{u}) (n : ℕ) :
    H (∏ᶜ F) n ≃+ ∀ i, H (F i) n := by
  letI := Fintype.ofFinite ι
  let e : Discrete.functor F ⋙ functorH J n ≅
      Discrete.functor (fun i => (functorH J n).obj (F i)) :=
    Discrete.natIso fun _ => Iso.refl _
  exact ((preservesLimitIso (functorH J n) (Discrete.functor F)) ≪≫
    HasLimit.isoOfNatIso e ≪≫
      AddCommGrpCat.productIsoPi
        (fun i => (functorH J n).obj (F i))).addCommGroupIsoToAddEquiv

/-- A finite product of sheaves has subsingleton cohomology when each factor does. -/
private theorem subsingleton_product_of_factors {ι : Type u} [Finite ι]
    (F : ι → Sheaf J AddCommGrpCat.{u}) (n : ℕ)
    (h : ∀ i, Subsingleton (H (F i) n)) : Subsingleton (H (∏ᶜ F) n) := by
  letI (i : ι) : Subsingleton (H (F i) n) := h i
  let e := addEquivPi F n
  exact ⟨fun x y => e.injective (funext fun i => Subsingleton.elim (e x i) (e y i))⟩

end CategoryTheory.Sheaf.H

namespace TopCat.Sheaf

variable {X : TopCat.{u}}
variable (F : Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} (U : ι → Opens X)

/-- A finite Cech term has vanishing cohomology in a degree whenever all of its
restriction-pushforward factors do. -/
theorem cechTerm_subsingleton_H_of_factors [Finite ι] (n q : ℕ)
    (h : ∀ i : Fin (n + 1) → ι,
      Subsingleton (H (cechTermFactor F U n i) q)) :
    Subsingleton (H (cechTerm F U n) q) := by
  exact CategoryTheory.Sheaf.H.subsingleton_product_of_factors
    (cechTermFactor F U n) q h

end TopCat.Sheaf
