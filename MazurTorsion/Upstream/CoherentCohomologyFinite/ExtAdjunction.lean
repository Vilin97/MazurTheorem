/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective

/-!
# Ext and an exact right adjoint

An adjunction `L ⊣ U` induces the usual change-of-rings comparison

`Ext (L X) Y ⟶ Ext X (U Y)`.

When the right adjoint is exact and preserves injective objects, this
comparison is an isomorphism in every degree.
-/

open CategoryTheory Limits

universe w w' v v' u u'

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ExtAdjunction

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (L : C ⥤ D) (U : D ⥤ C) (adj : L ⊣ U)
  [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [HasExt.{w} C] [HasExt.{w'} D]

noncomputable def precompIsoAddEquiv {X Y Z : C} (e : X ≅ Y) (n : ℕ) :
    Abelian.Ext Y Z n ≃+ Abelian.Ext X Z n where
  toFun := (Abelian.Ext.mk₀ e.hom).precomp Z (zero_add n)
  invFun := (Abelian.Ext.mk₀ e.inv).precomp Z (zero_add n)
  map_add' := map_add _
  left_inv x := by
    change (Abelian.Ext.mk₀ e.inv).comp
      ((Abelian.Ext.mk₀ e.hom).comp x (zero_add n)) (zero_add n) = x
    rw [Abelian.Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Abelian.Ext.mk₀_id_comp]
  right_inv x := by
    change (Abelian.Ext.mk₀ e.hom).comp
      ((Abelian.Ext.mk₀ e.inv).comp x (zero_add n)) (zero_add n) = x
    rw [Abelian.Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Abelian.Ext.mk₀_id_comp]

noncomputable def postcompIsoAddEquiv {X Y Z : C} (e : Y ≅ Z) (n : ℕ) :
    Abelian.Ext X Y n ≃+ Abelian.Ext X Z n where
  toFun := (Abelian.Ext.mk₀ e.hom).postcomp X (add_zero n)
  invFun := (Abelian.Ext.mk₀ e.inv).postcomp X (add_zero n)
  map_add' := map_add _
  left_inv x := by
    change (x.comp (Abelian.Ext.mk₀ e.hom) (add_zero n)).comp
      (Abelian.Ext.mk₀ e.inv) (add_zero n) = x
    rw [Abelian.Ext.comp_assoc_of_third_deg_zero,
      Abelian.Ext.mk₀_comp_mk₀, e.hom_inv_id, Abelian.Ext.comp_mk₀_id]
  right_inv x := by
    change (x.comp (Abelian.Ext.mk₀ e.inv) (add_zero n)).comp
      (Abelian.Ext.mk₀ e.hom) (add_zero n) = x
    rw [Abelian.Ext.comp_assoc_of_third_deg_zero,
      Abelian.Ext.mk₀_comp_mk₀, e.inv_hom_id, Abelian.Ext.comp_mk₀_id]

private def unitApp (X : C) : X ⟶ U.obj (L.obj X) :=
  adj.unit.app X

/--
The comparison from `Ext (L X) Y` to `Ext X (U Y)` induced by an
adjunction and an exact right adjoint.
-/
noncomputable def extAddHom (X : C) (Y : D) (n : ℕ) :
    Abelian.Ext (L.obj X) Y n →+ Abelian.Ext X (U.obj Y) n :=
  ((Abelian.Ext.mk₀
      (unitApp L U adj X)).precomp
        (U.obj Y) (zero_add n)).comp
    (U.mapExtAddHom (L.obj X) Y n)

@[simp]
lemma extAddHom_mk₀ (X : C) {Y : D} (f : L.obj X ⟶ Y) :
    extAddHom L U adj X Y 0 (Abelian.Ext.mk₀ f) =
      Abelian.Ext.mk₀ ((adj.homEquiv X Y) f) := by
  change (Abelian.Ext.mk₀ (unitApp L U adj X)).comp
      ((Abelian.Ext.mk₀ f).mapExactFunctor U) (zero_add 0) =
    Abelian.Ext.mk₀ ((adj.homEquiv X Y) f)
  rw [Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀,
    Adjunction.homEquiv_unit]
  rfl

lemma extAddHom_zero_bijective (X : C) (Y : D) :
    Function.Bijective (extAddHom L U adj X Y 0) := by
  constructor
  · intro a b h
    obtain ⟨f, rfl⟩ := (Abelian.Ext.mk₀_bijective (L.obj X) Y).2 a
    obtain ⟨g, rfl⟩ := (Abelian.Ext.mk₀_bijective (L.obj X) Y).2 b
    rw [extAddHom_mk₀, extAddHom_mk₀] at h
    exact congrArg (fun k : L.obj X ⟶ Y => Abelian.Ext.mk₀ k) <|
      (adj.homEquiv X Y).injective
        ((Abelian.Ext.mk₀_bijective X (U.obj Y)).1 h)
  · intro a
    obtain ⟨f, rfl⟩ := (Abelian.Ext.mk₀_bijective X (U.obj Y)).2 a
    exact ⟨Abelian.Ext.mk₀ ((adj.homEquiv X Y).symm f), by
      rw [extAddHom_mk₀, Equiv.apply_symm_apply]⟩

lemma extAddHom_naturality (X : C) {Y Z : D} (f : Y ⟶ Z) (n : ℕ) :
    ((Abelian.Ext.mk₀ (U.map f)).postcomp X (add_zero n)).comp
        (extAddHom L U adj X Y n) =
      (extAddHom L U adj X Z n).comp
        ((Abelian.Ext.mk₀ f).postcomp (L.obj X) (add_zero n)) := by
  ext e
  change ((Abelian.Ext.mk₀ (unitApp L U adj X)).comp
      (e.mapExactFunctor U) (zero_add n)).comp
        (Abelian.Ext.mk₀ (U.map f)) (add_zero n) =
    (Abelian.Ext.mk₀ (unitApp L U adj X)).comp
      ((e.comp (Abelian.Ext.mk₀ f) (add_zero n)).mapExactFunctor U) (zero_add n)
  rw [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀]
  exact Abelian.Ext.comp_assoc_of_third_deg_zero _ _ _ (zero_add n)

lemma extAddHom_extClass (X : C) {S : ShortComplex D}
    (hS : S.ShortExact) (n : ℕ) :
    ((hS.extClass.mapExactFunctor U).postcomp X rfl).comp
        (extAddHom L U adj X S.X₃ n) =
      (extAddHom L U adj X S.X₁ (n + 1)).comp
        (hS.extClass.postcomp (L.obj X) rfl) := by
  ext e
  change ((Abelian.Ext.mk₀ (unitApp L U adj X)).comp
      (e.mapExactFunctor U) (zero_add n)).comp
        (hS.extClass.mapExactFunctor U) rfl =
    (Abelian.Ext.mk₀ (unitApp L U adj X)).comp
      ((e.comp hS.extClass rfl).mapExactFunctor U) (zero_add (n + 1))
  rw [Abelian.Ext.mapExactFunctor_comp]
  exact Abelian.Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)

attribute [local instance] Abelian.Ext.subsingleton_of_injective in
/--
The Ext comparison for an exact right adjoint which preserves injectives is
bijective in every degree.
-/
theorem extAddHom_bijective [EnoughInjectives D] [U.PreservesInjectiveObjects]
    (X : C) (Y : D) (n : ℕ) :
    Function.Bijective (extAddHom L U adj X Y n) := by
  induction n generalizing Y with
  | zero => exact extAddHom_zero_bijective L U adj X Y
  | succ n hn =>
    let I : InjectivePresentation Y := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have : Injective (S.map U).X₂ :=
      Functor.PreservesInjectiveObjects.injective_obj I.injective
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (extAddHom L U adj X S.X₂ n)
      (extAddHom L U adj X S.X₃ n)
      (extAddHom L U adj X S.X₁ (n + 1))
      (by
        dsimp
        exact extAddHom_naturality L U adj X S.g n)
      (by
        dsimp
        rw [← Abelian.Ext.mapExactFunctor_extClass (F := U) hS]
        exact extAddHom_extClass L U adj X hS n)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Abelian.Ext.covariant_sequence_exact₃' (L.obj X) hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Abelian.Ext.covariant_sequence_exact₃' X (hS.map U) n (n + 1) rfl))
      (hn _).surjective (hn _)
      (fun x₁ ↦ Abelian.Ext.covariant_sequence_exact₁ _ hS x₁ (by subsingleton) rfl)
      (fun y₁ ↦
        Abelian.Ext.covariant_sequence_exact₁ _ (hS.map U) y₁ (by subsingleton) rfl)

noncomputable def extAddEquiv [EnoughInjectives D] [U.PreservesInjectiveObjects]
    (X : C) (Y : D) (n : ℕ) :
    Abelian.Ext (L.obj X) Y n ≃+ Abelian.Ext X (U.obj Y) n :=
  AddEquiv.ofBijective (extAddHom L U adj X Y n)
    (extAddHom_bijective L U adj X Y n)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ExtAdjunction
