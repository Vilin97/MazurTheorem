/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Locality and isomorphism invariance of finite type

Mathlib defines finite type for a sheaf of modules by finite local
generating families.  This file records two formal consequences of that
definition: invariance under isomorphism and descent along a cover of the
terminal object.
-/


open CategoryTheory Limits

noncomputable section

universe u

namespace SheafOfModules

variable {C : Type u} [Category.{u} C]
  {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, (J.over X).HasSheafCompose
    (forget₂ RingCat.{u} AddCommGrpCat.{u})]

/-- Transport local generating data across an isomorphism. -/
noncomputable def LocalGeneratorsData.ofIso
    {M N : SheafOfModules.{u} R} (e : M ≅ N)
    (P : LocalGeneratorsData.{u} M) :
    LocalGeneratorsData.{u} N where
  I := P.I
  X := P.X
  coversTop := P.coversTop
  generators i :=
    (GeneratingSections.equivOfIso
      ((overFunctor R (P.X i)).mapIso e))
      (P.generators i)

/-- Finiteness of local generating data survives transport by an
isomorphism. -/
instance LocalGeneratorsData.ofIso_isFiniteType
    {M N : SheafOfModules.{u} R} (e : M ≅ N)
    (P : LocalGeneratorsData.{u} M) [P.IsFiniteType] :
    (P.ofIso e).IsFiniteType where
  isFiniteType i := by
    letI : (P.generators i).IsFiniteType :=
      LocalGeneratorsData.IsFiniteType.isFiniteType _
    change
      ((P.generators i).ofEpi
        (((overFunctor R (P.X i)).mapIso e).hom)).IsFiniteType
    infer_instance

/-- Finite type is invariant under isomorphism. -/
theorem isFiniteType_of_iso
    {M N : SheafOfModules.{u} R} (e : M ≅ N)
    [M.IsFiniteType] :
    N.IsFiniteType := by
  obtain ⟨P, hP⟩ :=
    IsFiniteType.exists_localGeneratorsData M
  letI : P.IsFiniteType := hP
  exact ⟨P.ofIso e, inferInstance⟩

section Bind

variable
  [∀ X Y, HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ X Y,
    ((J.over X).over Y).WEqualsLocallyBijective
      AddCommGrpCat.{u}]
  [∀ X Y,
    ((J.over X).over Y).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u})]

/--
Flatten finite local generating data on a cover into finite local
generating data on the ambient site.
-/
noncomputable def LocalGeneratorsData.bind
    (M : SheafOfModules.{u} R)
    {I : Type u} (X : I → C) (hX : J.CoversTop X)
    (D : ∀ i, LocalGeneratorsData.{u} (M.over (X i))) :
    LocalGeneratorsData.{u} M where
  I := (i : I) × (D i).I
  X ij := ((D ij.1).X ij.2).left
  coversTop := hX.over (fun i => (D i).coversTop)
  generators ij := by
    let e :=
      pushforwardPushforwardEquivalence
        (Over.iteratedSliceEquiv ((D ij.1).X ij.2))
        (S := (R.over _).over _)
        (R := R.over _)
        (𝟙 _) (𝟙 _)
        (by ext : 2; exact R.1.map_id _)
        (by ext : 2; exact R.1.map_id _)
    let G :=
      ((D ij.1).generators ij.2).map
        e.inverse (Iso.refl _)
    exact G.ofEpi
      (e.fullyFaithfulFunctor.preimageIso
        (by
          exact e.counitIso.app
            ((M.over (X ij.1)).over
              ((D ij.1).X ij.2)))).hom

/-- The flattened local generating data is finite when every local piece
is finite. -/
instance LocalGeneratorsData.bind_isFiniteType
    (M : SheafOfModules.{u} R)
    {I : Type u} (X : I → C) (hX : J.CoversTop X)
    (D : ∀ i, LocalGeneratorsData.{u} (M.over (X i)))
    [∀ i, (D i).IsFiniteType] :
    (LocalGeneratorsData.bind M X hX D).IsFiniteType where
  isFiniteType ij := by
    letI :
        HasWeakSheafify
          (J.over ((D ij.1).X ij.2).left)
          AddCommGrpCat.{u} :=
      HasSheafify.isRightAdjoint
    letI :
        ((D ij.1).generators ij.2).IsFiniteType :=
      LocalGeneratorsData.IsFiniteType.isFiniteType _
    dsimp only [LocalGeneratorsData.bind]
    exact
      @GeneratingSections.IsFiniteType.mk.{u, u, u}
        (C := Over ((D ij.1).X ij.2).left)
        (J := J.over ((D ij.1).X ij.2).left)
        (R := R.over ((D ij.1).X ij.2).left)
        (M := _) (σ := _)
        (finite :=
          GeneratingSections.IsFiniteType.finite
            (σ := (D ij.1).generators ij.2))

/-- Finite type may be checked on a cover of the terminal object. -/
theorem IsFiniteType.of_coversTop
    (M : SheafOfModules.{u} R)
    {I : Type u} (X : I → C) (hX : J.CoversTop X)
    [∀ i, IsFiniteType (M.over (X i))] :
    IsFiniteType M := by
  let D : ∀ i, LocalGeneratorsData.{u} (M.over (X i)) :=
    fun i =>
      (IsFiniteType.exists_localGeneratorsData
        (M.over (X i))).choose
  letI : ∀ i, (D i).IsFiniteType :=
    fun i =>
      (IsFiniteType.exists_localGeneratorsData
        (M.over (X i))).choose_spec
  exact
    ⟨LocalGeneratorsData.bind M X hX D,
      inferInstance⟩

end Bind

end SheafOfModules
