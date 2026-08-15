/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.CoefficientRationalization
import MazurTorsion.Upstream.CoherentCohomologyFinite.ExtAdjunction
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
import Mathlib.Algebra.Module.LinearMap.Rat
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib

/-!
# Change of scalars for sheaf Ext

Infrastructure for comparing `Ext` in sheaves of rational vector spaces with
`Ext` in sheaves of abelian groups.
-/

open CategoryTheory Limits

universe uA uB

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ExtChangeOfScalars

noncomputable def ratLinearEquivOfAddEquiv
    {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module ℚ V] [Module ℚ W] (e : V ≃+ W) :
    V ≃ₗ[ℚ] W where
  toAddEquiv := e
  map_smul' q x := map_rat_smul e.toAddMonoidHom q x

noncomputable abbrev restrictQToZ : ModuleCat.{0} ℚ ⥤ ModuleCat.{0} ℤ :=
  ModuleCat.restrictScalars (algebraMap ℤ ℚ)

noncomputable local instance restrictQToZ_full : restrictQToZ.Full where
  map_surjective {_ _} f :=
    ⟨ModuleCat.ofHom
      { toFun := f
        map_add' := f.hom.map_add
        map_smul' := fun q x => map_rat_smul f.hom q x },
      rfl⟩

variable {C : Type} [SmallCategory C] (J : GrothendieckTopology C)

noncomputable def sheafComposeAdjunction
    {A : Type uA} {B : Type uB} [Category A] [Category B]
    {L : A ⥤ B} {R : B ⥤ A}
    [J.HasSheafCompose L] [J.HasSheafCompose R]
    (adj : L ⊣ R) :
    sheafCompose J L ⊣ sheafCompose J R :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨(adj.whiskerRight Cᵒᵖ).homEquiv X.obj Y.obj f.hom⟩
          invFun := fun f => ⟨((adj.whiskerRight Cᵒᵖ).homEquiv X.obj Y.obj).symm f.hom⟩
          left_inv := fun f => Sheaf.hom_ext <|
            ((adj.whiskerRight Cᵒᵖ).homEquiv X.obj Y.obj).left_inv f.hom
          right_inv := fun f => Sheaf.hom_ext <|
            ((adj.whiskerRight Cᵒᵖ).homEquiv X.obj Y.obj).right_inv f.hom }
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        apply Sheaf.hom_ext
        exact (adj.whiskerRight Cᵒᵖ).homEquiv_naturality_left_symm f.hom g.hom
      homEquiv_naturality_right := by
        intro X Y Y' f g
        apply Sheaf.hom_ext
        exact (adj.whiskerRight Cᵒᵖ).homEquiv_naturality_right f.hom g.hom }

noncomputable abbrev sheafRestrictQToZ :
    Sheaf J (ModuleCat.{0} ℚ) ⥤ Sheaf J (ModuleCat.{0} ℤ) :=
  sheafCompose J restrictQToZ

noncomputable abbrev extendZToQ : ModuleCat.{0} ℤ ⥤ ModuleCat.{0} ℚ :=
  ModuleCat.extendScalars (algebraMap ℤ ℚ)

noncomputable abbrev coextendZToQ : ModuleCat.{0} ℤ ⥤ ModuleCat.{0} ℚ :=
  ModuleCat.coextendScalars (algebraMap ℤ ℚ)

noncomputable abbrev forgetZToAb :
    ModuleCat.{0} ℤ ⥤ AddCommGrpCat.{0} :=
  forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0}

noncomputable abbrev liftAbToZ :
    AddCommGrpCat.{0} ⥤ ModuleCat.{0} ℤ :=
  forgetZToAb.inv

noncomputable local instance extendZToQ_preservesFiniteLimits :
    PreservesFiniteLimits extendZToQ :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat <|
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat ℚ (Submonoid.pos ℤ))

noncomputable abbrev sheafExtendZToQ :
    Sheaf J (ModuleCat.{0} ℤ) ⥤ Sheaf J (ModuleCat.{0} ℚ) :=
  Sheaf.composeAndSheafify J extendZToQ

noncomputable abbrev sheafCoextendZToQ :
    Sheaf J (ModuleCat.{0} ℤ) ⥤ Sheaf J (ModuleCat.{0} ℚ) :=
  sheafCompose J coextendZToQ

noncomputable abbrev sheafForgetZToAb :
    Sheaf J (ModuleCat.{0} ℤ) ⥤ Sheaf J AddCommGrpCat.{0} :=
  sheafCompose J forgetZToAb

noncomputable abbrev sheafLiftAbToZ :
    Sheaf J AddCommGrpCat.{0} ⥤ Sheaf J (ModuleCat.{0} ℤ) :=
  sheafCompose J liftAbToZ

noncomputable def sheafExtendRestrictAdjunction :
    sheafExtendZToQ J ⊣ sheafRestrictQToZ J :=
  Sheaf.adjunction J
    (ModuleCat.extendRestrictScalarsAdj (algebraMap ℤ ℚ))

noncomputable def sheafRestrictCoextendAdjunction :
    sheafRestrictQToZ J ⊣ sheafCoextendZToQ J :=
  sheafComposeAdjunction J
    (ModuleCat.restrictCoextendScalarsAdj (algebraMap ℤ ℚ))

noncomputable def sheafForgetLiftAdjunction :
    sheafForgetZToAb J ⊣ sheafLiftAbToZ J :=
  sheafComposeAdjunction J forgetZToAb.asEquivalence.toAdjunction

noncomputable def sheafLiftForgetAdjunction :
    sheafLiftAbToZ J ⊣ sheafForgetZToAb J :=
  sheafComposeAdjunction J forgetZToAb.asEquivalence.symm.toAdjunction

noncomputable def constantSheafExtendIso {T : C} (hT : IsTerminal T) :
    constantSheaf J (ModuleCat.{0} ℤ) ⋙ sheafExtendZToQ J ≅
      extendZToQ ⋙ constantSheaf J (ModuleCat.{0} ℚ) :=
  ((constantSheafAdj J (ModuleCat.{0} ℤ) hT).comp
      (sheafExtendRestrictAdjunction J)).leftAdjointUniq
    ((ModuleCat.extendRestrictScalarsAdj (algebraMap ℤ ℚ)).comp
      (constantSheafAdj J (ModuleCat.{0} ℚ) hT))

noncomputable def constantZExtendIso {T : C} (hT : IsTerminal T) :
    (sheafExtendZToQ J).obj
        ((constantSheaf J (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)) ≅
      (constantSheaf J (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ) :=
    (constantSheafExtendIso J hT).app (ModuleCat.of ℤ ℤ) ≪≫
    (constantSheaf J (ModuleCat.{0} ℚ)).mapIso
      (TensorProduct.AlgebraTensorModule.rid ℤ ℚ ℚ).toModuleIso

noncomputable def constantZForgetIso :
    (sheafForgetZToAb J).obj
        ((constantSheaf J (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)) ≅
      (constantSheaf J AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ) :=
  (constantCommuteCompose J forgetZToAb).app (ModuleCat.of ℤ ℤ)

noncomputable def constantAbZULiftIso :
    (constantSheaf J AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ) ≅
      (constantSheaf J AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift ℤ)) :=
  (constantSheaf J AddCommGrpCat.{0}).mapIso
    AddEquiv.ulift.symm.toAddCommGrpIso

noncomputable def sheafRestrictForgetIso :
    sheafRestrictQToZ J ⋙ sheafForgetZToAb J ≅
      CoefficientRationalization.UAb J :=
  Iso.refl _

noncomputable local instance sheafRestrictQToZ_isRightAdjoint :
    (sheafRestrictQToZ J).IsRightAdjoint :=
  (sheafExtendRestrictAdjunction J).isRightAdjoint

noncomputable local instance sheafRestrictQToZ_isLeftAdjoint :
    (sheafRestrictQToZ J).IsLeftAdjoint :=
  (sheafRestrictCoextendAdjunction J).isLeftAdjoint

noncomputable local instance sheafRestrictQToZ_additive :
    (sheafRestrictQToZ J).Additive :=
  (sheafRestrictQToZ J).additive_of_preserves_binary_products

noncomputable local instance sheafForgetZToAb_isRightAdjoint :
    (sheafForgetZToAb J).IsRightAdjoint :=
  (sheafLiftForgetAdjunction J).isRightAdjoint

noncomputable local instance sheafForgetZToAb_isLeftAdjoint :
    (sheafForgetZToAb J).IsLeftAdjoint :=
  (sheafForgetLiftAdjunction J).isLeftAdjoint

noncomputable local instance sheafLiftAbToZ_isRightAdjoint :
    (sheafLiftAbToZ J).IsRightAdjoint :=
  (sheafForgetLiftAdjunction J).isRightAdjoint

noncomputable local instance sheafForgetZToAb_additive :
    (sheafForgetZToAb J).Additive :=
  (sheafForgetZToAb J).additive_of_preserves_binary_products

noncomputable local instance sheafForgetZToAb_preservesInjectiveObjects :
    (sheafForgetZToAb J).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (sheafLiftForgetAdjunction J)

noncomputable local instance sheafRestrictQToZ_preservesInjectiveObjects :
    (sheafRestrictQToZ J).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (sheafExtendRestrictAdjunction J)

section MapExt

variable [HasExt.{0} (Sheaf J (ModuleCat.{0} ℚ))]
  [HasExt.{0} (Sheaf J (ModuleCat.{0} ℤ))]

theorem sheafRestrictQToZ_mapExt_bijective
    (A B : Sheaf J (ModuleCat.{0} ℚ)) (n : ℕ) :
    Function.Bijective ((sheafRestrictQToZ J).mapExtAddHom A B n) :=
  Functor.mapExt_bijective_of_preservesInjectiveObjects
    (sheafRestrictQToZ J) A B n

noncomputable def sheafRestrictQToZ_extAddEquiv
    (A B : Sheaf J (ModuleCat.{0} ℚ)) (n : ℕ) :
    Abelian.Ext A B n ≃+
      Abelian.Ext ((sheafRestrictQToZ J).obj A) ((sheafRestrictQToZ J).obj B) n :=
  AddEquiv.ofBijective
    ((sheafRestrictQToZ J).mapExtAddHom A B n)
    (sheafRestrictQToZ_mapExt_bijective J A B n)

noncomputable def constantSheafExtAddEquiv {T : C} (hT : IsTerminal T)
    (F : Sheaf J (ModuleCat.{0} ℚ)) (n : ℕ) :
    Abelian.Ext
        ((constantSheaf J (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)) F n ≃+
      Abelian.Ext
        ((constantSheaf J (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ))
        ((sheafRestrictQToZ J).obj F) n :=
  (ExtAdjunction.precompIsoAddEquiv (constantZExtendIso J hT) n).trans
    (ExtAdjunction.extAddEquiv
      (sheafExtendZToQ J) (sheafRestrictQToZ J)
      (sheafExtendRestrictAdjunction J)
      ((constantSheaf J (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)) F n)

end MapExt

section AbelianCarrier

variable [HasExt.{0} (Sheaf J (ModuleCat.{0} ℤ))]
  [HasExt.{0} (Sheaf J AddCommGrpCat.{0})]

theorem sheafForgetZToAb_mapExt_bijective
    (A B : Sheaf J (ModuleCat.{0} ℤ)) (n : ℕ) :
    Function.Bijective ((sheafForgetZToAb J).mapExtAddHom A B n) :=
  Functor.mapExt_bijective_of_preservesInjectiveObjects
    (sheafForgetZToAb J) A B n

noncomputable def sheafForgetZToAb_extAddEquiv
    (A B : Sheaf J (ModuleCat.{0} ℤ)) (n : ℕ) :
    Abelian.Ext A B n ≃+
      Abelian.Ext ((sheafForgetZToAb J).obj A) ((sheafForgetZToAb J).obj B) n :=
  AddEquiv.ofBijective
    ((sheafForgetZToAb J).mapExtAddHom A B n)
    (sheafForgetZToAb_mapExt_bijective J A B n)

variable [HasExt.{0} (Sheaf J (ModuleCat.{0} ℚ))]

/--
The carrier comparison needed by the LeanEval problem: Ext from the
constant rational sheaf is the same as Ext from the constant abelian
sheaf `ℤ` after forgetting rational scalar multiplication.
-/
noncomputable def constantSheafExtAbAddEquiv {T : C} (hT : IsTerminal T)
    (F : Sheaf J (ModuleCat.{0} ℚ)) (n : ℕ) :
    Abelian.Ext
        ((constantSheaf J (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)) F n ≃+
      Abelian.Ext
        ((constantSheaf J AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift ℤ)))
        ((CoefficientRationalization.UAb J).obj F) n :=
  (constantSheafExtAddEquiv J hT F n).trans <|
    (sheafForgetZToAb_extAddEquiv J
      ((constantSheaf J (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ))
      ((sheafRestrictQToZ J).obj F) n).trans <|
      (ExtAdjunction.precompIsoAddEquiv
        (constantZForgetIso J)
        n).symm |>.trans <|
        ExtAdjunction.postcompIsoAddEquiv
          ((sheafRestrictForgetIso J).app F) n |>.trans <|
          (ExtAdjunction.precompIsoAddEquiv (constantAbZULiftIso J) n).symm

noncomputable def constantSheafExtAbLinearEquiv {T : C} (hT : IsTerminal T)
    (F : Sheaf J (ModuleCat.{0} ℚ)) (n : ℕ) :
    letI := CoefficientRationalization.rationalExtModule
      (X := (constantSheaf J AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift ℤ))) J F n
    Abelian.Ext
        ((constantSheaf J (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)) F n ≃ₗ[ℚ]
      Abelian.Ext
        ((constantSheaf J AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift ℤ)))
        ((CoefficientRationalization.UAb J).obj F) n := by
  letI := CoefficientRationalization.rationalExtModule
    (X := (constantSheaf J AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift ℤ))) J F n
  exact ratLinearEquivOfAddEquiv (constantSheafExtAbAddEquiv J hT F n)

theorem constantSheafExtAb_moduleFinite {T : C} (hT : IsTerminal T)
    (F : Sheaf J (ModuleCat.{0} ℚ)) (n : ℕ)
    [Module.Finite ℚ
      (Abelian.Ext
        ((constantSheaf J (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)) F n)] :
    letI := CoefficientRationalization.rationalExtModule
      (X := (constantSheaf J AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift ℤ))) J F n
    Module.Finite ℚ
      (Abelian.Ext
        ((constantSheaf J AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift ℤ)))
        ((CoefficientRationalization.UAb J).obj F) n) := by
  letI := CoefficientRationalization.rationalExtModule
    (X := (constantSheaf J AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift ℤ))) J F n
  exact Module.Finite.equiv (constantSheafExtAbLinearEquiv J hT F n)

end AbelianCarrier

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ExtChangeOfScalars
