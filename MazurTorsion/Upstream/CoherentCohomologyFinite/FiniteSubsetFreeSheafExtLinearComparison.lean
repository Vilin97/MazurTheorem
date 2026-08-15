/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteSubsetFreeSheafExtAcyclic
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteSubsetFreeSheafHomComparison

/-!
# Linearizing the finite-subset free-sheaf Ext comparison

The source-resolution Ext comparison naturally produces a cochain
complex in abelian groups.  The explicit finite-subset Hom complex is
instead defined in modules over the coefficient ring.  This file
identifies the former with the underlying abelian-group complex of the
latter, including their homology objects.
-/

open CategoryTheory TopologicalSpace


noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {R : Type u} [CommRing R]
variable {T : TopCat.{u}}
variable {ι : Type u} [Fintype ι] [LinearOrder ι]

/-- The categorical contravariant Hom complex is the underlying
abelian-group complex of the explicit coefficient-linear Hom complex. -/
noncomputable def categoricalContravariantHomCocomplexIsoLinearForget
    (U : ι → Opens T) (F : ModuleSheaf (R := R) T) :
    (complex (R := R) U).contravariantHomCocomplex F ≅
      ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          (contravariantHomCocomplex U F) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q =>
      (CategoryTheory.oppositeHomAddEquiv
        ((complex (R := R) U).X q) F).toAddCommGrpIso)
    (by
      rintro i j (rfl : i + 1 = j)
      apply AddCommGrpCat.hom_ext
      ext f
      change
        (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
            (contravariantHomCocomplex U F)).d i (i + 1) f.unop =
          (((complex (R := R) U).contravariantHomCocomplex F).d
            i (i + 1) f).unop
      rw [Functor.mapHomologicalComplex_obj_d]
      change
        (contravariantHomCocomplex U F).d i (i + 1) f.unop =
          (((complex (R := R) U).contravariantHomCocomplex F).d
            i (i + 1) f).unop
      have hcustom :
          (contravariantHomCocomplex U F).d i (i + 1) f.unop =
            boundary (R := R) U i ≫ f.unop := by
        rw [show
          (contravariantHomCocomplex U F).d i (i + 1) =
            ModuleCat.ofHom (contravariantHomDifferential U F i) by
              simp only [contravariantHomCocomplex, CochainComplex.of_d]]
        rfl
      have hcategorical :
          ((complex (R := R) U).contravariantHomCocomplex F).d
              i (i + 1) f =
            f ≫ (boundary (R := R) U i).op := by
        change
          (CategoryTheory.contravariantHomFunctor F).map
              ((complex (R := R) U).d (i + 1) i).op f =
            f ≫ (boundary (R := R) U i).op
        dsimp [CategoryTheory.contravariantHomFunctor,
          preadditiveCoyoneda, preadditiveCoyonedaObj]
        rw [show
          (complex (R := R) U).d (i + 1) i =
            boundary (R := R) U i by
              simp only [complex, ChainComplex.of_d]]
        rfl
      rw [hcustom, hcategorical]
      rfl)

/-- Forgetting the coefficient-module structure commutes with homology
of the explicit finite-subset Hom complex. -/
noncomputable def linearForgetHomologyIso
    (U : ι → Opens T) (F : ModuleSheaf (R := R) T) (n : ℕ) :
    (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          (contravariantHomCocomplex U F)).homology n ≅
      (forget₂ (ModuleCat R) AddCommGrpCat).obj
        ((contravariantHomCocomplex U F).homology n) :=
  ((contravariantHomCocomplex U F).sc n).mapHomologyIso
    (forget₂ (ModuleCat R) AddCommGrpCat)

/-- Ext from the constant rank-one sheaf is computed by the underlying
abelian group of the coefficient-linear normalized Čech Homology. -/
noncomputable def finiteSubsetFreeSheafExtIsoLinearResolutionHomology
    (U : ι → Opens T) (hU : ⨆ i, U i = ⊤)
    (F : ModuleSheaf (R := R) T)
    (hfree :
      ∀ (q m : ℕ) (I : Simplex (ι := ι) q),
        Subsingleton
          (Abelian.Ext.{u}
            (freeModuleSheaf (R := R)
              (intersection U I.1))
            F (m + 1)))
    (n : ℕ) :
    AddCommGrpCat.of
        (Abelian.Ext.{u}
          (constantRankOneSheaf (R := R) T) F n) ≅
      (forget₂ (ModuleCat R) AddCommGrpCat).obj
        ((contravariantHomCocomplex U F).homology n) :=
  finiteSubsetFreeSheafExtIsoResolutionHomology U hU F hfree n ≪≫
    (HomologicalComplex.homologyFunctor
      AddCommGrpCat (ComplexShape.up ℕ) n).mapIso
        (categoricalContravariantHomCocomplexIsoLinearForget U F) ≪≫
    linearForgetHomologyIso U F n

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf
