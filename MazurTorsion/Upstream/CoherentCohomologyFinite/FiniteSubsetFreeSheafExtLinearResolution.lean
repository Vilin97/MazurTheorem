/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ExtLinearAcyclicCoresolution
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteSubsetFreeSheafExtAcyclic
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteSubsetFreeSheafHomComparison

/-!
# Coefficient-linear Ext comparison for the finite-subset resolution

The normalized finite-cover free-sheaf resolution computes Ext not only
as an additive group but as a module over the coefficient ring.  This is
the form required to transport finite generation over arbitrary
Noetherian affine bases.
-/

open CategoryTheory TopologicalSpace


noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {R : Type u} [CommRing R]
variable {T : TopCat.{u}}
variable {ι : Type u} [Fintype ι] [LinearOrder ι]

/-- The generic linear-Yoneda Hom complex of the finite-subset
resolution is its explicit coefficient-linear Hom complex. -/
noncomputable def linearContravariantHomCocomplexIso
    (U : ι → Opens T) (F : ModuleSheaf (R := R) T) :
    (complex (R := R) U).linearContravariantHomCocomplex R F ≅
      contravariantHomCocomplex U F :=
  HomologicalComplex.Hom.isoOfComponents
    (fun _ => Iso.refl _)
    (by
      rintro i j (rfl : i + 1 = j)
      change
        (𝟙 _ ≫ (contravariantHomCocomplex U F).d i (i + 1)) =
          ((complex (R := R) U).linearContravariantHomCocomplex R F).d
              i (i + 1) ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      have hcustom :
          (contravariantHomCocomplex U F).d i (i + 1) f =
            boundary (R := R) U i ≫ f := by
        rw [show
          (contravariantHomCocomplex U F).d i (i + 1) =
            ModuleCat.ofHom (contravariantHomDifferential U F i) by
              simp only [contravariantHomCocomplex, CochainComplex.of_d]]
        rfl
      have hgeneric :
          ((complex (R := R) U).linearContravariantHomCocomplex R F).d
              i (i + 1) f =
            boundary (R := R) U i ≫ f := by
        change
          (CategoryTheory.linearContravariantHomFunctor R F).map
              ((complex (R := R) U).d (i + 1) i).op f =
            boundary (R := R) U i ≫ f
        dsimp [CategoryTheory.linearContravariantHomFunctor,
          CategoryTheory.linearYoneda]
        rw [show
          (complex (R := R) U).d (i + 1) i =
            boundary (R := R) U i by
              simp only [complex, ChainComplex.of_d]]
        rfl
      exact hcustom.trans hgeneric.symm)

/-- Ext from the constant rank-one sheaf is the homology of the
coefficient-linear normalized Čech Hom complex. -/
noncomputable def finiteSubsetFreeSheafExtLinearIsoResolutionHomology
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
    ModuleCat.of R
        (Abelian.Ext.{u}
          (constantRankOneSheaf (R := R) T) F n) ≅
      (contravariantHomCocomplex U F).homology n := by
  let ε :=
    finiteSubsetFreeSheafAugmentationToConstant
      (R := R) U hU
  letI : QuasiIso ε :=
    finiteSubsetFreeSheafAugmentationToConstant_quasiIso
      (R := R) U hU
  exact
    CategoryTheory.extLinearIsoHomologyOfAcyclicCoresolution
        (R := R)
        (complex (R := R) U)
        (ChainComplex.opcyclesZeroIsoOfQuasiIsoToSingle ε)
        (finiteSubsetFreeSheafComplex_exactAt_succ
          (R := R) U hU)
        (fun q m =>
          finiteSubsetFreeSheafTerm_ext_subsingleton
            (R := R) U F q m (hfree q m))
        n ≪≫
      (HomologicalComplex.homologyFunctor
        (ModuleCat R) (ComplexShape.up ℕ) n).mapIso
          (linearContravariantHomCocomplexIso U F)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf
