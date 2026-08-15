/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteSubsetFreeSheafComplexComparison
import MazurTorsion.Upstream.CoherentCohomologyFinite.ExtAcyclicCoresolutionLES
import MazurTorsion.Upstream.CoherentCohomologyFinite.ExtAdjunction
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Ext-acyclicity of the finite-subset source resolution

Finite coproducts are biproducts in an abelian category, so Ext in its
contravariant source variable sends a finite coproduct to a finite
product.  Consequently, Ext-acyclicity of the represented intersection
summands implies Ext-acyclicity of every term in the ordered-cover
resolution.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace


noncomputable section

universe v u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

/-- Ext-acyclicity in the first variable is preserved by finite
coproducts. -/
theorem ext_subsingleton_finite_coproduct
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt.{v} C]
    {J : Type v} [Fintype J]
    (X : J → C) (B : C) (n : ℕ)
    (hX : ∀ j, Subsingleton (Abelian.Ext.{v} (X j) B n)) :
    Subsingleton (Abelian.Ext.{v} (∐ X) B n) := by
  let c : Bicone X :=
    Bicone.ofColimitCocone
      (colimit.isColimit (Discrete.functor X))
  let hc : c.IsBilimit :=
    biconeIsBilimitOfColimitCoconeOfIsColimit
      (colimit.isColimit (Discrete.functor X))
  let e :
      Abelian.Ext.{v} c.pt B n ≃+
        ((j : J) → Abelian.Ext.{v} (X j) B n) :=
    Abelian.Ext.biproductAddEquiv hc B n
  letI (j : J) :
      Subsingleton (Abelian.Ext.{v} (X j) B n) :=
    hX j
  exact
    ⟨fun x y => e.injective (Subsingleton.elim (e x) (e y))⟩

/-- Ext-acyclicity in the first variable transports across an
isomorphism. -/
theorem ext_subsingleton_of_source_iso
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt.{v} C]
    {X Y B : C} (e : X ≅ Y) (n : ℕ)
    (hY : Subsingleton (Abelian.Ext.{v} Y B n)) :
    Subsingleton (Abelian.Ext.{v} X B n) := by
  let E :=
    ExtAdjunction.precompIsoAddEquiv (Z := B) e n
  exact
    ⟨fun x y =>
      E.symm.injective (hY.elim (E.symm x) (E.symm y))⟩

namespace FiniteSubsetFreeSheaf

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {R : Type u} [CommRing R]
variable {T : TopCat.{u}}
variable {ι : Type u} [Fintype ι] [LinearOrder ι]

/-- Ext-acyclicity of the represented intersection summands implies
Ext-acyclicity of the existing finite-subset free sheaf term. -/
theorem finiteSubsetFreeSheafTerm_ext_subsingleton
    (U : ι → Opens T) (B : ModuleSheaf (R := R) T)
    (q m : ℕ)
    (hfree :
      ∀ I : Simplex (ι := ι) q,
        Subsingleton
          (Abelian.Ext.{u}
            (freeModuleSheaf (R := R)
              (intersection U I.1))
            B (m + 1))) :
    Subsingleton
      (Abelian.Ext.{u}
        (term (R := R) U q)
        B (m + 1)) :=
  ext_subsingleton_finite_coproduct
    (fun I : Simplex (ι := ι) q =>
      freeModuleSheaf (R := R) (intersection U I.1))
    B (m + 1) hfree

/-- If every represented intersection summand is Ext-acyclic against
`B`, then every sheafified ordered-cover term is Ext-acyclic against
`B`. -/
theorem sheafifiedOrderedCoverTerm_ext_subsingleton
    (U : ι → Opens T) (B : ModuleSheaf (R := R) T)
    (q m : ℕ)
    (hfree :
      ∀ I : Simplex (ι := ι) q,
        Subsingleton
          (Abelian.Ext.{u}
            (freeModuleSheaf (R := R)
              (intersection U I.1))
            B (m + 1))) :
    Subsingleton
      (Abelian.Ext.{u}
        ((sheafifiedOrderedCoverComplex (R := R) U).X q)
        B (m + 1)) := by
  have hterm :
      Subsingleton
        (Abelian.Ext.{u} (term (R := R) U q) B (m + 1)) :=
    finiteSubsetFreeSheafTerm_ext_subsingleton
      (R := R) U B q m hfree
  exact
    ext_subsingleton_of_source_iso
      (sheafifiedOrderedCoverTermIso (R := R) U q)
      (m + 1) hterm

/-- The projective-free Ext comparison supplied by the exact
ordered-cover resolution.  The only geometric input is the
positive-degree Ext-acyclicity of each represented intersection
summand. -/
noncomputable def orderedCoverExtIsoResolutionHomology
    (U : ι → Opens T) (hU : ⨆ i, U i = ⊤)
    (B : ModuleSheaf (R := R) T)
    (hfree :
      ∀ (q m : ℕ) (I : Simplex (ι := ι) q),
        Subsingleton
          (Abelian.Ext.{u}
            (freeModuleSheaf (R := R)
              (intersection U I.1))
            B (m + 1)))
    (n : ℕ) :
    AddCommGrpCat.of
        (Abelian.Ext.{u}
          (constantRankOneSheaf (R := R) T) B n) ≅
      ((sheafifiedOrderedCoverComplex
        (R := R) U).contravariantHomCocomplex B).homology n := by
  let ε :=
    sheafifiedOrderedCoverAugmentationToConstant
      (R := R) U hU
  letI : QuasiIso ε :=
    sheafifiedOrderedCoverAugmentationToConstant_quasiIso
      (R := R) U hU
  exact
    CategoryTheory.extIsoHomologyOfAcyclicCoresolutionLES
      (sheafifiedOrderedCoverComplex (R := R) U)
      (ChainComplex.opcyclesZeroIsoOfQuasiIsoToSingle ε)
      (sheafifiedOrderedCoverComplex_exactAt_succ
        (R := R) U hU)
      (fun q m =>
        sheafifiedOrderedCoverTerm_ext_subsingleton
          (R := R) U B q m (hfree q m))
      n

/-- Ext from the constant rank-one sheaf is computed by the
contravariant Hom cocomplex of the existing finite-subset free sheaf
resolution.  The only remaining input is positive-degree Ext
acyclicity of the represented intersection summands. -/
noncomputable def finiteSubsetFreeSheafExtIsoResolutionHomology
    (U : ι → Opens T) (hU : ⨆ i, U i = ⊤)
    (B : ModuleSheaf (R := R) T)
    (hfree :
      ∀ (q m : ℕ) (I : Simplex (ι := ι) q),
        Subsingleton
          (Abelian.Ext.{u}
            (freeModuleSheaf (R := R)
              (intersection U I.1))
            B (m + 1)))
    (n : ℕ) :
    AddCommGrpCat.of
        (Abelian.Ext.{u}
          (constantRankOneSheaf (R := R) T) B n) ≅
      ((complex (R := R) U).contravariantHomCocomplex B).homology n := by
  let ε :=
    finiteSubsetFreeSheafAugmentationToConstant
      (R := R) U hU
  letI : QuasiIso ε :=
    finiteSubsetFreeSheafAugmentationToConstant_quasiIso
      (R := R) U hU
  exact
    CategoryTheory.extIsoHomologyOfAcyclicCoresolutionLES
      (complex (R := R) U)
      (ChainComplex.opcyclesZeroIsoOfQuasiIsoToSingle ε)
      (finiteSubsetFreeSheafComplex_exactAt_succ
        (R := R) U hU)
      (fun q m =>
        finiteSubsetFreeSheafTerm_ext_subsingleton
          (R := R) U B q m (hfree q m))
      n

end FiniteSubsetFreeSheaf

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
