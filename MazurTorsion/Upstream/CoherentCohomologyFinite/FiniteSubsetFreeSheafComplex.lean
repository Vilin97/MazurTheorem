/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ExtAcyclicCoresolutionLES
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteSubsetCechComplex
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# The normalized finite-subset free-sheaf complex

For a finite ordered family of opens `U i`, degree `q` is the finite
coproduct of the sheafified free `R`-module representables on the
`(q+1)`-fold intersections.  The boundary is the alternating sum of
the maps which forget one vertex.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped BigOperators


noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {R : Type u} [CommRing R]
variable {T : TopCat.{u}}
variable {ι : Type u} [Fintype ι] [LinearOrder ι]

/-- Sheaves of modules over the constant coefficient ring `R`. -/
abbrev ModuleSheaf (T : TopCat.{u}) :=
  Sheaf (Opens.grothendieckTopology T) (ModuleCat.{u} R)

noncomputable instance moduleSheafHasFiniteCoproducts :
    HasFiniteCoproducts (ModuleSheaf (R := R) T) :=
  inferInstance

/-- Naming the finite simplex instance avoids an expensive search through
the subtype and finite-set hierarchy each time a coproduct is elaborated. -/
noncomputable instance simplexFintype (q : ℕ) :
    Fintype (Simplex (ι := ι) q) :=
  Fintype.ofFinite _

/-- The particular finite coproduct shape used in degree `q`.
Supplying it explicitly keeps the sheaf-colimit search below the default
heartbeat limit. -/
noncomputable instance simplexHasColimits (q : ℕ) :
    HasColimitsOfShape
      (Discrete (Simplex (ι := ι) q))
      (ModuleSheaf (R := R) T) := by
  letI : Finite (Simplex (ι := ι) q) := inferInstance
  exact Limits.hasColimitsOfShape_discrete
    (C := ModuleSheaf (R := R) T) _

/-- The sheafification of the free `R`-module presheaf represented by an
open. -/
noncomputable def freeModuleSheaf (V : Opens T) :
    ModuleSheaf (R := R) T :=
  (presheafToSheaf _ _).obj
    (yoneda.obj V ⋙ ModuleCat.free R)

/-- An inclusion of opens induces a morphism of free module sheaves. -/
noncomputable def freeModuleSheafMap {V W : Opens T} (i : V ⟶ W) :
    freeModuleSheaf (R := R) V ⟶ freeModuleSheaf (R := R) W :=
  (presheafToSheaf _ _).map
    (Functor.whiskerRight (yoneda.map i) (ModuleCat.free R))

@[simp]
lemma freeModuleSheafMap_id (V : Opens T) :
    freeModuleSheafMap (R := R) (𝟙 V) = 𝟙 _ := by
  change
    (presheafToSheaf _ _).map
        (Functor.whiskerRight (yoneda.map (𝟙 V)) (ModuleCat.free R)) =
      𝟙 ((presheafToSheaf _ _).obj
        (yoneda.obj V ⋙ ModuleCat.free R))
  simp

@[reassoc]
lemma freeModuleSheafMap_comp {V W Z : Opens T}
    (i : V ⟶ W) (j : W ⟶ Z) :
    freeModuleSheafMap (R := R) i ≫ freeModuleSheafMap (R := R) j =
      freeModuleSheafMap (R := R) (i ≫ j) := by
  change
    (presheafToSheaf _ _).map
          (Functor.whiskerRight (yoneda.map i) (ModuleCat.free R)) ≫
        (presheafToSheaf _ _).map
          (Functor.whiskerRight (yoneda.map j) (ModuleCat.free R)) =
      (presheafToSheaf _ _).map
        (Functor.whiskerRight (yoneda.map (i ≫ j)) (ModuleCat.free R))
  rw [← Functor.map_comp]
  congr 1
  simp

/-- The intersection of the opens indexed by a finite subset. -/
def intersection (U : ι → Opens T) (I : Finset ι) : Opens T :=
  ⨅ i ∈ I, U i

/-- Enlarging the index subset shrinks the intersection open. -/
lemma intersection_anti (U : ι → Opens T)
    {I J : Finset ι} (h : I ⊆ J) :
    intersection U J ≤ intersection U I := by
  refine le_iInf fun i => le_iInf fun hi => ?_
  exact iInf_le_of_le i (iInf_le_of_le (h hi) le_rfl)

/-- The free sheaf attached to one normalized simplex. -/
noncomputable abbrev simplexSheaf
    (U : ι → Opens T) {q : ℕ} (I : Simplex (ι := ι) q) :
    ModuleSheaf (R := R) T :=
  freeModuleSheaf (R := R) (intersection U I.1)

/-- Degree `q` of the normalized source complex. -/
noncomputable abbrev term (U : ι → Opens T) (q : ℕ) :
    ModuleSheaf (R := R) T :=
  ∐ fun I : Simplex (ι := ι) q => simplexSheaf (R := R) U I

/-- The face map which removes `j` from a simplex. -/
noncomputable def faceMap
    (U : ι → Opens T) {q : ℕ}
    (J : Simplex (ι := ι) (q + 1)) (j : ↥J.1) :
    simplexSheaf (R := R) U J ⟶
      simplexSheaf (R := R) U (J.erase j.1 j.2) :=
  freeModuleSheafMap (R := R)
    (homOfLE (intersection_anti U (Finset.erase_subset j.1 J.1)))

/-- The boundary of a single source simplex. -/
noncomputable def simplexBoundary
    (U : ι → Opens T) (q : ℕ)
    (J : Simplex (ι := ι) (q + 1)) :
    simplexSheaf (R := R) U J ⟶ term (R := R) U q :=
  ∑ j : ↥J.1,
    insertionSign (R := ℤ) (J.1.erase j.1) j.1 •
      (faceMap (R := R) U J j ≫
        Limits.Sigma.ι
          (fun I : Simplex (ι := ι) q =>
            simplexSheaf (R := R) U I)
          (J.erase j.1 j.2))

/-- The normalized alternating boundary. -/
noncomputable def boundary
    (U : ι → Opens T) (q : ℕ) :
    term (R := R) U (q + 1) ⟶ term (R := R) U q :=
  Limits.Sigma.desc (simplexBoundary (R := R) U q)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf
