/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentLocalization
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveFactorization
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistInteger
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleIsoSections
import MazurTorsion.Upstream.CoherentCohomologyFinite.CoefficientRationalization
import Mathlib.Algebra.Module.LinearMap.Rat

open CategoryTheory AlgebraicGeometry
open scoped BigOperators


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleIsoSections
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.CoefficientRationalization
open MazurTorsion.AlgebraicGeometry.CoherentCohomology
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

noncomputable section

lemma coordinateProduct_subtype_eq_variableProduct
    (k : Type) [CommRing k] (d : ℕ)
    (I : Finset (Fin (d + 1))) :
    coordinateProduct k (fun i : ↥I => i.1) =
      variableProduct (k := k) I := by
  simpa [coordinateProduct, variableProduct] using
    Finset.prod_attach I
      (fun i : Fin (d + 1) => MvPolynomial.X i)

def standardIntersectionAwayRingEquiv
    (k : Type) [CommRing k] (d : ℕ)
    {ι : Type} [Fintype ι] [Nonempty ι]
    (a : ι → Fin (d + 1)) :
    HomogeneousLocalization.Away
        (homogeneousGrading k d) (coordinateProduct k a) ≃+*
      Γ((standardIntersection k a).toScheme, ⊤) :=
  (Proj.basicOpenIsoAway
      (homogeneousGrading k d) (coordinateProduct k a)
      (coordinateProduct_mem_degreeCard k a)
      Fintype.card_pos).commRingCatIsoToRingEquiv.trans
    (standardIntersection k a).topIso.symm.commRingCatIsoToRingEquiv

def addEquivToRatLinearEquiv
    {M N : Type} [AddCommGroup M] [AddCommGroup N]
    [Module ℚ M] [Module ℚ N]
    (e : M ≃+ N) : M ≃ₗ[ℚ] N :=
  LinearEquiv.ofBijective e.toAddMonoidHom.toRatLinearMap
    e.bijective

def standardIntersectionDegreeZeroSectionsLinearEquiv
    (d : ℕ) (I : Finset (Fin (d + 1))) [Nonempty ↥I] :
    let U := standardIntersection ℚ (fun i : ↥I => i.1)
    letI :
        U.toScheme.Over (Spec (CommRingCat.of ℚ)) :=
      ⟨U.ι ≫ MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec ℚ d⟩
    letI : Module ℚ Γ(U.toScheme, ⊤) :=
      Geometric.sectionsModule
        (SheafOfModules.unit U.toScheme.ringCatSheaf) ⊤
    MonomialModule (ι := Fin (d + 1)) ℚ 0 I ≃ₗ[ℚ]
      Γ(U.toScheme, ⊤) := by
  classical
  dsimp only
  let U := standardIntersection ℚ (fun i : ↥I => i.1)
  letI :
      U.toScheme.Over (Spec (CommRingCat.of ℚ)) :=
    ⟨U.ι ≫ MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec ℚ d⟩
  letI : Module ℚ Γ(U.toScheme, ⊤) :=
    Geometric.sectionsModule
      (SheafOfModules.unit U.toScheme.ringCatSheaf) ⊤
  let h :
      coordinateProduct ℚ (fun i : ↥I => i.1) =
        variableProduct (k := ℚ) I :=
    coordinateProduct_subtype_eq_variableProduct ℚ d I
  let e :
      HomogeneousLocalization.Away
          (homogeneousGrading ℚ d) (variableProduct (k := ℚ) I) ≃+*
        Γ((standardIntersection ℚ
          (fun i : ↥I => i.1)).toScheme, ⊤) := by
    exact h ▸
      standardIntersectionAwayRingEquiv
        ℚ d (fun i : ↥I => i.1)
  exact addEquivToRatLinearEquiv <|
    (degreeZeroFractionLinearEquiv
      (k := ℚ) I).toAddEquiv.trans e.toAddEquiv

def integerIntersectionRestrictIso'
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    {ι : Type} [Fintype ι]
    (a : ι → Fin (d + 1)) (j : ι) :
    (OInt k d m).restrict (standardIntersection k a).ι ≅
      SheafOfModules.unit
        (standardIntersection k a).toScheme.ringCatSheaf :=
  (Scheme.Modules.restrictFunctorIsoPullback
      (standardIntersection k a).ι).app (OInt k d m) ≪≫
    integerIntersectionIso k d m a j

def sectionsRestrictTopAddEquiv
    {X : Scheme} (M : X.Modules) (U : X.Opens) :
    Γ(M, U) ≃+ Γ(M.restrict U.ι, ⊤) := by
  have himage :
      U.ι ''ᵁ (⊤ : U.toScheme.Opens) = U := by
    rw [U.ι.image_top_eq_opensRange,
      Scheme.Opens.opensRange_ι]
  exact
    (M.presheaf.mapIso
      (eqToIso himage).op).addCommGroupIsoToAddEquiv |>.trans
        ((M.restrictAppIso U.ι
          (⊤ : U.toScheme.Opens)).symm.addCommGroupIsoToAddEquiv)

def unitTopSectionsAddEquiv (X : Scheme) :
    Γ(SheafOfModules.unit X.ringCatSheaf, ⊤) ≃+
      Γ(X, ⊤) :=
  AddEquiv.refl _

def integerIntersectionSectionsAddEquiv
    (d : ℕ) (m : ℤ) (I : Finset (Fin (d + 1)))
    [Nonempty ↥I] (j : ↥I) :
    Γ(OInt ℚ d m, standardIntersection ℚ
        (fun i : ↥I => i.1)) ≃+
      Γ((standardIntersection ℚ
        (fun i : ↥I => i.1)).toScheme, ⊤) := by
  let U := standardIntersection ℚ (fun i : ↥I => i.1)
  exact
    (sectionsRestrictTopAddEquiv (OInt ℚ d m) U).trans <|
      (sectionsAddEquivOfIso
        (integerIntersectionRestrictIso'
          ℚ d m (fun i : ↥I => i.1) j)).trans <|
        unitTopSectionsAddEquiv U.toScheme

def integerIntersectionSectionsLinearEquiv
    (d : ℕ) (m : ℤ) (I : Finset (Fin (d + 1)))
    [Nonempty ↥I] (j : ↥I) :
    letI :
        (scheme ℚ d).Over (Spec (CommRingCat.of ℚ)) :=
      ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec ℚ d⟩
    let U := standardIntersection ℚ (fun i : ↥I => i.1)
    letI :
        U.toScheme.Over (Spec (CommRingCat.of ℚ)) :=
      ⟨U.ι ≫ MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec ℚ d⟩
    letI : Module ℚ Γ(U.toScheme, ⊤) :=
      Geometric.sectionsModule
        (SheafOfModules.unit U.toScheme.ringCatSheaf) ⊤
    (Geometric.moduleSheaf (OInt ℚ d m)).obj.obj (Opposite.op U) ≃ₗ[ℚ]
      Γ(U.toScheme, ⊤) := by
  dsimp only
  letI :
      (scheme ℚ d).Over (Spec (CommRingCat.of ℚ)) :=
    ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec ℚ d⟩
  let U := standardIntersection ℚ (fun i : ↥I => i.1)
  letI :
      U.toScheme.Over (Spec (CommRingCat.of ℚ)) :=
    ⟨U.ι ≫ MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec ℚ d⟩
  letI : Module ℚ Γ(U.toScheme, ⊤) :=
    Geometric.sectionsModule
      (SheafOfModules.unit U.toScheme.ringCatSheaf) ⊤
  exact addEquivToRatLinearEquiv <|
    integerIntersectionSectionsAddEquiv d m I j

/-- The exponent concentrated at the chosen trivializing coordinate. -/
def coordinateShift {ι : Type} [DecidableEq ι]
    (j : ι) (m : ℤ) : ProjectiveExponent ι :=
  fun i => if i = j then m else 0

@[simp]
lemma coordinateShift_apply {ι : Type} [DecidableEq ι]
    (j i : ι) (m : ℤ) :
    coordinateShift j m i = if i = j then m else 0 :=
  rfl

lemma coordinateShift_totalDegree {ι : Type}
    [Fintype ι] [DecidableEq ι] (j : ι) (m : ℤ) :
    ProjectiveExponent.totalDegree (coordinateShift j m) = m := by
  simp [ProjectiveExponent.totalDegree, coordinateShift]

def admissibleExponentShiftEquiv
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (I : Finset ι) (j : ↥I) (m : ℤ) :
    AdmissibleExponent (ι := ι) 0 I ≃
      AdmissibleExponent (ι := ι) m I where
  toFun a :=
    ⟨a.1 + coordinateShift j.1 m,
      by
        rw [ProjectiveExponent.totalDegree_add,
          a.2.1, coordinateShift_totalDegree]
        simp,
      by
        rw [ProjectiveExponent.admissibleOn_iff_nonnegative_outside]
        intro i hi
        have hij : i ≠ j.1 := fun h => hi (h ▸ j.2)
        have hai :=
          (ProjectiveExponent.admissibleOn_iff_nonnegative_outside
            a.1 I).mp a.2.2 i hi
        simpa [coordinateShift, hij] using hai⟩
  invFun b :=
    ⟨b.1 - coordinateShift j.1 m,
      by
        rw [ProjectiveExponent.totalDegree_sub,
          b.2.1, coordinateShift_totalDegree]
        simp,
      by
        rw [ProjectiveExponent.admissibleOn_iff_nonnegative_outside]
        intro i hi
        have hij : i ≠ j.1 := fun h => hi (h ▸ j.2)
        have hbi :=
          (ProjectiveExponent.admissibleOn_iff_nonnegative_outside
            b.1 I).mp b.2.2 i hi
        simpa [coordinateShift, hij] using hbi⟩
  left_inv a := by
    apply Subtype.ext
    module
  right_inv b := by
    apply Subtype.ext
    module

def monomialModuleShiftLinearEquiv
    {k ι : Type} [Semiring k] [Fintype ι] [DecidableEq ι]
    (I : Finset ι) (j : ↥I) (m : ℤ) :
    MonomialModule (ι := ι) k 0 I ≃ₗ[k]
      MonomialModule (ι := ι) k m I :=
  Finsupp.domLCongr (admissibleExponentShiftEquiv I j m)

def integerIntersectionLaurentSectionsLinearEquiv
    (d : ℕ) (m : ℤ) (I : Finset (Fin (d + 1)))
    [Nonempty ↥I] (j : ↥I) :
    letI :
        (scheme ℚ d).Over (Spec (CommRingCat.of ℚ)) :=
      ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec ℚ d⟩
    let U := standardIntersection ℚ (fun i : ↥I => i.1)
    letI :
        U.toScheme.Over (Spec (CommRingCat.of ℚ)) :=
      ⟨U.ι ≫ MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec ℚ d⟩
    (Geometric.moduleSheaf (OInt ℚ d m)).obj.obj (Opposite.op U) ≃ₗ[ℚ]
      MonomialModule (ι := Fin (d + 1)) ℚ m I := by
  dsimp only
  letI :
      (scheme ℚ d).Over (Spec (CommRingCat.of ℚ)) :=
    ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec ℚ d⟩
  let U := standardIntersection ℚ (fun i : ↥I => i.1)
  letI :
      U.toScheme.Over (Spec (CommRingCat.of ℚ)) :=
    ⟨U.ι ≫ MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec ℚ d⟩
  letI : Module ℚ Γ(U.toScheme, ⊤) :=
    Geometric.sectionsModule
      (SheafOfModules.unit U.toScheme.ringCatSheaf) ⊤
  exact
    (integerIntersectionSectionsLinearEquiv d m I j).trans <|
      (standardIntersectionDegreeZeroSectionsLinearEquiv d I).symm.trans <|
        monomialModuleShiftLinearEquiv I j m

end
end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
