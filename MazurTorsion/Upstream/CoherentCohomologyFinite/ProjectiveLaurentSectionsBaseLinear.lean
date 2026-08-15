/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentBaseScalars

/-!
# Base-linear Laurent coordinates on projective intersections

The arbitrary-base Laurent comparison is naturally linear for the
coefficient-ring action induced by the structure morphism
`ℙⁿ_k ⟶ Spec k`.  This file upgrades the additive comparisons to linear
equivalences.
-/

open CategoryTheory AlgebraicGeometry Opposite


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleIsoSections
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

noncomputable section

variable (k : Type) [CommRing k] (d : ℕ)

local instance projectiveSpaceOverCoefficientRing :
    (scheme k d).Over (Spec (CommRingCat.of k)) :=
  ⟨toSpec k d⟩

/-- The trivialization of an integer Serre twist on a standard
intersection respects coefficient scalars. -/
lemma integerIntersectionSectionsAddEquivOver_map_smul
    (m : ℤ) (I : Finset (Fin (d + 1)))
    [Nonempty ↥I] (j : ↥I)
    (r : k)
    (x : (moduleSheaf (k := k) (OInt k d m)).obj.obj
      (op (standardIntersection k (fun i : ↥I => i.1)))) :
    let U := standardIntersection k (fun i : ↥I => i.1)
    letI : U.toScheme.Over (Spec (CommRingCat.of k)) :=
      ⟨U.ι ≫ toSpec k d⟩
    letI : Module k Γ(U.toScheme, ⊤) :=
      sectionsModule
        (k := k) (SheafOfModules.unit U.toScheme.ringCatSheaf) ⊤
    integerIntersectionSectionsAddEquivOver k d m I j (r • x) =
      r • integerIntersectionSectionsAddEquivOver k d m I j x := by
  dsimp only
  let U := standardIntersection k (fun i : ↥I => i.1)
  letI : U.toScheme.Over (Spec (CommRingCat.of k)) :=
    ⟨U.ι ≫ toSpec k d⟩
  letI : Module k Γ(U.toScheme, ⊤) :=
    sectionsModule
      (k := k) (SheafOfModules.unit U.toScheme.ringCatSheaf) ⊤
  change
    integerIntersectionSectionsAddEquivOver k d m I j
        (((OInt k d m).smul
          (algebraMapOnOpen (k := k) U r)).hom x) =
      (Scheme.Modules.smul
        (M := SheafOfModules.unit U.toScheme.ringCatSheaf)
        (algebraMapOnOpen (k := k)
          (X := U.toScheme) ⊤ r)).hom
        (integerIntersectionSectionsAddEquivOver k d m I j x)
  let e :=
    integerIntersectionRestrictIso'
      k d m (fun i : ↥I => i.1) j
  change
    sectionsAddEquivOfIso e
        (sectionsRestrictTopAddEquiv (OInt k d m) U
          (((OInt k d m).smul
            (algebraMapOnOpen (k := k) U r)).hom x)) =
      (Scheme.Modules.smul
        (M := SheafOfModules.unit U.toScheme.ringCatSheaf)
        (algebraMapOnOpen (k := k)
          (X := U.toScheme) ⊤ r)).hom
        (sectionsAddEquivOfIso e
          (sectionsRestrictTopAddEquiv (OInt k d m) U x))
  have hrestrict :=
    sectionsRestrictTopAddEquiv_smul
      (M := OInt k d m) U
      (algebraMapOnOpen (k := k) U r) x
  have hiso :=
    sectionsAddEquivOfIso_smul e
      (U.topIso.inv.hom (algebraMapOnOpen (k := k) U r))
      (sectionsRestrictTopAddEquiv (OInt k d m) U x)
  have hscalar :=
    standardIntersection_topIso_inv_algebraMapOnOpen k d I r
  exact
    (congrArg (sectionsAddEquivOfIso e) hrestrict).trans <|
      hiso.trans <|
        congrArg
          (fun a =>
            (Scheme.Modules.smul
              (M := SheafOfModules.unit U.toScheme.ringCatSheaf) a).hom
              (sectionsAddEquivOfIso e
                (sectionsRestrictTopAddEquiv (OInt k d m) U x)))
          hscalar

/-- The standard-intersection twist trivialization as a coefficient-linear
equivalence. -/
noncomputable def integerIntersectionSectionsLinearEquivOver
    (m : ℤ) (I : Finset (Fin (d + 1)))
    [Nonempty ↥I] (j : ↥I) :
    let U := standardIntersection k (fun i : ↥I => i.1)
    letI : U.toScheme.Over (Spec (CommRingCat.of k)) :=
      ⟨U.ι ≫ toSpec k d⟩
    letI : Module k Γ(U.toScheme, ⊤) :=
      sectionsModule
        (k := k) (SheafOfModules.unit U.toScheme.ringCatSheaf) ⊤
    (moduleSheaf (k := k) (OInt k d m)).obj.obj (op U) ≃ₗ[k]
      Γ(U.toScheme, ⊤) := by
  dsimp only
  let U := standardIntersection k (fun i : ↥I => i.1)
  letI : U.toScheme.Over (Spec (CommRingCat.of k)) :=
    ⟨U.ι ≫ toSpec k d⟩
  letI : Module k Γ(U.toScheme, ⊤) :=
    sectionsModule
      (k := k) (SheafOfModules.unit U.toScheme.ringCatSheaf) ⊤
  let e := integerIntersectionSectionsAddEquivOver k d m I j
  exact
    { e with
      map_smul' :=
        integerIntersectionSectionsAddEquivOver_map_smul
          k d m I j }

/-- The ring equivalence from the homogeneous localization to sections
on its projective basic open sends coefficient constants to structural
coefficient sections. -/
lemma variableProductBasicOpenAwayRingEquiv_algebraMap
    (I : Finset (Fin (d + 1))) [Nonempty ↥I] (r : k) :
    let U := Proj.basicOpen (homogeneousGrading k d)
      (variableProduct (k := k) I)
    letI : U.toScheme.Over (Spec (CommRingCat.of k)) :=
      ⟨U.ι ≫ toSpec k d⟩
    let e :
        HomogeneousLocalization.Away
            (homogeneousGrading k d) (variableProduct (k := k) I) ≃+*
          Γ(U.toScheme, ⊤) :=
      (Proj.basicOpenIsoAway
        (homogeneousGrading k d)
        (variableProduct (k := k) I)
        (variableProduct_mem_degreeCard I)
        (by
          let j : ↥I := Classical.choice inferInstance
          exact Finset.card_pos.mpr ⟨j.1, j.2⟩)
        ).commRingCatIsoToRingEquiv.trans
          U.topIso.symm.commRingCatIsoToRingEquiv
    e (algebraMap k
        (HomogeneousLocalization.Away
          (homogeneousGrading k d)
          (variableProduct (k := k) I)) r) =
      algebraMapOnOpen (k := k) (X := U.toScheme) ⊤ r := by
  dsimp only
  let U := Proj.basicOpen (homogeneousGrading k d)
    (variableProduct (k := k) I)
  letI : U.toScheme.Over (Spec (CommRingCat.of k)) :=
    ⟨U.ι ≫ toSpec k d⟩
  let e :
      HomogeneousLocalization.Away
          (homogeneousGrading k d) (variableProduct (k := k) I) ≃+*
        Γ(U.toScheme, ⊤) :=
    (Proj.basicOpenIsoAway
      (homogeneousGrading k d)
      (variableProduct (k := k) I)
      (variableProduct_mem_degreeCard I)
      (by
        let j : ↥I := Classical.choice inferInstance
        exact Finset.card_pos.mpr ⟨j.1, j.2⟩)
      ).commRingCatIsoToRingEquiv.trans
        U.topIso.symm.commRingCatIsoToRingEquiv
  change
    e (algebraMap k
        (HomogeneousLocalization.Away
          (homogeneousGrading k d)
          (variableProduct (k := k) I)) r) =
      algebraMapOnOpen (k := k) (X := U.toScheme) ⊤ r
  change
    U.topIso.inv.hom
        ((Proj.basicOpenIsoAway
          (homogeneousGrading k d)
          (variableProduct (k := k) I)
          (variableProduct_mem_degreeCard I)
          (by
            let j : ↥I := Classical.choice inferInstance
            exact Finset.card_pos.mpr ⟨j.1, j.2⟩)
          ).hom.hom
          (algebraMap k
            (HomogeneousLocalization.Away
              (homogeneousGrading k d)
              (variableProduct (k := k) I)) r)) =
      algebraMapOnOpen (k := k) (X := U.toScheme) ⊤ r
  rw [basicOpenIsoAway_hom_algebraMap k d I r]
  exact openSubscheme_topIso_inv_algebraMapOnOpen k d U r

/-- Sections of the structure sheaf on a nonempty standard intersection
are coefficient-linearly equivalent to degree-zero Laurent monomials. -/
noncomputable def standardIntersectionDegreeZeroSectionsLinearEquivOver
    (I : Finset (Fin (d + 1))) [Nonempty ↥I] :
    let U := standardIntersection k (fun i : ↥I => i.1)
    letI : U.toScheme.Over (Spec (CommRingCat.of k)) :=
      ⟨U.ι ≫ toSpec k d⟩
    letI : Module k Γ(U.toScheme, ⊤) :=
      sectionsModule
        (k := k) (SheafOfModules.unit U.toScheme.ringCatSheaf) ⊤
    MonomialModule (ι := Fin (d + 1)) k 0 I ≃ₗ[k]
      Γ(U.toScheme, ⊤) := by
  dsimp only
  let U := standardIntersection k (fun i : ↥I => i.1)
  let V := Proj.basicOpen (homogeneousGrading k d)
    (variableProduct (k := k) I)
  have hUV : U = V := by
    dsimp [U, V, standardIntersection]
    rw [coordinateProduct_subtype_eq_variableProduct k d I]
  let T (W : (scheme k d).Opens) : Type :=
    letI : W.toScheme.Over (Spec (CommRingCat.of k)) :=
      ⟨W.ι ≫ toSpec k d⟩
    letI : Module k Γ(W.toScheme, ⊤) :=
      sectionsModule
        (k := k) (SheafOfModules.unit W.toScheme.ringCatSheaf) ⊤
    MonomialModule (ι := Fin (d + 1)) k 0 I ≃ₗ[k]
      Γ(W.toScheme, ⊤)
  let eV : T V := by
    change
      letI : V.toScheme.Over (Spec (CommRingCat.of k)) :=
        ⟨V.ι ≫ toSpec k d⟩
      letI : Module k Γ(V.toScheme, ⊤) :=
        sectionsModule
          (k := k) (SheafOfModules.unit V.toScheme.ringCatSheaf) ⊤
      MonomialModule (ι := Fin (d + 1)) k 0 I ≃ₗ[k]
        Γ(V.toScheme, ⊤)
    letI : V.toScheme.Over (Spec (CommRingCat.of k)) :=
      ⟨V.ι ≫ toSpec k d⟩
    letI : Module k Γ(V.toScheme, ⊤) :=
      sectionsModule
        (k := k) (SheafOfModules.unit V.toScheme.ringCatSheaf) ⊤
    let e :
        HomogeneousLocalization.Away
            (homogeneousGrading k d) (variableProduct (k := k) I) ≃+*
          Γ(V.toScheme, ⊤) :=
      (Proj.basicOpenIsoAway
        (homogeneousGrading k d)
        (variableProduct (k := k) I)
        (variableProduct_mem_degreeCard I)
        (by
          let j : ↥I := Classical.choice inferInstance
          exact Finset.card_pos.mpr ⟨j.1, j.2⟩)
        ).commRingCatIsoToRingEquiv.trans
          V.topIso.symm.commRingCatIsoToRingEquiv
    let eLinear :
        HomogeneousLocalization.Away
            (homogeneousGrading k d) (variableProduct (k := k) I) ≃ₗ[k]
          Γ(V.toScheme, ⊤) :=
      { e.toAddEquiv with
        map_smul' := fun r x => by
          have hmul :
              e ((algebraMap k
                (HomogeneousLocalization.Away
                  (homogeneousGrading k d)
                  (variableProduct (k := k) I)) r) * x) =
                (algebraMapOnOpen (k := k)
                  (X := V.toScheme) ⊤ r) * e x := by
            rw [map_mul,
              variableProductBasicOpenAwayRingEquiv_algebraMap
                k d I r]
          convert hmul using 1
          · exact congrArg e (Algebra.smul_def r x)
          · change
              (algebraMapOnOpen (k := k)
                (X := V.toScheme) ⊤ ((RingHom.id k) r)) • e x =
                (algebraMapOnOpen (k := k)
                  (X := V.toScheme) ⊤ r) * e x
            rw [RingHom.id_apply, Algebra.smul_def]
            rfl }
    exact
      (degreeZeroFractionLinearEquiv (k := k) I).trans eLinear
  change T U
  exact hUV.symm ▸ eV

/-- Sections of an integer Serre twist on a nonempty standard
intersection are linearly equivalent over the coefficient ring to the
corresponding Laurent monomial module. -/
noncomputable def integerIntersectionLaurentSectionsLinearEquivOver
    (m : ℤ) (I : Finset (Fin (d + 1)))
    [Nonempty ↥I] (j : ↥I) :
    (moduleSheaf
      (k := k) (OInt k d m)).obj.obj
        (op (standardIntersection k
          (fun i : ↥I => i.1))) ≃ₗ[k]
      MonomialModule (ι := Fin (d + 1)) k m I := by
  let U := standardIntersection k (fun i : ↥I => i.1)
  letI : U.toScheme.Over (Spec (CommRingCat.of k)) :=
    ⟨U.ι ≫ toSpec k d⟩
  letI : Module k Γ(U.toScheme, ⊤) :=
    sectionsModule
      (k := k) (SheafOfModules.unit U.toScheme.ringCatSheaf) ⊤
  exact
    (integerIntersectionSectionsLinearEquivOver k d m I j).trans <|
      (standardIntersectionDegreeZeroSectionsLinearEquivOver
        k d I).symm.trans <|
        monomialModuleShiftLinearEquiv I j m

end

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
