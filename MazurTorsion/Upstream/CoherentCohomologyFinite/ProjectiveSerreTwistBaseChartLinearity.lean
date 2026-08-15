/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistBaseChartCoordinates

/-!
# Base linearity of integer-twist chart coordinates

The standard-chart trivialization of an integer Serre twist respects the
structural coefficient action.  Consequently the chart-independent
Laurent coordinate is a linear equivalence over the coefficient ring.
-/

open CategoryTheory AlgebraicGeometry Opposite


noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

local instance projectiveSpaceOverCoefficientRingForChartLinearity
    (k : Type) [CommRing k] (d : ℕ) :
    (scheme k d).Over (Spec (CommRingCat.of k)) :=
  ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec k d⟩

/-- A selected-chart coordinate respects multiplication of a twist
section by an ambient regular function. -/
lemma integerChartAmbientSectionsAddEquiv_smul
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    (i : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (a : Γ(scheme k d, A))
    (x : Γ(OInt k d m, A)) :
    integerChartAmbientSectionsAddEquiv
        k d m i A hAi (a • x) =
      a * integerChartAmbientSectionsAddEquiv
        k d m i A hAi x := by
  let C := standardChart k i
  let W := chartPreimageOpen k d i A
  let e : C.ι ''ᵁ W = A :=
    chartPreimageOpen_image k d i A hAi
  let aW : Γ(C.toScheme, W) :=
    (C.ι.appIso W).hom.hom
      (((scheme k d).presheaf.mapIso
        (eqToIso e).op).hom.hom a)
  let y : Γ((OInt k d m).restrict C.ι, W) :=
    ((OInt k d m).restrictAppIso C.ι W).inv.hom
      (((OInt k d m).presheaf.mapIso
        (eqToIso e).op).hom.hom x)
  let z : Γ(C.toScheme, W) :=
    (integerRestrictionChartIso k d m i).hom.app W y
  have hy :
      ((OInt k d m).restrictAppIso C.ι W).inv.hom
          (((OInt k d m).presheaf.mapIso
            (eqToIso e).op).hom.hom (a • x)) =
        aW • y := by
    change
      ((OInt k d m).restrictAppIso C.ι W).inv.hom
          ((OInt k d m).presheaf.map (eqToHom e).op
            (a • x)) =
        aW • y
    rw [(OInt k d m).map_smul]
    rw [Scheme.Modules.smul_restrictAppIso_inv_apply]
    rfl
  have hz :
      (show Γ(C.toScheme, W) from
        (integerRestrictionChartIso k d m i).hom.app W
          (aW • y)) =
        aW • z := by
    exact Scheme.Modules.Hom.app_smul
      (integerRestrictionChartIso k d m i).hom aW y
  change
    ((scheme k d).presheaf.mapIso
        (eqToIso e).op).inv.hom
      ((C.ι.appIso W).inv.hom
        ((integerRestrictionChartIso k d m i).hom.app W
          (((OInt k d m).restrictAppIso C.ι W).inv.hom
            (((OInt k d m).presheaf.mapIso
              (eqToIso e).op).hom.hom (a • x))))) =
      a *
        ((scheme k d).presheaf.mapIso
          (eqToIso e).op).inv.hom
          ((C.ι.appIso W).inv.hom z)
  rw [hy]
  calc
    _ =
        ((scheme k d).presheaf.mapIso
          (eqToIso e).op).inv.hom
          ((C.ι.appIso W).inv.hom (aW • z)) := by
      exact congrArg
        (fun q : Γ(C.toScheme, W) =>
          ((scheme k d).presheaf.mapIso
            (eqToIso e).op).inv.hom
            ((C.ι.appIso W).inv.hom q)) hz
    _ = a *
        ((scheme k d).presheaf.mapIso
          (eqToIso e).op).inv.hom
          ((C.ι.appIso W).inv.hom z) := by
      change
        (scheme k d).presheaf.map (eqToHom e.symm).op
            ((C.ι.appIso W).inv.hom
              (aW * z)) =
          a *
            (scheme k d).presheaf.map (eqToHom e.symm).op
              ((C.ι.appIso W).inv.hom z)
      rw [map_mul, map_mul]
      apply congrArg (fun q => q *
        (scheme k d).presheaf.map (eqToHom e.symm).op
          ((C.ι.appIso W).inv.hom z))
      dsimp only [aW]
      change
        ((scheme k d).presheaf.mapIso
          (eqToIso e).op).inv.hom
            ((C.ι.appIso W).inv.hom
              ((C.ι.appIso W).hom.hom
                (((scheme k d).presheaf.mapIso
                  (eqToIso e).op).hom.hom a))) =
          a
      rw [Iso.hom_inv_id_apply]
      rw [Iso.hom_inv_id_apply]

/-- The chart coordinate, degree-zero Laurent conversion, and degree
shift as one additive equivalence. -/
noncomputable def integerChartLaurentSectionsAddEquivOver
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (j : ↥I) :
    Γ(OInt k d m, laurentOpen k d I) ≃+
      MonomialModule (ι := Fin (d + 1)) k m I := by
  letI : Nonempty ↥I := ⟨j⟩
  letI : Module k Γ(scheme k d, laurentOpen k d I) :=
    sectionsModule
      (k := k) (SheafOfModules.unit (scheme k d).ringCatSheaf)
      (laurentOpen k d I)
  exact
    (integerChartAmbientSectionsAddEquiv
      k d m j.1 (laurentOpen k d I)
      (laurentOpen_le_standardChart k d I j)).trans <|
      (degreeZeroAmbientSectionsLinearEquivOver
        k d I).symm.toAddEquiv.trans <|
        (monomialModuleShiftLinearEquiv
          (k := k) I j m).toAddEquiv

@[simp]
lemma integerChartLaurentSectionsAddEquivOver_apply
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (j : ↥I)
    (x : Γ(OInt k d m, laurentOpen k d I)) :
    integerChartLaurentSectionsAddEquivOver
        k d m I j x =
      integerChartLaurentCoordinateOver k d m I j x :=
  rfl

/-- The selected-chart Laurent equivalence respects structural
coefficient scalars. -/
lemma integerChartLaurentSectionsAddEquivOver_map_smul
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (j : ↥I)
    (r : k)
    (x : (moduleSheaf (k := k) (OInt k d m)).obj.obj
      (op (laurentOpen k d I))) :
    integerChartLaurentSectionsAddEquivOver
        k d m I j (r • x) =
      r • integerChartLaurentSectionsAddEquivOver
        k d m I j x := by
  letI : Nonempty ↥I := ⟨j⟩
  letI : Module k Γ(scheme k d, laurentOpen k d I) :=
    sectionsModule
      (k := k) (SheafOfModules.unit (scheme k d).ringCatSheaf)
      (laurentOpen k d I)
  change
    monomialModuleShiftLinearEquiv (k := k) I j m
        ((degreeZeroAmbientSectionsLinearEquivOver
          k d I).symm.toFun
          (integerChartAmbientSectionsAddEquiv
            k d m j.1 (laurentOpen k d I)
            (laurentOpen_le_standardChart k d I j)
            ((algebraMapOnOpen
              (k := k) (laurentOpen k d I) r) •
                (show Γ(OInt k d m, laurentOpen k d I)
                  from x)))) =
      r •
        monomialModuleShiftLinearEquiv (k := k) I j m
          ((degreeZeroAmbientSectionsLinearEquivOver
            k d I).symm.toFun
            (integerChartAmbientSectionsAddEquiv
              k d m j.1 (laurentOpen k d I)
              (laurentOpen_le_standardChart k d I j) x))
  rw [integerChartAmbientSectionsAddEquiv_smul]
  let s : Γ(scheme k d, laurentOpen k d I) :=
    integerChartAmbientSectionsAddEquiv
      k d m j.1 (laurentOpen k d I)
      (laurentOpen_le_standardChart k d I j) x
  let e₀ := (degreeZeroAmbientSectionsLinearEquivOver k d I).symm
  let eₘ := monomialModuleShiftLinearEquiv (k := k) I j m
  change eₘ.toFun (e₀.toFun (r • s)) =
    r • eₘ.toFun (e₀.toFun s)
  calc
    _ = eₘ.toFun (r • e₀.toFun s) := by
      exact congrArg eₘ.toFun (e₀.map_smul r s)
    _ = _ := eₘ.map_smul r (e₀.toFun s)

/-- The chart-independent Laurent description as a coefficient-linear
equivalence. -/
noncomputable def integerChartLaurentSectionsLinearEquivOver
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (j : ↥I) :
    (moduleSheaf (k := k) (OInt k d m)).obj.obj
        (op (laurentOpen k d I)) ≃ₗ[k]
      MonomialModule (ι := Fin (d + 1)) k m I := by
  let e := integerChartLaurentSectionsAddEquivOver
    k d m I j
  exact
    { e with
      map_smul' :=
        integerChartLaurentSectionsAddEquivOver_map_smul
          k d m I j }

@[simp]
lemma integerChartLaurentSectionsLinearEquivOver_apply
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (j : ↥I)
    (x : (moduleSheaf (k := k) (OInt k d m)).obj.obj
      (op (laurentOpen k d I))) :
    integerChartLaurentSectionsLinearEquivOver
        k d m I j x =
      integerChartLaurentCoordinateOver k d m I j x :=
  rfl

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
