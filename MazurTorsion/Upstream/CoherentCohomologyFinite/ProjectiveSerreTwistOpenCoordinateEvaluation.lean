/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveCorrectedChartGlobalMap
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistLaurentRestriction

/-!
# Integer-twist coordinates on arbitrary chart subopens

This file evaluates the slice-site chart trivialization on an arbitrary
open contained in a standard projective chart.
-/

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

variable (k : Type) [CommRing k] (d : ℕ)

/-- The inverse image in a standard chart of an ambient open. -/
def chartPreimageOpen
    (i : Fin (d + 1)) (A : (scheme k d).Opens) :
    (standardChart k i).toScheme.Opens :=
  (standardChart k i).ι ⁻¹ᵁ A

lemma chartPreimageOpen_image
    (i : Fin (d + 1)) (A : (scheme k d).Opens)
    (hA : A ≤ standardChart k i) :
    (standardChart k i).ι ''ᵁ chartPreimageOpen k d i A = A := by
  rw [chartPreimageOpen,
    Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι, inf_eq_right]
  exact hA

/-- The chart coordinate of an integer-twist section on an arbitrary
ambient subopen of that chart. -/
def integerChartAmbientSectionsAddEquiv
    (m : ℤ) (i : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hA : A ≤ standardChart k i) :
    Γ(OInt k d m, A) ≃+ Γ(scheme k d, A) := by
  let C := standardChart k i
  let W := chartPreimageOpen k d i A
  let e : C.ι ''ᵁ W = A :=
    chartPreimageOpen_image k d i A hA
  exact
    ((OInt k d m).presheaf.mapIso
        (eqToIso e).op).addCommGroupIsoToAddEquiv |>.trans
      (((OInt k d m).restrictAppIso C.ι W).symm
        |>.addCommGroupIsoToAddEquiv) |>.trans
      (sectionsAddEquivOfIsoAt
        (integerRestrictionChartIso k d m i) W) |>.trans
      (unitSectionsAddEquivAt C.toScheme W) |>.trans
      ((C.ι.appIso W).symm.commRingCatIsoToRingEquiv.toAddEquiv) |>.trans
      (((scheme k d).presheaf.mapIso
        (eqToIso e).op).symm.commRingCatIsoToRingEquiv.toAddEquiv)

lemma integerOverChartIso_hom_app_eq_ambientCoordinate
    (m : ℤ) (i : Fin (d + 1))
    (V : (Over (standardChart k i))ᵒᵖ)
    (x : (OInt k d m).val.obj (op V.unop.left)) :
    (show Γ(scheme k d, V.unop.left) from
      (integerOverChartIso k d m i).hom.val.app V x) =
      integerChartAmbientSectionsAddEquiv k d m i V.unop.left
        (leOfHom V.unop.hom) x := by
  let output :
      (SheafOfModules.unit
        ((scheme k d).ringCatSheaf.over
          (standardChart k i))).val.obj V →
        Γ(scheme k d, V.unop.left) :=
    fun y => y
  change output ((integerOverChartIso k d m i).hom.val.app V x) = _
  have h := Scheme.Modules.chartOverIso_hom_app
    (standardChart k i) (OInt k d m)
    (integerRestrictionChartIso k d m i) V x
  refine (congrArg output h).trans ?_
  unfold output integerChartAmbientSectionsAddEquiv
  rfl

/-- Integer-twist chart coordinates commute with transport along an
equality of ambient opens. -/
lemma integerChartAmbientSectionsAddEquiv_eqToIso
    (m : ℤ) (i : Fin (d + 1))
    {A B : (scheme k d).Opens} (h : A = B)
    (hAi : A ≤ standardChart k i)
    (hBi : B ≤ standardChart k i)
    (x : Γ(OInt k d m, A)) :
    ((scheme k d).presheaf.mapIso (eqToIso h).op).inv.hom
        (integerChartAmbientSectionsAddEquiv
          k d m i A hAi x) =
      integerChartAmbientSectionsAddEquiv
        k d m i B hBi
        (((OInt k d m).presheaf.mapIso
          (eqToIso h).op).inv.hom x) := by
  cases h
  rw [show hBi = hAi from Subsingleton.elim _ _]
  simp

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
