/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistOpenCoordinateEvaluation

/-!
# Restriction of integer-twist chart coordinates

The chart coordinate of a section of an integer Serre twist commutes with
restriction to every smaller ambient open contained in the same standard
chart.  The statement is valid over an arbitrary commutative base ring.
-/

open CategoryTheory AlgebraicGeometry Opposite


noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

lemma restrictToIntegerChartOpen_naturality
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    (i : Fin (d + 1))
    {A B : (scheme k d).Opens}
    (hBA : B ≤ A)
    (hAi : A ≤ standardChart k i)
    (hBi : B ≤ standardChart k i)
    (x : Γ(OInt k d m, A)) :
    let C := standardChart k i
    let WA := chartPreimageOpen k d i A
    let WB := chartPreimageOpen k d i B
    let hW : WB ≤ WA :=
      Scheme.Hom.preimage_mono C.ι hBA
    let eA : C.ι ''ᵁ WA = A :=
      chartPreimageOpen_image k d i A hAi
    let eB : C.ι ''ᵁ WB = B :=
      chartPreimageOpen_image k d i B hBi
    ((OInt k d m).restrictAppIso C.ι WB).inv.hom
        (((OInt k d m).presheaf.mapIso
          (eqToIso eB).op).hom.hom
          ((OInt k d m).presheaf.map
            (homOfLE hBA).op x)) =
      ((OInt k d m).restrict C.ι).presheaf.map
        (homOfLE hW).op
        (((OInt k d m).restrictAppIso C.ι WA).inv.hom
          (((OInt k d m).presheaf.mapIso
            (eqToIso eA).op).hom.hom x)) := by
  dsimp only
  let C := standardChart k i
  let WA := chartPreimageOpen k d i A
  let WB := chartPreimageOpen k d i B
  let hW : WB ≤ WA :=
    Scheme.Hom.preimage_mono C.ι hBA
  let eA : C.ι ''ᵁ WA = A :=
    chartPreimageOpen_image k d i A hAi
  let eB : C.ι ''ᵁ WB = B :=
    chartPreimageOpen_image k d i B hBi
  have hfront :
      (OInt k d m).presheaf.map (homOfLE hBA).op ≫
          ((OInt k d m).presheaf.mapIso (eqToIso eB).op).hom ≫
          ((OInt k d m).restrictAppIso C.ι WB).inv =
        ((OInt k d m).presheaf.mapIso (eqToIso eA).op).hom ≫
          ((OInt k d m).restrictAppIso C.ι WA).inv ≫
          ((OInt k d m).restrict C.ι).presheaf.map
            (homOfLE hW).op := by
    let himage : C.ι ''ᵁ WB ≤ C.ι ''ᵁ WA :=
      Scheme.Hom.image_mono C.ι hW
    have hopen :
        (homOfLE hBA).op ≫ (eqToIso eB).op.hom =
          (eqToIso eA).op.hom ≫ (homOfLE himage).op :=
      Subsingleton.elim _ _
    have himageMap :
        (OInt k d m).presheaf.map (homOfLE himage).op =
          (OInt k d m).presheaf.map
            (.op <| homOfLE <|
              Scheme.Hom.image_mono C.ι
                (leOfHom ((homOfLE hW).op).unop)) := by
      congr 1
    calc
      _ = (OInt k d m).presheaf.map
            ((homOfLE hBA).op ≫ (eqToIso eB).op.hom) ≫
            ((OInt k d m).restrictAppIso C.ι WB).inv := by
        rw [Functor.map_comp]
        exact (Category.assoc _ _ _).symm
      _ = (OInt k d m).presheaf.map
            ((eqToIso eA).op.hom ≫ (homOfLE himage).op) ≫
            ((OInt k d m).restrictAppIso C.ι WB).inv := by
        rw [hopen]
      _ = ((OInt k d m).presheaf.mapIso
              (eqToIso eA).op).hom ≫
            (OInt k d m).presheaf.map (homOfLE himage).op ≫
              ((OInt k d m).restrictAppIso C.ι WB).inv := by
        rw [Functor.map_comp]
        rfl
      _ = ((OInt k d m).presheaf.mapIso
              (eqToIso eA).op).hom ≫
            ((OInt k d m).restrictAppIso C.ι WA).inv ≫
              ((OInt k d m).restrict C.ι).presheaf.map
                (homOfLE hW).op := by
        rw [himageMap]
        rw [← Scheme.Modules.restrictAppIso_inv_map]
  exact congrArg (fun φ => φ.hom x) hfront

/-- Integer-twist chart coordinates commute with restriction inside one
standard chart. -/
lemma integerChartAmbientSectionsAddEquiv_restriction
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    (i : Fin (d + 1))
    {A B : (scheme k d).Opens}
    (hBA : B ≤ A)
    (hAi : A ≤ standardChart k i)
    (hBi : B ≤ standardChart k i)
    (x : Γ(OInt k d m, A)) :
    integerChartAmbientSectionsAddEquiv
        k d m i B hBi
        ((OInt k d m).presheaf.map (homOfLE hBA).op x) =
      (scheme k d).presheaf.map (homOfLE hBA).op
        (integerChartAmbientSectionsAddEquiv
          k d m i A hAi x) := by
  let C := standardChart k i
  let WA := chartPreimageOpen k d i A
  let WB := chartPreimageOpen k d i B
  let hW : WB ≤ WA :=
    Scheme.Hom.preimage_mono C.ι hBA
  let eA : C.ι ''ᵁ WA = A :=
    chartPreimageOpen_image k d i A hAi
  let eB : C.ι ''ᵁ WB = B :=
    chartPreimageOpen_image k d i B hBi
  let yA : Γ((OInt k d m).restrict C.ι, WA) :=
    ((OInt k d m).restrictAppIso C.ι WA).inv.hom <|
      ((OInt k d m).presheaf.mapIso
        (eqToIso eA).op).hom.hom x
  let yB : Γ((OInt k d m).restrict C.ι, WB) :=
    ((OInt k d m).restrictAppIso C.ι WB).inv.hom <|
      ((OInt k d m).presheaf.mapIso
        (eqToIso eB).op).hom.hom <|
        ((OInt k d m).presheaf.map (homOfLE hBA).op x)
  have hy :
      yB =
        ((OInt k d m).restrict C.ι).presheaf.map
          (homOfLE hW).op yA :=
    restrictToIntegerChartOpen_naturality
      k d m i hBA hAi hBi x
  let zA : Γ(C.toScheme, WA) :=
    sectionsAddEquivOfIsoAt
      (integerRestrictionChartIso k d m i) WA yA
  let zB : Γ(C.toScheme, WB) :=
    sectionsAddEquivOfIsoAt
      (integerRestrictionChartIso k d m i) WB yB
  have hz :
      zB = C.toScheme.presheaf.map
        (homOfLE hW).op zA := by
    dsimp only [zB, zA]
    rw [hy]
    exact sectionsAddEquivOfIsoAt_restriction
      (integerRestrictionChartIso k d m i) hW yA
  let wA : Γ(scheme k d, C.ι ''ᵁ WA) :=
    (C.ι.appIso WA).inv.hom zA
  let wB : Γ(scheme k d, C.ι ''ᵁ WB) :=
    (C.ι.appIso WB).inv.hom zB
  have hw :
      wB = (scheme k d).presheaf.map
        (homOfLE (Scheme.Hom.image_mono C.ι hW)).op wA := by
    dsimp only [wB, wA]
    rw [hz]
    exact appIso_inv_restriction C.ι hW zA
  let vA : Γ(scheme k d, A) :=
    ((scheme k d).presheaf.mapIso
      (eqToIso eA).op).inv.hom wA
  let vB : Γ(scheme k d, B) :=
    ((scheme k d).presheaf.mapIso
      (eqToIso eB).op).inv.hom wB
  have hv :
      vB = (scheme k d).presheaf.map
        (homOfLE hBA).op vA := by
    dsimp only [vB, vA]
    rw [hw]
    exact presheafMapIsoSymm_restriction
      eA eB (Scheme.Hom.image_mono C.ι hW) hBA wA
  change vB =
    (scheme k d).presheaf.map (homOfLE hBA).op vA
  exact hv

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
