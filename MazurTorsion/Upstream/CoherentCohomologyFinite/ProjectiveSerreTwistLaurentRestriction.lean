/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentGeometricRestriction

open CategoryTheory AlgebraicGeometry
open scoped BigOperators


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleIsoSections

noncomputable section

abbrev standardFinsetIntersection
    (k : Type) [CommRing k] (d : ℕ)
    (I : Finset (Fin (d + 1))) :
    (scheme k d).Opens :=
  standardIntersection k (fun i : ↥I => i.1)

lemma standardFinsetIntersection_eq_laurentOpen
    (k : Type) [CommRing k] (d : ℕ)
    (I : Finset (Fin (d + 1))) :
    standardFinsetIntersection k d I = laurentOpen k d I := by
  unfold standardFinsetIntersection standardIntersection laurentOpen
  rw [coordinateProduct_subtype_eq_variableProduct]

lemma standardFinsetIntersection_mono
    (k : Type) [CommRing k] (d : ℕ)
    {I J : Finset (Fin (d + 1))} (hIJ : I ⊆ J) :
    standardFinsetIntersection k d J ≤
      standardFinsetIntersection k d I := by
  rw [standardFinsetIntersection_eq_laurentOpen,
    standardFinsetIntersection_eq_laurentOpen]
  exact laurentOpen_mono k d hIJ

def integerIntersectionAmbientSectionsAddEquiv
    (d : ℕ) (m : ℤ) (I : Finset (Fin (d + 1)))
    [Nonempty ↥I] (j : ↥I) :
    Γ(OInt ℚ d m, standardFinsetIntersection ℚ d I) ≃+
      Γ(scheme ℚ d, standardFinsetIntersection ℚ d I) :=
  (integerIntersectionSectionsAddEquiv d m I j).trans
    (Scheme.Opens.topIso
      (standardFinsetIntersection ℚ d I)).commRingCatIsoToRingEquiv.toAddEquiv

lemma laurentOpen_le_standardChart
    (k : Type) [CommRing k] (d : ℕ)
    (I : Finset (Fin (d + 1))) (j : ↥I) :
    laurentOpen k d I ≤ standardChart k j.1 := by
  rw [← standardFinsetIntersection_eq_laurentOpen]
  exact standardIntersection_le_chart
    k d (fun i : ↥I => i.1) j

def chartPreimageLaurentOpen
    (k : Type) [CommRing k] (d : ℕ)
    (I : Finset (Fin (d + 1))) (j : ↥I) :
    (standardChart k j.1).toScheme.Opens :=
  (standardChart k j.1).ι ⁻¹ᵁ laurentOpen k d I

lemma chartPreimageLaurentOpen_image
    (k : Type) [CommRing k] (d : ℕ)
    (I : Finset (Fin (d + 1))) (j : ↥I) :
    (standardChart k j.1).ι ''ᵁ
        chartPreimageLaurentOpen k d I j =
      laurentOpen k d I := by
  rw [chartPreimageLaurentOpen,
    Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι, inf_eq_right]
  exact laurentOpen_le_standardChart k d I j

def sectionsAddEquivOfIsoAt
    {X : Scheme} {M N : X.Modules}
    (e : M ≅ N) (U : X.Opens) :
    Γ(M, U) ≃+ Γ(N, U) where
  toFun := e.hom.app U
  invFun := e.inv.app U
  left_inv x := by
    change (e.hom ≫ e.inv).app U x = x
    rw [e.hom_inv_id]
    rfl
  right_inv x := by
    change (e.inv ≫ e.hom).app U x = x
    rw [e.inv_hom_id]
    rfl
  map_add' x y := map_add _ x y

lemma sectionsAddEquivOfIsoAt_restriction
    {X : Scheme} {M N : X.Modules}
    (e : M ≅ N) {U V : X.Opens} (hVU : V ≤ U)
    (x : Γ(M, U)) :
    sectionsAddEquivOfIsoAt e V
        (M.presheaf.map (homOfLE hVU).op x) =
      N.presheaf.map (homOfLE hVU).op
        (sectionsAddEquivOfIsoAt e U x) := by
  exact congrArg (fun φ => φ.hom x)
    (e.hom.mapPresheaf.naturality (homOfLE hVU).op)

def integerChartRestrictIso
    (d : ℕ) (m : ℤ) (i : Fin (d + 1)) :
    (OInt ℚ d m).restrict (standardChart ℚ i).ι ≅
      SheafOfModules.unit
        (standardChart ℚ i).toScheme.ringCatSheaf :=
  (Scheme.Modules.restrictFunctorIsoPullback
      (standardChart ℚ i).ι).app (OInt ℚ d m) ≪≫
    integerChartIso ℚ d m i

def unitSectionsAddEquivAt (X : Scheme) (U : X.Opens) :
    Γ(SheafOfModules.unit X.ringCatSheaf, U) ≃+
      Γ(X, U) :=
  AddEquiv.refl _

def integerChartLaurentSectionsAddEquiv
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (j : ↥I) :
    Γ(OInt ℚ d m, laurentOpen ℚ d I) ≃+
      Γ(scheme ℚ d, laurentOpen ℚ d I) := by
  let C := standardChart ℚ j.1
  let W := chartPreimageLaurentOpen ℚ d I j
  let e : C.ι ''ᵁ W = laurentOpen ℚ d I :=
    chartPreimageLaurentOpen_image ℚ d I j
  exact
    ((OInt ℚ d m).presheaf.mapIso
        (eqToIso e).op).addCommGroupIsoToAddEquiv |>.trans
      (((OInt ℚ d m).restrictAppIso C.ι W).symm
        |>.addCommGroupIsoToAddEquiv) |>.trans
      (sectionsAddEquivOfIsoAt
        (integerChartRestrictIso d m j.1) W) |>.trans
      (unitSectionsAddEquivAt C.toScheme W) |>.trans
      ((C.ι.appIso W).symm.commRingCatIsoToRingEquiv.toAddEquiv) |>.trans
      (((scheme ℚ d).presheaf.mapIso
        (eqToIso e).op).symm.commRingCatIsoToRingEquiv.toAddEquiv)

lemma restrictToIntegerChart_naturality
    (d : ℕ) (m : ℤ)
    {I J : Finset (Fin (d + 1))}
    (hIJ : I ⊆ J) (j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    let C := standardChart ℚ j.1
    let jJ : ↥J := ⟨j.1, hIJ j.2⟩
    let WI := chartPreimageLaurentOpen ℚ d I j
    let WJ := chartPreimageLaurentOpen ℚ d J jJ
    let hW : WJ ≤ WI :=
      Scheme.Hom.preimage_mono C.ι
        (laurentOpen_mono ℚ d hIJ)
    let eI : C.ι ''ᵁ WI = laurentOpen ℚ d I :=
      chartPreimageLaurentOpen_image ℚ d I j
    let eJ : C.ι ''ᵁ WJ = laurentOpen ℚ d J :=
      chartPreimageLaurentOpen_image ℚ d J jJ
    ((OInt ℚ d m).restrictAppIso C.ι WJ).inv.hom
        (((OInt ℚ d m).presheaf.mapIso
          (eqToIso eJ).op).hom.hom
          ((OInt ℚ d m).presheaf.map
            (homOfLE (laurentOpen_mono ℚ d hIJ)).op x)) =
      ((OInt ℚ d m).restrict C.ι).presheaf.map
        (homOfLE hW).op
        (((OInt ℚ d m).restrictAppIso C.ι WI).inv.hom
          (((OInt ℚ d m).presheaf.mapIso
            (eqToIso eI).op).hom.hom x)) := by
  dsimp only
  let C := standardChart ℚ j.1
  let jJ : ↥J := ⟨j.1, hIJ j.2⟩
  let WI := chartPreimageLaurentOpen ℚ d I j
  let WJ := chartPreimageLaurentOpen ℚ d J jJ
  let hW : WJ ≤ WI :=
    Scheme.Hom.preimage_mono C.ι
      (laurentOpen_mono ℚ d hIJ)
  let eI : C.ι ''ᵁ WI = laurentOpen ℚ d I :=
    chartPreimageLaurentOpen_image ℚ d I j
  let eJ : C.ι ''ᵁ WJ = laurentOpen ℚ d J :=
    chartPreimageLaurentOpen_image ℚ d J jJ
  have hfront :
      (OInt ℚ d m).presheaf.map
          (homOfLE (laurentOpen_mono ℚ d hIJ)).op ≫
        ((OInt ℚ d m).presheaf.mapIso (eqToIso eJ).op).hom ≫
        ((OInt ℚ d m).restrictAppIso C.ι WJ).inv =
      ((OInt ℚ d m).presheaf.mapIso (eqToIso eI).op).hom ≫
        ((OInt ℚ d m).restrictAppIso C.ι WI).inv ≫
        ((OInt ℚ d m).restrict C.ι).presheaf.map
          (homOfLE hW).op := by
    let himage : C.ι ''ᵁ WJ ≤ C.ι ''ᵁ WI :=
      Scheme.Hom.image_mono C.ι hW
    have hopen :
        (homOfLE (laurentOpen_mono ℚ d hIJ)).op ≫
            (eqToIso eJ).op.hom =
          (eqToIso eI).op.hom ≫
            (homOfLE himage).op :=
      Subsingleton.elim _ _
    have himageMap :
        (OInt ℚ d m).presheaf.map
            (homOfLE himage).op =
          (OInt ℚ d m).presheaf.map
            (.op <| homOfLE <|
              Scheme.Hom.image_mono C.ι
                (leOfHom ((homOfLE hW).op).unop)) := by
      congr 1
    calc
      _ = (OInt ℚ d m).presheaf.map
            ((homOfLE (laurentOpen_mono ℚ d hIJ)).op ≫
              (eqToIso eJ).op.hom) ≫
            ((OInt ℚ d m).restrictAppIso C.ι WJ).inv := by
        rw [Functor.map_comp]
        exact (Category.assoc _ _ _).symm
      _ = (OInt ℚ d m).presheaf.map
            ((eqToIso eI).op.hom ≫
              (homOfLE himage).op) ≫
            ((OInt ℚ d m).restrictAppIso C.ι WJ).inv := by
        rw [hopen]
      _ = ((OInt ℚ d m).presheaf.mapIso
              (eqToIso eI).op).hom ≫
            (OInt ℚ d m).presheaf.map
                (homOfLE himage).op ≫
              ((OInt ℚ d m).restrictAppIso C.ι WJ).inv := by
        rw [Functor.map_comp]
        rfl
      _ = ((OInt ℚ d m).presheaf.mapIso
              (eqToIso eI).op).hom ≫
            ((OInt ℚ d m).restrictAppIso C.ι WI).inv ≫
              ((OInt ℚ d m).restrict C.ι).presheaf.map
                (homOfLE hW).op := by
        rw [himageMap]
        rw [← Scheme.Modules.restrictAppIso_inv_map]
  exact congrArg (fun φ => φ.hom x) hfront

lemma appIso_inv_restriction
    {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    {U V : X.Opens} (hVU : V ≤ U)
    (x : Γ(X, U)) :
    (f.appIso V).inv.hom
        (X.presheaf.map (homOfLE hVU).op x) =
      Y.presheaf.map
          (homOfLE (Scheme.Hom.image_mono f hVU)).op
        ((f.appIso U).inv.hom x) := by
  have hnat :=
    f.appIso_inv_naturality (homOfLE hVU).op
  have himage :
      f.opensFunctor.op.map (homOfLE hVU).op =
        (homOfLE (Scheme.Hom.image_mono f hVU)).op :=
    Subsingleton.elim _ _
  rw [himage] at hnat
  exact congrArg (fun φ => φ.hom x) hnat

lemma presheafMapIsoSymm_restriction
    {X : Scheme} {AI AJ UI UJ : X.Opens}
    (eI : AI = UI) (eJ : AJ = UJ)
    (hA : AJ ≤ AI) (hU : UJ ≤ UI)
    (x : Γ(X, AI)) :
    (X.presheaf.mapIso (eqToIso eJ).op).inv.hom
        (X.presheaf.map (homOfLE hA).op x) =
      X.presheaf.map (homOfLE hU).op
        ((X.presheaf.mapIso (eqToIso eI).op).inv.hom x) := by
  have hmaps :
      X.presheaf.map (homOfLE hA).op ≫
          (X.presheaf.mapIso (eqToIso eJ).op).inv =
        (X.presheaf.mapIso (eqToIso eI).op).inv ≫
          X.presheaf.map (homOfLE hU).op := by
    rw [Functor.mapIso_inv, Functor.mapIso_inv,
      ← Functor.map_comp, ← Functor.map_comp]
    congr 1
  exact congrArg (fun φ => φ.hom x) hmaps

lemma integerChartLaurentSectionsAddEquiv_restriction
    (d : ℕ) (m : ℤ)
    {I J : Finset (Fin (d + 1))}
    (hIJ : I ⊆ J) (j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    integerChartLaurentSectionsAddEquiv
        d m J ⟨j.1, hIJ j.2⟩
        ((OInt ℚ d m).presheaf.map
          (homOfLE (laurentOpen_mono ℚ d hIJ)).op x) =
      (scheme ℚ d).presheaf.map
        (homOfLE (laurentOpen_mono ℚ d hIJ)).op
        (integerChartLaurentSectionsAddEquiv d m I j x) := by
  let C := standardChart ℚ j.1
  let jJ : ↥J := ⟨j.1, hIJ j.2⟩
  let WI := chartPreimageLaurentOpen ℚ d I j
  let WJ := chartPreimageLaurentOpen ℚ d J jJ
  let hW : WJ ≤ WI :=
    Scheme.Hom.preimage_mono C.ι
      (laurentOpen_mono ℚ d hIJ)
  let eI : C.ι ''ᵁ WI = laurentOpen ℚ d I :=
    chartPreimageLaurentOpen_image ℚ d I j
  let eJ : C.ι ''ᵁ WJ = laurentOpen ℚ d J :=
    chartPreimageLaurentOpen_image ℚ d J jJ
  let yI : Γ((OInt ℚ d m).restrict C.ι, WI) :=
    ((OInt ℚ d m).restrictAppIso C.ι WI).inv.hom <|
      ((OInt ℚ d m).presheaf.mapIso
        (eqToIso eI).op).hom.hom x
  let yJ : Γ((OInt ℚ d m).restrict C.ι, WJ) :=
    ((OInt ℚ d m).restrictAppIso C.ι WJ).inv.hom <|
      ((OInt ℚ d m).presheaf.mapIso
        (eqToIso eJ).op).hom.hom <|
        ((OInt ℚ d m).presheaf.map
          (homOfLE (laurentOpen_mono ℚ d hIJ)).op x)
  have hy :
      yJ =
        ((OInt ℚ d m).restrict C.ι).presheaf.map
          (homOfLE hW).op yI :=
    restrictToIntegerChart_naturality d m hIJ j x
  let zI : Γ(C.toScheme, WI) :=
    sectionsAddEquivOfIsoAt
      (integerChartRestrictIso d m j.1) WI yI
  let zJ : Γ(C.toScheme, WJ) :=
    sectionsAddEquivOfIsoAt
      (integerChartRestrictIso d m j.1) WJ yJ
  have hz :
      zJ = C.toScheme.presheaf.map
        (homOfLE hW).op zI := by
    dsimp only [zJ, zI]
    rw [hy]
    exact sectionsAddEquivOfIsoAt_restriction
      (integerChartRestrictIso d m j.1) hW yI
  let wI : Γ(scheme ℚ d, C.ι ''ᵁ WI) :=
    (C.ι.appIso WI).inv.hom zI
  let wJ : Γ(scheme ℚ d, C.ι ''ᵁ WJ) :=
    (C.ι.appIso WJ).inv.hom zJ
  have hw :
      wJ = (scheme ℚ d).presheaf.map
        (homOfLE (Scheme.Hom.image_mono C.ι hW)).op wI := by
    dsimp only [wJ, wI]
    rw [hz]
    exact appIso_inv_restriction C.ι hW zI
  let vI : Γ(scheme ℚ d, laurentOpen ℚ d I) :=
    ((scheme ℚ d).presheaf.mapIso
      (eqToIso eI).op).inv.hom wI
  let vJ : Γ(scheme ℚ d, laurentOpen ℚ d J) :=
    ((scheme ℚ d).presheaf.mapIso
      (eqToIso eJ).op).inv.hom wJ
  have hv :
      vJ = (scheme ℚ d).presheaf.map
        (homOfLE (laurentOpen_mono ℚ d hIJ)).op vI := by
    dsimp only [vJ, vI]
    rw [hw]
    exact presheafMapIsoSymm_restriction
      eI eJ (Scheme.Hom.image_mono C.ι hW)
      (laurentOpen_mono ℚ d hIJ) wI
  change vJ =
    (scheme ℚ d).presheaf.map
      (homOfLE (laurentOpen_mono ℚ d hIJ)).op vI
  exact hv

end
end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
