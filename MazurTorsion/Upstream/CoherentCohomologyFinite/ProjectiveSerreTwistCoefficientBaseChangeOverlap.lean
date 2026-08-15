/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistCoefficientOverlap
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveStandardCoverCoefficientBaseChange
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverIsoOverlap

/-!
# Coefficient extension on relative projective overlaps

For a morphism into projective space after coefficient extension, the
canonical isomorphism of pulled-back standard covers identifies the direct
map to the old standard overlap with the route through the new standard
overlap and coefficient extension.
-/


open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
open AlgebraicGeometry.Scheme.Cover

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R]
variable (d : ℕ) {Y : Scheme} (g : Y ⟶ scheme R d)

/--
The coefficient-change cover isomorphism intertwines the two maps from a
relative pair overlap to the standard overlap over the original ring.
-/
theorem coefficientBaseChangeOverlapMap_comp_coefficientOverlapMap
    (i j : Fin (d + 1)) :
    coverIsoOverlapMap
          (coefficientBaseChangeStandardCoverIso d g) i j ≫
        baseChangeOverlapMap (cover R d) g i j ≫
        coefficientOverlapMap (algebraMap k R) d i j =
      baseChangeOverlapMap (cover k d)
        (g ≫ coefficientMap (algebraMap k R) d) i j := by
  let 𝒱k := (cover k d).pullback₁
    (g ≫ coefficientMap (algebraMap k R) d)
  let 𝒱R := (cover R d).pullback₁ g
  let a : (gluedCover 𝒱k).V (i, j) ⟶
      (gluedCover 𝒱R).V (i, j) :=
    coverIsoOverlapMap
      (coefficientBaseChangeStandardCoverIso d g) i j
  let bR : (gluedCover 𝒱R).V (i, j) ⟶
      (cover R d).gluedCover.V (i, j) :=
    baseChangeOverlapMap (cover R d) g i j
  let c : (cover R d).gluedCover.V (i, j) ⟶
      (cover k d).gluedCover.V (i, j) :=
    coefficientOverlapMap (algebraMap k R) d i j
  let bK : (gluedCover 𝒱k).V (i, j) ⟶
      (cover k d).gluedCover.V (i, j) :=
    baseChangeOverlapMap (cover k d)
      (g ≫ coefficientMap (algebraMap k R) d) i j
  let E : (cover k d).gluedCover.V (i, j) ≅
      (Proj.basicOpen (homogeneousGrading k d)
        (coordinate k i * coordinate k j)).toScheme :=
    openOverlapToBasicOpenIso k d i j
  let oK : (cover k d).gluedCover.V (i, j) ⟶
      (Proj.basicOpen (homogeneousGrading k d)
        (coordinate k i * coordinate k j)).toScheme :=
    overlapHom k d i j
  let oR : (cover R d).gluedCover.V (i, j) ⟶
      (Proj.basicOpen (homogeneousGrading R d)
        (coordinate R i * coordinate R j)).toScheme :=
    overlapHom R d i j
  let q :
      (Proj.basicOpen (homogeneousGrading R d)
        (coordinate R i * coordinate R j)).toScheme ⟶
      (Proj.basicOpen (homogeneousGrading k d)
        (coordinate k i * coordinate k j)).toScheme :=
    coefficientPairBasicOpenMap (algebraMap k R) d i j
  have hE : E.hom = oK := openOverlapToBasicOpenIso_hom k d i j
  have hc : c ≫ oK = oR ≫ q :=
    coefficientOverlapMap_comp_overlapHom
      (algebraMap k R) d i j
  change a ≫ bR ≫ c = bK
  apply (cancel_mono E.hom).mp
  rw [hE]
  calc
    (a ≫ bR ≫ c) ≫ oK =
        (a ≫ bR) ≫ (c ≫ oK) := Category.assoc _ _ _
    _ = (a ≫ bR) ≫ (oR ≫ q) :=
      congrArg (fun z => (a ≫ bR) ≫ z) hc
    _ = ((a ≫ bR) ≫ oR) ≫ q :=
      (Category.assoc _ _ _).symm
    _ = bK ≫ oK := by
      let BR := Proj.basicOpen (homogeneousGrading R d)
        (coordinate R i * coordinate R j)
      let BK := Proj.basicOpen (homogeneousGrading k d)
        (coordinate k i * coordinate k j)
      let ιR : BR.toScheme ⟶ scheme R d := BR.ι
      let ιK : BK.toScheme ⟶ scheme k d := BK.ι
      let m : scheme R d ⟶ scheme k d :=
        coefficientMap (algebraMap k R) d
      let pR : (cover R d).gluedCover.V (i, j) ⟶
          (cover R d).X i := overlapFst (cover R d) i j
      let pK : (cover k d).gluedCover.V (i, j) ⟶
          (cover k d).X i := overlapFst (cover k d) i j
      let pᵥR : (gluedCover 𝒱R).V (i, j) ⟶
          𝒱R.X i := overlapFst 𝒱R i j
      let pᵥK : (gluedCover 𝒱k).V (i, j) ⟶
          𝒱k.X i := overlapFst 𝒱k i j
      let rR : 𝒱R.X i ⟶ (cover R d).X i :=
        (cover R d).pullbackHom g i
      let rK : 𝒱k.X i ⟶ (cover k d).X i :=
        (cover k d).pullbackHom
          (g ≫ coefficientMap (algebraMap k R) d) i
      let uR : (cover R d).X i ⟶ scheme R d :=
        (cover R d).f i
      let uK : (cover k d).X i ⟶ scheme k d :=
        (cover k d).f i
      let uᵥR : 𝒱R.X i ⟶ Y := 𝒱R.f i
      let uᵥK : 𝒱k.X i ⟶ Y := 𝒱k.f i
      let eI : 𝒱k.X i ≅ 𝒱R.X i :=
        coefficientBaseChangeStandardChartIso d g i
      have hq : q ≫ ιK = ιR ≫ m := by
        dsimp only [q, ιK, ιR, m,
          coefficientPairBasicOpenMap, BK, BR]
        exact Scheme.Hom.resLE_comp_ι _ _
      have hoR : oR ≫ ιR = pR ≫ uR := by
        exact overlapHom_comp_ι R d i j
      have hoK : oK ≫ ιK = pK ≫ uK := by
        exact overlapHom_comp_ι k d i j
      have hbR : bR ≫ pR = pᵥR ≫ rR :=
        baseChangeOverlapMap_overlapFst (cover R d) g i j
      have hbK : bK ≫ pK = pᵥK ≫ rK :=
        baseChangeOverlapMap_overlapFst (cover k d)
          (g ≫ coefficientMap (algebraMap k R) d) i j
      have hrR : rR ≫ uR = uᵥR ≫ g :=
        Scheme.Cover.pullbackHom_map (cover R d) g i
      have hrK : rK ≫ uK =
          uᵥK ≫ (g ≫ m) :=
        Scheme.Cover.pullbackHom_map (cover k d)
          (g ≫ coefficientMap (algebraMap k R) d) i
      have ha : a ≫ pᵥR = pᵥK ≫ eI.hom := by
        simpa only [
          coefficientBaseChangeStandardCoverIso_hom_s₀,
          coefficientBaseChangeStandardCoverIso_hom_h₀] using
          coverIsoOverlapMap_overlapFst
            (coefficientBaseChangeStandardCoverIso d g) i j
      have he : eI.hom ≫ uᵥR = uᵥK :=
        coefficientBaseChangeStandardChartIso_hom_coverMap d g i
      have hBR : bR ≫ (pR ≫ uR) =
          pᵥR ≫ (uᵥR ≫ g) := by
        calc
          bR ≫ (pR ≫ uR) = (bR ≫ pR) ≫ uR :=
            (Category.assoc _ _ _).symm
          _ = (pᵥR ≫ rR) ≫ uR :=
            congrArg (fun z => z ≫ uR) hbR
          _ = pᵥR ≫ (rR ≫ uR) := Category.assoc _ _ _
          _ = pᵥR ≫ (uᵥR ≫ g) :=
            congrArg (fun z => pᵥR ≫ z) hrR
      have hBK : bK ≫ (pK ≫ uK) =
          pᵥK ≫ (uᵥK ≫ (g ≫ m)) := by
        calc
          bK ≫ (pK ≫ uK) = (bK ≫ pK) ≫ uK :=
            (Category.assoc _ _ _).symm
          _ = (pᵥK ≫ rK) ≫ uK :=
            congrArg (fun z => z ≫ uK) hbK
          _ = pᵥK ≫ (rK ≫ uK) := Category.assoc _ _ _
          _ = pᵥK ≫ (uᵥK ≫ (g ≫ m)) :=
            congrArg (fun z => pᵥK ≫ z) hrK
      have haBase : a ≫ (pᵥR ≫ (uᵥR ≫ g)) =
          pᵥK ≫ (uᵥK ≫ g) := by
        calc
          a ≫ (pᵥR ≫ (uᵥR ≫ g)) =
              (a ≫ pᵥR) ≫ (uᵥR ≫ g) :=
            (Category.assoc _ _ _).symm
          _ = (pᵥK ≫ eI.hom) ≫ (uᵥR ≫ g) :=
            congrArg (fun z => z ≫ (uᵥR ≫ g)) ha
          _ = pᵥK ≫ (eI.hom ≫ (uᵥR ≫ g)) :=
            Category.assoc _ _ _
          _ = pᵥK ≫ ((eI.hom ≫ uᵥR) ≫ g) :=
            congrArg (fun z => pᵥK ≫ z)
              (Category.assoc _ _ _).symm
          _ = pᵥK ≫ (uᵥK ≫ g) :=
            congrArg (fun z => pᵥK ≫ (z ≫ g)) he
      apply (cancel_mono ιK).mp
      calc
        (((a ≫ bR) ≫ oR) ≫ q) ≫ ιK =
            ((a ≫ bR) ≫ oR) ≫ (q ≫ ιK) :=
          Category.assoc _ _ _
        _ = ((a ≫ bR) ≫ oR) ≫ (ιR ≫ m) :=
          congrArg (fun z => ((a ≫ bR) ≫ oR) ≫ z) hq
        _ = (((a ≫ bR) ≫ oR) ≫ ιR) ≫ m :=
          (Category.assoc _ _ _).symm
        _ = ((a ≫ bR) ≫ (oR ≫ ιR)) ≫ m :=
          congrArg (fun z => z ≫ m) (Category.assoc _ _ _)
        _ = ((a ≫ bR) ≫ (pR ≫ uR)) ≫ m :=
          congrArg (fun z => ((a ≫ bR) ≫ z) ≫ m) hoR
        _ = (a ≫ (bR ≫ (pR ≫ uR))) ≫ m :=
          congrArg (fun z => z ≫ m) (Category.assoc _ _ _)
        _ = (a ≫ (pᵥR ≫ (uᵥR ≫ g))) ≫ m :=
          congrArg (fun z => (a ≫ z) ≫ m) hBR
        _ = (pᵥK ≫ (uᵥK ≫ g)) ≫ m :=
          congrArg (fun z => z ≫ m) haBase
        _ = pᵥK ≫ (uᵥK ≫ (g ≫ m)) := by
          simp only [Category.assoc]
        _ = bK ≫ (pK ≫ uK) := hBK.symm
        _ = bK ≫ (oK ≫ ιK) :=
          congrArg (fun z => bK ≫ z) hoK.symm
        _ = (bK ≫ oK) ≫ ιK :=
          (Category.assoc _ _ _).symm

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
