/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveCorrectedChartLocalMaps
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleOpenCoverHom

/-!
# Global maps from corrected projective-chart generators

The corrected local maps from a single negative integer twist agree on
pairwise standard-chart intersections.  Gluing them produces a global
morphism whose restriction to each standard chart is the prescribed local
map.
-/

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleOpenCoverHom
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleOpenSectionHom
open SerreTwist

variable (k : Type) [CommRing k] (d : ℕ)

/-- Coordinate transition needed from the integer-twist chart
trivializations.  For `𝒪(-N)`, the `l`-chart coordinate is the `j`-chart
coordinate multiplied by `(X_l/X_j)^N`, after restriction to any subopen
of the pairwise intersection. -/
def SerreTwist.IntegerOverChartCoordinateTransition (N : ℕ) : Prop :=
  ∀ (j l : Fin (d + 1))
    (V : (Over
      (standardChart k j ⊓ standardChart k l))ᵒᵖ)
    (x : (OInt k d (-(N : ℤ))).val.obj
      (op V.unop.left)),
    (show Γ(scheme k d, V.unop.left) from
      (integerOverChartIso k d (-(N : ℤ)) l).hom.val.app
        ((Over.map
          (Opens.infLERight
            (standardChart k j) (standardChart k l))).op.obj V) x) =
      (scheme k d).presheaf.map V.unop.hom.op
          (chartScalarOnPair k d l j
            (chartRatioElement k d l j) ^ N) *
        (show Γ(scheme k d, V.unop.left) from
          (integerOverChartIso k d (-(N : ℤ)) j).hom.val.app
            ((Over.map
              (Opens.infLELeft
                (standardChart k j) (standardChart k l))).op.obj V) x)

namespace CorrectedChartGeneratorExtensions

variable {k d}
variable {M : (scheme k d).Modules} {i : Fin (d + 1)}
variable {G : ChartGenerators k d M i}
variable {E : ChartGeneratorExtensions k d G}

/-- The standard-chart family of local maps from the corrected twist. -/
def correctedTwistOverHomFamily
    (C : CorrectedChartGeneratorExtensions k d E)
    (a : Fin G.count) :
    ∀ j : Fin (d + 1),
      (OInt k d (-(C.totalExponent : ℤ))).over
          (standardChart k j) ⟶
        M.over (standardChart k j) :=
  fun j => C.correctedTwistOverHom j a

/-- The corrected local twist maps agree on pairwise standard-chart
intersections. -/
theorem correctedTwistOverHomFamily_compatible
    (C : CorrectedChartGeneratorExtensions k d E)
    (a : Fin G.count)
    (hcoordinate :
      IntegerOverChartCoordinateTransition
        k d C.totalExponent) :
    Compatible
      (OInt k d (-(C.totalExponent : ℤ))) M
      (standardChart k)
      (C.correctedTwistOverHomFamily a) := by
  intro j l
  apply NatTrans.ext
  funext V
  dsimp only [CategoryTheory.presheafHom]
  ext x
  change
    (C.correctedTwistOverHom j a).val.app
          ((Over.map
            (Opens.infLELeft
              (standardChart k j) (standardChart k l))).op.obj V) x =
      (C.correctedTwistOverHom l a).val.app
          ((Over.map
            (Opens.infLERight
              (standardChart k j) (standardChart k l))).op.obj V) x
  change
    (C.correctedOverHom j a).val.app
          ((Over.map
            (Opens.infLELeft
              (standardChart k j) (standardChart k l))).op.obj V)
          ((integerOverChartIso k d
            (-(C.totalExponent : ℤ)) j).hom.val.app
              ((Over.map
                (Opens.infLELeft
                  (standardChart k j)
                  (standardChart k l))).op.obj V) x) =
      (C.correctedOverHom l a).val.app
          ((Over.map
            (Opens.infLERight
              (standardChart k j) (standardChart k l))).op.obj V)
          ((integerOverChartIso k d
            (-(C.totalExponent : ℤ)) l).hom.val.app
              ((Over.map
                (Opens.infLERight
                  (standardChart k j)
                  (standardChart k l))).op.obj V) x)
  let q : Γ(scheme k d, V.unop.left) :=
    (scheme k d).presheaf.map V.unop.hom.op
      (chartScalarOnPair k d l j
        (chartRatioElement k d l j) ^ C.totalExponent)
  let cj : Γ(scheme k d, V.unop.left) :=
    (show Γ(scheme k d, V.unop.left) from
      (integerOverChartIso k d
        (-(C.totalExponent : ℤ)) j).hom.val.app
          ((Over.map
            (Opens.infLELeft
              (standardChart k j)
              (standardChart k l))).op.obj V) x)
  let cl : Γ(scheme k d, V.unop.left) :=
    (show Γ(scheme k d, V.unop.left) from
      (integerOverChartIso k d
        (-(C.totalExponent : ℤ)) l).hom.val.app
          ((Over.map
            (Opens.infLERight
              (standardChart k j)
              (standardChart k l))).op.obj V) x)
  let s :=
    restrictOpenSection M (standardChart k l)
      (C.correctedAmbientSection l a)
      ((Over.map
        (Opens.infLERight
          (standardChart k j) (standardChart k l))).op.obj V)
  let act :
      Γ(scheme k d, V.unop.left) →
        (M.over (standardChart k l)).val.obj
          ((Over.map
            (Opens.infLERight
              (standardChart k j) (standardChart k l))).op.obj V) →
        (M.over (standardChart k l)).val.obj
          ((Over.map
            (Opens.infLERight
              (standardChart k j) (standardChart k l))).op.obj V) :=
    fun r t =>
      (show
        ((scheme k d).ringCatSheaf.over
          (standardChart k l)).obj.obj
            ((Over.map
              (Opens.infLERight
                (standardChart k j) (standardChart k l))).op.obj V)
        from r) • t
  have hleft := homOfOpenSection_app M (standardChart k j)
    (C.correctedAmbientSection j a)
    ((Over.map
      (Opens.infLELeft
        (standardChart k j) (standardChart k l))).op.obj V)
    cj
  have hrestrict :=
    C.restrict_correctedAmbientSection_over j l a V
  have hright := homOfOpenSection_app M (standardChart k l)
    (C.correctedAmbientSection l a)
    ((Over.map
      (Opens.infLERight
        (standardChart k j) (standardChart k l))).op.obj V)
    cl
  have halgebra : act cj (act q s) = act cl s := by
    unfold act
    rw [smul_smul]
    apply congrArg (fun r : Γ(scheme k d, V.unop.left) => act r s)
    calc
      cj * q = q * cj := mul_comm _ _
      _ = cl := by
        simpa only [q, cj, cl] using
          (hcoordinate j l V x).symm
  exact hleft.trans <|
    (congrArg (fun t => act cj t) hrestrict).trans <|
      halgebra.trans hright.symm

/-- The global morphism obtained by gluing one corrected generator. -/
def correctedGlobalHom
    (C : CorrectedChartGeneratorExtensions k d E)
    (a : Fin G.count)
    (hcoordinate :
      IntegerOverChartCoordinateTransition
        k d C.totalExponent) :
    OInt k d (-(C.totalExponent : ℤ)) ⟶ M :=
  glue
    (OInt k d (-(C.totalExponent : ℤ))) M
    (standardChart k)
    (C.correctedTwistOverHomFamily a)
    (by
      rw [iSup_standardChart k d])
    (C.correctedTwistOverHomFamily_compatible a hcoordinate)

/-- Restricting the glued global map to a standard chart recovers the
corrected local map. -/
theorem correctedGlobalHom_over
    (C : CorrectedChartGeneratorExtensions k d E)
    (j : Fin (d + 1)) (a : Fin G.count)
    (hcoordinate :
      IntegerOverChartCoordinateTransition
        k d C.totalExponent) :
    (C.correctedGlobalHom a hcoordinate).over
        (standardChart k j) =
      C.correctedTwistOverHom j a := by
  exact
    glue_over
      (OInt k d (-(C.totalExponent : ℤ))) M
      (standardChart k)
      (C.correctedTwistOverHomFamily a)
      (by
        rw [iSup_standardChart k d])
      (C.correctedTwistOverHomFamily_compatible
        a hcoordinate)
      j

end CorrectedChartGeneratorExtensions

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
