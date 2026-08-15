/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverIsoGluedComparison
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescentEquivalence
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescentIso
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescentTransport

/-!
# Pulling module descent objects along an isomorphism of open covers

We first glue descent data for the target cover, pull the resulting module
along the comparison of glued schemes, and restrict to the source cover.
Canonical pullback comparisons then identify its chart objects with the
pullbacks of the original chart objects.  The existing chartwise transport
construction supplies the coherent descent datum.
-/


open CategoryTheory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.CoverDescentData

open Scheme.Cover

variable {X : Scheme.{0}} {𝒰 𝒱 : X.OpenCover}

/-- Restrict to the source cover after gluing target-cover descent data
and pulling it along the induced comparison of glued schemes. -/
noncomputable def coverIsoRestriction
    (e : 𝒰 ≅ 𝒱)
    (A : CoverDescentData 𝒱.gluedCover) :
    CoverDescentData 𝒰.gluedCover :=
  (restrictionFunctor (D := 𝒰.gluedCover)).obj
    ((pullback (coverIsoGluedIso e).hom).obj
      ((glueFunctor (D := 𝒱.gluedCover)).obj A))

/-- The canonical chart comparison for descent data pulled along a cover
isomorphism, before rewriting a restricted glued object by effective
descent. -/
noncomputable def coverIsoCanonicalChartIso
    (e : 𝒰 ≅ 𝒱)
    (W : 𝒱.gluedCover.glued.Modules)
    (i : 𝒰.I₀) :
    ((restrictionFunctor (D := 𝒰.gluedCover)).obj
      ((pullback (coverIsoGluedIso e).hom).obj W)).chart i ≅
      (pullback (e.hom.h₀ i)).obj
        (((restrictionFunctor
          (D := 𝒱.gluedCover)).obj W).chart
            (e.hom.s₀ i)) :=
  (pullbackComp
      (𝒰.gluedCover.ι i)
      (coverIsoGluedIso e).hom).app
        W ≪≫
    (pullbackCongr
      (gluedCover_ι_coverIsoGluedIso_hom e i)).app
        W ≪≫
    (pullbackComp
      (e.hom.h₀ i)
      (𝒱.gluedCover.ι (e.hom.s₀ i))).symm.app
        W

/-- The canonical chart comparison for descent data pulled along a cover
isomorphism. -/
noncomputable def coverIsoRestrictionChartIso
    (e : 𝒰 ≅ 𝒱)
    (A : CoverDescentData 𝒱.gluedCover)
    (i : 𝒰.I₀) :
    (coverIsoRestriction e A).chart i ≅
      (pullback (e.hom.h₀ i)).obj
        (A.chart (e.hom.s₀ i)) :=
  coverIsoCanonicalChartIso e
      ((glueFunctor (D := 𝒱.gluedCover)).obj A) i ≪≫
    (pullback (e.hom.h₀ i)).mapIso
      (isoApp
        (descentGlueRestrictionIso
          (D := 𝒱.gluedCover) A)
        (e.hom.s₀ i))

/-- Descent data pulled along an isomorphism of open covers, with its
chart objects rewritten as literal pullbacks of the target chart data. -/
noncomputable def pullbackAlongCoverIso
    (e : 𝒰 ≅ 𝒱)
    (A : CoverDescentData 𝒱.gluedCover) :
    CoverDescentData 𝒰.gluedCover :=
  transport
    (coverIsoRestriction e A)
    (fun i =>
      (pullback (e.hom.h₀ i)).obj
        (A.chart (e.hom.s₀ i)))
    (coverIsoRestrictionChartIso e A)

/-- The raw global construction is canonically isomorphic to the
chart-normalized pullback descent object. -/
noncomputable def coverIsoRestrictionTransportIso
    (e : 𝒰 ≅ 𝒱)
    (A : CoverDescentData 𝒱.gluedCover) :
    coverIsoRestriction e A ≅
      pullbackAlongCoverIso e A :=
  transportIso
    (coverIsoRestriction e A)
    (fun i =>
      (pullback (e.hom.h₀ i)).obj
        (A.chart (e.hom.s₀ i)))
    (coverIsoRestrictionChartIso e A)

end AlgebraicGeometry.Scheme.Modules.CoverDescentData
