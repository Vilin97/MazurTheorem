/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.BaseRingModuleSheafPushforward
import MazurTorsion.Upstream.CoherentCohomologyFinite.FinitePushforwardCoherence
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveBaseExtFiniteness
import MazurTorsion.Upstream.CoherentCohomologyFinite.TopologicalSheafBaseLinearClosedEmbeddingExt

/-!
# Base-linear Ext for a projective factorization

This file transports the projective-space constant-source Ext theorem
through a closed immersion.  It is the fixed-base Ext form of the
projective case needed by the proper-scheme support dévissage.
-/


open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FlatBaseAcyclicCoverCechComparison
open SerreTwist

noncomputable local instance projectiveFactorizationExtAddCommGroup
    {R : Type} [CommRing R] {Y : TopCat}
    (F : Y.Sheaf (ModuleCat R)) (n : ℕ) :
    AddCommGroup
      (Abelian.Ext
        (constantRankOneSheaf (R := R) Y) F n) :=
  CategoryTheory.Abelian.Ext.instAddCommGroup

noncomputable local instance projectiveFactorizationExtModule
    {R : Type} [CommRing R] {Y : TopCat}
    (F : Y.Sheaf (ModuleCat R)) (n : ℕ) :
    Module R
      (Abelian.Ext
        (constantRankOneSheaf (R := R) Y) F n) :=
  CategoryTheory.Abelian.Ext.instModule

/-- A coherent module on a scheme with a closed projective-space
factorization has finite base-linear constant-source Ext, assuming the
two coordinate compatibilities in the projective-space calculation. -/
theorem coherentModuleSheafExt_finite_of_projectiveFactorization
    {R : Type} [CommRing R] [Module.Flat ℤ R]
    [IsNoetherianRing R]
    {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of R)}
    (hproj : IsProjectiveFactorization f)
    (hchart :
      ∀ (d : ℕ) (m : ℤ),
        BaseStandardCoverCoordinatesNatural R d m)
    (hcoordinate :
      ∀ (d N : ℕ),
        SerreTwist.IntegerOverChartCoordinateTransition
          R d N)
    (M : X.Modules)
    [M.IsFiniteType] [M.IsQuasicoherent]
    (n : ℕ) :
    letI :
        X.Over (Spec (CommRingCat.of R)) :=
      ⟨f⟩
    Module.Finite R
      (Abelian.Ext
        (constantRankOneSheaf
          (R := R) (X : TopCat))
        (moduleSheaf (k := R) M) n) := by
  letI :
      X.Over (Spec (CommRingCat.of R)) :=
    ⟨f⟩
  obtain ⟨d, i, hi, hif⟩ := hproj
  letI : IsClosedImmersion i := hi
  letI :
      (scheme R d).Over
        (Spec (CommRingCat.of R)) :=
    ⟨toSpec R d⟩
  letI : IsLocallyNoetherian (scheme R d) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (toSpec R d)
  let N :=
    (Scheme.Modules.pushforward i).obj M
  letI : N.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pushforward_closedImmersion
      i M
  letI : N.IsFiniteType :=
    SheafOfModules.instIsFiniteTypeOfIsFinitePresentation N
  letI : N.IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_pushforward_affineHom
      i M
  have hprojective :
      Module.Finite R
        (Abelian.Ext
          (constantRankOneSheaf
            (R := R) (scheme R d : TopCat))
          (moduleSheaf (k := R) N) n) :=
    coherentModuleSheafExt_finite_of_coordinate_seams
      d (hchart d) (hcoordinate d) N n
  have hpushforward :
      Module.Finite R
        (Abelian.Ext
          (constantRankOneSheaf
            (R := R) (scheme R d : TopCat))
          ((TopCat.Sheaf.pushforward
            (ModuleCat R) i.base).obj
              (moduleSheaf (k := R) M :
                (X : TopCat).Sheaf
                  (ModuleCat R))) n) := by
    letI hfiniteProjective :
        Module.Finite R
          (Abelian.Ext
            (constantRankOneSheaf
              (R := R) (scheme R d : TopCat))
            (moduleSheaf (k := R)
              ((Scheme.Modules.pushforward i).obj M)) n) :=
      hprojective
    exact
      extFinite_congr_right
        (moduleSheafPushforwardIso
          (k := R) i hif M).symm n
  exact
    (MazurTorsion.AlgebraicGeometry.CoherentCohomology.TopCat.closedEmbeddingConstantExt_finite_iff
        (R := R) i.base i.isClosedEmbedding
        (moduleSheaf (k := R) M :
          (X : TopCat).Sheaf (ModuleCat R)) n).mpr
      hpushforward

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
