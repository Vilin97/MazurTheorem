/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteAcyclicCoverPushforwardCohomology
import MazurTorsion.Upstream.CoherentCohomologyFinite.SeparatedAffineCoverBound

/-!
# Cohomology of an acyclic relative direct image

On a compact separated base, the chosen finite affine cover has affine
nonempty intersections.  Hence any quasicoherent direct image is acyclic
on the base cover.  If a sheaf upstairs is acyclic on the inverse-image
cover, the finite Čech comparison identifies its cohomology with that of
its direct image.  This is the precise Leray bridge used after relative
Serre vanishing.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace


noncomputable section

noncomputable local instance relativeAcyclicCohomologyAddCommGroup
    {Z : TopCat} (G : Z.Sheaf AddCommGrpCat) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H G n) := by
  dsimp only [CategoryTheory.Sheaf.H]
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.RelativeAcyclicPushforwardCohomology

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteAcyclicCoverPushforwardCohomology
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafCechComparison

variable {Y X : Scheme.{0}}

/--
Global higher-cohomology vanishing after restriction to every nonempty
inverse-image intersection gives precisely the source-side acyclicity
needed by the finite Čech comparison.
-/
theorem inverseImageCover_isAcyclicOnIntersections_of_restrict
    (f : Y ⟶ X) (M : Y.Modules)
    {ι : Type} [Fintype ι] [LinearOrder ι]
    (V : ι → X.Opens)
    (hrestrict :
      ∀ (t : Finset ι), t.Nonempty →
        ∀ (q : ℕ), 0 < q →
          Subsingleton
            (CategoryTheory.Sheaf.H
              ((M.restrict
                (f ⁻¹ᵁ finiteIntersection V t).ι).sheaf)
              q)) :
    IsAcyclicOnIntersections M.sheaf
      (fun i => f ⁻¹ᵁ V i) Finset.univ := by
  intro t ht _ q hq
  rw [show
      finiteIntersection (fun i => f ⁻¹ᵁ V i) t =
        f ⁻¹ᵁ finiteIntersection V t by
    exact
      intersection_inverseImageCover
        f.base V t]
  have hdegree : q - 1 + 1 = q :=
    Nat.sub_add_cancel hq
  rw [← hdegree]
  apply
    TopCat.Sheaf.OpenCohomology.subsingleton_H'_of_subsingleton_restrict_H
      M.sheaf
      (f ⁻¹ᵁ finiteIntersection V t)
      (q - 1)
  change
    Subsingleton
      (CategoryTheory.Sheaf.H
        ((M.restrict
          (f ⁻¹ᵁ finiteIntersection V t).ι).sheaf)
        (q - 1 + 1))
  rw [hdegree]
  exact hrestrict t ht q hq

/-- A quasicoherent module is acyclic on every nonempty intersection
of the canonical finite affine family of a compact separated scheme. -/
theorem finiteAffineOpenFamily_isAcyclicOnIntersections
    [CompactSpace X] [X.IsSeparated]
    (E : X.Modules) [E.IsQuasicoherent] :
    IsAcyclicOnIntersections E.sheaf
      (Scheme.finiteAffineOpenFamily X)
      Finset.univ := by
  intro t ht _ q hq
  letI :
      IsAffine
        (finiteIntersection
          (Scheme.finiteAffineOpenFamily X) t) :=
    Scheme.finiteIntersection_finiteAffineOpenFamily_isAffineOpen
      X t ht
  have h :=
    Scheme.Modules.subsingleton_H'_of_isAffineOpen
      E
      (finiteIntersection
        (Scheme.finiteAffineOpenFamily X) t)
      (q - 1)
  rw [Nat.sub_add_cancel hq] at h
  exact h

/-- The canonical finite affine family is a cover in `iSup` form. -/
lemma finiteAffineOpenFamily_iSup_eq_top
    (X : Scheme.{0}) [CompactSpace X] :
    ⨆ i, Scheme.finiteAffineOpenFamily X i = ⊤ := by
  simpa [finiteUnion] using
    Scheme.finiteAffineOpenFamily_covers X

/--
Relative Leray comparison on the canonical finite affine base cover:
acyclicity on inverse images, together with quasicoherence of the direct
image, identifies source and direct-image cohomology.
-/
noncomputable def pushforwardHAddEquiv_of_finiteAffineCoverAcyclic
    [CompactSpace X] [X.IsSeparated]
    (f : Y ⟶ X) (M : Y.Modules)
    [((Scheme.Modules.pushforward f).obj M).IsQuasicoherent]
    (hsource :
      IsAcyclicOnIntersections M.sheaf
        (fun i =>
          (Opens.map f.base).obj
            (Scheme.finiteAffineOpenFamily X i))
        Finset.univ)
    (n : ℕ) :
    M.sheaf.H n ≃+
      ((Scheme.Modules.pushforward f).obj M).sheaf.H n := by
  letI : LinearOrder
      (Option (Scheme.finiteAffineSubcover X).I₀) :=
    WellOrderingRel.isWellOrder.linearOrder
  exact
    schemePushforwardHAddEquivOfAcyclicCover
      f M (Scheme.finiteAffineOpenFamily X)
      (finiteAffineOpenFamily_iSup_eq_top X)
      hsource
      (finiteAffineOpenFamily_isAcyclicOnIntersections
        ((Scheme.Modules.pushforward f).obj M))
      n

/--
Restriction-level form of relative Leray comparison.  This is the form
directly produced by relative Serre vanishing on affine intersections.
-/
noncomputable def pushforwardHAddEquiv_of_finiteAffineCoverRestrictAcyclic
    [CompactSpace X] [X.IsSeparated]
    (f : Y ⟶ X) (M : Y.Modules)
    [((Scheme.Modules.pushforward f).obj M).IsQuasicoherent]
    (hrestrict :
      ∀ (t : Finset
          (Option (Scheme.finiteAffineSubcover X).I₀)),
        t.Nonempty →
        ∀ (q : ℕ), 0 < q →
          Subsingleton
            (CategoryTheory.Sheaf.H
              ((M.restrict
                (f ⁻¹ᵁ finiteIntersection
                  (Scheme.finiteAffineOpenFamily X) t).ι).sheaf)
              q))
    (n : ℕ) :
    M.sheaf.H n ≃+
      ((Scheme.Modules.pushforward f).obj M).sheaf.H n := by
  letI : LinearOrder
      (Option (Scheme.finiteAffineSubcover X).I₀) :=
    WellOrderingRel.isWellOrder.linearOrder
  apply
    pushforwardHAddEquiv_of_finiteAffineCoverAcyclic
      f M
  exact
    inverseImageCover_isAcyclicOnIntersections_of_restrict
      f M
      (Scheme.finiteAffineOpenFamily X)
      hrestrict

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.RelativeAcyclicPushforwardCohomology
