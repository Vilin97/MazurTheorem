/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveClosure
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveGraphClosure

/-!
# A projective modification from one affine chart

Let `Spec A` be an affine open of a `k`-scheme `S`, with `A` of finite
type over `k`.  A polynomial presentation embeds this affine open into a
standard chart of projective space.  Closing the resulting graph produces
a projective morphism to `S` which is the identity over that affine open.
-/

open CategoryTheory AlgebraicGeometry MvPolynomial

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-- A finite-type affine open of a `k`-scheme produces a projective graph
closure over that scheme.  The original affine open embeds densely into
the closure, and both projections restrict to the prescribed maps. -/
theorem exists_projectiveModification_of_affineOpen
    (k A : Type u) [CommRing k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A]
    (S : Scheme.{u})
    (s : S ⟶ Spec (CommRingCat.of k))
    (u : Spec (CommRingCat.of A) ⟶ S)
    [IsOpenImmersion u] [QuasiSeparatedSpace S]
    (hu :
      u ≫ s =
        Spec.map (CommRingCat.ofHom (algebraMap k A))) :
    ∃ (d : ℕ)
      (φ : MvPolynomial (Fin d) k →ₐ[k] A)
      (hbase :
        u ≫ s =
          affineChartImmersion φ ≫ toSpec k d),
      Function.Surjective φ ∧
      IsOpenImmersion
        (toProjectiveGraphClosure
          s d u (affineChartImmersion φ) hbase) ∧
      Dense
        (Set.range
          (toProjectiveGraphClosure
            s d u (affineChartImmersion φ) hbase).base) ∧
      IsRelativeProjectiveFactorization s
        (projectiveGraphClosureToBase
          s d u (affineChartImmersion φ) hbase) ∧
      IsProper
        (projectiveGraphClosureToBase
          s d u (affineChartImmersion φ) hbase) ∧
      toProjectiveGraphClosure
          s d u (affineChartImmersion φ) hbase ≫
        projectiveGraphClosureToBase
          s d u (affineChartImmersion φ) hbase =
        u ∧
      toProjectiveGraphClosure
          s d u (affineChartImmersion φ) hbase ≫
        projectiveGraphClosureToProjective
          s d u (affineChartImmersion φ) hbase =
        affineChartImmersion φ := by
  obtain ⟨d, φ, hφ⟩ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
      (inferInstance : Algebra.FiniteType k A)
  let hbase :
      u ≫ s =
        affineChartImmersion φ ≫ toSpec k d :=
    hu.trans (affineChartImmersion_toSpec φ).symm
  haveI : QuasiCompact u := inferInstance
  exact
    ⟨d, φ, hbase, hφ,
      isOpenImmersion_toProjectiveGraphClosure
        s d u (affineChartImmersion φ) hbase,
      denseRange_toProjectiveGraphClosure
        s d u (affineChartImmersion φ) hbase,
      isRelativeProjectiveFactorization_projectiveGraphClosureToBase
        s d u (affineChartImmersion φ) hbase,
      isProper_projectiveGraphClosureToBase
        s d u (affineChartImmersion φ) hbase,
      toProjectiveGraphClosure_toBase
        s d u (affineChartImmersion φ) hbase,
      toProjectiveGraphClosure_toProjective
        s d u (affineChartImmersion φ) hbase⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
