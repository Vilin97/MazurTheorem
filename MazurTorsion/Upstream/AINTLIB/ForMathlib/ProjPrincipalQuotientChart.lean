/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck

This is a declaration-generalized adaptation of `chartQuotientEquiv` and
`chartCoordEquiv` from AINTLIB's `EllipticCurve/WeierstrassModel.lean`, exact
source blob `0cea4fbbcd8f0976b8cb0949755ecacec6e58b26`. The source blob is present at
AINTLIB's Apache-2.0 licensed default commit
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`.
-/

import MazurTorsion.Upstream.AINTLIB.ForMathlib.ProjectiveSpaceChart
import MazurTorsion.Upstream.AINTLIB.ForMathlib.ProjQuotientAway

/-!
# Principal homogeneous quotient charts

The away chart of a principal homogeneous quotient is the quotient of the
ambient away chart by the dehomogenized equation. For a multivariate
polynomial ring, the standard projective-space chart equivalence identifies
that ring with a polynomial ring on all coordinates except the inverted one.

These are ring-level equivalences. No `Proj`, scheme, point, or smoothness API
is imported here.
-/

namespace HomogeneousIdeal

open HomogeneousLocalization

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] (I : HomogeneousIdeal 𝒜)

/-- The away chart of a principal homogeneous quotient is the quotient of the
ambient away chart by the localized homogeneous generator. -/
noncomputable def principalAwayQuotientEquiv {d : ℕ} {F : A} (hF : F ∈ 𝒜 d)
    (hI : I.toIdeal = Ideal.span {F}) {s : A} (hs : s ∈ 𝒜 1) :
    (HomogeneousLocalization.Away 𝒜 s ⧸
      Ideal.span {HomogeneousLocalization.Away.mk 𝒜 hs d F (by simpa using hF)}) ≃+*
    HomogeneousLocalization.Away (quotientGrading I) ((quotientGradingHom I) s) := by
  have hker :
      Ideal.span {HomogeneousLocalization.Away.mk 𝒜 hs d F (by simpa using hF)} =
        RingHom.ker
          (HomogeneousLocalization.Away.map (quotientGradingHom I) s) :=
    (ker_away_map_quotientGradingHom I hF hI hs).symm
  exact (Ideal.quotEquivOfEq hker).trans
    (RingHom.quotientKerEquivOfSurjective
      (away_map_quotientGradingHom_surjective I hs))

end HomogeneousIdeal

namespace MvPolynomial

open HomogeneousLocalization

variable (R : Type*) {σ : Type*} [CommRing R] [DecidableEq σ]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A standard chart of a principal homogeneous quotient of a multivariate
polynomial ring is the affine polynomial ring on the remaining variables,
quotiented by the dehomogenized equation. -/
noncomputable def principalQuotientChartEquiv
    (I : HomogeneousIdeal (homogeneousSubmodule σ R)) {d : ℕ}
    (F : MvPolynomial σ R) (hF : F.IsHomogeneous d)
    (hI : I.toIdeal = Ideal.span {F}) (i : σ) :
    (MvPolynomial {j : σ // j ≠ i} R ⧸
      Ideal.span {dehomogenizeAux R i F}) ≃+*
    HomogeneousLocalization.Away (HomogeneousIdeal.quotientGrading I)
      ((HomogeneousIdeal.quotientGradingHom I) (X i)) := by
  have hFmem : F ∈ homogeneousSubmodule σ R d :=
    (mem_homogeneousSubmodule _ _).mpr hF
  let hs : (X i : MvPolynomial σ R) ∈ homogeneousSubmodule σ R 1 :=
    X_mem_homogeneousSubmodule_one R i
  exact ((Ideal.quotientEquiv
    (Ideal.span {HomogeneousLocalization.Away.mk
      (homogeneousSubmodule σ R) hs d F (by simpa using hFmem)})
    (Ideal.span {dehomogenizeAux R i F})
    ((chartRingEquiv R i) :
      HomogeneousLocalization.Away (homogeneousSubmodule σ R) (X i) ≃+*
        MvPolynomial {j : σ // j ≠ i} R)
    (by
      rw [Ideal.map_span, Set.image_singleton]
      congr 1
      rw [Set.singleton_eq_singleton_iff]
      symm
      change dehomogenizeAt R i _ = _
      rw [dehomogenizeAt_mk])).symm).trans
    (HomogeneousIdeal.principalAwayQuotientEquiv I hFmem hI hs)

end MvPolynomial
