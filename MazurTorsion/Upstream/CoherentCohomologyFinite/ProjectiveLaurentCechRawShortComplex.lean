/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentCechCategoricalHomology

/-!
# A raw Laurent Čech short complex

The short complex extracted from the categorical cochain complex has
object carriers definitionally equal to the explicit Laurent cochains,
but those equalities become costly under kernels and quotients.  Here we
build the same three-term complex directly from the raw cochain types
and compare the two short complexes before taking homology.
-/

open CategoryTheory


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {ι R : Type*} [Fintype ι] [LinearOrder ι]

attribute [local instance 2000] laurentCechCyclesAddCommGroup

/-- The raw three-term Laurent Čech complex centered in degree `q + 1`. -/
noncomputable abbrev laurentCechRawShortComplex
    [CommRing R] (d : ℤ) (q : ℕ) :
    ShortComplex (ModuleCat R) where
  X₁ := ModuleCat.of R (Cochain (ι := ι) R d q)
  X₂ := ModuleCat.of R (Cochain (ι := ι) R d (q + 1))
  X₃ := ModuleCat.of R (Cochain (ι := ι) R d ((q + 1) + 1))
  f := ModuleCat.ofHom
    (differential (ι := ι) (R := R) d q)
  g := ModuleCat.ofHom
    (differential (ι := ι) (R := R) d (q + 1))
  zero := by
    apply ModuleCat.hom_ext
    exact differential_comp (ι := ι) (R := R) d q

@[simp]
lemma laurentCechRawShortComplex_f
    [CommRing R] (d : ℤ) (q : ℕ) :
    (laurentCechRawShortComplex
      (ι := ι) (R := R) d q).f.hom =
      differential (ι := ι) (R := R) d q :=
  rfl

@[simp]
lemma laurentCechRawShortComplex_g
    [CommRing R] (d : ℤ) (q : ℕ) :
    (laurentCechRawShortComplex
      (ι := ι) (R := R) d q).g.hom =
      differential (ι := ι) (R := R) d (q + 1) :=
  rfl

/-- The left object of the extracted short complex, normalized before
any kernels or quotients are formed. -/
noncomputable def laurentCechShortComplexX₁IsoRaw
    [CommRing R] (d : ℤ) (q : ℕ) :
    (laurentCechShortComplex
        (ι := ι) (R := R) d q).X₁ ≅
      (laurentCechRawShortComplex
        (ι := ι) (R := R) d q).X₁ := by
  change
    ModuleCat.of R (Cochain (ι := ι) R d q) ≅
      ModuleCat.of R (Cochain (ι := ι) R d q)
  exact Iso.refl _

/-- The middle object of the extracted short complex, normalized before
any kernels or quotients are formed. -/
noncomputable def laurentCechShortComplexX₂IsoRaw
    [CommRing R] (d : ℤ) (q : ℕ) :
    (laurentCechShortComplex
        (ι := ι) (R := R) d q).X₂ ≅
      (laurentCechRawShortComplex
        (ι := ι) (R := R) d q).X₂ := by
  change
    ModuleCat.of R (Cochain (ι := ι) R d (q + 1)) ≅
      ModuleCat.of R (Cochain (ι := ι) R d (q + 1))
  exact Iso.refl _

/-- The right object of the extracted short complex, normalized before
any kernels or quotients are formed. -/
noncomputable def laurentCechShortComplexX₃IsoRaw
    [CommRing R] (d : ℤ) (q : ℕ) :
    (laurentCechShortComplex
        (ι := ι) (R := R) d q).X₃ ≅
      (laurentCechRawShortComplex
        (ι := ι) (R := R) d q).X₃ := by
  change
    ModuleCat.of R (Cochain (ι := ι) R d ((q + 1) + 1)) ≅
      ModuleCat.of R (Cochain (ι := ι) R d ((q + 1) + 1))
  exact Iso.refl _

@[simp]
lemma laurentCechShortComplexX₁IsoRaw_hom_apply
    [CommRing R] (d : ℤ) (q : ℕ)
    (x : (laurentCechShortComplex
      (ι := ι) (R := R) d q).X₁) :
    (laurentCechShortComplexX₁IsoRaw
      (ι := ι) (R := R) d q).hom x = x :=
  rfl

@[simp]
lemma laurentCechShortComplexX₂IsoRaw_hom_apply
    [CommRing R] (d : ℤ) (q : ℕ)
    (x : (laurentCechShortComplex
      (ι := ι) (R := R) d q).X₂) :
    (laurentCechShortComplexX₂IsoRaw
      (ι := ι) (R := R) d q).hom x = x :=
  rfl

@[simp]
lemma laurentCechShortComplexX₃IsoRaw_hom_apply
    [CommRing R] (d : ℤ) (q : ℕ)
    (x : (laurentCechShortComplex
      (ι := ι) (R := R) d q).X₃) :
    (laurentCechShortComplexX₃IsoRaw
      (ι := ι) (R := R) d q).hom x = x :=
  rfl

/-- The short complex extracted from the categorical Laurent complex is
isomorphic to the raw three-term complex. -/
noncomputable def laurentCechShortComplexIsoRaw
    [CommRing R] (d : ℤ) (q : ℕ) :
    laurentCechShortComplex (ι := ι) (R := R) d q ≅
      laurentCechRawShortComplex (ι := ι) (R := R) d q :=
  ShortComplex.isoMk
    (laurentCechShortComplexX₁IsoRaw
      (ι := ι) (R := R) d q)
    (laurentCechShortComplexX₂IsoRaw
      (ι := ι) (R := R) d q)
    (laurentCechShortComplexX₃IsoRaw
      (ι := ι) (R := R) d q)
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change
        differential (ι := ι) (R := R) d q
            ((laurentCechShortComplexX₁IsoRaw
              (ι := ι) (R := R) d q).hom x) =
          (laurentCechShortComplexX₂IsoRaw
            (ι := ι) (R := R) d q).hom
            ((laurentCechShortComplex
              (ι := ι) (R := R) d q).f x)
      rw [laurentCechShortComplexX₁IsoRaw_hom_apply,
        laurentCechShortComplexX₂IsoRaw_hom_apply]
      exact (DFunLike.congr_fun
        (laurentCechShortComplex_f
          (ι := ι) (R := R) d q) x).symm)
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change
        differential (ι := ι) (R := R) d (q + 1)
            ((laurentCechShortComplexX₂IsoRaw
              (ι := ι) (R := R) d q).hom x) =
          (laurentCechShortComplexX₃IsoRaw
            (ι := ι) (R := R) d q).hom
            ((laurentCechShortComplex
              (ι := ι) (R := R) d q).g x)
      rw [laurentCechShortComplexX₂IsoRaw_hom_apply,
        laurentCechShortComplexX₃IsoRaw_hom_apply]
      exact (DFunLike.congr_fun
        (laurentCechShortComplex_g
          (ι := ι) (R := R) d q) x).symm)

/-- The explicit left-homology objects of the extracted and raw short
complexes are linearly equivalent. -/
noncomputable def laurentCechShortComplexRawHomologyLinearEquiv
    [CommRing R] (d : ℤ) (q : ℕ) :
    (laurentCechShortComplex
        (ι := ι) (R := R) d q).moduleCatLeftHomologyData.H ≃ₗ[R]
      (laurentCechRawShortComplex
        (ι := ι) (R := R) d q).moduleCatLeftHomologyData.H :=
  (ShortComplex.leftHomologyMapIso'
    (laurentCechShortComplexIsoRaw
      (ι := ι) (R := R) d q)
    (laurentCechShortComplex
      (ι := ι) (R := R) d q).moduleCatLeftHomologyData
    (laurentCechRawShortComplex
      (ι := ι) (R := R) d q).moduleCatLeftHomologyData).toLinearEquiv

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech
