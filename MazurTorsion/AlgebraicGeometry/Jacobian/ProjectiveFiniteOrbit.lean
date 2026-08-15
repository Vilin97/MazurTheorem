/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteGroupQuotient
import MazurTorsion.AlgebraicGeometry.Jacobian.PermutationPower
import MazurTorsion.Upstream.CoherentCohomologyFinite.SegreProductChartTransitionGeometry
import TauCeti.AlgebraicGeometry.ProjectiveLine.Proper

/-!
# Affine neighbourhoods of finite orbits in projective schemes

Finitely many points in projective space lie in a single positive-degree
basic open.  The proof builds homogeneous separators for the inclusion-
maximal point ideals, raises them to a common degree, and sums them.  Over
an infinite field a shorter degree-one argument is also recorded.  Pullback
along a closed projective embedding gives the same conclusion for every
scheme with a standard projective factorization.

The named downstream consumer is the permutation action on a finite power
of the projective line in `SymmetricPower`.
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.ProjectiveFiniteOrbit

universe u

open CoherentCohomology.ProjectiveSpace
open FiniteGroupQuotient
open TauCeti.AlgebraicGeometry

/-- The degree-one forms vanishing at a point of standard projective space. -/
def degreeOneVanishingSubmodule
    (K : Type u) [Field K] (d : ℕ) (p : scheme K d) :
    Submodule K (homogeneousGrading K d 1) :=
  Submodule.comap (homogeneousGrading K d 1).subtype
    (p.asHomogeneousIdeal.toIdeal.restrictScalars K)

@[simp]
theorem mem_degreeOneVanishingSubmodule_iff
    (K : Type u) [Field K] (d : ℕ) (p : scheme K d)
    (q : homogeneousGrading K d 1) :
    q ∈ degreeOneVanishingSubmodule K d p ↔
      (q : MvPolynomial (Fin (d + 1)) K) ∈ p.asHomogeneousIdeal :=
  Iff.rfl

/-- Every projective point has a nonvanishing homogeneous coordinate. -/
theorem exists_coordinate_not_mem
    (K : Type u) [Field K] (d : ℕ) (p : scheme K d) :
    ∃ i : Fin (d + 1), coordinate K i ∉ p.asHomogeneousIdeal := by
  have hp : p ∈ (⊤ : (scheme K d).Opens) := trivial
  rw [← iSup_standardChart K d] at hp
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hp
  exact ⟨i, (Proj.mem_basicOpen (homogeneousGrading K d) (coordinate K i) p).mp hi⟩

/-- Relevance makes the degree-one vanishing space at a projective point
proper. -/
theorem degreeOneVanishingSubmodule_ne_top
    (K : Type u) [Field K] (d : ℕ) (p : scheme K d) :
    degreeOneVanishingSubmodule K d p ≠ ⊤ := by
  obtain ⟨i, hi⟩ := exists_coordinate_not_mem K d p
  intro hp
  have hXi :
      (⟨coordinate K i, coordinate_mem_degreeOne K i⟩ :
          homogeneousGrading K d 1) ∈
        degreeOneVanishingSubmodule K d p := by
    rw [hp]
    trivial
  exact hi ((mem_degreeOneVanishingSubmodule_iff K d p _).mp hXi)

/-- Two non-comparable homogeneous ideals can be separated by a homogeneous
element. -/
theorem exists_homogeneous_mem_not_mem
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]
    (grading : ℕ → σ) [GradedRing grading]
    (I J : HomogeneousIdeal grading) (hJI : ¬ J ≤ I) :
    ∃ n : ℕ, ∃ x : grading n, (x : A) ∈ J ∧ (x : A) ∉ I := by
  rw [SetLike.not_le_iff_exists] at hJI
  obtain ⟨x, hxJ, hxI⟩ := hJI
  have hxcomp : ∃ n : ℕ, (DirectSum.decompose grading x n : A) ∉ I := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hxI (I.isHomogeneous.mem_iff.mpr h)
  obtain ⟨n, hn⟩ := hxcomp
  exact ⟨n, DirectSum.decompose grading x n,
    J.is_homogeneous' n hxJ, hn⟩

section FinitePointSeparation

variable (K : Type u) [Field K] {G : Type*} [Fintype G]
variable (d : ℕ) (p : G → scheme K d)

include p

/-- The finite set of homogeneous point ideals occurring in a family. -/
noncomputable def pointIdeals :
    Finset (HomogeneousIdeal (homogeneousGrading K d)) := by
  classical
  exact Finset.univ.image fun g ↦ (p g).asHomogeneousIdeal

/-- The inclusion-maximal point ideals in a finite family. -/
noncomputable def maximalPointIdeals :
    Finset (HomogeneousIdeal (homogeneousGrading K d)) := by
  classical
  exact (pointIdeals K d p).filter
    (Maximal fun I ↦ I ∈ pointIdeals K d p)

theorem pointIdeal_mem (g : G) :
    (p g).asHomogeneousIdeal ∈ pointIdeals K d p := by
  classical
  exact Finset.mem_image.mpr ⟨g, Finset.mem_univ g, rfl⟩

variable [Nonempty G] in
theorem maximalPointIdeals_nonempty :
    (maximalPointIdeals K d p).Nonempty := by
  classical
  obtain ⟨I, hI⟩ := (pointIdeals K d p).exists_maximal
    ⟨(p (Classical.choice inferInstance)).asHomogeneousIdeal,
      pointIdeal_mem K d p _⟩
  exact ⟨I, Finset.mem_filter.mpr ⟨hI.1, hI⟩⟩

/-- A point of the original family whose ideal is a selected maximal ideal. -/
noncomputable def maximalPointIndex
    (I : ↑(maximalPointIdeals K d p)) : G := by
  classical
  exact Classical.choose <| Finset.mem_image.mp
    ((Finset.mem_filter.mp I.property).1)

theorem maximalPointIndex_spec
    (I : ↑(maximalPointIdeals K d p)) :
    (p (maximalPointIndex K d p I)).asHomogeneousIdeal = I.1 :=
  by
    classical
    exact (Classical.choose_spec <| Finset.mem_image.mp
      ((Finset.mem_filter.mp I.property).1)).2

theorem maximalPointIdeal_maximal
    (I : ↑(maximalPointIdeals K d p)) :
    Maximal (fun J ↦ J ∈ pointIdeals K d p) I.1 :=
  by
    classical
    exact (Finset.mem_filter.mp I.property).2

theorem maximalPointIdeal_not_le
    (I J : ↑(maximalPointIdeals K d p)) (hIJ : I ≠ J) :
    ¬ J.1 ≤ I.1 := by
  classical
  intro hJI
  have hIJ' : I.1 ≤ J.1 :=
    (maximalPointIdeal_maximal K d p J).2
      (Finset.mem_filter.mp I.property).1 hJI
  exact hIJ (Subtype.ext (le_antisymm hIJ' hJI))

theorem maximalPointIdeal_isPrime
    (I : ↑(maximalPointIdeals K d p)) :
    I.1.toIdeal.IsPrime := by
  rw [← maximalPointIndex_spec K d p I]
  exact (p (maximalPointIndex K d p I)).isPrime

theorem maximalPointIdeal_relevant
    (I : ↑(maximalPointIdeals K d p)) :
    ¬ HomogeneousIdeal.irrelevant (homogeneousGrading K d) ≤ I.1 := by
  rw [← maximalPointIndex_spec K d p I]
  exact (p (maximalPointIndex K d p I)).not_irrelevant_le

/-- The degree of a homogeneous separator belonging to `J` but not `I`. -/
noncomputable def separatorDegreeOfNe
    (I J : ↑(maximalPointIdeals K d p)) (hIJ : I ≠ J) : ℕ :=
  Classical.choose <| exists_homogeneous_mem_not_mem
    (homogeneousGrading K d) I.1 J.1
      (maximalPointIdeal_not_le K d p I J hIJ)

/-- A homogeneous separator belonging to `J` but not `I`. -/
noncomputable def separatorOfNe
    (I J : ↑(maximalPointIdeals K d p)) (hIJ : I ≠ J) :
    homogeneousGrading K d (separatorDegreeOfNe K d p I J hIJ) :=
  Classical.choose <| Classical.choose_spec <|
    exists_homogeneous_mem_not_mem
      (homogeneousGrading K d) I.1 J.1
        (maximalPointIdeal_not_le K d p I J hIJ)

theorem separatorOfNe_mem_right
    (I J : ↑(maximalPointIdeals K d p)) (hIJ : I ≠ J) :
    (separatorOfNe K d p I J hIJ : MvPolynomial (Fin (d + 1)) K) ∈ J.1 :=
  (Classical.choose_spec <| Classical.choose_spec <|
    exists_homogeneous_mem_not_mem
      (homogeneousGrading K d) I.1 J.1
        (maximalPointIdeal_not_le K d p I J hIJ)).1

theorem separatorOfNe_not_mem_left
    (I J : ↑(maximalPointIdeals K d p)) (hIJ : I ≠ J) :
    (separatorOfNe K d p I J hIJ : MvPolynomial (Fin (d + 1)) K) ∉ I.1 :=
  (Classical.choose_spec <| Classical.choose_spec <|
    exists_homogeneous_mem_not_mem
      (homogeneousGrading K d) I.1 J.1
        (maximalPointIdeal_not_le K d p I J hIJ)).2

/-- A total separator family, with the diagonal entry set to `1`. -/
noncomputable def separator
    (I J : ↑(maximalPointIdeals K d p)) :
    MvPolynomial (Fin (d + 1)) K := by
  classical
  exact if hIJ : I = J then 1 else separatorOfNe K d p I J hIJ

/-- The homogeneous degree of `separator`. -/
noncomputable def separatorDegree
    (I J : ↑(maximalPointIdeals K d p)) : ℕ := by
  classical
  exact if hIJ : I = J then 0 else separatorDegreeOfNe K d p I J hIJ

theorem separator_mem_degree
    (I J : ↑(maximalPointIdeals K d p)) :
    separator K d p I J ∈
      homogeneousGrading K d (separatorDegree K d p I J) := by
  classical
  by_cases hIJ : I = J
  · subst J
    rw [separator, dif_pos rfl, separatorDegree, dif_pos rfl]
    exact SetLike.GradedOne.one_mem
  · rw [separator, dif_neg hIJ, separatorDegree, dif_neg hIJ]
    exact (separatorOfNe K d p I J hIJ).property

theorem separator_mem_right
    (I J : ↑(maximalPointIdeals K d p)) (hIJ : I ≠ J) :
    separator K d p I J ∈ J.1 := by
  classical
  rw [separator, dif_neg hIJ]
  exact separatorOfNe_mem_right K d p I J hIJ

theorem separator_not_mem_left
    (I J : ↑(maximalPointIdeals K d p)) :
    separator K d p I J ∉ I.1 := by
  classical
  by_cases hIJ : I = J
  · subst J
    rw [separator, dif_pos rfl]
    intro hOne
    exact (maximalPointIdeal_isPrime K d p I).ne_top
      (I.1.toIdeal.eq_top_iff_one.mpr hOne)
  · rw [separator, dif_neg hIJ]
    exact separatorOfNe_not_mem_left K d p I J hIJ

/-- The degree of the product of all separators associated to `I`. -/
noncomputable def rawSeparatorDegree
    (I : ↑(maximalPointIdeals K d p)) : ℕ :=
  ∑ J, separatorDegree K d p I J

/-- The product which vanishes at every other maximal point ideal and does
not vanish at `I`. -/
noncomputable def rawSeparator
    (I : ↑(maximalPointIdeals K d p)) :
    MvPolynomial (Fin (d + 1)) K :=
  ∏ J, separator K d p I J

theorem rawSeparator_mem_degree
    (I : ↑(maximalPointIdeals K d p)) :
    rawSeparator K d p I ∈
      homogeneousGrading K d (rawSeparatorDegree K d p I) := by
  classical
  simpa only [rawSeparator, rawSeparatorDegree, Finset.prod_filter,
      Finset.sum_filter] using
    (SetLike.prod_mem_graded (homogeneousGrading K d)
      (fun J ↦ separatorDegree K d p I J)
      (fun J ↦ separator K d p I J) (F := Finset.univ)
      (fun J _ ↦ separator_mem_degree K d p I J))

theorem rawSeparator_mem_other
    (I J : ↑(maximalPointIdeals K d p)) (hIJ : I ≠ J) :
    rawSeparator K d p I ∈ J.1 := by
  classical
  rw [rawSeparator]
  rw [← show separator K d p I J *
      (∏ L ∈ Finset.univ.erase J, separator K d p I L) =
        ∏ L, separator K d p I L by
    simpa only [Finset.prod_filter] using
      (Finset.mul_prod_erase Finset.univ
        (fun L ↦ separator K d p I L) (Finset.mem_univ J))]
  exact J.1.toIdeal.mul_mem_right _
    (separator_mem_right K d p I J hIJ)

theorem rawSeparator_not_mem
    (I : ↑(maximalPointIdeals K d p)) :
    rawSeparator K d p I ∉ I.1 := by
  classical
  letI : I.1.toIdeal.IsPrime := maximalPointIdeal_isPrime K d p I
  intro h
  have h' : (∏ J ∈ Finset.univ, separator K d p I J) ∈ I.1 := by
    simpa only [rawSeparator, Finset.prod_filter] using h
  have h'' : ∃ J ∈ Finset.univ, separator K d p I J ∈ I.1 :=
    Ideal.IsPrime.prod_mem_iff.mp h'
  obtain ⟨J, -, hJ⟩ := h''
  exact separator_not_mem_left K d p I J hJ

/-- A coordinate which does not vanish at a selected maximal point ideal. -/
noncomputable def nonvanishingCoordinate
    (I : ↑(maximalPointIdeals K d p)) : Fin (d + 1) :=
  Classical.choose <| exists_coordinate_not_mem K d
    (p (maximalPointIndex K d p I))

theorem nonvanishingCoordinate_not_mem
    (I : ↑(maximalPointIdeals K d p)) :
    coordinate K (nonvanishingCoordinate K d p I) ∉ I.1 := by
  rw [← maximalPointIndex_spec K d p I]
  exact Classical.choose_spec <| exists_coordinate_not_mem K d
    (p (maximalPointIndex K d p I))

/-- A positive common degree to which all raw separators can be raised by
multiplication with nonvanishing coordinates. -/
noncomputable def commonSeparatorDegree : ℕ :=
  (∑ I : ↑(maximalPointIdeals K d p), rawSeparatorDegree K d p I) + 1

theorem rawSeparatorDegree_le_commonSeparatorDegree
    (I : ↑(maximalPointIdeals K d p)) :
    rawSeparatorDegree K d p I ≤ commonSeparatorDegree K d p := by
  classical
  have hsum : rawSeparatorDegree K d p I ≤
      ∑ J : ↑(maximalPointIdeals K d p), rawSeparatorDegree K d p J :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ I)
  exact hsum.trans (Nat.le_add_right _ _)

theorem commonSeparatorDegree_pos :
    0 < commonSeparatorDegree K d p := by
  exact Nat.zero_lt_succ _

/-- A separator rescaled to the common positive degree. -/
noncomputable def adjustedSeparator
    (I : ↑(maximalPointIdeals K d p)) :
    MvPolynomial (Fin (d + 1)) K :=
  rawSeparator K d p I *
    coordinate K (nonvanishingCoordinate K d p I) ^
      (commonSeparatorDegree K d p - rawSeparatorDegree K d p I)

theorem adjustedSeparator_mem_degree
    (I : ↑(maximalPointIdeals K d p)) :
    adjustedSeparator K d p I ∈
      homogeneousGrading K d (commonSeparatorDegree K d p) := by
  have hraw := rawSeparator_mem_degree K d p I
  have hcoord := coordinate_mem_degreeOne K
    (nonvanishingCoordinate K d p I)
  have hpow := SetLike.pow_mem_graded
    (commonSeparatorDegree K d p - rawSeparatorDegree K d p I) hcoord
  have hmul := SetLike.mul_mem_graded hraw hpow
  simpa only [adjustedSeparator, nsmul_eq_mul, Nat.cast_id, mul_one,
      Nat.add_sub_of_le
        (rawSeparatorDegree_le_commonSeparatorDegree K d p I)] using hmul

theorem adjustedSeparator_not_mem
    (I : ↑(maximalPointIdeals K d p)) :
    adjustedSeparator K d p I ∉ I.1 := by
  intro h
  have hprime := maximalPointIdeal_isPrime K d p I
  obtain hraw | hpow := hprime.mem_or_mem h
  · exact rawSeparator_not_mem K d p I hraw
  · exact nonvanishingCoordinate_not_mem K d p I
      (hprime.mem_of_pow_mem _ hpow)

theorem adjustedSeparator_mem_other
    (I J : ↑(maximalPointIdeals K d p)) (hIJ : I ≠ J) :
    adjustedSeparator K d p I ∈ J.1 := by
  exact J.1.toIdeal.mul_mem_right _ (rawSeparator_mem_other K d p I J hIJ)

/-- The sum of the common-degree separators. -/
noncomputable def orbitSeparator : MvPolynomial (Fin (d + 1)) K :=
  ∑ I : ↑(maximalPointIdeals K d p), adjustedSeparator K d p I

theorem orbitSeparator_mem_degree :
    orbitSeparator K d p ∈
      homogeneousGrading K d (commonSeparatorDegree K d p) := by
  classical
  rw [orbitSeparator]
  exact (homogeneousGrading K d (commonSeparatorDegree K d p)).sum_mem
    fun I _ ↦ adjustedSeparator_mem_degree K d p I

theorem orbitSeparator_not_mem_maximal
    (I : ↑(maximalPointIdeals K d p)) :
    orbitSeparator K d p ∉ I.1 := by
  classical
  let rest := ∑ J ∈ Finset.univ.erase I, adjustedSeparator K d p J
  have hrest : rest ∈ I.1 := by
    dsimp only [rest]
    exact I.1.toIdeal.sum_mem fun J hJ ↦
      adjustedSeparator_mem_other K d p J I fun hJI ↦ by
        subst J
        exact (Finset.notMem_erase I Finset.univ) hJ
  have hsplit : adjustedSeparator K d p I + rest = orbitSeparator K d p := by
    rw [orbitSeparator]
    dsimp only [rest]
    simpa only [Finset.sum_filter] using
      (Finset.add_sum_erase Finset.univ
        (fun J ↦ adjustedSeparator K d p J) (Finset.mem_univ I))
  intro htotal
  apply adjustedSeparator_not_mem K d p I
  have hsub := I.1.toIdeal.sub_mem htotal hrest
  rw [← hsplit, add_sub_cancel_right] at hsub
  exact hsub

/-- The common-degree separator avoids every point ideal in the original
finite family. -/
theorem orbitSeparator_not_mem (g : G) :
    orbitSeparator K d p ∉ (p g).asHomogeneousIdeal := by
  classical
  obtain ⟨J, hle, hJmax⟩ :=
    (pointIdeals K d p).exists_le_maximal (pointIdeal_mem K d p g)
  let J' : ↑(maximalPointIdeals K d p) :=
    ⟨J, Finset.mem_filter.mpr ⟨hJmax.1, hJmax⟩⟩
  intro h
  exact orbitSeparator_not_mem_maximal K d p J' (hle h)

end FinitePointSeparation

/-- Over any field, a finite nonempty family of projective points is
contained in one positive-degree basic open. -/
theorem exists_positiveDegree_not_mem
    (K : Type u) [Field K] {G : Type*} [Finite G] [Nonempty G]
    (d : ℕ) (p : G → scheme K d) :
    ∃ n : ℕ, 0 < n ∧ ∃ q : homogeneousGrading K d n,
      ∀ g : G,
        (q : MvPolynomial (Fin (d + 1)) K) ∉
          (p g).asHomogeneousIdeal := by
  letI := Fintype.ofFinite G
  exact ⟨commonSeparatorDegree K d p, commonSeparatorDegree_pos K d p,
    ⟨orbitSeparator K d p, orbitSeparator_mem_degree K d p⟩,
    orbitSeparator_not_mem K d p⟩

/-- Over an infinite field, one linear form avoids any finite family of
projective points. -/
theorem exists_degreeOne_not_mem
    (K : Type u) [Field K] [Infinite K]
    {G : Type*} [Finite G] (d : ℕ) (p : G → scheme K d) :
    ∃ q : homogeneousGrading K d 1, ∀ g : G,
      (q : MvPolynomial (Fin (d + 1)) K) ∉ (p g).asHomogeneousIdeal := by
  obtain ⟨q, hq⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (fun g : G ↦ degreeOneVanishingSubmodule K d (p g))
    (fun g ↦ degreeOneVanishingSubmodule_ne_top K d (p g))
  exact ⟨q, fun g ↦ by
    simpa only [mem_degreeOneVanishingSubmodule_iff] using hq g⟩

/-- Every finite orbit on a scheme admitting a closed embedding into
projective space lies in an affine open. -/
theorem hasAffineOrbit_of_isProjectiveFactorization
    (K : Type u) [Field K]
    {G : Type*} [Group G] [Finite G]
    {X : Scheme.{u}} (sigma : SchemeAction G X)
    {f : X ⟶ Spec (.of K)} (hf : IsProjectiveFactorization f) :
    HasAffineOrbit sigma := by
  obtain ⟨d, i, hi, -⟩ := hf
  letI : IsClosedImmersion i := hi
  intro x
  obtain ⟨n, hn, q, hq⟩ := exists_positiveDegree_not_mem K d
    (fun g : G ↦ i (sigma.hom g x))
  let Uamb : (scheme K d).Opens :=
    Proj.basicOpen (homogeneousGrading K d)
      (q : MvPolynomial (Fin (d + 1)) K)
  let U : X.Opens := i ⁻¹ᵁ Uamb
  refine ⟨U, ?_, ?_⟩
  · exact (Proj.isAffineOpen_basicOpen (homogeneousGrading K d)
      (q : MvPolynomial (Fin (d + 1)) K) q.property hn).preimage i
  · intro g
    change i (sigma.hom g x) ∈ Uamb
    exact (Proj.mem_basicOpen
      (homogeneousGrading K d) (q : MvPolynomial (Fin (d + 1)) K) _).2 (hq g)

section ProjectiveProducts

variable (K : Type u) [Field K]

/-- Projectivity over `Spec K`, regarded as an object property on the slice
category. -/
abbrev projectiveOver : ObjectProperty (Over (Spec (.of K))) :=
  fun X ↦ IsProjectiveFactorization X.hom

instance projectiveOver_isClosedUnderIsomorphisms :
    (projectiveOver K).IsClosedUnderIsomorphisms := by
  constructor
  intro X Y e hX
  let eleft : Y.left ≅ X.left := (Over.forget _).mapIso e.symm
  letI : IsClosedImmersion eleft.hom := inferInstance
  have hY : IsProjectiveFactorization (eleft.hom ≫ X.hom) :=
    hX.comp_isClosedImmersion eleft.hom
  have heq : eleft.hom ≫ X.hom = Y.hom := by
    change e.inv.left ≫ X.hom = Y.hom
    exact e.inv.w
  rw [heq] at hY
  exact hY

/-- Binary products of projective schemes in the slice remain projective,
using the checked scheme-level Segre embedding. -/
theorem binaryProduct_isProjectiveFactorization
    (X Y : Over (Spec (.of K)))
    (hX : IsProjectiveFactorization X.hom)
    (hY : IsProjectiveFactorization Y.hom) :
    IsProjectiveFactorization (X ⨯ Y).hom := by
  have hpull : IsProjectiveFactorization
      (pullback.fst X.hom Y.hom ≫ X.hom) :=
    isProjectiveFactorization_fiberProduct
      (standardSegreEmbeddings K) hX hY
  have hcomp :
      (Over.prodLeftIsoPullback X Y).hom ≫
          (pullback.fst X.hom Y.hom ≫ X.hom) =
        (X ⨯ Y).hom := by
    rw [← Category.assoc, Over.prodLeftIsoPullback_hom_fst]
    exact (Limits.prod.fst : X ⨯ Y ⟶ X).w
  have hprod := hpull.comp_isClosedImmersion
    (Over.prodLeftIsoPullback X Y).hom
  rw [hcomp] at hprod
  exact hprod

instance projectiveOver_isClosedUnderBinaryProducts :
    (projectiveOver K).IsClosedUnderBinaryProducts := by
  apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
  rintro _ ⟨F, hF⟩
  let X := F.obj ⟨WalkingPair.left⟩
  let Y := F.obj ⟨WalkingPair.right⟩
  let e : limit F ≅ X ⨯ Y :=
    HasLimit.isoOfNatIso (diagramIsoPair F)
  apply (projectiveOver K).prop_of_iso e.symm
  exact binaryProduct_isProjectiveFactorization K X Y
    (hF ⟨WalkingPair.left⟩) (hF ⟨WalkingPair.right⟩)

/-- A nonempty finite product of objects satisfying an isomorphism-stable,
binary-product-stable property again satisfies the property.  This variant
deliberately needs no terminal-object hypothesis. -/
theorem ObjectProperty.prop_product_fin_succ
    {C : Type*} [Category* C] [HasFiniteProducts C] (P : ObjectProperty C)
    [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderBinaryProducts]
    (n : ℕ) (f : Fin (n + 1) → C)
    (hf : ∀ i, P (f i)) : P (∏ᶜ f) := by
  induction n with
  | zero =>
      let c : Fan f := Fan.mk (f 0) (fun i ↦ eqToHom (congrArg f (Fin.eq_zero i).symm))
      let hc : IsLimit c := Fan.IsLimit.mk c
        (fun s ↦ s.proj 0)
        (by
          intro s i
          have hi : i = 0 := Fin.eq_zero i
          subst i
          simp [c])
        (by
          intro s m hm
          simpa [c] using hm 0)
      let e : ∏ᶜ f ≅ f 0 :=
        IsLimit.conePointUniqueUpToIso (limit.isLimit (Discrete.functor f)) hc
      exact P.prop_of_iso e.symm (hf 0)
  | succ n ih =>
      let tail : Fin (n + 1) → C := fun i ↦ f i.succ
      let c₁ : Fan tail := Fan.mk (∏ᶜ tail) (fun i ↦ Pi.π tail i)
      let hc₁ : IsLimit c₁ := limit.isLimit (Discrete.functor tail)
      have htail : P (∏ᶜ tail) := ih tail (fun i ↦ hf i.succ)
      let c₂ : BinaryFan (f 0) c₁.pt :=
        BinaryFan.mk Limits.prod.fst Limits.prod.snd
      let hc₂ : IsLimit c₂ := Limits.prodIsProd (f 0) c₁.pt
      let c : Fan f := extendFan c₁ c₂
      let hc : IsLimit c := extendFanIsLimit f hc₁ hc₂
      let e : ∏ᶜ f ≅ c.pt :=
        IsLimit.conePointUniqueUpToIso (limit.isLimit (Discrete.functor f)) hc
      apply P.prop_of_iso e.symm
      exact P.prop_prod (f 0) c₁.pt (hf 0) htail

/-- The Tau Ceti projective-line structure map is the standard projective
space structure map in dimension one. -/
theorem projectiveLine_structureMap_eq_toSpec :
    ProjectiveLine.structureMap K = toSpec K 1 := by
  rfl

/-- Every nonempty finite relative power of the projective line is
projective over the ground field. -/
theorem projectiveLinePower_isProjectiveFactorization (d : ℕ) :
    IsProjectiveFactorization
      (PermutationPower.power (Spec (.of K)) (Fin (d + 1))
        (Over.mk (ProjectiveLine.structureMap K))).hom := by
  apply ObjectProperty.prop_product_fin_succ (projectiveOver K) d
  intro i
  change IsProjectiveFactorization (ProjectiveLine.structureMap K)
  rw [projectiveLine_structureMap_eq_toSpec K]
  exact isProjectiveFactorization_toSpec K 1

/-- Every permutation orbit in a nonempty power of the projective line lies
in an affine open. -/
theorem projectiveLinePower_hasAffineOrbit (d : ℕ) :
    HasAffineOrbit
      (PermutationPower.action (Spec (.of K)) (Fin (d + 1))
        (Over.mk (ProjectiveLine.structureMap K))) :=
  hasAffineOrbit_of_isProjectiveFactorization K _
    (projectiveLinePower_isProjectiveFactorization K d)

end ProjectiveProducts

end MazurTorsion.AlgebraicGeometry.Jacobian.ProjectiveFiniteOrbit
