/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentLocalization
import MazurTorsion.Upstream.CoherentCohomologyFinite.HomogeneousAwayCoefficientAlgebra
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSpectrumClosedImmersion
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveSpace
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Coefficient base change for standard projective space

The standard projective space defined by the homogeneous polynomial
ring commutes with extension of the coefficient ring.  This file keeps
the statement concrete: the morphism induced by coefficient extension
forms a pullback square with the two structural morphisms.
-/

open CategoryTheory Limits AlgebraicGeometry
open HomogeneousIdeal HomogeneousLocalization
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech
open scoped TensorProduct

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-- Coefficient extension on homogeneous polynomial rings, preserving
the standard grading. -/
def coefficientGradedHom
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) (d : ℕ) :
    homogeneousGrading k d →+*ᵍ
      homogeneousGrading R d where
  toRingHom := MvPolynomial.map φ
  map_mem := fun hp =>
    MvPolynomial.IsHomogeneous.map hp φ

@[simp]
theorem coefficientGradedHom_apply
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) (d : ℕ)
    (p : MvPolynomial (Fin (d + 1)) k) :
    coefficientGradedHom φ d p =
      MvPolynomial.map φ p :=
  rfl

@[simp]
theorem coefficientGradedHom_coordinate
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) {d : ℕ} (i : Fin (d + 1)) :
    coefficientGradedHom φ d (coordinate k i) =
      coordinate R i := by
  rw [coefficientGradedHom_apply]
  exact MvPolynomial.map_X φ i

/-- The coefficient-extension map satisfies the irrelevant-ideal
hypothesis required by `Proj.map`. -/
theorem coefficientIrrelevantLE
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) (d : ℕ) :
    (homogeneousGrading R d)₊ ≤
      (homogeneousGrading k d)₊.map
        (coefficientGradedHom φ d) := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro n hn p hp
  have hpIrrelevant :
      p ∈ (homogeneousGrading R d)₊.toIdeal :=
    HomogeneousIdeal.mem_irrelevant_of_mem
      (homogeneousGrading R d) hn hp
  have hpSpan :
      p ∈ Ideal.span
        (Set.range
          (coordinate R :
            Fin (d + 1) →
              MvPolynomial (Fin (d + 1)) R)) :=
    (irrelevant_le_coordinateIdeal R d) hpIrrelevant
  refine (Ideal.span_le.2 ?_) hpSpan
  intro x hx
  obtain ⟨i, rfl⟩ := hx
  rw [← coefficientGradedHom_coordinate φ i]
  exact Ideal.mem_map_of_mem
    (coefficientGradedHom φ d)
    (HomogeneousIdeal.mem_irrelevant_of_mem
      (homogeneousGrading k d) Nat.zero_lt_one
      (coordinate_mem_degreeOne k i))

/-- The morphism from projective space after coefficient extension to
the original projective space. -/
def coefficientMap
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) (d : ℕ) :
    scheme R d ⟶ scheme k d :=
  Proj.map (coefficientGradedHom φ d)
    (coefficientIrrelevantLE φ d)

@[simp]
theorem coefficientMap_preimage_standardChart
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) (d : ℕ)
    (i : Fin (d + 1)) :
    coefficientMap φ d ⁻¹ᵁ standardChart k i =
      standardChart R i := by
  simpa only [coefficientMap, standardChart,
    coefficientGradedHom_coordinate] using
      (Proj.map_preimage_basicOpen
        (coefficientGradedHom φ d)
        (coefficientIrrelevantLE φ d)
        (coordinate k i))

@[simp]
theorem coefficientGradedHom_variableProduct
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) {d : ℕ}
    (I : Finset (Fin (d + 1))) :
    coefficientGradedHom φ d
        (variableProduct (k := k) I) =
      variableProduct (k := R) I := by
  rw [coefficientGradedHom_apply]
  simp only [variableProduct, map_prod, MvPolynomial.map_X]

/-- Coefficient extension on the degree-zero homogeneous localization
away from a product of projective coordinates. -/
def coefficientVariableProductAwayMap
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) {d : ℕ}
    (I : Finset (Fin (d + 1))) :
    Away
        (homogeneousGrading k d)
        (variableProduct (k := k) I) →+*
      Away
        (homogeneousGrading R d)
        (variableProduct (k := R) I) :=
  homogeneousAwayMapTo
    (coefficientGradedHom φ d)
    (variableProduct (k := k) I)
    (variableProduct (k := R) I)
    (coefficientGradedHom_variableProduct φ I)

@[simp]
theorem coefficientVariableProductAwayMap_degreeZeroFraction
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) {d : ℕ}
    (I : Finset (Fin (d + 1)))
    (a : AdmissibleExponent (ι := Fin (d + 1)) 0 I) :
    coefficientVariableProductAwayMap φ I
        (degreeZeroFraction (k := k) I a) =
      degreeZeroFraction (k := R) I a := by
  rw [degreeZeroFraction, degreeZeroFraction,
    coefficientVariableProductAwayMap,
    homogeneousAwayMapTo_mk
      (ht := variableProduct_mem_degreeCard
        (k := R) I)]
  congr 1
  rw [coefficientGradedHom_apply, MvPolynomial.map_monomial, map_one]

/-- The Laurent monomial fractions form the standard basis of a
projective coordinate-product localization. -/
def degreeZeroFractionBasis
    (k : Type u) [CommRing k] {d : ℕ}
    (I : Finset (Fin (d + 1))) :
    Module.Basis
      (AdmissibleExponent (ι := Fin (d + 1)) 0 I)
      k
      (Away
        (homogeneousGrading k d)
        (variableProduct (k := k) I)) :=
  Finsupp.basisSingleOne.map
    (degreeZeroFractionLinearEquiv (k := k) I)

@[simp]
theorem degreeZeroFractionBasis_apply
    (k : Type u) [CommRing k] {d : ℕ}
    (I : Finset (Fin (d + 1)))
    (a : AdmissibleExponent (ι := Fin (d + 1)) 0 I) :
    degreeZeroFractionBasis k I a =
      degreeZeroFraction (k := k) I a := by
  simp [degreeZeroFractionBasis,
    degreeZeroFractionLinearEquiv,
    degreeZeroFractionLinearMap]

/-- The coefficient algebra on the target localization obtained by
composing `k → R` with its usual `R`-algebra structure. -/
@[reducible] private def coefficientVariableProductAwayAlgebra
    (k R : Type u) [CommRing k] [CommRing R]
    [Algebra k R] {d : ℕ}
    (I : Finset (Fin (d + 1))) :
    Algebra k
      (Away
        (homogeneousGrading R d)
        (variableProduct (k := R) I)) :=
  ((algebraMap R
      (Away
        (homogeneousGrading R d)
        (variableProduct (k := R) I))).comp
    (algebraMap k R)).toAlgebra

/-- Coefficient extension on a coordinate-product localization as a
`k`-algebra map, using the composite coefficient algebra on the
target. -/
private def coefficientVariableProductAwayAlgHom
    (k R : Type u) [CommRing k] [CommRing R]
    [Algebra k R] {d : ℕ}
    (I : Finset (Fin (d + 1))) :
    letI : Algebra k
        (Away
          (homogeneousGrading R d)
          (variableProduct (k := R) I)) :=
      coefficientVariableProductAwayAlgebra k R I
    Away
        (homogeneousGrading k d)
        (variableProduct (k := k) I) →ₐ[k]
      Away
        (homogeneousGrading R d)
        (variableProduct (k := R) I) := by
  letI : Algebra k
      (Away
        (homogeneousGrading R d)
        (variableProduct (k := R) I)) :=
    coefficientVariableProductAwayAlgebra k R I
  refine
    { __ :=
        coefficientVariableProductAwayMap
          (algebraMap k R) I
      commutes' := ?_ }
  intro r
  rw [homogeneousAway_algebraMap_eq_mk
    (variableProduct (k := k) I)
    (variableProduct_mem_degreeCard (k := k) I)]
  change
    coefficientVariableProductAwayMap
        (algebraMap k R) I
        (Away.mk
          (homogeneousGrading k d)
          (variableProduct_mem_degreeCard (k := k) I)
          0
          (algebraMap k
            (MvPolynomial (Fin (d + 1)) k) r)
          _) =
      algebraMap k
        (Away
          (homogeneousGrading R d)
          (variableProduct (k := R) I)) r
  rw [coefficientVariableProductAwayMap,
    homogeneousAwayMapTo_mk
      (h := coefficientGradedHom_variableProduct
        (algebraMap k R) I)
      (ht := variableProduct_mem_degreeCard
        (k := R) I)]
  change
    Away.mk
        (homogeneousGrading R d)
        (variableProduct_mem_degreeCard (k := R) I)
        0
        (MvPolynomial.map (algebraMap k R)
          (algebraMap k
            (MvPolynomial (Fin (d + 1)) k) r))
        _ =
      algebraMap R
        (Away
          (homogeneousGrading R d)
          (variableProduct (k := R) I))
        (algebraMap k R r)
  rw [homogeneousAway_algebraMap_eq_mk
    (variableProduct (k := R) I)
    (variableProduct_mem_degreeCard (k := R) I)]
  congr 1
  simp

@[simp]
theorem coefficientVariableProductAwayMap_algebraMap
    (k R : Type u) [CommRing k] [CommRing R]
    [Algebra k R] {d : ℕ}
    (I : Finset (Fin (d + 1))) (r : k) :
    coefficientVariableProductAwayMap
        (algebraMap k R) I
        (algebraMap k
          (Away
            (homogeneousGrading k d)
            (variableProduct (k := k) I)) r) =
      algebraMap R
        (Away
          (homogeneousGrading R d)
          (variableProduct (k := R) I))
        (algebraMap k R r) := by
  letI : Algebra k
      (Away
        (homogeneousGrading R d)
        (variableProduct (k := R) I)) :=
    coefficientVariableProductAwayAlgebra k R I
  change
    (coefficientVariableProductAwayAlgHom k R I)
        (algebraMap k
          (Away
            (homogeneousGrading k d)
            (variableProduct (k := k) I)) r) =
      algebraMap k
        (Away
          (homogeneousGrading R d)
          (variableProduct (k := R) I)) r
  exact
    (coefficientVariableProductAwayAlgHom
      k R I).commutes r

/-- The canonical ring map from the scalar extension of a standard
projective chart ring to the corresponding chart ring over `R`. -/
def coefficientVariableProductTensorMap
    (k R : Type u) [CommRing k] [CommRing R]
    [Algebra k R] {d : ℕ}
    (I : Finset (Fin (d + 1))) :
    (R ⊗[k]
        Away
          (homogeneousGrading k d)
          (variableProduct (k := k) I)) →+*
      Away
        (homogeneousGrading R d)
        (variableProduct (k := R) I) := by
  letI : Algebra k
      (Away
        (homogeneousGrading R d)
        (variableProduct (k := R) I)) :=
    coefficientVariableProductAwayAlgebra k R I
  let left :
      R →ₐ[k]
        Away
          (homogeneousGrading R d)
          (variableProduct (k := R) I) :=
    { __ :=
        algebraMap R
          (Away
            (homogeneousGrading R d)
            (variableProduct (k := R) I))
      commutes' := fun _ => rfl }
  exact
    (Algebra.TensorProduct.lift
      left
      (coefficientVariableProductAwayAlgHom k R I)
      (fun _ _ => Commute.all _ _)).toRingHom

/-- The canonical chart base-change map is `R`-linear. -/
def coefficientVariableProductTensorAlgHom
    (k R : Type u) [CommRing k] [CommRing R]
    [Algebra k R] {d : ℕ}
    (I : Finset (Fin (d + 1))) :
    (R ⊗[k]
        Away
          (homogeneousGrading k d)
          (variableProduct (k := k) I)) →ₐ[R]
      Away
        (homogeneousGrading R d)
        (variableProduct (k := R) I) where
  __ := coefficientVariableProductTensorMap k R I
  commutes' r := by
    simp [coefficientVariableProductTensorMap,
      coefficientVariableProductAwayAlgHom,
      coefficientVariableProductAwayAlgebra]

@[simp]
theorem coefficientVariableProductTensorAlgHom_baseChangeBasis
    (k R : Type u) [CommRing k] [CommRing R]
    [Algebra k R] {d : ℕ}
    (I : Finset (Fin (d + 1)))
    (a : AdmissibleExponent (ι := Fin (d + 1)) 0 I) :
    coefficientVariableProductTensorAlgHom k R I
        ((degreeZeroFractionBasis k I).baseChange R a) =
      degreeZeroFractionBasis R I a := by
  rw [Module.Basis.baseChange_apply,
    degreeZeroFractionBasis_apply,
    degreeZeroFractionBasis_apply]
  change
    coefficientVariableProductTensorMap k R I
        (1 ⊗ₜ[k] degreeZeroFraction (k := k) I a) =
      degreeZeroFraction (k := R) I a
  simp [coefficientVariableProductTensorMap,
    coefficientVariableProductAwayAlgHom]

/-- The canonical chart scalar-extension map is the linear
equivalence carrying the base-changed Laurent basis to the Laurent
basis over the new coefficient ring. -/
def coefficientVariableProductTensorLinearEquiv
    (k R : Type u) [CommRing k] [CommRing R]
    [Algebra k R] {d : ℕ}
    (I : Finset (Fin (d + 1))) :
    (R ⊗[k]
        Away
          (homogeneousGrading k d)
          (variableProduct (k := k) I)) ≃ₗ[R]
      Away
        (homogeneousGrading R d)
        (variableProduct (k := R) I) :=
  ((degreeZeroFractionBasis k I).baseChange R).equiv
    (degreeZeroFractionBasis R I)
    (Equiv.refl _)

theorem coefficientVariableProductTensorLinearEquiv_apply
    (k R : Type u) [CommRing k] [CommRing R]
    [Algebra k R] {d : ℕ}
    (I : Finset (Fin (d + 1)))
    (x :
      R ⊗[k]
        Away
          (homogeneousGrading k d)
          (variableProduct (k := k) I)) :
    coefficientVariableProductTensorLinearEquiv k R I x =
      coefficientVariableProductTensorAlgHom k R I x := by
  let b := (degreeZeroFractionBasis k I).baseChange R
  have hmaps :
      (coefficientVariableProductTensorLinearEquiv
          k R I).toLinearMap =
        (coefficientVariableProductTensorAlgHom
          k R I).toLinearMap := by
    apply b.ext
    intro a
    change
      coefficientVariableProductTensorLinearEquiv k R I (b a) =
        coefficientVariableProductTensorAlgHom k R I (b a)
    rw [coefficientVariableProductTensorLinearEquiv,
      Module.Basis.equiv_apply, Equiv.refl_apply,
      coefficientVariableProductTensorAlgHom_baseChangeBasis]
  exact LinearMap.congr_fun hmaps x

/-- Coefficient extension is an isomorphism on every standard
projective coordinate-product chart ring. -/
theorem coefficientVariableProductTensorMap_bijective
    (k R : Type u) [CommRing k] [CommRing R]
    [Algebra k R] {d : ℕ}
    (I : Finset (Fin (d + 1))) :
    Function.Bijective
      (coefficientVariableProductTensorMap k R I) := by
  have hfun :
      (coefficientVariableProductTensorLinearEquiv
          k R I : _ → _) =
        coefficientVariableProductTensorMap k R I :=
    funext fun x =>
      coefficientVariableProductTensorLinearEquiv_apply
        k R I x
  rw [← hfun]
  exact
    (coefficientVariableProductTensorLinearEquiv
      k R I).bijective

theorem coefficientVariableProductTensorMap_comp_includeLeft
    (k R : Type u) [CommRing k] [CommRing R]
    [Algebra k R] {d : ℕ}
    (I : Finset (Fin (d + 1))) :
    (coefficientVariableProductTensorMap k R I).comp
        (Algebra.TensorProduct.includeLeftRingHom :
          R →+*
            R ⊗[k]
              Away
                (homogeneousGrading k d)
                (variableProduct (k := k) I)) =
      algebraMap R
        (Away
          (homogeneousGrading R d)
          (variableProduct (k := R) I)) := by
  ext r
  simp [coefficientVariableProductTensorMap,
    coefficientVariableProductAwayAlgHom]

theorem coefficientVariableProductTensorMap_comp_includeRight
    (k R : Type u) [CommRing k] [CommRing R]
    [Algebra k R] {d : ℕ}
    (I : Finset (Fin (d + 1))) :
    (coefficientVariableProductTensorMap k R I).comp
        (Algebra.TensorProduct.includeRight :
          Away
              (homogeneousGrading k d)
              (variableProduct (k := k) I) →ₐ[k]
            R ⊗[k]
              Away
                (homogeneousGrading k d)
                (variableProduct (k := k) I)) =
      coefficientVariableProductAwayMap
        (algebraMap k R) I := by
  ext x
  simp [coefficientVariableProductTensorMap,
    coefficientVariableProductAwayAlgHom]

/-- The affine square on a coordinate-product chart is a pullback
square. -/
theorem isPullback_coefficientVariableProductAway
    (k R : Type u) [CommRing k] [CommRing R]
    [Algebra k R] {d : ℕ}
    (I : Finset (Fin (d + 1))) :
    IsPullback
      (Spec.map
        (CommRingCat.ofHom
          (algebraMap R
            (Away
              (homogeneousGrading R d)
              (variableProduct (k := R) I)))))
      (Spec.map
        (CommRingCat.ofHom
          (coefficientVariableProductAwayMap
            (algebraMap k R) I)))
      (Spec.map
        (CommRingCat.ofHom (algebraMap k R)))
      (Spec.map
        (CommRingCat.ofHom
          (algebraMap k
            (Away
              (homogeneousGrading k d)
              (variableProduct (k := k) I))))) := by
  let tensorMap :=
    coefficientVariableProductTensorMap k R I
  letI :
      IsIso (CommRingCat.ofHom tensorMap) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (coefficientVariableProductTensorMap_bijective
        k R I)
  let e :
      Spec
          (CommRingCat.of
            (Away
              (homogeneousGrading R d)
              (variableProduct (k := R) I))) ≅
        pullback
          (Spec.map
            (CommRingCat.ofHom (algebraMap k R)))
          (Spec.map
            (CommRingCat.ofHom
              (algebraMap k
                (Away
                  (homogeneousGrading k d)
                  (variableProduct (k := k) I))))) :=
    asIso (Spec.map (CommRingCat.ofHom tensorMap)) ≪≫
      (pullbackSpecIso k R
        (Away
          (homogeneousGrading k d)
          (variableProduct (k := k) I))).symm
  apply IsPullback.of_iso_pullback _ e
  · dsimp only [e]
    simp only [Iso.trans_hom, Iso.symm_hom,
      Category.assoc, pullbackSpecIso_inv_fst, asIso_hom,
      ← Spec.map_comp]
    dsimp only [tensorMap]
    rw [← CommRingCat.ofHom_comp]
    exact congrArg
      (fun f => Spec.map (CommRingCat.ofHom f))
      (coefficientVariableProductTensorMap_comp_includeLeft
        k R I)
  · dsimp only [e]
    simp only [Iso.trans_hom, Iso.symm_hom,
      Category.assoc, pullbackSpecIso_inv_snd, asIso_hom,
      ← Spec.map_comp]
    dsimp only [tensorMap]
    rw [← CommRingCat.ofHom_comp]
    exact congrArg
      (fun f => Spec.map (CommRingCat.ofHom f))
      (coefficientVariableProductTensorMap_comp_includeRight
        k R I)
  · constructor
    simp only [← Spec.map_comp]
    rw [← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    have h :
        (algebraMap R
          (Away
            (homogeneousGrading R d)
            (variableProduct (k := R) I))).comp
            (algebraMap k R) =
          (coefficientVariableProductAwayMap
            (algebraMap k R) I).comp
            (algebraMap k
              (Away
                (homogeneousGrading k d)
                (variableProduct (k := k) I))) := by
      apply RingHom.ext
      intro r
      simpa only [RingHom.comp_apply] using
        (coefficientVariableProductAwayMap_algebraMap
          k R I r).symm
    exact congrArg
      (fun f => Spec.map (CommRingCat.ofHom f)) h

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
