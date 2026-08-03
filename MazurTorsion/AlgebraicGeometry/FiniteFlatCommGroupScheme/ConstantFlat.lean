/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import MazurTorsion.Algebra.HopfLocalizationAway
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.Constant
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.QuasiFiniteFppfHOne

/-!
# The bad-level flat extension of a finite constant group

Let `G` be a finite commutative group and let `N : R`.  Inside the constant group scheme `G_R`,
retain the identity component over all of `Spec R` and retain every other component only over
`D(N)`.  On the function-ring coordinates `R^G`, this is the principal open defined by

`e_N(g) = 1` if `g = 1`, and `e_N(g) = N` otherwise.

The open is stable under the group operations.  We prove this directly by exhibiting the unit
witnesses needed to descend the constant Hopf structure to `R^G[1/e_N]`.  The resulting group
scheme is flat, quasi-finite, quasi-compact, separated, and of finite presentation, and its map
to the constant finite-flat group is an open immersion with range `D(e_N)`.

For `R = ℤ`, `G = Multiplicative (ZMod p)`, and `N = p`, this is Mazur's elementary factor
usually denoted `(Z/pZ)^flat`.  It is finite away from `p` but need not be finite over `ℤ`.
-/

noncomputable section

open CategoryTheory
open scoped TensorProduct CategoryTheory.MonObj

namespace AlgebraicGeometry
namespace QuasiFiniteFlatCommGroupScheme

open FiniteFlatCommGroupScheme

universe u

variable {R G : Type u} [CommRing R] [CommGroup G]

local instance : DecidableEq G := Classical.decEq G

private abbrev ConstantA := ConstantCoordinates R G

/-- The function cutting out the bad-level constant-flat model inside the constant group. -/
noncomputable def constantFlatElement (N : R) : ConstantCoordinates R G := by
  classical
  exact ULift.up (fun g ↦ if g = 1 then 1 else N)

@[simp]
theorem constantFlatElement_down_apply (N : R) (g : G) :
    (constantFlatElement (G := G) N).down g = if g = 1 then 1 else N := by
  classical
  rfl

/-- The complementary function satisfies `e_N * e_N' = N`. -/
noncomputable def constantFlatComplement (N : R) : ConstantCoordinates R G := by
  classical
  exact ULift.up (fun g ↦ if g = 1 then N else 1)

@[simp]
theorem constantFlatComplement_down_apply (N : R) (g : G) :
    (constantFlatComplement (G := G) N).down g = if g = 1 then N else 1 := by
  classical
  rfl

/-- Multiplying the two complementary component functions gives the pullback of `N` from the
base.  In particular, the entire constant group over `D(N)` lies in the principal open
`D(e_N)`. -/
theorem constantFlatElement_mul_complement (N : R) :
    constantFlatElement (G := G) N * constantFlatComplement (G := G) N =
      algebraMap R (ConstantCoordinates R G) N := by
  apply ULift.down_injective
  funext g
  by_cases hg : g = 1 <;> simp [hg]

/-- The base principal open `D(N)` is contained in the componentwise principal open `D(e_N)`.
This is the coordinate-level certificate that the model agrees with the full constant model
away from the bad level. -/
theorem basicOpen_level_le_constantFlatElement (N : R) :
    PrimeSpectrum.basicOpen (algebraMap R (ConstantCoordinates R G) N) ≤
      PrimeSpectrum.basicOpen (constantFlatElement (G := G) N) := by
  rw [← constantFlatElement_mul_complement (G := G) N]
  exact PrimeSpectrum.basicOpen_mul_le_left _ _

noncomputable instance constantCoordinatesModuleFinitePresentation [Finite G] :
    Module.FinitePresentation R (ConstantA (R := R) (G := G)) :=
  Module.FinitePresentation.of_equiv
    (ULift.moduleEquiv (R := R) (M := G → R)).symm

variable [Fintype G]

private noncomputable def comulWitness (N : R) :
    ConstantA (R := R) (G := G) ⊗[R] ConstantA (R := R) (G := G) := by
  classical
  exact (ConstantCoordinates.tensorEval (R := R) (G := G)).symm
    (fun p ↦ if p.1 = 1 then 1 else if p.2 = 1 then 1
      else if p.1 * p.2 = 1 then N * N else N)

private theorem comul_element_mul_witness (N : R) :
    ConstantCoordinates.comulAlgHom (R := R) (G := G)
          (constantFlatElement (G := G) N) * comulWitness (G := G) N =
      constantFlatElement (G := G) N ⊗ₜ[R] constantFlatElement (G := G) N := by
  apply (ConstantCoordinates.tensorEval (R := R) (G := G)).injective
  funext p
  rcases p with ⟨g, h⟩
  simp only [map_mul, Pi.mul_apply, ConstantCoordinates.tensorEval_comulAlgHom,
    comulWitness, AlgEquiv.apply_symm_apply, ConstantCoordinates.tensorEval_tmul,
    constantFlatElement_down_apply]
  by_cases hg : g = 1
  · subst g
    simp
  by_cases hh : h = 1
  · subst h
    simp [hg]
  by_cases hgh : g * h = 1
  · simp [hg, hh, hgh]
  · simp [hg, hh, hgh]

/-- Coordinates of the bad-level constant-flat model. -/
abbrev ConstantFlatCoordinates (R : Type u) [CommRing R]
    (G : Type u) [CommGroup G] (N : R) :=
  Localization.Away (constantFlatElement (G := G) N)

private abbrev iota (N : R) :
    ConstantA (R := R) (G := G) →ₐ[R] ConstantFlatCoordinates R G N :=
  Algebra.algHom R (ConstantA (R := R) (G := G)) (ConstantFlatCoordinates R G N)

private theorem comul_element_isUnit (N : R) :
    IsUnit (((Algebra.TensorProduct.map (iota (G := G) N) (iota (G := G) N)).comp
      (Bialgebra.comulAlgHom R (ConstantA (R := R) (G := G))))
        (constantFlatElement (G := G) N)) := by
  let e := constantFlatElement (G := G) N
  have he : IsUnit
      (algebraMap (ConstantA (R := R) (G := G))
        (ConstantFlatCoordinates R G N) e) :=
    IsLocalization.Away.algebraMap_isUnit e
  have hl : IsUnit
      (Algebra.TensorProduct.includeLeft
        (R := R) (A := ConstantFlatCoordinates R G N)
          (B := ConstantFlatCoordinates R G N)
            (algebraMap (ConstantA (R := R) (G := G))
              (ConstantFlatCoordinates R G N) e)) :=
    he.map (Algebra.TensorProduct.includeLeft
      (R := R) (S := R) (A := ConstantFlatCoordinates R G N)
        (B := ConstantFlatCoordinates R G N)).toMonoidHom
  have hr : IsUnit
      (Algebra.TensorProduct.includeRight
        (R := R) (A := ConstantFlatCoordinates R G N)
          (B := ConstantFlatCoordinates R G N)
            (algebraMap (ConstantA (R := R) (G := G))
              (ConstantFlatCoordinates R G N) e)) :=
    he.map (Algebra.TensorProduct.includeRight
      (R := R) (A := ConstantFlatCoordinates R G N)
        (B := ConstantFlatCoordinates R G N)).toMonoidHom
  have ht : IsUnit
      (algebraMap (ConstantA (R := R) (G := G))
          (ConstantFlatCoordinates R G N) e ⊗ₜ[R]
        algebraMap (ConstantA (R := R) (G := G))
          (ConstantFlatCoordinates R G N) e) := by
    convert hl.mul hr using 1
    simp [Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul]
  have hm := congrArg
    (Algebra.TensorProduct.map (iota (G := G) N) (iota (G := G) N))
      (comul_element_mul_witness (G := G) N)
  rw [map_mul, Algebra.TensorProduct.map_tmul] at hm
  have hp : IsUnit
      ((((Algebra.TensorProduct.map (iota (G := G) N) (iota (G := G) N)).comp
        (Bialgebra.comulAlgHom R (ConstantA (R := R) (G := G))))
          (constantFlatElement (G := G) N)) *
            Algebra.TensorProduct.map (iota (G := G) N) (iota (G := G) N)
              (comulWitness (G := G) N)) := by
    rw [AlgHom.comp_apply]
    change IsUnit
      (Algebra.TensorProduct.map (iota (G := G) N) (iota (G := G) N)
          (ConstantCoordinates.comulAlgHom (R := R) (G := G)
            (constantFlatElement (G := G) N)) *
        Algebra.TensorProduct.map (iota (G := G) N) (iota (G := G) N)
          (comulWitness (G := G) N))
    rw [hm]
    change IsUnit
      (algebraMap (ConstantA (R := R) (G := G))
          (ConstantFlatCoordinates R G N) e ⊗ₜ[R]
        algebraMap (ConstantA (R := R) (G := G))
          (ConstantFlatCoordinates R G N) e)
    exact ht
  letI : IsDedekindFiniteMonoid
      (ConstantFlatCoordinates R G N ⊗[R] ConstantFlatCoordinates R G N) := {
    mul_eq_one_symm := fun {a b} h ↦ by
      calc
        b * a = a * b := Algebra.TensorProduct.instCommSemiring.mul_comm _ _
        _ = 1 := h }
  exact isUnit_of_mul_isUnit_left hp

private theorem counit_element_isUnit (N : R) :
    IsUnit (Bialgebra.counitAlgHom R (ConstantA (R := R) (G := G))
      (constantFlatElement (G := G) N)) := by
  rw [show Bialgebra.counitAlgHom R (ConstantA (R := R) (G := G)) =
    ConstantCoordinates.counitAlgHom (R := R) (G := G) from rfl]
  simp [ConstantCoordinates.counitAlgHom_apply]

private theorem antipode_element (N : R) :
    HopfAlgebra.antipodeAlgHom R (ConstantA (R := R) (G := G))
        (constantFlatElement (G := G) N) =
      constantFlatElement (G := G) N := by
  apply ULift.down_injective
  funext g
  simp only [show HopfAlgebra.antipodeAlgHom R (ConstantA (R := R) (G := G)) =
    ConstantCoordinates.antipodeAlgHom (R := R) (G := G) from rfl,
    ConstantCoordinates.antipodeAlgHom_down_apply, constantFlatElement_down_apply]
  by_cases hg : g = 1
  · simp [hg]
  · simp [hg]

private theorem antipode_element_isUnit (N : R) :
    IsUnit (((Algebra.algHom R (ConstantA (R := R) (G := G))
        (ConstantFlatCoordinates R G N)).comp
      (HopfAlgebra.antipodeAlgHom R (ConstantA (R := R) (G := G))))
        (constantFlatElement (G := G) N)) := by
  rw [AlgHom.comp_apply, antipode_element]
  exact IsLocalization.Away.algebraMap_isUnit _

noncomputable instance constantFlatBialgebra (N : R) :
    Bialgebra R (ConstantFlatCoordinates R G N) :=
  HopfLocalizationAway.bialgebra (constantFlatElement (G := G) N)
    (comul_element_isUnit (G := G) N)
    (counit_element_isUnit (G := G) N)

noncomputable instance constantFlatHopfAlgebra (N : R) :
    HopfAlgebra R (ConstantFlatCoordinates R G N) :=
  HopfLocalizationAway.hopfAlgebra (constantFlatElement (G := G) N)
    (comul_element_isUnit (G := G) N)
    (counit_element_isUnit (G := G) N)
    (antipode_element_isUnit (G := G) N)

noncomputable instance constantFlatIsCocomm (N : R) :
    Coalgebra.IsCocomm R (ConstantFlatCoordinates R G N) where
  comm_comp_comul := by
    have h :
        (Algebra.TensorProduct.comm R (ConstantFlatCoordinates R G N)
          (ConstantFlatCoordinates R G N)).toAlgHom.comp
            (Bialgebra.comulAlgHom R (ConstantFlatCoordinates R G N)) =
          Bialgebra.comulAlgHom R (ConstantFlatCoordinates R G N) := by
      apply IsLocalization.algHom_ext
        (Submonoid.powers (constantFlatElement (G := G) N))
      apply AlgHom.ext
      intro a
      simp only [AlgHom.comp_apply]
      change (Algebra.TensorProduct.comm R _ _)
          (HopfLocalizationAway.comul (constantFlatElement (G := G) N)
            (comul_element_isUnit (G := G) N)
              (algebraMap (ConstantA (R := R) (G := G))
                (ConstantFlatCoordinates R G N) a)) =
        HopfLocalizationAway.comul (constantFlatElement (G := G) N)
          (comul_element_isUnit (G := G) N)
            (algebraMap (ConstantA (R := R) (G := G))
              (ConstantFlatCoordinates R G N) a)
      rw [HopfLocalizationAway.comul_algebraMap,
        Algebra.TensorProduct.comm_comp_map_apply]
      apply congrArg
        (Algebra.TensorProduct.map
          (Algebra.algHom R (ConstantA (R := R) (G := G))
            (ConstantFlatCoordinates R G N))
          (Algebra.algHom R (ConstantA (R := R) (G := G))
            (ConstantFlatCoordinates R G N)))
      change TensorProduct.comm R _ _ (Coalgebra.comul a) = Coalgebra.comul a
      exact Coalgebra.comm_comul R a
    exact congrArg AlgHom.toLinearMap h

/-- The affine bad-level constant-flat group. -/
noncomputable abbrev constantFlatAffine (R : Type u) [CommRing R]
    (G : Type u) [CommGroup G] [Fintype G] (N : R) : AffineCommGroupScheme R :=
  Opposite.op
    ⟨CommHopfAlgCat.of R (ConstantFlatCoordinates R G N), by
      change Coalgebra.IsCocomm R (ConstantFlatCoordinates R G N)
      exact constantFlatIsCocomm (G := G) N⟩

/-- The underlying principal-open immersion into the finite constant group. -/
noncomputable abbrev constantFlatInclusionSchemeMap (N : R) :
    (constantFlatAffine R G N).scheme ⟶ (constant R G).obj.scheme :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (ConstantA (R := R) (G := G)) (ConstantFlatCoordinates R G N)))

instance constantFlatInclusionSchemeMap_isOpenImmersion (N : R) :
    IsOpenImmersion (constantFlatInclusionSchemeMap (G := G) N) := by
  change IsOpenImmersion
    (Spec.map (CommRingCat.ofHom
      (algebraMap (ConstantA (R := R) (G := G)) (ConstantFlatCoordinates R G N))))
  infer_instance

instance constantStructureMap_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (constant R G).obj.structureMap := by
  change LocallyOfFinitePresentation
    (Spec.map (CommRingCat.ofHom (algebraMap R (ConstantA (R := R) (G := G)))))
  rw [LocallyOfFinitePresentation.SpecMap_iff]
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

private noncomputable def inclusionBialgHom (N : R) :
    ConstantA (R := R) (G := G) →ₐc[R] ConstantFlatCoordinates R G N :=
  BialgHom.ofAlgHom
    (Algebra.algHom R (ConstantA (R := R) (G := G)) (ConstantFlatCoordinates R G N))
    (by
      apply AlgHom.ext
      intro a
      change HopfLocalizationAway.counit (constantFlatElement (G := G) N)
          (counit_element_isUnit (G := G) N)
            (algebraMap (ConstantA (R := R) (G := G))
              (ConstantFlatCoordinates R G N) a) =
        Bialgebra.counitAlgHom R (ConstantA (R := R) (G := G)) a
      exact HopfLocalizationAway.counit_algebraMap _ _ _)
    (by
      apply AlgHom.ext
      intro a
      change Algebra.TensorProduct.map
          (Algebra.algHom R (ConstantA (R := R) (G := G))
            (ConstantFlatCoordinates R G N))
          (Algebra.algHom R (ConstantA (R := R) (G := G))
            (ConstantFlatCoordinates R G N))
            (Bialgebra.comulAlgHom R (ConstantA (R := R) (G := G)) a) =
        HopfLocalizationAway.comul (constantFlatElement (G := G) N)
          (comul_element_isUnit (G := G) N)
            (algebraMap (ConstantA (R := R) (G := G))
              (ConstantFlatCoordinates R G N) a)
      exact (HopfLocalizationAway.comul_algebraMap _ _ _).symm)

/-- The affine open-subgroup morphism from the bad-level model to the constant model. -/
noncomputable def constantFlatInclusionAffine (N : R) :
    constantFlatAffine R G N ⟶ (constant R G).obj :=
  (ObjectProperty.homMk (P := cocommutativeHopfProperty R)
    (CommHopfAlgCat.ofHom (inclusionBialgHom (G := G) N))).op

@[simp]
theorem schemeMap_constantFlatInclusionAffine (N : R) :
    AffineCommGroupScheme.schemeMap (constantFlatInclusionAffine (G := G) N) =
      constantFlatInclusionSchemeMap (G := G) N := rfl

private theorem constantFlatAffine_structureMap_eq (N : R) :
    (constantFlatAffine R G N).structureMap =
      constantFlatInclusionSchemeMap (G := G) N ≫ (constant R G).obj.structureMap := by
  change Spec.map (CommRingCat.ofHom (algebraMap R (ConstantFlatCoordinates R G N))) =
    Spec.map (CommRingCat.ofHom
        (algebraMap (ConstantA (R := R) (G := G)) (ConstantFlatCoordinates R G N))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (ConstantA (R := R) (G := G))))
  rw [← Spec.map_comp, Spec.map_inj]
  ext r
  exact (IsScalarTower.algebraMap_apply R (ConstantA (R := R) (G := G))
    (ConstantFlatCoordinates R G N) r).symm

instance constantFlatAffine_flat (N : R) :
    Flat (constantFlatAffine R G N).structureMap := by
  rw [constantFlatAffine_structureMap_eq]
  infer_instance

instance constantFlatAffine_locallyQuasiFinite (N : R) :
    LocallyQuasiFinite (constantFlatAffine R G N).structureMap := by
  rw [constantFlatAffine_structureMap_eq]
  infer_instance

instance constantFlatAffine_quasiCompact (N : R) :
    QuasiCompact (constantFlatAffine R G N).structureMap := by
  rw [constantFlatAffine_structureMap_eq]
  infer_instance

instance constantFlatAffine_isSeparated (N : R) :
    IsSeparated (constantFlatAffine R G N).structureMap := by
  rw [constantFlatAffine_structureMap_eq]
  infer_instance

instance constantFlatAffine_locallyOfFinitePresentation (N : R) :
    LocallyOfFinitePresentation (constantFlatAffine R G N).structureMap := by
  rw [constantFlatAffine_structureMap_eq]
  infer_instance

/-- The bad-level flat extension of the finite constant group `G`, as a flat quasi-finite
commutative group scheme over `Spec R`. -/
noncomputable def constantFlat (R : Type u) [CommRing R]
    (G : Type u) [CommGroup G] [Fintype G] (N : R) :
    QuasiFiniteFlatCommGroupScheme (Spec (.of R)) where
  obj := (constantFlatAffine R G N).toCommGroupScheme
  property := by
    change Flat (constantFlatAffine R G N).structureMap ∧
      LocallyQuasiFinite (constantFlatAffine R G N).structureMap ∧
      QuasiCompact (constantFlatAffine R G N).structureMap ∧
      IsSeparated (constantFlatAffine R G N).structureMap ∧
      LocallyOfFinitePresentation (constantFlatAffine R G N).structureMap
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- The realized open-subgroup morphism from `constantFlat` to the finite constant group. -/
noncomputable def constantFlatInclusion (N : R) :
    (constantFlat R G N).obj ⟶ (constantScheme R G).obj :=
  (AffineCommGroupScheme.realizationFunctor R).map
    (constantFlatInclusionAffine (G := G) N)

@[simp]
theorem constantFlatInclusion_left (N : R) :
    (constantFlatInclusion (G := G) N).hom.hom.hom.left =
      constantFlatInclusionSchemeMap (G := G) N := rfl

instance constantFlatInclusion_isOpenImmersion (N : R) :
    IsOpenImmersion (constantFlatInclusion (G := G) N).hom.hom.hom.left := by
  rw [constantFlatInclusion_left]
  exact constantFlatInclusionSchemeMap_isOpenImmersion (G := G) N

/-- The affine scheme map has exactly the advertised componentwise principal-open range. -/
theorem constantFlatInclusionSchemeMap_opensRange (N : R) :
    (constantFlatInclusionSchemeMap (G := G) N).opensRange =
      PrimeSpectrum.basicOpen (constantFlatElement (G := G) N) := by
  change (Spec.map (CommRingCat.ofHom
      (algebraMap (ConstantA (R := R) (G := G))
        (ConstantFlatCoordinates R G N)))).opensRange =
    PrimeSpectrum.basicOpen (constantFlatElement (G := G) N)
  exact Scheme.Hom.opensRange_localizationAway
    (R := CommRingCat.of (ConstantA (R := R) (G := G)))
      (constantFlatElement (G := G) N)

/-- The realized open-subgroup morphism has exactly the advertised componentwise principal-open
range. -/
theorem constantFlatInclusion_opensRange (N : R) :
    ((constantFlatInclusion (G := G) N).hom.hom.hom.left).opensRange =
      PrimeSpectrum.basicOpen (constantFlatElement (G := G) N) := by
  change (constantFlatInclusionSchemeMap (G := G) N).opensRange =
    PrimeSpectrum.basicOpen (constantFlatElement (G := G) N)
  exact constantFlatInclusionSchemeMap_opensRange (G := G) N

/-- Over `D(N)`, every component of the finite constant model lies in the bad-level model.  This
is the geometric consumer of the coordinate identity `e_N * e_N' = N`. -/
theorem constantFlatInclusion_contains_levelOpen (N : R) :
    PrimeSpectrum.basicOpen (algebraMap R (ConstantCoordinates R G) N) ≤
      ((constantFlatInclusion (G := G) N).hom.hom.hom.left).opensRange := by
  change PrimeSpectrum.basicOpen (algebraMap R (ConstantCoordinates R G) N) ≤
    (constantFlatInclusionSchemeMap (G := G) N).opensRange
  rw [constantFlatInclusionSchemeMap_opensRange]
  exact basicOpen_level_le_constantFlatElement (G := G) N

/-- Mazur's elementary factor `(Z/pZ)^flat` over `Spec ℤ`.  The multiplicative type wrapper
turns the additive cyclic group `ZMod p` into the indexing commutative group used by the constant
group-scheme API. -/
noncomputable abbrev mazurConstantFlat (p : ℕ) [NeZero p] :
    QuasiFiniteFlatCommGroupScheme (Spec (.of ℤ)) :=
  constantFlat ℤ (Multiplicative (ZMod p)) (p : ℤ)

end QuasiFiniteFlatCommGroupScheme
end AlgebraicGeometry
