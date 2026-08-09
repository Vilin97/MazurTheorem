/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.AdjoinRoot
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.AdditiveFppfHOneField
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.CommGroupSchemeFppfQuotient
import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Frobenius

/-!
# The Artin--Schreier map on the additive group is fppf

Over the prime field `ZMod p`, this file constructs the additive-group endomorphism whose
Hopf-coordinate map sends the primitive generator `x` to `x ^ p - x`.  The coordinate extension
is identified with the monic universal-root algebra

`R[x][T] / (T ^ p - T - x)`.

It follows directly that the morphism is finite free, faithfully flat, and locally of finite
presentation.  The final declaration packages these proved geometric properties with the
canonical scheme-theoretic kernel; no quotient geometry is supplied as a hypothesis.
-/

noncomputable section

open CategoryTheory Opposite WithConv
open Coalgebra HopfAlgebra SymmetricAlgebra
open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry
namespace CommGroupScheme.ArtinSchreierGeometry

universe u

variable (p : ℕ) [Fact p.Prime]

abbrev CoordinateRing := SymmetricAlgebra (ZMod p) (ZMod p)

abbrev coordinateGenerator : CoordinateRing p :=
  SymmetricAlgebra.ι (ZMod p) (ZMod p) 1

/-- The algebra endomorphism `x ↦ x ^ p - x` underlying the Artin--Schreier map. -/
private noncomputable def artinSchreierAlgHom :
    CoordinateRing p →ₐ[ZMod p] CoordinateRing p :=
  SymmetricAlgebra.lift
    (LinearMap.toSpanSingleton (ZMod p) (CoordinateRing p)
      (coordinateGenerator p ^ p - coordinateGenerator p))

omit [Fact p.Prime] in
private theorem artinSchreierAlgHom_ι (r : ZMod p) :
    artinSchreierAlgHom p (SymmetricAlgebra.ι (ZMod p) (ZMod p) r) =
      r • (coordinateGenerator p ^ p - coordinateGenerator p) := by
  rw [artinSchreierAlgHom, SymmetricAlgebra.lift_ι_apply,
    LinearMap.toSpanSingleton_apply]

omit [Fact p.Prime] in
private theorem artinSchreierAlgHom_generator :
    artinSchreierAlgHom p (coordinateGenerator p) =
      coordinateGenerator p ^ p - coordinateGenerator p := by
  rw [coordinateGenerator, artinSchreierAlgHom_ι, one_smul]

/-- The Artin--Schreier substitution is a bialgebra endomorphism: the difference of the
Frobenius primitive and the standard primitive generator is again primitive. -/
noncomputable def artinSchreierCoordinateBialgHom :
    CoordinateRing p →ₐc[ZMod p] CoordinateRing p :=
  BialgHom.ofAlgHom (artinSchreierAlgHom p)
    (by
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext_ring
      simp [artinSchreierAlgHom_generator, algebraMapInv_ι,
        zero_pow (expChar_ne_zero (ZMod p) p)])
    (by
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext_ring
      simp [artinSchreierAlgHom_generator,
        TauCeti.AdditiveGroup.comul_ι_pow (ZMod p) p, comul_ι]
      rw [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
      abel)

@[simp]
theorem artinSchreierCoordinateBialgHom_generator :
    artinSchreierCoordinateBialgHom p (coordinateGenerator p) =
      coordinateGenerator p ^ p - coordinateGenerator p :=
  artinSchreierAlgHom_generator p

/-- The affine Hopf-coordinate Artin--Schreier endomorphism. -/
noncomputable def artinSchreierMapAffine :
    AffineCommGroupScheme.additive (ZMod p) ⟶
      AffineCommGroupScheme.additive (ZMod p) :=
  (ObjectProperty.homMk (P := cocommutativeHopfProperty (ZMod p))
    (CommHopfAlgCat.ofHom (artinSchreierCoordinateBialgHom p))).op

@[simp]
theorem coordinateMap_artinSchreierMapAffine :
    AffineCommGroupScheme.coordinateMap (artinSchreierMapAffine p) =
      artinSchreierCoordinateBialgHom p :=
  rfl

@[simp]
theorem coordinateMap_artinSchreierMapAffine_generator :
    AffineCommGroupScheme.coordinateMap (artinSchreierMapAffine p)
        (coordinateGenerator p) =
      coordinateGenerator p ^ p - coordinateGenerator p := by
  exact artinSchreierCoordinateBialgHom_generator p

/-- The actual Artin--Schreier additive-group endomorphism over `Spec (ZMod p)`. -/
noncomputable def artinSchreierQuotientMap :
    AffineCommGroupScheme.additiveScheme (ZMod p) ⟶
      AffineCommGroupScheme.additiveScheme (ZMod p) :=
  (AffineCommGroupScheme.realizationFunctor (ZMod p)).map
    (artinSchreierMapAffine p)

/-- The underlying scheme morphism is the spectrum map of the displayed Artin--Schreier
coordinate substitution. -/
theorem underlyingHom_artinSchreierQuotientMap_eq_schemeMap :
    CommGroupScheme.underlyingHom (artinSchreierQuotientMap p) =
      AffineCommGroupScheme.schemeMap (artinSchreierMapAffine p) :=
  AffineCommGroupScheme.realizationFunctor_map_left (artinSchreierMapAffine p)

/-- Mapping an affine point by a realized Hopf morphism is contravariant composition with its
coordinate map. -/
private theorem pointToAlgHom_map_realizationFunctor
    {R : Type u} [CommRing R] {G H : AffineCommGroupScheme R} (f : G ⟶ H)
    (B : Type u) [CommRing B] [Algebra R B] (x : G.Point B) :
    H.pointToAlgHom B
        (CommGroupScheme.mapPoint
          ((AffineCommGroupScheme.realizationFunctor R).map f)
          (AffineCommGroupScheme.testObject (R := R) B) x) =
      (G.pointToAlgHom B x).comp (AffineCommGroupScheme.coordinateMap f) := by
  apply AlgHom.ext
  intro a
  let xleft : Spec (.of B) ⟶ G.scheme := x.left
  change (Spec.preimage
      (xleft ≫ AffineCommGroupScheme.schemeMap f)).hom a = _
  rw [Spec.preimage_comp]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  rw [AffineCommGroupScheme.schemeMap, Spec.preimage_map]
  rfl

/-- On every affine test algebra, the displayed geometric morphism acts by the actual
Artin--Schreier formula `b ↦ b ^ p - b`. -/
theorem toAdd_additivePointMulEquiv_mapPoint_artinSchreierQuotientMap
    (B : Type) [CommRing B] [Algebra (ZMod p) B]
    (x : (AffineCommGroupScheme.additiveScheme (ZMod p)).Point
      (AffineCommGroupScheme.testObject (R := ZMod p) B)) :
    Multiplicative.toAdd
        (AffineCommGroupScheme.additivePointMulEquiv (ZMod p) B
          (CommGroupScheme.mapPoint (artinSchreierQuotientMap p)
            (AffineCommGroupScheme.testObject (R := ZMod p) B) x)) =
      Multiplicative.toAdd
          (AffineCommGroupScheme.additivePointMulEquiv (ZMod p) B x) ^ p -
        Multiplicative.toAdd
          (AffineCommGroupScheme.additivePointMulEquiv (ZMod p) B x) := by
  simp only [AffineCommGroupScheme.additivePointMulEquiv, MulEquiv.trans_apply,
    TauCeti.AdditiveGroup.toAdd_gaPointsMulEquiv]
  rw [AffineCommGroupScheme.pointMulEquiv_apply,
    AffineCommGroupScheme.pointMulEquiv_apply]
  change ((AffineCommGroupScheme.additive (ZMod p)).pointToAlgHom B
      (CommGroupScheme.mapPoint
        ((AffineCommGroupScheme.realizationFunctor (ZMod p)).map
          (artinSchreierMapAffine p))
        (AffineCommGroupScheme.testObject (R := ZMod p) B) x))
      (coordinateGenerator p) = _
  have h := pointToAlgHom_map_realizationFunctor
    (artinSchreierMapAffine p) B x
  rw [h]
  change (AffineCommGroupScheme.additive (ZMod p)).pointToAlgHom B x
    (AffineCommGroupScheme.coordinateMap (artinSchreierMapAffine p)
      (coordinateGenerator p)) = _
  rw [coordinateMap_artinSchreierMapAffine_generator]
  simp only [map_sub, map_pow]

/-- The monic polynomial presenting the Artin--Schreier coordinate extension. -/
private def rootPolynomial : Polynomial (CoordinateRing p) :=
  Polynomial.X ^ p -
    (Polynomial.X + Polynomial.C (coordinateGenerator p))

private theorem rootPolynomial_lower_degree_lt :
    (Polynomial.X + Polynomial.C (coordinateGenerator p)).degree <
      (p : WithBot ℕ) := by
  have hdegree :
      (Polynomial.X + Polynomial.C (coordinateGenerator p)).degree ≤
        (1 : WithBot ℕ) := by
    refine (Polynomial.degree_add_le _ _).trans (max_le ?_ ?_)
    · simp
    · exact Polynomial.degree_C_le.trans (by norm_num)
  exact hdegree.trans_lt (by
    exact_mod_cast (Fact.out : p.Prime).one_lt)

private theorem rootPolynomial_monic : (rootPolynomial p).Monic := by
  exact Polynomial.monic_X_pow_sub (rootPolynomial_lower_degree_lt p)

private abbrev RootAlgebra := AdjoinRoot (rootPolynomial p)

omit [Fact p.Prime] in
private theorem rootPolynomial_eval_generator :
    (rootPolynomial p).eval₂ (artinSchreierAlgHom p)
      (coordinateGenerator p) = 0 := by
  simp [rootPolynomial, artinSchreierAlgHom_generator]

/-- Evaluation from the universal Artin--Schreier root algebra to the target coordinate ring.
The coefficient generator acts by `x ↦ x ^ p - x`, while the adjoined root acts by `x`. -/
private noncomputable def rootForward :
    RootAlgebra p →ₐ[ZMod p] CoordinateRing p :=
  AdjoinRoot.liftAlgHom (rootPolynomial p) (artinSchreierAlgHom p)
    (coordinateGenerator p) (rootPolynomial_eval_generator p)

omit [Fact p.Prime] in
@[simp]
private theorem rootForward_root :
    rootForward p (AdjoinRoot.root (rootPolynomial p)) =
      coordinateGenerator p := by
  simp [rootForward]

omit [Fact p.Prime] in
@[simp]
private theorem rootForward_algebraMap (x : CoordinateRing p) :
    rootForward p (algebraMap (CoordinateRing p) (RootAlgebra p) x) =
      artinSchreierAlgHom p x := by
  simp [rootForward]

/-- Evaluate the target symmetric-algebra generator at the distinguished universal root. -/
private noncomputable def rootBackward :
    CoordinateRing p →ₐ[ZMod p] RootAlgebra p :=
  SymmetricAlgebra.lift
    (LinearMap.toSpanSingleton (ZMod p) (RootAlgebra p)
      (AdjoinRoot.root (rootPolynomial p)))

omit [Fact p.Prime] in
@[simp]
private theorem rootBackward_generator :
    rootBackward p (coordinateGenerator p) =
      AdjoinRoot.root (rootPolynomial p) := by
  rw [coordinateGenerator, rootBackward, SymmetricAlgebra.lift_ι_apply,
    LinearMap.toSpanSingleton_apply, one_smul]

omit [Fact p.Prime] in
private theorem root_pow_sub_root_eq_algebraMap_generator :
    AdjoinRoot.root (rootPolynomial p) ^ p -
        AdjoinRoot.root (rootPolynomial p) =
      algebraMap (CoordinateRing p) (RootAlgebra p) (coordinateGenerator p) := by
  have h := AdjoinRoot.mk_self (f := rootPolynomial p)
  rw [rootPolynomial, map_sub, map_pow, AdjoinRoot.mk_X, map_add,
    AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
  change AdjoinRoot.root (rootPolynomial p) ^ p -
      (AdjoinRoot.root (rootPolynomial p) +
        algebraMap (CoordinateRing p) (RootAlgebra p) (coordinateGenerator p)) = 0 at h
  have heq := sub_eq_zero.mp h
  rw [heq]
  ring

omit [Fact p.Prime] in
private theorem rootForward_comp_rootBackward :
    (rootForward p).comp (rootBackward p) =
      AlgHom.id (ZMod p) (CoordinateRing p) := by
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext_ring
  simp

omit [Fact p.Prime] in
private theorem rootBackward_comp_rootForward :
    (rootBackward p).comp (rootForward p) =
      AlgHom.id (ZMod p) (RootAlgebra p) := by
  apply AdjoinRoot.algHom_ext'
  · apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext_ring
    change rootBackward p
        (rootForward p
          (algebraMap (CoordinateRing p) (RootAlgebra p) (coordinateGenerator p))) =
      algebraMap (CoordinateRing p) (RootAlgebra p) (coordinateGenerator p)
    rw [rootForward_algebraMap, artinSchreierAlgHom_generator, map_sub, map_pow,
      rootBackward_generator]
    exact root_pow_sub_root_eq_algebraMap_generator p
  · simp

/-- The universal monic Artin--Schreier root algebra is the target coordinate ring. -/
private noncomputable def rootEquiv :
    RootAlgebra p ≃ₐ[ZMod p] CoordinateRing p :=
  AlgEquiv.ofAlgHom (rootForward p) (rootBackward p)
    (rootForward_comp_rootBackward p) (rootBackward_comp_rootForward p)

private theorem rootEquiv_comp_algebraMap :
    (rootEquiv p).toRingEquiv.toRingHom.comp
        (algebraMap (CoordinateRing p) (RootAlgebra p)) =
      (artinSchreierCoordinateBialgHom p).toAlgHom.toRingHom := by
  change (rootForward p).toRingHom.comp
      (algebraMap (CoordinateRing p) (RootAlgebra p)) =
    (artinSchreierAlgHom p).toRingHom
  exact AdjoinRoot.lift_comp_of (rootPolynomial_eval_generator p)

private theorem rootPolynomial_ne_one : rootPolynomial p ≠ 1 := by
  intro h
  have hp := (Fact.out : p.Prime)
  have hdegree : (rootPolynomial p).degree = (p : WithBot ℕ) := by
    have hlower :
        (Polynomial.X + Polynomial.C (coordinateGenerator p)).degree <
          (Polynomial.X ^ p : Polynomial (CoordinateRing p)).degree := by
      simpa [hp.ne_zero] using rootPolynomial_lower_degree_lt p
    rw [rootPolynomial, Polynomial.degree_sub_eq_left_of_degree_lt hlower]
    simp
  have hnatDegree : (rootPolynomial p).natDegree = p :=
    (Polynomial.degree_eq_iff_natDegree_eq_of_pos hp.pos).mp hdegree
  rw [h] at hnatDegree
  have hpzero : p = 0 := by simpa using hnatDegree.symm
  exact hp.ne_zero hpzero

private theorem rootAlgebra_nontrivial : Nontrivial (RootAlgebra p) := by
  change Nontrivial
    (Polynomial (CoordinateRing p) ⧸
      Ideal.span ({rootPolynomial p} : Set (Polynomial (CoordinateRing p))))
  apply Ideal.Quotient.nontrivial_iff.mpr
  rw [ne_eq, Ideal.span_singleton_eq_top]
  intro hunit
  exact rootPolynomial_ne_one p ((rootPolynomial_monic p).eq_one_of_isUnit hunit)

/-- The universal monic Artin--Schreier root algebra is faithfully flat over the coefficient
coordinate ring. -/
private theorem rootAlgebra_faithfullyFlat :
    (algebraMap (CoordinateRing p) (RootAlgebra p)).FaithfullyFlat := by
  letI : Module.Free (CoordinateRing p) (RootAlgebra p) :=
    (rootPolynomial_monic p).free_adjoinRoot
  letI : Nontrivial (RootAlgebra p) := rootAlgebra_nontrivial p
  exact RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance

omit [Fact p.Prime] in
/-- The universal Artin--Schreier root algebra is finitely presented. -/
private theorem rootAlgebra_finitePresentation :
    (algebraMap (CoordinateRing p) (RootAlgebra p)).FinitePresentation := by
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

/-- Artin--Schreier substitution on additive Hopf coordinates is faithfully flat. -/
theorem artinSchreierCoordinate_faithfullyFlat :
    (artinSchreierCoordinateBialgHom p).toAlgHom.toRingHom.FaithfullyFlat := by
  rw [← rootEquiv_comp_algebraMap p]
  exact RingHom.FaithfullyFlat.respectsIso.1 _ (rootEquiv p).toRingEquiv
    (rootAlgebra_faithfullyFlat p)

/-- Artin--Schreier substitution on additive Hopf coordinates is finitely presented. -/
theorem artinSchreierCoordinate_finitePresentation :
    (artinSchreierCoordinateBialgHom p).toAlgHom.toRingHom.FinitePresentation := by
  rw [← rootEquiv_comp_algebraMap p]
  exact RingHom.finitePresentation_respectsIso.1 _ (rootEquiv p).toRingEquiv
    (rootAlgebra_finitePresentation p)

/-- The Artin--Schreier endomorphism of the additive group is flat and surjective. -/
theorem artinSchreierMap_flat_and_surjective :
    Flat (CommGroupScheme.underlyingHom (artinSchreierQuotientMap p)) ∧
      Surjective
        (CommGroupScheme.underlyingHom (artinSchreierQuotientMap p)) := by
  rw [underlyingHom_artinSchreierQuotientMap_eq_schemeMap p]
  change Flat
      (Spec.map (CommRingCat.ofHom
        (artinSchreierCoordinateBialgHom p).toAlgHom.toRingHom)) ∧
    Surjective
      (Spec.map (CommRingCat.ofHom
        (artinSchreierCoordinateBialgHom p).toAlgHom.toRingHom))
  exact (flat_and_surjective_SpecMap_iff _).mpr
    (artinSchreierCoordinate_faithfullyFlat p)

/-- The Artin--Schreier endomorphism of the additive group is locally of finite presentation. -/
theorem artinSchreierMap_locallyOfFinitePresentation :
    LocallyOfFinitePresentation
      (CommGroupScheme.underlyingHom (artinSchreierQuotientMap p)) := by
  rw [underlyingHom_artinSchreierQuotientMap_eq_schemeMap p]
  change LocallyOfFinitePresentation
    (Spec.map (CommRingCat.ofHom
      (artinSchreierCoordinateBialgHom p).toAlgHom.toRingHom))
  exact (LocallyOfFinitePresentation.SpecMap_iff _).mpr
    (artinSchreierCoordinate_finitePresentation p)

/-- The no-hypothesis fppf quotient presentation of the Artin--Schreier map.  Its chosen
subgroup is the canonical scheme-theoretic kernel of the displayed additive endomorphism. -/
noncomputable def artinSchreierFppfQuotientPresentation :
    CommGroupScheme.FppfQuotientPresentation
      (CommGroupScheme.kernelInclusion (artinSchreierQuotientMap p)) where
  quotient := AffineCommGroupScheme.additiveScheme (ZMod p)
  project := artinSchreierQuotientMap p
  project_flat := (artinSchreierMap_flat_and_surjective p).1
  project_surjective := (artinSchreierMap_flat_and_surjective p).2
  project_lfp := artinSchreierMap_locallyOfFinitePresentation p
  kernelIso := Iso.refl _
  kernelIso_hom_kernelInclusion := by simp

end CommGroupScheme.ArtinSchreierGeometry
end AlgebraicGeometry
