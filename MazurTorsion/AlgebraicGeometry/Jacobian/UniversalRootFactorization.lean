/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing

/-!
# The universal root as a finite free factorization space

Let `p` be the universal monic polynomial of degree `n + 1`.  Splitting off a
monic linear factor from `p` is equivalent to adjoining a root of `p`.  This
identifies Mathlib's universal factorization algebra for degrees `1` and `n`
with `AdjoinRoot p`.  In particular, the universal factorization map is finite
free of rank `n + 1` over an arbitrary nontrivial commutative ring.

Geometrically, this is the characteristic-free affine-line model for the
pointed symmetric-power map

`A¹ × Symⁿ(A¹) ⟶ Symⁿ⁺¹(A¹)`.

The named downstream consumer is `UniversalEffectiveDivisorDescent`: it uses
this calculation as the local algebraic input for the universal effective
divisor on a smooth curve.  The design deliberately uses the universal monic
polynomial and its root algebra, rather than a general invariant-ideal base
change assertion, which would fail without extra hypotheses in wild
characteristic.
-/

noncomputable section

open Polynomial
open CategoryTheory

namespace MazurTorsion.AlgebraicGeometry.Jacobian.UniversalRootFactorization

variable (R : Type*) [CommRing R] [Nontrivial R] (n : ℕ)

/-- The coefficient ring of the universal monic polynomial of degree `n + 1`. -/
abbrev coefficientRing := MvPolynomial (Fin (n + 1)) R

/-- The ring classifying a monic linear factor and a monic complementary
factor of degree `n`. -/
abbrev factorizationRing :=
  TensorProduct R (MvPolynomial (Fin 1) R) (MvPolynomial (Fin n) R)

/-- The universal monic polynomial of degree `n + 1`. -/
noncomputable abbrev universalPolynomial : (coefficientRing R n)[X] :=
  Polynomial.freeMonic R (n + 1)

/-- The algebra obtained by adjoining a root of the universal polynomial. -/
abbrev universalRootAlgebra := AdjoinRoot (universalPolynomial R n)

noncomputable instance universalRootAlgebra_nontrivial :
    Nontrivial (universalRootAlgebra R n) := by
  rw [universalRootAlgebra, AdjoinRoot, Ideal.Quotient.nontrivial_iff,
    ne_eq, Ideal.span_singleton_eq_top]
  intro h
  have heq := (Polynomial.monic_freeMonic R (n + 1)).eq_one_of_isUnit h
  have hdeg := congrArg Polynomial.natDegree heq
  simp [Polynomial.natDegree_freeMonic] at hdeg

/-- The universal map sending the coefficients of a monic polynomial to the
coefficients of a monic linear factor and its degree-`n` complement. -/
noncomputable def coefficientToFactors :
    coefficientRing R n →ₐ[R] factorizationRing R n :=
  MvPolynomial.universalFactorizationMap R (n + 1) 1 n (by omega)

noncomputable def mappedPolynomial :
    Polynomial.MonicDegreeEq (universalRootAlgebra R n) (n + 1) :=
  (Polynomial.MonicDegreeEq.freeMonic R (n + 1)).map
    (AdjoinRoot.ofAlgHom R (universalPolynomial R n))

noncomputable def linearFactor :
    Polynomial.MonicDegreeEq (universalRootAlgebra R n) 1 :=
  MvPolynomial.mapEquivMonic R (universalRootAlgebra R n) 1
    (MvPolynomial.aeval fun _ ↦ -AdjoinRoot.root (universalPolynomial R n))

omit [Nontrivial R] in
theorem linearFactor_coe :
    (linearFactor R n).1 =
      Polynomial.X - Polynomial.C
        (AdjoinRoot.root (universalPolynomial R n)) := by
  simp [linearFactor, MvPolynomial.mapEquivMonic, Polynomial.freeMonic,
    sub_eq_add_neg]

omit [Nontrivial R] in
theorem mappedPolynomial_isRoot :
    (mappedPolynomial R n).1.IsRoot
      (AdjoinRoot.root (universalPolynomial R n)) := by
  simp [mappedPolynomial, Polynomial.IsRoot, Polynomial.eval_map,
    AdjoinRoot.eval₂_root]

theorem exists_complementaryFactor :
    ∃ q : Polynomial.MonicDegreeEq (universalRootAlgebra R n) n,
      q.1 = (mappedPolynomial R n).1 /ₘ (linearFactor R n).1 := by
  let q := (mappedPolynomial R n).1 /ₘ (linearFactor R n).1
  have hmul : (linearFactor R n).1 * q = (mappedPolynomial R n).1 := by
    dsimp only [q]
    simpa only [linearFactor_coe] using
      Polynomial.mul_divByMonic_eq_iff_isRoot.mpr
        (mappedPolynomial_isRoot R n)
  have hmonic : q.Monic :=
    (linearFactor R n).monic.of_mul_monic_left
      (hmul.symm ▸ (mappedPolynomial R n).monic)
  have hdeg : q.natDegree = n := by
    rw [Polynomial.natDegree_divByMonic _ (linearFactor R n).monic,
      (mappedPolynomial R n).natDegree, (linearFactor R n).natDegree]
    omega
  exact ⟨Polynomial.MonicDegreeEq.mk q hmonic hdeg, rfl⟩

noncomputable def complementaryFactor :
    Polynomial.MonicDegreeEq (universalRootAlgebra R n) n :=
  Classical.choose (exists_complementaryFactor R n)

theorem complementaryFactor_coe :
    (complementaryFactor R n).1 =
      (mappedPolynomial R n).1 /ₘ (linearFactor R n).1 :=
  Classical.choose_spec (exists_complementaryFactor R n)

theorem linear_mul_complementary :
    (linearFactor R n).1 * (complementaryFactor R n).1 =
      (mappedPolynomial R n).1 := by
  rw [complementaryFactor_coe, linearFactor_coe]
  exact Polynomial.mul_divByMonic_eq_iff_isRoot.mpr
    (mappedPolynomial_isRoot R n)

/-- The factorization algebra maps to the universal root algebra by sending
the linear factor to `X - root`. -/
noncomputable def factorsToRootR :
    factorizationRing R n →ₐ[R] universalRootAlgebra R n :=
  Algebra.TensorProduct.lift
    ((MvPolynomial.mapEquivMonic R (universalRootAlgebra R n) 1).symm
      (linearFactor R n))
    ((MvPolynomial.mapEquivMonic R (universalRootAlgebra R n) n).symm
      (complementaryFactor R n))
    (fun _ _ ↦ .all _ _)

theorem factorsToRootR_comp_coefficientToFactors :
    (factorsToRootR R n).comp (coefficientToFactors R n) =
      AdjoinRoot.ofAlgHom R (universalPolynomial R n) := by
  rw [show (factorsToRootR R n).comp (coefficientToFactors R n) =
      (MvPolynomial.mapEquivMonic R (universalRootAlgebra R n) (n + 1)).symm
        (mappedPolynomial R n) from
    ((MvPolynomial.universalFactorizationMapLiftEquiv R
      (universalRootAlgebra R n) (n + 1) 1 n (by omega)
      (mappedPolynomial R n)).symm
        ⟨(linearFactor R n, complementaryFactor R n),
          linear_mul_complementary R n⟩).2]
  change (MvPolynomial.mapEquivMonic R (universalRootAlgebra R n) (n + 1)).symm
      ((Polynomial.MonicDegreeEq.freeMonic R (n + 1)).map
        (AdjoinRoot.ofAlgHom R (universalPolynomial R n))) = _
  have hmap :
      (MvPolynomial.mapEquivMonic R (universalRootAlgebra R n) (n + 1)).symm
          ((Polynomial.MonicDegreeEq.freeMonic R (n + 1)).map
            (AdjoinRoot.ofAlgHom R (universalPolynomial R n))) =
        (AdjoinRoot.ofAlgHom R (universalPolynomial R n)).comp
          ((MvPolynomial.mapEquivMonic R (coefficientRing R n) (n + 1)).symm
            (Polynomial.MonicDegreeEq.freeMonic R (n + 1))) := by
    simpa only [universalRootAlgebra] using
      MvPolynomial.mapEquivMonic_symm_map (n := n + 1)
        (Polynomial.MonicDegreeEq.freeMonic R (n + 1))
        (AdjoinRoot.ofAlgHom R (universalPolynomial R n))
  rw [hmap]
  have hfree :
      (MvPolynomial.mapEquivMonic R (coefficientRing R n) (n + 1)).symm
          (Polynomial.MonicDegreeEq.freeMonic R (n + 1)) =
        AlgHom.id R (coefficientRing R n) := by
    apply MvPolynomial.algHom_ext
    intro i
    have hi : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
    simp [MvPolynomial.mapEquivMonic, Polynomial.coeff_freeMonic, hi]
  rw [hfree, AlgHom.comp_id]

/-- The distinguished root in the factorization algebra is the negative of
the coefficient of the monic linear factor. -/
noncomputable def factorRoot : factorizationRing R n :=
  -Algebra.TensorProduct.includeLeft (R := R) (S := R)
    (MvPolynomial.X (0 : Fin 1))

omit [Nontrivial R] in
theorem factorRoot_isRoot :
    Polynomial.eval₂ (coefficientToFactors R n) (factorRoot R n)
      (universalPolynomial R n) = 0 := by
  rw [← Polynomial.eval_map]
  change Polynomial.eval (factorRoot R n)
    ((Polynomial.freeMonic R (n + 1)).map
      (MvPolynomial.universalFactorizationMap R (n + 1) 1 n (by omega))) = 0
  rw [MvPolynomial.universalFactorizationMap_freeMonic]
  simp [factorRoot, Polynomial.freeMonic]

/-- Evaluation at the distinguished root maps the universal root algebra to
the factorization algebra. -/
noncomputable def rootToFactorsR :
    universalRootAlgebra R n →ₐ[R] factorizationRing R n :=
  AdjoinRoot.liftAlgHom (universalPolynomial R n) (coefficientToFactors R n)
    (factorRoot R n) (factorRoot_isRoot R n)

omit [Nontrivial R] in
@[simp]
theorem rootToFactorsR_root :
    rootToFactorsR R n (AdjoinRoot.root (universalPolynomial R n)) =
      factorRoot R n := by
  simp [rootToFactorsR]

theorem factorsToRootR_includeLeft_X_zero :
    factorsToRootR R n
        (Algebra.TensorProduct.includeLeft (R := R) (S := R)
          (MvPolynomial.X (0 : Fin 1))) =
      -AdjoinRoot.root (universalPolynomial R n) := by
  simp [factorsToRootR, linearFactor]

theorem factorsToRootR_factorRoot :
    factorsToRootR R n (factorRoot R n) =
      AdjoinRoot.root (universalPolynomial R n) := by
  rw [factorRoot, map_neg, factorsToRootR_includeLeft_X_zero, neg_neg]

omit [Nontrivial R] in
theorem rootToFactorsR_comp_of :
    (rootToFactorsR R n).comp
        (AdjoinRoot.ofAlgHom R (universalPolynomial R n)) =
      coefficientToFactors R n := by
  ext x
  simp [rootToFactorsR]

theorem factorsToRootR_comp_rootToFactorsR :
    (factorsToRootR R n).comp (rootToFactorsR R n) =
      AlgHom.id R (universalRootAlgebra R n) := by
  apply AdjoinRoot.algHom_ext' (S := R)
  · rw [AlgHom.comp_assoc, rootToFactorsR_comp_of,
      factorsToRootR_comp_coefficientToFactors]
    rfl
  · rw [AlgHom.comp_apply, rootToFactorsR_root,
      factorsToRootR_factorRoot, AlgHom.id_apply]

theorem rootToFactorsR_comp_factorsToRootR_coefficients :
    ((rootToFactorsR R n).comp (factorsToRootR R n)).comp
        (coefficientToFactors R n) = coefficientToFactors R n := by
  rw [AlgHom.comp_assoc, factorsToRootR_comp_coefficientToFactors,
    rootToFactorsR_comp_of]

theorem rootToFactorsR_comp_factorsToRootR_includeLeft :
    ((rootToFactorsR R n).comp (factorsToRootR R n)).comp
        (Algebra.TensorProduct.includeLeft (R := R) (S := R)) =
      Algebra.TensorProduct.includeLeft := by
  apply MvPolynomial.algHom_ext
  intro i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  simp only [AlgHom.comp_apply]
  rw [factorsToRootR_includeLeft_X_zero, map_neg,
    rootToFactorsR_root, factorRoot, neg_neg]

theorem rootToFactorsR_comp_factorsToRootR_includeRight :
    ((rootToFactorsR R n).comp (factorsToRootR R n)).comp
        Algebra.TensorProduct.includeRight =
      Algebra.TensorProduct.includeRight := by
  let h := (rootToFactorsR R n).comp (factorsToRootR R n)
  let l : MvPolynomial (Fin 1) R →ₐ[R] factorizationRing R n :=
    Algebra.TensorProduct.includeLeft
  let r : MvPolynomial (Fin n) R →ₐ[R] factorizationRing R n :=
    Algebra.TensorProduct.includeRight
  let first : (factorizationRing R n)[X] :=
    (Polynomial.freeMonic R 1).map l
  let second : (factorizationRing R n)[X] :=
    (Polynomial.freeMonic R n).map r
  have hcoeff : h.comp (coefficientToFactors R n) =
      coefficientToFactors R n :=
    rootToFactorsR_comp_factorsToRootR_coefficients R n
  have hleft : h.comp l = l := by
    exact rootToFactorsR_comp_factorsToRootR_includeLeft R n
  have hfactor :
      (Polynomial.freeMonic R (n + 1)).map
          (coefficientToFactors R n).toRingHom = first * second := by
    exact MvPolynomial.universalFactorizationMap_freeMonic
      R (n + 1) 1 n (by omega)
  have hfirst : first.map h = first := by
    dsimp only [first]
    rw [Polynomial.map_map]
    have hleftRing : h.toRingHom.comp l.toRingHom = l.toRingHom :=
      congrArg (fun f : MvPolynomial (Fin 1) R →ₐ[R]
        factorizationRing R n ↦ f.toRingHom) hleft
    change (Polynomial.freeMonic R 1).map
        (h.toRingHom.comp l.toRingHom) =
      (Polynomial.freeMonic R 1).map l.toRingHom
    rw [hleftRing]
  have hsource :
      ((Polynomial.freeMonic R (n + 1)).map
        (coefficientToFactors R n).toRingHom).map h =
          (Polynomial.freeMonic R (n + 1)).map
            (coefficientToFactors R n).toRingHom := by
    rw [Polynomial.map_map]
    have hcoeffRing :
        h.toRingHom.comp (coefficientToFactors R n).toRingHom =
          (coefficientToFactors R n).toRingHom :=
      congrArg (fun f : coefficientRing R n →ₐ[R]
        factorizationRing R n ↦ f.toRingHom) hcoeff
    change (Polynomial.freeMonic R (n + 1)).map
        (h.toRingHom.comp (coefficientToFactors R n).toRingHom) =
      (Polynomial.freeMonic R (n + 1)).map
        (coefficientToFactors R n).toRingHom
    rw [hcoeffRing]
  have hprod : first * second.map h = first * second := by
    calc
      first * second.map h = (first * second).map h := by
        rw [Polynomial.map_mul, hfirst]
      _ = ((Polynomial.freeMonic R (n + 1)).map
          (coefficientToFactors R n).toRingHom).map h := by rw [hfactor]
      _ = (Polynomial.freeMonic R (n + 1)).map
          (coefficientToFactors R n).toRingHom := hsource
      _ = first * second := hfactor
  have hfirstMonic : first.Monic := by
    exact (Polynomial.monic_freeMonic R 1).map l.toRingHom
  have hsecond : second.map h = second := by
    exact hfirstMonic.isRegular.left hprod
  apply MvPolynomial.algHom_ext
  intro i
  have hi := congrArg (fun q : (factorizationRing R n)[X] ↦ q.coeff i) hsecond
  simpa [h, r, second, Polynomial.coeff_map, Polynomial.coeff_freeMonic,
    i.isLt] using hi

theorem rootToFactorsR_comp_factorsToRootR :
    (rootToFactorsR R n).comp (factorsToRootR R n) =
      AlgHom.id R (factorizationRing R n) := by
  apply Algebra.TensorProduct.ext
  · change ((rootToFactorsR R n).comp (factorsToRootR R n)).comp
        (Algebra.TensorProduct.includeLeft (R := R) (S := R)) =
      (AlgHom.id R (factorizationRing R n)).comp
        Algebra.TensorProduct.includeLeft
    simpa using rootToFactorsR_comp_factorsToRootR_includeLeft R n
  · change ((rootToFactorsR R n).comp (factorsToRootR R n)).comp
        Algebra.TensorProduct.includeRight =
      (AlgHom.id R (factorizationRing R n)).comp
        Algebra.TensorProduct.includeRight
    simpa using rootToFactorsR_comp_factorsToRootR_includeRight R n

noncomputable def factorsToRoot :
    letI := (coefficientToFactors R n).toAlgebra
    factorizationRing R n →ₐ[coefficientRing R n]
      universalRootAlgebra R n := by
  letI := (coefficientToFactors R n).toAlgebra
  exact
    { (factorsToRootR R n).toRingHom with
      commutes' := fun b ↦ DFunLike.congr_fun
        (factorsToRootR_comp_coefficientToFactors R n) b }

noncomputable def rootToFactors :
    letI := (coefficientToFactors R n).toAlgebra
    universalRootAlgebra R n →ₐ[coefficientRing R n]
      factorizationRing R n := by
  letI := (coefficientToFactors R n).toAlgebra
  exact
    { (rootToFactorsR R n).toRingHom with
      commutes' := fun b ↦ DFunLike.congr_fun
        (rootToFactorsR_comp_of R n) b }

/-- Splitting the universal monic polynomial into degrees `1` and `n` is
equivalent, over its coefficient ring, to adjoining one root. -/
noncomputable def factorsEquivRoot :
    letI := (coefficientToFactors R n).toAlgebra
    factorizationRing R n ≃ₐ[coefficientRing R n]
      universalRootAlgebra R n := by
  letI := (coefficientToFactors R n).toAlgebra
  exact
    { factorsToRoot R n with
      invFun := rootToFactors R n
      left_inv := fun x ↦ DFunLike.congr_fun
        (rootToFactorsR_comp_factorsToRootR R n) x
      right_inv := fun x ↦ DFunLike.congr_fun
        (factorsToRootR_comp_rootToFactorsR R n) x }

noncomputable instance factorizationRing_free :
    letI := (coefficientToFactors R n).toAlgebra
    Module.Free (coefficientRing R n) (factorizationRing R n) := by
  letI := (coefficientToFactors R n).toAlgebra
  letI : Module.Free (coefficientRing R n) (universalRootAlgebra R n) :=
    (Polynomial.monic_freeMonic R (n + 1)).free_adjoinRoot
  exact Module.Free.of_equiv (factorsEquivRoot R n).symm.toLinearEquiv

noncomputable instance factorizationRing_flat :
    letI := (coefficientToFactors R n).toAlgebra
    Module.Flat (coefficientRing R n) (factorizationRing R n) := by
  letI := (coefficientToFactors R n).toAlgebra
  infer_instance

/-- The universal root algebra, hence the universal linear-factor algebra, has
constant rank `n + 1` over the universal coefficient ring. -/
theorem factorizationRing_finrank :
    letI := (coefficientToFactors R n).toAlgebra
    Module.finrank (coefficientRing R n) (factorizationRing R n) = n + 1 := by
  letI := (coefficientToFactors R n).toAlgebra
  rw [(factorsEquivRoot R n).toLinearEquiv.finrank_eq]
  simpa [universalRootAlgebra, coefficientRing,
    Polynomial.natDegree_freeMonic] using
      (AdjoinRoot.powerBasis'
        (Polynomial.monic_freeMonic R (n + 1))).finrank

/-- The coordinate ring of the ambient affine line over the universal
coefficient space. -/
abbrev universalRootAmbientRing := Polynomial (coefficientRing R n)

/-- The universal root locus as a quotient of its ambient polynomial ring. -/
noncomputable def ambientToFactors :
    universalRootAmbientRing R n →+* factorizationRing R n := by
  letI := (coefficientToFactors R n).toAlgebra
  exact (rootToFactors R n).toRingHom.comp
    (AdjoinRoot.mk (universalPolynomial R n))

/-- The coordinate map cutting out the universal root locus is surjective. -/
theorem ambientToFactors_surjective :
    Function.Surjective (ambientToFactors R n) := by
  letI := (coefficientToFactors R n).toAlgebra
  exact (factorsEquivRoot R n).symm.surjective.comp
    AdjoinRoot.mk_surjective

/-- The universal root locus is cut out by the universal monic polynomial. -/
theorem ambientToFactors_ker :
    RingHom.ker (ambientToFactors R n) =
      Ideal.span {universalPolynomial R n} := by
  letI := (coefficientToFactors R n).toAlgebra
  unfold ambientToFactors
  rw [RingHom.ker_comp_of_injective]
  · exact Ideal.mk_ker
  · exact (factorsEquivRoot R n).symm.injective

omit [Nontrivial R] in
theorem ambientToFactors_comp_C :
    (ambientToFactors R n).comp
        (Polynomial.C : coefficientRing R n →+* universalRootAmbientRing R n) =
      (coefficientToFactors R n).toRingHom := by
  letI := (coefficientToFactors R n).toAlgebra
  apply DFunLike.ext _ _
  intro b
  change rootToFactors R n
      (AdjoinRoot.mk (universalPolynomial R n) (Polynomial.C b)) = _
  rw [AdjoinRoot.mk_C]
  exact DFunLike.congr_fun (rootToFactorsR_comp_of R n) b

omit [Nontrivial R] in
/-- The equation of the universal root locus is a non-zero-divisor over any
commutative base ring. -/
theorem universalPolynomial_isRegular :
    IsRegular (universalPolynomial R n) :=
  (Polynomial.monic_freeMonic R (n + 1)).isRegular

omit [Nontrivial R] in
/-- The universal factorization map is finite. -/
theorem coefficientToFactors_finite :
    (coefficientToFactors R n).toRingHom.Finite := by
  exact MvPolynomial.finite_universalFactorizationMap
    R (n + 1) 1 n (by omega)

/-- The universal factorization map is flat over every nontrivial base ring. -/
theorem coefficientToFactors_flat :
    (coefficientToFactors R n).toRingHom.Flat := by
  change letI := (coefficientToFactors R n).toAlgebra
    Module.Flat (coefficientRing R n) (factorizationRing R n)
  exact factorizationRing_flat R n

open _root_.AlgebraicGeometry

/-- The affine universal-root morphism.  On points it records a monic
polynomial together with one of its roots, or equivalently a factorization
into monic factors of degrees `1` and `n`. -/
noncomputable def universalRootProjection :
    Spec (.of (factorizationRing R n)) ⟶
      Spec (.of (coefficientRing R n)) :=
  Spec.map (CommRingCat.ofHom (coefficientToFactors R n).toRingHom)

/-- The universal root locus embedded in the affine line over the universal
coefficient space. -/
noncomputable def universalRootLocusι :
    Spec (.of (factorizationRing R n)) ⟶
      Spec (.of (universalRootAmbientRing R n)) :=
  Spec.map (CommRingCat.ofHom (ambientToFactors R n))

/-- Projection from the ambient affine line to the universal coefficient
space. -/
noncomputable def universalRootAmbientProjection :
    Spec (.of (universalRootAmbientRing R n)) ⟶
      Spec (.of (coefficientRing R n)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.C :
    coefficientRing R n →+* universalRootAmbientRing R n))

omit [Nontrivial R] in
/-- The structure morphism of the universal root locus factors through its
ambient affine line. -/
theorem universalRootLocusι_comp_ambientProjection :
    universalRootLocusι R n ≫ universalRootAmbientProjection R n =
      universalRootProjection R n := by
  rw [universalRootLocusι, universalRootAmbientProjection,
    universalRootProjection, ← Spec.map_comp]
  congr 1
  change CommRingCat.ofHom ((ambientToFactors R n).comp
      (Polynomial.C : coefficientRing R n →+* universalRootAmbientRing R n)) =
    CommRingCat.ofHom (coefficientToFactors R n).toRingHom
  exact congrArg CommRingCat.ofHom (ambientToFactors_comp_C R n)

instance universalRootLocusι_isClosedImmersion :
    IsClosedImmersion (universalRootLocusι R n) := by
  apply IsClosedImmersion.spec_of_surjective
  exact ambientToFactors_surjective R n

instance universalRootProjection_isFinite :
    IsFinite (universalRootProjection R n) := by
  change IsFinite (Spec.map
    (CommRingCat.ofHom (coefficientToFactors R n).toRingHom))
  rw [IsFinite.SpecMap_iff]
  exact coefficientToFactors_finite R n

instance universalRootProjection_flat :
    Flat (universalRootProjection R n) := by
  change Flat (Spec.map
    (CommRingCat.ofHom (coefficientToFactors R n).toRingHom))
  rw [Flat.SpecMap_iff]
  exact coefficientToFactors_flat R n

/-- The affine universal-root morphism has constant rank `n + 1`. -/
theorem universalRootProjection_finrank :
    (universalRootProjection R n).finrank = fun _ ↦ n + 1 := by
  change (Spec.map
    (CommRingCat.ofHom (coefficientToFactors R n).toRingHom)).finrank = _
  rw [Scheme.Hom.finrank_SpecMap_eq_finrank]
  · ext x
    change (letI := (coefficientToFactors R n).toAlgebra
      Module.rankAtStalk (factorizationRing R n) x) = n + 1
    letI := (coefficientToFactors R n).toAlgebra
    rw [Module.rankAtStalk_eq_finrank_of_free]
    exact factorizationRing_finrank R n
  · exact coefficientToFactors_finite R n
  · exact coefficientToFactors_flat R n

end MazurTorsion.AlgebraicGeometry.Jacobian.UniversalRootFactorization
