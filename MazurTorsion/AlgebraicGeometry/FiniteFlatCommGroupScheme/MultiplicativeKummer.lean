/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.RingTheory.AdjoinRoot
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.AdmissibleCohomology
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.CommGroupSchemeFppfConnecting
import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Basic

/-!
# The geometric Kummer boundary for the multiplicative group

This file gives the actual fppf Kummer boundary used by the finite-flat rank-zero lane.
It realizes `G_m = D(Z)` as an affine commutative group scheme, identifies its affine points
with units, and constructs multiplication by `n` on every ambient commutative group scheme.

The construction uses the finite free algebra obtained by adjoining an `n`th root of a unit to
give genuine fppf-local lifts through the power map.  Thus the resulting connecting map is the
checked Čech boundary into the scheme-theoretic kernel, rather than an abstractly supplied map.
-/

noncomputable section

open CategoryTheory Opposite WithConv
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open scoped CategoryTheory.MonObj
open scoped LaurentPolynomial

namespace AlgebraicGeometry

universe u

namespace AffineCommGroupScheme

variable {R : Type u} [CommRing R]

/-- The affine multiplicative group with Laurent-polynomial Hopf coordinates. -/
abbrev multiplicative (R : Type u) [CommRing R] : AffineCommGroupScheme R :=
  Opposite.op
    ⟨CommHopfAlgCat.of R R[T;T⁻¹], by
      change Coalgebra.IsCocomm R R[T;T⁻¹]
      infer_instance⟩

/-- The multiplicative group as an actual commutative group object over `Spec R`. -/
abbrev multiplicativeScheme (R : Type u) [CommRing R] :
    CommGroupScheme (Spec (.of R)) :=
  (multiplicative R).toCommGroupScheme

/-- Affine points of the geometric multiplicative group are the units of the value algebra. -/
def multiplicativePointMulEquiv (R : Type u) [CommRing R]
    (B : Type u) [CommRing B] [Algebra R B] :
    (multiplicativeScheme R).Point (testObject (R := R) B) ≃* Bˣ :=
  ((multiplicative R).pointMulEquiv B).trans
    (TauCeti.MultiplicativeGroup.pointsMulEquiv (R := R) (A := B))

/-- The named identity object used for global sections is canonically the affine self-test
object. -/
noncomputable def baseObjectIsoSelfTestObject (R : Type u) [CommRing R] :
    CommGroupScheme.baseObject (Spec (.of R)) ≅ testObject (R := R) R :=
  baseIsoSelfTestObject R

/-- Global points of an affine commutative group scheme may be read on the affine self-test
object. -/
def basePointMulEquiv (G : AffineCommGroupScheme R) :
    CommGroupScheme.BasePoint G.toCommGroupScheme ≃* G.Point R where
  __ := CommGroupScheme.pointMulEquivOfOverIso G.toCommGroupScheme
    (baseObjectIsoSelfTestObject R)

/-- Global geometric points of `G_m` over `Spec R` are the units of `R`. -/
def multiplicativeBasePointMulEquiv (R : Type u) [CommRing R] :
    CommGroupScheme.BasePoint (multiplicativeScheme R) ≃* Rˣ :=
  (basePointMulEquiv (multiplicative R)).trans (multiplicativePointMulEquiv R R)

/-- The unit read from a geometric multiplicative-group point is natural in the affine test
algebra. -/
theorem multiplicativePointMulEquiv_testObjectMap
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (x : (multiplicative R).Point A) :
    multiplicativePointMulEquiv R B (testObjectMap f ≫ x) =
      Units.map f.toMonoidHom (multiplicativePointMulEquiv R A x) := by
  apply Units.ext
  change (TauCeti.MultiplicativeGroup.unitOfPoint
        (((multiplicative R).pointMulEquiv B (testObjectMap f ≫ x)).ofConv) : B) =
    f (TauCeti.MultiplicativeGroup.unitOfPoint
      (((multiplicative R).pointMulEquiv A x).ofConv) : A)
  rw [TauCeti.MultiplicativeGroup.unitOfPoint_val,
    TauCeti.MultiplicativeGroup.unitOfPoint_val, pointMulEquiv_apply,
    pointMulEquiv_apply]
  change (multiplicative R).pointToAlgHom B (testObjectMap f ≫ x)
      (LaurentPolynomial.T 1) =
    f ((multiplicative R).pointToAlgHom A x (LaurentPolynomial.T 1))
  rw [pointToAlgHom_testObjectMap]
  rfl

end AffineCommGroupScheme

namespace CommGroupScheme

variable {S : Scheme.{u}}

/-- Multiplication by `n` on an arbitrary commutative group scheme, in multiplicative
notation. -/
def powerEnd (G : CommGroupScheme S) (n : ℕ) : G ⟶ G :=
  InducedCategory.homMk ((𝟙 G.toGrp) ^ n)

@[simp]
theorem mapPoint_powerEnd (G : CommGroupScheme S) (n : ℕ)
    (T : Over S) (x : G.Point T) :
    mapPoint (powerEnd G n) T x = x ^ n := by
  change x ≫ (((𝟙 G.toGrp) ^ n).hom.hom) = x ^ n
  rw [Grp.Hom.hom_pow, Mon.Hom.hom_pow, MonObj.comp_pow]
  simp

/-- The canonical group-scheme kernel is itself a kernel presentation. -/
noncomputable def canonicalKernelPresentation {G H : CommGroupScheme S} (f : G ⟶ H) :
    KernelPresentation f where
  kernel := kernel f
  inclusion := kernelInclusion f
  kernelIso := Iso.refl _
  kernelIso_hom_kernelInclusion := by simp

end CommGroupScheme

namespace CommGroupScheme.MultiplicativeKummer

variable (R : Type u) [CommRing R]

/-- The polynomial used to adjoin an `n`th root of a unit. -/
def rootPolynomial (u : Rˣ) (n : ℕ) : Polynomial R :=
  Polynomial.X ^ n - Polynomial.C (u : R)

/-- The finite root algebra `R[X]/(X^n-u)`. -/
abbrev RootAlgebra (u : Rˣ) (n : ℕ) :=
  AdjoinRoot (rootPolynomial R u n)

theorem rootPolynomial_monic (u : Rˣ) (n : ℕ) (hn : n ≠ 0) :
    (rootPolynomial R u n).Monic :=
  Polynomial.monic_X_pow_sub_C (u : R) hn

/-- A positive-degree root algebra over a nontrivial base is nontrivial. -/
theorem rootAlgebra_nontrivial [Nontrivial R] (u : Rˣ) (n : ℕ) (hn : n ≠ 0) :
    Nontrivial (RootAlgebra R u n) := by
  change Nontrivial
    (Polynomial R ⧸ Ideal.span ({rootPolynomial R u n} : Set (Polynomial R)))
  apply Ideal.Quotient.nontrivial_iff.mpr
  rw [ne_eq, Ideal.span_singleton_eq_top]
  intro hunit
  have hone := (rootPolynomial_monic R u n hn).eq_one_of_isUnit hunit
  have hdegree : (rootPolynomial R u n).natDegree = n := by
    simp [rootPolynomial]
  apply hn
  rw [← hdegree, hone]
  simp

/-- The root algebra is finite free, hence faithfully flat, over a nontrivial base. -/
theorem rootAlgebra_faithfullyFlat [Nontrivial R]
    (u : Rˣ) (n : ℕ) (hn : n ≠ 0) :
    (algebraMap R (RootAlgebra R u n)).FaithfullyFlat := by
  letI : Module.Free R (RootAlgebra R u n) :=
    (rootPolynomial_monic R u n hn).free_adjoinRoot
  letI : Nontrivial (RootAlgebra R u n) := rootAlgebra_nontrivial R u n hn
  exact RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance

/-- The root algebra is finitely presented over the base. -/
theorem rootAlgebra_finitePresentation
    (u : Rˣ) (n : ℕ) :
    (algebraMap R (RootAlgebra R u n)).FinitePresentation := by
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

/-- The distinguished root in the root algebra has `n`th power equal to the original unit. -/
theorem root_pow_eq (u : Rˣ) (n : ℕ) :
    (AdjoinRoot.root (rootPolynomial R u n)) ^ n =
      algebraMap R (RootAlgebra R u n) (u : R) := by
  have h := AdjoinRoot.mk_self (f := rootPolynomial R u n)
  rw [rootPolynomial, map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
  exact sub_eq_zero.mp h

/-- For positive `n`, the distinguished root is a unit. -/
theorem root_isUnit (u : Rˣ) (n : ℕ) (hn : n ≠ 0) :
    IsUnit (AdjoinRoot.root (rootPolynomial R u n)) := by
  rw [← isUnit_pow_iff hn, root_pow_eq]
  exact (Units.map (algebraMap R (RootAlgebra R u n)).toMonoidHom u).isUnit

/-- The distinguished root packaged as a unit of the root algebra. -/
noncomputable def rootUnit (u : Rˣ) (n : ℕ) (hn : n ≠ 0) :
    (RootAlgebra R u n)ˣ :=
  (root_isUnit R u n hn).unit

@[simp]
theorem rootUnit_val (u : Rˣ) (n : ℕ) (hn : n ≠ 0) :
    (rootUnit R u n hn : RootAlgebra R u n) =
      AdjoinRoot.root (rootPolynomial R u n) :=
  IsUnit.unit_spec (root_isUnit R u n hn)

/-- The packaged root maps to the original unit after taking its `n`th power. -/
theorem rootUnit_pow (u : Rˣ) (n : ℕ) (hn : n ≠ 0) :
    rootUnit R u n hn ^ n =
      Units.map (algebraMap R (RootAlgebra R u n)).toMonoidHom u := by
  ext
  simp [root_pow_eq]

/-- The affine morphism from the root algebra to the base. -/
abbrev rootSpecMap (u : Rˣ) (n : ℕ) :
    Spec (.of (RootAlgebra R u n)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (RootAlgebra R u n)))

/-- The singleton root-algebra map belongs to the fppf precoverage. -/
theorem rootSpecMap_mem_fppfPrecoverage [Nontrivial R]
    (u : Rˣ) (n : ℕ) (hn : n ≠ 0) :
    Presieve.singleton (rootSpecMap R u n) ∈
      Scheme.fppfPrecoverage (Spec (.of R)) := by
  have hflatSurjective : Flat (rootSpecMap R u n) ∧ Surjective (rootSpecMap R u n) :=
    (flat_and_surjective_SpecMap_iff _).mpr
      (rootAlgebra_faithfullyFlat R u n hn)
  letI : Flat (rootSpecMap R u n) := hflatSurjective.1
  letI : Surjective (rootSpecMap R u n) := hflatSurjective.2
  have hlfp : LocallyOfFinitePresentation (rootSpecMap R u n) :=
    (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (rootAlgebra_finitePresentation R u n)
  letI : LocallyOfFinitePresentation (rootSpecMap R u n) := hlfp
  exact Scheme.Hom.singleton_mem_fppfPrecoverage (rootSpecMap R u n)

/-- Adjoining an `n`th root of a unit gives a singleton fppf cover when `n` is positive. -/
noncomputable abbrev rootCover [Nontrivial R] (u : Rˣ) (n : ℕ) (hn : n ≠ 0) :
    Scheme.Cover.{u} Scheme.fppfPrecoverage (Spec (.of R)) :=
  Precoverage.ZeroHypercover.singleton (rootSpecMap R u n)
    (rootSpecMap_mem_fppfPrecoverage R u n hn)

/-- Every member of the singleton root cover is canonically the affine root-algebra test
object. -/
noncomputable def rootCoverObjectIso [Nontrivial R]
    (u : Rˣ) (n : ℕ) (hn : n ≠ 0) (i : (rootCover R u n hn).I₀) :
    (rootCover R u n hn).overFamily i ≅
      AffineCommGroupScheme.testObject (R := R) (RootAlgebra R u n) :=
  Over.isoMk (Iso.refl _) (by rfl)

/-- Points of `G_m` on a root-cover member are canonically units of the root algebra. -/
noncomputable def rootCoverPointMulEquiv [Nontrivial R]
    (u : Rˣ) (n : ℕ) (hn : n ≠ 0) (i : (rootCover R u n hn).I₀) :
    (AffineCommGroupScheme.multiplicativeScheme R).Point
        ((rootCover R u n hn).overFamily i) ≃*
      (RootAlgebra R u n)ˣ :=
  (CommGroupScheme.pointMulEquivOfOverIso
      (AffineCommGroupScheme.multiplicativeScheme R)
      (rootCoverObjectIso R u n hn i)).trans
    (AffineCommGroupScheme.multiplicativePointMulEquiv R (RootAlgebra R u n))

/-- Restricting a global `G_m` point to its root cover applies the algebra map to the
corresponding base unit. -/
theorem multiplicativePointMulEquiv_restrict_rootCover [Nontrivial R]
    (q : CommGroupScheme.BasePoint (AffineCommGroupScheme.multiplicativeScheme R))
    (n : ℕ) (hn : n ≠ 0) (i : (rootCover R
      (AffineCommGroupScheme.multiplicativeBasePointMulEquiv R q) n hn).I₀) :
    rootCoverPointMulEquiv R
        (AffineCommGroupScheme.multiplicativeBasePointMulEquiv R q) n hn i
        (CommGroupScheme.restrictBasePoint _
          (rootCover R (AffineCommGroupScheme.multiplicativeBasePointMulEquiv R q) n hn) i q) =
      Units.map (algebraMap R
        (RootAlgebra R (AffineCommGroupScheme.multiplicativeBasePointMulEquiv R q) n)).toMonoidHom
        (AffineCommGroupScheme.multiplicativeBasePointMulEquiv R q) := by
  let f := Algebra.ofId R
    (RootAlgebra R (AffineCommGroupScheme.multiplicativeBasePointMulEquiv R q) n)
  let e := rootCoverObjectIso R
    (AffineCommGroupScheme.multiplicativeBasePointMulEquiv R q) n hn i
  have hcover : e.inv ≫ CommGroupScheme.coverToBase
        (rootCover R (AffineCommGroupScheme.multiplicativeBasePointMulEquiv R q) n hn) i =
      AffineCommGroupScheme.testObjectMap f ≫
        (AffineCommGroupScheme.baseObjectIsoSelfTestObject R).inv :=
    Over.mkIdTerminal.hom_ext _ _
  have hpoint :
      CommGroupScheme.pullPoint _ e.inv
          (CommGroupScheme.restrictBasePoint _
            (rootCover R (AffineCommGroupScheme.multiplicativeBasePointMulEquiv R q) n hn) i q) =
        CommGroupScheme.pullPoint _ (AffineCommGroupScheme.testObjectMap f)
          (CommGroupScheme.pullPoint _
            (AffineCommGroupScheme.baseObjectIsoSelfTestObject R).inv q) := by
    unfold CommGroupScheme.restrictBasePoint
    change e.inv ≫
        (CommGroupScheme.coverToBase
          (rootCover R (AffineCommGroupScheme.multiplicativeBasePointMulEquiv R q) n hn) i ≫ q) =
      AffineCommGroupScheme.testObjectMap f ≫
        ((AffineCommGroupScheme.baseObjectIsoSelfTestObject R).inv ≫ q)
    rw [← Category.assoc, ← Category.assoc, hcover]
  change AffineCommGroupScheme.multiplicativePointMulEquiv R _
      (CommGroupScheme.pullPoint _ e.inv
        (CommGroupScheme.restrictBasePoint _ _ i q)) = _
  rw [hpoint]
  exact AffineCommGroupScheme.multiplicativePointMulEquiv_testObjectMap
    f
    (AffineCommGroupScheme.basePointMulEquiv
      (AffineCommGroupScheme.multiplicative R) q)

/-- The geometric `n`th-power endomorphism of `G_m`. -/
abbrev powerMap (n : ℕ) :
    AffineCommGroupScheme.multiplicativeScheme R ⟶
      AffineCommGroupScheme.multiplicativeScheme R :=
  CommGroupScheme.powerEnd _ n

/-- The canonical scheme-theoretic kernel of the `n`th-power map. -/
abbrev powerKernel (n : ℕ) : CommGroupScheme (Spec (.of R)) :=
  CommGroupScheme.kernel (powerMap R n)

/-- The canonical kernel presentation consumed by the checked connecting construction. -/
noncomputable abbrev powerKernelPresentation (n : ℕ) :
    KernelPresentation (powerMap R n) :=
  CommGroupScheme.canonicalKernelPresentation (powerMap R n)

/-- The root point, typed on an arbitrary member of the singleton root cover. -/
noncomputable def rootCoverPoint [Nontrivial R]
    (u : Rˣ) (n : ℕ) (hn : n ≠ 0) (i : (rootCover R u n hn).I₀) :
    AffineCommGroupScheme.multiplicativeScheme R |>.Point
      ((rootCover R u n hn).overFamily i) :=
  (rootCoverPointMulEquiv R u n hn i).symm (rootUnit R u n hn)

@[simp]
theorem multiplicativePointMulEquiv_rootCoverPoint [Nontrivial R]
    (u : Rˣ) (n : ℕ) (hn : n ≠ 0) (i : (rootCover R u n hn).I₀) :
    rootCoverPointMulEquiv R u n hn i (rootCoverPoint R u n hn i) =
      rootUnit R u n hn :=
  (rootCoverPointMulEquiv R u n hn i).apply_symm_apply (rootUnit R u n hn)

/-- Every global `G_m` point lifts on the explicit fppf cover obtained by adjoining an
`n`th root of its associated unit. -/
noncomputable def localLift [Nontrivial R]
    (n : ℕ) (hn : n ≠ 0)
    (q : BasePoint (AffineCommGroupScheme.multiplicativeScheme R)) :
    (powerKernelPresentation R n).LocalLift.{u} q where
  cover := rootCover R (AffineCommGroupScheme.multiplicativeBasePointMulEquiv R q) n hn
  lift i := rootCoverPoint R
    (AffineCommGroupScheme.multiplicativeBasePointMulEquiv R q) n hn i
  maps_to i := by
    apply (rootCoverPointMulEquiv R
      (AffineCommGroupScheme.multiplicativeBasePointMulEquiv R q) n hn i).injective
    rw [CommGroupScheme.mapPoint_powerEnd, map_pow,
      multiplicativePointMulEquiv_rootCoverPoint, rootUnit_pow]
    exact (multiplicativePointMulEquiv_restrict_rootCover R q n hn i).symm

/-- The positive power map on `G_m` is locally surjective for the fppf topology, witnessed by
the finite-free root cover rather than by an assumed sheaf-surjectivity principle. -/
noncomputable def locallyLiftable [Nontrivial R] (n : ℕ) (hn : n ≠ 0) :
    (powerKernelPresentation R n).LocallyLiftable.{u} where
  localLift := localLift R n hn

/-- The checked geometric Kummer boundary into fppf `H¹` of the scheme-theoretic power
kernel. -/
noncomputable def boundaryHom [Nontrivial R] (n : ℕ) (hn : n ≠ 0) :
    BasePoint (AffineCommGroupScheme.multiplicativeScheme R) →*
      (powerKernel R n).FppfHOne.{u} :=
  (locallyLiftable R n hn).boundaryHom

/-- The geometric boundary written on the unit group via the checked `G_m(R) ≃ Rˣ`
equivalence. -/
noncomputable def unitBoundaryHom [Nontrivial R] (n : ℕ) (hn : n ≠ 0) :
    Rˣ →* (powerKernel R n).FppfHOne.{u} :=
  (boundaryHom R n hn).comp
    (AffineCommGroupScheme.multiplicativeBasePointMulEquiv R).symm.toMonoidHom

/-- The geometric boundary kills actual `n`th powers of units. -/
@[simp]
theorem unitBoundaryHom_pow [Nontrivial R]
    (n : ℕ) (hn : n ≠ 0) (u : Rˣ) :
    unitBoundaryHom R n hn (u ^ n) = 1 := by
  let x := (AffineCommGroupScheme.multiplicativeBasePointMulEquiv R).symm u
  have h := (locallyLiftable R n hn).boundaryHom_mapPoint x
  rw [CommGroupScheme.mapPoint_powerEnd] at h
  change boundaryHom R n hn
      ((AffineCommGroupScheme.multiplicativeBasePointMulEquiv R).symm (u ^ n)) = 1
  rw [map_pow]
  exact h

/-- The checked Kummer boundary factors through units modulo actual `n`th powers. -/
noncomputable def unitKummerBoundaryHom [Nontrivial R]
    (n : ℕ) (hn : n ≠ 0) :
    FiniteFlatCommGroupScheme.UnitKummerClasses R n →*
      (powerKernel R n).FppfHOne.{u} :=
  QuotientGroup.lift (powMonoidHom n : Rˣ →* Rˣ).range
    (unitBoundaryHom R n hn) (by
      intro x hx
      obtain ⟨u, rfl⟩ := hx
      exact MonoidHom.mem_ker.mpr (unitBoundaryHom_pow R n hn u))

/-- The quotient boundary agrees with the geometric boundary on every represented unit. -/
@[simp]
theorem unitKummerBoundaryHom_mk [Nontrivial R]
    (n : ℕ) (hn : n ≠ 0) (u : Rˣ) :
    unitKummerBoundaryHom R n hn
        (QuotientGroup.mk' (powMonoidHom n : Rˣ →* Rˣ).range u) =
      unitBoundaryHom R n hn u := by
  exact QuotientGroup.lift_mk'
    (N := (powMonoidHom n : Rˣ →* Rˣ).range) _ u

/-- Every geometric Kummer class is the quotient boundary of the unit attached to its global
`G_m` point.  This is the downstream consumer linking the explicit unit quotient to the actual
Čech boundary. -/
theorem boundaryHom_eq_unitKummerBoundaryHom [Nontrivial R]
    (n : ℕ) (hn : n ≠ 0)
    (q : BasePoint (AffineCommGroupScheme.multiplicativeScheme R)) :
    boundaryHom R n hn q =
      unitKummerBoundaryHom R n hn
        (QuotientGroup.mk' (powMonoidHom n : Rˣ →* Rˣ).range
          (AffineCommGroupScheme.multiplicativeBasePointMulEquiv R q)) := by
  rw [unitKummerBoundaryHom_mk]
  change boundaryHom R n hn q = boundaryHom R n hn
    ((AffineCommGroupScheme.multiplicativeBasePointMulEquiv R).symm
      (AffineCommGroupScheme.multiplicativeBasePointMulEquiv R q))
  rw [MulEquiv.symm_apply_apply]

end CommGroupScheme.MultiplicativeKummer

end AlgebraicGeometry
