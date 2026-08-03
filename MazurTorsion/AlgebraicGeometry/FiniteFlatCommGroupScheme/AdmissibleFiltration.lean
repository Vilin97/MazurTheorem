/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.Examples
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.Quotient

/-!
# Admissible finite-flat filtration steps

This file is the first rank-zero-oriented consumer of the finite-flat kernel and base-change
APIs.  It packages one faithfully flat filtration step whose kernel and quotient are each
identified with one of the two admissible order-`p` factors, the constant group `Z/pZ` or
`mu_p`.

The main theorem is not a reformulation of a point equivalence: it combines the certified
scheme-theoretic kernel universal property with both factor exponents to prove that every
affine point of the middle term is killed by `p^2`.  A separate compatibility datum records
exactly what remains to transport a certified kernel presentation through geometric base
change; once supplied, the same exponent theorem applies after scalar extension and the
constant/`mu_p` factors are normalized by the checked named base-change isomorphisms.

This is deliberately narrower than a connected--etale or Oort--Tate classification.  Iterated
filtrations, fppf cohomology, and Raynaud uniqueness remain later rank-zero work.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry
namespace FiniteFlatCommGroupScheme

/-- A chosen identification of a finite-flat group scheme with one of the two order-`p`
factors permitted in Mazur's admissible filtrations. -/
inductive AdmissibleSimpleFactor
    (R : Type) [CommRing R] (p : ℕ) [NeZero p]
    (Q : FiniteFlatCommGroupScheme (Spec (.of R))) where
  /-- The etale factor `Z/pZ`. -/
  | constant (iso : Q ≅ constantScheme R (Multiplicative (ZMod p)))
  /-- The multiplicative factor `mu_p`. -/
  | multiplicative (iso : Q ≅ muScheme R p)

namespace AdmissibleSimpleFactor

variable {R : Type} [CommRing R] {p : ℕ} [NeZero p]
variable {Q Q' : FiniteFlatCommGroupScheme (Spec (.of R))}

/-- Transport a chosen simple-factor presentation across an isomorphism of finite-flat group
schemes. -/
def ofIso (F : AdmissibleSimpleFactor R p Q) (e : Q' ≅ Q) :
    AdmissibleSimpleFactor R p Q' :=
  match F with
  | .constant i => .constant (e ≪≫ i)
  | .multiplicative i => .multiplicative (e ≪≫ i)

/-- An admissible factor stays admissible after scalar extension.  The result is expressed
using the named constant and `mu_p` models over the new base. -/
def baseChange
    {K : Type} [CommRing K] [Algebra R K]
    (F : AdmissibleSimpleFactor R p Q) :
    AdmissibleSimpleFactor K p
      ((FiniteFlatCommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj Q) :=
  match F with
  | .constant i =>
      .constant
        ((FiniteFlatCommGroupScheme.baseChange
            (Spec.map (CommRingCat.ofHom (algebraMap R K)))).mapIso i ≪≫
          constantBaseChangeIso (R := R) (K := K) (Multiplicative (ZMod p)))
  | .multiplicative i =>
      .multiplicative
        ((FiniteFlatCommGroupScheme.baseChange
            (Spec.map (CommRingCat.ofHom (algebraMap R K)))).mapIso i ≪≫
          muBaseChangeIso (R := R) (K := K) p)

/-- Every affine point of an admissible order-`p` factor is killed by `p`. -/
theorem point_pow_eq_one [Nontrivial R]
    (F : AdmissibleSimpleFactor R p Q)
    (B : Type) [CommRing B] [Algebra R B]
    (x : Q.Point (AffineCommGroupScheme.testObject (R := R) B)) :
    x ^ p = 1 := by
  let X := AffineCommGroupScheme.testObject (R := R) B
  cases F with
  | constant i =>
      apply (pointMulEquivOfIso i X).injective
      rw [map_pow, map_one]
      have h := (FiniteFlatCommGroupScheme.constant R
        (Multiplicative (ZMod p))).realize_point_pow_order_eq_one B
        (pointMulEquivOfIso i X x)
      have hcard : Nat.card (Multiplicative (ZMod p)) = p :=
        (Nat.card_congr
          (Multiplicative.ofAdd : ZMod p ≃ Multiplicative (ZMod p))).trans
            (Nat.card_zmod p)
      simpa [constant_order, ← Nat.card_eq_fintype_card, hcard] using h
  | multiplicative i =>
      apply (pointMulEquivOfIso i X).injective
      rw [map_pow, map_one]
      have h := (mu R p).realize_point_pow_order_eq_one B
        (pointMulEquivOfIso i X x)
      simpa [mu_order] using h

end AdmissibleSimpleFactor

/-- The named constant-quotient square controls the actual pointwise kernel after scalar
extension.  This is stronger than exposing the point equivalence of either endpoint: it says
that the base-changed quotient projection and the quotient projection over the new base cut
out the same kernel under the named source identification. -/
theorem constantQuotient_baseChange_kernel_condition
    {R K : Type} [CommRing R] [CommRing K] [Algebra R K]
    {A : Type} [CommGroup A] [Fintype A] (N : Subgroup A)
    (X : Over (Spec (.of K)))
    (x : ((FiniteFlatCommGroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj
        (constantScheme R A)).Point X) :
    mapPoint
        ((FiniteFlatCommGroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map
            (constantQuotientMap R N)) X x = 1 ↔
      mapPoint (constantQuotientMap K N) X
        (mapPoint (constantBaseChangeIso (R := R) (K := K) A).hom X x) = 1 := by
  let b := FiniteFlatCommGroupScheme.baseChange
    (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  let sourceIso := constantBaseChangeIso (R := R) (K := K) A
  let targetIso := constantQuotientBaseChangeIso (R := R) (K := K) N
  have hpoint :
      mapPoint targetIso.hom X
          (mapPoint (b.map (constantQuotientMap R N)) X x) =
        mapPoint (constantQuotientMap K N) X
          (mapPoint sourceIso.hom X x) := by
    rw [← MonoidHom.comp_apply, ← mapPoint_comp,
      ← MonoidHom.comp_apply, ← mapPoint_comp]
    exact congrArg (fun f ↦ mapPoint f X x)
      (constantQuotientMap_baseChange_naturality (R := R) (K := K) N)
  constructor
  · intro hx
    calc
      mapPoint (constantQuotientMap K N) X (mapPoint sourceIso.hom X x) =
          mapPoint targetIso.hom X
            (mapPoint (b.map (constantQuotientMap R N)) X x) := hpoint.symm
      _ = mapPoint targetIso.hom X 1 := by rw [hx]
      _ = 1 := map_one _
  · intro hx
    apply (pointMulEquivOfIso targetIso X).injective
    calc
      pointMulEquivOfIso targetIso X
          (mapPoint (b.map (constantQuotientMap R N)) X x) =
        mapPoint (constantQuotientMap K N) X
          (mapPoint sourceIso.hom X x) := hpoint
      _ = 1 := hx
      _ = pointMulEquivOfIso targetIso X 1 := (map_one _).symm

/-- One exact step of an admissible `p`-primary finite-flat filtration.  The projection is
faithfully flat, and exactness at the middle term is carried by a certified scheme-theoretic
kernel presentation of `project`; both the kernel and quotient are supplied with honest
constant-or-multiplicative factor presentations.  The projection is automatically finite since
it is a morphism between schemes finite over the base; local finite presentation is recorded
separately, since it does not follow from finiteness over an arbitrary base ring. -/
structure AdmissibleFiltrationStep
    (R : Type) [CommRing R] (p : ℕ) [NeZero p]
    (G : FiniteFlatCommGroupScheme (Spec (.of R))) where
  /-- The filtration is primary at an actual rational prime. -/
  prime : p.Prime
  /-- The graded quotient of this step. -/
  quotient : FiniteFlatCommGroupScheme (Spec (.of R))
  /-- Projection from the middle term to the graded quotient. -/
  project : G ⟶ quotient
  /-- The quotient projection is flat. -/
  project_flat : Flat (FiniteFlatCommGroupScheme.hom project)
  /-- The quotient projection is surjective on the underlying topological spaces. -/
  project_surjective : Surjective (FiniteFlatCommGroupScheme.hom project)
  /-- The quotient projection is locally of finite presentation. -/
  project_lfp : LocallyOfFinitePresentation (FiniteFlatCommGroupScheme.hom project)
  /-- The scheme-theoretic kernel, including its universal point-lifting property. -/
  kernelPresentation : KernelPresentation project
  /-- Identification of the kernel with `Z/pZ` or `mu_p`. -/
  kernelFactor : AdmissibleSimpleFactor R p kernelPresentation.kernel
  /-- Identification of the quotient with `Z/pZ` or `mu_p`. -/
  quotientFactor : AdmissibleSimpleFactor R p quotient

namespace AdmissibleFiltrationStep

variable {R : Type} [CommRing R]
variable {p : ℕ} [NeZero p]
variable {G : FiniteFlatCommGroupScheme (Spec (.of R))}

/-- The projection in an admissible filtration step is finite.  This is not an extra field:
both its source and target are finite over the base, and the target structure map is separated. -/
theorem project_isFinite (D : AdmissibleFiltrationStep R p G) :
    IsFinite (FiniteFlatCommGroupScheme.hom D.project) := by
  haveI : IsFinite
      (FiniteFlatCommGroupScheme.hom D.project ≫ D.quotient.structureMap) := by
    rw [hom_comp_structureMap]
    infer_instance
  exact IsFinite.of_comp (FiniteFlatCommGroupScheme.hom D.project) D.quotient.structureMap

/-- The finite quotient projection is locally of finite presentation. -/
theorem project_locallyOfFinitePresentation (D : AdmissibleFiltrationStep R p G) :
    LocallyOfFinitePresentation (FiniteFlatCommGroupScheme.hom D.project) :=
  D.project_lfp

/-- The projection is an fppf cover in the concrete sense used by the later descent consumer:
it is flat, surjective, and locally of finite presentation. -/
theorem project_is_fppf (D : AdmissibleFiltrationStep R p G) :
    Flat (FiniteFlatCommGroupScheme.hom D.project) ∧
      Surjective (FiniteFlatCommGroupScheme.hom D.project) ∧
        LocallyOfFinitePresentation (FiniteFlatCommGroupScheme.hom D.project) :=
  ⟨D.project_flat, D.project_surjective, D.project_locallyOfFinitePresentation⟩

/-- The arithmetic content of one admissible filtration step: two order-`p` graded pieces
force exponent dividing `p^2` on every affine point of the middle finite-flat group scheme. -/
theorem point_pow_sq_eq_one
    [Nontrivial R]
    (D : AdmissibleFiltrationStep R p G)
    (B : Type) [CommRing B] [Algebra R B]
    (x : G.Point (AffineCommGroupScheme.testObject (R := R) B)) :
    x ^ (p * p) = 1 := by
  let X := AffineCommGroupScheme.testObject (R := R) B
  have hquotient :
      (mapPoint D.project X x) ^ p = 1 :=
    D.quotientFactor.point_pow_eq_one B (mapPoint D.project X x)
  have hproject : mapPoint D.project X (x ^ p) = 1 := by
    rw [map_pow]
    exact hquotient
  obtain ⟨y, hy, -⟩ := D.kernelPresentation.existsUnique_point_lift X (x ^ p) hproject
  have hkernel : y ^ p = 1 := D.kernelFactor.point_pow_eq_one B y
  calc
    x ^ (p * p) = (x ^ p) ^ p := pow_mul x p p
    _ = (mapPoint D.kernelPresentation.inclusion X y) ^ p := by rw [hy]
    _ = mapPoint D.kernelPresentation.inclusion X (y ^ p) := (map_pow _ _ _).symm
    _ = mapPoint D.kernelPresentation.inclusion X 1 := by rw [hkernel]
    _ = 1 := map_one _

/-- The precise extra datum needed to transport a certified kernel presentation across base
change.  The compatibility equation prevents replacing the true base-changed kernel inclusion
with an unrelated isomorphic object. -/
structure KernelBaseChangeCompatibility
    (D : AdmissibleFiltrationStep R p G)
    (K : Type) [CommRing K] [Algebra R K] where
  /-- A certified kernel presentation for the base-changed projection. -/
  presentation : KernelPresentation
    ((FiniteFlatCommGroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map D.project)
  /-- Its kernel is the geometric pullback of the original kernel. -/
  kernelIso : presentation.kernel ≅
    (FiniteFlatCommGroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj
        D.kernelPresentation.kernel
  /-- The kernel isomorphism respects the actual inclusions into the middle term. -/
  inclusion_compatibility :
    kernelIso.hom ≫
        (FiniteFlatCommGroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map
            D.kernelPresentation.inclusion =
      presentation.inclusion

/-- A point killed by the base-changed projection really lifts through the geometric pullback
of the original kernel inclusion.  This consumes the inclusion compatibility in
`KernelBaseChangeCompatibility`; it is the pointwise consequence needed by an iterated
admissible filtration. -/
theorem exists_baseChangedKernel_lift
    (D : AdmissibleFiltrationStep R p G)
    (K : Type) [CommRing K] [Algebra R K]
    (C : D.KernelBaseChangeCompatibility K)
    (X : Over (Spec (.of K)))
    (x : ((FiniteFlatCommGroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj G).Point X)
    (hx : mapPoint
      ((FiniteFlatCommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map D.project) X x = 1) :
    ∃ y : ((FiniteFlatCommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj
          D.kernelPresentation.kernel).Point X,
      mapPoint
        ((FiniteFlatCommGroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map
            D.kernelPresentation.inclusion) X y = x := by
  obtain ⟨z, hz, -⟩ := C.presentation.existsUnique_point_lift X x hx
  refine ⟨mapPoint C.kernelIso.hom X z, ?_⟩
  calc
    mapPoint
        ((FiniteFlatCommGroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map
            D.kernelPresentation.inclusion) X (mapPoint C.kernelIso.hom X z) =
      mapPoint (C.kernelIso.hom ≫
        (FiniteFlatCommGroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map
            D.kernelPresentation.inclusion) X z := by
        rw [mapPoint_comp]
        rfl
    _ = mapPoint C.presentation.inclusion X z := by
      rw [C.inclusion_compatibility]
    _ = x := hz

/-- Transport an admissible filtration step through scalar extension once the genuine
scheme-theoretic kernel comparison has been supplied. -/
def baseChange
    (D : AdmissibleFiltrationStep R p G)
    (K : Type) [CommRing K] [Nontrivial K] [Algebra R K]
    (C : D.KernelBaseChangeCompatibility K) :
    AdmissibleFiltrationStep K p
      ((FiniteFlatCommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj G) where
  prime := D.prime
  quotient := (FiniteFlatCommGroupScheme.baseChange
    (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj D.quotient
  project := (FiniteFlatCommGroupScheme.baseChange
    (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map D.project
  project_flat := by
    exact MorphismProperty.overPullbackMap
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) D.project.hom.hom.hom.hom D.project_flat
  project_surjective := by
    exact MorphismProperty.overPullbackMap
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) D.project.hom.hom.hom.hom
        D.project_surjective
  project_lfp := by
    exact MorphismProperty.overPullbackMap
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) D.project.hom.hom.hom.hom D.project_lfp
  kernelPresentation := C.presentation
  kernelFactor := D.kernelFactor.baseChange.ofIso C.kernelIso
  quotientFactor := D.quotientFactor.baseChange

/-- The `p^2` exponent bound survives scalar extension for a kernel-compatible admissible
filtration step.  This is the compiled downstream consumer of the factor and morphism
base-change interfaces. -/
theorem baseChange_point_pow_sq_eq_one
    (D : AdmissibleFiltrationStep R p G)
    (K : Type) [CommRing K] [Nontrivial K] [Algebra R K]
    (C : D.KernelBaseChangeCompatibility K)
    (B : Type) [CommRing B] [Algebra K B]
    (x : ((FiniteFlatCommGroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj G).Point
        (AffineCommGroupScheme.testObject (R := K) B)) :
    x ^ (p * p) = 1 :=
  (D.baseChange K C).point_pow_sq_eq_one B x

end AdmissibleFiltrationStep

end FiniteFlatCommGroupScheme
end AlgebraicGeometry
