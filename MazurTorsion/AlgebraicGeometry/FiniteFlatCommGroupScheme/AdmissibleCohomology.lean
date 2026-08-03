/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.GroupTheory.Index
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.AdmissibleFiltration
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfHOneCommGroup

/-!
# Iterated admissible filtrations and the low-degree cardinal estimate

This file advances the finite-flat input to Mazur's Eisenstein rank-zero argument in two
directions.

First, `AdmissibleFiltration` is an honest iterated geometric filtration.  Each extension uses
the checked fppf quotient presentation from the previous layer, so exactness is the certified
scheme-theoretic kernel universal property rather than an unrelated sequence of point groups.
Every affine point is killed by `p ^ length`, and the result commutes with arbitrary base change.
The old two-factor `AdmissibleFiltrationStep` compiles as a downstream instance.

Second, `FppfLowDegreeExactSequence` isolates the elementary finite-group calculation behind
Mazur's inequality

`h¹(G) - h⁰(G) ≤ (h¹(G₁) - h⁰(G₁)) + (h¹(G₃) - h⁰(G₃))`.

It requires the actual five low-degree homomorphisms, injectivity at the left endpoint, exactness
at all four interior terms, finiteness, and certified `p`-power cardinalities.  Thus it can be
instantiated by global fppf cohomology without postulating any cohomology theorem here.  The
cardinal bound `middleHOne_natCard_le_pow` is the form consumed by the later rank-zero argument.

At the pinned Mathlib revision, `Scheme.fppfTopology` and cover-level
`PresheafOfGroups.H1` exist, but the latter file explicitly leaves the global colimit over covers,
the connecting morphism, and the low-degree exact sequence as TODOs.  The repository's
`FppfHOne` module now constructs the first of these from genuine cover refinements.  This file
still does not pretend that the connecting morphism or exact sequence follows automatically.
`UnitKummerClasses` is only the explicit unit quotient on the right of the Kummer comparison; its
exponent and finite-unit cardinal bound are proved directly.

The mathematical source for the inequality and elementary Kummer reduction is
B. Mazur, *Modular curves and the Eisenstein ideal*, Chapter I, Proposition 1.7.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme

/-- The explicit unit quotient occurring on the right of the fppf Kummer sequence.  This is
defined without claiming the still-missing comparison with global fppf `H¹`. -/
abbrev UnitKummerClasses (R : Type*) [CommRing R] (p : ℕ) : Type _ :=
  Rˣ ⧸ (powMonoidHom p : Rˣ →* Rˣ).range

namespace UnitKummerClasses

variable {R : Type*} [CommRing R] (p : ℕ)

/-- Every explicit Kummer unit class is killed by `p`. -/
theorem pow_eq_one (x : UnitKummerClasses R p) : x ^ p = 1 := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom p : Rˣ →* Rˣ).range x
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff (u ^ p)).mpr ⟨u, rfl⟩

/-- If the unit group is finite, quotienting by actual `p`-th powers cannot increase its
cardinality. -/
theorem natCard_le [Finite Rˣ] : Nat.card (UnitKummerClasses R p) ≤ Nat.card Rˣ :=
  Nat.card_le_card_of_surjective
    (QuotientGroup.mk' (powMonoidHom p : Rˣ →* Rˣ).range)
    (QuotientGroup.mk'_surjective (powMonoidHom p : Rˣ →* Rˣ).range)

end UnitKummerClasses

/-- An iterated filtration by exact supplied quotients whose successive kernels are each
identified with `Z/pZ` or `mu_p`.  The terminal term is itself one admissible simple factor. -/
inductive AdmissibleFiltration
    (R : Type) [CommRing R] (p : ℕ) [NeZero p] :
    FiniteFlatCommGroupScheme (Spec (.of R)) → Type _ where
  | simple {G} (factor : AdmissibleSimpleFactor R p G) :
      AdmissibleFiltration R p G
  | extension {G} (quotient : FppfQuotientPresentation G)
      (kernelFactor : AdmissibleSimpleFactor R p quotient.kernelPresentation.kernel)
      (quotientFiltration : AdmissibleFiltration R p quotient.quotient) :
      AdmissibleFiltration R p G

namespace AdmissibleFiltration

variable {R : Type} [CommRing R] {p : ℕ} [NeZero p]
variable {G : FiniteFlatCommGroupScheme (Spec (.of R))}

/-- Number of admissible simple factors in a filtration. -/
def length : {G : FiniteFlatCommGroupScheme (Spec (.of R))} →
    AdmissibleFiltration R p G → ℕ
  | _, .simple _ => 1
  | _, .extension _ _ F => F.length + 1

/-- Every affine point of a length-`r` admissible filtration is killed by `p ^ r`. -/
theorem point_pow_eq_one [Nontrivial R]
    (F : AdmissibleFiltration R p G)
    (B : Type) [CommRing B] [Algebra R B]
    (x : G.Point (AffineCommGroupScheme.testObject (R := R) B)) :
    x ^ (p ^ F.length) = 1 := by
  induction F with
  | simple factor =>
      simpa [length] using factor.point_pow_eq_one B x
  | @extension G quotient kernelFactor quotientFiltration ih =>
      let X := AffineCommGroupScheme.testObject (R := R) B
      have hquotient :
          (mapPoint quotient.project X x) ^ (p ^ quotientFiltration.length) = 1 :=
        ih (mapPoint quotient.project X x)
      have hproject :
          mapPoint quotient.project X (x ^ (p ^ quotientFiltration.length)) = 1 := by
        rw [map_pow]
        exact hquotient
      obtain ⟨y, hy⟩ :=
        (quotient.project_point_eq_one_iff X
          (x ^ (p ^ quotientFiltration.length))).mp hproject
      have hkernel : y ^ p = 1 := kernelFactor.point_pow_eq_one B y
      calc
        x ^ (p ^ (AdmissibleFiltration.extension quotient kernelFactor
            quotientFiltration).length) =
            (x ^ (p ^ quotientFiltration.length)) ^ p := by
              rw [length, pow_succ, pow_mul]
        _ = (mapPoint quotient.kernelPresentation.inclusion X y) ^ p := by rw [hy]
        _ = mapPoint quotient.kernelPresentation.inclusion X (y ^ p) :=
          (map_pow _ _ _).symm
        _ = 1 := by rw [hkernel, map_one]

/-- Pull every exact quotient and simple factor in an admissible filtration through scalar
extension. -/
def baseChange
    {K : Type} [CommRing K] [Nontrivial K] [Algebra R K]
    (F : AdmissibleFiltration R p G) :
    AdmissibleFiltration K p
      ((FiniteFlatCommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj G) := by
  induction F with
  | simple factor => exact .simple factor.baseChange
  | extension quotient kernelFactor quotientFiltration ih =>
      exact .extension
        (quotient.baseChangePresentation
          (Spec.map (CommRingCat.ofHom (algebraMap R K))))
        kernelFactor.baseChange ih

/-- Scalar extension preserves the number of graded pieces. -/
@[simp]
theorem length_baseChange
    {K : Type} [CommRing K] [Nontrivial K] [Algebra R K]
    (F : AdmissibleFiltration R p G) :
    (F.baseChange (K := K)).length = F.length := by
  induction F with
  | simple factor => rfl
  | extension quotient kernelFactor quotientFiltration ih =>
      change (quotientFiltration.baseChange (K := K)).length + 1 =
        quotientFiltration.length + 1
      rw [ih]

/-- The iterated exponent bound after arbitrary scalar extension. -/
theorem baseChange_point_pow_eq_one
    {K : Type} [CommRing K] [Nontrivial K] [Algebra R K]
    (F : AdmissibleFiltration R p G)
    (B : Type) [CommRing B] [Algebra K B]
    (x : ((FiniteFlatCommGroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj G).Point
        (AffineCommGroupScheme.testObject (R := K) B)) :
    x ^ (p ^ F.length) = 1 := by
  simpa using (F.baseChange (K := K)).point_pow_eq_one B x

end AdmissibleFiltration

/-- A finite-flat group equipped with an honest iterated admissible filtration. -/
structure AdmissibleFiniteFlatGroup
    (R : Type) [CommRing R] (p : ℕ) [NeZero p]
    (G : FiniteFlatCommGroupScheme (Spec (.of R))) where
  prime : p.Prime
  filtration : AdmissibleFiltration R p G

namespace AdmissibleFiniteFlatGroup

variable {R : Type} [CommRing R] {p : ℕ} [NeZero p]
variable {G : FiniteFlatCommGroupScheme (Spec (.of R))}

/-- Length of the chosen admissible filtration. -/
def length (D : AdmissibleFiniteFlatGroup R p G) : ℕ := D.filtration.length

/-- The filtration-length point-exponent consumer. -/
theorem point_pow_eq_one [Nontrivial R]
    (D : AdmissibleFiniteFlatGroup R p G)
    (B : Type) [CommRing B] [Algebra R B]
    (x : G.Point (AffineCommGroupScheme.testObject (R := R) B)) :
    x ^ (p ^ D.length) = 1 :=
  D.filtration.point_pow_eq_one B x

/-- Scalar extension of an admissible finite-flat group and its entire chosen filtration. -/
def baseChange
    {K : Type} [CommRing K] [Nontrivial K] [Algebra R K]
    (D : AdmissibleFiniteFlatGroup R p G) :
    AdmissibleFiniteFlatGroup K p
      ((FiniteFlatCommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj G) where
  prime := D.prime
  filtration := D.filtration.baseChange

/-- The public base-changed point-exponent consumer. -/
theorem baseChange_point_pow_eq_one
    {K : Type} [CommRing K] [Nontrivial K] [Algebra R K]
    (D : AdmissibleFiniteFlatGroup R p G)
    (B : Type) [CommRing B] [Algebra K B]
    (x : ((FiniteFlatCommGroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj G).Point
        (AffineCommGroupScheme.testObject (R := K) B)) :
    x ^ (p ^ D.length) = 1 :=
  D.filtration.baseChange_point_pow_eq_one B x

end AdmissibleFiniteFlatGroup

namespace AdmissibleFiltrationStep

variable {R : Type} [CommRing R] {p : ℕ} [NeZero p]
variable {G : FiniteFlatCommGroupScheme (Spec (.of R))}

/-- Regard the already-checked two-factor exact presentation as the first nontrivial iterated
admissible filtration. -/
def toAdmissibleFiltration (D : AdmissibleFiltrationStep R p G) :
    AdmissibleFiltration R p G :=
  .extension D.toFppfQuotientPresentation D.kernelFactor (.simple D.quotientFactor)

@[simp]
theorem toAdmissibleFiltration_length (D : AdmissibleFiltrationStep R p G) :
    D.toAdmissibleFiltration.length = 2 := rfl

/-- The existing exact one-step API is a genuine consumer of the iterated interface. -/
def toAdmissibleFiniteFlatGroup (D : AdmissibleFiltrationStep R p G) :
    AdmissibleFiniteFlatGroup R p G where
  prime := D.prime
  filtration := D.toAdmissibleFiltration

theorem toAdmissibleFiltration_point_pow_sq_eq_one [Nontrivial R]
    (D : AdmissibleFiltrationStep R p G)
    (B : Type) [CommRing B] [Algebra R B]
    (x : G.Point (AffineCommGroupScheme.testObject (R := R) B)) :
    x ^ (p * p) = 1 := by
  simpa [pow_two] using D.toAdmissibleFiltration.point_pow_eq_one B x

end AdmissibleFiltrationStep

universe u

/-- A finite commutative group together with a certified base-`p` logarithm of its cardinality. -/
structure FinitePGroup (p : ℕ) where
  carrier : Type u
  commGroup : CommGroup carrier
  finite : Finite carrier
  length : ℕ
  card_eq : Nat.card carrier = p ^ length

namespace FinitePGroup

instance {p : ℕ} : CoeSort (FinitePGroup.{u} p) (Type u) := ⟨carrier⟩
instance {p : ℕ} (A : FinitePGroup.{u} p) : CommGroup A := A.commGroup
instance {p : ℕ} (A : FinitePGroup.{u} p) : Finite A := A.finite

universe v uScheme

/-- Package global fppf `H¹` of an actual finite-flat commutative group scheme as a finite
`p`-group once finiteness and its `p`-power cardinality have been proved.  The group law is the
canonical common-refinement law constructed from cover-level cocycles; it is not supplied as an
independent input. -/
def ofFiniteFlatFppfHOne {p : ℕ} {S : Scheme.{uScheme}}
    (G : FiniteFlatCommGroupScheme S)
    [Finite G.FppfHOne.{v}]
    (length : ℕ)
    (card_eq : Nat.card G.FppfHOne.{v} = p ^ length) :
    FinitePGroup p where
  carrier := G.FppfHOne.{v}
  commGroup := inferInstance
  finite := inferInstance
  length := length
  card_eq := card_eq

@[simp]
lemma ofFiniteFlatFppfHOne_length {p : ℕ} {S : Scheme.{uScheme}}
    (G : FiniteFlatCommGroupScheme S)
    [Finite G.FppfHOne.{v}]
    (length : ℕ)
    (card_eq : Nat.card G.FppfHOne.{v} = p ^ length) :
    (ofFiniteFlatFppfHOne G length card_eq).length = length :=
  rfl

/-- The low-degree Euler length `h¹ - h⁰`. -/
def eulerLength {p : ℕ} (hZero hOne : FinitePGroup.{u} p) : ℤ :=
  hOne.length - hZero.length

end FinitePGroup

/-- Checked algebraic data of the five-term portion
`H⁰(G₁) → H⁰(G₂) → H⁰(G₃) → H¹(G₁) → H¹(G₂) → H¹(G₃)`.

This structure does not manufacture or rename global fppf cohomology.  A later geometric
consumer must supply its actual finite groups, maps, and exactness proofs. -/
structure FppfLowDegreeExactSequence (p : ℕ) where
  kernelHZero : FinitePGroup.{u} p
  middleHZero : FinitePGroup.{u} p
  quotientHZero : FinitePGroup.{u} p
  kernelHOne : FinitePGroup.{u} p
  middleHOne : FinitePGroup.{u} p
  quotientHOne : FinitePGroup.{u} p
  includeHZero : kernelHZero →* middleHZero
  projectHZero : middleHZero →* quotientHZero
  boundary : quotientHZero →* kernelHOne
  includeHOne : kernelHOne →* middleHOne
  projectHOne : middleHOne →* quotientHOne
  includeHZero_injective : Function.Injective includeHZero
  exact_middleHZero : Function.MulExact includeHZero projectHZero
  exact_quotientHZero : Function.MulExact projectHZero boundary
  exact_kernelHOne : Function.MulExact boundary includeHOne
  exact_middleHOne : Function.MulExact includeHOne projectHOne

namespace FppfLowDegreeExactSequence

variable {p : ℕ}

private theorem card_eq_range_mul_range
    {A B C : Type*} [Group A] [Group B] [Group C]
    [Finite A] [Finite B] [Finite C]
    (f : A →* B) (g : B →* C) (h : Function.MulExact f g) :
    Nat.card B = Nat.card f.range * Nat.card g.range := by
  calc
    Nat.card B = Nat.card g.ker * g.ker.index := g.ker.card_mul_index.symm
    _ = Nat.card f.range * Nat.card g.range := by
      rw [Subgroup.index_ker g, h.monoidHom_ker_eq]

private theorem card_range_eq_of_injective
    {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (f : A →* B) (hf : Function.Injective f) :
    Nat.card f.range = Nat.card A := by
  symm
  exact Nat.card_congr (Equiv.ofInjective f hf)

/-- Multiplicative cardinal subadditivity for five consecutive maps in an exact sequence.

Unlike `FppfLowDegreeExactSequence.card_euler_le`, this form needs only finiteness of the six
groups.  In particular, a geometric consumer can bound the middle `H¹` without first supplying
its exact `p`-power cardinality. -/
theorem card_euler_le_of_exact
    {A₀ B₀ C₀ : Type u} {A₁ B₁ C₁ : Type v}
    [Group A₀] [Group B₀] [Group C₀]
    [Group A₁] [Group B₁] [Group C₁]
    [Finite A₀] [Finite B₀] [Finite C₀]
    [Finite A₁] [Finite B₁] [Finite C₁]
    (i₀ : A₀ →* B₀) (q₀ : B₀ →* C₀) (d : C₀ →* A₁)
    (i₁ : A₁ →* B₁) (q₁ : B₁ →* C₁)
    (hi₀ : Function.Injective i₀)
    (hB₀ : Function.MulExact i₀ q₀)
    (hC₀ : Function.MulExact q₀ d)
    (hA₁ : Function.MulExact d i₁)
    (hB₁ : Function.MulExact i₁ q₁) :
    Nat.card B₁ * Nat.card A₀ * Nat.card C₀ ≤
      Nat.card B₀ * Nat.card A₁ * Nat.card C₁ := by
  have hcardB₀ := card_eq_range_mul_range i₀ q₀ hB₀
  have hcardC₀ := card_eq_range_mul_range q₀ d hC₀
  have hcardA₁ := card_eq_range_mul_range d i₁ hA₁
  have hcardB₁ := card_eq_range_mul_range i₁ q₁ hB₁
  have hcardA₀ := card_range_eq_of_injective i₀ hi₀
  rw [hcardB₀, hcardC₀, hcardA₁, hcardB₁, ← hcardA₀]
  have hrange : Nat.card q₁.range ≤ Nat.card C₁ :=
    q₁.range.card_le_card_group
  calc
    (Nat.card i₁.range * Nat.card q₁.range) *
          Nat.card i₀.range *
          (Nat.card q₀.range * Nat.card d.range) ≤
        (Nat.card i₁.range * Nat.card C₁) *
          Nat.card i₀.range *
          (Nat.card q₀.range * Nat.card d.range) := by
      gcongr
    _ = (Nat.card i₀.range * Nat.card q₀.range) *
          (Nat.card d.range * Nat.card i₁.range) *
          Nat.card C₁ := by ac_rfl

/-- Multiplicative cardinal form of subadditivity for the five-term exact sequence. -/
theorem card_euler_le (D : FppfLowDegreeExactSequence.{u} p) :
    Nat.card D.middleHOne * Nat.card D.kernelHZero * Nat.card D.quotientHZero ≤
      Nat.card D.middleHZero * Nat.card D.kernelHOne * Nat.card D.quotientHOne := by
  exact card_euler_le_of_exact
    D.includeHZero D.projectHZero D.boundary D.includeHOne D.projectHOne
    D.includeHZero_injective D.exact_middleHZero D.exact_quotientHZero
    D.exact_kernelHOne D.exact_middleHOne

/-- Natural-number form of the low-degree Euler-length inequality. -/
theorem length_euler_le (D : FppfLowDegreeExactSequence.{u} p) (hp : p.Prime) :
    D.middleHOne.length + D.kernelHZero.length + D.quotientHZero.length ≤
      D.middleHZero.length + D.kernelHOne.length + D.quotientHOne.length := by
  have hcard := D.card_euler_le
  rw [D.middleHOne.card_eq, D.kernelHZero.card_eq, D.quotientHZero.card_eq,
    D.middleHZero.card_eq, D.kernelHOne.card_eq, D.quotientHOne.card_eq,
    ← pow_add, ← pow_add, ← pow_add, ← pow_add] at hcard
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hcard

/-- Mazur's low-degree filtration inequality `h¹ - h⁰` for one exact extension step. -/
theorem hOne_sub_hZero_le (D : FppfLowDegreeExactSequence.{u} p) (hp : p.Prime) :
    FinitePGroup.eulerLength D.middleHZero D.middleHOne ≤
      FinitePGroup.eulerLength D.kernelHZero D.kernelHOne +
        FinitePGroup.eulerLength D.quotientHZero D.quotientHOne := by
  have hlength := D.length_euler_le hp
  dsimp [FinitePGroup.eulerLength]
  omega

/-- The form used by the rank-zero argument: once the degree-zero term and the two elementary
degree-one corrections fit under one uniform exponent, the middle degree-one group does too. -/
theorem middleHOne_length_le
    (D : FppfLowDegreeExactSequence.{u} p) (hp : p.Prime) (bound : ℕ)
    (hbound :
      D.middleHZero.length + D.kernelHOne.length + D.quotientHOne.length ≤
        bound + D.kernelHZero.length + D.quotientHZero.length) :
    D.middleHOne.length ≤ bound := by
  have hlength := D.length_euler_le hp
  omega

/-- Cardinal form of `middleHOne_length_le`, ready for a bounded-torsor consumer. -/
theorem middleHOne_natCard_le_pow
    (D : FppfLowDegreeExactSequence.{u} p) (hp : p.Prime) (bound : ℕ)
    (hbound :
      D.middleHZero.length + D.kernelHOne.length + D.quotientHOne.length ≤
        bound + D.kernelHZero.length + D.quotientHZero.length) :
    Nat.card D.middleHOne ≤ p ^ bound := by
  rw [D.middleHOne.card_eq]
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mpr
    (D.middleHOne_length_le hp bound hbound)

end FppfLowDegreeExactSequence

end AlgebraicGeometry.FiniteFlatCommGroupScheme
