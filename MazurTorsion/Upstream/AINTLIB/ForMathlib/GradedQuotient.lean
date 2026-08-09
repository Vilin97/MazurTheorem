/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate. Ticket T-A2a.
-/
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.GradedAlgebra.RingHom
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The quotient of a graded ring by a homogeneous ideal is graded

For a graded algebra `𝒜 : ι → Submodule R A` and a homogeneous ideal
`I : HomogeneousIdeal 𝒜`, the images `HomogeneousIdeal.quotientGrading I n :=
(𝒜 n).map (mkₐ)` grade the quotient ring `A ⧸ I.toIdeal`: the decomposition of `A`
descends because homogeneity of `I` is precisely the statement that the graded
components of elements of `I` stay in `I`.

This is the missing ingredient for `Proj` of a quotient (e.g. a projective plane curve
as `Proj (R[X,Y,Z]/(F))` with `F` homogeneous), for which mathlib provides
`Proj.toSpecZero`, properness, and `fromOfGlobalSections`.

## Main definitions

* `HomogeneousIdeal.quotientGrading`: the induced grading on `A ⧸ I.toIdeal`.
* `HomogeneousIdeal.quotientGradingGradedAlgebra`: the `GradedAlgebra` instance on it.
-/

namespace HomogeneousIdeal

open DirectSum

variable {ι R A : Type*} [DecidableEq ι] [AddCommMonoid ι] [CommRing R] [CommRing A]
  [Algebra R A] {𝒜 : ι → Submodule R A} [GradedAlgebra 𝒜] (I : HomogeneousIdeal 𝒜)

/-- The quotient map `A → A ⧸ I`, as a linear map over `R`. -/
private abbrev mkL : A →ₗ[R] A ⧸ I.toIdeal :=
  (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap

/-- The grading on `A ⧸ I` induced by a grading on `A` and a homogeneous ideal `I`:
the `n`-th piece is the image of `𝒜 n`. -/
def quotientGrading (n : ι) : Submodule R (A ⧸ I.toIdeal) :=
  (𝒜 n).map (mkL I)

lemma mk_mem_quotientGrading {n : ι} {a : A} (ha : a ∈ 𝒜 n) :
    Ideal.Quotient.mk I.toIdeal a ∈ quotientGrading I n :=
  Submodule.mem_map.mpr ⟨a, ha, rfl⟩

instance : SetLike.GradedMonoid (quotientGrading I) where
  one_mem := Submodule.mem_map.mpr
    ⟨1, SetLike.one_mem_graded 𝒜, map_one (Ideal.Quotient.mkₐ R I.toIdeal)⟩
  mul_mem := by
    intro m n x y hx hy
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp hy
    exact Submodule.mem_map.mpr
      ⟨a * b, SetLike.mul_mem_graded ha hb, map_mul (Ideal.Quotient.mkₐ R I.toIdeal) a b⟩

/-- The componentwise map `⨁ n, 𝒜 n →+ ⨁ n, (𝒜 n).map mk` induced by the quotient
map. -/
private def quotientDecomposeAux : (⨁ n, 𝒜 n) →+ ⨁ n, quotientGrading I n :=
  DFinsupp.mapRange.addMonoidHom fun n => ((mkL I).submoduleMap (𝒜 n)).toAddMonoidHom

private lemma quotientDecomposeAux_apply (x : ⨁ n, 𝒜 n) (n : ι) :
    quotientDecomposeAux I x n = (mkL I).submoduleMap (𝒜 n) (x n) :=
  rfl

private lemma quotientDecomposeAux_of (n : ι) (a : 𝒜 n) :
    quotientDecomposeAux I (DirectSum.of _ n a) =
      DirectSum.of _ n ((mkL I).submoduleMap (𝒜 n) a) := by
  classical
  exact DFinsupp.mapRange_single (hf := fun n => map_zero _)

private lemma quotientDecomposeAux_coe (x : ⨁ n, 𝒜 n) :
    DirectSum.coeAddMonoidHom (quotientGrading I) (quotientDecomposeAux I x) =
      Ideal.Quotient.mk I.toIdeal (DirectSum.coeAddMonoidHom 𝒜 x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of n a =>
    rw [quotientDecomposeAux_of]
    exact (DirectSum.coeAddMonoidHom_of (quotientGrading I) n _).trans
      (congrArg (Ideal.Quotient.mk I.toIdeal) (DirectSum.coeAddMonoidHom_of 𝒜 n a)).symm
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- The decomposition of the quotient ring: descend the decomposition of `A`.
Well-defined precisely because `I` is homogeneous. -/
private def quotientDecompose (x : A ⧸ I.toIdeal) : ⨁ n, quotientGrading I n :=
  Quotient.liftOn' x (fun a => quotientDecomposeAux I (DirectSum.decompose 𝒜 a)) (by
    intro a b hab
    have hab' : a - b ∈ I.toIdeal := (Submodule.quotientRel_def _).mp hab
    ext n
    have hmem : ((DirectSum.decompose 𝒜 a n : A) - (DirectSum.decompose 𝒜 b n : A)) ∈
        I.toIdeal := by
      have h := (Submodule.IsHomogeneous.mem_iff 𝒜 I.isHomogeneous).mp hab' n
      rwa [DirectSum.decompose_sub, DirectSum.sub_apply, Submodule.coe_sub] at h
    have key : Ideal.Quotient.mk I.toIdeal (DirectSum.decompose 𝒜 a n : A) =
        Ideal.Quotient.mk I.toIdeal (DirectSum.decompose 𝒜 b n : A) := by
      rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact hmem
    rw [quotientDecomposeAux_apply, quotientDecomposeAux_apply]
    exact key)

private lemma quotientDecompose_mk (a : A) :
    quotientDecompose I (Ideal.Quotient.mk I.toIdeal a) =
      quotientDecomposeAux I (DirectSum.decompose 𝒜 a) :=
  rfl

private lemma quotientDecompose_add (x y : A ⧸ I.toIdeal) :
    quotientDecompose I (x + y) = quotientDecompose I x + quotientDecompose I y := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_add, quotientDecompose_mk, quotientDecompose_mk, quotientDecompose_mk,
    DirectSum.decompose_add, map_add]

instance : DirectSum.Decomposition (quotientGrading I) where
  decompose' := quotientDecompose I
  left_inv x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [quotientDecompose_mk, quotientDecomposeAux_coe]
    congr 1
    exact (DirectSum.decompose 𝒜).symm_apply_apply a
  right_inv x := by
    induction x using DirectSum.induction_on with
    | zero =>
      have h0 : (0 : A ⧸ I.toIdeal) = Ideal.Quotient.mk I.toIdeal 0 := by simp
      rw [map_zero, h0, quotientDecompose_mk]
      simp
    | of n a =>
      obtain ⟨b, hb, hba⟩ := Submodule.mem_map.mp a.2
      have h1 : (DirectSum.coeAddMonoidHom (quotientGrading I)) (DirectSum.of _ n a) =
          Ideal.Quotient.mk I.toIdeal b := by
        rw [DirectSum.coeAddMonoidHom_of, ← hba]; rfl
      rw [h1, quotientDecompose_mk, DirectSum.decompose_of_mem 𝒜 hb,
        quotientDecomposeAux_of]
      exact congrArg (DirectSum.of _ n) (Subtype.ext hba)
    | add x y hx hy =>
      rw [map_add, quotientDecompose_add, hx, hy]

/-- The quotient of a graded algebra by a homogeneous ideal is a graded algebra. -/
instance quotientGradingGradedAlgebra : GradedAlgebra (quotientGrading I) := ⟨⟩

/-- The decomposition of the class of a homogeneous element is the evident single
component. -/
lemma decompose_quotientGrading_mk {n : ι} {a : A} (ha : a ∈ 𝒜 n) :
    DirectSum.decompose (quotientGrading I) (Ideal.Quotient.mk I.toIdeal a) =
      DirectSum.of _ n ⟨Ideal.Quotient.mk I.toIdeal a, mk_mem_quotientGrading I ha⟩ := by
  have h : DirectSum.decompose (quotientGrading I) (Ideal.Quotient.mk I.toIdeal a) =
      quotientDecompose I (Ideal.Quotient.mk I.toIdeal a) := rfl
  rw [h, quotientDecompose_mk, DirectSum.decompose_of_mem 𝒜 ha, quotientDecomposeAux_of]
  rfl

/-- The canonical ring homomorphism from `R` to the degree-zero part of the quotient
grading. -/
def algebraMapGradeZero : R →+* quotientGrading I 0 where
  toFun r := ⟨algebraMap R (A ⧸ I.toIdeal) r,
    Submodule.mem_map.mpr ⟨algebraMap R A r, SetLike.algebraMap_mem_graded 𝒜 r,
      (Ideal.Quotient.mkₐ R I.toIdeal).commutes r⟩⟩
  map_one' := Subtype.ext (map_one (algebraMap R (A ⧸ I.toIdeal)))
  map_mul' a b := Subtype.ext (map_mul (algebraMap R (A ⧸ I.toIdeal)) a b)
  map_zero' := Subtype.ext (map_zero (algebraMap R (A ⧸ I.toIdeal)))
  map_add' a b := Subtype.ext (map_add (algebraMap R (A ⧸ I.toIdeal)) a b)

@[simp]
lemma coe_algebraMapGradeZero (r : R) :
    (algebraMapGradeZero I r : A ⧸ I.toIdeal) = algebraMap R (A ⧸ I.toIdeal) r :=
  rfl

section MvPolynomial

variable {σ : Type*}

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every degree-zero class in a homogeneous quotient of a polynomial ring is represented by a
base coefficient. -/
lemma algebraMapGradeZero_surjective_mvPolynomial
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R)) :
    Function.Surjective (algebraMapGradeZero J) := by
  rintro ⟨x, hx⟩
  obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp hx
  have hp0 : p.totalDegree = 0 :=
    (MvPolynomial.totalDegree_zero_iff_isHomogeneous σ).mpr
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hp)
  have hpC : p = MvPolynomial.C (MvPolynomial.coeff 0 p) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hp0
  refine ⟨MvPolynomial.coeff 0 p, Subtype.ext ?_⟩
  change algebraMap R (MvPolynomial σ R ⧸ J.toIdeal) (MvPolynomial.coeff 0 p) = x
  rw [← hpx]
  change algebraMap R (MvPolynomial σ R ⧸ J.toIdeal) (MvPolynomial.coeff 0 p) =
    Ideal.Quotient.mk J.toIdeal p
  calc
    _ = Ideal.Quotient.mk J.toIdeal (MvPolynomial.C (MvPolynomial.coeff 0 p)) := by
      change Ideal.Quotient.mk J.toIdeal
          (algebraMap R (MvPolynomial σ R) (MvPolynomial.coeff 0 p)) = _
      rw [MvPolynomial.algebraMap_eq]
    _ = Ideal.Quotient.mk J.toIdeal p := congrArg (Ideal.Quotient.mk J.toIdeal) hpC.symm

end MvPolynomial

instance : IsScalarTower R (↥(quotientGrading I 0)) (A ⧸ I.toIdeal) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The quotient map `A → A ⧸ I` as a graded ring homomorphism onto the quotient
grading. -/
def quotientGradingHom : 𝒜 →+*ᵍ quotientGrading I where
  toRingHom := Ideal.Quotient.mk I.toIdeal
  map_mem := mk_mem_quotientGrading I

lemma quotientGradingHom_surjective :
    Function.Surjective (quotientGradingHom I) :=
  Ideal.Quotient.mk_surjective

@[simp]
lemma quotientGradingHom_apply (a : A) :
    quotientGradingHom I a = Ideal.Quotient.mk I.toIdeal a :=
  rfl

/-- Componentwise description of the quotient decomposition on classes. -/
lemma decompose_quotientGrading_mk_apply (a : A) (n : ι) :
    (DirectSum.decompose (quotientGrading I) (Ideal.Quotient.mk I.toIdeal a) n :
        A ⧸ I.toIdeal) =
      Ideal.Quotient.mk I.toIdeal (DirectSum.decompose 𝒜 a n) :=
  rfl

section Irrelevant

variable [PartialOrder ι] [CanonicallyOrderedAdd ι]

/-- The irrelevant ideal of the quotient grading is contained in the image of the
irrelevant ideal — the hypothesis of `Proj.map` for the quotient map. -/
lemma quotientGradingHom_irrelevant_le :
    HomogeneousIdeal.irrelevant (quotientGrading I) ≤
      HomogeneousIdeal.map (quotientGradingHom I) (HomogeneousIdeal.irrelevant 𝒜) := by
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
    decompose_quotientGrading_mk_apply] at hx
  have hmem : a - (DirectSum.decompose 𝒜 a 0 : A) ∈ HomogeneousIdeal.irrelevant 𝒜 := by
    rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
      DirectSum.decompose_sub]
    simp [DirectSum.sub_apply, DirectSum.decompose_coe, DirectSum.of_eq_same]
  have hval : Ideal.Quotient.mk I.toIdeal a =
      quotientGradingHom I (a - (DirectSum.decompose 𝒜 a 0 : A)) := by
    rw [quotientGradingHom_apply, map_sub, hx, sub_zero]
  rw [hval]
  exact Ideal.mem_map_of_mem _ hmem

end Irrelevant

section Map

variable {τ B S : Type*} [CommRing S] [CommRing B] [Algebra S B]
  {ℬ : ι → Submodule S B} [GradedAlgebra ℬ]

/-- Functoriality of the quotient grading: a graded ring homomorphism mapping `I`
into `J` descends to a graded homomorphism of the quotient gradings. -/
def quotientGradingMap (φ : GradedRingHom 𝒜 ℬ) (I : HomogeneousIdeal 𝒜)
    (J : HomogeneousIdeal ℬ) (h : I.toIdeal ≤ J.toIdeal.comap φ.toRingHom) :
    GradedRingHom (quotientGrading I) (quotientGrading J) where
  toRingHom := Ideal.quotientMap J.toIdeal φ.toRingHom h
  map_mem {i x} hx := by
    obtain ⟨a, ha, rfl⟩ := hx
    refine ⟨φ a, φ.map_mem ha, ?_⟩
    exact Ideal.quotientMap_mk.symm

@[simp]
lemma quotientGradingMap_mk (φ : GradedRingHom 𝒜 ℬ) (I : HomogeneousIdeal 𝒜)
    (J : HomogeneousIdeal ℬ) (h : I.toIdeal ≤ J.toIdeal.comap φ.toRingHom) (a : A) :
    quotientGradingMap φ I J h (Ideal.Quotient.mk I.toIdeal a) =
      Ideal.Quotient.mk J.toIdeal (φ a) :=
  Ideal.quotientMap_mk (H := h)

end Map

end HomogeneousIdeal
