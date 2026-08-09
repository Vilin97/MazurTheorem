/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveDivisorPicardDescent
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Degree

/-!
# The absolute degree-zero Picard subgroup

This is a downstream consumer of the divisor-class/Picard interface for
`MT-TC-D1-PICARD-FUNCTOR`. Given a product formula and a divisor-class/Picard equivalence, it
transports Tau Ceti's weighted degree-zero divisor classes to an absolute `Pic⁰` subgroup of the
scheme Picard group.

The final adapter consumes the explicit-inverse curve-descent equivalence directly, so this D1
precursor does not require the stronger dictionary comparing every invertible sheaf with a
Picard unit.

No relative Picard functor or representability claim is made here. The generic weighted
construction retains the product formula as an explicit input; the smooth proper curve
specialization discharges it with Tau Ceti's checked theorem.
-/

namespace MazurTorsion.AlgebraicGeometry

universe u v

open _root_.AlgebraicGeometry
open TauCeti.AlgebraicGeometry

namespace PicardGroup

variable {X : Scheme.{u}}
variable {Y : Type*} {G : Type v} [AddCommGroup G]

/-- The image in the scheme Picard group of the weighted degree-zero divisor
classes under a supplied additive homomorphism.

Unlike `degreeZero`, this construction neither assumes nor asserts that every
Picard class is represented by a divisor.  In particular, it is an image
subgroup, not a representability statement about a relative Picard functor. -/
noncomputable def degreeZeroImage
    (S : WeilDivisor.OrderSystem Y G)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (φ : S.ClassGroup →+ PicardGroup X) :
    AddSubgroup (PicardGroup X) :=
  (S.picZero w h).map φ

/-- Restrict a divisor-class-to-Picard homomorphism to its actual
weighted-degree-zero image. -/
noncomputable def picZeroToDegreeZeroImage
    (S : WeilDivisor.OrderSystem Y G)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (φ : S.ClassGroup →+ PicardGroup X) :
    S.picZero w h →+ degreeZeroImage S w h φ where
  toFun c := ⟨φ c.1, ⟨c.1, c.2, rfl⟩⟩
  map_zero' := Subtype.ext (map_zero φ)
  map_add' c d := Subtype.ext (map_add φ c.1 d.1)

/-- The restricted map has the supplied class-to-Picard homomorphism as its
underlying Picard-valued function. -/
@[simp]
lemma coe_picZeroToDegreeZeroImage
    (S : WeilDivisor.OrderSystem Y G)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (φ : S.ClassGroup →+ PicardGroup X) (c : S.picZero w h) :
    (picZeroToDegreeZeroImage S w h φ c : PicardGroup X) = φ c.1 :=
  rfl

/-- The degree-zero subgroup of the scheme Picard group transported from divisor classes. -/
noncomputable def degreeZero
    (S : WeilDivisor.OrderSystem Y G)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (e : DivisorPicard.ClassEquivalence S X) :
    AddSubgroup (PicardGroup X) :=
  (S.picZero w h).map e.toAddMonoidHom

/-- The divisor-class/Picard equivalence restricts to the degree-zero subgroups. -/
noncomputable def picZeroEquiv
    (S : WeilDivisor.OrderSystem Y G)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (e : DivisorPicard.ClassEquivalence S X) :
    S.picZero w h ≃+ degreeZero S w h e :=
  e.addSubgroupMap (S.picZero w h)

/-- Membership in transported `Pic⁰` can be tested after applying the inverse equivalence. -/
@[simp]
lemma mem_degreeZero_iff
    (S : WeilDivisor.OrderSystem Y G)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (e : DivisorPicard.ClassEquivalence S X)
    (p : PicardGroup X) :
    p ∈ degreeZero S w h e ↔ e.symm p ∈ S.picZero w h := by
  rw [degreeZero, AddSubgroup.mem_map_equiv]

/-- A divisor class lands in absolute `Pic⁰` exactly when its weighted degree is zero. -/
lemma divisorClass_mem_degreeZero_iff
    (S : WeilDivisor.OrderSystem Y G)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (e : DivisorPicard.ClassEquivalence S X)
    (D : WeilDivisor Y) :
    e (S.divisorClass D) ∈ degreeZero S w h e ↔
      WeilDivisor.weightedDegree w D = 0 := by
  rw [mem_degreeZero_iff, e.symm_apply_apply, S.divisorClass_mem_picZero]

end PicardGroup

namespace DivisorPicard.Dictionary

variable {X : Scheme.{u}}
variable {Y : Type*} {G : Type v} [AddCommGroup G]
variable {S : WeilDivisor.OrderSystem Y G}

/-- The weighted degree-zero Picard subgroup attached to an exact divisor-line-bundle
dictionary. This generic construction retains the weight and product formula as explicit
inputs; `degreeZero` below is the canonical proper-curve specialization. -/
noncomputable def weightedDegreeZero
    (d : DivisorPicard.Dictionary S X)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w) :
    AddSubgroup (PicardGroup X) :=
  PicardGroup.degreeZero S w h d.classEquivalence

/-- The canonical degree-zero Picard subgroup of a smooth proper integral curve. The geometric
product formula supplies the weighted-degree hypothesis automatically, so no abstract premise
remains in this named Challenge consumer. -/
noncomputable def degreeZero
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (π : X ⟶ Spec (.of K)) [IsProper π] [SmoothOfRelativeDimension 1 π]
    (d : DivisorPicard.Dictionary
      (TauCeti.AlgebraicGeometry.SchemeWeilDivisor.orderSystem X) X) :
    AddSubgroup (PicardGroup X) :=
  d.weightedDegreeZero (fun x ↦ (π.residueDegree x.1 : ℤ))
    (TauCeti.AlgebraicGeometry.SchemeWeilDivisor.orderSystem_isWeightedDegreeZero K X π)

/-- Explicitly named alias for the proper-curve specialization, retained for downstream code
that needs to distinguish it from `PicardGroup.degreeZero`. -/
noncomputable def properCurveDegreeZero
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (π : X ⟶ Spec (.of K)) [IsProper π] [SmoothOfRelativeDimension 1 π]
    (d : DivisorPicard.Dictionary
      (TauCeti.AlgebraicGeometry.SchemeWeilDivisor.orderSystem X) X) :
    AddSubgroup (PicardGroup X) :=
  d.degreeZero K X π

/-- An exact dictionary identifies divisor `Pic⁰` with its absolute scheme-Picard image. -/
noncomputable def picZeroEquiv
    (d : DivisorPicard.Dictionary S X)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w) :
    S.picZero w h ≃+ d.weightedDegreeZero w h :=
  PicardGroup.picZeroEquiv S w h d.classEquivalence

/-- A chosen Tau Ceti invertible-sheaf representative of an absolute degree-zero Picard class.
This consumes the full Picard comparison forced by the exact divisor dictionary. -/
noncomputable def degreeZeroRepresentative
    (d : DivisorPicard.Dictionary S X)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (p : d.weightedDegreeZero w h) : InvertibleSheaf X :=
  d.picardComparison.representative (Additive.toMul p.1)

/-- The chosen degree-zero line bundle represents the underlying Picard class. -/
@[simp]
lemma degreeZeroRepresentative_toPic
    (d : DivisorPicard.Dictionary S X)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (p : d.weightedDegreeZero w h) :
    Additive.ofMul
      (d.picardComparison.toPic (d.degreeZeroRepresentative w h p)) = p.1 := by
  change Additive.ofMul
    (d.picardComparison.toPic
      (d.picardComparison.representative (Additive.toMul p.1))) = p.1
  rw [PicardComparison.toPic_representative]
  rfl

/-- The Picard class of the chosen representative remains in the transported degree-zero
subgroup. -/
lemma degreeZeroRepresentative_mem
    (d : DivisorPicard.Dictionary S X)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (p : d.weightedDegreeZero w h) :
    Additive.ofMul
        (d.picardComparison.toPic (d.degreeZeroRepresentative w h p)) ∈
      d.weightedDegreeZero w h := by
  rw [d.degreeZeroRepresentative_toPic w h p]
  exact p.property

/-- Under an exact dictionary, a divisor represents an absolute degree-zero Picard class
exactly when its weighted degree vanishes. -/
lemma divisorToPic_mem_degreeZero_iff
    (d : DivisorPicard.Dictionary S X)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (D : WeilDivisor Y) :
    d.divisorToPic D ∈ d.weightedDegreeZero w h ↔
      WeilDivisor.weightedDegree w D = 0 := by
  rw [← d.classEquivalence_divisorClass D]
  exact PicardGroup.divisorClass_mem_degreeZero_iff S w h d.classEquivalence D

end DivisorPicard.Dictionary

namespace CurveDivisorDescent.DivisorCocycleSystem.ExplicitInverse

open TopologicalSpace
open TauCeti.AlgebraicGeometry.WeilDivisor

/-- Descend the divisor-to-Picard map supplied by an exact global principal
boundary to divisor classes.  This construction needs principal triviality,
but no surjectivity onto the full scheme Picard group. -/
noncomputable def classToPicOfGlobalPrincipalBoundary
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : WeilDivisor.OrderSystem
      (TauCeti.AlgebraicGeometry.CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : CurveDivisorDescent.DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : CurveDivisorDescent.EffectiveDivisorCocycleSystem
      X U hnonempty hcover hU h C)
    (hadd : CurveDivisorDescent.DescendedTensorAdditive
      X U hnonempty hcover hU h C heffective)
    (b : GlobalPrincipalBoundary X U hnonempty hcover hU h S C heffective) :
    S.ClassGroup →+ PicardGroup X :=
  DivisorPicard.classToPic S
    (divisorToPicOfGlobalPrincipalBoundary
      X U hnonempty hcover hU h S C heffective hadd b)
    (divisorToPicOfGlobalPrincipalBoundary_principalTrivial
      X U hnonempty hcover hU h S C heffective hadd b)

/-- On a divisor representative, the descended class map is the actual
line-bundle Picard class constructed from the global principal boundary. -/
@[simp]
lemma classToPicOfGlobalPrincipalBoundary_divisorClass
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : WeilDivisor.OrderSystem
      (TauCeti.AlgebraicGeometry.CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : CurveDivisorDescent.DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : CurveDivisorDescent.EffectiveDivisorCocycleSystem
      X U hnonempty hcover hU h C)
    (hadd : CurveDivisorDescent.DescendedTensorAdditive
      X U hnonempty hcover hU h C heffective)
    (b : GlobalPrincipalBoundary X U hnonempty hcover hU h S C heffective)
    (D : WeilDivisor (TauCeti.AlgebraicGeometry.CodimensionOnePoint X)) :
    classToPicOfGlobalPrincipalBoundary
        X U hnonempty hcover hU h S C heffective hadd b (S.divisorClass D) =
      divisorToPicOfGlobalPrincipalBoundary
        X U hnonempty hcover hU h S C heffective hadd b D :=
  DivisorPicard.classToPic_divisorClass S
    (divisorToPicOfGlobalPrincipalBoundary
      X U hnonempty hcover hU h S C heffective hadd b)
    (divisorToPicOfGlobalPrincipalBoundary_principalTrivial
      X U hnonempty hcover hU h S C heffective hadd b) D

/-- The weighted degree-zero divisor-class image supplied by the global
principal boundary, without a Picard-surjectivity hypothesis. -/
noncomputable def degreeZeroImageOfGlobalPrincipalBoundary
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : WeilDivisor.OrderSystem
      (TauCeti.AlgebraicGeometry.CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : CurveDivisorDescent.DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : CurveDivisorDescent.EffectiveDivisorCocycleSystem
      X U hnonempty hcover hU h C)
    (hadd : CurveDivisorDescent.DescendedTensorAdditive
      X U hnonempty hcover hU h C heffective)
    (b : GlobalPrincipalBoundary X U hnonempty hcover hU h S C heffective)
    (w : TauCeti.AlgebraicGeometry.CodimensionOnePoint X → ℤ)
    (hdegree : S.IsWeightedDegreeZero w) : AddSubgroup (PicardGroup X) :=
  PicardGroup.degreeZeroImage S w hdegree
    (classToPicOfGlobalPrincipalBoundary
      X U hnonempty hcover hU h S C heffective hadd b)

/-- The explicit-inverse curve descent route supplies the absolute degree-zero Picard subgroup
without first constructing the stronger all-invertible-sheaves dictionary. This is a direct
`MT-TC-D1` consumer of the strongest A3 divisor-class/Picard equivalence. -/
noncomputable def degreeZero
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : WeilDivisor.OrderSystem
      (TauCeti.AlgebraicGeometry.CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : CurveDivisorDescent.DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : CurveDivisorDescent.EffectiveDivisorCocycleSystem
      X U hnonempty hcover hU h C)
    (hadd : CurveDivisorDescent.DescendedTensorAdditive
      X U hnonempty hcover hU h C heffective)
    (hzero : _root_.MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.DescendedZeroTrivial
      X U hnonempty hcover hU h C heffective)
    (hker : DivisorPicard.HasPrincipalKernel S
      (divisorToPic X U hnonempty hcover hU h C heffective hadd hzero))
    (hsurjective : Function.Surjective
      (divisorToPic X U hnonempty hcover hU h C heffective hadd hzero))
    (w : TauCeti.AlgebraicGeometry.CodimensionOnePoint X → ℤ)
    (hdegree : S.IsWeightedDegreeZero w) : AddSubgroup (PicardGroup X) :=
  PicardGroup.degreeZero S w hdegree
    (classEquivPicard X U hnonempty hcover hU h S C heffective hadd hzero
      hker hsurjective)

/-- A divisor lands in the explicit-inverse absolute degree-zero subgroup exactly when its
weighted degree vanishes. -/
lemma divisorToPic_mem_degreeZero_iff
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : WeilDivisor.OrderSystem
      (TauCeti.AlgebraicGeometry.CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : CurveDivisorDescent.DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : CurveDivisorDescent.EffectiveDivisorCocycleSystem
      X U hnonempty hcover hU h C)
    (hadd : CurveDivisorDescent.DescendedTensorAdditive
      X U hnonempty hcover hU h C heffective)
    (hzero : _root_.MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.DescendedZeroTrivial
      X U hnonempty hcover hU h C heffective)
    (hker : DivisorPicard.HasPrincipalKernel S
      (divisorToPic X U hnonempty hcover hU h C heffective hadd hzero))
    (hsurjective : Function.Surjective
      (divisorToPic X U hnonempty hcover hU h C heffective hadd hzero))
    (w : TauCeti.AlgebraicGeometry.CodimensionOnePoint X → ℤ)
    (hdegree : S.IsWeightedDegreeZero w)
    (D : WeilDivisor (TauCeti.AlgebraicGeometry.CodimensionOnePoint X)) :
    divisorToPic X U hnonempty hcover hU h C heffective hadd hzero D ∈
        degreeZero X U hnonempty hcover hU h S C heffective hadd hzero
          hker hsurjective w hdegree ↔
      WeilDivisor.weightedDegree w D = 0 := by
  rw [← classEquivPicard_divisorClass X U hnonempty hcover hU h S C
    heffective hadd hzero hker hsurjective D]
  exact PicardGroup.divisorClass_mem_degreeZero_iff S w hdegree
    (classEquivPicard X U hnonempty hcover hU h S C heffective hadd hzero
      hker hsurjective) D

end CurveDivisorDescent.DivisorCocycleSystem.ExplicitInverse

end MazurTorsion.AlgebraicGeometry
