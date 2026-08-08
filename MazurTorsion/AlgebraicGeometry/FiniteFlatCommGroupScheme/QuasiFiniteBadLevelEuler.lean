/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.ConstantFlatGlobalSections
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.MultiplicativeFlatGlobalSections
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.QuasiFiniteFppfQuotientEuler

/-!
# Euler bounds for the two bad-level elementary factors

The bad-level constant-flat and multiplicative-flat models have checked trivial integral global
sections.  This file inserts those actual `p^0` certificates into the quasi-finite Euler bound.

`FppfExtensionPresentation K G Q` is a narrow geometric interface for an extension with
specified kernel `K` and quotient `Q`: its kernel field is an isomorphism from `K` to the actual
scheme-theoretic kernel of the supplied fppf projection.  Thus the specializations below do not
assume an equality between an unrelated kernel model and a bad-level factor.  The two factors
are definitionally the kernel and quotient of the extension data.

When both endpoint groups have only the identity integral point, exactness at the middle
represented-point term also proves that `G(Spec Z)` is trivial.  Consequently all three `H^0`
terms disappear from the numerical inequality.  The only remaining cohomological inputs are
certified `H^1` data for the two bad-level factors.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme

open FiniteFlatCommGroupScheme

universe u

variable {S : Scheme.{u}}

/-- An actual fppf extension `K ⟶ G ⟶ Q` with the kernel object specified definitionally.
The geometric kernel isomorphism is precisely the input required by `KernelPresentation`; no
factor comparison is added later by the Euler consumer. -/
structure FppfExtensionPresentation
    (K G Q : QuasiFiniteFlatCommGroupScheme S) where
  /-- The quotient projection. -/
  project : G ⟶ Q
  /-- Flatness of the projection. -/
  project_flat : Flat (hom project)
  /-- Surjectivity of the projection on underlying topological spaces. -/
  project_surjective : Surjective (hom project)
  /-- Local finite presentation of the projection. -/
  project_lfp : LocallyOfFinitePresentation (hom project)
  /-- Identification of the specified object with the actual scheme-theoretic kernel. -/
  kernelIso : K.obj ≅ CommGroupScheme.kernel project.hom

namespace FppfExtensionPresentation

variable {K G Q : QuasiFiniteFlatCommGroupScheme S}

/-- Forget that the kernel and quotient were externally specified. -/
def toFppfQuotientPresentation (D : FppfExtensionPresentation K G Q) :
    FppfQuotientPresentation G where
  quotient := Q
  project := D.project
  project_flat := D.project_flat
  project_surjective := D.project_surjective
  project_lfp := D.project_lfp
  kernelPresentation :=
    { kernel := K
      kernelIso := D.kernelIso }

@[simp]
theorem toFppfQuotientPresentation_quotient
    (D : FppfExtensionPresentation K G Q) :
    D.toFppfQuotientPresentation.quotient = Q :=
  rfl

@[simp]
theorem toFppfQuotientPresentation_project
    (D : FppfExtensionPresentation K G Q) :
    D.toFppfQuotientPresentation.project = D.project :=
  rfl

@[simp]
theorem toFppfQuotientPresentation_kernel
    (D : FppfExtensionPresentation K G Q) :
    D.toFppfQuotientPresentation.kernelPresentation.kernel = K :=
  rfl

/-- If the specified kernel and quotient have only identity global sections, then so does the
middle group scheme. -/
theorem middleBasePoint_eq_one (D : FppfExtensionPresentation K G Q)
    (hK : ∀ x : BasePoint K, x = 1)
    (hQ : ∀ x : BasePoint Q, x = 1)
    (x : BasePoint G) : x = 1 := by
  have hxq : mapPoint D.project (baseObject S) x = 1 := hQ _
  obtain ⟨y, hy⟩ :=
    (D.toFppfQuotientPresentation.project_point_eq_one_iff
      (baseObject S) x).mp hxq
  calc
    x = mapPoint D.toFppfQuotientPresentation.kernelPresentation.inclusion
        (baseObject S) y := hy.symm
    _ = mapPoint D.toFppfQuotientPresentation.kernelPresentation.inclusion
        (baseObject S) 1 := congrArg _ (hK y)
    _ = 1 := map_one _

/-- The middle represented-point group of such an extension is equivalent to the trivial
group. -/
noncomputable def middleBasePointMulEquivUnit
    (D : FppfExtensionPresentation K G Q)
    (hK : ∀ x : BasePoint K, x = 1)
    (hQ : ∀ x : BasePoint Q, x = 1) :
    BasePoint G ≃* Unit where
  toFun _ := Unit.unit
  invFun _ := 1
  left_inv x := (D.middleBasePoint_eq_one hK hQ x).symm
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The middle represented-point group has the honest cardinal certificate `p^0`. -/
noncomputable def middleBasePointCertifiedData (p : ℕ)
    (D : FppfExtensionPresentation K G Q)
    (hK : ∀ x : BasePoint K, x = 1)
    (hQ : ∀ x : BasePoint Q, x = 1) :
    FinitePGroup.CertifiedData p (BasePoint G) where
  finite := Finite.of_equiv Unit
    (D.middleBasePointMulEquivUnit hK hQ).symm.toEquiv
  length := 0
  card_eq := by
    rw [Nat.card_congr (D.middleBasePointMulEquivUnit hK hQ).toEquiv]
    simp

@[simp]
theorem middleBasePointCertifiedData_length (p : ℕ)
    (D : FppfExtensionPresentation K G Q)
    (hK : ∀ x : BasePoint K, x = 1)
    (hQ : ∀ x : BasePoint Q, x = 1) :
    (D.middleBasePointCertifiedData p hK hQ).length = 0 :=
  rfl

end FppfExtensionPresentation

namespace FppfLowDegreeExactSequence

variable {coeffPrime level : ℕ} [NeZero coeffPrime]
variable {G : QuasiFiniteFlatCommGroupScheme (Spec (.of ℤ))}

/-- Euler bound when the kernel is Mazur's actual constant-flat factor and the quotient is the
actual multiplicative-flat factor.  All represented `H^0` certificates are discharged as
`coeffPrime^0`. -/
theorem fppfHOne_natCard_le_pow_of_constantFlatKernel_muFlatQuotient
    (hprime : coeffPrime.Prime) (hprime2 : coeffPrime ≠ 2)
    (hlevel : level.Prime) (datum : MuFlatDatum coeffPrime level)
    (D : FppfExtensionPresentation
      (mazurConstantFlat coeffPrime level) G (muFlat coeffPrime level datum))
    (kernelHOneData : FinitePGroup.CertifiedData coeffPrime
      (mazurConstantFlat coeffPrime level).FppfHOne.{0})
    (quotientHOneData : FinitePGroup.CertifiedData coeffPrime
      (muFlat coeffPrime level datum).FppfHOne.{0})
    (bound : ℕ)
    (hbound : kernelHOneData.length + quotientHOneData.length ≤ bound) :
    Nat.card G.FppfHOne.{0} ≤ coeffPrime ^ bound := by
  have hodd : Odd coeffPrime := hprime.odd_of_ne_two hprime2
  have hconstant : ∀ x : BasePoint (mazurConstantFlat coeffPrime level), x = 1 := by
    intro x
    exact constantFlatBasePoint_eq_one ℤ (Multiplicative (ZMod coeffPrime))
      (level : ℤ) (by
        rw [Int.ofNat_isUnit]
        exact hlevel.not_isUnit) x
  have hmu : ∀ x : BasePoint (muFlat coeffPrime level datum), x = 1 :=
    fun x ↦ muFlatBasePoint_eq_one coeffPrime level datum hodd x
  have hconstantLength :
      (mazurConstantFlatBasePointCertifiedDataOfPrimeLevel
        coeffPrime level hlevel).length = 0 := rfl
  have hmuLength :
      (muFlatBasePointCertifiedDataOfOdd
        coeffPrime level datum hodd).length = 0 := rfl
  apply fppfHOne_natCard_le_pow_ofFppfQuotientPresentation
    D.toFppfQuotientPresentation
    (mazurConstantFlatBasePointCertifiedDataOfPrimeLevel
      coeffPrime level hlevel)
    (D.middleBasePointCertifiedData coeffPrime hconstant hmu)
    (muFlatBasePointCertifiedDataOfOdd coeffPrime level datum hodd)
    kernelHOneData quotientHOneData hprime bound
  simpa [hconstantLength, hmuLength] using hbound

/-- Euler bound in the reverse order: the actual multiplicative-flat factor is the kernel and
Mazur's actual constant-flat factor is the quotient.  Again all three represented `H^0` terms
are checked `coeffPrime^0` groups. -/
theorem fppfHOne_natCard_le_pow_of_muFlatKernel_constantFlatQuotient
    (hprime : coeffPrime.Prime) (hprime2 : coeffPrime ≠ 2)
    (hlevel : level.Prime) (datum : MuFlatDatum coeffPrime level)
    (D : FppfExtensionPresentation
      (muFlat coeffPrime level datum) G (mazurConstantFlat coeffPrime level))
    (kernelHOneData : FinitePGroup.CertifiedData coeffPrime
      (muFlat coeffPrime level datum).FppfHOne.{0})
    (quotientHOneData : FinitePGroup.CertifiedData coeffPrime
      (mazurConstantFlat coeffPrime level).FppfHOne.{0})
    (bound : ℕ)
    (hbound : kernelHOneData.length + quotientHOneData.length ≤ bound) :
    Nat.card G.FppfHOne.{0} ≤ coeffPrime ^ bound := by
  have hodd : Odd coeffPrime := hprime.odd_of_ne_two hprime2
  have hmu : ∀ x : BasePoint (muFlat coeffPrime level datum), x = 1 :=
    fun x ↦ muFlatBasePoint_eq_one coeffPrime level datum hodd x
  have hconstant : ∀ x : BasePoint (mazurConstantFlat coeffPrime level), x = 1 := by
    intro x
    exact constantFlatBasePoint_eq_one ℤ (Multiplicative (ZMod coeffPrime))
      (level : ℤ) (by
        rw [Int.ofNat_isUnit]
        exact hlevel.not_isUnit) x
  have hconstantLength :
      (mazurConstantFlatBasePointCertifiedDataOfPrimeLevel
        coeffPrime level hlevel).length = 0 := rfl
  have hmuLength :
      (muFlatBasePointCertifiedDataOfOdd
        coeffPrime level datum hodd).length = 0 := rfl
  apply fppfHOne_natCard_le_pow_ofFppfQuotientPresentation
    D.toFppfQuotientPresentation
    (muFlatBasePointCertifiedDataOfOdd coeffPrime level datum hodd)
    (D.middleBasePointCertifiedData coeffPrime hmu hconstant)
    (mazurConstantFlatBasePointCertifiedDataOfPrimeLevel
      coeffPrime level hlevel)
    kernelHOneData quotientHOneData hprime bound
  simpa [hconstantLength, hmuLength] using hbound

end FppfLowDegreeExactSequence

end AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme
