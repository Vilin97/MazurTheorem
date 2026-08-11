/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/

import MazurTorsion.NumberTheory.XOneEighteenDyadicKernelSeparation
import MazurTorsion.NumberTheory.XOneEighteenGlobalKernelEquivalence
import MazurTorsion.NumberTheory.XOneEighteenTwoDivisionClassNumberOne
import MazurTorsion.NumberTheory.XOneEighteenDyadicValuationCertificate
import MazurTorsion.NumberTheory.XOneEighteenKernelGeneratorSupport
import MazurTorsion.NumberTheory.XOneEighteenFinalRankZero

/-!
# Unconditional completion of the `X₁(18)` two-descent

The global dyadic norm kernel has exactly the sixteen explicitly displayed
representatives.  The selected dyadic factor admits only their identity
representative in the local descent image.  Transporting the representatives
back through the checked equivalence with the generic minimal descent algebra
therefore makes the global `x - T` image trivial.

The rank-zero, finite-reduction, and Kubert consumers then give both the full
rational-point classification required by `Challenge.XOneEighteenNoncusp` and
the genuine exact-order-eighteen exclusion.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.XOneEighteenDescent

noncomputable section

open MazurTorsion.XOneEighteenDyadicCompletionBridge
open MazurTorsion.XOneEighteenDyadicKernelSeparation
open MazurTorsion.XOneEighteenDyadicValuationCertificate
open MazurTorsion.XOneEighteenGlobalKernelEquivalence
open MazurTorsion.XOneEighteenGlobalSelmerBridge
open MazurTorsion.XOneEighteenKernelGeneratorSupport
open MazurTorsion.XOneEighteenMinimalTwoDescentModel
open MazurTorsion.XOneEighteenFinalRankZero
open MazurTorsion.XOneEighteenSelmerSieve
open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionClassNumberOne

private abbrev concreteKernelSupportCertificate :
    KernelGeneratorSupportCertificate :=
  kernelGeneratorSupportCertificate

/-- The checked equivalence between the generic minimal-model norm kernel
and the explicit dyadically supported relative-norm kernel. -/
private def descentDyadicNormKernelEquiv :
    descentDyadicNormKernel ≃* fullDyadicRelativeNorm.ker :=
  MulEquiv.ofBijective descentDyadicNormKernelHom
    descentDyadicNormKernelHom_bijective

/-- The sixteen explicit relative-norm-kernel representatives, transported
back to the generic squareclass algebra of the minimal descent model. -/
private def minimalKernelRepresentative (mask : Fin 16) :
    descentDyadicNormKernel :=
  descentDyadicNormKernelEquiv.symm
    (dyadicKernelRepresentative concreteKernelSupportCertificate mask)

private theorem descentDyadicNormKernelHom_minimalKernelRepresentative
    (mask : Fin 16) :
    descentDyadicNormKernelHom (minimalKernelRepresentative mask) =
      dyadicKernelRepresentative concreteKernelSupportCertificate mask := by
  change descentDyadicNormKernelEquiv
      (descentDyadicNormKernelEquiv.symm
        (dyadicKernelRepresentative concreteKernelSupportCertificate mask)) =
    dyadicKernelRepresentative concreteKernelSupportCertificate mask
  exact descentDyadicNormKernelEquiv.apply_symm_apply _

/-- Under the explicit squareclass equivalence, the transported generic
representative is the corresponding masked product. -/
private theorem minimalKernelRepresentative_squareclass (mask : Fin 16) :
    minimalDescentSquareclassEquiv
        (minimalKernelRepresentative mask : minimalDescentCurve.toAffine.M) =
      kernelRepresentative mask := by
  have h := congrArg
    (fun z : fullDyadicRelativeNorm.ker ↦
      ((z.1 : DyadicSelmerM) : Units.modPow M 2))
    (descentDyadicNormKernelHom_minimalKernelRepresentative mask)
  simpa only [descentDyadicNormKernelHom_coe,
    dyadicKernelRepresentative] using h

/-- The transported representatives exhaust the generic global kernel. -/
private theorem minimalKernelRepresentative_bijective :
    Function.Bijective minimalKernelRepresentative := by
  change Function.Bijective
    (fun mask : Fin 16 ↦ descentDyadicNormKernelEquiv.symm
      (dyadicKernelRepresentative concreteKernelSupportCertificate mask))
  exact descentDyadicNormKernelEquiv.symm.bijective.comp
    (dyadicKernelRepresentative_bijective
      compositumRingOfIntegers_isPrincipal
      dyadicValuationCertificate
      concreteKernelSupportCertificate
      kernelRepresentative_injective)

/-- The transported zero mask is the identity generic squareclass. -/
private theorem minimalKernelRepresentative_zero :
    minimalKernelRepresentative 0 = 1 := by
  apply Subtype.ext
  apply minimalDescentSquareclassEquiv.injective
  change minimalDescentSquareclassEquiv
      (minimalKernelRepresentative 0 : minimalDescentCurve.toAffine.M) =
    minimalDescentSquareclassEquiv (1 : minimalDescentCurve.toAffine.M)
  rw [minimalKernelRepresentative_squareclass,
    kernelRepresentative_zero, map_one]

/-- The kernel of the selected dyadic factor projection on the generic
minimal descent squareclass algebra. -/
private def selectedMinimalLocalKernel :
    Subgroup minimalDescentCurve.toAffine.M :=
  (localRelativeSquareclassProjection.comp
    minimalDescentSquareclassEquiv.toMonoidHom).ker

/-- Every global minimal-model descent value satisfies the selected local
condition. -/
private theorem minimalDescentCurve_range_μ_le_selectedMinimalLocalKernel :
    (minimalDescentCurve.toAffine.μ).range ≤ selectedMinimalLocalKernel := by
  rintro _ ⟨P, rfl⟩
  change localRelativeSquareclassProjection
      (minimalDescentSquareclassEquiv
        (minimalDescentCurve.toAffine.μ P)) = 1
  calc
    localRelativeSquareclassProjection
          (minimalDescentSquareclassEquiv
            (minimalDescentCurve.toAffine.μ P)) =
        localMinimalSquareclassProjection
          (minimalDescentCurve.toAffine.localRes CoefficientCompletion
            (minimalDescentCurve.toAffine.μ P)) := by
      exact (DFunLike.congr_fun
        localMinimalSquareclassProjection_comp_localRes
          (minimalDescentCurve.toAffine.μ P)).symm
    _ = 1 := by
      simpa only [ofAdd_toAdd] using
        localMinimalSquareclassProjection_localRes_μ_eq_one P.toAdd

/-- Among the transported global representatives, only the zero mask lies
in the selected local kernel. -/
private theorem minimalKernelRepresentative_local_exclusion
    (mask : Fin 16)
    (hlocal :
      (minimalKernelRepresentative mask : minimalDescentCurve.toAffine.M) ∈
        selectedMinimalLocalKernel) :
    mask = 0 := by
  apply
    (localRelativeSquareclassProjection_kernelRepresentative_eq_one_iff
      mask).mp
  change localRelativeSquareclassProjection
      (minimalDescentSquareclassEquiv
        (minimalKernelRepresentative mask : minimalDescentCurve.toAffine.M)) =
    1 at hlocal
  simpa only [minimalKernelRepresentative_squareclass] using hlocal

/-- The concrete global and selected-local calculations make the minimal
`x - T` descent image trivial. -/
theorem minimalDescentCurve_range_μ_eq_bot :
    (minimalDescentCurve.toAffine.μ).range = ⊥ := by
  apply subgroup_eq_bot_of_sixteen_representatives
    (T := (minimalDescentCurve.toAffine.μ).range)
    (global := descentDyadicNormKernel)
    (localCondition := selectedMinimalLocalKernel)
    (representative := minimalKernelRepresentative)
  · exact minimalDescentCurve_range_μ_le_descentDyadicNormKernel
  · exact minimalDescentCurve_range_μ_le_selectedMinimalLocalKernel
  · exact minimalKernelRepresentative_bijective.surjective
  · exact minimalKernelRepresentative_zero
  · exact minimalKernelRepresentative_local_exclusion

/-- The order-eighteen genus-two model has no rational point away from its
two cusp abscissas. -/
theorem no_noncuspidal_point
    (x y : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hcurve :
      y ^ 2 =
        MazurTorsion.Kubert.orderEighteenHyperellipticPolynomial x) :
    False :=
  no_noncuspidal_point_of_minimal_range_mu_eq_bot
    minimalDescentCurve_range_μ_eq_bot x y hx0 hx1 hcurve

/-- No elliptic curve over `ℚ` has a rational point of exact additive order
eighteen. -/
theorem rationalPoint_addOrderOf_ne_eighteen
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : E.toAffine.Point) :
    addOrderOf Q ≠ 18 := by
  apply
    MazurTorsion.Kubert.rationalPoint_addOrderOf_ne_eighteen_of_noNoncuspidalPoint
      E Q
  intro x y hx0 hx1 hcurve
  exact no_noncuspidal_point x y hx0 hx1 hcurve

end

end MazurTorsion.XOneEighteenDescent
