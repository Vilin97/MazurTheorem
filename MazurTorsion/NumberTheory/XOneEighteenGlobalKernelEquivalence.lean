/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/

import MazurTorsion.NumberTheory.XOneEighteenGlobalSelmerBridge

/-!
# The explicit and generic global norm kernels agree

The minimal two-descent algebra is explicitly equivalent to the degree-nine
two-division field.  This file restricts the induced squareclass equivalence
to the dyadically supported relative-norm kernels on the two sides.
-/

namespace MazurTorsion.XOneEighteenGlobalKernelEquivalence

noncomputable section

open MazurTorsion.XOneEighteenGlobalSelmerBridge
open MazurTorsion.XOneEighteenMinimalTwoDescentModel
open MazurTorsion.XOneEighteenTwoDivisionArithmetic

private def descentDyadicSupportedHom :
    descentDyadicNormKernel →* DyadicSelmerM :=
  (minimalDescentSquareclassEquiv.toMonoidHom.comp
      descentDyadicNormKernel.subtype).codRestrict
    DyadicSelmerM fun x ↦ x.property.1

/-- The explicit squareclass equivalence, restricted from the generic global
dyadic norm kernel to the supported relative-norm kernel. -/
def descentDyadicNormKernelHom :
    descentDyadicNormKernel →* fullDyadicRelativeNorm.ker :=
  descentDyadicSupportedHom.codRestrict fullDyadicRelativeNorm.ker fun x ↦ by
    change relativeNormSquareclasses
      (minimalDescentSquareclassEquiv
        (x : minimalDescentCurve.toAffine.M)) = 1
    rw [relativeNorm_minimalDescentSquareclassEquiv]
    exact x.property.2

/-- The restricted hom has the expected underlying explicit squareclass. -/
@[simp] theorem descentDyadicNormKernelHom_coe
    (x : descentDyadicNormKernel) :
    (((descentDyadicNormKernelHom x : fullDyadicRelativeNorm.ker) :
        DyadicSelmerM) : Units.modPow M 2) =
      minimalDescentSquareclassEquiv x :=
  rfl

private theorem symm_mem_descentDyadicNormKernel
    (y : fullDyadicRelativeNorm.ker) :
    minimalDescentSquareclassEquiv.symm
        ((y.1 : DyadicSelmerM) : Units.modPow M 2) ∈
      descentDyadicNormKernel := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · apply Subgroup.mem_comap.mpr
    change minimalDescentSquareclassEquiv
      (minimalDescentSquareclassEquiv.symm
        ((y.1 : DyadicSelmerM) : Units.modPow M 2)) ∈ DyadicSelmerM
    rw [minimalDescentSquareclassEquiv.apply_symm_apply]
    exact y.1.property
  · apply MonoidHom.mem_ker.mpr
    rw [← relativeNorm_minimalDescentSquareclassEquiv,
      minimalDescentSquareclassEquiv.apply_symm_apply]
    have hy := MonoidHom.mem_ker.mp y.property
    change relativeNormSquareclasses
      ((y.1 : DyadicSelmerM) : Units.modPow M 2) = 1 at hy
    exact hy

/-- The restricted hom is a bijection.  Surjectivity is witnessed explicitly
by the inverse squareclass equivalence. -/
theorem descentDyadicNormKernelHom_bijective :
    Function.Bijective descentDyadicNormKernelHom := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply minimalDescentSquareclassEquiv.injective
    have h := congrArg
      (fun z : fullDyadicRelativeNorm.ker ↦
        ((z.1 : DyadicSelmerM) : Units.modPow M 2)) hxy
    simpa only [descentDyadicNormKernelHom_coe] using h
  · intro y
    let x : descentDyadicNormKernel :=
      ⟨minimalDescentSquareclassEquiv.symm
        ((y.1 : DyadicSelmerM) : Units.modPow M 2),
          symm_mem_descentDyadicNormKernel y⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    calc
      (((descentDyadicNormKernelHom x : fullDyadicRelativeNorm.ker) :
          DyadicSelmerM) : Units.modPow M 2) =
          minimalDescentSquareclassEquiv x :=
        descentDyadicNormKernelHom_coe x
      _ = minimalDescentSquareclassEquiv
          (minimalDescentSquareclassEquiv.symm
            ((y.1 : DyadicSelmerM) : Units.modPow M 2)) := rfl
      _ = ((y.1 : DyadicSelmerM) : Units.modPow M 2) :=
        minimalDescentSquareclassEquiv.apply_symm_apply _

end

end MazurTorsion.XOneEighteenGlobalKernelEquivalence
