/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.CommGroupSchemePowerKummerRankZero
import MazurTorsion.EllipticCurve.IntegerPrimeSpecialization

/-!
# The actual multiplication kernel supplies the torsion cardinality

The scheme-theoretic kernel of multiplication by `p` represents the pointwise kernel on every
test scheme.  On base points, changing from multiplicative to additive notation identifies that
pointwise kernel with the kernel of `p`-fold addition.  Consequently an actual finite-`p`
certificate on the geometric kernel supplies the torsion-cardinality equality required by the
checked Kummer rank-zero theorem.

The resulting endpoints still require an actual ambient commutative group scheme, fppf
multiplication, finite-generation of its base points, and cohomology certificates for its actual
kernel.  No Néron model, Mordell--Weil comparison, Raynaud classification, or torsion theorem is
manufactured here.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj
open IsDedekindDomain HeightOneSpectrum
open MazurTorsion.IntegerPrimeSpecialization

namespace AlgebraicGeometry.CommGroupScheme

universe u

variable {S : Scheme.{u}}

/-- The pointwise kernel of the multiplicative power map is the additive `n`-torsion kernel on
the same base-point group. -/
noncomputable def powerPointKernelEquivNsmulKernel
    (G : CommGroupScheme S) (n : ℕ) :
    (mapPoint (powerEnd G n) (baseObject S)).ker ≃
      (nsmulAddMonoidHom (α := Additive (BasePoint G)) n).ker where
  toFun x := ⟨Additive.ofMul x.1, by
    apply AddMonoidHom.mem_ker.mpr
    change Additive.ofMul (x.1 ^ n) = Additive.ofMul 1
    exact congrArg Additive.ofMul (by
      simpa only [mapPoint_powerEnd] using MonoidHom.mem_ker.mp x.2)⟩
  invFun x := ⟨x.1.toMul, by
    apply MonoidHom.mem_ker.mpr
    rw [mapPoint_powerEnd]
    simpa using congrArg Additive.toMul (AddMonoidHom.mem_ker.mp x.2)⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

/-- Base points of the actual scheme-theoretic multiplication kernel are equivalent to the
additive torsion kernel. -/
noncomputable def powerKernelBasePointEquivNsmulKernel
    (G : CommGroupScheme S) (n : ℕ) :
    BasePoint (kernel (powerEnd G n)) ≃
      (nsmulAddMonoidHom (α := Additive (BasePoint G)) n).ker :=
  (pointKernelMulEquiv (powerEnd G n) (baseObject S)).toEquiv.trans
    (powerPointKernelEquivNsmulKernel G n)

end AlgebraicGeometry.CommGroupScheme

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme

open CommGroupScheme

universe u

noncomputable local instance powerKernelIsCommMonObj
    {S : Scheme.{u}} (G : CommGroupScheme S) (p : ℕ) :
    IsCommMonObj
      (CommGroupScheme.kernelGrp (CommGroupScheme.powerEnd G p)).X :=
  CommGroupScheme.kernelGrp_isComm (CommGroupScheme.powerEnd G p)

noncomputable local instance powerKernelBasePointCommGroup
    {S : Scheme.{u}} (G : CommGroupScheme S) (p : ℕ) :
    CommGroup (CommGroupScheme.BasePoint
      (CommGroupScheme.kernel (CommGroupScheme.powerEnd G p))) :=
  CategoryTheory.Hom.commGroup

/-- A finite-`p` cardinal certificate on the actual multiplication kernel supplies the exact
cardinality of the additive `p`-torsion subgroup of base points. -/
theorem nsmulKernel_natCard_eq_of_powerKernelCertifiedData
    {S : Scheme.{u}} {p : ℕ} (G : CommGroupScheme S)
    (kernelHZeroData : FinitePGroup.CertifiedData p
      (CommGroupScheme.BasePoint
        (CommGroupScheme.kernel (CommGroupScheme.powerEnd G p)))) :
    Nat.card (nsmulAddMonoidHom
        (α := Additive (CommGroupScheme.BasePoint G)) p).ker =
      p ^ kernelHZeroData.length := by
  rw [← kernelHZeroData.card_eq]
  exact (Nat.card_congr (powerKernelBasePointEquivNsmulKernel G p)).symm

/-- The actual multiplication kernel supplies both the torsion length and its cardinality law,
so the power-Kummer rank-zero theorem needs no separately restated torsion equality. -/
theorem finrank_additive_basePoint_eq_zero_of_powerKummer_kernelData
    {S : Scheme.{u}} {p : ℕ} (hp : p.Prime)
    (G : CommGroupScheme S)
    [AddGroup.FG (Additive (CommGroupScheme.BasePoint G))]
    (hflat : Flat (CommGroupScheme.underlyingHom
      (CommGroupScheme.powerEnd G p)))
    (hsurjective : Surjective (CommGroupScheme.underlyingHom
      (CommGroupScheme.powerEnd G p)))
    (hlfp : LocallyOfFinitePresentation (CommGroupScheme.underlyingHom
      (CommGroupScheme.powerEnd G p)))
    (kernelHZeroData : FinitePGroup.CertifiedData p
      (CommGroupScheme.BasePoint
        (CommGroupScheme.kernel (CommGroupScheme.powerEnd G p))))
    (kernelHOneData : FinitePGroup.BoundedData p
      (CommGroupScheme.kernel (CommGroupScheme.powerEnd G p)).FppfHOne.{u})
    (hbound : kernelHOneData.length ≤ kernelHZeroData.length) :
    Module.finrank ℤ (Additive (CommGroupScheme.BasePoint G)) = 0 :=
  finrank_additive_basePoint_eq_zero_of_powerKummer hp G hflat hsurjective hlfp
    kernelHOneData kernelHZeroData.length
      (nsmulKernel_natCard_eq_of_powerKernelCertifiedData G kernelHZeroData) hbound

/-- Genuine five-adic rank-zero endpoint: actual degree-zero and degree-one data on the
scheme-theoretic `[5]`-kernel supply the Kummer and torsion inputs. -/
theorem finrank_additive_basePoint_eq_zero_of_powerKummer_kernelDataAtFive
    (G : CommGroupScheme
      (Spec (.of (atFive.adicCompletionIntegers ℚ))))
    [AddGroup.FG (Additive (CommGroupScheme.BasePoint G))]
    (hflat : Flat (CommGroupScheme.underlyingHom
      (CommGroupScheme.powerEnd G 5)))
    (hsurjective : Surjective (CommGroupScheme.underlyingHom
      (CommGroupScheme.powerEnd G 5)))
    (hlfp : LocallyOfFinitePresentation (CommGroupScheme.underlyingHom
      (CommGroupScheme.powerEnd G 5)))
    (kernelHZeroData : FinitePGroup.CertifiedData 5
      (CommGroupScheme.BasePoint
        (CommGroupScheme.kernel (CommGroupScheme.powerEnd G 5))))
    (kernelHOneData : FinitePGroup.BoundedData 5
      (CommGroupScheme.kernel (CommGroupScheme.powerEnd G 5)).FppfHOne.{0})
    (hbound : kernelHOneData.length ≤ kernelHZeroData.length) :
    Module.finrank ℤ (Additive (CommGroupScheme.BasePoint G)) = 0 :=
  finrank_additive_basePoint_eq_zero_of_powerKummer_kernelData
    (by decide) G hflat hsurjective hlfp kernelHZeroData kernelHOneData hbound

/-- Genuine eleven-adic counterpart of the actual-kernel Kummer endpoint. -/
theorem finrank_additive_basePoint_eq_zero_of_powerKummer_kernelDataAtEleven
    (G : CommGroupScheme
      (Spec (.of (atEleven.adicCompletionIntegers ℚ))))
    [AddGroup.FG (Additive (CommGroupScheme.BasePoint G))]
    (hflat : Flat (CommGroupScheme.underlyingHom
      (CommGroupScheme.powerEnd G 11)))
    (hsurjective : Surjective (CommGroupScheme.underlyingHom
      (CommGroupScheme.powerEnd G 11)))
    (hlfp : LocallyOfFinitePresentation (CommGroupScheme.underlyingHom
      (CommGroupScheme.powerEnd G 11)))
    (kernelHZeroData : FinitePGroup.CertifiedData 11
      (CommGroupScheme.BasePoint
        (CommGroupScheme.kernel (CommGroupScheme.powerEnd G 11))))
    (kernelHOneData : FinitePGroup.BoundedData 11
      (CommGroupScheme.kernel (CommGroupScheme.powerEnd G 11)).FppfHOne.{0})
    (hbound : kernelHOneData.length ≤ kernelHZeroData.length) :
    Module.finrank ℤ (Additive (CommGroupScheme.BasePoint G)) = 0 :=
  finrank_additive_basePoint_eq_zero_of_powerKummer_kernelData
    (by decide) G hflat hsurjective hlfp kernelHZeroData kernelHOneData hbound

end AlgebraicGeometry.FiniteFlatCommGroupScheme
