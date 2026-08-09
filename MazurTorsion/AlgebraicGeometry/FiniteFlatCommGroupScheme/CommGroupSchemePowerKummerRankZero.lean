/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfQuotientBoundaryInjection
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.MuKernelPrimeFiberKummerRankZero

/-!
# The actual multiplication boundary as a Kummer rank-zero input

If multiplication by `p` on an ambient commutative group scheme is fppf, its canonical
scheme-theoretic kernel gives a genuine quotient presentation.  The checked fppf boundary then
descends to an injection from base points modulo `p`th powers.  In additive notation this is the
actual multiplication-by-`p` quotient used by the numerical rank-zero theorem, so no independent
Kummer homomorphism or injectivity hypothesis remains.

The generic endpoint keeps the geometric fppf laws, kernel `H¹` bound, torsion-cardinality law,
and numerical inequality explicit.  The final consumers specialize the kernel to the actual
`mu_p` scheme over `ZMod 5` and `ZMod 11`, using its represented fppf `H¹` bound.  They do not
assert that an intended Mordell--Weil group has been realized as base points, nor do they supply
Raynaud classification, a Néron model, or the torsion law.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.CommGroupScheme

universe u

variable {S : Scheme.{u}}

/-- The canonical fppf quotient presentation of multiplication by `n`, once its three
geometric fppf laws are supplied. -/
noncomputable def powerFppfQuotientPresentation
    (G : CommGroupScheme S) (n : ℕ)
    (hflat : Flat (underlyingHom (powerEnd G n)))
    (hsurjective : Surjective (underlyingHom (powerEnd G n)))
    (hlfp : LocallyOfFinitePresentation (underlyingHom (powerEnd G n))) :
    FppfQuotientPresentation (kernelInclusion (powerEnd G n)) where
  quotient := G
  project := powerEnd G n
  project_flat := hflat
  project_surjective := hsurjective
  project_lfp := hlfp
  kernelIso := Iso.refl _
  kernelIso_hom_kernelInclusion := by simp

namespace FppfQuotientPresentation

/-- For the multiplication-by-`n` presentation, source base points map onto exactly the
subgroup of `n`th powers. -/
theorem power_basePointProjectRange
    (G : CommGroupScheme S) (n : ℕ)
    (hflat : Flat (underlyingHom (powerEnd G n)))
    (hsurjective : Surjective (underlyingHom (powerEnd G n)))
    (hlfp : LocallyOfFinitePresentation (underlyingHom (powerEnd G n))) :
    (powerFppfQuotientPresentation G n hflat hsurjective hlfp).basePointProjectRange =
      (powMonoidHom (α := BasePoint G) n).range := by
  change (mapPoint (powerEnd G n) (baseObject S)).range = _
  apply congrArg MonoidHom.range
  apply MonoidHom.ext
  intro x
  exact mapPoint_powerEnd G n (baseObject S) x

/-- Low-degree exactness for multiplication by `n` identifies the subgroup of `n`th powers
with the kernel of the actual fppf boundary. -/
theorem powerRange_eq_boundaryHom_ker
    (G : CommGroupScheme S) (n : ℕ)
    (hflat : Flat (underlyingHom (powerEnd G n)))
    (hsurjective : Surjective (underlyingHom (powerEnd G n)))
    (hlfp : LocallyOfFinitePresentation (underlyingHom (powerEnd G n))) :
    (powMonoidHom (α := BasePoint G) n).range =
      (powerFppfQuotientPresentation G n hflat hsurjective hlfp).boundaryHom.ker :=
  (power_basePointProjectRange G n hflat hsurjective hlfp).symm.trans
    ((powerFppfQuotientPresentation G n hflat hsurjective hlfp)
      |>.basePointProjectRange_eq_boundaryHom_ker)

/-- The actual fppf Kummer homomorphism for multiplication by `n`. -/
noncomputable def powerKummerHom
    (G : CommGroupScheme S) (n : ℕ)
    (hflat : Flat (underlyingHom (powerEnd G n)))
    (hsurjective : Surjective (underlyingHom (powerEnd G n)))
    (hlfp : LocallyOfFinitePresentation (underlyingHom (powerEnd G n))) :
    BasePoint G ⧸ (powMonoidHom (α := BasePoint G) n).range →*
      (CommGroupScheme.kernel (powerEnd G n)).FppfHOne.{u} :=
  QuotientGroup.lift (powMonoidHom (α := BasePoint G) n).range
    (powerFppfQuotientPresentation G n hflat hsurjective hlfp).boundaryHom
    (powerRange_eq_boundaryHom_ker G n hflat hsurjective hlfp).le

/-- The multiplication-by-`n` fppf Kummer homomorphism is injective. -/
theorem powerKummerHom_injective
    (G : CommGroupScheme S) (n : ℕ)
    (hflat : Flat (underlyingHom (powerEnd G n)))
    (hsurjective : Surjective (underlyingHom (powerEnd G n)))
    (hlfp : LocallyOfFinitePresentation (underlyingHom (powerEnd G n))) :
    Function.Injective (powerKummerHom G n hflat hsurjective hlfp) := by
  change Function.Injective
    (QuotientGroup.lift (powMonoidHom (α := BasePoint G) n).range
      (powerFppfQuotientPresentation G n hflat hsurjective hlfp).boundaryHom
      (powerRange_eq_boundaryHom_ker G n hflat hsurjective hlfp).le)
  exact (QuotientGroup.injective_lift_iff
    (N := (powMonoidHom (α := BasePoint G) n).range)
      (powerFppfQuotientPresentation G n hflat hsurjective hlfp).boundaryHom
      (powerRange_eq_boundaryHom_ker G n hflat hsurjective hlfp).le).2
        (powerRange_eq_boundaryHom_ker G n hflat hsurjective hlfp)

end FppfQuotientPresentation

end AlgebraicGeometry.CommGroupScheme

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme

open CommGroupScheme

universe u

/-- The actual multiplication-by-`p` boundary supplies the Kummer map and its injectivity;
only the geometric fppf laws, kernel cohomology bound, torsion law, and numerical inequality
remain as inputs. -/
theorem finrank_additive_basePoint_eq_zero_of_powerKummer
    {S : Scheme.{u}} {p : ℕ} (hp : p.Prime)
    (G : CommGroupScheme S)
    [AddGroup.FG (Additive (CommGroupScheme.BasePoint G))]
    (hflat : Flat (underlyingHom (CommGroupScheme.powerEnd G p)))
    (hsurjective : Surjective (underlyingHom (CommGroupScheme.powerEnd G p)))
    (hlfp : LocallyOfFinitePresentation
      (underlyingHom (CommGroupScheme.powerEnd G p)))
    (kernelHOneData : FinitePGroup.BoundedData p
      (CommGroupScheme.kernel (CommGroupScheme.powerEnd G p)).FppfHOne.{u})
    (torsionLength : ℕ)
    (hkernel : Nat.card
        (nsmulAddMonoidHom
          (α := Additive (CommGroupScheme.BasePoint G)) p).ker =
      p ^ torsionLength)
    (hbound : kernelHOneData.length ≤ torsionLength) :
    Module.finrank ℤ (Additive (CommGroupScheme.BasePoint G)) = 0 := by
  letI : Finite
      (CommGroupScheme.kernel (CommGroupScheme.powerEnd G p)).FppfHOne.{u} :=
    kernelHOneData.finite
  apply finrank_eq_zero_of_injective_kummer_of_card_le_torsion
    p torsionLength hp hkernel
    (CommGroupScheme.FppfQuotientPresentation.powerKummerHom
      G p hflat hsurjective hlfp)
    (CommGroupScheme.FppfQuotientPresentation.powerKummerHom_injective
      G p hflat hsurjective hlfp)
  exact kernelHOneData.card_le.trans
    ((Nat.pow_le_pow_iff_right hp.one_lt).mpr hbound)

/-- An fppf multiplication-by-`p` map whose actual kernel is `mu_p` over `ZMod 5` supplies
the Kummer injection required by the rank-zero criterion. -/
theorem finrank_additive_basePoint_eq_zero_of_powerKummer_muKernelAtFive
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (G : CommGroupScheme (Spec (.of (ZMod 5))))
    [AddGroup.FG (Additive (CommGroupScheme.BasePoint G))]
    (hflat : Flat (underlyingHom (CommGroupScheme.powerEnd G p)))
    (hsurjective : Surjective (underlyingHom (CommGroupScheme.powerEnd G p)))
    (hlfp : LocallyOfFinitePresentation
      (underlyingHom (CommGroupScheme.powerEnd G p)))
    (kernelIso : CommGroupScheme.kernel (CommGroupScheme.powerEnd G p) ≅
      (finiteFlatCommGroupSchemeProperty _).ι.obj (muScheme (ZMod 5) p))
    (torsionLength : ℕ)
    (hkernel : Nat.card
        (nsmulAddMonoidHom
          (α := Additive (CommGroupScheme.BasePoint G)) p).ker =
      p ^ torsionLength)
    (hbound : 1 ≤ torsionLength) :
    Module.finrank ℤ (Additive (CommGroupScheme.BasePoint G)) = 0 := by
  have hresiduePrime : Nat.Prime 5 := by decide
  let kernelHOneData :=
    (muSchemeFppfHOne_zmod_primes_boundedData p 5 hp hresiduePrime).congr
      (CommGroupScheme.fppfHOneMulEquivOfIso kernelIso).symm
  have hlength : kernelHOneData.length = 1 := by
    calc
      kernelHOneData.length =
          (muSchemeFppfHOne_zmod_primes_boundedData p 5 hp hresiduePrime).length :=
        FinitePGroup.BoundedData.congr_length _ _
      _ = 1 :=
        muSchemeFppfHOne_zmod_primes_boundedData_length p 5 hp hresiduePrime
  exact finrank_additive_basePoint_eq_zero_of_powerKummer hp G hflat
    hsurjective hlfp kernelHOneData torsionLength hkernel (hlength ▸ hbound)

/-- The same actual multiplication-by-`p` Kummer construction gives the residue-eleven
rank-zero endpoint. -/
theorem finrank_additive_basePoint_eq_zero_of_powerKummer_muKernelAtEleven
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (G : CommGroupScheme (Spec (.of (ZMod 11))))
    [AddGroup.FG (Additive (CommGroupScheme.BasePoint G))]
    (hflat : Flat (underlyingHom (CommGroupScheme.powerEnd G p)))
    (hsurjective : Surjective (underlyingHom (CommGroupScheme.powerEnd G p)))
    (hlfp : LocallyOfFinitePresentation
      (underlyingHom (CommGroupScheme.powerEnd G p)))
    (kernelIso : CommGroupScheme.kernel (CommGroupScheme.powerEnd G p) ≅
      (finiteFlatCommGroupSchemeProperty _).ι.obj (muScheme (ZMod 11) p))
    (torsionLength : ℕ)
    (hkernel : Nat.card
        (nsmulAddMonoidHom
          (α := Additive (CommGroupScheme.BasePoint G)) p).ker =
      p ^ torsionLength)
    (hbound : 1 ≤ torsionLength) :
    Module.finrank ℤ (Additive (CommGroupScheme.BasePoint G)) = 0 := by
  have hresiduePrime : Nat.Prime 11 := by decide
  let kernelHOneData :=
    (muSchemeFppfHOne_zmod_primes_boundedData p 11 hp hresiduePrime).congr
      (CommGroupScheme.fppfHOneMulEquivOfIso kernelIso).symm
  have hlength : kernelHOneData.length = 1 := by
    calc
      kernelHOneData.length =
          (muSchemeFppfHOne_zmod_primes_boundedData p 11 hp hresiduePrime).length :=
        FinitePGroup.BoundedData.congr_length _ _
      _ = 1 :=
        muSchemeFppfHOne_zmod_primes_boundedData_length p 11 hp hresiduePrime
  exact finrank_additive_basePoint_eq_zero_of_powerKummer hp G hflat
    hsurjective hlfp kernelHOneData torsionLength hkernel (hlength ▸ hbound)

end AlgebraicGeometry.FiniteFlatCommGroupScheme
