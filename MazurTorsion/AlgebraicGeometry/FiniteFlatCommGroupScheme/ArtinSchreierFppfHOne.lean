/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.GroupTheory.QuotientGroup.Basic
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.ArtinSchreierConstantKernel
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.ArtinSchreierMapFppf
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfHOneBaseIso
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfQuotientBoundaryInjection
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfQuotientConnecting

/-!
# Fppf cohomology of the constant prime group via Artin--Schreier

The two constructions of the Artin--Schreier endomorphism, from the represented-kernel and
fppf-quotient developments, have the same Hopf-coordinate map.  This file records their
definitional agreement and combines the resulting geometric quotient presentation with
additive Hilbert 90.

Over `Spec (ZMod p)`, the Artin--Schreier map is zero on global points.  Hence its boundary
source is the additive prime field itself, and low-degree exactness identifies this source
with the full fppf `H¹` of the canonical kernel.  Transport across the represented
constant-kernel isomorphism gives exact cardinality `p`, with concrete consumers at five and
eleven.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.CommGroupScheme.ArtinSchreier

open AffineCommGroupScheme
open FiniteFlatCommGroupScheme

variable (p : ℕ) [Fact p.Prime]

/-- The geometric Artin--Schreier map used for the fppf quotient is definitionally the map
used to identify the represented constant kernel. -/
theorem artinSchreierQuotientMap_eq_artinSchreierMap :
    ArtinSchreierGeometry.artinSchreierQuotientMap p =
      artinSchreierMap (ZMod p) p :=
  rfl

/-- The projection in the canonical fppf quotient presentation is the represented
Artin--Schreier endomorphism. -/
theorem artinSchreierFppfQuotientPresentation_project :
    (ArtinSchreierGeometry.artinSchreierFppfQuotientPresentation p).project =
      artinSchreierMap (ZMod p) p :=
  rfl

/-- The chosen subgroup in the fppf quotient presentation is the same canonical kernel as
the represented constant-kernel comparison. -/
theorem artinSchreierFppfQuotientPresentation_inclusion :
    (ArtinSchreierGeometry.artinSchreierFppfQuotientPresentation p).kernelPresentation.inclusion =
      kernelInclusion (artinSchreierMap (ZMod p) p) :=
  rfl

/-- Base points of the additive quotient modulo global Artin--Schreier images. -/
abbrev ArtinSchreierBoundaryQuotient :=
  (ArtinSchreierGeometry.artinSchreierFppfQuotientPresentation p).BoundarySourceQuotient

/-- Additive global points over `Spec R`, read on the canonical affine self-test object. -/
def additiveBasePointMulEquiv (R : Type*) [CommRing R] :
    BasePoint (additiveScheme R) ≃* Multiplicative R :=
  (pointMulEquivOfOverIso (additiveScheme R)
      (baseIsoSelfTestObject R)).trans
    (additivePointMulEquiv R R)

/-- On prime-field global points the Artin--Schreier projection is identically zero. -/
theorem mapPoint_artinSchreierQuotientMap_base_eq_one
    (x : BasePoint (additiveScheme (ZMod p))) :
    mapPoint (ArtinSchreierGeometry.artinSchreierQuotientMap p)
        (baseObject (Spec (.of (ZMod p)))) x = 1 := by
  let e : baseObject (Spec (.of (ZMod p))) ≅
      testObject (R := ZMod p) (ZMod p) :=
    baseIsoSelfTestObject (ZMod p)
  apply (pointMulEquivOfOverIso (additiveScheme (ZMod p)) e).injective
  rw [map_one, pointMulEquivOfOverIso]
  change pullPoint (additiveScheme (ZMod p)) e.inv
      (mapPoint (ArtinSchreierGeometry.artinSchreierQuotientMap p)
        (baseObject (Spec (.of (ZMod p)))) x) = 1
  rw [← mapPoint_pullPoint]
  apply (additivePointMulEquiv (ZMod p) (ZMod p)).injective
  rw [map_one]
  change Multiplicative.toAdd
      (additivePointMulEquiv (ZMod p) (ZMod p)
        (mapPoint (ArtinSchreierGeometry.artinSchreierQuotientMap p)
          (testObject (R := ZMod p) (ZMod p))
          (pullPoint (additiveScheme (ZMod p)) e.inv x))) = 0
  rw [ArtinSchreierGeometry.toAdd_additivePointMulEquiv_mapPoint_artinSchreierQuotientMap]
  simp [ZMod.pow_card]

/-- The image subgroup of global Artin--Schreier points over the prime field is trivial. -/
theorem artinSchreierBasePointProjectRange_eq_bot :
    (ArtinSchreierGeometry.artinSchreierFppfQuotientPresentation p).basePointProjectRange =
      ⊥ := by
  change (mapPoint (ArtinSchreierGeometry.artinSchreierQuotientMap p)
    (baseObject (Spec (.of (ZMod p))))).range = ⊥
  rw [MonoidHom.range_eq_bot_iff]
  apply MonoidHom.ext
  intro x
  exact mapPoint_artinSchreierQuotientMap_base_eq_one p x

/-- The Artin--Schreier boundary source over the prime field is the additive prime field. -/
def artinSchreierBoundaryQuotientMulEquivPrimeField :
    ArtinSchreierBoundaryQuotient p ≃* Multiplicative (ZMod p) :=
  (QuotientGroup.quotientMulEquivOfEq
      (artinSchreierBasePointProjectRange_eq_bot p)).trans
    ((QuotientGroup.quotientBot).trans
      (additiveBasePointMulEquiv (ZMod p)))

/-- Additive Hilbert 90 upgrades low-degree exactness from the kernel of extension to the
full fppf `H¹` of the canonical Artin--Schreier kernel. -/
def artinSchreierBoundaryQuotientMulEquivKernelFppfHOne :
    ArtinSchreierBoundaryQuotient p ≃*
      (kernel (artinSchreierMap (ZMod p) p)).FppfHOne.{0} := by
  let D := ArtinSchreierGeometry.artinSchreierFppfQuotientPresentation p
  letI : Subsingleton (additiveScheme (ZMod p)).FppfHOne.{0} :=
    AdditiveCocycleDescent.additiveFppfHOne_subsingleton (ZMod p)
  let f : (kernel (artinSchreierMap (ZMod p) p)).FppfHOne.{0} →*
      (fppfHOneMap (kernelInclusion
        (artinSchreierMap (ZMod p) p))).ker :=
    (MonoidHom.id _).codRestrict _
      (fun z ↦ MonoidHom.mem_ker.mpr (Subsingleton.elim _ _))
  let e : (kernel (artinSchreierMap (ZMod p) p)).FppfHOne.{0} ≃*
      (fppfHOneMap (kernelInclusion
        (artinSchreierMap (ZMod p) p))).ker :=
    MulEquiv.ofBijective f
      ⟨(fun _ _ h ↦ congrArg Subtype.val h),
        (fun z ↦ ⟨z.1, Subtype.ext rfl⟩)⟩
  exact D.boundaryQuotientKernelMulEquiv.trans e.symm

/-- The Artin--Schreier boundary source is the full fppf `H¹` of the represented constant
prime group. -/
def artinSchreierBoundaryQuotientMulEquivConstantFppfHOne :
    ArtinSchreierBoundaryQuotient p ≃*
      ((constantScheme (ZMod p) (Multiplicative (ZMod p))).obj).FppfHOne.{0} :=
  (artinSchreierBoundaryQuotientMulEquivKernelFppfHOne p).trans
    (fppfHOneMulEquivOfIso (constantSchemeArtinSchreierKernelIso p)).symm

/-- The actual Artin--Schreier boundary quotient over a prime field has cardinality `p`. -/
def artinSchreierBoundaryQuotientCertifiedData :
    FinitePGroup.CertifiedData p (ArtinSchreierBoundaryQuotient p) := by
  let e := artinSchreierBoundaryQuotientMulEquivPrimeField p
  exact
    { finite := Finite.of_equiv (Multiplicative (ZMod p)) e.symm.toEquiv
      length := 1
      card_eq := by
        rw [Nat.card_congr e.toEquiv, pow_one]
        exact (Nat.card_congr
          (Multiplicative.ofAdd : ZMod p ≃ Multiplicative (ZMod p))).trans
            (Nat.card_zmod p) }

/-- The represented constant prime group has fppf `H¹` of exact cardinality `p`, proved
through the geometric Artin--Schreier sequence. -/
def constantSchemeFppfHOne_zmod_prime_certifiedData :
    FinitePGroup.CertifiedData p
      ((constantScheme (ZMod p) (Multiplicative (ZMod p))).obj).FppfHOne.{0} := by
  let D := artinSchreierBoundaryQuotientCertifiedData p
  let e := artinSchreierBoundaryQuotientMulEquivConstantFppfHOne p
  letI : Finite (ArtinSchreierBoundaryQuotient p) := D.finite
  exact
    { finite := Finite.of_equiv (ArtinSchreierBoundaryQuotient p) e.toEquiv
      length := D.length
      card_eq := (Nat.card_congr e.symm.toEquiv).trans D.card_eq }

@[simp]
theorem artinSchreierBoundaryQuotientCertifiedData_length :
    (artinSchreierBoundaryQuotientCertifiedData p).length = 1 :=
  rfl

@[simp]
theorem constantSchemeFppfHOne_zmod_prime_certifiedData_length :
    (constantSchemeFppfHOne_zmod_prime_certifiedData p).length = 1 :=
  rfl

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- Concrete exact cardinal data for constant `Z/5Z` fppf `H¹` over `Spec (ZMod 5)`. -/
def constantSchemeFppfHOneCertifiedDataAtFive :
    FinitePGroup.CertifiedData 5
      ((constantScheme (ZMod 5) (Multiplicative (ZMod 5))).obj).FppfHOne.{0} :=
  constantSchemeFppfHOne_zmod_prime_certifiedData 5

/-- Concrete exact cardinal data for constant `Z/11Z` fppf `H¹` over `Spec (ZMod 11)`. -/
def constantSchemeFppfHOneCertifiedDataAtEleven :
    FinitePGroup.CertifiedData 11
      ((constantScheme (ZMod 11) (Multiplicative (ZMod 11))).obj).FppfHOne.{0} :=
  constantSchemeFppfHOne_zmod_prime_certifiedData 11

@[simp]
theorem constantSchemeFppfHOneCertifiedDataAtFive_length :
    constantSchemeFppfHOneCertifiedDataAtFive.length = 1 :=
  rfl

@[simp]
theorem constantSchemeFppfHOneCertifiedDataAtEleven_length :
    constantSchemeFppfHOneCertifiedDataAtEleven.length = 1 :=
  rfl

end AlgebraicGeometry.CommGroupScheme.ArtinSchreier
