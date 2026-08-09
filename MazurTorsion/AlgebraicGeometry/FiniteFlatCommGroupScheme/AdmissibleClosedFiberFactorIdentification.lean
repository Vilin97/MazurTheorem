/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.RingTheory.Etale.Field
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.AdmissibleClosedFiberConnectedEtale
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.ArtinSchreierAdmissiblePrimeFiberConsumers
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.MultiplicativeIntegralHOneRankZeroConsumers

/-!
# Identifying admissible factors from their closed-fibre geometry

In characteristic `p`, the two already-admissible order-`p` factors are distinguished by actual
geometry.  The nontrivial constant factor is disconnected, while `mu_p` is not étale because its
group algebra contains a nonzero nilpotent.  Consequently geometric connectedness forces an
admissible factor into its multiplicative branch, and étaleness forces it into its constant
branch.  The conclusions also descend from a closed fibre to the constructor tag of an integral
admissible factor, since the named factor base changes preserve that tag.

The final theorem consumes both geometric conclusions in the checked integral Kummer rank-zero
criterion, with genuine coefficient-five and coefficient-eleven wrappers.  It leaves the middle
`H⁰`, quotient `H¹`, torsion-cardinality equality, Kummer homomorphism, and Kummer injectivity
explicit.

This is a uniqueness/identification boundary for a factor already supplied by the project's
admissible filtration.  It does not construct an `AdmissibleSimpleFactor` from an arbitrary
rank-`p` finite-flat group scheme, nor extend a generic-fibre isomorphism to an integral one;
those are precisely the still-missing Oort--Tate/Raynaud existence and fullness inputs.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme

universe u

namespace ConstantClosedFiber

variable {p : ℕ} [NeZero p]

/-- The idempotent cutting out the identity component of the constant cyclic group. -/
private def identityIndicator :
    ConstantCoordinates (ZMod p) (Multiplicative (ZMod p)) :=
  ULift.up fun g ↦ if g = 1 then 1 else 0

omit [NeZero p] in
private theorem identityIndicator_isIdempotent :
    IsIdempotentElem (identityIndicator (p := p)) := by
  ext g
  by_cases hg : g = 1 <;> simp [identityIndicator, hg]

omit [NeZero p] in
private theorem identityIndicator_ne_zero (hp : p.Prime) :
    identityIndicator (p := p) ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  intro h
  have hvalue := congrArg
    (fun e : ConstantCoordinates (ZMod p) (Multiplicative (ZMod p)) ↦ e.down 1) h
  simp [identityIndicator] at hvalue

omit [NeZero p] in
private theorem multiplicativeOfAdd_one_ne_one (hp : p.Prime) :
    Multiplicative.ofAdd (1 : ZMod p) ≠ (1 : Multiplicative (ZMod p)) := by
  letI : Fact p.Prime := ⟨hp⟩
  intro h
  change Multiplicative.ofAdd (1 : ZMod p) = Multiplicative.ofAdd 0 at h
  have h10 : (1 : ZMod p) = 0 := by
    simpa using congrArg Multiplicative.toAdd h
  exact one_ne_zero h10

omit [NeZero p] in
private theorem identityIndicator_ne_one (hp : p.Prime) :
    identityIndicator (p := p) ≠ 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  intro h
  have hvalue := congrArg
    (fun e : ConstantCoordinates (ZMod p) (Multiplicative (ZMod p)) ↦
      e.down (Multiplicative.ofAdd (1 : ZMod p))) h
  simp [identityIndicator, multiplicativeOfAdd_one_ne_one hp] at hvalue

/-- The constant group scheme of prime order has a genuine nontrivial clopen component on its
characteristic-`p` fibre. -/
theorem not_connectedSpace_constantScheme (hp : p.Prime) :
    ¬ ConnectedSpace
      (constantScheme (ZMod p) (Multiplicative (ZMod p))).scheme := by
  letI : Fact p.Prime := ⟨hp⟩
  change ¬ ConnectedSpace
    (PrimeSpectrum (ConstantCoordinates (ZMod p) (Multiplicative (ZMod p))))
  intro hconnected
  let e := identityIndicator (p := p)
  have he : IsIdempotentElem e := identityIndicator_isIdempotent
  have hopen : IsClopen
      (PrimeSpectrum.basicOpen e : Set
        (PrimeSpectrum (ConstantCoordinates (ZMod p) (Multiplicative (ZMod p))))) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩
  rcases (connectedSpace_iff_clopen.mp hconnected).2 _ hopen with hempty | huniv
  · have hbot : PrimeSpectrum.basicOpen e =
        (⊥ : TopologicalSpace.Opens
          (PrimeSpectrum (ConstantCoordinates (ZMod p) (Multiplicative (ZMod p))))) := by
      rw [← TopologicalSpace.Opens.coe_inj]
      simpa using hempty
    have hnilpotent : IsNilpotent e :=
      (PrimeSpectrum.basicOpen_eq_bot_iff e).mp hbot
    exact identityIndicator_ne_zero hp (he.eq_zero_of_isNilpotent hnilpotent)
  · have htop : PrimeSpectrum.basicOpen e =
        (⊤ : TopologicalSpace.Opens
          (PrimeSpectrum (ConstantCoordinates (ZMod p) (Multiplicative (ZMod p))))) := by
      rw [← TopologicalSpace.Opens.coe_inj]
      simpa using huniv
    have hsup :
        (⨆ _ : Unit, PrimeSpectrum.basicOpen e) =
          (⊤ : TopologicalSpace.Opens
            (PrimeSpectrum (ConstantCoordinates (ZMod p) (Multiplicative (ZMod p))))) := by
      simpa using htop
    have hspan : Ideal.span (Set.range (fun _ : Unit ↦ e)) = ⊤ :=
      PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp hsup
    have hunit : IsUnit e := by
      rw [show Set.range (fun _ : Unit ↦ e) = {e} by simp] at hspan
      exact Ideal.span_singleton_eq_top.mp hspan
    exact identityIndicator_ne_one hp
      ((IsIdempotentElem.iff_eq_one_of_isUnit hunit).mp he)

end ConstantClosedFiber

namespace MuClosedFiber

variable {p : ℕ} [NeZero p]

omit [NeZero p] in
private theorem groupGenerator_ne_one (hp : p.Prime) :
    Multiplicative.ofAdd (1 : ZMod p) ≠ (1 : Multiplicative (ZMod p)) := by
  letI : Fact p.Prime := ⟨hp⟩
  intro h
  change Multiplicative.ofAdd (1 : ZMod p) = Multiplicative.ofAdd 0 at h
  have h10 : (1 : ZMod p) = 0 := by
    simpa using congrArg Multiplicative.toAdd h
  exact one_ne_zero h10

/-- The characteristic-`p` coordinate algebra of `mu_p` contains an explicit nonzero
nilpotent. -/
theorem exists_nonzero_isNilpotent_monoidAlgebra (hp : p.Prime) :
    ∃ x : MonoidAlgebra (ZMod p) (Multiplicative (ZMod p)),
      x ≠ 0 ∧ IsNilpotent x := by
  letI : Fact p.Prime := ⟨hp⟩
  let g : Multiplicative (ZMod p) := Multiplicative.ofAdd 1
  let x : MonoidAlgebra (ZMod p) (Multiplicative (ZMod p)) :=
    MonoidAlgebra.single g 1 - MonoidAlgebra.single 1 1
  have hg : g ≠ 1 := groupGenerator_ne_one hp
  have hx0 : x ≠ 0 := by
    intro hx
    have hcoeff := congrArg
      (fun y : MonoidAlgebra (ZMod p) (Multiplicative (ZMod p)) ↦ y.coeff g) hx
    simp [x, hg] at hcoeff
  have haugmentation : augmentation (p := p) (ZMod p) x = 0 := by
    simp [x]
  exact ⟨x, hx0, isNilpotent_of_augmentation_eq_zero hp (ZMod p) haugmentation⟩

/-- The actual characteristic-`p` group scheme `mu_p` is not étale. -/
theorem not_etale_muScheme (hp : p.Prime) :
    ¬ Etale (muScheme (ZMod p) p).structureMap := by
  letI : Fact p.Prime := ⟨hp⟩
  intro hetale
  change Etale
    (Spec.map (CommRingCat.ofHom
      (algebraMap (ZMod p)
        (MonoidAlgebra (ZMod p) (Multiplicative (ZMod p)))))) at hetale
  rw [HasRingHomProperty.Spec_iff (P := @Etale)] at hetale
  letI : Algebra.Etale (ZMod p)
      (MonoidAlgebra (ZMod p) (Multiplicative (ZMod p))) :=
    RingHom.etale_algebraMap.mp hetale
  letI : _root_.IsReduced (MonoidAlgebra (ZMod p) (Multiplicative (ZMod p))) :=
    Algebra.FormallyUnramified.isReduced_of_field (ZMod p)
      (MonoidAlgebra (ZMod p) (Multiplicative (ZMod p)))
  obtain ⟨x, hx, hnilpotent⟩ := exists_nonzero_isNilpotent_monoidAlgebra hp
  exact hx hnilpotent.eq_zero

end MuClosedFiber

namespace AdmissibleSimpleFactor

/-- Geometric connectedness of an already-admissible order-`p` factor on the characteristic-`p`
fibre uniquely selects its multiplicative branch. -/
theorem isMultiplicative_of_geometricallyConnected
    {p : ℕ} [NeZero p]
    {Q : FiniteFlatCommGroupScheme (Spec (.of (ZMod p)))}
    (F : AdmissibleSimpleFactor (ZMod p) p Q) (hp : p.Prime)
    (hQ : GeometricallyConnected Q.structureMap) : F.IsMultiplicative := by
  cases F with
  | constant e =>
      exfalso
      letI : Fact p.Prime := ⟨hp⟩
      have hconnected : ConnectedSpace Q.scheme :=
        hQ.geometrically_connectedSpace (K := ZMod p) (Z := Q.scheme)
          (𝟙 (Spec (.of (ZMod p))))
          (𝟙 Q.scheme) Q.structureMap (IsPullback.id_horiz Q.structureMap)
      rw [(schemeIsoOfFiniteFlatIso e).hom.homeomorph.connectedSpace_iff] at hconnected
      exact ConstantClosedFiber.not_connectedSpace_constantScheme hp hconnected
  | multiplicative _ => trivial

/-- Étaleness of an already-admissible order-`p` factor on the characteristic-`p` fibre uniquely
selects its constant branch. -/
theorem isConstant_of_etale
    {p : ℕ} [NeZero p]
    {Q : FiniteFlatCommGroupScheme (Spec (.of (ZMod p)))}
    (F : AdmissibleSimpleFactor (ZMod p) p Q) (hp : p.Prime)
    (hQ : Etale Q.structureMap) : F.IsConstant := by
  cases F with
  | constant _ => trivial
  | multiplicative e =>
      exfalso
      have hmu : Etale (muScheme (ZMod p) p).structureMap :=
        etale_structureMap_of_iso e.symm hQ
      exact MuClosedFiber.not_etale_muScheme hp hmu

/-- If the actual characteristic-`p` fibre of an already-admissible factor is geometrically
connected, the original factor was constructed from the multiplicative branch. -/
theorem isMultiplicative_of_closedFiber_geometricallyConnected
    {R : Type} [CommRing R] {p : ℕ} [NeZero p] [Algebra R (ZMod p)]
    {Q : FiniteFlatCommGroupScheme (Spec (.of R))}
    (F : AdmissibleSimpleFactor R p Q) (hp : p.Prime)
    (hQ : GeometricallyConnected
      ((FiniteFlatCommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap R (ZMod p))))).obj Q).structureMap) :
    F.IsMultiplicative := by
  have hbase : (F.baseChange (K := ZMod p)).IsMultiplicative :=
    (F.baseChange (K := ZMod p)).isMultiplicative_of_geometricallyConnected hp hQ
  cases F with
  | constant _ => exact hbase
  | multiplicative _ => trivial

/-- If the actual characteristic-`p` fibre of an already-admissible factor is étale, the
original factor was constructed from the constant branch. -/
theorem isConstant_of_closedFiber_etale
    {R : Type} [CommRing R] {p : ℕ} [NeZero p] [Algebra R (ZMod p)]
    {Q : FiniteFlatCommGroupScheme (Spec (.of R))}
    (F : AdmissibleSimpleFactor R p Q) (hp : p.Prime)
    (hQ : Etale
      ((FiniteFlatCommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap R (ZMod p))))).obj Q).structureMap) :
    F.IsConstant := by
  have hbase : (F.baseChange (K := ZMod p)).IsConstant :=
    (F.baseChange (K := ZMod p)).isConstant_of_etale hp hQ
  cases F with
  | constant _ => trivial
  | multiplicative _ => exact hbase

private theorem hZeroLength_eq_one_of_isConstant
    {p : ℕ} [NeZero p]
    {Q : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (F : AdmissibleSimpleFactor ℤ p Q) (hF : F.IsConstant) :
    F.hZeroLength = 1 := by
  cases F with
  | constant _ => rfl
  | multiplicative _ => contradiction

end AdmissibleSimpleFactor

namespace AdmissibleFiltrationStep

/-- Closed-fibre connectedness of the kernel and étaleness of the quotient identify the two
stored admissible branches and feed the actual integral finite-flat Kummer rank-zero theorem. -/
theorem finrank_eq_zero_of_fppfKummer_closedFiberConnectedKernelEtaleQuotientInt
    {p : ℕ} [NeZero p]
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : AdmissibleFiltrationStep ℤ p G)
    (hkernelConnected : GeometricallyConnected
      ((FiniteFlatCommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod p))))).obj
          D.kernelPresentation.kernel).structureMap)
    (hquotientEtale : Etale
      ((FiniteFlatCommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod p))))).obj
          D.quotient).structureMap)
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) p).ker =
      p ^ torsionLength)
    (middleHZeroData : FinitePGroup.CertifiedData p (BasePoint G))
    (quotientHOneData : FinitePGroup.CertifiedData p D.quotient.FppfHOne.{0})
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) p).range) →* G.FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hp2 : p ≠ 2)
    (hbound : middleHZeroData.length + quotientHOneData.length ≤
      torsionLength + 1) :
    Module.finrank ℤ A = 0 := by
  have hkernelFactor : D.kernelFactor.IsMultiplicative :=
    D.kernelFactor.isMultiplicative_of_closedFiber_geometricallyConnected
      D.prime hkernelConnected
  have hquotientFactor : D.quotientFactor.IsConstant :=
    D.quotientFactor.isConstant_of_closedFiber_etale D.prime hquotientEtale
  apply D.finrank_eq_zero_of_fppfKummer_multiplicativeKernelInt
    hkernelFactor torsionLength hkernel middleHZeroData quotientHOneData
    kummer hkummer hp2
  rw [D.quotientFactor.hZeroLength_eq_one_of_isConstant hquotientFactor]
  exact hbound

/-- Genuine coefficient-five integral rank-zero consumer using only closed-fibre connectedness
and étaleness to identify the stored admissible factors. -/
theorem finrank_eq_zero_of_fppfKummer_closedFiberConnectedKernelEtaleQuotientIntAtFive
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : AdmissibleFiltrationStep ℤ 5 G)
    (hkernelConnected : GeometricallyConnected
      ((FiniteFlatCommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod 5))))).obj
          D.kernelPresentation.kernel).structureMap)
    (hquotientEtale : Etale
      ((FiniteFlatCommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod 5))))).obj
          D.quotient).structureMap)
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) 5).ker =
      5 ^ torsionLength)
    (middleHZeroData : FinitePGroup.CertifiedData 5 (BasePoint G))
    (quotientHOneData : FinitePGroup.CertifiedData 5 D.quotient.FppfHOne.{0})
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) 5).range) →* G.FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hbound : middleHZeroData.length + quotientHOneData.length ≤
      torsionLength + 1) :
    Module.finrank ℤ A = 0 :=
  D.finrank_eq_zero_of_fppfKummer_closedFiberConnectedKernelEtaleQuotientInt
    hkernelConnected hquotientEtale torsionLength hkernel middleHZeroData
    quotientHOneData kummer hkummer (by decide) hbound

/-- Genuine coefficient-eleven integral rank-zero consumer using only closed-fibre connectedness
and étaleness to identify the stored admissible factors. -/
theorem finrank_eq_zero_of_fppfKummer_closedFiberConnectedKernelEtaleQuotientIntAtEleven
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : AdmissibleFiltrationStep ℤ 11 G)
    (hkernelConnected : GeometricallyConnected
      ((FiniteFlatCommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod 11))))).obj
          D.kernelPresentation.kernel).structureMap)
    (hquotientEtale : Etale
      ((FiniteFlatCommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod 11))))).obj
          D.quotient).structureMap)
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) 11).ker =
      11 ^ torsionLength)
    (middleHZeroData : FinitePGroup.CertifiedData 11 (BasePoint G))
    (quotientHOneData : FinitePGroup.CertifiedData 11 D.quotient.FppfHOne.{0})
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) 11).range) →* G.FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hbound : middleHZeroData.length + quotientHOneData.length ≤
      torsionLength + 1) :
    Module.finrank ℤ A = 0 :=
  D.finrank_eq_zero_of_fppfKummer_closedFiberConnectedKernelEtaleQuotientInt
    hkernelConnected hquotientEtale torsionLength hkernel middleHZeroData
    quotientHOneData kummer hkummer (by decide) hbound

end AdmissibleFiltrationStep

end AlgebraicGeometry.FiniteFlatCommGroupScheme
