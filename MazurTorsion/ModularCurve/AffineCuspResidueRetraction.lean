/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.AffineCuspQExpansion

/-!
# Residue fields at a rational affine cusp

An affine section `Spec R → Spec T` is contravariantly an `R`-algebra
retraction `T →ₐ[R] R`.  If the inverse image of the closed point of
`Spec R` is the ambient prime underlying a selected special-fibre cusp, this
file proves that the ambient localized map at that cusp is surjective on
residue fields.

The proof does not assume a residue-field identification.  It localizes the
structural map and the retraction at the two identified primes.  Their
composite is the identity, so the structural map is surjective on residue
fields.  Naturality of localization along the represented affine morphism
then gives the required surjectivity for `Ideal.Fiber.ambientLocalizedMap`.

The final theorem is a genuine `Spec.map` formal-immersion consumer.  It
replaces the former ambient residue-field hypothesis by the rational affine
section and the exact closed-point equality.  The separate special-fibre
residue map remains explicit, since it belongs to the affine chart
calculation rather than to this ambient section argument.
-/

open Algebra TensorProduct AlgebraicGeometry

namespace IsLocalRing

universe u

variable {A B : Type u} [CommRing A] [CommRing B]
  [IsLocalRing A] [IsLocalRing B]

/-- A split local ring map is surjective on residue fields.

The induced map of the retraction is injective because it is a homomorphism
of fields.  Applying that injection reduces surjectivity to the retraction
identity itself. -/
theorem residueField_map_surjective_of_retraction
    (f : A →+* B) (r : B →+* A)
    [IsLocalHom f] [IsLocalHom r]
    (hretract : r.comp f = RingHom.id A) :
    Function.Surjective (ResidueField.map f) := by
  intro y
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective y
  refine ⟨ResidueField.map r (IsLocalRing.residue B b), ?_⟩
  apply (ResidueField.map r).injective
  simp only [ResidueField.map_residue]
  exact congrArg (IsLocalRing.residue A)
    (DFunLike.congr_fun hretract (r b))

end IsLocalRing

namespace Ideal.Fiber

universe u

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T]

/-- An `R`-algebra retraction at the selected closed point makes the
localized structural map surjective on residue fields.

The equality `hclosedPoint` is the exact geometric compatibility: the
ambient prime below `q` is the inverse image of `p` under the affine section.
It is stronger and more precise than merely supplying an unrelated rational
point of `Spec T`. -/
theorem algebraMapResidue_surjective_of_retraction
    (p : Ideal R) [p.IsPrime]
    (q : Ideal (p.Fiber T)) [q.IsPrime]
    (r : T →ₐ[R] R)
    (hclosedPoint : targetBasePrime p q = p.comap r.toRingHom) :
    Function.Surjective
      (IsLocalRing.ResidueField.map
        (Localization.localRingHom p (targetBasePrime p q)
          (algebraMap R T) (targetBasePrime_liesOver p q).over)) := by
  let qT := targetBasePrime p q
  let iLoc : Localization.AtPrime p →+* Localization.AtPrime qT :=
    Localization.localRingHom p qT (algebraMap R T)
      (targetBasePrime_liesOver p q).over
  let rLoc : Localization.AtPrime qT →+* Localization.AtPrime p :=
    Localization.localRingHom qT p r.toRingHom hclosedPoint
  letI : IsLocalHom iLoc :=
    Localization.isLocalHom_localRingHom p qT (algebraMap R T)
      (targetBasePrime_liesOver p q).over
  letI : IsLocalHom rLoc :=
    Localization.isLocalHom_localRingHom qT p r.toRingHom hclosedPoint
  have hretract : rLoc.comp iLoc =
      RingHom.id (Localization.AtPrime p) := by
    calc
      rLoc.comp iLoc =
          Localization.localRingHom p p (RingHom.id R)
            (Ideal.comap_id p).symm := by
        symm
        apply Localization.localRingHom_unique p p (RingHom.id R)
          (Ideal.comap_id p).symm
        intro x
        simp only [RingHom.comp_apply, rLoc, iLoc,
          Localization.localRingHom_to_map, RingHom.id_apply]
        congr 1
        change r (algebraMap R T x) = x
        simpa only [Algebra.algebraMap_self_apply] using r.commutes x
      _ = RingHom.id (Localization.AtPrime p) := by
        apply Localization.localRingHom_unique p p (RingHom.id R)
          (Ideal.comap_id p).symm
        intro x
        rfl
  exact IsLocalRing.residueField_map_surjective_of_retraction
    iLoc rLoc hretract

/-- A rational affine section through the selected fibre cusp discharges
ambient residue-field surjectivity for the represented affine morphism.

No second source-prime hypothesis is needed.  The equality of the source
prime with the comap of the target prime shows that the induced section
`r.comp g` meets the corresponding source point, while the localized
structural maps give the required naturality square. -/
theorem ambientResidue_surjective_of_retraction
    (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime]
    (r : T →ₐ[R] R)
    (hclosedPoint : targetBasePrime p q = p.comap r.toRingHom) :
    Function.Surjective
      (IsLocalRing.ResidueField.map (ambientLocalizedMap p g q)) := by
  let qS := sourceBasePrime p g q
  let qT := targetBasePrime p q
  let iS : Localization.AtPrime p →+* Localization.AtPrime qS :=
    Localization.localRingHom p qS (algebraMap R S)
      (sourceBasePrime_liesOver p g q).over
  let iT : Localization.AtPrime p →+* Localization.AtPrime qT :=
    Localization.localRingHom p qT (algebraMap R T)
      (targetBasePrime_liesOver p q).over
  let f := ambientLocalizedMap p g q
  letI : IsLocalHom iS :=
    Localization.isLocalHom_localRingHom p qS (algebraMap R S)
      (sourceBasePrime_liesOver p g q).over
  letI : IsLocalHom iT :=
    Localization.isLocalHom_localRingHom p qT (algebraMap R T)
      (targetBasePrime_liesOver p q).over
  have hf : f = Localization.localRingHom qS qT g.toRingHom
      (sourceBasePrime_eq_comap_toRingHom p g q) := by
    apply RingHom.ext
    intro x
    rfl
  have hbase : f.comp iS = iT := by
    symm
    apply Localization.localRingHom_unique p qT (algebraMap R T)
      (targetBasePrime_liesOver p q).over
    intro x
    simp only [RingHom.comp_apply, iS,
      Localization.localRingHom_to_map]
    rw [hf, Localization.localRingHom_to_map]
    congr 1
    change g (algebraMap R S x) = algebraMap R T x
    exact g.commutes x
  have hbaseResidue : IsLocalRing.ResidueField.map (f.comp iS) =
      IsLocalRing.ResidueField.map iT := by
    apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    simp only [IsLocalRing.ResidueField.map_residue]
    exact congrArg (IsLocalRing.residue (Localization.AtPrime qT))
      (DFunLike.congr_fun hbase a)
  have hiT : Function.Surjective
      (IsLocalRing.ResidueField.map iT) :=
    algebraMapResidue_surjective_of_retraction p q r hclosedPoint
  intro y
  obtain ⟨x, hx⟩ := hiT y
  refine ⟨IsLocalRing.ResidueField.map iS x, ?_⟩
  rw [IsLocalRing.ResidueField.map_map]
  exact (DFunLike.congr_fun hbaseResidue x).trans hx

end Ideal.Fiber

namespace MazurTorsion.ModularCurve.AffineCuspQExpansion

open Ideal.Fiber

universe u

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T]

/-- A unit first `q`-coefficient proves formal immersion at a rational affine
cusp without assuming ambient residue-field surjectivity.

The retraction `cuspRetraction` is the coordinate-ring form of the affine
cusp section.  `hcuspClosedPoint` ensures that it passes through the same
prime `q` used in the local `q`-expansion. -/
theorem isFormalImmersionAtSpecMap_of_unit_qExpansion_of_retraction
    (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime]
    [IsNoetherianRing S] [IsNoetherianRing T]
    [IsNoetherianRing (p.Fiber T)]
    (hresidueFiber : Function.Surjective
      (IsLocalRing.ResidueField.map (localizedRingMap p g q)))
    (qParameter : Localization.AtPrime q)
    (hmaximal : IsLocalRing.maximalIdeal (Localization.AtPrime q) =
      Ideal.span {qParameter})
    (hqLinear : qParameter ∉
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ 2)
    (sourceParameter :
      Localization.AtPrime (q.comap (map p g)))
    (hsourceMem : sourceParameter ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime (q.comap (map p g))))
    (unitCoefficient remainder : Localization.AtPrime q)
    (hunit : IsUnit unitCoefficient)
    (hremainder : remainder ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ 2)
    (hfirstOrder : localizedMap p g q sourceParameter =
      unitCoefficient * qParameter + remainder)
    (cuspRetraction : T →ₐ[R] R)
    (hcuspClosedPoint : targetBasePrime p q =
      p.comap cuspRetraction.toRingHom) :
    IsFormalImmersionAt (Spec.map (CommRingCat.ofHom g.toRingHom))
      (targetSpecPoint p q) :=
  isFormalImmersionAtSpecMap_of_unit_qExpansion p g q hresidueFiber
    qParameter hmaximal hqLinear sourceParameter hsourceMem unitCoefficient
    remainder hunit hremainder hfirstOrder
    (ambientResidue_surjective_of_retraction p g q cuspRetraction
      hcuspClosedPoint)

end MazurTorsion.ModularCurve.AffineCuspQExpansion
