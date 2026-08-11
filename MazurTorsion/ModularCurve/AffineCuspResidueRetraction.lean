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
packages the rational affine section, its section law, and its exact fibre
point in one object.  The resulting retraction supplies ambient residue-field
surjectivity, and the checked compatible-quotient comparison derives the
special-fibre residue surjection, so neither residue map remains an
independent premise.
-/

open Algebra TensorProduct AlgebraicGeometry CategoryTheory

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

/-- An affine section of a structural morphism.

Unlike `AffineSectionAtFiberPoint`, this structure does not ask the caller
to choose a prime of every special fibre.  A prime is instead constructed
canonically below as the kernel of the section after base change to the
residue field. -/
structure AffineStructuralSection where
  toSpec : Spec (.of R) ⟶ Spec (.of T)
  isSection :
    toSpec ≫ Spec.map (CommRingCat.ofHom (algebraMap R T)) = 𝟙 _

namespace AffineStructuralSection

/-- The coordinate-ring retraction contravariantly represented by an affine
structural section. -/
noncomputable def retraction
    (C : AffineStructuralSection (R := R) (T := T)) : T →ₐ[R] R where
  toRingHom := (Spec.preimage C.toSpec).hom
  commutes' r := by
    change (Spec.preimage C.toSpec).hom (algebraMap R T r) = r
    have hcomp :
        (CommRingCat.ofHom (algebraMap R T)) ≫
          Spec.preimage C.toSpec = 𝟙 _ := by
      rw [← Spec.preimage_map
        (φ := CommRingCat.ofHom (algebraMap R T))]
      rw [← Spec.preimage_comp, C.isSection, Spec.preimage_id]
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hcomp) r

/-- Base change of an affine structural section to the residue field at
`p`. -/
noncomputable def fiberRetraction
    (p : Ideal R) [p.IsPrime]
    (C : AffineStructuralSection (R := R) (T := T)) :
    p.Fiber T →ₐ[p.ResidueField] p.ResidueField :=
  Algebra.TensorProduct.lift (AlgHom.id _ _)
    ((Algebra.ofId R p.ResidueField).comp C.retraction)
    fun _ _ ↦ Commute.all _ _

/-- The base-changed section is surjective: the left residue-field factor
maps identically to the target residue field. -/
theorem fiberRetraction_surjective
    (p : Ideal R) [p.IsPrime]
    (C : AffineStructuralSection (R := R) (T := T)) :
    Function.Surjective (C.fiberRetraction p) := by
  intro k
  refine ⟨Algebra.TensorProduct.includeLeft
    (R := R) (S := p.ResidueField) (B := T) k, ?_⟩
  simp [fiberRetraction]

/-- The point of the special fibre selected canonically by an affine
structural section. -/
noncomputable def fiberPrime
    (p : Ideal R) [p.IsPrime]
    (C : AffineStructuralSection (R := R) (T := T)) :
    Ideal (p.Fiber T) :=
  RingHom.ker (C.fiberRetraction p).toRingHom

instance fiberPrime_isPrime
    (p : Ideal R) [p.IsPrime]
    (C : AffineStructuralSection (R := R) (T := T)) :
    (C.fiberPrime p).IsPrime :=
  RingHom.ker_isPrime _

/-- The canonical fibre prime is maximal because its residue evaluation is
surjective onto the field `κ(p)`. -/
instance fiberPrime_isMaximal
    (p : Ideal R) [p.IsPrime]
    (C : AffineStructuralSection (R := R) (T := T)) :
    (C.fiberPrime p).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (C.fiberRetraction_surjective p)

/-- The point selected by a structural section is a closed point of the
affine special fibre. -/
theorem isClosed_fiberPoint
    (p : Ideal R) [p.IsPrime]
    (C : AffineStructuralSection (R := R) (T := T)) :
    IsClosed
      ({(show Spec (.of (p.Fiber T)) from
        ⟨C.fiberPrime p, inferInstance⟩)} : Set (Spec (.of (p.Fiber T)))) :=
  (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 inferInstance

/-- The ambient prime under the canonical fibre point is exactly the
inverse image of the base prime under the section retraction. -/
theorem targetBasePrime_fiberPrime
    (p : Ideal R) [p.IsPrime]
    (C : AffineStructuralSection (R := R) (T := T)) :
    targetBasePrime p (C.fiberPrime p) =
      p.comap C.retraction.toRingHom := by
  ext t
  simp [targetBasePrime, fiberPrime, fiberRetraction,
    Ideal.algebraMap_residueField_eq_zero]

/-- The structural section meets its canonically constructed special-fibre
point. -/
theorem atPrime
    (p : Ideal R) [p.IsPrime]
    (C : AffineStructuralSection (R := R) (T := T)) :
    C.toSpec (show Spec (.of R) from ⟨p, inferInstance⟩) =
      targetSpecPoint p (C.fiberPrime p) := by
  rw [← Spec.map_preimage C.toSpec]
  apply PrimeSpectrum.ext
  change p.comap (Spec.preimage C.toSpec).hom =
    targetBasePrime p (C.fiberPrime p)
  exact (C.targetBasePrime_fiberPrime p).symm

end AffineStructuralSection

/-- A section of an affine structural morphism that meets a specified point
of the special fibre.

The two compatibility fields prevent the geometric section and the selected
fibre prime from being supplied independently.  Contravariance of `Spec`
then produces the coordinate-ring retraction used by the residue-field
argument below. -/
structure AffineSectionAtFiberPoint
    (p : Ideal R) [p.IsPrime]
    (q : Ideal (p.Fiber T)) [q.IsPrime] where
  toSpec : Spec (.of R) ⟶ Spec (.of T)
  isSection :
    toSpec ≫ Spec.map (CommRingCat.ofHom (algebraMap R T)) = 𝟙 _
  atPrime :
    toSpec (show Spec (.of R) from ⟨p, inferInstance⟩) =
      targetSpecPoint p q

namespace AffineSectionAtFiberPoint

/-- The algebra retraction contravariantly represented by an affine
section. -/
noncomputable def retraction
    (p : Ideal R) [p.IsPrime]
    (q : Ideal (p.Fiber T)) [q.IsPrime]
    (C : AffineSectionAtFiberPoint p q) : T →ₐ[R] R where
  toRingHom := (Spec.preimage C.toSpec).hom
  commutes' r := by
    change (Spec.preimage C.toSpec).hom (algebraMap R T r) = r
    have hcomp :
        (CommRingCat.ofHom (algebraMap R T)) ≫
          Spec.preimage C.toSpec = 𝟙 _ := by
      rw [← Spec.preimage_map
        (φ := CommRingCat.ofHom (algebraMap R T))]
      rw [← Spec.preimage_comp, C.isSection, Spec.preimage_id]
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hcomp) r

/-- The retraction extracted from the section meets precisely the ambient
prime underlying the selected special-fibre point. -/
theorem targetBasePrime_eq_comap_retraction
    (p : Ideal R) [p.IsPrime]
    (q : Ideal (p.Fiber T)) [q.IsPrime]
    (C : AffineSectionAtFiberPoint p q) :
    targetBasePrime p q = p.comap (C.retraction p q).toRingHom := by
  have hmap : Spec.map (Spec.preimage C.toSpec) = C.toSpec :=
    Spec.map_preimage C.toSpec
  have hpoint :
      (Spec.map (Spec.preimage C.toSpec))
        (show Spec (.of R) from ⟨p, inferInstance⟩) =
        targetSpecPoint p q := by
    rw [hmap]
    exact C.atPrime
  exact (congrArg PrimeSpectrum.asIdeal hpoint).symm

end AffineSectionAtFiberPoint

namespace AffineStructuralSection

/-- A structural section, together with its canonical closed fibre point,
supplies the point-compatible section package used by the affine
formal-immersion consumer. -/
noncomputable def atFiberPoint
    (p : Ideal R) [p.IsPrime]
    (C : AffineStructuralSection (R := R) (T := T)) :
    AffineSectionAtFiberPoint p (C.fiberPrime p) where
  toSpec := C.toSpec
  isSection := C.isSection
  atPrime := C.atPrime p

end AffineStructuralSection

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

/-- A genuine affine section through the selected fibre point supplies the
ambient residue-field surjection.  Unlike the retraction-level adapter, this
theorem requires the section law and point compatibility in one geometric
object. -/
theorem ambientResidue_surjective_of_section
    (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime]
    (C : AffineSectionAtFiberPoint p q) :
    Function.Surjective
      (IsLocalRing.ResidueField.map (ambientLocalizedMap p g q)) :=
  ambientResidue_surjective_of_retraction p g q (C.retraction p q)
    (C.targetBasePrime_eq_comap_retraction p q)

end Ideal.Fiber

namespace MazurTorsion.ModularCurve.AffineCuspQExpansion

open Ideal.Fiber

universe u

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T]

/-- A unit first `q`-coefficient proves formal immersion at a rational affine
cusp without assuming either residue-field surjectivity.

The retraction `cuspRetraction` is the coordinate-ring form of the affine
cusp section.  `hcuspClosedPoint` ensures that it passes through the same
prime `q` used in the local `q`-expansion. -/
theorem isFormalImmersionAtSpecMap_of_unit_qExpansion_of_retraction
    (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime]
    [IsNoetherianRing S] [IsNoetherianRing T]
    [IsNoetherianRing (p.Fiber T)]
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
      (targetSpecPoint p q) := by
  have hresidueAmbient : Function.Surjective
      (IsLocalRing.ResidueField.map (ambientLocalizedMap p g q)) :=
    ambientResidue_surjective_of_retraction p g q cuspRetraction
      hcuspClosedPoint
  have hresidueFiber : Function.Surjective
      (IsLocalRing.ResidueField.map (localizedRingMap p g q)) :=
    localizedResidueFieldMap_surjective_of_ambient p g q hresidueAmbient
  exact isFormalImmersionAtSpecMap_of_unit_qExpansion p g q hresidueFiber
    qParameter hmaximal hqLinear sourceParameter hsourceMem unitCoefficient
    remainder hunit hremainder hfirstOrder hresidueAmbient

/-- A nonzero Hecke eigen-expansion proves formal immersion at a rational
affine cusp without independent residue-field hypotheses.

The affine cusp retraction supplies ambient residue-field surjectivity.  The
checked affine-fibre quotient comparison then supplies the special-fibre
surjectivity used by the degree-one cotangent argument. -/
theorem isFormalImmersionAtSpecMap_of_heckeEigen_qExpansion_of_retraction
    (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime]
    [IsNoetherianRing S] [IsNoetherianRing T]
    [IsNoetherianRing (p.Fiber T)]
    (qParameter : Localization.AtPrime q)
    (hmaximal : IsLocalRing.maximalIdeal (Localization.AtPrime q) =
      Ideal.span {qParameter})
    (hqLinear : qParameter ∉
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ 2)
    (sourceParameter :
      Localization.AtPrime (q.comap (map p g)))
    (hsourceMem : sourceParameter ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime (q.comap (map p g))))
    (qCoordinate :
      LocalCompletion.Ring (Localization.AtPrime q) ≃+*
        PowerSeries (IsLocalRing.ResidueField (Localization.AtPrime q)))
    (Q : PowerSeries
      (IsLocalRing.ResidueField (Localization.AtPrime q)))
    (hqExpansion :
      qCoordinate
          (completionRingHom (Localization.AtPrime q)
            (localizedMap p g q sourceParameter)) = Q)
    (hQ : Q ≠ 0)
    (hecke : ℕ → Module.End
      (IsLocalRing.ResidueField (Localization.AtPrime q))
      (PowerSeries
        (IsLocalRing.ResidueField (Localization.AtPrime q))))
    (eigenvalue : ℕ →
      IsLocalRing.ResidueField (Localization.AtPrime q))
    (hfirst : ∀ n, PowerSeries.coeff 1 (hecke n Q) =
      PowerSeries.coeff n Q)
    (heigen : ∀ n, hecke n Q = eigenvalue n • Q)
    (cuspRetraction : T →ₐ[R] R)
    (hcuspClosedPoint : targetBasePrime p q =
      p.comap cuspRetraction.toRingHom) :
    IsFormalImmersionAt (Spec.map (CommRingCat.ofHom g.toRingHom))
      (targetSpecPoint p q) :=
  isFormalImmersionAtSpecMap_of_heckeEigen_qExpansion p g q qParameter
    hmaximal hqLinear sourceParameter hsourceMem qCoordinate Q hqExpansion
    hQ hecke eigenvalue hfirst heigen
    (ambientResidue_surjective_of_retraction p g q cuspRetraction
      hcuspClosedPoint)

/-- A nonzero Hecke eigen-expansion proves formal immersion at the point of
a genuine affine section.

The section law canonically determines the coordinate-ring retraction, and
the point field identifies its inverse image of the base prime.  Thus the
caller cannot mix a geometric cusp section with an unrelated algebra
retraction. -/
theorem isFormalImmersionAtSpecMap_of_heckeEigen_qExpansion_of_section
    (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime]
    [IsNoetherianRing S] [IsNoetherianRing T]
    [IsNoetherianRing (p.Fiber T)]
    (qParameter : Localization.AtPrime q)
    (hmaximal : IsLocalRing.maximalIdeal (Localization.AtPrime q) =
      Ideal.span {qParameter})
    (hqLinear : qParameter ∉
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ 2)
    (sourceParameter :
      Localization.AtPrime (q.comap (map p g)))
    (hsourceMem : sourceParameter ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime (q.comap (map p g))))
    (qCoordinate :
      LocalCompletion.Ring (Localization.AtPrime q) ≃+*
        PowerSeries (IsLocalRing.ResidueField (Localization.AtPrime q)))
    (Q : PowerSeries
      (IsLocalRing.ResidueField (Localization.AtPrime q)))
    (hqExpansion :
      qCoordinate
          (completionRingHom (Localization.AtPrime q)
            (localizedMap p g q sourceParameter)) = Q)
    (hQ : Q ≠ 0)
    (hecke : ℕ → Module.End
      (IsLocalRing.ResidueField (Localization.AtPrime q))
      (PowerSeries
        (IsLocalRing.ResidueField (Localization.AtPrime q))))
    (eigenvalue : ℕ →
      IsLocalRing.ResidueField (Localization.AtPrime q))
    (hfirst : ∀ n, PowerSeries.coeff 1 (hecke n Q) =
      PowerSeries.coeff n Q)
    (heigen : ∀ n, hecke n Q = eigenvalue n • Q)
    (C : AffineSectionAtFiberPoint p q) :
    IsFormalImmersionAt (Spec.map (CommRingCat.ofHom g.toRingHom))
      (targetSpecPoint p q) :=
  isFormalImmersionAtSpecMap_of_heckeEigen_qExpansion p g q qParameter
    hmaximal hqLinear sourceParameter hsourceMem qCoordinate Q hqExpansion
    hQ hecke eigenvalue hfirst heigen
    (ambientResidue_surjective_of_section p g q C)

/-- A structural affine section canonically selects the special-fibre prime
at which its Hecke expansion proves formal immersion.

The fibre prime is the kernel of the base-changed section.  Consequently the
caller no longer supplies either that prime or a proof that the section meets
it; both are derived from the represented section itself. -/
theorem
    isFormalImmersionAtSpecMap_of_heckeEigen_qExpansion_of_structuralSection
    (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T)
    (C : AffineStructuralSection (R := R) (T := T))
    [IsNoetherianRing S] [IsNoetherianRing T]
    [IsNoetherianRing (p.Fiber T)]
    (qParameter : Localization.AtPrime (C.fiberPrime p))
    (hmaximal :
      IsLocalRing.maximalIdeal
          (Localization.AtPrime (C.fiberPrime p)) =
        Ideal.span {qParameter})
    (hqLinear : qParameter ∉
      IsLocalRing.maximalIdeal
          (Localization.AtPrime (C.fiberPrime p)) ^ 2)
    (sourceParameter : Localization.AtPrime
      ((C.fiberPrime p).comap (map p g)))
    (hsourceMem : sourceParameter ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime ((C.fiberPrime p).comap (map p g))))
    (qCoordinate :
      LocalCompletion.Ring
          (Localization.AtPrime (C.fiberPrime p)) ≃+*
        PowerSeries
          (IsLocalRing.ResidueField
            (Localization.AtPrime (C.fiberPrime p))))
    (Q : PowerSeries
      (IsLocalRing.ResidueField
        (Localization.AtPrime (C.fiberPrime p))))
    (hqExpansion :
      qCoordinate
          (completionRingHom
            (Localization.AtPrime (C.fiberPrime p))
            (localizedMap p g (C.fiberPrime p) sourceParameter)) = Q)
    (hQ : Q ≠ 0)
    (hecke : ℕ → Module.End
      (IsLocalRing.ResidueField
        (Localization.AtPrime (C.fiberPrime p)))
      (PowerSeries
        (IsLocalRing.ResidueField
          (Localization.AtPrime (C.fiberPrime p)))))
    (eigenvalue : ℕ →
      IsLocalRing.ResidueField
        (Localization.AtPrime (C.fiberPrime p)))
    (hfirst : ∀ n, PowerSeries.coeff 1 (hecke n Q) =
      PowerSeries.coeff n Q)
    (heigen : ∀ n, hecke n Q = eigenvalue n • Q) :
    IsFormalImmersionAt (Spec.map (CommRingCat.ofHom g.toRingHom))
      (targetSpecPoint p (C.fiberPrime p)) :=
  isFormalImmersionAtSpecMap_of_heckeEigen_qExpansion_of_section
    p g (C.fiberPrime p) qParameter hmaximal hqLinear sourceParameter
    hsourceMem qCoordinate Q hqExpansion hQ hecke eigenvalue hfirst heigen
    (C.atFiberPoint p)

/-- A structural cusp section and an intrinsic DVR uniformizer prove formal
immersion at the canonically selected special-fibre point.

The section constructs the fibre prime and both residue-field comparisons.
The DVR and irreducibility hypotheses derive the maximal-ideal generator and
nonzero cotangent class, so neither ideal-theoretic conclusion is part of the
public input. -/
theorem
    isFormalImmersionAtSpecMap_of_heckeEigen_qExpansion_of_dvrUniformizer_of_structuralSection
    (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T)
    (C : AffineStructuralSection (R := R) (T := T))
    [IsNoetherianRing S] [IsNoetherianRing T]
    [IsNoetherianRing (p.Fiber T)]
    [IsDomain (Localization.AtPrime (C.fiberPrime p))]
    [IsDiscreteValuationRing
      (Localization.AtPrime (C.fiberPrime p))]
    (qParameter : Localization.AtPrime (C.fiberPrime p))
    (hqParameter : Irreducible qParameter)
    (sourceParameter : Localization.AtPrime
      ((C.fiberPrime p).comap (map p g)))
    (hsourceMem : sourceParameter ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime ((C.fiberPrime p).comap (map p g))))
    (qCoordinate :
      LocalCompletion.Ring
          (Localization.AtPrime (C.fiberPrime p)) ≃+*
        PowerSeries
          (IsLocalRing.ResidueField
            (Localization.AtPrime (C.fiberPrime p))))
    (Q : PowerSeries
      (IsLocalRing.ResidueField
        (Localization.AtPrime (C.fiberPrime p))))
    (hqExpansion :
      qCoordinate
          (completionRingHom
            (Localization.AtPrime (C.fiberPrime p))
            (localizedMap p g (C.fiberPrime p) sourceParameter)) = Q)
    (hQ : Q ≠ 0)
    (hecke : ℕ → Module.End
      (IsLocalRing.ResidueField
        (Localization.AtPrime (C.fiberPrime p)))
      (PowerSeries
        (IsLocalRing.ResidueField
          (Localization.AtPrime (C.fiberPrime p)))))
    (eigenvalue : ℕ →
      IsLocalRing.ResidueField
        (Localization.AtPrime (C.fiberPrime p)))
    (hfirst : ∀ n, PowerSeries.coeff 1 (hecke n Q) =
      PowerSeries.coeff n Q)
    (heigen : ∀ n, hecke n Q = eigenvalue n • Q) :
    IsFormalImmersionAt (Spec.map (CommRingCat.ofHom g.toRingHom))
      (targetSpecPoint p (C.fiberPrime p)) :=
  isFormalImmersionAtSpecMap_of_heckeEigen_qExpansion_of_dvrUniformizer
    p g (C.fiberPrime p) qParameter hqParameter sourceParameter
    hsourceMem qCoordinate Q hqExpansion hQ hecke eigenvalue hfirst heigen
    (ambientResidue_surjective_of_section p g (C.fiberPrime p)
      (C.atFiberPoint p))

/-- An explicitly computed nonzero linear q-coefficient proves formal
immersion at a structural cusp with DVR local ring.

The structural section supplies both residue-field surjections, while the
DVR uniformizer supplies the one-dimensional source cotangent space.  The
only quotient-side calculation is the displayed completed expansion and its
computed degree-one coefficient. -/
theorem
    isFormalImmersionAtSpecMap_of_explicit_qExpansion_of_structuralSection_dvr
    {K : Type u} [Field K]
    (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T)
    (C : AffineStructuralSection (R := R) (T := T))
    [IsNoetherianRing S] [IsNoetherianRing T]
    [IsNoetherianRing (p.Fiber T)]
    [IsDomain (Localization.AtPrime (C.fiberPrime p))]
    [IsDiscreteValuationRing
      (Localization.AtPrime (C.fiberPrime p))]
    (qParameter : Localization.AtPrime (C.fiberPrime p))
    (hqParameter : Irreducible qParameter)
    (sourceParameter : Localization.AtPrime
      ((C.fiberPrime p).comap (map p g)))
    (hsourceMem : sourceParameter ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime ((C.fiberPrime p).comap (map p g))))
    (qCoordinate :
      LocalCompletion.Ring
          (Localization.AtPrime (C.fiberPrime p)) ≃+*
        PowerSeries K)
    (Q : PowerSeries K)
    (hqExpansion :
      qCoordinate
          (completionRingHom
            (Localization.AtPrime (C.fiberPrime p))
            (localizedMap p g (C.fiberPrime p) sourceParameter)) = Q)
    (hcoeff : PowerSeries.coeff 1 Q ≠ 0) :
    IsFormalImmersionAt (Spec.map (CommRingCat.ofHom g.toRingHom))
      (targetSpecPoint p (C.fiberPrime p)) := by
  have hresidueAmbient : Function.Surjective
      (IsLocalRing.ResidueField.map
        (ambientLocalizedMap p g (C.fiberPrime p))) :=
    ambientResidue_surjective_of_section p g (C.fiberPrime p)
      (C.atFiberPoint p)
  have hresidueFiber : Function.Surjective
      (IsLocalRing.ResidueField.map
        (localizedRingMap p g (C.fiberPrime p))) :=
    localizedResidueFieldMap_surjective_of_ambient p g (C.fiberPrime p)
      hresidueAmbient
  obtain ⟨detectedVector, hdetected⟩ :=
    exists_detectedVector_of_qExpansion_coeff_one_ne_zero p g
      (C.fiberPrime p) sourceParameter hsourceMem qCoordinate Q hqExpansion
      hcoeff
  exact isFormalImmersionAtSpecMap_of_qParameter p g (C.fiberPrime p)
    hresidueFiber qParameter hqParameter.maximalIdeal_eq
    (irreducible_not_mem_maximalIdeal_sq hqParameter) detectedVector hdetected
    hresidueAmbient

end MazurTorsion.ModularCurve.AffineCuspQExpansion
