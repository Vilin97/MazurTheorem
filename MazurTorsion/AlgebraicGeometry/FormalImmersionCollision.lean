/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FormalCompletion
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.AdicCompletion.Noetherian

/-!
# Separating local maps with a formal immersion

Mazur's formal-immersion argument uses more than the existence of a surjection on completed
local rings.  It uses that surjection to cancel the map from the quotient: two local points of
the modular curve whose images in the quotient agree must have the same local-ring map.

This file proves that cancellation statement.  The target local ring of the two points is
assumed separated for its maximal-ideal-adic topology; this is exactly what lets equality after
completion descend to equality before completion.  A Noetherian local ring, and in particular
a discrete valuation ring, satisfies this hypothesis.

The final theorem is a scheme-level consumer.  It applies the local cancellation result to the
actual morphisms from a local spectrum represented by the standard Mathlib maps
`Spec.map a ≫ X.fromSpecStalk x`.
-/

namespace AlgebraicGeometry

universe u

open CategoryTheory

namespace LocalCompletion

/-- The completion map depends only on the underlying local ring homomorphism, not on the
chosen proof that it is local. -/
lemma map_congr
    {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    (a b : A →+* B) [IsLocalHom a] [IsLocalHom b] (h : a = b) :
    map a = map b := by
  subst b
  rfl

end LocalCompletion

/-- A formal immersion separates local homomorphisms into a maximal-adically separated local
ring.  Equality only after restriction to the target stalk is enough.

This is the completed-local-ring cancellation at the heart of Mazur's collision argument. -/
theorem IsFormalImmersionAt.localHom_ext
    {X Y : Scheme.{u}} {f : X ⟶ Y} {x : X}
    {R : Type u} [CommRing R] [IsLocalRing R]
    [IsHausdorff (IsLocalRing.maximalIdeal R) R]
    (hf : IsFormalImmersionAt f x)
    (a b : X.presheaf.stalk x →+* R) [IsLocalHom a] [IsLocalHom b]
    (hrestrict : a.comp (f.stalkMap x).hom = b.comp (f.stalkMap x).hom) :
    a = b := by
  have hcompleted :
      (LocalCompletion.map a).comp (Scheme.Hom.completedStalkMap f x) =
        (LocalCompletion.map b).comp (Scheme.Hom.completedStalkMap f x) := by
    change
      (LocalCompletion.map a).comp (LocalCompletion.map (f.stalkMap x).hom) =
        (LocalCompletion.map b).comp (LocalCompletion.map (f.stalkMap x).hom)
    rw [← LocalCompletion.map_comp (f.stalkMap x).hom a,
      ← LocalCompletion.map_comp (f.stalkMap x).hom b]
    exact LocalCompletion.map_congr _ _ hrestrict
  have habCompletion : LocalCompletion.map a = LocalCompletion.map b := by
    apply RingHom.ext
    intro z
    obtain ⟨w, rfl⟩ := hf z
    exact DFunLike.congr_fun hcompleted w
  apply RingHom.ext
  intro z
  apply AdicCompletion.of_injective (IsLocalRing.maximalIdeal R) R
  simpa only [LocalCompletion.map_of] using
    DFunLike.congr_fun habCompletion
      (AdicCompletion.of
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) z)

/-- The Noetherian specialization of completed-local-ring cancellation. -/
theorem IsFormalImmersionAt.localHom_ext_of_isNoetherian
    {X Y : Scheme.{u}} {f : X ⟶ Y} {x : X}
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hf : IsFormalImmersionAt f x)
    (a b : X.presheaf.stalk x →+* R) [IsLocalHom a] [IsLocalHom b]
    (hrestrict : a.comp (f.stalkMap x).hom = b.comp (f.stalkMap x).hom) :
    a = b :=
  hf.localHom_ext a b hrestrict

/-- Scheme-level collision consumer for local points written in Mathlib's canonical normal
form.  A formal immersion at `x` makes two maps from a separated local spectrum equal as soon
as their local homomorphisms agree after restriction along `f`.

Every morphism from the spectrum of a local ring has this form by
`AlgebraicGeometry.SpecToEquivOfLocalRing`. -/
theorem IsFormalImmersionAt.specMap_fromStalk_ext
    {X Y : Scheme.{u}} {f : X ⟶ Y} {x : X}
    {R : Type u} [CommRing R] [IsLocalRing R]
    [IsHausdorff (IsLocalRing.maximalIdeal R) R]
    (hf : IsFormalImmersionAt f x)
    (a b : X.presheaf.stalk x →+* R) [IsLocalHom a] [IsLocalHom b]
    (hrestrict : a.comp (f.stalkMap x).hom = b.comp (f.stalkMap x).hom) :
    Spec.map (CommRingCat.ofHom a) ≫ X.fromSpecStalk x =
      Spec.map (CommRingCat.ofHom b) ≫ X.fromSpecStalk x := by
  rw [hf.localHom_ext a b hrestrict]

/-- Noetherian local spectra satisfy the separatedness required by the scheme-level collision
consumer. -/
theorem IsFormalImmersionAt.specMap_fromStalk_ext_of_isNoetherian
    {X Y : Scheme.{u}} {f : X ⟶ Y} {x : X}
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hf : IsFormalImmersionAt f x)
    (a b : X.presheaf.stalk x →+* R) [IsLocalHom a] [IsLocalHom b]
    (hrestrict : a.comp (f.stalkMap x).hom = b.comp (f.stalkMap x).hom) :
    Spec.map (CommRingCat.ofHom a) ≫ X.fromSpecStalk x =
      Spec.map (CommRingCat.ofHom b) ≫ X.fromSpecStalk x :=
  hf.specMap_fromStalk_ext a b hrestrict

/-- The local collision theorem for arbitrary morphisms from a local spectrum.  If the two
morphisms meet at the closed point and their induced local homomorphisms agree after restriction
along a formal immersion, then they are equal.  Maximal-adic separatedness is the precise
target-ring hypothesis used to descend equality from completed local rings. -/
theorem IsFormalImmersionAt.spec_ext_of_stalkClosedPointTo
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {R : Type u} [CommRing R] [IsLocalRing R]
    [IsHausdorff (IsLocalRing.maximalIdeal R) R]
    (g h : Spec (.of R) ⟶ X)
    (hpoint : g (IsLocalRing.closedPoint R) = h (IsLocalRing.closedPoint R))
    (hf : IsFormalImmersionAt f (g (IsLocalRing.closedPoint R)))
    (hrestrict :
      (Scheme.stalkClosedPointTo g).hom.comp
          (f.stalkMap (g (IsLocalRing.closedPoint R))).hom =
        ((X.presheaf.stalkCongr (.of_eq hpoint)).hom ≫
          Scheme.stalkClosedPointTo h).hom.comp
            (f.stalkMap (g (IsLocalRing.closedPoint R))).hom) :
    g = h := by
  letI : IsLocalHom
      (X.presheaf.stalkCongr (.of_eq hpoint)).hom.hom := by
    rw [← Iso.commRingCatIsoToRingEquiv_toRingHom]
    infer_instance
  letI : IsLocalHom
      ((X.presheaf.stalkCongr (.of_eq hpoint)).hom ≫
        Scheme.stalkClosedPointTo h).hom := by
    change IsLocalHom
      ((Scheme.stalkClosedPointTo h).hom.comp
        (X.presheaf.stalkCongr (.of_eq hpoint)).hom.hom)
    infer_instance
  have hlocal := hf.localHom_ext
    (Scheme.stalkClosedPointTo g).hom
    ((X.presheaf.stalkCongr (.of_eq hpoint)).hom ≫
      Scheme.stalkClosedPointTo h).hom hrestrict
  apply (SpecToEquivOfLocalRing X (.of R)).injective
  apply (SpecToEquivOfLocalRing_eq_iff (X := X) (R := .of R)).mpr
  exact ⟨hpoint, CommRingCat.hom_ext hlocal⟩

/-- Noetherian local rings supply the separatedness needed by
`spec_ext_of_stalkClosedPointTo`. -/
theorem IsFormalImmersionAt.spec_ext_of_stalkClosedPointTo_of_isNoetherian
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (g h : Spec (.of R) ⟶ X)
    (hpoint : g (IsLocalRing.closedPoint R) = h (IsLocalRing.closedPoint R))
    (hf : IsFormalImmersionAt f (g (IsLocalRing.closedPoint R)))
    (hrestrict :
      (Scheme.stalkClosedPointTo g).hom.comp
          (f.stalkMap (g (IsLocalRing.closedPoint R))).hom =
        ((X.presheaf.stalkCongr (.of_eq hpoint)).hom ≫
          Scheme.stalkClosedPointTo h).hom.comp
            (f.stalkMap (g (IsLocalRing.closedPoint R))).hom) :
    g = h :=
  hf.spec_ext_of_stalkClosedPointTo g h hpoint hrestrict

end AlgebraicGeometry
