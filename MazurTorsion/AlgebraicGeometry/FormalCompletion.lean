/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.RingHom

/-!
# Maps of completed local rings

A local homomorphism `f : A →+* B` is continuous for the maximal-ideal-adic topologies, so it
induces a map from the completion of `A` to the completion of `B`.  The pinned Mathlib version
provides the inverse-limit lifting construction but does not yet bundle this differing-ideal
map.  This file constructs it from the compatible maps

`Â → B / m_B^n`.

For a morphism of schemes, applying the construction to the contravariant stalk map gives the
map on completed local rings used in the definition of a formal immersion.  No Noetherian
hypothesis is needed for this definition; such hypotheses enter only when deriving
surjectivity from a first-order cotangent criterion.
-/

namespace AlgebraicGeometry

universe u

open CategoryTheory Ideal

namespace LocalCompletion

/-- The completion of a local ring at its maximal ideal. -/
abbrev Ring (R : Type*) [CommRing R] [IsLocalRing R] :=
  AdicCompletion (IsLocalRing.maximalIdeal R) R

variable {A B : Type*} [CommRing A] [CommRing B]
  [IsLocalRing A] [IsLocalRing B]
variable (f : A →+* B) [IsLocalHom f]

/-- A local homomorphism sends the `n`th power of the source maximal ideal into the `n`th
power of the target maximal ideal. -/
lemma maximalIdeal_pow_le_comap (n : ℕ) :
    IsLocalRing.maximalIdeal A ^ n ≤
      (IsLocalRing.maximalIdeal B ^ n).comap f := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr
    (le_of_eq (IsLocalRing.maximalIdeal_comap f).symm)) n

/-- The map from the completed source to the `n`th infinitesimal quotient of the target. -/
noncomputable def quotientMap (n : ℕ) :
    Ring A →+* B ⧸ IsLocalRing.maximalIdeal B ^ n :=
  (Ideal.quotientMap (IsLocalRing.maximalIdeal B ^ n) f
      (maximalIdeal_pow_le_comap f n)).comp
    (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n).toRingHom

lemma quotientMap_compatible {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal B) h).comp
        (quotientMap f n) =
      quotientMap f m := by
  ext z
  apply AdicCompletion.induction_on (IsLocalRing.maximalIdeal A) A z
  intro a
  simp only [quotientMap, RingHom.coe_comp, Function.comp_apply,
    Ideal.Quotient.factorPow]
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
  rw [← map_sub]
  apply maximalIdeal_pow_le_comap f m
  have ha := (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
    (a.property h).symm
  simpa using ha

/-- The continuous map on maximal-ideal-adic completions induced by a local homomorphism. -/
noncomputable def map : Ring A →+* Ring B :=
  AdicCompletion.liftRingHom (IsLocalRing.maximalIdeal B)
    (quotientMap f) (quotientMap_compatible f)

/-- Evaluation of a completion map at finite level is the defining quotient map. -/
@[simp]
lemma evalₐ_map (n : ℕ) (z : Ring A) :
    AdicCompletion.evalₐ (IsLocalRing.maximalIdeal B) n (map f z) =
      quotientMap f n z :=
  AdicCompletion.evalₐ_liftRingHom _ _ _ _ _

/-- The completion map extends the original local homomorphism. -/
@[simp]
lemma map_of (a : A) :
    map f (AdicCompletion.of (IsLocalRing.maximalIdeal A) A a) =
      AdicCompletion.of (IsLocalRing.maximalIdeal B) B (f a) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  simp [map, quotientMap]

/-- Completion maps are covariantly functorial in local ring homomorphisms. -/
lemma map_comp
    {C : Type*} [CommRing C] [IsLocalRing C]
    (g : B →+* C) [IsLocalHom g] :
    map (g.comp f) = (map g).comp (map f) := by
  apply RingHom.ext
  intro z
  apply AdicCompletion.ext_evalₐ
  intro n
  change AdicCompletion.evalₐ (IsLocalRing.maximalIdeal C) n
      (map (g.comp f) z) =
    AdicCompletion.evalₐ (IsLocalRing.maximalIdeal C) n
      (map g (map f z))
  rw [evalₐ_map, evalₐ_map]
  simp only [quotientMap, RingHom.coe_comp, Function.comp_apply]
  change Ideal.quotientMap (IsLocalRing.maximalIdeal C ^ n) (g.comp f) _
      (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n z) =
    Ideal.quotientMap (IsLocalRing.maximalIdeal C ^ n) g _
      (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal B) n (map f z))
  rw [evalₐ_map]
  simp only [quotientMap, RingHom.coe_comp, Function.comp_apply]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n z)
  let qgf := Ideal.quotientMap (IsLocalRing.maximalIdeal C ^ n) (g.comp f)
    (maximalIdeal_pow_le_comap (g.comp f) n)
  let qf := Ideal.quotientMap (IsLocalRing.maximalIdeal B ^ n) f
    (maximalIdeal_pow_le_comap f n)
  let qg := Ideal.quotientMap (IsLocalRing.maximalIdeal C ^ n) g
    (maximalIdeal_pow_le_comap g n)
  change qgf (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n z) =
    qg (qf (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n z))
  calc
    qgf (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n z) =
        qgf (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ n) a) :=
      congrArg qgf ha.symm
    _ = qg (qf (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ n) a)) := by
      simp [qgf, qf, qg]
    _ = qg (qf (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n z)) :=
      congrArg (fun t ↦ qg (qf t)) ha

/-- Completing the identity homomorphism gives the identity.  This is the normalization
consumer for `LocalCompletion.map`. -/
@[simp]
lemma map_id :
    map (RingHom.id A) = RingHom.id (Ring A) := by
  apply RingHom.ext
  intro z
  apply AdicCompletion.ext_evalₐ
  intro n
  change AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n
      (map (RingHom.id A) z) =
    AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n z
  rw [map, AdicCompletion.evalₐ_liftRingHom]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n z)
  let q := Ideal.quotientMap (IsLocalRing.maximalIdeal A ^ n)
    (RingHom.id A) (maximalIdeal_pow_le_comap (RingHom.id A) n)
  change q (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n z) =
    AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n z
  calc
    q (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n z) =
        q (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ n) a) :=
      congrArg q ha.symm
    _ = Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ n) a := by
      simp [q]
    _ = AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n z := ha

end LocalCompletion

namespace Scheme

/-- The completed local ring of a scheme at a point. -/
abbrev CompletedStalk (Z : Scheme.{u}) (z : Z) : Type u :=
  LocalCompletion.Ring (Z.presheaf.stalk z)

namespace Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)

/-- The map on completed local rings induced contravariantly by a scheme morphism. -/
noncomputable def completedStalkMap :
    CompletedStalk Y (f x) →+* CompletedStalk X x :=
  LocalCompletion.map (f.stalkMap x).hom

/-- Maps on completed stalks are contravariantly functorial under composition of scheme
morphisms. -/
theorem completedStalkMap_comp
    {Z : Scheme.{u}} (g : Y ⟶ Z) :
    completedStalkMap (f ≫ g) x =
      (completedStalkMap f x).comp (completedStalkMap g (f x)) := by
  simp only [completedStalkMap, Scheme.Hom.stalkMap_comp]
  change LocalCompletion.map
      ((f.stalkMap x).hom.comp (g.stalkMap (f x)).hom) =
    (LocalCompletion.map (f.stalkMap x).hom).comp
      (LocalCompletion.map (g.stalkMap (f x)).hom)
  exact LocalCompletion.map_comp (g.stalkMap (f x)).hom (f.stalkMap x).hom

end Hom

end Scheme

/-- A scheme morphism is a formal immersion at `x` when its map on completed local rings at
`x` and `f(x)` is surjective. -/
def IsFormalImmersionAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) : Prop :=
  Function.Surjective (Scheme.Hom.completedStalkMap f x)

/-- Formal immersions at compatible points are stable under composition.  This is the
factorization interface for a modular curve mapping through its Jacobian to a quotient. -/
theorem IsFormalImmersionAt.comp
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {x : X}
    (hf : IsFormalImmersionAt f x)
    (hg : IsFormalImmersionAt g (f x)) :
    IsFormalImmersionAt (f ≫ g) x := by
  rw [IsFormalImmersionAt, Scheme.Hom.completedStalkMap_comp]
  change Function.Surjective (fun z ↦
    Scheme.Hom.completedStalkMap f x (Scheme.Hom.completedStalkMap g (f x) z))
  exact Function.Surjective.comp hf hg

end AlgebraicGeometry
