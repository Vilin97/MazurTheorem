/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FormalImmersionAffineFiber
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Affine-fibre calculations on affine-scheme stalks

This file identifies the local-ring map constructed in
`FormalImmersionAffineFiber` with the actual stalk map of an affine scheme
morphism.  A point `q` of the special fibre determines an ambient prime in
the target algebra.  Under Mathlib's canonical affine stalk/localization
isomorphisms, the stalk map of `Spec.map g` at this point is
`Ideal.Fiber.ambientLocalizedMap p g q`.

There is one genuine transport in the source localization.  The prime found
by first mapping `q` along the affine-fibre map is propositionally, rather
than definitionally, the inverse image of the target ambient prime.  The
equivalence `sourceLocalizationEquiv` records exactly this equality-induced
cast.

The final consumers transport the already checked affine-fibre degree-one
cotangent certificate to `IsFormalImmersionAt` for `Spec.map g`.  The first
version exposes the precise finite-module and residue-surjectivity inputs.
The Noetherian version discharges the finite-module inputs by typeclass
inference, while keeping residue surjectivity explicit.
-/

open AlgebraicGeometry CategoryTheory

namespace Ideal.Fiber

universe u

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T]

/-- The ambient target prime underlying a prime of the affine fibre. -/
noncomputable abbrev targetPrime (p : Ideal R) [p.IsPrime]
    (q : Ideal (p.Fiber T)) [q.IsPrime] : PrimeSpectrum T :=
  ⟨targetBasePrime p q, inferInstance⟩

/-- The ambient target prime, regarded as an actual point of `Spec T`. -/
noncomputable abbrev targetSpecPoint (p : Ideal R) [p.IsPrime]
    (q : Ideal (p.Fiber T)) [q.IsPrime] : Spec (.of T) :=
  targetPrime p q

/-- The equality-induced equivalence from the source localization used by
`Spec.map` to the source localization used by `ambientLocalizedMap`. -/
noncomputable def sourceLocalizationEquiv (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime] :
    Localization.AtPrime ((targetBasePrime p q).comap g.toRingHom) ≃+*
      Localization.AtPrime (sourceBasePrime p g q) :=
  RingEquiv.cast (by
    ext x
    simp only [Ideal.mem_primeCompl_iff]
    rw [sourceBasePrime_eq_comap_toRingHom p g q])

/-- After the equality-induced source-localization transport, the ambient
localized map is Mathlib's canonical localized map attached to `g`. -/
theorem sourceLocalizationEquiv_comp_ambientLocalizedMap
    (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime] :
    (ambientLocalizedMap p g q).comp
        (sourceLocalizationEquiv p g q).toRingHom =
      Localization.localRingHom
        ((targetBasePrime p q).comap g.toRingHom)
        (targetBasePrime p q) g.toRingHom rfl := by
  symm
  apply Localization.localRingHom_unique
  intro x
  change ambientLocalizedMap p g q
      (sourceLocalizationEquiv p g q
        (algebraMap S
          (Localization.AtPrime
            ((targetBasePrime p q).comap g.toRingHom)) x)) = _
  unfold sourceLocalizationEquiv
  rw [RingEquiv.cast_apply]
  change Localization.localRingHom (sourceBasePrime p g q)
      (targetBasePrime p q) g.toRingHom
        (sourceBasePrime_eq_comap_toRingHom p g q)
      (algebraMap S
        (Localization.AtPrime (sourceBasePrime p g q)) x) = _
  exact Localization.localRingHom_to_map _ _ _ _ x

/-- The canonical localization map and the ambient localized map, packaged as
isomorphic arrows.  The source isomorphism is the only nontrivial transport. -/
noncomputable def localizedMapArrowIso (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime] :
    Arrow.mk (CommRingCat.ofHom
        (Localization.localRingHom
          ((targetBasePrime p q).comap g.toRingHom)
          (targetBasePrime p q) g.toRingHom rfl)) ≅
      Arrow.mk (CommRingCat.ofHom (ambientLocalizedMap p g q)) :=
  Arrow.isoMk (sourceLocalizationEquiv p g q).toCommRingCatIso
    (Iso.refl _) (by
      have hlocal :
          (sourceLocalizationEquiv p g q).toCommRingCatIso.hom ≫
              CommRingCat.ofHom (ambientLocalizedMap p g q) =
            CommRingCat.ofHom
              (Localization.localRingHom
                ((targetBasePrime p q).comap g.toRingHom)
                (targetBasePrime p q) g.toRingHom rfl) := by
        apply CommRingCat.hom_ext
        exact sourceLocalizationEquiv_comp_ambientLocalizedMap p g q
      simpa using hlocal)

/-- The actual stalk map of `Spec.map g`, packaged as an arrow isomorphic to
the ambient localized map attached to the fibre point. -/
noncomputable def specStalkMapAmbientIso (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime] :
    Arrow.mk
        ((Spec.map (CommRingCat.ofHom g.toRingHom)).stalkMap
          (targetSpecPoint p q)) ≅
      Arrow.mk (CommRingCat.ofHom (ambientLocalizedMap p g q)) :=
  (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom g.toRingHom)
    (targetPrime p q)).trans (localizedMapArrowIso p g q)

/-- The source component of `specStalkMapAmbientIso`. -/
noncomputable abbrev sourceStalkIso (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime] :
    (Spec (.of S)).presheaf.stalk
        ((Spec.map (CommRingCat.ofHom g.toRingHom))
          (targetSpecPoint p q)) ≅
      .of (Localization.AtPrime (sourceBasePrime p g q)) :=
  Arrow.leftFunc.mapIso (specStalkMapAmbientIso p g q)

/-- The target component of `specStalkMapAmbientIso`. -/
noncomputable abbrev targetStalkIso (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime] :
    (Spec (.of T)).presheaf.stalk (targetSpecPoint p q) ≅
      .of (Localization.AtPrime (targetBasePrime p q)) :=
  Arrow.rightFunc.mapIso (specStalkMapAmbientIso p g q)

/-- At the ambient point underlying `q`, the actual stalk map of
`Spec.map g` is `ambientLocalizedMap p g q` under the canonical affine
stalk/localization isomorphisms and the equality-induced source transport. -/
theorem specMap_stalkMap_eq_ambientLocalizedMap
    (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime] :
    (sourceStalkIso p g q).hom ≫
        CommRingCat.ofHom (ambientLocalizedMap p g q) ≫
      (targetStalkIso p g q).inv =
        (Spec.map (CommRingCat.ofHom g.toRingHom)).stalkMap
          (targetSpecPoint p q) := by
  let E := specStalkMapAmbientIso p g q
  have hw :
      (sourceStalkIso p g q).hom ≫
          CommRingCat.ofHom (ambientLocalizedMap p g q) =
        (Spec.map (CommRingCat.ofHom g.toRingHom)).stalkMap
            (targetSpecPoint p q) ≫
          (targetStalkIso p g q).hom :=
    E.hom.w
  calc
    (sourceStalkIso p g q).hom ≫
          CommRingCat.ofHom (ambientLocalizedMap p g q) ≫
        (targetStalkIso p g q).inv =
        ((sourceStalkIso p g q).hom ≫
          CommRingCat.ofHom (ambientLocalizedMap p g q)) ≫
            (targetStalkIso p g q).inv :=
      (Category.assoc _ _ _).symm
    _ = ((Spec.map (CommRingCat.ofHom g.toRingHom)).stalkMap
          (targetSpecPoint p q) ≫
        (targetStalkIso p g q).hom) ≫
          (targetStalkIso p g q).inv :=
      congrArg (fun h ↦ h ≫ (targetStalkIso p g q).inv) hw
    _ = (Spec.map (CommRingCat.ofHom g.toRingHom)).stalkMap
        (targetSpecPoint p q) := by
      rw [Category.assoc, (targetStalkIso p g q).hom_inv_id,
        Category.comp_id]

private theorem localCompletion_map_congr
    {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    (f g : A →+* B) [IsLocalHom f] [IsLocalHom g] (h : f = g) :
    LocalCompletion.map f = LocalCompletion.map g := by
  subst g
  rfl

private theorem localCompletion_map_surjective_of_ringEquiv
    {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    Function.Surjective (LocalCompletion.map e.toRingHom) := by
  letI : IsLocalHom e.toRingHom :=
    ⟨fun x hx ↦ (isLocalHom_equiv e).map_nonunit x hx⟩
  letI : IsLocalHom e.symm.toRingHom :=
    ⟨fun x hx ↦ (isLocalHom_equiv e.symm).map_nonunit x hx⟩
  intro y
  refine ⟨LocalCompletion.map e.symm.toRingHom y, ?_⟩
  change LocalCompletion.map e.toRingHom
      (LocalCompletion.map e.symm.toRingHom y) = y
  rw [← RingHom.comp_apply, ← LocalCompletion.map_comp]
  have he : e.toRingHom.comp e.symm.toRingHom = RingHom.id B := by
    ext b
    exact e.apply_symm_apply b
  have hmap := localCompletion_map_congr
    (e.toRingHom.comp e.symm.toRingHom) (RingHom.id B) he
  rw [hmap, LocalCompletion.map_id]
  rfl

/-- A degree-one calculation on the affine fibre proves formal immersion for
the actual affine scheme morphism.  The hypotheses expose exactly the two
finite maximal-ideal inputs, the finite special-fibre quotient input, and
residue-field surjectivity used by the completion argument. -/
theorem IsAffineFiberDegreeOneCotangent.isFormalImmersionAtSpecMap
    (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime]
    [Module.Finite (Localization.AtPrime (sourceBasePrime p g q))
      (IsLocalRing.maximalIdeal
        (Localization.AtPrime (sourceBasePrime p g q)))]
    [Module.Finite (Localization.AtPrime (targetBasePrime p q))
      (IsLocalRing.maximalIdeal
        (Localization.AtPrime (targetBasePrime p q)))]
    (hdegreeOne : IsAffineFiberDegreeOneCotangent p g q)
    (hfinite : Module.Finite
      (Localization.AtPrime (targetBasePrime p q) ⧸
        targetSpecialFiberIdeal p q)
      ((IsLocalRing.maximalIdeal
          (Localization.AtPrime (targetBasePrime p q))).map
        (Ideal.Quotient.mk (targetSpecialFiberIdeal p q))))
    (hresidue : Function.Surjective
      (IsLocalRing.ResidueField.map (ambientLocalizedMap p g q))) :
    IsFormalImmersionAt (Spec.map (CommRingCat.ofHom g.toRingHom))
      (targetSpecPoint p q) := by
  let eS := (sourceStalkIso p g q).commRingCatIsoToRingEquiv
  let eT := (targetStalkIso p g q).commRingCatIsoToRingEquiv
  letI : IsLocalRing
      ((Spec (.of S)).presheaf.stalk
        ((Spec.map (CommRingCat.ofHom g.toRingHom))
          (targetSpecPoint p q))) :=
    eS.symm.isLocalRing
  letI : IsLocalRing
      ((Spec (.of T)).presheaf.stalk (targetSpecPoint p q)) :=
    eT.symm.isLocalRing
  letI : IsLocalHom eS.toRingHom :=
    ⟨fun x hx ↦ (isLocalHom_equiv eS).map_nonunit x hx⟩
  letI : IsLocalHom eT.symm.toRingHom :=
    ⟨fun x hx ↦ (isLocalHom_equiv eT.symm).map_nonunit x hx⟩
  letI hmid : IsLocalHom
      ((ambientLocalizedMap p g q).comp eS.toRingHom) :=
    RingHom.isLocalHom_comp _ _
  letI hfull : IsLocalHom
      (eT.symm.toRingHom.comp
        ((ambientLocalizedMap p g q).comp eS.toRingHom)) :=
    RingHom.isLocalHom_comp _ _
  have hambient : Function.Surjective
      (LocalCompletion.map (ambientLocalizedMap p g q)) :=
    hdegreeOne.ambientCompletionMapSurjective p g q hfinite hresidue
  have heS : Function.Surjective
      (LocalCompletion.map eS.toRingHom) :=
    localCompletion_map_surjective_of_ringEquiv eS
  have heT : Function.Surjective
      (LocalCompletion.map eT.symm.toRingHom) :=
    localCompletion_map_surjective_of_ringEquiv eT.symm
  have hstalk :
      ((Spec.map (CommRingCat.ofHom g.toRingHom)).stalkMap
        (targetSpecPoint p q)).hom =
      eT.symm.toRingHom.comp
        ((ambientLocalizedMap p g q).comp eS.toRingHom) := by
    symm
    exact CommRingCat.hom_ext_iff.mp
      (specMap_stalkMap_eq_ambientLocalizedMap p g q)
  letI hstalkLocal : IsLocalHom
      ((Spec.map (CommRingCat.ofHom g.toRingHom)).stalkMap
        (targetSpecPoint p q)).hom := by
    exact hstalk.symm ▸ hfull
  change Function.Surjective
    (LocalCompletion.map
      ((Spec.map (CommRingCat.ofHom g.toRingHom)).stalkMap
        (targetSpecPoint p q)).hom)
  have hcompletion := @localCompletion_map_congr _ _ _ _ _ _
    ((Spec.map (CommRingCat.ofHom g.toRingHom)).stalkMap
      (targetSpecPoint p q)).hom
    (eT.symm.toRingHom.comp
      ((ambientLocalizedMap p g q).comp eS.toRingHom))
    hstalkLocal hfull hstalk
  have houter := LocalCompletion.map_comp
    ((ambientLocalizedMap p g q).comp eS.toRingHom)
    eT.symm.toRingHom
  have hinner := LocalCompletion.map_comp eS.toRingHom
    (ambientLocalizedMap p g q)
  intro y
  obtain ⟨yT, hyT⟩ := heT y
  obtain ⟨yA, hyA⟩ := hambient yT
  obtain ⟨x, hx⟩ := heS yA
  refine ⟨x, ?_⟩
  calc
    LocalCompletion.map
        ((Spec.map (CommRingCat.ofHom g.toRingHom)).stalkMap
          (targetSpecPoint p q)).hom x =
        LocalCompletion.map
          (eT.symm.toRingHom.comp
            ((ambientLocalizedMap p g q).comp eS.toRingHom)) x :=
      congrArg (fun F ↦ F x) hcompletion
    _ = LocalCompletion.map eT.symm.toRingHom
        (LocalCompletion.map
          ((ambientLocalizedMap p g q).comp eS.toRingHom) x) :=
      congrArg (fun F ↦ F x) houter
    _ = LocalCompletion.map eT.symm.toRingHom
        (LocalCompletion.map (ambientLocalizedMap p g q)
          (LocalCompletion.map eS.toRingHom x)) := by
      rw [congrArg (fun F ↦ F x) hinner]
      rfl
    _ = y := by rw [hx, hyA, hyT]

/-- On Noetherian affine source and target rings, the finite-module inputs in
`isFormalImmersionAtSpecMap` are automatic.  Residue-field surjectivity
remains an explicit geometric hypothesis. -/
theorem
    IsAffineFiberDegreeOneCotangent.isFormalImmersionAtSpecMap_of_isNoetherian
    (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime]
    [IsNoetherianRing S] [IsNoetherianRing T]
    (hdegreeOne : IsAffineFiberDegreeOneCotangent p g q)
    (hresidue : Function.Surjective
      (IsLocalRing.ResidueField.map (ambientLocalizedMap p g q))) :
    IsFormalImmersionAt (Spec.map (CommRingCat.ofHom g.toRingHom))
      (targetSpecPoint p q) :=
  hdegreeOne.isFormalImmersionAtSpecMap p g q (by infer_instance)
    hresidue

end Ideal.Fiber
