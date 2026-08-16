/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.PermutationPower
import MazurTorsion.AlgebraicGeometry.Jacobian.AffineLineSymmetricPower
import Mathlib.AlgebraicGeometry.AffineSpace

/-!
# Relative powers of the affine line

The finite relative power of the standard affine line over \`Spec R\` is
identified with Mathlib's affine space and hence with
\`Spec (MvPolynomial ι R)\`.  The construction retains exact coordinate
projections and intertwines the permutation action with renaming polynomial
variables, including the universe lift used by \`AffineSpace\`.

The named downstream consumer is the block-monic coordinate quotient in
\`GeometricAssignedAffineChart\`.
-/

noncomputable section

universe u

open CategoryTheory Limits
open AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.RelativeAffineLinePower

open MazurTorsion.AlgebraicGeometry.Jacobian.AffineLineSymmetricPower

variable (R : Type u) [CommRing R]
variable (ι : Type) [Finite ι]

abbrev lineOver : Over (Spec (.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom
    (MvPolynomial.C : R →+* MvPolynomial (Fin 1) R)))

abbrev affineLineOver : Over (Spec (.of R)) :=
  Over.mk (𝔸(ULift.{u} (Fin 1); Spec (.of R)) ↘ Spec (.of R))

abbrev affineSpaceOver : Over (Spec (.of R)) :=
  Over.mk (𝔸(ULift.{u} ι; Spec (.of R)) ↘ Spec (.of R))

def linePolynomialIsoLifted :
    Spec (.of (MvPolynomial (Fin 1) R)) ≅
      Spec (.of (MvPolynomial (ULift.{u} (Fin 1)) R)) :=
  (Scheme.Spec.mapIso
    (MvPolynomial.renameEquiv R Equiv.ulift.symm).toRingEquiv.toCommRingCatIso.op).symm

theorem linePolynomialIsoLifted_hom_over :
    (linePolynomialIsoLifted R).hom ≫
        Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : R →+* MvPolynomial (ULift.{u} (Fin 1)) R)) =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : R →+* MvPolynomial (Fin 1) R)) := by
  rw [linePolynomialIsoLifted]
  simp only [Iso.symm_hom, Functor.mapIso_inv, Iso.op_inv,
    RingEquiv.toCommRingCatIso_inv,
    Scheme.Spec_map, Quiver.Hom.unop_op, ← Spec.map_comp]
  rw [Spec.map_inj]
  apply CommRingCat.hom_ext
  apply DFunLike.ext _ _
  intro r
  simp

def lineIsoAffineLine : lineOver R ≅ affineLineOver R :=
  Over.isoMk
    (linePolynomialIsoLifted R ≪≫
      (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of R)).symm)
    (by
      change ((linePolynomialIsoLifted R).hom ≫
        (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of R)).inv) ≫
          (𝔸(ULift.{u} (Fin 1); Spec (.of R)) ↘ Spec (.of R)) = _
      rw [Category.assoc, AffineSpace.SpecIso_inv_over]
      exact linePolynomialIsoLifted_hom_over R)

def affineSpaceProjection (i : ι) :
    affineSpaceOver R ι ⟶ affineLineOver R :=
  Over.homMk
    (AffineSpace.reindex
      (fun _ : ULift.{u} (Fin 1) ↦ ULift.up i) (Spec (.of R)))
    (AffineSpace.reindex_over
      (fun _ : ULift.{u} (Fin 1) ↦ ULift.up i) (Spec (.of R)))

abbrev affineLinePower : Over (Spec (.of R)) :=
  MazurTorsion.AlgebraicGeometry.Jacobian.PermutationPower.power
    (Spec (.of R)) ι (affineLineOver R)

def powerToAffineSpace : affineLinePower R ι ⟶ affineSpaceOver R ι :=
  Over.homMk
    (AffineSpace.homOfVector
      (affineLinePower R ι).hom
      (fun i ↦ (Pi.π (fun _ : ι ↦ affineLineOver R) i.down).left.appTop
        (AffineSpace.coord (Spec (.of R))
          (ULift.up (0 : Fin 1)))))
    (AffineSpace.homOfVector_over _ _)

def affineSpaceToPower : affineSpaceOver R ι ⟶ affineLinePower R ι :=
  Pi.lift (affineSpaceProjection R ι)

theorem powerToAffineSpace_comp_projection (i : ι) :
    powerToAffineSpace R ι ≫ affineSpaceProjection R ι i =
      Pi.π (fun _ : ι ↦ affineLineOver R) i := by
  apply Over.OverMorphism.ext
  apply AffineSpace.hom_ext
  · calc
      (powerToAffineSpace R ι ≫ affineSpaceProjection R ι i).left ≫
          (affineLineOver R).hom =
        (powerToAffineSpace R ι).left ≫
          ((affineSpaceProjection R ι i).left ≫
            (affineLineOver R).hom) := Category.assoc _ _ _
      _ = (powerToAffineSpace R ι).left ≫
          (affineSpaceOver R ι).hom := congrArg
            (fun f ↦ (powerToAffineSpace R ι).left ≫ f)
            (affineSpaceProjection R ι i).w
      _ = (affineLinePower R ι).hom := (powerToAffineSpace R ι).w
      _ = (Pi.π (fun _ : ι ↦ affineLineOver R) i).left ≫
          (affineLineOver R).hom :=
        (Pi.π (fun _ : ι ↦ affineLineOver R) i).w.symm
  · intro j
    have hj : j = ULift.up (0 : Fin 1) := Subsingleton.elim _ _
    subst j
    change (AffineSpace.homOfVector
        (affineLinePower R ι).hom
        (fun j ↦ (Pi.π (fun _ : ι ↦ affineLineOver R) j.down).left.appTop
          (AffineSpace.coord (Spec (.of R))
            (ULift.up (0 : Fin 1))))).appTop
      ((AffineSpace.reindex
          (fun _ : ULift.{u} (Fin 1) ↦ ULift.up i)
          (Spec (.of R))).appTop
        (AffineSpace.coord (Spec (.of R)) (ULift.up (0 : Fin 1)))) = _
    rw [AffineSpace.reindex_appTop_coord]
    exact AffineSpace.homOfVector_appTop_coord _ _ _

def affineLinePowerIsoAffineSpace :
    affineLinePower R ι ≅ affineSpaceOver R ι where
  hom := powerToAffineSpace R ι
  inv := affineSpaceToPower R ι
  hom_inv_id := by
    apply Pi.hom_ext
    intro i
    simp only [Category.assoc, affineSpaceToPower, Pi.lift_π,
      Category.id_comp]
    rw [powerToAffineSpace_comp_projection]
  inv_hom_id := by
    apply Over.OverMorphism.ext
    apply AffineSpace.hom_ext
    · change ((affineSpaceToPower R ι).left ≫
          (powerToAffineSpace R ι).left) ≫
          (affineSpaceOver R ι).hom =
        𝟙 (affineSpaceOver R ι).left ≫ (affineSpaceOver R ι).hom
      rw [Category.id_comp]
      exact (affineSpaceToPower R ι ≫ powerToAffineSpace R ι).w
    · intro i
      rcases i with ⟨i⟩
      simp only [Over.comp_left, Over.id_left, Scheme.Hom.id_appTop]
      rw [Scheme.Hom.comp_appTop]
      change (affineSpaceToPower R ι).left.appTop
        ((AffineSpace.homOfVector
          (affineLinePower R ι).hom
          (fun j ↦ (Pi.π (fun _ : ι ↦ affineLineOver R) j.down).left.appTop
            (AffineSpace.coord (Spec (.of R))
              (ULift.up (0 : Fin 1))))).appTop
            (AffineSpace.coord (Spec (.of R)) (ULift.up i))) = _
      rw [AffineSpace.homOfVector_appTop_coord]
      have hπ : affineSpaceToPower R ι ≫
          Pi.π (fun _ : ι ↦ affineLineOver R) i =
        affineSpaceProjection R ι i := by
        simp [affineSpaceToPower]
      have happ := congrArg
        (fun f : (affineSpaceOver R ι).left ⟶ (affineLineOver R).left ↦
          f.appTop (AffineSpace.coord (Spec (.of R))
            (ULift.up (0 : Fin 1))))
        (congrArg Over.Hom.left hπ)
      change ((affineSpaceToPower R ι).left ≫
          (Pi.π (fun _ : ι ↦ affineLineOver R) i).left).appTop
            (AffineSpace.coord (Spec (.of R))
              (ULift.up (0 : Fin 1))) =
        (affineSpaceProjection R ι i).left.appTop
          (AffineSpace.coord (Spec (.of R))
            (ULift.up (0 : Fin 1))) at happ
      rw [Scheme.Hom.comp_appTop] at happ
      simpa [affineSpaceProjection, Scheme.Hom.id_appTop] using happ

abbrev linePower : Over (Spec (.of R)) :=
  MazurTorsion.AlgebraicGeometry.Jacobian.PermutationPower.power
    (Spec (.of R)) ι (lineOver R)

def linePowerIsoAffineSpace :
    linePower R ι ≅ affineSpaceOver R ι :=
  Pi.mapIso (fun _ : ι ↦ lineIsoAffineLine R) ≪≫
    affineLinePowerIsoAffineSpace R ι

theorem linePowerIsoAffineSpace_hom_comp_projection (i : ι) :
    (linePowerIsoAffineSpace R ι).hom ≫ affineSpaceProjection R ι i =
      Pi.π (fun _ : ι ↦ lineOver R) i ≫ (lineIsoAffineLine R).hom := by
  change ((Pi.mapIso (fun _ : ι ↦ lineIsoAffineLine R)).hom ≫
      powerToAffineSpace R ι) ≫ affineSpaceProjection R ι i = _
  rw [Category.assoc, powerToAffineSpace_comp_projection]
  exact Pi.mapIso_hom_π (fun _ : ι ↦ lineIsoAffineLine R) i

def affineSpacePermutation (g : Equiv.Perm ι) :
    affineSpaceOver R ι ⟶ affineSpaceOver R ι :=
  Over.homMk
    (AffineSpace.reindex
      (fun i : ULift.{u} ι ↦ ULift.up (g i.down)) (Spec (.of R)))
    (AffineSpace.reindex_over
      (fun i : ULift.{u} ι ↦ ULift.up (g i.down)) (Spec (.of R)))

omit [Finite ι] in
theorem affineSpacePermutation_comp_projection
    (g : Equiv.Perm ι) (i : ι) :
    affineSpacePermutation R ι g ≫ affineSpaceProjection R ι i =
      affineSpaceProjection R ι (g i) := by
  apply Over.OverMorphism.ext
  change AffineSpace.reindex
      (fun j : ULift.{u} ι ↦ ULift.up (g j.down)) (Spec (.of R)) ≫
      AffineSpace.reindex
        (fun _ : ULift.{u} (Fin 1) ↦ ULift.up i) (Spec (.of R)) =
    AffineSpace.reindex
      (fun _ : ULift.{u} (Fin 1) ↦ ULift.up (g i)) (Spec (.of R))
  let a : ULift.{u} (Fin 1) ⟶ ULift.{u} ι :=
    ↾(fun _ ↦ ULift.up i)
  let b : ULift.{u} ι ⟶ ULift.{u} ι :=
    ↾(fun j ↦ ULift.up (g j.down))
  calc
    AffineSpace.reindex (ConcreteCategory.hom b) (Spec (.of R)) ≫
        AffineSpace.reindex (ConcreteCategory.hom a) (Spec (.of R)) =
      AffineSpace.reindex (ConcreteCategory.hom (a ≫ b))
        (Spec (.of R)) :=
        (AffineSpace.reindex_comp a b (Spec (.of R))).symm
    _ = _ := by
      congr 1

theorem affineSpace_hom_ext {X : Over (Spec (.of R))}
    (f g : X ⟶ affineSpaceOver R ι)
    (h : ∀ i, f ≫ affineSpaceProjection R ι i =
      g ≫ affineSpaceProjection R ι i) : f = g := by
  apply (cancel_mono (affineLinePowerIsoAffineSpace R ι).inv).mp
  apply Pi.hom_ext
  intro i
  rw [Category.assoc, Category.assoc]
  change f ≫ (affineSpaceToPower R ι ≫
      Pi.π (fun _ : ι ↦ affineLineOver R) i) =
    g ≫ (affineSpaceToPower R ι ≫
      Pi.π (fun _ : ι ↦ affineLineOver R) i)
  rw [show affineSpaceToPower R ι ≫
      Pi.π (fun _ : ι ↦ affineLineOver R) i =
    affineSpaceProjection R ι i by simp [affineSpaceToPower]]
  exact h i

theorem linePowerIsoAffineSpace_permutation
    (g : Equiv.Perm ι) :
    MazurTorsion.AlgebraicGeometry.Jacobian.PermutationPower.permutationHom
        (Spec (.of R)) ι (lineOver R) g ≫
      (linePowerIsoAffineSpace R ι).hom =
    (linePowerIsoAffineSpace R ι).hom ≫ affineSpacePermutation R ι g := by
  apply affineSpace_hom_ext R ι
  intro i
  calc
    (_ ≫ (linePowerIsoAffineSpace R ι).hom) ≫
        affineSpaceProjection R ι i =
      _ ≫ ((linePowerIsoAffineSpace R ι).hom ≫
        affineSpaceProjection R ι i) := Category.assoc _ _ _
    _ = _ ≫ (Pi.π (fun _ : ι ↦ lineOver R) i ≫
        (lineIsoAffineLine R).hom) := by
      rw [linePowerIsoAffineSpace_hom_comp_projection]
    _ = (_ ≫ Pi.π (fun _ : ι ↦ lineOver R) i) ≫
        (lineIsoAffineLine R).hom := (Category.assoc _ _ _).symm
    _ = Pi.π (fun _ : ι ↦ lineOver R) (g i) ≫
        (lineIsoAffineLine R).hom := by
      rw [MazurTorsion.AlgebraicGeometry.Jacobian.PermutationPower.permutationHom_comp_π]
    _ = (linePowerIsoAffineSpace R ι).hom ≫
        affineSpaceProjection R ι (g i) :=
      (linePowerIsoAffineSpace_hom_comp_projection R ι (g i)).symm
    _ = (linePowerIsoAffineSpace R ι).hom ≫
        (affineSpacePermutation R ι g ≫
          affineSpaceProjection R ι i) := by
      rw [affineSpacePermutation_comp_projection]
    _ = ((linePowerIsoAffineSpace R ι).hom ≫
        affineSpacePermutation R ι g) ≫
          affineSpaceProjection R ι i := (Category.assoc _ _ _).symm

def liftPermutation (g : Equiv.Perm ι) : Equiv.Perm (ULift.{u} ι) :=
  Equiv.ulift.trans (g.trans Equiv.ulift.symm)

omit [Finite ι] in
theorem liftPermutation_up (g : Equiv.Perm ι) (i : ι) :
    liftPermutation ι g (ULift.up i) = ULift.up (g i) := rfl

def liftedPolynomialPermutationSpec (g : Equiv.Perm ι) :
    Spec (.of (MvPolynomial (ULift.{u} ι) R)) ⟶
      Spec (.of (MvPolynomial (ULift.{u} ι) R)) := by
  letI := coordinatePermutationAction R (ULift.{u} ι)
  exact specSMul (liftPermutation ι g)

omit [Finite ι] in
theorem liftedPolynomialPermutationSpec_comp_over
    (g : Equiv.Perm ι) :
    liftedPolynomialPermutationSpec R ι g ≫
        Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : R →+* MvPolynomial (ULift.{u} ι) R)) =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : R →+* MvPolynomial (ULift.{u} ι) R)) := by
  letI := coordinatePermutationAction R (ULift.{u} ι)
  rw [liftedPolynomialPermutationSpec, specSMul, ← Spec.map_comp,
    Spec.map_inj]
  apply CommRingCat.hom_ext
  apply DFunLike.ext _ _
  intro r
  change MvPolynomial.rename (liftPermutation ι g)
    (MvPolynomial.C r) = MvPolynomial.C r
  rw [MvPolynomial.rename_C]

omit [Finite ι] in
theorem affineSpacePermutation_comp_SpecIso
    (g : Equiv.Perm ι) :
    (affineSpacePermutation R ι g).left ≫
        (AffineSpace.SpecIso (ULift.{u} ι) (.of R)).hom =
      (AffineSpace.SpecIso (ULift.{u} ι) (.of R)).hom ≫
        liftedPolynomialPermutationSpec R ι g := by
  apply (cancel_mono
    (AffineSpace.SpecIso (ULift.{u} ι) (.of R)).inv).mp
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply AffineSpace.hom_ext
  · refine (affineSpacePermutation R ι g).w.trans ?_
    symm
    have hEover :
        (AffineSpace.SpecIso (ULift.{u} ι) (.of R)).inv ≫
            (affineSpaceOver R ι).hom =
          Spec.map (CommRingCat.ofHom
            (MvPolynomial.C : R →+*
              MvPolynomial (ULift.{u} ι) R)) :=
      AffineSpace.SpecIso_inv_over (.of R)
    calc
      (((AffineSpace.SpecIso (ULift.{u} ι) (.of R)).hom ≫
          liftedPolynomialPermutationSpec R ι g) ≫
          (AffineSpace.SpecIso (ULift.{u} ι) (.of R)).inv) ≫
            (affineSpaceOver R ι).hom =
        (AffineSpace.SpecIso (ULift.{u} ι) (.of R)).hom ≫
          (liftedPolynomialPermutationSpec R ι g ≫
            ((AffineSpace.SpecIso (ULift.{u} ι) (.of R)).inv ≫
              (affineSpaceOver R ι).hom)) := by simp
      _ = (AffineSpace.SpecIso (ULift.{u} ι) (.of R)).hom ≫
          (liftedPolynomialPermutationSpec R ι g ≫
            Spec.map (CommRingCat.ofHom
              (MvPolynomial.C : R →+*
                MvPolynomial (ULift.{u} ι) R))) := by
        exact congrArg
          (fun q ↦ (AffineSpace.SpecIso (ULift.{u} ι) (.of R)).hom ≫
            (liftedPolynomialPermutationSpec R ι g ≫ q)) hEover
      _ = (AffineSpace.SpecIso (ULift.{u} ι) (.of R)).hom ≫
          Spec.map (CommRingCat.ofHom
            (MvPolynomial.C : R →+*
              MvPolynomial (ULift.{u} ι) R)) := by
        rw [liftedPolynomialPermutationSpec_comp_over]
      _ = (affineSpaceOver R ι).hom := by
        calc
          (AffineSpace.SpecIso (ULift.{u} ι) (.of R)).hom ≫
              Spec.map (CommRingCat.ofHom
                (MvPolynomial.C : R →+*
                  MvPolynomial (ULift.{u} ι) R)) =
            (AffineSpace.SpecIso (ULift.{u} ι) (.of R)).hom ≫
              ((AffineSpace.SpecIso (ULift.{u} ι) (.of R)).inv ≫
                (affineSpaceOver R ι).hom) := congrArg
                  (fun q ↦ (AffineSpace.SpecIso
                    (ULift.{u} ι) (.of R)).hom ≫ q) hEover.symm
          _ = (affineSpaceOver R ι).hom := by
            rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  · intro i
    rcases i with ⟨i⟩
    let E := AffineSpace.SpecIso (ULift.{u} ι) (.of R)
    let p := liftPermutation ι g
    have hperm :
        (liftedPolynomialPermutationSpec R ι g).appTop
            ((Scheme.ΓSpecIso
              (.of (MvPolynomial (ULift.{u} ι) R))).inv
                (MvPolynomial.X (ULift.up i))) =
          (Scheme.ΓSpecIso
            (.of (MvPolynomial (ULift.{u} ι) R))).inv
              (MvPolynomial.X (ULift.up (g i))) := by
      letI := coordinatePermutationAction R (ULift.{u} ι)
      change (Spec.map (CommRingCat.ofHom
          (MulSemiringAction.toRingHom
            (Equiv.Perm (ULift.{u} ι))
            (MvPolynomial (ULift.{u} ι) R) p))).appTop
          ((Scheme.ΓSpecIso
            (.of (MvPolynomial (ULift.{u} ι) R))).inv
              (MvPolynomial.X (ULift.up i))) = _
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
      change (Scheme.ΓSpecIso
          (.of (MvPolynomial (ULift.{u} ι) R))).inv
        (p • MvPolynomial.X (ULift.up i)) = _
      rw [smul_eq_rename, MvPolynomial.rename_X, liftPermutation_up]
    have hcancel := congrArg
      (fun f : 𝔸(ULift.{u} ι; Spec (.of R)) ⟶
          𝔸(ULift.{u} ι; Spec (.of R)) ↦
        f.appTop (AffineSpace.coord (Spec (.of R))
          (ULift.up (g i)))) E.hom_inv_id
    change E.hom.appTop
        (E.inv.appTop (AffineSpace.coord (Spec (.of R))
          (ULift.up (g i)))) =
      AffineSpace.coord (Spec (.of R)) (ULift.up (g i)) at hcancel
    change (AffineSpace.reindex
        (fun j : ULift.{u} ι ↦ ULift.up (g j.down))
        (Spec (.of R))).appTop
          (AffineSpace.coord (Spec (.of R)) (ULift.up i)) = _
    rw [AffineSpace.reindex_appTop_coord]
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
    change AffineSpace.coord (Spec (.of R)) (ULift.up (g i)) =
      E.hom.appTop
        ((liftedPolynomialPermutationSpec R ι g).appTop
          (E.inv.appTop (AffineSpace.coord (Spec (.of R))
            (ULift.up i))))
    rw [AffineSpace.SpecIso_inv_appTop_coord, hperm]
    rw [AffineSpace.SpecIso_inv_appTop_coord] at hcancel
    exact hcancel.symm

def linePowerUnderlyingIsoAffineSpace :
    (linePower R ι).left ≅ (affineSpaceOver R ι).left where
  hom := (linePowerIsoAffineSpace R ι).hom.left
  inv := (linePowerIsoAffineSpace R ι).inv.left
  hom_inv_id := congrArg Over.Hom.left
    (linePowerIsoAffineSpace R ι).hom_inv_id
  inv_hom_id := congrArg Over.Hom.left
    (linePowerIsoAffineSpace R ι).inv_hom_id

def linePowerSchemeIsoPolynomial :
    (linePower R ι).left ≅ Spec (.of (MvPolynomial ι R)) :=
  linePowerUnderlyingIsoAffineSpace R ι ≪≫
    AffineSpace.SpecIso (ULift.{u} ι) (.of R) ≪≫
    Scheme.Spec.mapIso
      (MvPolynomial.renameEquiv R Equiv.ulift.symm).toRingEquiv.toCommRingCatIso.op

def polynomialPermutationSpec (g : Equiv.Perm ι) :
    Spec (.of (MvPolynomial ι R)) ⟶ Spec (.of (MvPolynomial ι R)) := by
  letI := coordinatePermutationAction R ι
  exact specSMul g

def polynomialUnliftIso :
    Spec (.of (MvPolynomial (ULift.{u} ι) R)) ≅
      Spec (.of (MvPolynomial ι R)) :=
  Scheme.Spec.mapIso
    (MvPolynomial.renameEquiv R Equiv.ulift.symm).toRingEquiv.toCommRingCatIso.op

omit [Finite ι] in
theorem liftedPolynomialPermutationSpec_comp_unliftIso
    (g : Equiv.Perm ι) :
    liftedPolynomialPermutationSpec R ι g ≫
        (polynomialUnliftIso R ι).hom =
      (polynomialUnliftIso R ι).hom ≫
        polynomialPermutationSpec R ι g := by
  letI := coordinatePermutationAction R (ULift.{u} ι)
  letI := coordinatePermutationAction R ι
  simp only [liftedPolynomialPermutationSpec, polynomialPermutationSpec,
    polynomialUnliftIso, specSMul, Functor.mapIso_hom, Iso.op_hom,
    Scheme.Spec_map, Quiver.Hom.unop_op]
  rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    change (liftPermutation ι g) •
        MvPolynomial.rename ULift.up
          (MvPolynomial.C r : MvPolynomial ι R) =
      MvPolynomial.rename ULift.up
        (g • (MvPolynomial.C r : MvPolynomial ι R))
    rw [smul_eq_rename R (ULift.{u} ι), smul_eq_rename R ι,
      MvPolynomial.rename_C, MvPolynomial.rename_C]
    simp
  · intro i
    change (liftPermutation ι g) •
        MvPolynomial.rename ULift.up
          (MvPolynomial.X i : MvPolynomial ι R) =
      MvPolynomial.rename ULift.up
        (g • (MvPolynomial.X i : MvPolynomial ι R))
    rw [smul_eq_rename R (ULift.{u} ι), smul_eq_rename R ι,
      MvPolynomial.rename_X, MvPolynomial.rename_X,
      MvPolynomial.rename_X, liftPermutation_up]
    simp

theorem linePowerSchemeIsoPolynomial_permutation
    (g : Equiv.Perm ι) :
    (MazurTorsion.AlgebraicGeometry.Jacobian.PermutationPower.action
        (Spec (.of R)) ι (lineOver R)).hom g ≫
      (linePowerSchemeIsoPolynomial R ι).hom =
    (linePowerSchemeIsoPolynomial R ι).hom ≫
      polynomialPermutationSpec R ι g := by
  let L := linePowerUnderlyingIsoAffineSpace R ι
  let A := AffineSpace.SpecIso (ULift.{u} ι) (.of R)
  let U := polynomialUnliftIso R ι
  let P :=
    (MazurTorsion.AlgebraicGeometry.Jacobian.PermutationPower.permutationHom
      (Spec (.of R)) ι (lineOver R) g).left
  have hL :
      P ≫ L.hom =
        L.hom ≫ (affineSpacePermutation R ι g).left := by
    exact congrArg Over.Hom.left
      (linePowerIsoAffineSpace_permutation R ι g)
  have hA :
      (affineSpacePermutation R ι g).left ≫ A.hom =
        A.hom ≫ liftedPolynomialPermutationSpec R ι g :=
    affineSpacePermutation_comp_SpecIso R ι g
  have hU :
      liftedPolynomialPermutationSpec R ι g ≫ U.hom =
        U.hom ≫ polynomialPermutationSpec R ι g :=
    liftedPolynomialPermutationSpec_comp_unliftIso R ι g
  change
    P ≫
      ((L.hom ≫ A.hom) ≫ U.hom) =
    ((L.hom ≫ A.hom) ≫ U.hom) ≫ polynomialPermutationSpec R ι g
  calc
    P ≫ ((L.hom ≫ A.hom) ≫ U.hom) =
        (((P ≫ L.hom) ≫ A.hom) ≫ U.hom) := by simp
    _ = (((L.hom ≫ (affineSpacePermutation R ι g).left) ≫
        A.hom) ≫ U.hom) := by rw [hL]
    _ = ((L.hom ≫ ((affineSpacePermutation R ι g).left ≫
        A.hom)) ≫ U.hom) := by simp
    _ = ((L.hom ≫ (A.hom ≫
        liftedPolynomialPermutationSpec R ι g)) ≫ U.hom) := by rw [hA]
    _ = ((L.hom ≫ A.hom) ≫
        (liftedPolynomialPermutationSpec R ι g ≫ U.hom)) := by simp
    _ = ((L.hom ≫ A.hom) ≫
        (U.hom ≫ polynomialPermutationSpec R ι g)) := by rw [hU]
    _ = _ := by simp

end MazurTorsion.AlgebraicGeometry.Jacobian.RelativeAffineLinePower

