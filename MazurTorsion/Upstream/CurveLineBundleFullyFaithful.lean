/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveLineBundleCompatibleFamilies
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleOpenCoverIso

/-!
# Fully faithful module descent on a scheme open cover

This file supplies the morphism-descent half of the scheme-module stack property for
`OpenCover.{0}`.  Its design boundary is deliberately the same universe-zero cover boundary as
the compatible-family equalizer construction: a compatible family of local morphisms out of a
global module is lifted into that equalizer, and the resulting reconstruction morphism is tested
on the given cover.

The named downstream consumer is `CurveDivisorGlobalTensorAdd`, where this removes the remaining
conditional fully-faithful hypothesis from global divisor-line-bundle tensor additivity.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.LineBundleDescent

universe u

/-- The family of adjoints of a descent morphism whose source comes from a global module. -/
noncomputable def compatibleFamilyLiftAmbient
    {X : Scheme.{u}} {cov : X.OpenCover}
    {M : X.Modules} {D : modulesPseudofunctor.DescentData cov.f}
    (phi : (modulesPseudofunctor.toDescentData cov.f).obj M ⟶ D) :
    M ⟶ compatibleFamilyAmbient D :=
  Pi.lift fun i ↦
    (Scheme.Modules.pullbackPushforwardAdjunction (cov.f i)).homEquiv
      M (D.obj i) (phi.hom i)

/-- Projection of the ambient lift is the adjoint of the corresponding local morphism. -/
@[reassoc]
theorem compatibleFamilyLiftAmbient_comp_projection
    {X : Scheme.{u}} {cov : X.OpenCover}
    {M : X.Modules} {D : modulesPseudofunctor.DescentData cov.f}
    (phi : (modulesPseudofunctor.toDescentData cov.f).obj M ⟶ D) (i : cov.I₀) :
    compatibleFamilyLiftAmbient phi ≫
        Pi.π (fun j ↦ (Scheme.Modules.pushforward (cov.f j)).obj (D.obj j)) i =
      (Scheme.Modules.pullbackPushforwardAdjunction (cov.f i)).homEquiv
        M (D.obj i) (phi.hom i) := by
  exact Pi.lift_π _ i

/-- The ambient family defined by a descent morphism satisfies the compatibility equations. -/
theorem compatibleFamilyLiftAmbient_condition
    {X : Scheme.{u}} {cov : X.OpenCover}
    {M : X.Modules} {D : modulesPseudofunctor.DescentData cov.f}
    (phi : (modulesPseudofunctor.toDescentData cov.f).obj M ⟶ D) :
    compatibleFamilyLiftAmbient phi ≫ compatibleFamilyFirst D =
      compatibleFamilyLiftAmbient phi ≫ compatibleFamilySecond D := by
  apply Pi.hom_ext
  intro ij
  let N : cov.I₀ × cov.I₀ → X.Modules := fun kl ↦
    (Scheme.Modules.pushforward (cov.f kl.1)).obj
      ((Scheme.Modules.restrictFunctor (cov.f kl.1)).obj
        ((Scheme.Modules.pushforward (cov.f kl.2)).obj (D.obj kl.2)))
  let q : compatibleFamilyOverlapAmbient D ⟶ N ij := Pi.π N ij
  change (compatibleFamilyLiftAmbient phi ≫ compatibleFamilyFirst D) ≫ q =
    (compatibleFamilyLiftAmbient phi ≫ compatibleFamilySecond D) ≫ q
  simp only [Category.assoc]
  rw [show compatibleFamilyFirst D ≫ q =
      compatibleFamilyFirstComponent D ij.1 ij.2 by
        exact Pi.lift_π _ ij]
  rw [show compatibleFamilySecond D ≫ q =
      compatibleFamilySecondComponent D ij.1 ij.2 by
        exact Pi.lift_π _ ij]
  let Di : (cov.X ij.1).Modules := D.obj ij.1
  let Dj : (cov.X ij.2).Modules := D.obj ij.2
  let ri : (Scheme.Modules.pullback (cov.f ij.1)).obj M ⟶ Di := phi.hom ij.1
  let rj : (Scheme.Modules.pullback (cov.f ij.2)).obj M ⟶ Dj := phi.hom ij.2
  let Mi : X.Modules := (Scheme.Modules.pushforward (cov.f ij.1)).obj Di
  let Mj : X.Modules := (Scheme.Modules.pushforward (cov.f ij.2)).obj Dj
  let T : X.Modules := (Scheme.Modules.pushforward (cov.f ij.1)).obj
    ((Scheme.Modules.restrictFunctor (cov.f ij.1)).obj Mj)
  let pi : compatibleFamilyAmbient D ⟶ Mi :=
    Pi.π (fun k ↦ (Scheme.Modules.pushforward (cov.f k)).obj (D.obj k)) ij.1
  let pj : compatibleFamilyAmbient D ⟶ Mj :=
    Pi.π (fun k ↦ (Scheme.Modules.pushforward (cov.f k)).obj (D.obj k)) ij.2
  let c : Mi ⟶ T := (Scheme.Modules.pushforward (cov.f ij.1)).map
    (compatibleFamilyChartComponent D ij.1 ij.2)
  let e : Mj ⟶ T := (Scheme.Modules.restrictAdjunction (cov.f ij.1)).unit.app Mj
  let gi : M ⟶ Mi :=
    (Scheme.Modules.pullbackPushforwardAdjunction (cov.f ij.1)).homEquiv M Di ri
  let gj : M ⟶ Mj :=
    (Scheme.Modules.pullbackPushforwardAdjunction (cov.f ij.2)).homEquiv M Dj rj
  have hfirst : compatibleFamilyFirstComponent D ij.1 ij.2 = pi ≫ c := rfl
  have hsecond : compatibleFamilySecondComponent D ij.1 ij.2 = pj ≫ e := rfl
  have hgi : compatibleFamilyLiftAmbient phi ≫ pi = gi := by
    exact compatibleFamilyLiftAmbient_comp_projection phi ij.1
  have hgj : compatibleFamilyLiftAmbient phi ≫ pj = gj := by
    exact compatibleFamilyLiftAmbient_comp_projection phi ij.2
  rw [hfirst, hsecond, ← Category.assoc, hgi, ← Category.assoc, hgj]
  exact compatibleFamilyAdjunct_comp_chartComponent phi ij.1 ij.2

/-- The global morphism into the compatible-family equalizer induced by a descent morphism. -/
noncomputable def compatibleFamilyLift
    {X : Scheme.{u}} {cov : X.OpenCover.{0}}
    {M : X.Modules} {D : modulesPseudofunctor.DescentData cov.f}
    (phi : (modulesPseudofunctor.toDescentData cov.f).obj M ⟶ D) :
    M ⟶ compatibleFamilyModule D :=
  equalizer.lift (compatibleFamilyLiftAmbient phi)
    (compatibleFamilyLiftAmbient_condition phi)

/-- The equalizer inclusion of the lifted morphism is its ambient compatible family. -/
@[reassoc]
theorem compatibleFamilyLift_comp_ι
    {X : Scheme.{u}} {cov : X.OpenCover.{0}}
    {M : X.Modules} {D : modulesPseudofunctor.DescentData cov.f}
    (phi : (modulesPseudofunctor.toDescentData cov.f).obj M ⟶ D) :
    compatibleFamilyLift phi ≫
        equalizer.ι (compatibleFamilyFirst D) (compatibleFamilySecond D) =
      compatibleFamilyLiftAmbient phi := by
  exact equalizer.lift_ι _ _

/-- Restricting the lifted morphism to a chart and applying the reconstruction projection
recovers the specified component of the descent morphism. -/
theorem compatibleFamilyLift_comp_restrictionHom
    {X : Scheme.{u}} {cov : X.OpenCover.{0}}
    {M : X.Modules} {D : modulesPseudofunctor.DescentData cov.f}
    (phi : (modulesPseudofunctor.toDescentData cov.f).obj M ⟶ D)
    (i : cov.I₀) :
    (Scheme.Modules.pullback (cov.f i)).map (compatibleFamilyLift phi) ≫
        compatibleFamilyRestrictionHom D i =
      phi.hom i := by
  let P := Scheme.Modules.pullback (cov.f i)
  let A := Scheme.Modules.pullbackPushforwardAdjunction (cov.f i)
  let Di : (cov.X i).Modules := D.obj i
  let hi : P.obj M ⟶ Di := phi.hom i
  let r : P.obj (compatibleFamilyModule D) ⟶ Di :=
    compatibleFamilyRestrictionHom D i
  let Si : X.Modules := (Scheme.Modules.pushforward (cov.f i)).obj Di
  let pi : compatibleFamilyAmbient D ⟶ Si :=
    Pi.π (fun j ↦ (Scheme.Modules.pushforward (cov.f j)).obj (D.obj j)) i
  let inc : compatibleFamilyModule D ⟶ compatibleFamilyAmbient D :=
    equalizer.ι (compatibleFamilyFirst D) (compatibleFamilySecond D)
  let p : compatibleFamilyModule D ⟶ Si := compatibleFamilyProjection D i
  change P.map (compatibleFamilyLift phi) ≫ r = hi
  apply (A.homEquiv M Di).injective
  rw [A.homEquiv_naturality_left]
  rw [show A.homEquiv (compatibleFamilyModule D) Di r =
      p by
        exact compatibleFamilyRestrictionHom_adjunct D i]
  have hp : p = inc ≫ pi := rfl
  have hinc : compatibleFamilyLift phi ≫ inc = compatibleFamilyLiftAmbient phi := by
    exact compatibleFamilyLift_comp_ι phi
  calc
    compatibleFamilyLift phi ≫ p =
        compatibleFamilyLift phi ≫ (inc ≫ pi) := by rw [hp]
    _ = (compatibleFamilyLift phi ≫ inc) ≫ pi :=
      (Category.assoc _ _ _).symm
    _ = compatibleFamilyLiftAmbient phi ≫ pi := by rw [hinc]
    _ = A.homEquiv M Di hi :=
      compatibleFamilyLiftAmbient_comp_projection phi i

/-- The canonical map from a global module to the compatible-family reconstruction of its
canonical descent datum. -/
noncomputable def compatibleFamilyUnit
    {X : Scheme.{u}} (cov : X.OpenCover.{0}) (M : X.Modules) :
    M ⟶ compatibleFamilyModule
      ((modulesPseudofunctor.toDescentData cov.f).obj M) :=
  compatibleFamilyLift
    (𝟙 ((modulesPseudofunctor.toDescentData cov.f).obj M))

/-- On each chart, the reconstruction unit followed by the canonical projection is the
identity. -/
theorem compatibleFamilyUnit_comp_restrictionHom
    {X : Scheme.{u}} (cov : X.OpenCover.{0}) (M : X.Modules) (i : cov.I₀) :
    (Scheme.Modules.pullback (cov.f i)).map (compatibleFamilyUnit cov M) ≫
        compatibleFamilyRestrictionHom
          ((modulesPseudofunctor.toDescentData cov.f).obj M) i =
      𝟙 (((modulesPseudofunctor.toDescentData cov.f).obj M).obj i) := by
  simpa only [compatibleFamilyUnit, Pseudofunctor.DescentData.id_hom] using
    compatibleFamilyLift_comp_restrictionHom
      (𝟙 ((modulesPseudofunctor.toDescentData cov.f).obj M)) i

/-- The reconstruction unit is an isomorphism, detected on the same open-cover charts. -/
theorem compatibleFamilyUnit_isIso
    {X : Scheme.{u}} (cov : X.OpenCover.{0}) (M : X.Modules) :
    IsIso (compatibleFamilyUnit cov M) := by
  let unit := compatibleFamilyUnit cov M
  let D := (modulesPseudofunctor.toDescentData cov.f).obj M
  letI hPullback (i : cov.I₀) :
      IsIso ((Scheme.Modules.pullback (cov.f i)).map unit) := by
    let P := Scheme.Modules.pullback (cov.f i)
    let r : P.obj (compatibleFamilyModule D) ⟶ P.obj M :=
      compatibleFamilyRestrictionHom D i
    haveI hr : IsIso r := (compatibleFamilyRestrictionIso D i).isIso_hom
    have hunit : P.map unit ≫ r = 𝟙 (P.obj M) := by
      have h := compatibleFamilyUnit_comp_restrictionHom cov M i
      unfold modulesPseudofunctor Scheme.Modules.pseudofunctor at h
      exact h
    have hp : P.map unit = inv r := by
      apply (cancel_mono r).mp
      rw [hunit, IsIso.inv_hom_id]
    rw [hp]
    infer_instance
  letI hRestrict (i : cov.I₀) :
      IsIso ((Scheme.Modules.restrictFunctor (cov.f i)).map unit) := by
    let e := Scheme.Modules.restrictFunctorIsoPullback (cov.f i)
    haveI heSource : IsIso (e.hom.app M) := (e.app M).isIso_hom
    haveI heTarget : IsIso (e.hom.app (compatibleFamilyModule D)) :=
      (e.app (compatibleFamilyModule D)).isIso_hom
    haveI hcomp : IsIso
        ((Scheme.Modules.restrictFunctor (cov.f i)).map unit ≫
          e.hom.app (compatibleFamilyModule D)) := by
      rw [e.hom.naturality unit]
      infer_instance
    exact IsIso.of_isIso_comp_right
      ((Scheme.Modules.restrictFunctor (cov.f i)).map unit)
      (e.hom.app (compatibleFamilyModule D))
  exact Scheme.Modules.isIso_of_isIso_restrict_openCoverFamily
    unit cov.f cov.exists_eq

/-- The global preimage of a morphism between canonical descent data. -/
noncomputable def moduleDescentPreimage
    {X : Scheme.{u}} (cov : X.OpenCover.{0})
    {M N : X.Modules}
    (phi : (modulesPseudofunctor.toDescentData cov.f).obj M ⟶
      (modulesPseudofunctor.toDescentData cov.f).obj N) :
    M ⟶ N := by
  letI : IsIso (compatibleFamilyUnit cov N) := compatibleFamilyUnit_isIso cov N
  exact compatibleFamilyLift phi ≫ inv (compatibleFamilyUnit cov N)

/-- Pulling the global preimage back to a chart recovers the given local component. -/
theorem moduleDescentPreimage_restrict
    {X : Scheme.{u}} (cov : X.OpenCover.{0})
    {M N : X.Modules}
    (phi : (modulesPseudofunctor.toDescentData cov.f).obj M ⟶
      (modulesPseudofunctor.toDescentData cov.f).obj N)
    (i : cov.I₀) :
    (Scheme.Modules.pullback (cov.f i)).map
        (moduleDescentPreimage cov phi) =
      phi.hom i := by
  let P := Scheme.Modules.pullback (cov.f i)
  let D := (modulesPseudofunctor.toDescentData cov.f).obj N
  let unit := compatibleFamilyUnit cov N
  let Di : (cov.X i).Modules := D.obj i
  let r : P.obj (compatibleFamilyModule D) ⟶ Di :=
    compatibleFamilyRestrictionHom D i
  letI hUnit : IsIso unit := compatibleFamilyUnit_isIso cov N
  haveI hPullbackUnit : IsIso (P.map unit) := by
    dsimp only [P]
    infer_instance
  have hInv : P.map (inv unit) = r := by
    have hunit : P.map unit ≫ r = 𝟙 (P.obj N) := by
      have h := compatibleFamilyUnit_comp_restrictionHom cov N i
      unfold modulesPseudofunctor Scheme.Modules.pseudofunctor at h
      exact h
    apply (cancel_epi (P.map unit)).mp
    rw [← P.map_comp, IsIso.hom_inv_id, P.map_id]
    exact hunit.symm
  dsimp only [moduleDescentPreimage]
  rw [P.map_comp, hInv]
  exact compatibleFamilyLift_comp_restrictionHom phi i

/-- Lifting the restriction of a global morphism is composition with the target reconstruction
unit. -/
theorem compatibleFamilyLift_map
    {X : Scheme.{u}} (cov : X.OpenCover.{0})
    {M N : X.Modules} (f : M ⟶ N) :
    compatibleFamilyLift ((modulesPseudofunctor.toDescentData cov.f).map f) =
      f ≫ compatibleFamilyUnit cov N := by
  let D := (modulesPseudofunctor.toDescentData cov.f).obj N
  let phi : (modulesPseudofunctor.toDescentData cov.f).obj M ⟶ D :=
    (modulesPseudofunctor.toDescentData cov.f).map f
  let idD : D ⟶ D := 𝟙 D
  let unit : N ⟶ compatibleFamilyModule D := compatibleFamilyLift idD
  let inc : compatibleFamilyModule D ⟶ compatibleFamilyAmbient D :=
    equalizer.ι (compatibleFamilyFirst D) (compatibleFamilySecond D)
  change compatibleFamilyLift phi = f ≫ unit
  have hlift : compatibleFamilyLift phi ≫ inc =
      compatibleFamilyLiftAmbient phi := by
    exact compatibleFamilyLift_comp_ι phi
  have hunit : unit ≫ inc = compatibleFamilyLiftAmbient idD := by
    exact compatibleFamilyLift_comp_ι idD
  haveI hincMono : Mono inc := by
    dsimp only [inc, compatibleFamilyModule]
    infer_instance
  have hambient : compatibleFamilyLiftAmbient phi =
      f ≫ compatibleFamilyLiftAmbient idD := by
    apply Pi.hom_ext
    intro i
    let P := Scheme.Modules.pullback (cov.f i)
    let A := Scheme.Modules.pullbackPushforwardAdjunction (cov.f i)
    let Di : (cov.X i).Modules := P.obj N
    let ri : P.obj M ⟶ Di := phi.hom i
    let ei : P.obj N ⟶ Di := idD.hom i
    let Si : X.Modules := (Scheme.Modules.pushforward (cov.f i)).obj Di
    let pi : compatibleFamilyAmbient D ⟶ Si :=
      Pi.π (fun j ↦ (Scheme.Modules.pushforward (cov.f j)).obj (D.obj j)) i
    let gi : M ⟶ Si := A.homEquiv M Di ri
    let ui : N ⟶ Si := A.homEquiv N Di ei
    have hgi : compatibleFamilyLiftAmbient phi ≫ pi = gi := by
      exact compatibleFamilyLiftAmbient_comp_projection phi i
    have hui : compatibleFamilyLiftAmbient idD ≫ pi = ui := by
      exact compatibleFamilyLiftAmbient_comp_projection idD i
    change compatibleFamilyLiftAmbient phi ≫ pi =
      (f ≫ compatibleFamilyLiftAmbient idD) ≫ pi
    calc
      _ = gi := hgi
      _ = f ≫ ui := by
        dsimp only [gi, ui]
        rw [show ri = P.map f by rfl, show ei = 𝟙 (P.obj N) by rfl]
        rw [← A.homEquiv_naturality_left f (𝟙 _), Category.comp_id]
      _ = f ≫ (compatibleFamilyLiftAmbient idD ≫ pi) := by rw [hui]
      _ = (f ≫ compatibleFamilyLiftAmbient idD) ≫ pi :=
        (Category.assoc _ _ _).symm
  apply (cancel_mono inc).mp
  calc
    compatibleFamilyLift phi ≫ inc = compatibleFamilyLiftAmbient phi := hlift
    _ = f ≫ compatibleFamilyLiftAmbient idD := hambient
    _ = f ≫ (unit ≫ inc) := by rw [hunit]
    _ = (f ≫ unit) ≫ inc := (Category.assoc _ _ _).symm

/-- The preimage construction fixes morphisms that already come from the global category. -/
theorem moduleDescentPreimage_map
    {X : Scheme.{u}} (cov : X.OpenCover.{0})
    {M N : X.Modules} (f : M ⟶ N) :
    moduleDescentPreimage cov
        ((modulesPseudofunctor.toDescentData cov.f).map f) = f := by
  letI : IsIso (compatibleFamilyUnit cov N) := compatibleFamilyUnit_isIso cov N
  dsimp only [moduleDescentPreimage]
  rw [compatibleFamilyLift_map]
  simp

/-- Module restriction to a universe-zero scheme open cover is fully faithful.

The inverse on morphisms is the compatible-family lift followed by the inverse reconstruction
unit.  The two fields are respectively the chart-restriction computation and the computation on
a morphism already defined globally. -/
noncomputable def moduleDescentFullyFaithfulForOpenCover
    {X : Scheme.{u}} (cov : X.OpenCover.{0}) :
    ModuleDescentFullyFaithfulFor cov where
  preimage phi := moduleDescentPreimage cov phi
  map_preimage phi := by
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    exact moduleDescentPreimage_restrict cov phi i
  preimage_map f := moduleDescentPreimage_map cov f

end MazurTorsion.AlgebraicGeometry.LineBundleDescent
