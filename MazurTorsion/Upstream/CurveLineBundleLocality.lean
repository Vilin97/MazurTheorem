/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveLineBundleDescent
import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.LocalTriviality

/-!
# Locality of invertible sheaves on scheme open covers

Tau Ceti defines an invertible sheaf by a cover carrying singleton free-module
trivializations. This file proves that its predicate is local for an arbitrary scheme open
cover. Starting with local trivialization atlases on the cover members, it transports each
trivialization through restriction and the open-immersion range equivalence, then refines the
chart covers to a cover of the original scheme.

The final theorem discharges `LineBundleDescent.InvertibilityIsLocal`. Consequently ordinary
module effectivity for locally invertible descent data already gives effective descent by a
global invertible sheaf; locality is no longer an open hypothesis in the A3 route.
-/

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.LineBundleDescent

universe u v w

noncomputable section

open TauCeti

variable {X : Scheme.{u}}

private noncomputable def freePUnitIsoUnit
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    SheafOfModules.free (R := R) PUnit ≅ SheafOfModules.unit R := by
  let s : Cofan (fun (_ : PUnit.{u + 1}) ↦ SheafOfModules.unit R) :=
    Cofan.mk (P := SheafOfModules.unit R) (fun _ ↦ 𝟙 _)
  let hs : IsColimit s := Cofan.IsColimit.mk s
    (fun t ↦ t.inj PUnit.unit)
    (by
      intro t j
      cases j
      simp [s])
    (by
      intro t m hm
      simpa [s] using hm PUnit.unit)
  exact IsColimit.coconePointUniqueUpToIso
    (SheafOfModules.isColimitFreeCofan PUnit) hs

private noncomputable def mapFreePUnitIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {C' : Type u} [Category.{w} C'] {J' : GrothendieckTopology C'}
    {S : Sheaf J' RingCat.{u}}
    [HasWeakSheafify J' AddCommGrpCat.{u}]
    [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F : CategoryTheory.Functor
      (SheafOfModules.{u} R) (SheafOfModules.{u} S))
    (e : SheafOfModules.unit S ≅ F.obj (SheafOfModules.unit R)) :
    SheafOfModules.free (R := S) PUnit ≅
      F.obj (SheafOfModules.free (R := R) PUnit) :=
  freePUnitIsoUnit ≪≫ e ≪≫ F.mapIso freePUnitIsoUnit.symm

private lemma refinedCover (cov : X.OpenCover)
    {I : cov.I₀ → Type u}
    (V : ∀ i, I i → (cov.X i).Opens)
    (hV : ∀ i, (Opens.grothendieckTopology (cov.X i)).CoversTop (V i)) :
    (Opens.grothendieckTopology X).CoversTop
      (fun ij : Σ i, I i ↦ ((V ij.1 ij.2).ι ≫ cov.f ij.1).opensRange) := by
  rw [Opens.coversTop_iff, TopologicalSpace.IsOpenCover, iSup_sigma]
  rw [← cov.iSup_opensRange]
  apply iSup_congr
  intro i
  simp_rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι]
  rw [← Scheme.Hom.image_top_eq_opensRange]
  rw [← Scheme.Hom.image_iSup]
  congr 1
  exact (Opens.coversTop_iff _ (V i)).mp (hV i)

private noncomputable def trivializationToRestriction
    {Y : Scheme.{u}} (N : Y.Modules) (V : Y.Opens)
    (e : SheafOfModules.free (R := Y.ringCatSheaf.over V) PUnit ≅ N.over V) :
    SheafOfModules.free (R := V.toScheme.ringCatSheaf) PUnit ≅ N.restrict V.ι := by
  exact mapFreePUnitIso (Scheme.Modules.overEquiv V).functor
      (TopologicalSpace.Opens.sheafOfModulesEquivOverUnit V Y.ringCatSheaf).symm ≪≫
    (Scheme.Modules.overEquiv V).functor.mapIso e ≪≫
    (Scheme.Modules.overFunctorEquiv V).app N

private noncomputable def trivializationRestrict
    {Y Z : Scheme.{u}} (g : Z ⟶ Y) [IsOpenImmersion g]
    (N : Y.Modules)
    (e : SheafOfModules.free (R := Y.ringCatSheaf) PUnit ≅ N) :
    SheafOfModules.free (R := Z.ringCatSheaf) PUnit ≅ N.restrict g := by
  exact mapFreePUnitIso (Scheme.Modules.restrictFunctor g)
      (Scheme.Modules.restrictUnitIso g).symm ≪≫
    (Scheme.Modules.restrictFunctor g).mapIso e

private noncomputable def iteratedRestrictionIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (V : Y.Opens) :
    ((M.restrict f).restrict V.ι).restrict
        (V.ι ≫ f).isoOpensRange.inv ≅
      M.restrict (V.ι ≫ f).opensRange.ι :=
  ((Scheme.Modules.restrictFunctorComp
      (V.ι ≫ f).isoOpensRange.inv V.ι).app (M.restrict f)).symm ≪≫
    ((Scheme.Modules.restrictFunctorComp
      ((V.ι ≫ f).isoOpensRange.inv ≫ V.ι) f).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr (by
      simpa only [Category.assoc] using
        Scheme.Hom.isoOpensRange_inv_comp (V.ι ≫ f))).app M

private noncomputable def transportChartTrivialization
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (V : Y.Opens)
    (e : SheafOfModules.free (R := Y.ringCatSheaf.over V) PUnit ≅
      (M.restrict f).over V) :
    SheafOfModules.free (R := X.ringCatSheaf.over (V.ι ≫ f).opensRange) PUnit ≅
      M.over (V.ι ≫ f).opensRange := by
  let q := V.ι ≫ f
  let W := q.opensRange
  let E := Scheme.Modules.overEquiv W
  exact mapFreePUnitIso E.inverse
      (TopologicalSpace.Opens.sheafOfModulesEquivOverInverseUnit
        W X.ringCatSheaf).symm ≪≫
    E.inverse.mapIso
      (trivializationRestrict q.isoOpensRange.inv ((M.restrict f).restrict V.ι)
          (trivializationToRestriction (M.restrict f) V e) ≪≫
        iteratedRestrictionIso f M V) ≪≫
    E.inverse.mapIso ((Scheme.Modules.overFunctorEquiv W).app M).symm ≪≫
    (E.unitIso.app (M.over W)).symm

private theorem restrictIsInvertibleOfPullback
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules)
    (h : TauCeti.SheafOfModules.IsInvertible (R := Y.ringCatSheaf)
      ((Scheme.Modules.pullback f).obj M)) :
    TauCeti.SheafOfModules.IsInvertible (R := Y.ringCatSheaf) (M.restrict f) := by
  letI := h
  exact TauCeti.SheafOfModules.IsInvertible.of_iso (R := Y.ringCatSheaf)
    ((Scheme.Modules.restrictFunctorIsoPullback f).app M).symm

private structure SchemeLocalAtlas (Y : Scheme.{u}) (N : Y.Modules) where
  I : Type u
  X : I → Y.Opens
  coversTop : (Opens.grothendieckTopology Y).CoversTop X
  iso (i : I) :
    SheafOfModules.free (R := Y.ringCatSheaf.over (X i)) PUnit ≅ N.over (X i)

private noncomputable def SchemeLocalAtlas.ofLocalTrivializations
    {Y : Scheme.{u}} {N : Y.Modules}
    (t : TauCeti.SheafOfModules.LocalTrivializations
      (R := Y.ringCatSheaf) N) : SchemeLocalAtlas Y N where
  I := t.I
  X := t.X
  coversTop := t.coversTop
  iso := t.iso

private noncomputable def chartLocalAtlases
    {X : Scheme.{u}} (cov : X.OpenCover) (M : X.Modules)
    (h : ∀ i, TauCeti.SheafOfModules.IsInvertible (R := (cov.X i).ringCatSheaf)
      ((Scheme.Modules.pullback (cov.f i)).obj M)) :
    ∀ i, SchemeLocalAtlas (cov.X i) (M.restrict (cov.f i)) :=
  fun i ↦
    letI := restrictIsInvertibleOfPullback (cov.f i) M (h i)
    SchemeLocalAtlas.ofLocalTrivializations
      (TauCeti.SheafOfModules.LocalTrivializations.ofIsInvertible
        (M.restrict (cov.f i)))

private abbrev RefinedAtlasIndex
    {X : Scheme.{u}} (cov : X.OpenCover)
    (N : ∀ i, (cov.X i).Modules)
    (t : ∀ i, SchemeLocalAtlas (cov.X i) (N i)) :=
  Σ i, (t i).I

private noncomputable def refinedAtlasOpen
    {X : Scheme.{u}} (cov : X.OpenCover)
    (N : ∀ i, (cov.X i).Modules)
    (t : ∀ i, SchemeLocalAtlas (cov.X i) (N i))
    (ij : RefinedAtlasIndex cov N t) : X.Opens :=
  (((t ij.1).X ij.2).ι ≫ cov.f ij.1).opensRange

private theorem refinedAtlasOpen_coversTop
    {X : Scheme.{u}} (cov : X.OpenCover)
    (N : ∀ i, (cov.X i).Modules)
    (t : ∀ i, SchemeLocalAtlas (cov.X i) (N i)) :
    (Opens.grothendieckTopology X).CoversTop
      (refinedAtlasOpen cov N t) := by
  exact refinedCover cov (I := fun i ↦ (t i).I)
    (fun i j ↦ (t i).X j) (fun i ↦ (t i).coversTop)

/-- Refine rank-one trivialization atlases on all cover members to a rank-one atlas on the
original scheme. -/
private noncomputable def openCoverLocalTrivializations
    {X : Scheme.{u}} (cov : X.OpenCover) (M : X.Modules)
    (h : ∀ i, TauCeti.SheafOfModules.IsInvertible (R := (cov.X i).ringCatSheaf)
      ((Scheme.Modules.pullback (cov.f i)).obj M)) :
    TauCeti.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) M :=
  let t := chartLocalAtlases cov M h
  { I := RefinedAtlasIndex cov (fun i ↦ M.restrict (cov.f i)) t
    X := refinedAtlasOpen cov (fun i ↦ M.restrict (cov.f i)) t
    coversTop := refinedAtlasOpen_coversTop cov (fun i ↦ M.restrict (cov.f i)) t
    iso := fun ij ↦ transportChartTrivialization (cov.f ij.1) M
      ((t ij.1).X ij.2) ((t ij.1).iso ij.2) }

/-- Invertibility of scheme modules is local for arbitrary scheme open covers. -/
theorem isInvertibleOfOpenCover
    {X : Scheme.{u}} (cov : X.OpenCover) (M : X.Modules)
    (h : ∀ i, TauCeti.SheafOfModules.IsInvertible (R := (cov.X i).ringCatSheaf)
      ((Scheme.Modules.pullback (cov.f i)).obj M)) :
    TauCeti.SheafOfModules.IsInvertible (R := X.ringCatSheaf) M := by
  exact (openCoverLocalTrivializations cov.ulift M
    (fun x ↦ h (cov.idx x))).isInvertible

/-- Tau Ceti invertibility is local on every scheme open cover, discharging the exact locality
predicate used by line-bundle descent. -/
theorem invertibilityIsLocal
    {X : Scheme.{u}} (cov : X.OpenCover) : InvertibilityIsLocal cov := by
  intro M h
  exact isInvertibleOfOpenCover cov M h

/-- Ordinary module effectivity now suffices for effective descent of locally invertible data;
the former locality hypothesis is discharged by `invertibilityIsLocal`. -/
theorem invertibleEffectiveDescentFor_of_moduleEffectivity
    {X : Scheme.{u}} {cov : X.OpenCover}
    (heffective : ModuleEffectiveDescentFor cov) :
    InvertibleEffectiveDescentFor cov :=
  invertibleEffectiveDescentFor_of_moduleEffectivity_of_locality
    heffective (invertibilityIsLocal cov)

/-- On an open cover, effective descent of a locally invertible datum as a module is equivalent
to effective descent as an invertible sheaf. -/
theorem effectiveInvertible_iff_effectiveModule_of_openCover
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : InvertibleDescentData cov) :
    EffectiveInvertible cov D.toDescentData ↔
      EffectiveModule cov D.toDescentData :=
  effectiveInvertible_iff_effectiveModule D (invertibilityIsLocal cov)

end

end MazurTorsion.AlgebraicGeometry.LineBundleDescent
