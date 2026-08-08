/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.ConstantFlatBadFiberHZero

/-!
# Concrete closed-fibre control for the constant-flat supported cokernel

This file discharges the geometric obligations recorded by
`MazurConstantFlatBadFiberClosedFiberControl`.  On the fibre where the level vanishes, the
constant-flat coordinate localization is the identity component.  Consequently its represented
point sheaf restricts to zero, while the ambient-to-cokernel projection restricts to an
isomorphism.  A separate kernel calculation for the adjunction unit to the closed fibre proves
that canonical restriction of supported-cokernel sections is injective.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme

open CommGroupScheme FiniteFlatCommGroupScheme

universe w v u

/-! ### The constant-flat model on a fibre where the level vanishes -/

section Coordinates

variable {R K G : Type u} [CommRing R] [CommRing K] [Algebra R K]
  [CommGroup G] [Fintype G]

private abbrev BaseChangedConstantCoordinates :=
  K ⊗[R] ConstantCoordinates R G

private def badFiberDelta (N : R) :
    BaseChangedConstantCoordinates (R := R) (K := K) (G := G) :=
  (1 : K) ⊗ₜ[R] constantFlatElement (G := G) N

private def badFiberEvaluation :
    BaseChangedConstantCoordinates (R := R) (K := K) (G := G) →ₐ[K] K :=
  (ConstantCoordinates.evaluation (R := K) (1 : G)).comp
    (constantBaseChangeAlgEquiv (R := R) (K := K) G).toAlgHom

private theorem constantBaseChangeAlgEquiv_badFiberDelta
    (N : R) (hN : algebraMap R K N = 0) :
    constantBaseChangeAlgEquiv (R := R) (K := K) G
        (badFiberDelta (R := R) (K := K) (G := G) N) =
      constantFlatElement (G := G) (0 : K) := by
  apply ULift.down_injective
  funext g
  change
    (constantBaseChangeAlgEquiv (R := R) (K := K) G
      ((1 : K) ⊗ₜ[R] constantFlatElement (G := G) N)).down g = _
  rw [constantBaseChangeAlgEquiv_tmul,
    constantFlatElement_down_apply, constantFlatElement_down_apply]
  by_cases hg : g = 1 <;> simp [hg, hN]

omit [Fintype G] in
private theorem badFiberDelta_isIdempotentElem [Finite G]
    (N : R) (hN : algebraMap R K N = 0) :
    IsIdempotentElem
      (badFiberDelta (R := R) (K := K) (G := G) N) := by
  letI := Fintype.ofFinite G
  let e := constantBaseChangeAlgEquiv (R := R) (K := K) G
  apply e.injective
  rw [map_mul, constantBaseChangeAlgEquiv_badFiberDelta (G := G) N hN]
  apply ULift.down_injective
  funext g
  by_cases hg : g = 1 <;> simp [constantFlatElement_down_apply, hg]

private theorem badFiberEvaluation_mul_delta_eq_iff
    (N : R) (hN : algebraMap R K N = 0)
    (x y : BaseChangedConstantCoordinates (R := R) (K := K) (G := G)) :
    badFiberEvaluation (R := R) (K := K) (G := G) x =
        badFiberEvaluation (R := R) (K := K) (G := G) y ↔
      badFiberDelta (R := R) (K := K) (G := G) N * x =
        badFiberDelta (R := R) (K := K) (G := G) N * y := by
  let e := constantBaseChangeAlgEquiv (R := R) (K := K) G
  constructor
  · intro hxy
    apply e.injective
    rw [map_mul, map_mul,
      constantBaseChangeAlgEquiv_badFiberDelta (G := G) N hN]
    apply ULift.down_injective
    funext g
    by_cases hg : g = 1
    · subst g
      simpa [badFiberEvaluation, e] using hxy
    · simp [constantFlatElement_down_apply, hg]
  · intro hxy
    have h := congrArg e hxy
    have h1 := congrArg (fun f : ConstantCoordinates K G ↦ f.down (1 : G)) h
    simpa [badFiberEvaluation, e,
      constantBaseChangeAlgEquiv_badFiberDelta (G := G) N hN] using h1

private theorem badFiberEvaluation_surjective :
    Function.Surjective
      (badFiberEvaluation (R := R) (K := K) (G := G)) := by
  intro k
  refine ⟨algebraMap K
    (BaseChangedConstantCoordinates (R := R) (K := K) (G := G)) k, ?_⟩
  exact (badFiberEvaluation (R := R) (K := K) (G := G)).commutes k

private theorem badFiberAway
    (N : R) (hN : algebraMap R K N = 0) :
    let A := BaseChangedConstantCoordinates (R := R) (K := K) (G := G)
    let δ := badFiberDelta (R := R) (K := K) (G := G) N
    let φ := badFiberEvaluation (R := R) (K := K) (G := G)
    letI : Algebra A K := φ.toRingHom.toAlgebra
    IsLocalization.Away δ K := by
  dsimp only
  letI : Algebra
      (BaseChangedConstantCoordinates (R := R) (K := K) (G := G)) K :=
    (badFiberEvaluation (R := R) (K := K) (G := G)).toRingHom.toAlgebra
  apply IsLocalization.away_of_isIdempotentElem_of_mul
    (badFiberDelta_isIdempotentElem (G := G) N hN)
  · intro x y
    change badFiberEvaluation (R := R) (K := K) (G := G) x =
        badFiberEvaluation (R := R) (K := K) (G := G) y ↔ _
    exact badFiberEvaluation_mul_delta_eq_iff (G := G) N hN x y
  · exact badFiberEvaluation_surjective (R := R) (K := K) (G := G)

private noncomputable def constantFlatBadFiberCoordinatesAlgEquiv
    (N : R) (hN : algebraMap R K N = 0) :
    K ⊗[R] ConstantFlatCoordinates R G N ≃ₐ[K] K := by
  let A := BaseChangedConstantCoordinates (R := R) (K := K) (G := G)
  let δ := badFiberDelta (R := R) (K := K) (G := G) N
  let φ := badFiberEvaluation (R := R) (K := K) (G := G)
  letI : Algebra A K := φ.toRingHom.toAlgebra
  letI : IsLocalization.Away δ K := badFiberAway (G := G) N hN
  exact
    (IsLocalization.Away.tensorProductEquivTMulRight R K
      (constantFlatElement (G := G) N) (ConstantFlatCoordinates R G N)).trans
      ((IsLocalization.algEquiv (Submonoid.powers δ)
        (Localization.Away δ) K).restrictScalars K)

private theorem constantFlatAffine_baseChange_structureMap_isIso
    (N : R) (hN : algebraMap R K N = 0) :
    IsIso ((constantFlatAffine R G N).baseChange (K := K)).structureMap := by
  change IsIso (Spec.map (CommRingCat.ofHom (algebraMap K
    ((constantFlatAffine R G N).baseChange (K := K)).coordinates)))
  rw [isIso_SpecMap_iff]
  let e := constantFlatBadFiberCoordinatesAlgEquiv (G := G) N hN
  have heval (k : K) :
      e ((CommRingCat.ofHom (algebraMap K
        ((constantFlatAffine R G N).baseChange (K := K)).coordinates)).hom k) = k := by
    change e (k ⊗ₜ[R] (1 : ConstantFlatCoordinates R G N)) = k
    exact e.commutes k
  constructor
  · intro x y hxy
    simpa only [heval] using congrArg e hxy
  · intro z
    refine ⟨e z, ?_⟩
    apply e.injective
    exact heval (e z)

end Coordinates

section ClosedFiberVanishing

private abbrev FiberIndexGroup (coeffPrime : ℕ) :=
  Multiplicative (ZMod coeffPrime)

private abbrev ClosedBaseChangeConstantFlat
    (coeffPrime level : ℕ) [NeZero coeffPrime] :
    CommGroupScheme (Spec (.of (ZMod level))) :=
  (Over.pullback (zmodLevelFiberInclusion level)).mapCommGrp.obj
    (constantFlat ℤ (FiberIndexGroup coeffPrime) (level : ℤ)).obj

private theorem closedBaseChangeConstantFlat_structureMap_isIso
    (coeffPrime level : ℕ) [NeZero coeffPrime] :
    IsIso (ClosedBaseChangeConstantFlat coeffPrime level).X.hom := by
  change IsIso (((Over.pullback (zmodLevelFiberInclusion level)).mapCommGrp.obj
    (constantFlatAffine ℤ (FiberIndexGroup coeffPrime) (level : ℤ)).toCommGroupScheme).X.hom)
  letI : IsIso
      ((constantFlatAffine ℤ (FiberIndexGroup coeffPrime) (level : ℤ)).baseChange
        (K := ZMod level)).structureMap :=
    constantFlatAffine_baseChange_structureMap_isIso
      (R := ℤ) (K := ZMod level) (G := FiberIndexGroup coeffPrime)
      (level : ℤ) (by simp)
  letI : IsIso
      ((constantFlatAffine ℤ (FiberIndexGroup coeffPrime) (level : ℤ)).baseChange
        (K := ZMod level)).toCommGroupScheme.X.hom := by
    change IsIso
      ((constantFlatAffine ℤ (FiberIndexGroup coeffPrime) (level : ℤ)).baseChange
        (K := ZMod level)).structureMap
    infer_instance
  let e := AffineCommGroupScheme.realizationBaseChangeIso (K := ZMod level)
    (constantFlatAffine ℤ (FiberIndexGroup coeffPrime) (level : ℤ))
  letI : IsIso e.hom.hom.hom.hom := inferInstance
  letI : IsIso ((Over.forget (Spec (.of (ZMod level)))).map
      e.hom.hom.hom.hom) := inferInstance
  rw [← e.hom.hom.hom.hom.w]
  change IsIso (((Over.forget (Spec (.of (ZMod level)))).map
    e.hom.hom.hom.hom) ≫
      ((constantFlatAffine ℤ (FiberIndexGroup coeffPrime) (level : ℤ)).baseChange
        (K := ZMod level)).structureMap)
  exact IsIso.comp_isIso' (by infer_instance)
    (constantFlatAffine_baseChange_structureMap_isIso
      (R := ℤ) (K := ZMod level) (G := FiberIndexGroup coeffPrime)
      (level : ℤ) (by simp))

private theorem closedBaseChangeConstantFlat_point_subsingleton
    (coeffPrime level : ℕ) [NeZero coeffPrime]
    (T : Over (Spec (.of (ZMod level)))) :
    Subsingleton (CommGroupScheme.Point
      (ClosedBaseChangeConstantFlat coeffPrime level) T) := by
  letI : IsIso (ClosedBaseChangeConstantFlat coeffPrime level).X.hom :=
    closedBaseChangeConstantFlat_structureMap_isIso coeffPrime level
  constructor
  intro x y
  apply Over.OverMorphism.ext
  apply (cancel_mono (ClosedBaseChangeConstantFlat coeffPrime level).X.hom).1
  exact x.w.trans y.w.symm

private theorem sheaf_isZero_of_obj_isZero
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    {F : Sheaf J AddCommGrpCat.{w}}
    (hF : IsZero F.obj) : IsZero F :=
  IsZero.mk
    (fun _G ↦ ⟨{ default := 0, uniq := fun f ↦
      InducedCategory.Hom.ext (NatTrans.ext (funext fun U ↦
        (hF.obj U).eq_zero_of_src (f.hom.app U))) }⟩)
    (fun _G ↦ ⟨{ default := 0, uniq := fun f ↦
      InducedCategory.Hom.ext (NatTrans.ext (funext fun U ↦
        (hF.obj U).eq_zero_of_tgt (f.hom.app U))) }⟩)

private theorem constantFlatRepresentedAddPointFppfSheaf_closedFiber_isZero
    (coeffPrime level : ℕ) [NeZero coeffPrime] :
    IsZero
      ((Scheme.fppfTopology.overMapPullback AddCommGrpCat.{1}
        (zmodLevelFiberInclusion level)).obj
          (representedAddPointFppfSheaf
            (constantFlat ℤ (FiberIndexGroup coeffPrime) (level : ℤ)).obj)) := by
  apply sheaf_isZero_of_obj_isZero
  apply Functor.isZero
  intro T
  change IsZero (AddCommGrpCat.of (ULift (Additive
    ((constantFlat ℤ (FiberIndexGroup coeffPrime) (level : ℤ)).obj.Point
      ((Over.map (zmodLevelFiberInclusion level)).obj T.unop)))))
  letI : Subsingleton (CommGroupScheme.Point
      (ClosedBaseChangeConstantFlat coeffPrime level) T.unop) :=
    closedBaseChangeConstantFlat_point_subsingleton coeffPrime level T.unop
  let e := CommGroupScheme.baseChangePointMulEquiv
    (zmodLevelFiberInclusion level)
    (constantFlat ℤ (FiberIndexGroup coeffPrime) (level : ℤ)).obj T.unop
  letI : Subsingleton
      ((constantFlat ℤ (FiberIndexGroup coeffPrime) (level : ℤ)).obj.Point
        ((Over.map (zmodLevelFiberInclusion level)).obj T.unop)) :=
    e.symm.subsingleton
  exact AddCommGrpCat.isZero_of_subsingleton _

private theorem constantFlatAddPointFppfSheaf_closedFiber_isZero
    (coeffPrime level : ℕ) [NeZero coeffPrime] :
    IsZero
      ((Scheme.fppfTopology.overMapPullback AddCommGrpCat.{1}
        (zmodLevelFiberInclusion level)).obj
          (addPointFppfSheaf
            (constantFlat ℤ (FiberIndexGroup coeffPrime) (level : ℤ)).obj)) := by
  let L := Scheme.fppfTopology.overMapPullback AddCommGrpCat.{1}
    (zmodLevelFiberInclusion level)
  exact
    (constantFlatRepresentedAddPointFppfSheaf_closedFiber_isZero coeffPrime level).of_iso
      (L.mapIso (representedAddPointFppfSheafIso
        (constantFlat ℤ (FiberIndexGroup coeffPrime) (level : ℤ)).obj)).symm

private theorem zmodLevelFiberInclusion_range (level : ℕ) :
    Set.range (zmodLevelFiberInclusion level) =
      ((levelOpen (level : ℤ) : Set (Spec (.of ℤ)))ᶜ) := by
  let e := levelClosedFiberIsoZMod level
  haveI : IsIso e.hom := inferInstance
  calc
    Set.range (zmodLevelFiberInclusion level) =
        Set.range (e.hom ≫ zmodLevelFiberInclusion level) := by
      apply Set.Subset.antisymm
      · rintro y ⟨z, rfl⟩
        obtain ⟨x, hx⟩ := e.hom.surjective z
        refine ⟨x, ?_⟩
        change zmodLevelFiberInclusion level (e.hom x) =
          zmodLevelFiberInclusion level z
        rw [hx]
      · rintro y ⟨x, rfl⟩
        exact ⟨e.hom x, rfl⟩
    _ = Set.range (levelClosedFiberι (level : ℤ)) := by
      rw [levelClosedFiberIsoZMod_hom_comp_inclusion]
    _ = ((levelOpen (level : ℤ) : Set (Spec (.of ℤ)))ᶜ) :=
      (levelOpen_complement_eq_levelClosedFiberι_range (level : ℤ)).symm

private noncomputable def zmodLevelFiberPullbackBaseObjectIso (level : ℕ) :
    (Over.pullback (zmodLevelFiberInclusion level)).obj
        (CommGroupScheme.baseObject (Spec (.of ℤ))) ≅
      CommGroupScheme.baseObject (Spec (.of (ZMod level))) := by
  let e : pullback (𝟙 (Spec (.of ℤ))) (zmodLevelFiberInclusion level) ≅
      Spec (.of (ZMod level)) :=
    { hom := pullback.snd _ _
      inv := pullback.lift (zmodLevelFiberInclusion level) (𝟙 _) (by simp)
      hom_inv_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst]
          simpa using (pullback.condition
            (f := 𝟙 (Spec (.of ℤ)))
            (g := zmodLevelFiberInclusion level)).symm
        · rw [Category.assoc, pullback.lift_snd, Category.id_comp,
            Category.comp_id]
      inv_hom_id := pullback.lift_snd _ _ _ }
  exact Over.isoMk e

private noncomputable def zmodLevelFiberOverBaseIsoFiberUnitObject (level : ℕ) :
    zmodLevelFiberOverBase level ≅
      (Over.map (zmodLevelFiberInclusion level)).obj
        ((Over.pullback (zmodLevelFiberInclusion level)).obj
          (CommGroupScheme.baseObject (Spec (.of ℤ)))) :=
  zmodLevelFiberOverBaseIsoMappedBaseObject level ≪≫
    ((Over.map (zmodLevelFiberInclusion level)).mapIso
      (zmodLevelFiberPullbackBaseObjectIso level)).symm

private theorem zmodLevelFiberOverBaseIsoFiberUnitObject_hom_comp
    (level : ℕ) :
    (zmodLevelFiberOverBaseIsoFiberUnitObject level).hom ≫
        (Over.mapPullbackAdj (zmodLevelFiberInclusion level)).counit.app
          (CommGroupScheme.baseObject (Spec (.of ℤ))) =
      zmodLevelFiberToBaseObject level := by
  apply Over.OverMorphism.ext
  simpa [CommGroupScheme.baseObject] using
    (Over.w ((zmodLevelFiberOverBaseIsoFiberUnitObject level).hom ≫
      (Over.mapPullbackAdj (zmodLevelFiberInclusion level)).counit.app
        (CommGroupScheme.baseObject (Spec (.of ℤ))))).trans
      (Over.w (zmodLevelFiberToBaseObject level)).symm

private theorem constantFlat_point_range_of_pullback_eq_one
    (coeffPrime level : ℕ) [NeZero coeffPrime]
    (T : Over (Spec (.of ℤ)))
    (x : (constantScheme ℤ (FiberIndexGroup coeffPrime)).obj.Point T)
    (hx : CommGroupScheme.pullPoint
      (constantScheme ℤ (FiberIndexGroup coeffPrime)).obj
      ((Over.mapPullbackAdj (zmodLevelFiberInclusion level)).counit.app T) x = 1) :
    Set.range x.left ⊆
      ((constantFlatInclusion (R := ℤ) (G := FiberIndexGroup coeffPrime)
        (level : ℤ)).hom.hom.hom.left).opensRange := by
  rintro _ ⟨t, rfl⟩
  by_cases ht : T.hom t ∈ levelOpen (level : ℤ)
  · apply constantFlatInclusion_target_preimage_levelOpen_le
      (G := FiberIndexGroup coeffPrime) (level : ℤ)
    change (constantScheme ℤ (FiberIndexGroup coeffPrime)).obj.X.hom (x.left t) ∈
      levelOpen (level : ℤ)
    rw [← Scheme.Hom.comp_apply, x.w]
    exact ht
  · have htRange : T.hom t ∈ Set.range (zmodLevelFiberInclusion level) := by
      rw [zmodLevelFiberInclusion_range]
      exact ht
    have htPullback : t ∈ T.hom ⁻¹' Set.range (zmodLevelFiberInclusion level) :=
      htRange
    rw [← Scheme.Pullback.range_fst] at htPullback
    obtain ⟨z, hz⟩ := htPullback
    let inclusion := constantFlatInclusion
      (R := ℤ) (G := FiberIndexGroup coeffPrime) (level : ℤ)
    let oneFlat :
        (constantFlat ℤ (FiberIndexGroup coeffPrime) (level : ℤ)).obj.Point T := 1
    have himage : CommGroupScheme.mapPoint inclusion T oneFlat = 1 := map_one _
    have hpull : CommGroupScheme.pullPoint
        (constantScheme ℤ (FiberIndexGroup coeffPrime)).obj
        ((Over.mapPullbackAdj (zmodLevelFiberInclusion level)).counit.app T) x =
      CommGroupScheme.pullPoint
        (constantScheme ℤ (FiberIndexGroup coeffPrime)).obj
        ((Over.mapPullbackAdj (zmodLevelFiberInclusion level)).counit.app T)
        (CommGroupScheme.mapPoint inclusion T oneFlat) := by
      rw [hx, himage, map_one]
    have hp := congrArg (fun p ↦ p.left z) hpull
    change x.left (pullback.fst T.hom (zmodLevelFiberInclusion level) z) =
      inclusion.hom.hom.hom.left
        (oneFlat.left (pullback.fst T.hom (zmodLevelFiberInclusion level) z)) at hp
    rw [hz] at hp
    exact ⟨oneFlat.left t, hp.symm⟩

end ClosedFiberVanishing

/-! ### Restriction to a fibre and descent through an actual cokernel -/

section FiberAdjunction

/-- The adjunction between restriction to a relative fibre and pushforward from that fibre. -/
private noncomputable def fppfFiberAdjunction
    {S Z : Scheme.{u}} (i : Z ⟶ S) :
    Scheme.fppfTopology.overMapPullback AddCommGrpCat.{u + 1} i ⊣
      (Over.pullback i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (Scheme.fppfTopology.over S) (Scheme.fppfTopology.over Z) :=
  (Over.mapPullbackAdj i).sheafPushforwardContinuous
    (Scheme.fppfTopology.over Z) (Scheme.fppfTopology.over S)

private noncomputable abbrev fppfFiberPushforwardRestriction
    {S Z : Scheme.{u}} (i : Z ⟶ S)
    (A : Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}) :
    Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1} :=
  (Over.pullback i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Scheme.fppfTopology.over S) (Scheme.fppfTopology.over Z) |>.obj
    (Scheme.fppfTopology.overMapPullback AddCommGrpCat.{u + 1} i |>.obj A)

/-- The sheaf-level unit `A ⟶ i_* i^* A`. -/
private noncomputable def fppfSheafToFiberPushforward
    {S Z : Scheme.{u}} (i : Z ⟶ S)
    (A : Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}) :
    A ⟶ fppfFiberPushforwardRestriction i A :=
  (fppfFiberAdjunction i).unit.app A

private theorem fppfSheafToFiberPushforward_hom
    {S Z : Scheme.{u}} (i : Z ⟶ S)
    (A : Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}) :
    (fppfSheafToFiberPushforward i A).hom =
      Functor.whiskerRight (NatTrans.op (Over.mapPullbackAdj i).counit) A.obj :=
  rfl

private noncomputable def representedAddPointFppfMap
    {S : Scheme.{u}} {G H : CommGroupScheme S} (f : G ⟶ H) :
    representedAddPointFppfSheaf G ⟶ representedAddPointFppfSheaf H :=
  ⟨Functor.whiskerRight (addPointPresheafMap f)
    AddCommGrpCat.uliftFunctor.{u + 1}⟩

private theorem representedAddPointFppfMap_comp_sheafificationIso
    {S : Scheme.{u}} {G H : CommGroupScheme S} (f : G ⟶ H) :
    representedAddPointFppfMap f ≫ (representedAddPointFppfSheafIso H).hom =
      (representedAddPointFppfSheafIso G).hom ≫ addPointFppfMap f := by
  exact (sheafificationNatIso (Scheme.fppfTopology.over S)
    AddCommGrpCat.{u + 1}).hom.naturality (representedAddPointFppfMap f)

section MazurKernel

variable (coeffPrime level : ℕ) [NeZero coeffPrime]

private abbrev mazurFlatGroup :=
  (constantFlat ℤ (FiberIndexGroup coeffPrime) (level : ℤ)).obj

private abbrev mazurAmbientGroup :=
  (constantScheme ℤ (FiberIndexGroup coeffPrime)).obj

private abbrev mazurRepresentedSubgroupSheaf :
    Sheaf (Scheme.fppfTopology.over (Spec (.of ℤ))) AddCommGrpCat.{1} :=
  representedAddPointFppfSheaf (mazurFlatGroup coeffPrime level)

private abbrev mazurRepresentedAmbientSheaf :
    Sheaf (Scheme.fppfTopology.over (Spec (.of ℤ))) AddCommGrpCat.{1} :=
  representedAddPointFppfSheaf (mazurAmbientGroup coeffPrime)

private abbrev mazurRepresentedSubgroupMap :
    mazurRepresentedSubgroupSheaf coeffPrime level ⟶
      mazurRepresentedAmbientSheaf coeffPrime :=
  representedAddPointFppfMap
    (constantFlatInclusion (R := ℤ) (G := FiberIndexGroup coeffPrime) (level : ℤ))

private theorem mazurRepresentedSubgroupMap_comp_fiberUnit_zero :
    mazurRepresentedSubgroupMap coeffPrime level ≫
      fppfSheafToFiberPushforward (zmodLevelFiberInclusion level)
        (mazurRepresentedAmbientSheaf coeffPrime) = 0 := by
  let L := Scheme.fppfTopology.overMapPullback AddCommGrpCat.{1}
    (zmodLevelFiberInclusion level)
  let R := (Over.pullback (zmodLevelFiberInclusion level)).sheafPushforwardContinuous
    AddCommGrpCat.{1} (Scheme.fppfTopology.over (Spec (.of ℤ)))
      (Scheme.fppfTopology.over (Spec (.of (ZMod level))))
  have hsource : IsZero
      (L.obj (mazurRepresentedSubgroupSheaf coeffPrime level)) :=
    constantFlatRepresentedAddPointFppfSheaf_closedFiber_isZero coeffPrime level
  calc
    mazurRepresentedSubgroupMap coeffPrime level ≫
        fppfSheafToFiberPushforward (zmodLevelFiberInclusion level)
          (mazurRepresentedAmbientSheaf coeffPrime) =
      (fppfFiberAdjunction (zmodLevelFiberInclusion level)).unit.app
          (mazurRepresentedSubgroupSheaf coeffPrime level) ≫
        (L ⋙ R).map (mazurRepresentedSubgroupMap coeffPrime level) := by
      simpa only [Functor.id_obj, Functor.id_map, fppfSheafToFiberPushforward]
        using (fppfFiberAdjunction
          (zmodLevelFiberInclusion level)).unit.naturality
            (mazurRepresentedSubgroupMap coeffPrime level)
    _ = 0 := by
      change (fppfFiberAdjunction (zmodLevelFiberInclusion level)).unit.app _ ≫
        R.map (L.map (mazurRepresentedSubgroupMap coeffPrime level)) = 0
      have hLf : L.map (mazurRepresentedSubgroupMap coeffPrime level) = 0 :=
        hsource.eq_zero_of_src _
      rw [hLf]
      simp

private theorem mazurRepresentedFiberKernel_app_exact
    (T : (Over (Spec (.of ℤ)))ᵒᵖ) :
    let f := (mazurRepresentedSubgroupMap coeffPrime level).hom.app T
    let g := (fppfSheafToFiberPushforward (zmodLevelFiberInclusion level)
      (mazurRepresentedAmbientSheaf coeffPrime)).hom.app T
    let hzero : f ≫ g = 0 := by
      simpa using congrArg (fun k ↦ k.hom.app T)
        (mazurRepresentedSubgroupMap_comp_fiberUnit_zero coeffPrime level)
    (ShortComplex.mk f g hzero).Exact := by
  dsimp only
  rw [ShortComplex.ab_exact_iff]
  intro x hx
  change ULift (Additive ((mazurAmbientGroup coeffPrime).Point T.unop)) at x
  have hxPoint : CommGroupScheme.pullPoint (mazurAmbientGroup coeffPrime)
      ((Over.mapPullbackAdj (zmodLevelFiberInclusion level)).counit.app T.unop)
        x.down.toMul = 1 := by
    have h := congrArg (fun y ↦ y.down.toMul) hx
    change ((Over.mapPullbackAdj (zmodLevelFiberInclusion level)).counit.app T.unop ≫
      x.down.toMul) = 1 at h
    exact h
  let y := CommGroupScheme.pointLiftThroughOpen
    (constantFlatInclusion (R := ℤ) (G := FiberIndexGroup coeffPrime) (level : ℤ))
    T.unop x.down.toMul
    (constantFlat_point_range_of_pullback_eq_one coeffPrime level T.unop x.down.toMul hxPoint)
  refine ⟨ULift.up (Additive.ofMul y), ?_⟩
  apply ULift.down_injective
  exact CommGroupScheme.mapPoint_pointLiftThroughOpen
    (constantFlatInclusion (R := ℤ) (G := FiberIndexGroup coeffPrime) (level : ℤ))
    T.unop x.down.toMul _

end MazurKernel

private noncomputable def subgroupFiberKernelComplex
    {S Z : Scheme.{u}} (i : Z ⟶ S)
    {A₁ A₂ : Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}}
    (f : A₁ ⟶ A₂)
    (hzero : f ≫ fppfSheafToFiberPushforward i A₂ = 0) :
    ShortComplex (Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}) :=
  ShortComplex.mk f (fppfSheafToFiberPushforward i A₂) hzero

section MazurKernelExact

variable (coeffPrime level : ℕ) [NeZero coeffPrime]

private theorem mazurRepresentedFiberKernel_exact :
    (subgroupFiberKernelComplex (zmodLevelFiberInclusion level)
      (mazurRepresentedSubgroupMap coeffPrime level)
      (mazurRepresentedSubgroupMap_comp_fiberUnit_zero coeffPrime level)).Exact := by
  let inclusion := constantFlatInclusion
    (R := ℤ) (G := FiberIndexGroup coeffPrime) (level : ℤ)
  let S := subgroupFiberKernelComplex (zmodLevelFiberInclusion level)
    (mazurRepresentedSubgroupMap coeffPrime level)
    (mazurRepresentedSubgroupMap_comp_fiberUnit_zero coeffPrime level)
  let U := sheafToPresheaf (Scheme.fppfTopology.over (Spec (.of ℤ)))
    AddCommGrpCat.{1}
  haveI : Mono (commPointPresheafMap inclusion) := by
    rw [NatTrans.mono_iff_mono_app]
    intro T
    apply ConcreteCategory.mono_of_injective
    exact mapPoint_injective_of_mono inclusion T.unop
  haveI : Mono (addPointPresheafMap inclusion) := by
    dsimp [addPointPresheafMap]
    infer_instance
  haveI : Mono (mazurRepresentedSubgroupMap coeffPrime level).hom := by
    change Mono (Functor.whiskerRight (addPointPresheafMap inclusion)
      AddCommGrpCat.uliftFunctor.{1})
    infer_instance
  haveI : Mono (S.map U).f := by
    change Mono (mazurRepresentedSubgroupMap coeffPrime level).hom
    infer_instance
  have hpre : (S.map U).Exact := by
    apply ShortComplex.exact_of_f_is_kernel
    apply evaluationJointlyReflectsLimits
    intro T
    apply (KernelFork.isLimitMapConeEquiv ..).2
    have hT := mazurRepresentedFiberKernel_app_exact coeffPrime level T
    haveI : Mono ((S.map U).f.app T) := by
      apply (NatTrans.mono_iff_mono_app _).mp
        (show Mono (S.map U).f by
          change Mono (mazurRepresentedSubgroupMap coeffPrime level).hom
          infer_instance)
    exact hT.fIsKernel
  apply ShortComplex.exact_of_f_is_kernel
  apply isLimitOfReflects U
  exact (KernelFork.isLimitMapConeEquiv ..).2 hpre.fIsKernel

private abbrev mazurCokernelSheaf :
    Sheaf (Scheme.fppfTopology.over (Spec (.of ℤ))) AddCommGrpCat.{1} :=
  constantFlatPointCokernelFppfSheaf
    (R := ℤ) (G := FiberIndexGroup coeffPrime) (level : ℤ)

private abbrev mazurRepresentedCokernelProjection :
    mazurRepresentedAmbientSheaf coeffPrime ⟶
      mazurCokernelSheaf coeffPrime level :=
  constantFlatRepresentedPointCokernelFppfProjection
    (R := ℤ) (G := FiberIndexGroup coeffPrime) (level : ℤ)

private theorem mazurRepresentedSubgroupMap_comp_cokernelProjection_zero :
    mazurRepresentedSubgroupMap coeffPrime level ≫
      mazurRepresentedCokernelProjection coeffPrime level = 0 := by
  let inclusion := constantFlatInclusion
    (R := ℤ) (G := FiberIndexGroup coeffPrime) (level : ℤ)
  calc
    representedAddPointFppfMap inclusion ≫
        ((representedAddPointFppfSheafIso (mazurAmbientGroup coeffPrime)).hom ≫
          pointCokernelFppfProjection inclusion) =
      (representedAddPointFppfMap inclusion ≫
        (representedAddPointFppfSheafIso (mazurAmbientGroup coeffPrime)).hom) ≫
          pointCokernelFppfProjection inclusion := (Category.assoc _ _ _).symm
    _ = ((representedAddPointFppfSheafIso
          (mazurFlatGroup coeffPrime level)).hom ≫ addPointFppfMap inclusion) ≫
        pointCokernelFppfProjection inclusion := by
      rw [representedAddPointFppfMap_comp_sheafificationIso]
    _ = (representedAddPointFppfSheafIso
          (mazurFlatGroup coeffPrime level)).hom ≫
        (addPointFppfMap inclusion ≫ pointCokernelFppfProjection inclusion) :=
      Category.assoc _ _ _
    _ = 0 := by
      have hz : addPointFppfMap inclusion ≫
          pointCokernelFppfProjection inclusion = 0 :=
        (pointCokernelFppfSequence inclusion).zero
      rw [hz, comp_zero]

private noncomputable def mazurRepresentedCokernelSequence :
    ShortComplex
      (Sheaf (Scheme.fppfTopology.over (Spec (.of ℤ))) AddCommGrpCat.{1}) :=
  ShortComplex.mk (mazurRepresentedSubgroupMap coeffPrime level)
    (mazurRepresentedCokernelProjection coeffPrime level)
    (mazurRepresentedSubgroupMap_comp_cokernelProjection_zero coeffPrime level)

private theorem mazurRepresentedCokernelSequence_exact :
    (mazurRepresentedCokernelSequence coeffPrime level).Exact := by
  let inclusion := constantFlatInclusion
    (R := ℤ) (G := FiberIndexGroup coeffPrime) (level : ℤ)
  let S₀ := pointCokernelFppfSequence inclusion
  let S := mazurRepresentedCokernelSequence coeffPrime level
  let e : S ≅ S₀ :=
    ShortComplex.isoMk
      (representedAddPointFppfSheafIso (mazurFlatGroup coeffPrime level))
      (representedAddPointFppfSheafIso (mazurAmbientGroup coeffPrime))
      (Iso.refl _) (by
        exact (representedAddPointFppfMap_comp_sheafificationIso inclusion).symm)
      (by
        change (representedAddPointFppfSheafIso
            (mazurAmbientGroup coeffPrime)).hom ≫
              pointCokernelFppfProjection inclusion =
          ((representedAddPointFppfSheafIso
            (mazurAmbientGroup coeffPrime)).hom ≫
              pointCokernelFppfProjection inclusion) ≫ 𝟙 _
        simp)
  exact ShortComplex.exact_of_iso e.symm (pointCokernelFppfSequence_exact inclusion)

private noncomputable def mazurRepresentedCokernelProjection_isCokernel :
    IsColimit (CokernelCofork.ofπ
      (mazurRepresentedCokernelProjection coeffPrime level)
      (mazurRepresentedSubgroupMap_comp_cokernelProjection_zero coeffPrime level)) := by
  letI : Epi (mazurRepresentedCokernelProjection coeffPrime level) := inferInstance
  letI : Epi (mazurRepresentedCokernelSequence coeffPrime level).g := by
    change Epi (mazurRepresentedCokernelProjection coeffPrime level)
    infer_instance
  exact (mazurRepresentedCokernelSequence_exact coeffPrime level).gIsCokernel

end MazurKernelExact

private noncomputable def descendFiberUnitThroughCokernel
    {S Z : Scheme.{u}} (i : Z ⟶ S)
    {A₁ A₂ Q : Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}}
    (f : A₁ ⟶ A₂) (q : A₂ ⟶ Q)
    (hzeroQ : f ≫ q = 0)
    (hq : IsColimit (CokernelCofork.ofπ q hzeroQ))
    (hzero : f ≫ fppfSheafToFiberPushforward i A₂ = 0) :
    Q ⟶ fppfFiberPushforwardRestriction i A₂ :=
  hq.desc (CokernelCofork.ofπ (fppfSheafToFiberPushforward i A₂) hzero)

private theorem descendFiberUnitThroughCokernel_mono
    {S Z : Scheme.{u}} (i : Z ⟶ S)
    {A₁ A₂ Q : Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}}
    (f : A₁ ⟶ A₂) (q : A₂ ⟶ Q)
    (hzeroQ : f ≫ q = 0)
    (hq : IsColimit (CokernelCofork.ofπ q hzeroQ))
    (hzero : f ≫ fppfSheafToFiberPushforward i A₂ = 0)
    (hexact : (subgroupFiberKernelComplex i f hzero).Exact) :
    Mono (descendFiberUnitThroughCokernel i f q hzeroQ hq hzero) := by
  let d := descendFiberUnitThroughCokernel i f q hzeroQ hq hzero
  let hright : (subgroupFiberKernelComplex i f hzero).RightHomologyData :=
    { Q := Q
      H := kernel d
      p := q
      «ι» := kernel.ι d
      wp := hzeroQ
      hp := hq
      «wι» := kernel.condition d
      «hι» := kernelIsKernel d }
  have hm := hexact.mono_g' hright
  have heq : hright.g' = d := by
    dsimp only [hright, ShortComplex.RightHomologyData.g',
      ShortComplex.RightHomologyData.descQ, subgroupFiberKernelComplex, d,
      descendFiberUnitThroughCokernel]
  change Mono d
  rw [← heq]
  exact hm

private theorem cokernelFiberRestrictionUnit_mono
    {S Z : Scheme.{u}} (i : Z ⟶ S)
    {A₁ A₂ Q : Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}}
    (f : A₁ ⟶ A₂) (q : A₂ ⟶ Q)
    (hzeroQ : f ≫ q = 0)
    (hq : IsColimit (CokernelCofork.ofπ q hzeroQ))
    (hzero : f ≫ fppfSheafToFiberPushforward i A₂ = 0)
    (hexact : (subgroupFiberKernelComplex i f hzero).Exact) :
    Mono ((fppfFiberAdjunction i).unit.app Q) := by
  let d := descendFiberUnitThroughCokernel i f q hzeroQ hq hzero
  let c :
      (Scheme.fppfTopology.overMapPullback AddCommGrpCat.{u + 1} i).obj Q ⟶
        (Scheme.fppfTopology.overMapPullback AddCommGrpCat.{u + 1} i).obj A₂ :=
    ((fppfFiberAdjunction i).homEquiv _ _).symm d
  let R := (Over.pullback i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Scheme.fppfTopology.over S) (Scheme.fppfTopology.over Z)
  have hd : Mono d :=
    descendFiberUnitThroughCokernel_mono i f q hzeroQ hq hzero hexact
  have hfac :
      (fppfFiberAdjunction i).unit.app Q ≫ R.map c = d := by
    dsimp [c, R]
    rw [← CategoryTheory.Adjunction.homEquiv_unit]
    exact Equiv.apply_symm_apply ((fppfFiberAdjunction i).homEquiv _ _) d
  haveI : Mono ((fppfFiberAdjunction i).unit.app Q ≫ R.map c) := by
    rw [hfac]
    exact hd
  constructor
  intro T g h e
  apply (cancel_mono ((fppfFiberAdjunction i).unit.app Q ≫ R.map c)).mp
  simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ R.map c) e

private theorem cokernelFiberRestrictionUnit_app_injective
    {S Z : Scheme.{u}} (i : Z ⟶ S)
    {A₁ A₂ Q : Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}}
    (f : A₁ ⟶ A₂) (q : A₂ ⟶ Q)
    (hzeroQ : f ≫ q = 0)
    (hq : IsColimit (CokernelCofork.ofπ q hzeroQ))
    (hzero : f ≫ fppfSheafToFiberPushforward i A₂ = 0)
    (hexact : (subgroupFiberKernelComplex i f hzero).Exact)
    (T : (Over S)ᵒᵖ) :
    Function.Injective (((fppfFiberAdjunction i).unit.app Q).hom.app T) := by
  letI : Mono ((fppfFiberAdjunction i).unit.app Q) :=
    cokernelFiberRestrictionUnit_mono i f q hzeroQ hq hzero hexact
  haveI : Mono ((fppfFiberAdjunction i).unit.app Q).hom := inferInstance
  haveI : Mono (((fppfFiberAdjunction i).unit.app Q).hom.app T) :=
    (NatTrans.mono_iff_mono_app _).mp (by infer_instance) T
  exact (AddCommGrpCat.mono_iff_injective _).mp (by infer_instance)

/-! ### The concrete Mazur restriction map -/

private theorem mazurCokernelFiberUnit_base_injective
    (coeffPrime level : ℕ) [NeZero coeffPrime] :
    Function.Injective
      (((fppfFiberAdjunction (zmodLevelFiberInclusion level)).unit.app
        (mazurCokernelSheaf coeffPrime level)).hom.app
          (op (CommGroupScheme.baseObject (Spec (.of ℤ))))) := by
  exact cokernelFiberRestrictionUnit_app_injective
    (zmodLevelFiberInclusion level)
    (mazurRepresentedSubgroupMap coeffPrime level)
    (mazurRepresentedCokernelProjection coeffPrime level)
    (mazurRepresentedSubgroupMap_comp_cokernelProjection_zero coeffPrime level)
    (mazurRepresentedCokernelProjection_isCokernel coeffPrime level)
    (mazurRepresentedSubgroupMap_comp_fiberUnit_zero coeffPrime level)
    (mazurRepresentedFiberKernel_exact coeffPrime level)
    (op (CommGroupScheme.baseObject (Spec (.of ℤ))))

private theorem mazurConstantFlatBadFiberRestriction_add_injective
    (coeffPrime level : ℕ) [NeZero coeffPrime] :
    Function.Injective
      (((mazurCokernelSheaf coeffPrime level).obj.map
        (zmodLevelFiberToBaseObject level).op).hom) := by
  let i := zmodLevelFiberInclusion level
  let Q := mazurCokernelSheaf coeffPrime level
  let T := CommGroupScheme.baseObject (Spec (.of ℤ))
  let e := zmodLevelFiberOverBaseIsoFiberUnitObject level
  have hunit : Function.Injective
      (((fppfFiberAdjunction i).unit.app Q).hom.app (op T)) :=
    mazurCokernelFiberUnit_base_injective coeffPrime level
  have he : Function.Injective (Q.obj.map e.hom.op) :=
    (AddCommGrpCat.mono_iff_injective _).mp (by infer_instance)
  have hcomp :
      ((fppfFiberAdjunction i).unit.app Q).hom.app (op T) ≫
          Q.obj.map e.hom.op =
        Q.obj.map (zmodLevelFiberToBaseObject level).op := by
    change Q.obj.map
        ((Over.mapPullbackAdj i).counit.app T).op ≫
          Q.obj.map e.hom.op =
        Q.obj.map (zmodLevelFiberToBaseObject level).op
    rw [← Functor.map_comp, ← op_comp,
      zmodLevelFiberOverBaseIsoFiberUnitObject_hom_comp]
  have hinjective : Function.Injective
      (((fppfFiberAdjunction i).unit.app Q).hom.app (op T) ≫
        Q.obj.map e.hom.op) := he.comp hunit
  rw [hcomp] at hinjective
  exact hinjective

/-- Canonical restriction of the actual supported cokernel to `Spec (ZMod level)` is
injective. -/
theorem mazurConstantFlatBadFiberRestriction_injective
    (coeffPrime level : ℕ) [NeZero coeffPrime] :
    Function.Injective
      (mazurConstantFlatBadFiberRestriction coeffPrime level) := by
  exact mazurConstantFlatBadFiberRestriction_add_injective coeffPrime level

/-! ### The evaluated projection on the bad fibre -/

private noncomputable instance fppfFiberRestriction_preservesFiniteColimits
    {S Z : Scheme.{u}} (i : Z ⟶ S) :
    PreservesFiniteColimits
      (Scheme.fppfTopology.overMapPullback AddCommGrpCat.{u + 1} i) := by
  let L := Scheme.fppfTopology.overMapPullback AddCommGrpCat.{u + 1} i
  letI : L.IsLeftAdjoint := (fppfFiberAdjunction i).isLeftAdjoint
  infer_instance

private theorem mazurRepresentedCokernelProjection_closedFiber_isIso
    (coeffPrime level : ℕ) [NeZero coeffPrime] :
    IsIso
      ((Scheme.fppfTopology.overMapPullback AddCommGrpCat.{1}
        (zmodLevelFiberInclusion level)).map
          (mazurRepresentedCokernelProjection coeffPrime level)) := by
  let inclusion := constantFlatInclusion
    (R := ℤ) (G := FiberIndexGroup coeffPrime) (level : ℤ)
  let L := Scheme.fppfTopology.overMapPullback AddCommGrpCat.{1}
    (zmodLevelFiberInclusion level)
  have hshort :=
    (pointCokernelFppfSequence_shortExact_of_mono inclusion).map_of_exact L
  haveI : IsIso (L.map (pointCokernelFppfProjection inclusion)) :=
    hshort.isIso_g_iff.mpr
      (constantFlatAddPointFppfSheaf_closedFiber_isZero coeffPrime level)
  change IsIso (L.map
    ((representedAddPointFppfSheafIso (mazurAmbientGroup coeffPrime)).hom ≫
      pointCokernelFppfProjection inclusion))
  rw [Functor.map_comp]
  infer_instance

private theorem mazurRepresentedCokernelProjection_mappedBase_isIso
    (coeffPrime level : ℕ) [NeZero coeffPrime] :
    IsIso ((mazurRepresentedCokernelProjection coeffPrime level).hom.app
      (op ((Over.map (zmodLevelFiberInclusion level)).obj
        (CommGroupScheme.baseObject (Spec (.of (ZMod level))))))) := by
  let L := Scheme.fppfTopology.overMapPullback AddCommGrpCat.{1}
    (zmodLevelFiberInclusion level)
  letI : IsIso
      (L.map (mazurRepresentedCokernelProjection coeffPrime level)) :=
    mazurRepresentedCokernelProjection_closedFiber_isIso coeffPrime level
  change IsIso
    ((L.map (mazurRepresentedCokernelProjection coeffPrime level)).hom.app
      (op (CommGroupScheme.baseObject (Spec (.of (ZMod level))))))
  infer_instance

private theorem mazurRepresentedCokernelProjection_badFiber_isIso
    (coeffPrime level : ℕ) [NeZero coeffPrime] :
    IsIso ((mazurRepresentedCokernelProjection coeffPrime level).hom.app
      (op (zmodLevelFiberOverBase level))) := by
  let A := mazurRepresentedAmbientSheaf coeffPrime
  let Q := mazurCokernelSheaf coeffPrime level
  let q := mazurRepresentedCokernelProjection coeffPrime level
  let e := zmodLevelFiberOverBaseIsoMappedBaseObject level
  haveI : IsIso (q.hom.app
      (op ((Over.map (zmodLevelFiberInclusion level)).obj
        (CommGroupScheme.baseObject (Spec (.of (ZMod level))))))) :=
    mazurRepresentedCokernelProjection_mappedBase_isIso coeffPrime level
  have hnat := q.hom.naturality e.hom.op
  haveI : IsIso (A.obj.map e.hom.op) := inferInstance
  haveI : IsIso (Q.obj.map e.hom.op) := inferInstance
  haveI : IsIso
      (A.obj.map e.hom.op ≫ q.hom.app (op (zmodLevelFiberOverBase level))) := by
    rw [hnat]
    infer_instance
  exact IsIso.of_isIso_comp_left (A.obj.map e.hom.op)
    (q.hom.app (op (zmodLevelFiberOverBase level)))

end FiberAdjunction

/-! ### Concrete closed-fibre control -/

/-- The inverse of the actual evaluated ambient-to-cokernel projection on the bad fibre. -/
noncomputable def mazurConstantFlatBadFiberComparison
    (coeffPrime level : ℕ) [NeZero coeffPrime] :
    MazurConstantFlatClosedFiberCokernelHZero coeffPrime level →*
      MazurConstantFlatClosedFiberAmbientHZero coeffPrime level := by
  let q := (mazurRepresentedCokernelProjection coeffPrime level).hom.app
    (op (zmodLevelFiberOverBase level))
  letI : IsIso q :=
    mazurRepresentedCokernelProjection_badFiber_isIso coeffPrime level
  exact AddMonoidHom.toMultiplicative (inv q).hom

/-- The concrete comparison splits the actual evaluated fppf-cokernel projection. -/
theorem mazurConstantFlatBadFiberProjection_comp_comparison
    (coeffPrime level : ℕ) [NeZero coeffPrime] :
    (mazurConstantFlatClosedFiberCokernelProjection coeffPrime level).comp
        (mazurConstantFlatBadFiberComparison coeffPrime level) =
      MonoidHom.id _ := by
  let q := (mazurRepresentedCokernelProjection coeffPrime level).hom.app
    (op (zmodLevelFiberOverBase level))
  letI : IsIso q :=
    mazurRepresentedCokernelProjection_badFiber_isIso coeffPrime level
  apply MonoidHom.ext
  intro x
  change (inv q ≫ q) x = x
  rw [IsIso.inv_hom_id]
  rfl

/-- Concrete closed-fibre control for Mazur's constant-flat supported cokernel.  Both fields are
proved from the represented group schemes and the actual sheaf cokernel. -/
noncomputable def mazurConstantFlatBadFiberClosedFiberControl
    (coeffPrime level : ℕ) [NeZero coeffPrime] :
    MazurConstantFlatBadFiberClosedFiberControl coeffPrime level :=
  { comparison := mazurConstantFlatBadFiberComparison coeffPrime level
    projection_comp_comparison :=
      mazurConstantFlatBadFiberProjection_comp_comparison coeffPrime level
    restriction_injective :=
      mazurConstantFlatBadFiberRestriction_injective coeffPrime level }

end AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme
