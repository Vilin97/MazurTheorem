/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfHOneUniverse
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.SupportedFppfHOne

/-!
# The represented-group-scheme spelling of supported fppf `H¹`

The supported-cokernel calculation uses universe-lifted additive point sheaves, whereas the
original group-scheme API uses the represented multiplicative point presheaf.  This file proves
that these are the same checked `H¹` after passing to an open subscheme.

There are three genuine comparisons.  First, the pullback adjunction identifies points of the
canonical base-changed commutative group scheme with restricted points of the original scheme;
the proof below checks the group law against the cartesian tensor comparison for pullback.
Second, the represented point presheaf is already an fppf sheaf, so its canonical sheafification
isomorphism may be restricted to the open.  No compatibility between arbitrary sheafification
and base change is assumed.  Third, `Scheme.FppfHOne.mulEquivUlift` supplies the previously
checked cocycle-level universe invariance.

The final constant-flat and multiplicative-flat declarations are downstream consumers stated
entirely with `CommGroupScheme.FppfHOne` of canonical base changes.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace AlgebraicGeometry.CommGroupScheme

universe v u

variable {S T : Scheme.{u}}
variable (f : T ⟶ S) (G : CommGroupScheme S)

private noncomputable def pullbackPointMulEquiv (X : Over T) :
    (X ⟶ (Over.pullback f).obj G.X) ≃* ((Over.map f).obj X ⟶ G.X) where
  toEquiv := ((Over.mapPullbackAdj f).homEquiv X G.X).symm
  map_mul' x y := by
    simp only [CategoryTheory.Hom.mul_def]
    change
      (Over.map f).map
          (CartesianMonoidalCategory.lift x y ≫
            μ[(Over.pullback f).obj G.X]) ≫
          (Over.mapPullbackAdj f).counit.app G.X =
        CartesianMonoidalCategory.lift
            ((Over.map f).map x ≫ (Over.mapPullbackAdj f).counit.app G.X)
            ((Over.map f).map y ≫ (Over.mapPullbackAdj f).counit.app G.X) ≫
          μ[G.X]
    rw [Functor.obj.μ_def]
    have hpair :
        (Over.map f).map
            (CartesianMonoidalCategory.lift x y ≫
              Functor.LaxMonoidal.μ (Over.pullback f) G.X G.X) ≫
            (Over.mapPullbackAdj f).counit.app
              (MonoidalCategoryStruct.tensorObj G.X G.X) =
          CartesianMonoidalCategory.lift
            ((Over.map f).map x ≫ (Over.mapPullbackAdj f).counit.app G.X)
            ((Over.map f).map y ≫ (Over.mapPullbackAdj f).counit.app G.X) := by
      apply CartesianMonoidalCategory.hom_ext
      · have hcounit :
            (Over.mapPullbackAdj f).counit.app
                (MonoidalCategoryStruct.tensorObj G.X G.X) ≫
                CartesianMonoidalCategory.fst G.X G.X =
              (Over.map f).map ((Over.pullback f).map
                  (CartesianMonoidalCategory.fst G.X G.X)) ≫
                (Over.mapPullbackAdj f).counit.app G.X := by
          simpa using ((Over.mapPullbackAdj f).counit.naturality
            (CartesianMonoidalCategory.fst G.X G.X)).symm
        have hsource :
            (CartesianMonoidalCategory.lift x y ≫
                Functor.LaxMonoidal.μ (Over.pullback f) G.X G.X) ≫
                (Over.pullback f).map
                  (CartesianMonoidalCategory.fst G.X G.X) = x := by
          rw [Category.assoc, Functor.Monoidal.μ_fst,
            CartesianMonoidalCategory.lift_fst]
        calc
          ((Over.map f).map
                (CartesianMonoidalCategory.lift x y ≫
                  Functor.LaxMonoidal.μ (Over.pullback f) G.X G.X) ≫
              (Over.mapPullbackAdj f).counit.app
                (MonoidalCategoryStruct.tensorObj G.X G.X)) ≫
              CartesianMonoidalCategory.fst G.X G.X =
              (Over.map f).map
                  (CartesianMonoidalCategory.lift x y ≫
                    Functor.LaxMonoidal.μ (Over.pullback f) G.X G.X) ≫
                ((Over.mapPullbackAdj f).counit.app
                    (MonoidalCategoryStruct.tensorObj G.X G.X) ≫
                  CartesianMonoidalCategory.fst G.X G.X) :=
            Category.assoc _ _ _
          _ = (Over.map f).map
                  (CartesianMonoidalCategory.lift x y ≫
                    Functor.LaxMonoidal.μ (Over.pullback f) G.X G.X) ≫
                ((Over.map f).map ((Over.pullback f).map
                    (CartesianMonoidalCategory.fst G.X G.X)) ≫
                  (Over.mapPullbackAdj f).counit.app G.X) := by rw [hcounit]
          _ = ((Over.map f).map
                  (CartesianMonoidalCategory.lift x y ≫
                    Functor.LaxMonoidal.μ (Over.pullback f) G.X G.X) ≫
                (Over.map f).map ((Over.pullback f).map
                  (CartesianMonoidalCategory.fst G.X G.X))) ≫
                (Over.mapPullbackAdj f).counit.app G.X :=
            (Category.assoc _ _ _).symm
          _ = (Over.map f).map
                  ((CartesianMonoidalCategory.lift x y ≫
                      Functor.LaxMonoidal.μ (Over.pullback f) G.X G.X) ≫
                    (Over.pullback f).map
                      (CartesianMonoidalCategory.fst G.X G.X)) ≫
                (Over.mapPullbackAdj f).counit.app G.X := by
            rw [(Over.map f).map_comp, (Over.map f).map_comp,
              (Over.map f).map_comp]
          _ = (Over.map f).map x ≫
                (Over.mapPullbackAdj f).counit.app G.X := by rw [hsource]
          _ = CartesianMonoidalCategory.lift
                  ((Over.map f).map x ≫ (Over.mapPullbackAdj f).counit.app G.X)
                  ((Over.map f).map y ≫ (Over.mapPullbackAdj f).counit.app G.X) ≫
                CartesianMonoidalCategory.fst G.X G.X :=
            (CartesianMonoidalCategory.lift_fst _ _).symm
      · have hcounit :
            (Over.mapPullbackAdj f).counit.app
                (MonoidalCategoryStruct.tensorObj G.X G.X) ≫
                CartesianMonoidalCategory.snd G.X G.X =
              (Over.map f).map ((Over.pullback f).map
                  (CartesianMonoidalCategory.snd G.X G.X)) ≫
                (Over.mapPullbackAdj f).counit.app G.X := by
          simpa using ((Over.mapPullbackAdj f).counit.naturality
            (CartesianMonoidalCategory.snd G.X G.X)).symm
        have hsource :
            (CartesianMonoidalCategory.lift x y ≫
                Functor.LaxMonoidal.μ (Over.pullback f) G.X G.X) ≫
                (Over.pullback f).map
                  (CartesianMonoidalCategory.snd G.X G.X) = y := by
          rw [Category.assoc, Functor.Monoidal.μ_snd,
            CartesianMonoidalCategory.lift_snd]
        calc
          ((Over.map f).map
                (CartesianMonoidalCategory.lift x y ≫
                  Functor.LaxMonoidal.μ (Over.pullback f) G.X G.X) ≫
              (Over.mapPullbackAdj f).counit.app
                (MonoidalCategoryStruct.tensorObj G.X G.X)) ≫
              CartesianMonoidalCategory.snd G.X G.X =
              (Over.map f).map
                  (CartesianMonoidalCategory.lift x y ≫
                    Functor.LaxMonoidal.μ (Over.pullback f) G.X G.X) ≫
                ((Over.mapPullbackAdj f).counit.app
                    (MonoidalCategoryStruct.tensorObj G.X G.X) ≫
                  CartesianMonoidalCategory.snd G.X G.X) :=
            Category.assoc _ _ _
          _ = (Over.map f).map
                  (CartesianMonoidalCategory.lift x y ≫
                    Functor.LaxMonoidal.μ (Over.pullback f) G.X G.X) ≫
                ((Over.map f).map ((Over.pullback f).map
                    (CartesianMonoidalCategory.snd G.X G.X)) ≫
                  (Over.mapPullbackAdj f).counit.app G.X) := by rw [hcounit]
          _ = ((Over.map f).map
                  (CartesianMonoidalCategory.lift x y ≫
                    Functor.LaxMonoidal.μ (Over.pullback f) G.X G.X) ≫
                (Over.map f).map ((Over.pullback f).map
                  (CartesianMonoidalCategory.snd G.X G.X))) ≫
                (Over.mapPullbackAdj f).counit.app G.X :=
            (Category.assoc _ _ _).symm
          _ = (Over.map f).map
                  ((CartesianMonoidalCategory.lift x y ≫
                      Functor.LaxMonoidal.μ (Over.pullback f) G.X G.X) ≫
                    (Over.pullback f).map
                      (CartesianMonoidalCategory.snd G.X G.X)) ≫
                (Over.mapPullbackAdj f).counit.app G.X := by
            rw [(Over.map f).map_comp, (Over.map f).map_comp,
              (Over.map f).map_comp]
          _ = (Over.map f).map y ≫
                (Over.mapPullbackAdj f).counit.app G.X := by rw [hsource]
          _ = CartesianMonoidalCategory.lift
                  ((Over.map f).map x ≫ (Over.mapPullbackAdj f).counit.app G.X)
                  ((Over.map f).map y ≫ (Over.mapPullbackAdj f).counit.app G.X) ≫
                CartesianMonoidalCategory.snd G.X G.X :=
            (CartesianMonoidalCategory.lift_snd _ _).symm
    have hcounitMul :
        (Over.map f).map ((Over.pullback f).map μ[G.X]) ≫
            (Over.mapPullbackAdj f).counit.app G.X =
          (Over.mapPullbackAdj f).counit.app
              (MonoidalCategoryStruct.tensorObj G.X G.X) ≫ μ[G.X] := by
      simpa using (Over.mapPullbackAdj f).counit.naturality μ[G.X]
    calc
      (Over.map f).map
            ((CartesianMonoidalCategory.lift x y ≫
                Functor.LaxMonoidal.μ (Over.pullback f) G.X G.X) ≫
              (Over.pullback f).map μ[G.X]) ≫
          (Over.mapPullbackAdj f).counit.app G.X =
          ((Over.map f).map
              (CartesianMonoidalCategory.lift x y ≫
                Functor.LaxMonoidal.μ (Over.pullback f) G.X G.X) ≫
            (Over.map f).map ((Over.pullback f).map μ[G.X])) ≫
              (Over.mapPullbackAdj f).counit.app G.X := by
        rw [(Over.map f).map_comp]
      _ = (Over.map f).map
              (CartesianMonoidalCategory.lift x y ≫
                Functor.LaxMonoidal.μ (Over.pullback f) G.X G.X) ≫
            ((Over.map f).map ((Over.pullback f).map μ[G.X]) ≫
              (Over.mapPullbackAdj f).counit.app G.X) :=
        Category.assoc _ _ _
      _ = (Over.map f).map
              (CartesianMonoidalCategory.lift x y ≫
                Functor.LaxMonoidal.μ (Over.pullback f) G.X G.X) ≫
            ((Over.mapPullbackAdj f).counit.app
                (MonoidalCategoryStruct.tensorObj G.X G.X) ≫ μ[G.X]) := by
        rw [hcounitMul]
      _ = ((Over.map f).map
              (CartesianMonoidalCategory.lift x y ≫
                Functor.LaxMonoidal.μ (Over.pullback f) G.X G.X) ≫
            (Over.mapPullbackAdj f).counit.app
              (MonoidalCategoryStruct.tensorObj G.X G.X)) ≫ μ[G.X] :=
        (Category.assoc _ _ _).symm
      _ = CartesianMonoidalCategory.lift
              ((Over.map f).map x ≫ (Over.mapPullbackAdj f).counit.app G.X)
              ((Over.map f).map y ≫ (Over.mapPullbackAdj f).counit.app G.X) ≫
            μ[G.X] := by rw [hpair]

/-- The pullback adjunction identifies points of the canonical base-changed commutative group
scheme with restricted points of the original scheme, as multiplicative groups. -/
noncomputable def baseChangePointMulEquiv (X : Over T) :
    CommGroupScheme.Point ((Over.pullback f).mapCommGrp.obj G) X ≃*
      G.Point ((Over.map f).obj X) :=
  pullbackPointMulEquiv f G X

/-- The pointwise base-change equivalence is natural in the test scheme.  Thus the point
presheaf of the canonical base change is the restriction of the original point presheaf. -/
noncomputable def baseChangeCommPointPresheafIso :
    CommGroupScheme.commPointPresheaf ((Over.pullback f).mapCommGrp.obj G) ≅
      (Over.map f).op ⋙ G.commPointPresheaf :=
  NatIso.ofComponents
    (fun X ↦ (baseChangePointMulEquiv f G X.unop).toCommGrpIso)
    (fun {X Y} k ↦ by
      ext p
      exact (Over.mapPullbackAdj f).homEquiv_naturality_left_symm k.unop p)

variable (U : S.Opens)

private noncomputable def restrictedRepresentedAddPointFppfCommPresheafIso :
    (((Over.map U.ι).op ⋙ G.commPointPresheaf) ⋙
        CommGrpCat.uliftFunctor.{u + 1}) ≅
      addPointFppfCommPresheafOverOpen G U := by
  let e := (Scheme.fppfTopology.overMapPullback
    AddCommGrpCat.{u + 1} U.ι).mapIso (representedAddPointFppfSheafIso G)
  exact Functor.isoWhiskerRight
    ((sheafToPresheaf (Scheme.fppfTopology.over U.toScheme)
      AddCommGrpCat.{u + 1}).mapIso e) AddCommGrpCat.toCommGrp

/-- After universe lifting, the point presheaf of the canonical base change is the actual
restricted represented additive point sheaf used by the supported-cokernel construction. -/
noncomputable def baseChangeAddPointFppfCommPresheafIso :
    CommGroupScheme.commPointPresheaf
        ((Over.pullback U.ι).mapCommGrp.obj G) ⋙
          CommGrpCat.uliftFunctor.{u + 1} ≅
      addPointFppfCommPresheafOverOpen G U :=
  Functor.isoWhiskerRight (baseChangeCommPointPresheafIso U.ι G)
      CommGrpCat.uliftFunctor.{u + 1} ≪≫
    restrictedRepresentedAddPointFppfCommPresheafIso G U

/-- The represented `CommGroupScheme.FppfHOne` of the canonical base change is multiplicatively
equivalent to the universe-lifted additive-sheaf `H¹` used on the open. -/
noncomputable def baseChangeFppfHOneMulEquivAddPointFppfHOneOverOpen :
    CommGroupScheme.FppfHOne.{v} ((Over.pullback U.ι).mapCommGrp.obj G) ≃*
      AddPointFppfHOneOverOpen.{v} G U :=
  (Scheme.FppfHOne.mulEquivUlift
      (CommGroupScheme.commPointPresheaf
        ((Over.pullback U.ι).mapCommGrp.obj G))).trans
    (Scheme.FppfHOne.mulEquivOfIso
      (baseChangeAddPointFppfCommPresheafIso G U))

end AlgebraicGeometry.CommGroupScheme

namespace AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme

universe v u

open CommGroupScheme

section ConstantFlat

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]

/-- On the good open, the represented `H¹` of the canonical base change of the constant-flat
bad-level model agrees with that of the canonical base change of the constant group scheme. -/
noncomputable def constantFlatFppfHOneAwayMulEquiv (level : R) :
    CommGroupScheme.FppfHOne.{v}
        ((Over.pullback (levelOpen level).ι).mapCommGrp.obj
          (constantFlat R G level).obj) ≃*
      CommGroupScheme.FppfHOne.{v}
        ((Over.pullback (levelOpen level).ι).mapCommGrp.obj
          (FiniteFlatCommGroupScheme.constantScheme R G).obj) :=
  (baseChangeFppfHOneMulEquivAddPointFppfHOneOverOpen
      (constantFlat R G level).obj (levelOpen level)).trans
    ((constantFlatAddPointFppfHOneAwayMulEquiv level).trans
      (baseChangeFppfHOneMulEquivAddPointFppfHOneOverOpen
        (FiniteFlatCommGroupScheme.constantScheme R G).obj
        (levelOpen level)).symm)

end ConstantFlat

section MultiplicativeFlat

variable {coeffPrime level : ℕ} [NeZero coeffPrime]

/-- On the good open, the represented `H¹` of the canonical base change of the
multiplicative-flat bad-level model agrees with that of the canonical base change of `μ_p`. -/
noncomputable def muFlatFppfHOneAwayMulEquiv
    (datum : MuFlatDatum coeffPrime level) :
    CommGroupScheme.FppfHOne.{v}
        ((Over.pullback (levelOpen (level : ℤ)).ι).mapCommGrp.obj
          (muFlat coeffPrime level datum).obj) ≃*
      CommGroupScheme.FppfHOne.{v}
        ((Over.pullback (levelOpen (level : ℤ)).ι).mapCommGrp.obj
          (FiniteFlatCommGroupScheme.muScheme ℤ coeffPrime).obj) :=
  (baseChangeFppfHOneMulEquivAddPointFppfHOneOverOpen
      (muFlat coeffPrime level datum).obj
      (levelOpen (level : ℤ))).trans
    ((muFlatAddPointFppfHOneAwayMulEquiv datum).trans
      (baseChangeFppfHOneMulEquivAddPointFppfHOneOverOpen
        (FiniteFlatCommGroupScheme.muScheme ℤ coeffPrime).obj
        (levelOpen (level : ℤ))).symm)

end MultiplicativeFlat

end AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme
