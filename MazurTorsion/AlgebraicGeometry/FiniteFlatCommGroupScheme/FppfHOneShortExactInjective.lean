/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfHOneFunctoriality
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.SupportedFppfCokernel

/-!
# Injectivity on fppf H¹ for short exact coefficient sheaves

For an objectwise exact sequence of commutative-group-valued presheaves, a class in the kernel
of the induced map on fppf `H¹` is represented locally by a zero-cochain in the middle term.
Its image in the quotient is compatible on overlaps.  The sheaf condition glues those local
images over the base; surjectivity of the middle-to-quotient map at the base object supplies one
global lift.  Adjusting the zero-cochain by this lift puts it in the first term and proves that
the original class is trivial.

The final theorem applies this argument to an actual short exact sequence of
`AddCommGrpCat`-valued fppf sheaves.  Exactness and injectivity are extracted pointwise from the
categorical short exact sequence.  Only surjectivity of the actual second sheaf map at the base
object remains as a hypothesis; in particular, no objectwise surjectivity premise is imposed.
-/

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open CategoryTheory.PresheafOfCommGroups
open CategoryTheory.PresheafOfGroups

namespace AlgebraicGeometry.Scheme.FppfHOne

universe w v u

/-- The structural map from one member of an fppf cover to the terminal object of the relative
site. -/
private def coverToBase {X : Scheme.{u}}
    (U : Scheme.Cover.{v} Scheme.fppfPrecoverage X) (j : U.I₀) :
    U.overFamily j ⟶ Over.mk (𝟙 X) :=
  (Scheme.Cover.Hom.toOverFamilyRefinement (Scheme.FppfHOne.toIdentityCover U)).map j

/-- An objectwise exact inclusion of coefficient presheaves induces an injection on global
fppf `H¹` when the quotient is a sheaf and every quotient section over the base lifts globally.

The lifting assumption is deliberately only at `Over.mk (𝟙 X)`.  Quotient sections on an
arbitrary cover are first glued by `hQ`, so no objectwise-surjectivity assumption is needed. -/
theorem mapHom_injective_of_objectwise_mulExact_of_base_surjective
    {X : Scheme.{u}}
    {F A Q : Functor (Over X)ᵒᵖ CommGrpCat.{w}}
    (i : F ⟶ A) (q : A ⟶ Q)
    (hinj : ∀ T, Function.Injective (i.app T).hom)
    (hexact : ∀ T, Function.MulExact (i.app T).hom (q.app T).hom)
    (hQ : Presheaf.IsSheaf (Scheme.fppfTopology.over X)
      (toGroups Q ⋙ CategoryTheory.forget GrpCat))
    (hbase : Function.Surjective
      (q.app (Opposite.op (Over.mk (𝟙 X)))).hom) :
    Function.Injective (Scheme.FppfHOne.mapHom.{w, v, u} i) := by
  letI coefficientCommGroupF (T : (Over X)ᵒᵖ) :
      CommGroup ((toGroups F).obj T) := by
    change CommGroup (F.obj T)
    infer_instance
  letI coefficientCommGroupA (T : (Over X)ᵒᵖ) :
      CommGroup ((toGroups A).obj T) := by
    change CommGroup (A.obj T)
    infer_instance
  letI coefficientCommGroupQ (T : (Over X)ᵒᵖ) :
      CommGroup ((toGroups Q).obj T) := by
    change CommGroup (Q.obj T)
    infer_instance
  rw [injective_iff_map_eq_one]
  intro z hz
  induction z using Quot.inductionOn with
  | _ rep =>
      rcases rep with ⟨U, x⟩
      induction x using Quot.inductionOn with
      | _ c =>
          change Scheme.FppfHOne.mk U
              (NatTrans.mapOneCocycle i c).class = 1 at hz
          have hz' : Scheme.FppfHOne.mk U
                (NatTrans.mapOneCocycle i c).class =
              Scheme.FppfHOne.mk (Scheme.FppfHOne.identityCover X) 1 := by
            rw [Scheme.FppfHOne.mk_one]
            exact hz
          obtain ⟨W, r, _s, hrs⟩ :=
            (Scheme.FppfHOne.class_eq_iff U
              (Scheme.FppfHOne.identityCover X)
              (NatTrans.mapOneCocycle i c).class 1).mp hz'
          let rho := Scheme.Cover.Hom.toOverFamilyRefinement r
          let cW := rho.pullbackOneCocycle c
          have hrs' :
              (rho.pullbackOneCocycle (NatTrans.mapOneCocycle i c)).class = 1 := by
            simpa only [Scheme.Cover.Hom.pullbackHOne,
              FamilyRefinement.pullbackHOne_class,
              FamilyRefinement.pullbackHOne_one] using hrs
          have hmapped : (NatTrans.mapOneCocycle i cW).class = 1 := by
            change (NatTrans.mapOneCocycle i
              (rho.pullbackOneCocycle c)).class = 1
            rw [NatTrans.mapOneCocycle_pullback]
            exact hrs'
          obtain ⟨b, hb⟩ :=
            (OneCocycle.class_eq_iff (NatTrans.mapOneCocycle i cW) 1).mp hmapped
          let bA (j : W.I₀) : A.obj (Opposite.op (W.overFamily j)) := b j
          let qLocal (j : W.I₀) : Q.obj (Opposite.op (W.overFamily j)) :=
            (q.app (Opposite.op (W.overFamily j))).hom (bA j)
          have hqLocal {T : Over X} {j k : W.I₀}
              (a : T ⟶ W.overFamily j) (d : T ⟶ W.overFamily k) :
              Q.map a.op (qLocal j) = Q.map d.op (qLocal k) := by
            have hrel := hb j k a d
            change A.map a.op (bA j) *
                (i.app (Opposite.op T)).hom (cW.ev j k a d) =
              1 * A.map d.op (bA k) at hrel
            have hmap : (q.app (Opposite.op T)).hom (A.map a.op (bA j)) *
                  (q.app (Opposite.op T)).hom
                    ((i.app (Opposite.op T)).hom (cW.ev j k a d)) =
                (q.app (Opposite.op T)).hom 1 *
                  (q.app (Opposite.op T)).hom (A.map d.op (bA k)) := by
              simpa only [_root_.map_mul] using
                congrArg (q.app (Opposite.op T)).hom hrel
            have hkill : (q.app (Opposite.op T)).hom
                ((i.app (Opposite.op T)).hom (cW.ev j k a d)) = 1 :=
              (hexact (Opposite.op T)
                ((i.app (Opposite.op T)).hom (cW.ev j k a d))).2
                  ⟨cW.ev j k a d, rfl⟩
            rw [hkill, map_one, mul_one, one_mul] at hmap
            change Q.map a.op
                ((q.app (Opposite.op (W.overFamily j))).hom (bA j)) =
              Q.map d.op
                ((q.app (Opposite.op (W.overFamily k))).hom (bA k))
            rw [← _root_.CategoryTheory.NatTrans.naturality_apply q a.op (bA j),
              ← _root_.CategoryTheory.NatTrans.naturality_apply q d.op (bA k)]
            exact hmap
          have hcover : Sieve.ofArrows W.overFamily (coverToBase W) ∈
              (Scheme.fppfTopology.over X) (Over.mk (𝟙 X)) := by
            rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
            change Sieve.ofArrows W.X W.f ∈ Scheme.fppfTopology X
            exact W.mem_grothendieckTopology
          let xq : ∀ j : W.I₀, PUnit ⟶
              (toGroups Q ⋙ CategoryTheory.forget GrpCat).obj
                (Opposite.op (W.overFamily j)) :=
            fun j => ↾fun _ => qLocal j
          have hxq : ∀ ⦃T : Over X⦄ ⦃j k : W.I₀⦄
              (a : T ⟶ W.overFamily j) (d : T ⟶ W.overFamily k),
              a ≫ coverToBase W j = d ≫ coverToBase W k →
              xq j ≫ (toGroups Q ⋙ CategoryTheory.forget GrpCat).map a.op =
                xq k ≫ (toGroups Q ⋙ CategoryTheory.forget GrpCat).map d.op := by
            intro T j k a d _had
            ext _
            exact hqLocal a d
          let qGlobalMap := hQ.amalgamateOfArrows
            (coverToBase W) hcover xq hxq
          let qGlobal : Q.obj (Opposite.op (Over.mk (𝟙 X))) :=
            qGlobalMap PUnit.unit
          have qGlobal_map (j : W.I₀) :
              Q.map (coverToBase W j).op qGlobal = qLocal j := by
            have h := hQ.amalgamateOfArrows_map
              (coverToBase W) hcover xq hxq j
            exact ConcreteCategory.congr_hom h PUnit.unit
          obtain ⟨a₀, ha₀⟩ := hbase qGlobal
          let aLocal (j : W.I₀) : A.obj (Opposite.op (W.overFamily j)) :=
            A.map (coverToBase W j).op a₀
          let adjusted (j : W.I₀) : A.obj (Opposite.op (W.overFamily j)) :=
            bA j * (aLocal j)⁻¹
          have hadjustedQ (j : W.I₀) :
              (q.app (Opposite.op (W.overFamily j))).hom (adjusted j) = 1 := by
            have haLocal : (q.app (Opposite.op (W.overFamily j))).hom
                (aLocal j) = qLocal j := by
              change (q.app (Opposite.op (W.overFamily j))).hom
                  (A.map (coverToBase W j).op a₀) = qLocal j
              calc
                _ = Q.map (coverToBase W j).op
                    ((q.app (Opposite.op (Over.mk (𝟙 X)))).hom a₀) :=
                  _root_.CategoryTheory.NatTrans.naturality_apply q
                    (coverToBase W j).op a₀
                _ = Q.map (coverToBase W j).op qGlobal := by rw [ha₀]
                _ = qLocal j := qGlobal_map j
            dsimp only [adjusted]
            rw [(q.app (Opposite.op (W.overFamily j))).hom.map_mul,
              (q.app (Opposite.op (W.overFamily j))).hom.map_inv]
            rw [haLocal, mul_inv_cancel]
          let alpha (j : W.I₀) : F.obj (Opposite.op (W.overFamily j)) :=
            Classical.choose ((hexact (Opposite.op (W.overFamily j))
              (adjusted j)).mp (hadjustedQ j))
          have halpha (j : W.I₀) :
              (i.app (Opposite.op (W.overFamily j))).hom (alpha j) =
                adjusted j :=
            Classical.choose_spec ((hexact (Opposite.op (W.overFamily j))
              (adjusted j)).mp (hadjustedQ j))
          have aLocal_pull_eq {T : Over X} {j k : W.I₀}
              (a : T ⟶ W.overFamily j) (d : T ⟶ W.overFamily k) :
              A.map a.op (aLocal j) = A.map d.op (aLocal k) := by
            change A.map a.op (A.map (coverToBase W j).op a₀) =
              A.map d.op (A.map (coverToBase W k).op a₀)
            rw [← A.map_comp_apply, ← A.map_comp_apply]
            exact congrArg (fun g : T ⟶ Over.mk (𝟙 X) => A.map g.op a₀)
              (Over.mkIdTerminal.hom_ext _ _)
          have hadjustedRel (j k : W.I₀) {T : Over X}
              (a : T ⟶ W.overFamily j) (d : T ⟶ W.overFamily k) :
              A.map a.op (adjusted j) *
                  (i.app (Opposite.op T)).hom (cW.ev j k a d) =
                1 * A.map d.op (adjusted k) := by
            have hrel := hb j k a d
            change A.map a.op (bA j) *
                (i.app (Opposite.op T)).hom (cW.ev j k a d) =
              1 * A.map d.op (bA k) at hrel
            dsimp only [adjusted]
            rw [_root_.map_mul, _root_.map_inv,
              _root_.map_mul, _root_.map_inv]
            rw [one_mul] at hrel
            rw [aLocal_pull_eq a d, one_mul]
            rw [← hrel]
            ac_rfl
          have hcoh : cW.IsCohomologous
              (1 : OneCocycle (toGroups F) W.overFamily) := by
            refine ⟨alpha, ?_⟩
            intro j k T a d
            apply hinj (Opposite.op T)
            rw [(i.app (Opposite.op T)).hom.map_mul,
              (i.app (Opposite.op T)).hom.map_mul,
              OneCocycle.one_toOneCochain, OneCochain.one_ev,
              (i.app (Opposite.op T)).hom.map_one,
              ← PresheafOfCommGroups.NatTrans.naturality_apply
                i a.op (alpha j),
              ← PresheafOfCommGroups.NatTrans.naturality_apply
                i d.op (alpha k), halpha, halpha]
            exact hadjustedRel j k a d
          have hcW : cW.class = 1 := hcoh.class_eq
          change Scheme.FppfHOne.mk U c.class = 1
          calc
            Scheme.FppfHOne.mk U c.class =
                Scheme.FppfHOne.mk W cW.class := by
              symm
              simpa only [cW, rho, Scheme.Cover.Hom.pullbackHOne,
                FamilyRefinement.pullbackHOne_class] using
                  Scheme.FppfHOne.class_pullback U W r c.class
            _ = Scheme.FppfHOne.mk W 1 :=
              congrArg (Scheme.FppfHOne.mk W) hcW
            _ = 1 := Scheme.FppfHOne.mk_one W

/-- The multiplicative commutative-group presheaf underlying an additive commutative-group
sheaf.  The conversion is objectwise `Multiplicative`, with no change to the underlying data. -/
noncomputable abbrev addCommSheafCommPresheaf
    {X : Scheme.{u}}
    (F : Sheaf (Scheme.fppfTopology.over X) AddCommGrpCat.{u + 1}) :
    Functor (Over X)ᵒᵖ CommGrpCat.{u + 1} :=
  F.obj ⋙ AddCommGrpCat.toCommGrp

/-- A map of additive commutative-group sheaves, converted objectwise to a map of
multiplicative commutative-group presheaves. -/
noncomputable def addCommSheafCommPresheafMap
    {X : Scheme.{u}}
    {F A : Sheaf (Scheme.fppfTopology.over X) AddCommGrpCat.{u + 1}}
    (f : F ⟶ A) :
    addCommSheafCommPresheaf F ⟶ addCommSheafCommPresheaf A :=
  Functor.whiskerRight
    ((sheafToPresheaf
      (Scheme.fppfTopology.over X) AddCommGrpCat.{u + 1}).map f)
    AddCommGrpCat.toCommGrp

/-- Forgetting the multiplicative wrapper on an additive sheaf gives its original underlying
type-valued presheaf. -/
private noncomputable def addCommSheafUnderlyingTypeIso
    {X : Scheme.{u}}
    (F : Sheaf (Scheme.fppfTopology.over X) AddCommGrpCat.{u + 1}) :
    (toGroups (addCommSheafCommPresheaf F) ⋙
      CategoryTheory.forget GrpCat) ≅
      (F.obj ⋙ CategoryTheory.forget AddCommGrpCat) where
  hom :=
    { app := fun _ => ↾fun x => Multiplicative.toAdd x
      naturality := by
        intro _ _ _
        rfl }
  inv :=
    { app := fun _ => ↾fun x => Multiplicative.ofAdd x
      naturality := by
        intro _ _ _
        rfl }
  hom_inv_id := by
    ext T x
    rfl
  inv_hom_id := by
    ext T x
    rfl

/-- The first map in an actual short exact sequence of additive fppf sheaves induces an
injection on global fppf `H¹` as soon as the actual second map is surjective at the base object.

All other inputs are consequences of `hS`: the first map is objectwise injective, the sequence
is objectwise exact, and the third term satisfies the fppf sheaf condition. -/
theorem mapHom_injective_of_shortExact_of_base_surjective
    {X : Scheme.{u}}
    (S : ShortComplex
      (Sheaf (Scheme.fppfTopology.over X) AddCommGrpCat.{u + 1}))
    (hS : S.ShortExact)
    (hbase : Function.Surjective
      (S.g.hom.app (Opposite.op (Over.mk (𝟙 X)))).hom) :
    Function.Injective
      (Scheme.FppfHOne.mapHom.{u + 1, v, u}
        (addCommSheafCommPresheafMap S.f)) := by
  let i := addCommSheafCommPresheafMap S.f
  let q := addCommSheafCommPresheafMap S.g
  apply mapHom_injective_of_objectwise_mulExact_of_base_surjective
    i q
  · intro T
    let L := sheafToPresheaf (Scheme.fppfTopology.over X)
        AddCommGrpCat.{u + 1} ⋙
      (_root_.CategoryTheory.evaluation
        (Over X)ᵒᵖ AddCommGrpCat.{u + 1}).obj T
    haveI : Mono S.f := hS.mono_f
    haveI : Mono (L.map S.f) := by infer_instance
    change Function.Injective (L.map S.f)
    exact (AddCommGrpCat.mono_iff_injective (L.map S.f)).mp
      (inferInstance : Mono (L.map S.f))
  · intro T
    let L := sheafToPresheaf (Scheme.fppfTopology.over X)
        AddCommGrpCat.{u + 1} ⋙
      (_root_.CategoryTheory.evaluation
        (Over X)ᵒᵖ AddCommGrpCat.{u + 1}).obj T
    haveI : Mono S.f := hS.mono_f
    have hExact : (S.map L).Exact :=
      hS.exact.map_of_mono_of_preservesKernel L
        (by infer_instance) (by infer_instance)
    have hfun : Function.Exact (S.map L).f (S.map L).g :=
      (ShortComplex.ab_exact_iff_function_exact (S.map L)).mp hExact
    intro y
    change (S.map L).g y = 0 ↔ y ∈ Set.range (S.map L).f
    exact hfun y
  · rw [Presheaf.isSheaf_of_iso_iff (addCommSheafUnderlyingTypeIso S.X₃)]
    exact (Presheaf.isSheaf_iff_isSheaf_forget
      (Scheme.fppfTopology.over X) S.X₃.obj
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).mp S.X₃.property
  · dsimp [q, addCommSheafCommPresheafMap]
    intro y
    obtain ⟨x, hx⟩ := hbase y.toAdd
    exact ⟨Multiplicative.ofAdd x, by
      change Multiplicative.ofAdd
        (S.g.hom.app (Opposite.op (Over.mk (𝟙 X))) x) = y
      rw [hx]
      rfl⟩

end AlgebraicGeometry.Scheme.FppfHOne
