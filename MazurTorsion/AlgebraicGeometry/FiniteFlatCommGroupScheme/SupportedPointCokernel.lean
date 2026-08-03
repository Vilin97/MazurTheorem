/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Whiskering
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.ConstantFlat
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.MultiplicativeFlat

/-!
# Pointwise cokernels and away-from-bad-fibre vanishing

Mazur's two bad-level localization sequences have quotient terms supported on the bad fibre.
Those terms are fppf sheaves, not quasi-finite flat group schemes.  This file constructs the
honest presheaf precursor: the pointwise additive cokernel of an ambient commutative
group-scheme morphism.  Its projection is objectwise surjective and its defining sequence is
categorically exact.

The file makes no sheaf-restriction claim.  It does prove the exact pointwise support input:
an ambient point over a test scheme lying above `D(level)` factors through the checked open
subgroup, so the corresponding point-cokernel object is zero.  The next layer must transport this
objectwise vanishing through site restriction and sheafification.  The constant-flat and
multiplicative-flat inclusions below are the two concrete consumers.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.CommGroupScheme

universe u

variable {S : Scheme.{u}} {G H K : CommGroupScheme S}

/-- The represented point presheaf written additively.  Passing through the standard
commutative-group/additive-commutative-group equivalence lets us form categorical cokernels
without changing any point sets. -/
noncomputable abbrev addPointPresheaf (G : CommGroupScheme S) :
    (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  G.commPointPresheaf ⋙ commGroupAddCommGroupEquivalence.functor

/-- The natural transformation on additive point presheaves induced by a group-scheme map. -/
noncomputable def addPointPresheafMap (f : G ⟶ H) :
    addPointPresheaf G ⟶ addPointPresheaf H :=
  Functor.whiskerRight (commPointPresheafMap f)
    commGroupAddCommGroupEquivalence.functor

@[simp]
theorem addPointPresheafMap_id (G : CommGroupScheme S) :
    addPointPresheafMap (CategoryStruct.id G) = CategoryStruct.id (addPointPresheaf G) := by
  rw [addPointPresheafMap, commPointPresheafMap_id]
  exact Functor.whiskerRight_id' commGroupAddCommGroupEquivalence.functor

theorem addPointPresheafMap_comp (f : G ⟶ H) (g : H ⟶ K) :
    addPointPresheafMap (f ≫ g) = addPointPresheafMap f ≫ addPointPresheafMap g := by
  rw [addPointPresheafMap, commPointPresheafMap_comp]
  exact Functor.whiskerRight_comp _ _ commGroupAddCommGroupEquivalence.functor

/-- The pointwise additive cokernel presheaf of an ambient group-scheme map.  This is the input
to, not a replacement for, the eventual fppf supported-quotient sheaf. -/
noncomputable abbrev pointCokernelPresheaf (f : G ⟶ H) :
    (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  cokernel (addPointPresheafMap f)

/-- The canonical projection to the pointwise cokernel presheaf. -/
noncomputable abbrev pointCokernelProjection (f : G ⟶ H) :
    addPointPresheaf H ⟶ pointCokernelPresheaf f :=
  cokernel.π (addPointPresheafMap f)

/-- Before sheafification, the cokernel projection is already surjective on every test scheme. -/
theorem pointCokernelProjection_app_surjective (f : G ⟶ H) (T : (Over S)ᵒᵖ) :
    Function.Surjective ((pointCokernelProjection f).app T) := by
  rw [← AddCommGrpCat.epi_iff_surjective]
  exact (NatTrans.epi_iff_epi_app (pointCokernelProjection f)).mp (by infer_instance) T

/-- The exact presheaf sequence consisting of the point map and its categorical cokernel. -/
noncomputable def pointCokernelSequence (f : G ⟶ H) :
    ShortComplex ((Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  ShortComplex.mk (addPointPresheafMap f) (pointCokernelProjection f)
    (cokernel.condition _)

/-- The pointwise cokernel sequence is exact by its actual categorical construction. -/
theorem pointCokernelSequence_exact (f : G ⟶ H) :
    (pointCokernelSequence f).Exact :=
  ShortComplex.exact_cokernel _

/-! ### Factorization through an open subgroup -/

/-- Lift an ambient test point through an open subgroup whenever its underlying
scheme map has range in that subgroup. -/
noncomputable def pointLiftThroughOpen
    (f : G ⟶ H)
    [IsOpenImmersion f.hom.hom.hom.left]
    (T : Over S) (x : Point H T)
    (hx : Set.range x.left ⊆ f.hom.hom.hom.left.opensRange) :
    Point G T := by
  let g : T.left ⟶ G.X.left :=
    IsOpenImmersion.lift f.hom.hom.hom.left x.left hx
  have hg : g ≫ f.hom.hom.hom.left = x.left := by
    exact IsOpenImmersion.lift_fac f.hom.hom.hom.left x.left hx
  refine Over.homMk g ?_
  calc
    g ≫ G.X.hom =
        g ≫ (f.hom.hom.hom.left ≫ H.X.hom) :=
      congrArg (fun q ↦ g ≫ q) f.hom.hom.hom.w.symm
    _ = (g ≫ f.hom.hom.hom.left) ≫ H.X.hom :=
      (Category.assoc _ _ _).symm
    _ = x.left ≫ H.X.hom := congrArg (fun q ↦ q ≫ H.X.hom) hg
    _ = T.hom := x.w

/-- Mapping the open-subgroup lift back to the ambient group recovers the
original test point. -/
theorem mapPoint_pointLiftThroughOpen
    (f : G ⟶ H)
    [IsOpenImmersion f.hom.hom.hom.left]
    (T : Over S) (x : Point H T)
    (hx : Set.range x.left ⊆ f.hom.hom.hom.left.opensRange) :
    mapPoint f T (pointLiftThroughOpen f T x hx) = x := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

/-- If every ambient test point lands in an open subgroup, the induced map on
test points is surjective. -/
theorem mapPoint_surjective_of_range
    (f : G ⟶ H)
    [IsOpenImmersion f.hom.hom.hom.left]
    (T : Over S)
    (hT : ∀ x : Point H T,
      Set.range x.left ⊆ f.hom.hom.hom.left.opensRange) :
    Function.Surjective (mapPoint f T) := by
  intro x
  exact ⟨pointLiftThroughOpen f T x (hT x),
    mapPoint_pointLiftThroughOpen f T x (hT x)⟩

/-- A base open contained in the subgroup range contains the range of every
ambient point whose test scheme lies over that base open. -/
theorem point_range_le_of_base_preimage_eq_top
    (f : G ⟶ H)
    [IsOpenImmersion f.hom.hom.hom.left]
    (U : S.Opens)
    (hU : H.X.hom ⁻¹ᵁ U ≤ f.hom.hom.hom.left.opensRange)
    (T : Over S) (hT : T.hom ⁻¹ᵁ U = ⊤)
    (x : Point H T) :
    Set.range x.left ⊆ f.hom.hom.hom.left.opensRange := by
  rintro y ⟨t, rfl⟩
  apply hU
  have ht : t ∈ T.hom ⁻¹ᵁ U := by
    rw [hT]
    trivial
  change H.X.hom (x.left t) ∈ U
  rw [← Scheme.Hom.comp_apply, x.w]
  exact ht

/-- Over a test scheme lying above a base open contained in the subgroup
range, the open-subgroup map is surjective on points. -/
theorem mapPoint_surjective_of_base_preimage_eq_top
    (f : G ⟶ H)
    [IsOpenImmersion f.hom.hom.hom.left]
    (U : S.Opens)
    (hU : H.X.hom ⁻¹ᵁ U ≤ f.hom.hom.hom.left.opensRange)
    (T : Over S) (hT : T.hom ⁻¹ᵁ U = ⊤) :
    Function.Surjective (mapPoint f T) :=
  mapPoint_surjective_of_range f T
    (point_range_le_of_base_preimage_eq_top f U hU T hT)

/-- Surjectivity of the subgroup map on a test object makes its pointwise
cokernel object zero. -/
theorem pointCokernelPresheaf_obj_isZero_of_mapPoint_surjective
    (f : G ⟶ H) (T : (Over S)ᵒᵖ)
    (h : Function.Surjective (mapPoint f T.unop)) :
    IsZero ((pointCokernelPresheaf f).obj T) := by
  haveI : Epi ((addPointPresheafMap f).app T) := by
    rw [AddCommGrpCat.epi_iff_surjective]
    exact h
  haveI : Epi ((pointCokernelProjection f).app T) := by
    rw [AddCommGrpCat.epi_iff_surjective]
    exact pointCokernelProjection_app_surjective f T
  apply IsZero.of_epi_eq_zero ((pointCokernelProjection f).app T)
  apply (cancel_epi ((addPointPresheafMap f).app T)).1
  have hc := congrArg (fun q ↦ q.app T)
    (cokernel.condition (addPointPresheafMap f))
  exact hc

/-- The point-cokernel presheaf is zero on every test object lying over a
base open contained in the subgroup range. -/
theorem pointCokernelPresheaf_obj_isZero_of_base_preimage_eq_top
    (f : G ⟶ H)
    [IsOpenImmersion f.hom.hom.hom.left]
    (U : S.Opens)
    (hU : H.X.hom ⁻¹ᵁ U ≤ f.hom.hom.hom.left.opensRange)
    (T : (Over S)ᵒᵖ) (hT : T.unop.hom ⁻¹ᵁ U = ⊤) :
    IsZero ((pointCokernelPresheaf f).obj T) :=
  pointCokernelPresheaf_obj_isZero_of_mapPoint_surjective f T
    (mapPoint_surjective_of_base_preimage_eq_top f U hU T.unop hT)

end AlgebraicGeometry.CommGroupScheme

namespace AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme

universe u

open CommGroupScheme

section ConstantFlat

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]

/-- The actual point-cokernel presheaf attached to the constant-flat open subgroup. -/
noncomputable abbrev constantFlatPointCokernelPresheaf (level : R) :=
  pointCokernelPresheaf (constantFlatInclusion (G := G) level)

/-- The concrete constant-flat cokernel projection is surjective on every test scheme. -/
theorem constantFlatPointCokernelProjection_app_surjective (level : R)
    (T : (Over (Spec (.of R)))ᵒᵖ) :
    Function.Surjective
      ((pointCokernelProjection (constantFlatInclusion (G := G) level)).app T) :=
  pointCokernelProjection_app_surjective _ _

/-- The constant-flat inclusion supplies a concrete exact point-cokernel sequence. -/
theorem constantFlatPointCokernelSequence_exact (level : R) :
    (pointCokernelSequence (constantFlatInclusion (G := G) level)).Exact :=
  pointCokernelSequence_exact _

/-- The inverse image of `D(level)` in the constant ambient group lies in
the constant-flat open subgroup. -/
theorem constantFlatInclusion_target_preimage_levelOpen_le
    (level : R) :
    (FiniteFlatCommGroupScheme.constantScheme R G).obj.X.hom ⁻¹ᵁ
        PrimeSpectrum.basicOpen level ≤
      ((constantFlatInclusion (G := G) level).hom.hom.hom.left).opensRange := by
  change PrimeSpectrum.basicOpen
      (algebraMap R (FiniteFlatCommGroupScheme.ConstantCoordinates R G) level) ≤ _
  exact constantFlatInclusion_contains_levelOpen (G := G) level

/-- Over a test scheme above `D(level)`, every ambient constant-group point
comes from the constant-flat open subgroup. -/
theorem constantFlat_mapPoint_surjective_away
    (level : R) (T : Over (Spec (.of R)))
    (hT : T.hom ⁻¹ᵁ PrimeSpectrum.basicOpen level = ⊤) :
    Function.Surjective
      (CommGroupScheme.mapPoint (constantFlatInclusion (G := G) level) T) :=
  CommGroupScheme.mapPoint_surjective_of_base_preimage_eq_top
    (constantFlatInclusion (G := G) level)
    (PrimeSpectrum.basicOpen level)
    (constantFlatInclusion_target_preimage_levelOpen_le (G := G) level)
    T hT

/-- The constant-flat point-cokernel presheaf vanishes on every test scheme
lying over `D(level)`. -/
theorem constantFlatPointCokernelPresheaf_obj_isZero_away
    (level : R) (T : (Over (Spec (.of R)))ᵒᵖ)
    (hT : T.unop.hom ⁻¹ᵁ PrimeSpectrum.basicOpen level = ⊤) :
    IsZero ((constantFlatPointCokernelPresheaf (G := G) level).obj T) :=
  CommGroupScheme.pointCokernelPresheaf_obj_isZero_of_base_preimage_eq_top
    (constantFlatInclusion (G := G) level)
    (PrimeSpectrum.basicOpen level)
    (constantFlatInclusion_target_preimage_levelOpen_le (G := G) level)
    T hT

end ConstantFlat

section MultiplicativeFlat

variable {coeffPrime level : ℕ} [NeZero coeffPrime]

/-- The actual point-cokernel presheaf attached to the multiplicative-flat open subgroup. -/
noncomputable abbrev muFlatPointCokernelPresheaf
    (datum : MuFlatDatum coeffPrime level) :=
  pointCokernelPresheaf (muFlatInclusion coeffPrime level datum)

/-- The concrete multiplicative-flat cokernel projection is surjective on every test scheme. -/
theorem muFlatPointCokernelProjection_app_surjective
    (datum : MuFlatDatum coeffPrime level) (T : (Over (Spec (.of ℤ)))ᵒᵖ) :
    Function.Surjective
      ((pointCokernelProjection (muFlatInclusion coeffPrime level datum)).app T) :=
  pointCokernelProjection_app_surjective _ _

/-- The multiplicative-flat inclusion supplies the second concrete exact point-cokernel
sequence required before constructing Mazur's supported quotient sheaf. -/
theorem muFlatPointCokernelSequence_exact (datum : MuFlatDatum coeffPrime level) :
    (pointCokernelSequence (muFlatInclusion coeffPrime level datum)).Exact :=
  pointCokernelSequence_exact _

/-- The inverse image of `D(level)` in `mu_p` lies in the multiplicative-flat
open subgroup. -/
theorem muFlatInclusion_target_preimage_levelOpen_le
    (datum : MuFlatDatum coeffPrime level) :
    (FiniteFlatCommGroupScheme.muScheme ℤ coeffPrime).obj.X.hom ⁻¹ᵁ
        PrimeSpectrum.basicOpen (level : ℤ) ≤
      ((muFlatInclusion coeffPrime level datum).hom.hom.hom.left).opensRange := by
  change PrimeSpectrum.basicOpen
      (algebraMap ℤ (MuCoordinates coeffPrime) (level : ℤ)) ≤ _
  exact muFlatInclusion_contains_levelOpen coeffPrime level datum

/-- Over a test scheme above `D(level)`, every `mu_p` point comes from the
multiplicative-flat open subgroup. -/
theorem muFlat_mapPoint_surjective_away
    (datum : MuFlatDatum coeffPrime level)
    (T : Over (Spec (.of ℤ)))
    (hT : T.hom ⁻¹ᵁ PrimeSpectrum.basicOpen (level : ℤ) = ⊤) :
    Function.Surjective
      (CommGroupScheme.mapPoint (muFlatInclusion coeffPrime level datum) T) :=
  CommGroupScheme.mapPoint_surjective_of_base_preimage_eq_top
    (muFlatInclusion coeffPrime level datum)
    (PrimeSpectrum.basicOpen (level : ℤ))
    (muFlatInclusion_target_preimage_levelOpen_le datum)
    T hT

/-- The multiplicative-flat point-cokernel presheaf vanishes on every test
scheme lying over `D(level)`. -/
theorem muFlatPointCokernelPresheaf_obj_isZero_away
    (datum : MuFlatDatum coeffPrime level)
    (T : (Over (Spec (.of ℤ)))ᵒᵖ)
    (hT : T.unop.hom ⁻¹ᵁ PrimeSpectrum.basicOpen (level : ℤ) = ⊤) :
    IsZero ((muFlatPointCokernelPresheaf datum).obj T) :=
  CommGroupScheme.pointCokernelPresheaf_obj_isZero_of_base_preimage_eq_top
    (muFlatInclusion coeffPrime level datum)
    (PrimeSpectrum.basicOpen (level : ℤ))
    (muFlatInclusion_target_preimage_levelOpen_le datum)
    T hT

end MultiplicativeFlat

end AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme
