/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.GroupTheory.QuotientGroup.Defs
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.CommGroupSchemeFppfConnecting

/-!
# Fppf quotient presentations for ambient commutative group schemes

An elliptic curve quotient by a finite subgroup is not a finite group scheme, so the existing
finite-flat and quasi-finite quotient records cannot express it.  This file gives the ambient
version.  A `FppfQuotientPresentation i` consists of an actual commutative group scheme, an
fppf-surjective homomorphism to it, and an isomorphism identifying the supplied inclusion `i`
with the scheme-theoretic kernel.

This is a certificate for a quotient that has already been constructed.  It is not a theorem
constructing `G/K`, and it does not separately assert a categorical coequalizer.  An fppf cover
with the displayed geometric kernel presents the corresponding quotient of fppf sheaves.

The point API deliberately keeps the arithmetic obstruction visible.  On every test scheme `X`
there is an injection

`G(X) / K(X) ⟶ Q(X)`.

No surjectivity is asserted.  Over the base, the image is exactly the zero fibre of the genuine
connecting homomorphism `Q(S) ⟶ H¹_fppf(S, K)`.  Thus this file cannot be used to identify
`Q(S)` with `G(S) / K(S)` while a nontrivial `H¹` obstruction remains.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.CommGroupScheme

universe u v

variable {S T : Scheme.{u}}

/-- An actual ambient fppf quotient projection with a specified geometric kernel.

The parameter `i : K ⟶ G` is retained in the type so the kernel identification is with the
caller's chosen subgroup scheme and inclusion, not merely with an unnamed isomorphic object. -/
structure FppfQuotientPresentation {K G : CommGroupScheme S} (i : K ⟶ G) where
  /-- The supplied quotient group scheme. -/
  quotient : CommGroupScheme S
  /-- The supplied quotient homomorphism. -/
  project : G ⟶ quotient
  /-- Flatness of the quotient projection. -/
  project_flat : Flat (underlyingHom project)
  /-- Surjectivity of the quotient projection on underlying topological spaces. -/
  project_surjective : Surjective (underlyingHom project)
  /-- Local finite presentation of the quotient projection. -/
  project_lfp : LocallyOfFinitePresentation (underlyingHom project)
  /-- Identification of the supplied subgroup with the geometric kernel. -/
  kernelIso : K ≅ kernel project
  /-- The kernel identification carries the canonical inclusion to the supplied inclusion. -/
  kernelIso_hom_kernelInclusion :
    kernelIso.hom ≫ kernelInclusion project = i

namespace FppfQuotientPresentation

variable {K G : CommGroupScheme S} {i : K ⟶ G}

/-- The quotient presentation as the ambient geometric-kernel record used by the existing fppf
connecting construction. -/
abbrev kernelPresentation (D : FppfQuotientPresentation i) :
    KernelPresentation D.project where
  kernel := K
  inclusion := i
  kernelIso := D.kernelIso
  kernelIso_hom_kernelInclusion := D.kernelIso_hom_kernelInclusion

/-- The three geometric properties making the supplied projection an fppf cover. -/
theorem project_is_fppf (D : FppfQuotientPresentation i) :
    Flat (underlyingHom D.project) ∧
      Surjective (underlyingHom D.project) ∧
        LocallyOfFinitePresentation (underlyingHom D.project) :=
  ⟨D.project_flat, D.project_surjective, D.project_lfp⟩

/-- The chosen subgroup is exactly the pointwise kernel on every test scheme. -/
theorem project_point_eq_one_iff (D : FppfQuotientPresentation i)
    (X : Over S) (x : G.Point X) :
    mapPoint D.project X x = 1 ↔
      x ∈ Set.range (mapPoint i X) := by
  simpa only [Set.mem_range] using
    D.kernelPresentation.mapPoint_eq_one_iff_exists_kernelPoint X x

/-- Pull an ambient fppf quotient presentation back along an arbitrary base morphism.  Both the
specified kernel object and its inclusion are the literal pullbacks of the original data. -/
noncomputable def baseChange (D : FppfQuotientPresentation i) (t : T ⟶ S) :
    FppfQuotientPresentation ((Over.pullback t).mapCommGrp.map i) := by
  let P := D.kernelPresentation.baseChange t
  exact
    { quotient := (Over.pullback t).mapCommGrp.obj D.quotient
      project := (Over.pullback t).mapCommGrp.map D.project
      project_flat := by
        exact MorphismProperty.overPullbackMap t D.project.hom.hom.hom
          D.project_flat
      project_surjective := by
        exact MorphismProperty.overPullbackMap t D.project.hom.hom.hom
          D.project_surjective
      project_lfp := by
        exact MorphismProperty.overPullbackMap t D.project.hom.hom.hom
          D.project_lfp
      kernelIso := P.kernelIso
      kernelIso_hom_kernelInclusion := P.kernelIso_hom_kernelInclusion }

@[simp]
theorem baseChange_quotient (D : FppfQuotientPresentation i) (t : T ⟶ S) :
    (D.baseChange t).quotient = (Over.pullback t).mapCommGrp.obj D.quotient :=
  rfl

@[simp]
theorem baseChange_project (D : FppfQuotientPresentation i) (t : T ⟶ S) :
    (D.baseChange t).project = (Over.pullback t).mapCommGrp.map D.project :=
  rfl

@[simp]
theorem baseChange_kernelPresentation_kernel
    (D : FppfQuotientPresentation i) (t : T ⟶ S) :
    (D.baseChange t).kernelPresentation.kernel =
      (Over.pullback t).mapCommGrp.obj K :=
  rfl

@[simp]
theorem baseChange_kernelPresentation_inclusion
    (D : FppfQuotientPresentation i) (t : T ⟶ S) :
    (D.baseChange t).kernelPresentation.inclusion =
      (Over.pullback t).mapCommGrp.map i :=
  rfl

/-- The image of the specified kernel on `X`-valued points. -/
def pointKernelRange (_D : FppfQuotientPresentation i) (X : Over S) :
    Subgroup (G.Point X) :=
  (mapPoint i X).range

/-- The quotient of source points by points coming from the specified geometric kernel. -/
abbrev PointQuotient (D : FppfQuotientPresentation i) (X : Over S) :=
  G.Point X ⧸ D.pointKernelRange X

private theorem pointKernelRange_le_project_ker
    (D : FppfQuotientPresentation i) (X : Over S) :
    D.pointKernelRange X ≤ (mapPoint D.project X).ker := by
  rintro _ ⟨y, rfl⟩
  exact D.kernelPresentation.mapPoint_inclusion_eq_one X y

/-- The quotient projection on represented points, induced by the actual group-scheme
projection. -/
def pointQuotientMap (D : FppfQuotientPresentation i) (X : Over S) :
    D.PointQuotient X →* D.quotient.Point X :=
  QuotientGroup.lift (D.pointKernelRange X) (mapPoint D.project X)
    (D.pointKernelRange_le_project_ker X)

@[simp]
theorem pointQuotientMap_mk (D : FppfQuotientPresentation i)
    (X : Over S) (x : G.Point X) :
    D.pointQuotientMap X (QuotientGroup.mk' (D.pointKernelRange X) x) =
      mapPoint D.project X x :=
  QuotientGroup.lift_mk' _ _ _

/-- Scheme-theoretic kernel exactness says that the specified point image is precisely the
kernel of the quotient projection on every test scheme. -/
theorem pointKernelRange_eq_project_ker
    (D : FppfQuotientPresentation i) (X : Over S) :
    D.pointKernelRange X = (mapPoint D.project X).ker := by
  apply le_antisymm
  · exact D.pointKernelRange_le_project_ker X
  · intro x hx
    exact (D.project_point_eq_one_iff X x).mp (MonoidHom.mem_ker.mp hx)

/-- The point quotient maps injectively into the points of the quotient scheme on every test
scheme.  Surjectivity is deliberately absent. -/
theorem pointQuotientMap_injective
    (D : FppfQuotientPresentation i) (X : Over S) :
    Function.Injective (D.pointQuotientMap X) := by
  change Function.Injective
    (QuotientGroup.lift (D.pointKernelRange X) (mapPoint D.project X)
      (D.pointKernelRange_le_project_ker X))
  exact (QuotientGroup.injective_lift_iff
    (N := D.pointKernelRange X) (mapPoint D.project X)
      (D.pointKernelRange_le_project_ker X)).2
        (D.pointKernelRange_eq_project_ker X)

private theorem pointMulEquivOfOverIso_mapPoint
    {A B : CommGroupScheme S} (g : A ⟶ B)
    {X Y : Over S} (e : X ≅ Y) (x : A.Point X) :
    pointMulEquivOfOverIso B e (mapPoint g X x) =
      mapPoint g Y (pointMulEquivOfOverIso A e x) :=
  (mapPoint_pullPoint g e.inv x).symm

/-- Changing the test scheme by an isomorphism carries the specified point-kernel image to the
specified point-kernel image. -/
theorem pointKernelRange_map_pointMulEquivOfOverIso
    (D : FppfQuotientPresentation i) {X Y : Over S} (e : X ≅ Y) :
    (D.pointKernelRange X).map
        (pointMulEquivOfOverIso G e).toMonoidHom =
      D.pointKernelRange Y := by
  ext y
  constructor
  · rintro ⟨x, ⟨k, rfl⟩, rfl⟩
    exact ⟨pointMulEquivOfOverIso K e k,
      (pointMulEquivOfOverIso_mapPoint i e k).symm⟩
  · rintro ⟨k, rfl⟩
    obtain ⟨k', rfl⟩ := (pointMulEquivOfOverIso K e).surjective k
    exact ⟨mapPoint i X k', ⟨k', rfl⟩,
      pointMulEquivOfOverIso_mapPoint i e k'⟩

/-- Point quotients are invariant under an isomorphism of test schemes. -/
def pointQuotientMulEquivOfOverIso
    (D : FppfQuotientPresentation i) {X Y : Over S} (e : X ≅ Y) :
    D.PointQuotient X ≃* D.PointQuotient Y :=
  QuotientGroup.congr (D.pointKernelRange X) (D.pointKernelRange Y)
    (pointMulEquivOfOverIso G e)
    (D.pointKernelRange_map_pointMulEquivOfOverIso e)

/-- The point-quotient injection commutes with changing the test scheme by an isomorphism. -/
theorem pointQuotientMap_pointQuotientMulEquivOfOverIso
    (D : FppfQuotientPresentation i) {X Y : Over S} (e : X ≅ Y)
    (x : D.PointQuotient X) :
    D.pointQuotientMap Y (D.pointQuotientMulEquivOfOverIso e x) =
      pointMulEquivOfOverIso D.quotient e (D.pointQuotientMap X x) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (D.pointKernelRange X) x
  rw [D.pointQuotientMap_mk]
  change D.pointQuotientMap Y
      (QuotientGroup.mk' (D.pointKernelRange Y)
        (pointMulEquivOfOverIso G e x)) = _
  rw [D.pointQuotientMap_mk]
  exact (pointMulEquivOfOverIso_mapPoint D.project e x).symm

/-- The quotient projection itself, regarded as a singleton fppf cover of its target. -/
abbrev projectCover (D : FppfQuotientPresentation i) :
    Scheme.Cover.{u} Scheme.fppfPrecoverage D.quotient.X.left := by
  letI : Flat (underlyingHom D.project) := D.project_flat
  letI : Surjective (underlyingHom D.project) := D.project_surjective
  letI : LocallyOfFinitePresentation (underlyingHom D.project) := D.project_lfp
  exact (underlyingHom D.project).cover ⟨D.project_flat, D.project_lfp⟩

/-- Pulling the actual quotient cover back along a target section gives local source lifts. -/
def locallyLiftable (D : FppfQuotientPresentation i) :
    D.kernelPresentation.LocallyLiftable.{u} where
  localLift q := by
    letI : Precoverage.IsStableUnderBaseChange Scheme.fppfPrecoverage :=
      Scheme.instIsStableUnderBaseChangeFppfPrecoverage
    let 𝒱 := D.projectCover
    let 𝒬 := 𝒱.pullback₁ q.left
    have hq : q.left ≫ D.quotient.X.hom = (baseObject S).hom := Over.w q
    exact
      { cover := 𝒬
        lift := fun _ ↦
          Over.homMk (pullback.snd q.left (underlyingHom D.project)) (by
            change pullback.snd q.left (underlyingHom D.project) ≫ G.X.hom =
              pullback.fst q.left (underlyingHom D.project)
            rw [← D.project.hom.hom.hom.w, ← Category.assoc,
              ← pullback.condition, Category.assoc, hq]
            change pullback.fst q.left (underlyingHom D.project) ≫ 𝟙 S =
              pullback.fst q.left (underlyingHom D.project)
            exact Category.comp_id _)
        maps_to := fun j ↦ by
          ext
          change pullback.snd q.left (underlyingHom D.project) ≫
              underlyingHom D.project =
            (coverToBase 𝒬 j).left ≫ q.left
          exact (pullback.condition :
            pullback.fst q.left (underlyingHom D.project) ≫ q.left =
              pullback.snd q.left (underlyingHom D.project) ≫
                underlyingHom D.project).symm }

/-- The genuine fppf connecting homomorphism attached to the supplied quotient projection. -/
def boundaryHom (D : FppfQuotientPresentation i) :
    BasePoint D.quotient →* K.FppfHOne.{u} :=
  D.locallyLiftable.boundaryHom

@[simp]
theorem boundaryHom_project (D : FppfQuotientPresentation i)
    (x : BasePoint G) :
    D.boundaryHom (mapPoint D.project (baseObject S) x) = 1 :=
  D.locallyLiftable.boundaryHom_mapPoint x

/-- A quotient-scheme base point has zero connecting class exactly when it is represented by a
class in the point quotient.  This is the explicit `H¹` obstruction to surjectivity. -/
theorem boundaryHom_eq_one_iff_exists_pointQuotient
    (D : FppfQuotientPresentation i) (q : BasePoint D.quotient) :
    D.boundaryHom q = 1 ↔
      ∃ x : D.PointQuotient (baseObject S),
        D.pointQuotientMap (baseObject S) x = q := by
  constructor
  · intro hq
    obtain ⟨x, hx⟩ := D.locallyLiftable.exists_source_of_boundaryHom_eq_one q hq
    exact ⟨QuotientGroup.mk' (D.pointKernelRange (baseObject S)) x, by
      rw [D.pointQuotientMap_mk]
      exact hx⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨y, hy⟩ :=
      QuotientGroup.mk'_surjective (D.pointKernelRange (baseObject S)) x
    rw [← hy, D.pointQuotientMap_mk, D.boundaryHom_project]

/-- The point quotient embeds as exactly the zero-boundary fibre in the low-degree fppf
cohomology sequence. -/
theorem exact_pointQuotientMap_boundaryHom
    (D : FppfQuotientPresentation i) :
    Function.MulExact
      (D.pointQuotientMap (baseObject S)) D.boundaryHom :=
  fun q ↦ D.boundaryHom_eq_one_iff_exists_pointQuotient q

/-- Transport the fppf boundary homomorphism from base sections to points on an isomorphic test
scheme.  This changes only the presentation of the represented points; it does not assert point
surjectivity. -/
def boundaryHomOfOverIso (D : FppfQuotientPresentation i)
    {X : Over S} (e : baseObject S ≅ X) :
    D.quotient.Point X →* K.FppfHOne.{u} :=
  D.boundaryHom.comp
    (pointMulEquivOfOverIso D.quotient e).symm.toMonoidHom

/-- After transport along an isomorphism of test schemes, the same point quotient embeds as
exactly the zero-boundary fibre. -/
theorem exact_pointQuotientMap_boundaryHomOfOverIso
    (D : FppfQuotientPresentation i) {X : Over S}
    (e : baseObject S ≅ X) :
    Function.MulExact (D.pointQuotientMap X) (D.boundaryHomOfOverIso e) := by
  refine Function.MulExact.of_ladder_mulEquiv_of_mulExact
    (D.pointQuotientMulEquivOfOverIso e)
    (pointMulEquivOfOverIso D.quotient e) (MulEquiv.refl _)
    ?_ ?_ D.exact_pointQuotientMap_boundaryHom
  · apply MonoidHom.ext
    intro x
    exact D.pointQuotientMap_pointQuotientMulEquivOfOverIso e x
  · apply MonoidHom.ext
    intro q
    change D.boundaryHom
        ((pointMulEquivOfOverIso D.quotient e).symm
          (pointMulEquivOfOverIso D.quotient e q)) = D.boundaryHom q
    rw [(pointMulEquivOfOverIso D.quotient e).symm_apply_apply]

end FppfQuotientPresentation

end AlgebraicGeometry.CommGroupScheme
