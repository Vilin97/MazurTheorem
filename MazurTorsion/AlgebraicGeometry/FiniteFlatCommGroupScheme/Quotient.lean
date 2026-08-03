/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.GroupTheory.Coset.Card
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.Constant

/-!
# Fppf quotient presentations and constant finite-flat quotients

The rank-zero argument does not need a constructor for the fppf-sheaf quotient by every
finite-flat closed subgroup.  Its actual input is narrower: a supplied finite-flat quotient
object and projection, the fppf properties of that projection, and a certified presentation of
its scheme-theoretic kernel.  `FppfQuotientPresentation` packages exactly this data.  Its base
change API consumes the checked theorem that certified scheme-theoretic kernels commute with
arbitrary base change.

For a finite commutative group `G` and a subgroup `N`, the quotient `G/N` is again finite
commutative.  Applying the explicit function-Hopf-algebra construction gives a genuine
finite-flat quotient group scheme.  The quotient morphism and its factorization property are
constructed from `QuotientGroup.mk'` and `QuotientGroup.lift`; faithfulness of function-ring
pullback over a nonzero base proves uniqueness among morphisms induced from group homomorphisms.

This concrete construction is intentionally separate from the still-larger theorem that an
arbitrary finite-flat closed subgroup quotient is representable as an fppf sheaf quotient.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry
namespace FiniteFlatCommGroupScheme

universe u

variable {S T : Scheme.{u}}

/-- The exact quotient data consumed by an admissible finite-flat filtration.

This structure does not assert a new general representability theorem.  It records a quotient
object already constructed in `FiniteFlatCommGroupScheme`, an fppf projection to it, and the
certified scheme-theoretic kernel of that projection.  For a faithfully flat homomorphism of
group schemes this is the concrete exact-sequence interface used by descent. -/
structure FppfQuotientPresentation (G : FiniteFlatCommGroupScheme S) where
  /-- The supplied finite-flat quotient object. -/
  quotient : FiniteFlatCommGroupScheme S
  /-- Projection from the middle group scheme to the quotient. -/
  project : G ⟶ quotient
  /-- Flatness of the quotient projection. -/
  project_flat : Flat (hom project)
  /-- Surjectivity of the quotient projection on underlying topological spaces. -/
  project_surjective : Surjective (hom project)
  /-- Local finite presentation of the quotient projection. -/
  project_lfp : LocallyOfFinitePresentation (hom project)
  /-- The certified scheme-theoretic kernel of the projection. -/
  kernelPresentation : KernelPresentation project

namespace FppfQuotientPresentation

variable {G : FiniteFlatCommGroupScheme S}

/-- A quotient projection between finite schemes over the same base is finite. -/
theorem project_isFinite (D : FppfQuotientPresentation G) :
    IsFinite (hom D.project) := by
  haveI : IsFinite (hom D.project ≫ D.quotient.structureMap) := by
    rw [hom_comp_structureMap]
    infer_instance
  exact IsFinite.of_comp (hom D.project) D.quotient.structureMap

/-- The three concrete properties making the supplied projection an fppf cover. -/
theorem project_is_fppf (D : FppfQuotientPresentation G) :
    Flat (hom D.project) ∧ Surjective (hom D.project) ∧
      LocallyOfFinitePresentation (hom D.project) :=
  ⟨D.project_flat, D.project_surjective, D.project_lfp⟩

/-- Exactness at the middle group scheme on points of every test scheme.  Raw surjectivity of
the quotient map on `X`-points is neither asserted nor needed. -/
theorem project_point_eq_one_iff (D : FppfQuotientPresentation G)
    (X : Over S) (x : G.Point X) :
    mapPoint D.project X x = 1 ↔
      x ∈ Set.range (mapPoint D.kernelPresentation.inclusion X) := by
  constructor
  · intro hx
    obtain ⟨y, hy, -⟩ := D.kernelPresentation.existsUnique_point_lift X x hx
    exact ⟨y, hy⟩
  · rintro ⟨y, rfl⟩
    exact D.kernelPresentation.mapPoint_inclusion_eq_one X y

/-- A point killed by the pulled-back quotient projection lifts through the pulled-back
original kernel inclusion. -/
theorem exists_baseChangedKernel_lift
    (D : FppfQuotientPresentation G) (f : T ⟶ S) (X : Over T)
    (x : ((baseChange f).obj G).Point X)
    (hx : mapPoint ((baseChange f).map D.project) X x = 1) :
    ∃ y : ((baseChange f).obj D.kernelPresentation.kernel).Point X,
      mapPoint ((baseChange f).map D.kernelPresentation.inclusion) X y = x := by
  obtain ⟨y, hy, -⟩ := (D.kernelPresentation.baseChange f).existsUnique_point_lift X x hx
  exact ⟨y, hy⟩

/-- Pull an fppf exact quotient presentation back along an arbitrary base morphism. -/
def baseChangePresentation
    (D : FppfQuotientPresentation G) (f : T ⟶ S) :
    FppfQuotientPresentation ((baseChange f).obj G) where
  quotient := (baseChange f).obj D.quotient
  project := (baseChange f).map D.project
  project_flat := by
    exact MorphismProperty.overPullbackMap f D.project.hom.hom.hom.hom D.project_flat
  project_surjective := by
    exact MorphismProperty.overPullbackMap f D.project.hom.hom.hom.hom D.project_surjective
  project_lfp := by
    exact MorphismProperty.overPullbackMap f D.project.hom.hom.hom.hom D.project_lfp
  kernelPresentation := D.kernelPresentation.baseChange f

end FppfQuotientPresentation

noncomputable local instance quotientFintype
    {G : Type u} [Group G] [Finite G] (N : Subgroup G) : Fintype (G ⧸ N) :=
  Fintype.ofFinite (G ⧸ N)

/-- The finite-free affine quotient of a constant group by a subgroup. -/
abbrev constantQuotientAffine (R : Type u) [CommRing R]
    {G : Type u} [CommGroup G] [Fintype G] (N : Subgroup G) :
    AffineFiniteFreeCommGroupScheme R :=
  (constant R (G ⧸ N))

/-- The geometric constant finite-flat quotient `G/N`. -/
abbrev constantQuotient (R : Type u) [CommRing R]
    {G : Type u} [CommGroup G] [Fintype G] (N : Subgroup G) :
    FiniteFlatCommGroupScheme (Spec (.of R)) :=
  constantScheme R (G ⧸ N)

/-- The affine quotient morphism induced by `G → G/N`. -/
def constantQuotientMapAffine (R : Type u) [CommRing R]
    {G : Type u} [CommGroup G] [Fintype G] (N : Subgroup G) :
    (constant R G) ⟶ constantQuotientAffine R N :=
  constantMapAffine R (QuotientGroup.mk' N)

/-- The geometric quotient morphism induced by `G → G/N`. -/
def constantQuotientMap (R : Type u) [CommRing R]
    {G : Type u} [CommGroup G] [Fintype G] (N : Subgroup G) :
    constantScheme R G ⟶ constantQuotient R N :=
  constantMap R (QuotientGroup.mk' N)

/-- A homomorphism killing `N` descends to a morphism out of the constant quotient. -/
def constantQuotientLiftAffine (R : Type u) [CommRing R]
    {G K : Type u} [CommGroup G] [Fintype G] [CommGroup K] [Fintype K]
    (N : Subgroup G) (f : G →* K) (hf : N ≤ f.ker) :
    constantQuotientAffine R N ⟶ constant R K :=
  constantMapAffine R (QuotientGroup.lift N f hf)

/-- The descended affine morphism factors the original constant-group morphism. -/
theorem constantQuotientMapAffine_comp_lift (R : Type u) [CommRing R]
    {G K : Type u} [CommGroup G] [Fintype G] [CommGroup K] [Fintype K]
    (N : Subgroup G) (f : G →* K) (hf : N ≤ f.ker) :
    constantQuotientMapAffine R N ≫ constantQuotientLiftAffine R N f hf =
      constantMapAffine R f := by
  change constantMapAffine R (QuotientGroup.mk' N) ≫
      constantMapAffine R (QuotientGroup.lift N f hf) = constantMapAffine R f
  rw [← constantMapAffine_comp]
  rw [QuotientGroup.lift_comp_mk']

/-- Universal factorization and uniqueness for constant quotient morphisms.  The maps quantified
here are the actual scheme morphisms induced by the displayed group homomorphisms. -/
theorem existsUnique_constantQuotientLiftAffine
    (R : Type u) [CommRing R] [Nontrivial R]
    {G K : Type u} [CommGroup G] [Fintype G] [CommGroup K] [Fintype K]
    (N : Subgroup G) (f : G →* K) (hf : N ≤ f.ker) :
    ∃! q : G ⧸ N →* K,
      constantQuotientMapAffine R N ≫ constantMapAffine R q = constantMapAffine R f := by
  refine ⟨QuotientGroup.lift N f hf, constantQuotientMapAffine_comp_lift R N f hf, ?_⟩
  intro q hq
  apply QuotientGroup.monoidHom_ext
  have hcomp : q.comp (QuotientGroup.mk' N) = f := by
    apply constantMapAffine_injective R
    rw [constantMapAffine_comp]
    exact hq
  rw [hcomp, QuotientGroup.lift_comp_mk']

/-- The quotient morphism sends the distinguished point `g` to its coset. -/
@[simp]
theorem mapPoint_constantQuotientMap (R : Type u) [CommRing R]
    {G : Type u} [CommGroup G] [Fintype G] (N : Subgroup G) (g : G) :
    mapPoint (constantQuotientMap R N) (AffineCommGroupScheme.testObject (R := R) R)
        (constantGeometricPoint R G g) =
      constantGeometricPoint R (G ⧸ N) (QuotientGroup.mk' N g) :=
  mapPoint_constantMap_constantPoint R (QuotientGroup.mk' N) g

/-- The quotient has the expected finite-free order. -/
@[simp]
theorem constantQuotient_order (R : Type u) [CommRing R] [Nontrivial R]
    {G : Type u} [CommGroup G] [Fintype G] (N : Subgroup G) :
    (constantQuotientAffine R N).order = Fintype.card (G ⧸ N) :=
  constant_order R (G ⧸ N)

/-- Geometric base change of a constant quotient agrees with scalar extension of its explicit
function Hopf algebra. -/
noncomputable def constantQuotientRealizeBaseChangeIso
    {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    {G : Type u} [CommGroup G] [Fintype G] (N : Subgroup G) :
    (baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj
        (constantQuotient R N) ≅
      ((constantQuotientAffine R N).baseChange (K := K)).realize :=
  constantRealizeBaseChangeIso (R := R) (K := K) (G ⧸ N)

/-- Geometric base change of a constant quotient is canonically the named constant quotient
over the new base.  This is the concrete constant-family statement and does not assert
representability of quotients by arbitrary finite-flat closed subgroups. -/
noncomputable def constantQuotientBaseChangeIso
    {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    {G : Type u} [CommGroup G] [Fintype G] (N : Subgroup G) :
    (baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj
        (constantQuotient R N) ≅ constantQuotient K N :=
  constantBaseChangeIso (R := R) (K := K) (G ⧸ N)

/-- The constant quotient projection commutes with scalar extension.  This is the
morphism-level base-change square needed when the projection is used as a graded step in an
admissible finite-flat filtration. -/
theorem constantQuotientMap_baseChange_naturality
    {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    {G : Type u} [CommGroup G] [Fintype G] (N : Subgroup G) :
    (baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map
          (constantQuotientMap R N) ≫
        (constantQuotientBaseChangeIso (R := R) (K := K) N).hom =
      (constantBaseChangeIso (R := R) (K := K) G).hom ≫
        constantQuotientMap K N :=
  constantBaseChangeIso_naturality (R := R) (K := K) (QuotientGroup.mk' N)

end FiniteFlatCommGroupScheme
end AlgebraicGeometry
