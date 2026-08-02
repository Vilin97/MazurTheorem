/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_

/-!
# Finite flat commutative group schemes

This file packages commutative group objects over a scheme whose structure morphism is finite
and flat.  The ambient group-scheme category is mathlib's category of internal commutative group
objects in `Over S`; the finite-flat category is its full subcategory.  Consequently morphisms
carry all compatibility with multiplication, identity, and inverse without repeating those laws.

The rank is deliberately a function on the base.  A finite flat morphism need not have a single
global rank on a disconnected base.  `HasConstantOrder G n` records the additional assertion
needed to speak of one order `n`.

The scheme-theoretic kernel is exposed as the pullback of a homomorphism along the identity
section.  Packaging it back into the finite-flat category requires a commutative group structure
and flatness over the base; neither is silently postulated here.  In particular, flatness of
kernels is an arithmetic-base theorem rather than a formal consequence of the two source and
target objects being finite flat.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj

namespace AlgebraicGeometry

universe u

/-- A commutative group scheme over `S`, expressed as an internal commutative group object in
the slice category of schemes over `S`. -/
abbrev CommGroupScheme (S : Scheme.{u}) := CommGrp (Over S)

/-- The object property saying that the structure morphism of a commutative group scheme is
finite and flat. -/
def finiteFlatCommGroupSchemeProperty (S : Scheme.{u}) :
    ObjectProperty (CommGroupScheme S) :=
  fun G => IsFinite G.X.hom ∧ Flat G.X.hom

/-- Finite flat commutative group schemes over `S` form the full subcategory of commutative
group schemes whose structure morphism is finite and flat. -/
abbrev FiniteFlatCommGroupScheme (S : Scheme.{u}) :=
  (finiteFlatCommGroupSchemeProperty S).FullSubcategory

namespace FiniteFlatCommGroupScheme

variable {S T U : Scheme.{u}}

/-- The underlying commutative group scheme. -/
abbrev toCommGroupScheme (G : FiniteFlatCommGroupScheme S) : CommGroupScheme S := G.obj

/-- The underlying scheme. -/
abbrev scheme (G : FiniteFlatCommGroupScheme S) : Scheme.{u} := G.obj.X.left

/-- The finite flat structure morphism. -/
abbrev structureMap (G : FiniteFlatCommGroupScheme S) : G.scheme ⟶ S := G.obj.X.hom

instance (G : FiniteFlatCommGroupScheme S) : IsFinite G.structureMap := G.property.1

instance (G : FiniteFlatCommGroupScheme S) : Flat G.structureMap := G.property.2

/-- The underlying morphism of schemes of a morphism of finite flat commutative group schemes. -/
abbrev hom {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H) : G.scheme ⟶ H.scheme :=
  f.hom.hom.hom.hom.left

@[simp]
theorem hom_id (G : FiniteFlatCommGroupScheme S) : hom (𝟙 G) = 𝟙 G.scheme := rfl

@[simp]
theorem hom_comp {G H K : FiniteFlatCommGroupScheme S} (f : G ⟶ H) (g : H ⟶ K) :
    hom (f ≫ g) = hom f ≫ hom g := rfl

@[reassoc (attr := simp)]
theorem hom_comp_structureMap {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H) :
    hom f ≫ H.structureMap = G.structureMap :=
  f.hom.hom.hom.hom.w

/-- The group of `X`-valued points of `G`, where `X` is any scheme over the same base.

Because `G` is an internal commutative group object, this hom-set carries its canonical
commutative group structure. -/
abbrev Point (G : FiniteFlatCommGroupScheme S) (X : Over S) := X ⟶ G.obj.X

/-- A homomorphism of finite-flat commutative group schemes acts on points by postcomposition. -/
def mapPoint {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H) (X : Over S) :
    G.Point X →* H.Point X :=
  IsMonHom.monoidHom f.hom.hom.hom.hom X

@[simp]
theorem mapPoint_apply {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H)
    (X : Over S) (x : G.Point X) :
    mapPoint f X x = x ≫ f.hom.hom.hom.hom :=
  rfl

@[simp]
theorem mapPoint_id (G : FiniteFlatCommGroupScheme S) (X : Over S) :
    mapPoint (CategoryStruct.id G) X = MonoidHom.id (G.Point X) := by
  ext x
  simp

@[simp]
theorem mapPoint_comp {G H K : FiniteFlatCommGroupScheme S} (f : G ⟶ H) (g : H ⟶ K)
    (X : Over S) :
    mapPoint (f ≫ g) X = (mapPoint g X).comp (mapPoint f X) := by
  ext x
  simp

/-- Base change of finite flat commutative group schemes.  This is a functor because pullback is a
finite-product-preserving functor on slice categories, hence maps internal commutative groups. -/
def baseChange (f : T ⟶ S) :
    FiniteFlatCommGroupScheme S ⥤ FiniteFlatCommGroupScheme T where
  obj G :=
    { obj := (Over.pullback f).mapCommGrp.obj G.obj
      property := by
        change IsFinite (pullback.snd G.structureMap f) ∧ Flat (pullback.snd G.structureMap f)
        exact ⟨inferInstance, inferInstance⟩ }
  map g := ObjectProperty.homMk ((Over.pullback f).mapCommGrp.map g.hom)

@[simp]
theorem baseChange_scheme (f : T ⟶ S) (G : FiniteFlatCommGroupScheme S) :
    ((baseChange f).obj G).scheme = pullback G.structureMap f := rfl

@[simp]
theorem baseChange_structureMap (f : T ⟶ S) (G : FiniteFlatCommGroupScheme S) :
    ((baseChange f).obj G).structureMap = pullback.snd G.structureMap f := rfl

/-- The rank of a finite flat commutative group scheme at a point of its base. -/
def orderAt (G : FiniteFlatCommGroupScheme S) : S → ℕ := G.structureMap.finrank

/-- The assertion that a finite flat commutative group scheme has one constant order on its
possibly disconnected base. -/
def HasConstantOrder (G : FiniteFlatCommGroupScheme S) (n : ℕ) : Prop :=
  G.orderAt = Function.const S n

theorem orderAt_baseChange (f : T ⟶ S) (G : FiniteFlatCommGroupScheme S) (t : T) :
    ((baseChange f).obj G).orderAt t = G.orderAt (f t) :=
  Scheme.Hom.finrank_pullback_snd G.structureMap f t

theorem hasConstantOrder_baseChange {G : FiniteFlatCommGroupScheme S} {n : ℕ}
    (hG : G.HasConstantOrder n) (f : T ⟶ S) :
    ((baseChange f).obj G).HasConstantOrder n := by
  funext t
  rw [orderAt_baseChange, hG]
  rfl

/-- The underlying scheme of the scheme-theoretic kernel of `f`, obtained by pulling `G` back
along the identity section of `H`. -/
def kernelScheme {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H) : Scheme.{u} :=
  pullback (hom f) (η[H.obj.X].left)

/-- The canonical map from the scheme-theoretic kernel to the source group scheme. -/
def kernelι {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H) :
    kernelScheme f ⟶ G.scheme :=
  pullback.fst (hom f) (η[H.obj.X].left)

/-- The structure morphism of the underlying scheme-theoretic kernel. -/
def kernelStructureMap {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H) :
    kernelScheme f ⟶ S :=
  pullback.snd (hom f) (η[H.obj.X].left)

@[reassoc (attr := simp)]
theorem kernel_condition {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H) :
    kernelι f ≫ hom f = kernelStructureMap f ≫ η[H.obj.X].left :=
  pullback.condition

/-- Data certifying that the scheme-theoretic kernel carries the expected finite-flat
commutative group-scheme structure.  The isomorphism fixes its underlying scheme and structure
map, while the universal pullback above fixes its geometric meaning. -/
structure KernelPresentation {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H) where
  /-- The kernel as a finite flat commutative group scheme. -/
  kernel : FiniteFlatCommGroupScheme S
  /-- The kernel inclusion as a homomorphism of group schemes. -/
  inclusion : kernel ⟶ G
  /-- Identification with the scheme-theoretic pullback kernel. -/
  schemeIso : kernel.scheme ≅ kernelScheme f
  /-- Compatibility of the identification with the maps to the base. -/
  schemeIso_hom_structureMap : schemeIso.hom ≫ kernelStructureMap f = kernel.structureMap
  /-- Compatibility of the group-scheme inclusion with the pullback projection. -/
  schemeIso_hom_kernelι : schemeIso.hom ≫ kernelι f = hom inclusion

namespace KernelPresentation

variable {G H : FiniteFlatCommGroupScheme S} {f : G ⟶ H}

/-- The certified kernel inclusion maps trivially to the target group scheme. -/
@[reassoc]
theorem inclusion_condition (P : KernelPresentation f) :
    hom P.inclusion ≫ hom f = P.kernel.structureMap ≫ η[H.obj.X].left := by
  rw [← P.schemeIso_hom_kernelι, Category.assoc, kernel_condition, ← Category.assoc,
    P.schemeIso_hom_structureMap]

end KernelPresentation

end FiniteFlatCommGroupScheme

end AlgebraicGeometry
