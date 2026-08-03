/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.QuasiFiniteFppfHOne

/-!
# Canonical kernels of ambient commutative group schemes

The kernel of an arbitrary commutative group-scheme morphism exists before imposing any
finiteness property: take its pullback against the identity section in internal groups.  This
file constructs that commutative group scheme, identifies its underlying scheme with the
ordinary scheme-theoretic pullback, and proves its universal property on points of every test
scheme.  Consequently the represented point functors are exact at the source.

This ambient construction is required for Mazur's integral pre-admissible groups, which are
quasi-finite rather than finite at primes dividing the level.  The final theorems are concrete
compatibility consumers: the construction recovers the existing canonical finite-flat kernel
when that kernel is flat, and every quasi-finite morphism consumes the ambient point-exactness
theorem.  No claim is made that the kernel of an arbitrary quasi-finite flat morphism is itself
flat; the later four-factor exact sequences must supply that arithmetic input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.CommGroupScheme

universe u

variable {S : Scheme.{u}}

/-- Underlying scheme morphism of an ambient commutative group-scheme morphism. -/
abbrev underlyingHom {G H : CommGroupScheme S} (f : G ⟶ H) :
    G.X.left ⟶ H.X.left :=
  f.hom.hom.hom.left

/-- Underlying scheme of the canonical kernel pullback. -/
abbrev kernelScheme {G H : CommGroupScheme S} (f : G ⟶ H) : Scheme.{u} :=
  pullback (underlyingHom f) (η[H.X].left)

/-- Projection from the canonical kernel scheme to its source. -/
abbrev kernelι {G H : CommGroupScheme S} (f : G ⟶ H) :
    kernelScheme f ⟶ G.X.left :=
  pullback.fst (underlyingHom f) (η[H.X].left)

/-- Structure morphism of the canonical kernel scheme. -/
abbrev kernelStructureMap {G H : CommGroupScheme S} (f : G ⟶ H) :
    kernelScheme f ⟶ S :=
  pullback.snd (underlyingHom f) (η[H.X].left)

@[reassoc (attr := simp)]
theorem kernel_condition {G H : CommGroupScheme S} (f : G ⟶ H) :
    kernelι f ≫ underlyingHom f =
      kernelStructureMap f ≫ η[H.X].left :=
  pullback.condition

/-- Zero map from the trivial internal group to the target. -/
noncomputable abbrev kernelZero (H : CommGroupScheme S) :
    Grp.trivial (Over S) ⟶ H.toGrp :=
  default

/-- Kernel inherited in internal groups. -/
noncomputable abbrev kernelGrp {G H : CommGroupScheme S} (f : G ⟶ H) :
    Grp (Over S) :=
  pullback f.hom (kernelZero H)

theorem kernelGrp_isComm {G H : CommGroupScheme S} (f : G ⟶ H) :
    IsCommMonObj (kernelGrp f).X := by
  let se : SplitMono (kernelZero H) := SplitMono.mk default (Subsingleton.elim _ _)
  letI : Mono (kernelZero H) := se.mono
  haveI : Mono (pullback.fst f.hom (kernelZero H)) := inferInstance
  haveI : Mono (pullback.fst f.hom (kernelZero H)).hom.hom := inferInstanceAs
    (Mono ((Grp.forget (Over S)).map (pullback.fst f.hom (kernelZero H))))
  constructor
  apply (cancel_mono (pullback.fst f.hom (kernelZero H)).hom.hom).1
  rw [Category.assoc, IsMonHom.mul_hom]
  rw [← Category.assoc, ← BraidedCategory.braiding_naturality, Category.assoc,
    IsCommMonObj.mul_comm]

/-- Canonical ambient commutative group-scheme kernel. -/
noncomputable abbrev kernel {G H : CommGroupScheme S} (f : G ⟶ H) :
    CommGroupScheme S :=
  letI : IsCommMonObj (kernelGrp f).X := kernelGrp_isComm f
  { X := (kernelGrp f).X }

/-- Canonical kernel inclusion. -/
noncomputable def kernelInclusion {G H : CommGroupScheme S} (f : G ⟶ H) :
    kernel f ⟶ G := by
  apply InducedCategory.homMk
  exact pullback.fst f.hom (kernelZero H)

theorem kernelGrp_isPullback {G H : CommGroupScheme S} (f : G ⟶ H) :
    IsPullback
      (pullback.fst f.hom (kernelZero H)).hom.hom.left
      (pullback.snd f.hom (kernelZero H)).hom.hom.left
      (underlyingHom f) (η[H.X].left) := by
  change IsPullback
    ((Over.forget S).map
      ((Grp.forget (Over S)).map (pullback.fst f.hom (kernelZero H))))
    ((Over.forget S).map
      ((Grp.forget (Over S)).map (pullback.snd f.hom (kernelZero H))))
    ((Over.forget S).map ((Grp.forget (Over S)).map f.hom))
    ((Over.forget S).map ((Grp.forget (Over S)).map (kernelZero H)))
  exact (((IsPullback.of_hasPullback f.hom (kernelZero H)).map
    (Grp.forget (Over S))).map (Over.forget S))

/-- Canonical identification of the internal-group kernel with the scheme pullback. -/
noncomputable def kernelSchemeIso {G H : CommGroupScheme S} (f : G ⟶ H) :
    (kernelGrp f).X.left ≅ kernelScheme f :=
  (kernelGrp_isPullback f).isoPullback

@[reassoc]
theorem kernelSchemeIso_hom_structureMap
    {G H : CommGroupScheme S} (f : G ⟶ H) :
    (kernelSchemeIso f).hom ≫ kernelStructureMap f = (kernelGrp f).X.hom := by
  have hs : (kernelSchemeIso f).hom ≫ kernelStructureMap f =
      (pullback.snd f.hom (kernelZero H)).hom.hom.left := by
    change (kernelGrp_isPullback f).isoPullback.hom ≫
      pullback.snd (underlyingHom f) (η[H.X].left) =
        (pullback.snd f.hom (kernelZero H)).hom.hom.left
    exact IsPullback.isoPullback_hom_snd (kernelGrp_isPullback f)
  rw [hs]
  exact Over.w (pullback.snd f.hom (kernelZero H)).hom.hom

@[reassoc]
theorem kernelSchemeIso_hom_kernelι
    {G H : CommGroupScheme S} (f : G ⟶ H) :
    (kernelSchemeIso f).hom ≫ kernelι f =
      underlyingHom (kernelInclusion f) := by
  change (kernelGrp_isPullback f).isoPullback.hom ≫
    pullback.fst (underlyingHom f) (η[H.X].left) =
      (pullback.fst f.hom (kernelZero H)).hom.hom.left
  exact IsPullback.isoPullback_hom_fst (kernelGrp_isPullback f)

@[reassoc]
theorem kernelInclusion_condition {G H : CommGroupScheme S} (f : G ⟶ H) :
    underlyingHom (kernelInclusion f) ≫ underlyingHom f =
      (kernel f).X.hom ≫ η[H.X].left := by
  rw [← kernelSchemeIso_hom_kernelι, Category.assoc, kernel_condition,
    ← Category.assoc, kernelSchemeIso_hom_structureMap]

@[simp]
theorem mapPoint_kernelInclusion_eq_one {G H : CommGroupScheme S}
    (f : G ⟶ H) (T : Over S) (y : (kernel f).Point T) :
    mapPoint f T (mapPoint (kernelInclusion f) T y) = 1 := by
  apply Over.OverMorphism.ext
  change (y.left ≫ underlyingHom (kernelInclusion f)) ≫ underlyingHom f =
    T.hom ≫ η[H.X].left
  rw [Category.assoc, kernelInclusion_condition, ← Category.assoc, Over.w y]

private theorem point_condition_scheme {G H : CommGroupScheme S}
    (f : G ⟶ H) (T : Over S) (x : G.Point T)
    (hx : mapPoint f T x = 1) :
    x.left ≫ underlyingHom f = T.hom ≫ η[H.X].left := by
  have hxleft := congrArg Over.Hom.left hx
  change x.left ≫ underlyingHom f = T.hom ≫ η[H.X].left at hxleft
  exact hxleft

/-- Every test-scheme point killed by a group-scheme morphism lifts uniquely to the canonical
ambient group-scheme kernel. -/
theorem existsUnique_kernelPoint_lift {G H : CommGroupScheme S}
    (f : G ⟶ H) (T : Over S) (x : G.Point T)
    (hx : mapPoint f T x = 1) :
    ∃! y : (kernel f).Point T, mapPoint (kernelInclusion f) T y = x := by
  let l : T.left ⟶ kernelScheme f :=
    pullback.lift x.left T.hom (point_condition_scheme f T x hx)
  have hstruct : (kernelSchemeIso f).inv ≫ (kernel f).X.hom =
      kernelStructureMap f := by
    apply (cancel_epi (kernelSchemeIso f).hom).1
    simpa using (kernelSchemeIso_hom_structureMap f).symm
  have hincl : (kernelSchemeIso f).inv ≫ underlyingHom (kernelInclusion f) =
      kernelι f := by
    apply (cancel_epi (kernelSchemeIso f).hom).1
    simpa using (kernelSchemeIso_hom_kernelι f).symm
  let y : (kernel f).Point T := Over.homMk (l ≫ (kernelSchemeIso f).inv) (by
    rw [Category.assoc, hstruct]
    exact pullback.lift_snd _ _ _)
  refine ⟨y, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    change (l ≫ (kernelSchemeIso f).inv) ≫
      underlyingHom (kernelInclusion f) = x.left
    rw [Category.assoc, hincl]
    exact pullback.lift_fst _ _ _
  · intro z hz
    apply Over.OverMorphism.ext
    apply (cancel_mono (kernelSchemeIso f).hom).1
    change z.left ≫ (kernelSchemeIso f).hom =
      (l ≫ (kernelSchemeIso f).inv) ≫ (kernelSchemeIso f).hom
    rw [Category.assoc, (kernelSchemeIso f).inv_hom_id, Category.comp_id]
    apply pullback.hom_ext
    · rw [Category.assoc, kernelSchemeIso_hom_kernelι]
      rw [show l ≫ kernelι f = x.left by exact pullback.lift_fst _ _ _]
      exact congrArg Over.Hom.left hz
    · rw [Category.assoc, kernelSchemeIso_hom_structureMap]
      rw [show l ≫ kernelStructureMap f = T.hom by exact pullback.lift_snd _ _ _]
      exact Over.w z

/-- The canonical kernel inclusion is injective on points of every test scheme. -/
theorem kernelInclusion_point_injective {G H : CommGroupScheme S}
    (f : G ⟶ H) (T : Over S) :
    Function.Injective (mapPoint (kernelInclusion f) T) := by
  intro a b hab
  exact (existsUnique_kernelPoint_lift f T
    (mapPoint (kernelInclusion f) T a)
    (mapPoint_kernelInclusion_eq_one f T a)).unique rfl hab.symm

/-- The canonical kernel inclusion as a homomorphism into the pointwise kernel. -/
def pointKernelHom {G H : CommGroupScheme S} (f : G ⟶ H) (T : Over S) :
    (kernel f).Point T →* (mapPoint f T).ker :=
  (mapPoint (kernelInclusion f) T).codRestrict
    (mapPoint f T).ker (mapPoint_kernelInclusion_eq_one f T)

/-- The scheme-theoretic ambient kernel represents the pointwise kernel functor on every test
scheme, as a multiplicative equivalence rather than only a bijection of sets. -/
noncomputable def pointKernelMulEquiv {G H : CommGroupScheme S}
    (f : G ⟶ H) (T : Over S) :
    (kernel f).Point T ≃* (mapPoint f T).ker :=
  MulEquiv.ofBijective (pointKernelHom f T)
    ⟨by
      intro a b hab
      apply kernelInclusion_point_injective f T
      exact congrArg Subtype.val hab, by
      intro x
      obtain ⟨y, hy, _⟩ := existsUnique_kernelPoint_lift f T x.1 x.2
      exact ⟨y, Subtype.ext hy⟩⟩

/-- The canonical ambient kernel is exact on represented points of every test scheme. -/
theorem kernel_point_mulExact {G H : CommGroupScheme S}
    (f : G ⟶ H) (T : Over S) :
    Function.MulExact (mapPoint (kernelInclusion f) T) (mapPoint f T) := by
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy, _⟩ := existsUnique_kernelPoint_lift f T x hx
    exact ⟨y, hy⟩
  · rintro ⟨y, rfl⟩
    exact mapPoint_kernelInclusion_eq_one f T y

end AlgebraicGeometry.CommGroupScheme

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme

universe u

open scoped CategoryTheory.MonObj

variable {S : Scheme.{u}} {G H : FiniteFlatCommGroupScheme S}

/-- Forgetting the finite-flat structure on the existing internal-group kernel gives the
canonical ambient kernel definitionally. -/
theorem commGroupScheme_kernel_eq (f : G ⟶ H) :
    CommGroupScheme.kernel f.hom = kernelCommGroupScheme f :=
  rfl

/-- The ambient and finite-flat canonical kernel inclusions agree definitionally. -/
theorem commGroupScheme_kernelInclusion_eq (f : G ⟶ H) :
    CommGroupScheme.kernelInclusion f.hom =
      kernelCommGroupSchemeInclusion f :=
  rfl

/-- The ambient canonical-kernel exactness specializes to the canonical finite-flat kernel
whenever the latter carries the required finite-flat structure. -/
theorem canonicalKernel_point_mulExact
    (f : G ⟶ H) [IsFinite (kernelStructureMap f)] [Flat (kernelStructureMap f)]
    (T : Over S) :
    Function.MulExact (mapPoint (kernelInclusion f) T) (mapPoint f T) := by
  exact CommGroupScheme.kernel_point_mulExact f.hom T

end AlgebraicGeometry.FiniteFlatCommGroupScheme

namespace AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme

universe u

variable {S : Scheme.{u}} {G H : QuasiFiniteFlatCommGroupScheme S}

/-- Every quasi-finite group-scheme morphism is exact at its canonical ambient kernel on all
represented test-scheme points; no finite-flat hypothesis is used. -/
theorem canonicalAmbientKernel_point_mulExact
    (f : G ⟶ H) (T : Over S) :
    Function.MulExact
      (CommGroupScheme.mapPoint (CommGroupScheme.kernelInclusion f.hom) T)
      (mapPoint f T) :=
  CommGroupScheme.kernel_point_mulExact f.hom T

/-- The canonical ambient kernel of a quasi-finite group-scheme morphism represents its
pointwise kernel on every test scheme.  The target is ambient because flatness of this kernel is
an additional arithmetic theorem, not a formal consequence of the endpoint wrappers. -/
noncomputable def canonicalAmbientKernel_pointMulEquiv
    (f : G ⟶ H) (T : Over S) :
    (CommGroupScheme.kernel f.hom).Point T ≃*
      (mapPoint f T).ker :=
  CommGroupScheme.pointKernelMulEquiv f.hom T

end AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme
