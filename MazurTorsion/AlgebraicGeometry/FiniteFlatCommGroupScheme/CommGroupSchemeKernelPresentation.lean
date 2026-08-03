/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.CommGroupSchemeKernel

/-!
# Geometric kernel presentations for ambient commutative group schemes

The canonical kernel of an arbitrary morphism of commutative group schemes exists, but it need
not inherit a finiteness or flatness property from the source and target.  A
`KernelPresentation` records an actual supplied group scheme, its chosen inclusion, and its
geometric identification with that canonical kernel.  Compatibility with the inclusion rules
out unrelated pointwise models.

This interface is deliberately independent of finite-flat and quasi-finite wrappers.  Its
point-kernel equivalence, unique lift, and represented-point exactness API therefore applies to
both settings without duplicating the later fppf connecting construction.  No claim is made
that an arbitrary canonical kernel is flat, quasi-finite, finite, or finitely presented.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.CommGroupScheme

universe u

variable {S : Scheme.{u}} {G H K : CommGroupScheme S}

/-- Ambient group-scheme point maps preserve identity morphisms. -/
@[simp]
theorem mapPoint_id (G : CommGroupScheme S) (T : Over S) :
    mapPoint (CategoryStruct.id G) T = MonoidHom.id (G.Point T) := by
  ext x
  simp [mapPoint]

/-- Ambient group-scheme point maps turn composition into composition of homomorphisms. -/
@[simp]
theorem mapPoint_comp (f : G ⟶ H) (g : H ⟶ K) (T : Over S) :
    mapPoint (f ≫ g) T = (mapPoint g T).comp (mapPoint f T) := by
  ext x
  simp only [mapPoint_apply, MonoidHom.comp_apply]
  exact (Category.assoc _ _ _).symm

/-- An isomorphism of ambient commutative group schemes induces a multiplicative equivalence on
points of every test scheme. -/
def pointMulEquivOfIso (e : G ≅ H) (T : Over S) : G.Point T ≃* H.Point T where
  toFun := mapPoint e.hom T
  invFun := mapPoint e.inv T
  left_inv x := by
    rw [← MonoidHom.comp_apply, ← mapPoint_comp, e.hom_inv_id, mapPoint_id]
    rfl
  right_inv x := by
    rw [← MonoidHom.comp_apply, ← mapPoint_comp, e.inv_hom_id, mapPoint_id]
    rfl
  map_mul' x y := map_mul (mapPoint e.hom T) x y

/-- A supplied commutative group scheme identified geometrically with the canonical kernel of
`f`.  The explicit inclusion preserves a caller's chosen exact-sequence morphism, while the
compatibility field certifies that it is the inclusion induced by the geometric kernel. -/
structure KernelPresentation (f : G ⟶ H) where
  /-- The supplied geometric kernel object. -/
  kernel : CommGroupScheme S
  /-- The chosen inclusion into the source. -/
  inclusion : kernel ⟶ G
  /-- Identification with the canonical ambient group-scheme kernel. -/
  kernelIso : kernel ≅ CommGroupScheme.kernel f
  /-- The chosen inclusion is the canonical one under the geometric identification. -/
  kernelIso_hom_kernelInclusion :
    kernelIso.hom ≫ CommGroupScheme.kernelInclusion f = inclusion

namespace KernelPresentation

variable {f : G ⟶ H} (P : KernelPresentation f)

/-- Points of a supplied geometric kernel are the pointwise kernel of the original morphism. -/
noncomputable def pointKernelMulEquiv (T : Over S) :
    P.kernel.Point T ≃* (mapPoint f T).ker :=
  (pointMulEquivOfIso P.kernelIso T).trans (CommGroupScheme.pointKernelMulEquiv f T)

@[simp]
theorem pointKernelMulEquiv_apply (T : Over S) (x : P.kernel.Point T) :
    (P.pointKernelMulEquiv T x).1 = mapPoint P.inclusion T x := by
  change (x ≫ P.kernelIso.hom.hom.hom.hom) ≫
      (CommGroupScheme.kernelInclusion f).hom.hom.hom =
    x ≫ P.inclusion.hom.hom.hom
  rw [Category.assoc]
  exact congrArg (fun q ↦ x ≫ q.hom.hom.hom) P.kernelIso_hom_kernelInclusion

/-- Every supplied-kernel point maps to the identity in the target. -/
@[simp]
theorem mapPoint_inclusion_eq_one (T : Over S) (x : P.kernel.Point T) :
    mapPoint f T (mapPoint P.inclusion T x) = 1 := by
  rw [← P.pointKernelMulEquiv_apply T x]
  exact (P.pointKernelMulEquiv T x).2

/-- The canonical chosen lift of a point killed by the original morphism. -/
noncomputable def liftPoint {T : Over S} (x : G.Point T) (hx : mapPoint f T x = 1) :
    P.kernel.Point T :=
  (P.pointKernelMulEquiv T).symm ⟨x, hx⟩

@[simp]
theorem mapPoint_liftPoint {T : Over S} (x : G.Point T)
    (hx : mapPoint f T x = 1) :
    mapPoint P.inclusion T (P.liftPoint x hx) = x := by
  have h := P.pointKernelMulEquiv_apply T (P.liftPoint x hx)
  rw [show P.pointKernelMulEquiv T (P.liftPoint x hx) = ⟨x, hx⟩ by
    exact MulEquiv.apply_symm_apply (P.pointKernelMulEquiv T) ⟨x, hx⟩] at h
  exact h.symm

/-- A supplied geometric kernel inclusion is injective on every test scheme. -/
theorem inclusion_point_injective (T : Over S) :
    Function.Injective (mapPoint P.inclusion T) := by
  intro x y hxy
  apply (P.pointKernelMulEquiv T).injective
  apply Subtype.ext
  simpa only [P.pointKernelMulEquiv_apply] using hxy

/-- Every killed point lifts uniquely through the supplied geometric kernel. -/
theorem existsUnique_point_lift (T : Over S) (x : G.Point T)
    (hx : mapPoint f T x = 1) :
    ∃! y : P.kernel.Point T, mapPoint P.inclusion T y = x := by
  refine ⟨P.liftPoint x hx, P.mapPoint_liftPoint x hx, ?_⟩
  intro y hy
  apply P.inclusion_point_injective T
  exact hy.trans (P.mapPoint_liftPoint x hx).symm

/-- A geometric kernel presentation is exact on represented points of every test scheme. -/
theorem point_mulExact (T : Over S) :
    Function.MulExact (mapPoint P.inclusion T) (mapPoint f T) := by
  intro x
  constructor
  · intro hx
    exact ⟨P.liftPoint x hx, P.mapPoint_liftPoint x hx⟩
  · rintro ⟨y, rfl⟩
    exact P.mapPoint_inclusion_eq_one T y

/-- Concrete represented-point consumer of the ambient presentation: a source point is killed
exactly when it comes from the supplied geometric kernel. -/
theorem mapPoint_eq_one_iff_exists_kernelPoint (T : Over S) (x : G.Point T) :
    mapPoint f T x = 1 ↔
      ∃ y : P.kernel.Point T, mapPoint P.inclusion T y = x :=
  P.point_mulExact T x

end KernelPresentation

end AlgebraicGeometry.CommGroupScheme
