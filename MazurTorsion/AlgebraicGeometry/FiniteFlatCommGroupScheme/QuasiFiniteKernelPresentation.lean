/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.CommGroupSchemeKernel

/-!
# Kernel presentations for quasi-finite flat group schemes

The canonical kernel of an ambient commutative group-scheme morphism always exists, but its
flatness is not formal.  Mazur's four integral elementary-factor sequences instead provide an
actual quasi-finite flat kernel together with its geometric identification with that canonical
kernel.  `KernelPresentation` records exactly this data as an isomorphism of commutative group
schemes.

The chosen identification yields a multiplicative equivalence with the pointwise kernel and
therefore exactness on points of every test scheme.  The final adapter is a genuine downstream
consumer: when the canonical kernel is finite flat and locally of finite presentation, the
existing finite-flat kernel supplies this quasi-finite presentation definitionally.  No general
kernel-flatness or quotient-representability theorem is asserted.
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

end AlgebraicGeometry.CommGroupScheme

namespace AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme

universe u

variable {S : Scheme.{u}} {G H : QuasiFiniteFlatCommGroupScheme S}

/-- A chosen quasi-finite flat model of the canonical ambient kernel of a morphism.  Requiring
an isomorphism of commutative group schemes, rather than a pointwise equivalence, keeps the
kernel geometric. -/
structure KernelPresentation (f : G ⟶ H) where
  /-- The chosen quasi-finite flat kernel object. -/
  kernel : QuasiFiniteFlatCommGroupScheme S
  /-- Its group-scheme identification with the canonical ambient kernel. -/
  kernelIso : kernel.obj ≅ CommGroupScheme.kernel f.hom

namespace KernelPresentation

variable {f : G ⟶ H} (P : KernelPresentation f)

/-- Inclusion of the chosen quasi-finite kernel into the source. -/
def inclusion : P.kernel ⟶ G :=
  ObjectProperty.homMk
    (P.kernelIso.hom ≫ CommGroupScheme.kernelInclusion f.hom)

/-- Points of the chosen geometric kernel are the pointwise kernel of the original morphism. -/
noncomputable def pointKernelMulEquiv (T : Over S) :
    CommGroupScheme.Point P.kernel.obj T ≃* (mapPoint f T).ker :=
  (CommGroupScheme.pointMulEquivOfIso P.kernelIso T).trans
    (CommGroupScheme.pointKernelMulEquiv f.hom T)

@[simp]
theorem pointKernelMulEquiv_apply (T : Over S)
    (x : CommGroupScheme.Point P.kernel.obj T) :
    (P.pointKernelMulEquiv T x).1 = mapPoint P.inclusion T x := by
  change (x ≫ P.kernelIso.hom.hom.hom.hom) ≫
      (CommGroupScheme.kernelInclusion f.hom).hom.hom.hom =
    x ≫ (P.kernelIso.hom.hom.hom.hom ≫
      (CommGroupScheme.kernelInclusion f.hom).hom.hom.hom)
  exact Category.assoc _ _ _

@[simp]
theorem mapPoint_inclusion_eq_one (T : Over S)
    (x : CommGroupScheme.Point P.kernel.obj T) :
    mapPoint f T (mapPoint P.inclusion T x) = 1 :=
  (P.pointKernelMulEquiv T x).2

/-- The chosen quasi-finite kernel presentation is exact on represented points of every test
scheme. -/
theorem point_mulExact (T : Over S) :
    Function.MulExact (mapPoint P.inclusion T) (mapPoint f T) := by
  intro x
  constructor
  · intro hx
    let z : (mapPoint f T).ker := ⟨x, hx⟩
    exact ⟨(P.pointKernelMulEquiv T).symm z, by
      have h := P.pointKernelMulEquiv_apply T ((P.pointKernelMulEquiv T).symm z)
      rw [MulEquiv.apply_symm_apply] at h
      exact h.symm⟩
  · rintro ⟨y, rfl⟩
    exact P.mapPoint_inclusion_eq_one T y

end KernelPresentation

/-- The canonical finite-flat kernel gives a quasi-finite kernel presentation whenever its
structure map has the explicitly required finite-presentation property. -/
def KernelPresentation.ofFiniteFlatCanonical
    {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H)
    [LocallyOfFinitePresentation G.obj.X.hom]
    [LocallyOfFinitePresentation H.obj.X.hom]
    [IsFinite (FiniteFlatCommGroupScheme.kernelStructureMap f)]
    [Flat (FiniteFlatCommGroupScheme.kernelStructureMap f)]
    [LocallyOfFinitePresentation
      (FiniteFlatCommGroupScheme.kernel f).obj.X.hom] :
    KernelPresentation (ofFiniteFlatMap f) where
  kernel := ofFiniteFlat (FiniteFlatCommGroupScheme.kernel f)
  kernelIso := Iso.refl _

/-- The finite-flat canonical-kernel adapter has exactly the existing finite-flat inclusion. -/
theorem KernelPresentation.ofFiniteFlatCanonical_inclusion
    {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H)
    [LocallyOfFinitePresentation G.obj.X.hom]
    [LocallyOfFinitePresentation H.obj.X.hom]
    [IsFinite (FiniteFlatCommGroupScheme.kernelStructureMap f)]
    [Flat (FiniteFlatCommGroupScheme.kernelStructureMap f)]
    [LocallyOfFinitePresentation
      (FiniteFlatCommGroupScheme.kernel f).obj.X.hom] :
    (KernelPresentation.ofFiniteFlatCanonical f).inclusion =
      ofFiniteFlatMap (FiniteFlatCommGroupScheme.kernelInclusion f) :=
  rfl

end AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme
