/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.SplitComponentGraphIdeal

/-!
# The graph-ideal quotient is the split ordered-root family

On a split symmetric-power component, the product of the coordinate-graph
ideals is the kernel of the simultaneous sheetwise root-evaluation map.
The first isomorphism theorem therefore identifies the quotient by the
actual graph-product ideal with the product of the sheetwise ordered-root
algebras.

The scheme-level isomorphism retains its compatibility with the two closed
immersions into the common sheetwise affine-line ambient space.  It also
identifies the quotient presentation with Mathlib's ideal-sheaf subscheme,
so a geometric open-restriction calculation can transport the actual curve
incidence ideal without changing presentations.  The named downstream
consumers are `SplitComponentInvariantRootComparison` and the local chart in
`PointedIncidenceDescent`.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.SplitComponentGraphQuotient

open SplitComponentGraphIdeal
open SplitComponentMonicCoordinates
open SplitComponentOrderedIncidence
open SplitComponentUniversalRoot
open SplitFiniteSymmetricQuotient

variable (R : Type u) [CommRing R] [Nontrivial R]
variable (d m : ℕ) (c : splitComponentIndex d m)

local instance : MulAction (Equiv.Perm (Fin d)) (Fin d → Fin m) :=
  tuplePermutationAction d (Fin m)

/-- The coordinate algebra of the incidence family defined by the actual
product of coordinate-graph ideals. -/
abbrev orderedGraphQuotientAlgebra : Type u :=
  (orderedAmbientAlgebra R d m c) ⧸ orderedGraphIdeal R d m c

noncomputable local instance orderedProductRootAlgebraBaseAlgebra :
    Algebra R (orderedProductRootAlgebra R d m c) :=
  Algebra.compHom _
    (algebraMap R (SplitComponentUniversalRoot.coefficientRing R d m c))

/-- Simultaneous sheetwise root evaluation as an `R`-algebra map. -/
noncomputable def ambientToOrderedRootAlgHom :
    orderedAmbientAlgebra R d m c →ₐ[R]
      orderedProductRootAlgebra R d m c where
  toRingHom := ambientToOrderedRoot R d m c
  commutes' r := by
    funext j
    change AdjoinRoot.mk
        (sheetOrderedRootPolynomial R d m c j)
        (Polynomial.C (MvPolynomial.C r)) =
      algebraMap (coefficientRing R d m c)
        (AdjoinRoot (sheetOrderedRootPolynomial R d m c j))
        (MvPolynomial.C r)
    rw [AdjoinRoot.mk_C]
    rfl

/-- The graph-ideal quotient is the product of the sheetwise ordered-root
algebras. -/
noncomputable def orderedGraphQuotientEquivOrderedRoot :
    orderedGraphQuotientAlgebra R d m c ≃ₐ[R]
      orderedProductRootAlgebra R d m c :=
  (Ideal.quotientEquivAlgOfEq R
      (orderedGraphIdeal_eq_ker R d m c)).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := ambientToOrderedRootAlgHom R d m c)
      (ambientToOrderedRoot_surjective R d m c))

/-- The graph-product incidence family as a closed subscheme of the
sheetwise affine-line ambient space. -/
noncomputable def orderedGraphLocusι :
    Spec (.of (orderedGraphQuotientAlgebra R d m c)) ⟶
      Spec (.of (orderedAmbientAlgebra R d m c)) :=
  Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (orderedGraphIdeal R d m c)))

instance orderedGraphLocusι_isClosedImmersion :
    IsClosedImmersion (orderedGraphLocusι R d m c) := by
  apply IsClosedImmersion.spec_of_surjective
  exact Ideal.Quotient.mk_surjective

/-- The graph ideal written in the canonical global-section ring of its
ambient affine spectrum.  The `ΓSpecIso` transport is necessary because
Mathlib's `ofIdealTop` constructor takes an ideal of global sections rather
than an ideal of the original presentation ring. -/
noncomputable def orderedGraphIdealSections :
    Ideal Γ(Spec (.of (orderedAmbientAlgebra R d m c)), ⊤) :=
  Ideal.map
    (Scheme.ΓSpecIso (.of (orderedAmbientAlgebra R d m c))).inv.hom
    (orderedGraphIdeal R d m c)

/-- The ideal sheaf on the sheetwise affine-line ambient spectrum defined by
the product of all ordered coordinate graphs. -/
noncomputable abbrev orderedGraphIdealSheaf :
    (Spec (.of (orderedAmbientAlgebra R d m c))).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    (orderedGraphIdealSections R d m c)

omit [Nontrivial R] in
/-- The kernel ideal sheaf of the graph-locus immersion is exactly the ideal
sheaf obtained from the algebraic graph-product ideal.  This is the bridge
from affine graph algebra to geometric ideal-sheaf restriction. -/
theorem orderedGraphLocusι_ker :
    (orderedGraphLocusι R d m c).ker =
      orderedGraphIdealSheaf R d m c := by
  rw [Scheme.ker_of_isAffine]
  congr 1
  rw [orderedGraphIdealSections]
  ext y
  rw [Ideal.mem_map_iff_of_surjective
    (Scheme.ΓSpecIso
      (.of (orderedAmbientAlgebra R d m c))).inv.hom
    (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso
        (.of (orderedAmbientAlgebra R d m c))).inv).2]
  have happ (a : Γ(Spec (.of (orderedAmbientAlgebra R d m c)), ⊤)) :
      (Scheme.ΓSpecIso (.of (orderedGraphQuotientAlgebra R d m c))).hom
          ((orderedGraphLocusι R d m c).appTop a) =
        Ideal.Quotient.mk (orderedGraphIdeal R d m c)
          ((Scheme.ΓSpecIso
            (.of (orderedAmbientAlgebra R d m c))).hom a) := by
    change (((orderedGraphLocusι R d m c).appTop ≫
      (Scheme.ΓSpecIso
        (.of (orderedGraphQuotientAlgebra R d m c))).hom) a) = _
    rw [orderedGraphLocusι, Scheme.ΓSpecIso_naturality]
    rfl
  constructor
  · intro hy
    refine ⟨(Scheme.ΓSpecIso
      (.of (orderedAmbientAlgebra R d m c))).hom y, ?_, by simp⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [← happ]
    rw [RingHom.mem_ker] at hy
    simp [hy]
  · rintro ⟨x, hx, rfl⟩
    rw [RingHom.mem_ker]
    apply (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso
        (.of (orderedGraphQuotientAlgebra R d m c))).hom).1
    rw [map_zero, happ]
    simpa using Ideal.Quotient.eq_zero_iff_mem.mpr hx

omit [Nontrivial R] in
/-- The affine quotient presentation of the graph locus agrees canonically
with the subscheme constructed from its ideal sheaf. -/
noncomputable def orderedGraphLocusIsoIdealSubscheme :
    Spec (.of (orderedGraphQuotientAlgebra R d m c)) ≅
      (orderedGraphIdealSheaf R d m c).subscheme :=
  asIso (orderedGraphLocusι R d m c).toImage ≪≫
    eqToIso (congrArg Scheme.IdealSheafData.subscheme
      (orderedGraphLocusι_ker R d m c))

private theorem closedImmersionImageTransport_hom_comp
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (I : Y.IdealSheafData) (h : f.ker = I) :
    (asIso f.toImage ≪≫
        eqToIso (congrArg Scheme.IdealSheafData.subscheme h)).hom ≫
      I.subschemeι = f := by
  subst I
  simp

omit [Nontrivial R] in
/-- The quotient-to-subscheme isomorphism preserves the closed immersion
into the ambient sheetwise affine-line spectrum. -/
@[reassoc]
theorem orderedGraphLocusIsoIdealSubscheme_hom_comp_ι :
    (orderedGraphLocusIsoIdealSubscheme R d m c).hom ≫
        (orderedGraphIdealSheaf R d m c).subschemeι =
      orderedGraphLocusι R d m c :=
  closedImmersionImageTransport_hom_comp
    (orderedGraphLocusι R d m c) (orderedGraphIdealSheaf R d m c)
    (orderedGraphLocusι_ker R d m c)

/-- The graph-defined incidence family is canonically the ordered-root
family.  The orientation is chosen so that the isomorphism followed by the
graph closed immersion equals the ordered-root closed immersion. -/
noncomputable def orderedRootLocusIsoGraphLocus :
    Spec (.of (orderedProductRootAlgebra R d m c)) ≅
      Spec (.of (orderedGraphQuotientAlgebra R d m c)) where
  hom := Spec.map (CommRingCat.ofHom
    (orderedGraphQuotientEquivOrderedRoot R d m c).toRingHom)
  inv := Spec.map (CommRingCat.ofHom
    (orderedGraphQuotientEquivOrderedRoot R d m c).symm.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ← Spec.map_id, Spec.map_inj]
    apply CommRingCat.hom_ext
    apply DFunLike.ext _ _
    intro x
    exact (orderedGraphQuotientEquivOrderedRoot R d m c).apply_symm_apply x
  inv_hom_id := by
    rw [← Spec.map_comp, ← Spec.map_id, Spec.map_inj]
    apply CommRingCat.hom_ext
    apply DFunLike.ext _ _
    intro x
    exact (orderedGraphQuotientEquivOrderedRoot R d m c).symm_apply_apply x

omit [Nontrivial R] in
/-- The first-isomorphism-theorem identification is compatible with the
closed immersions into the common ambient affine scheme. -/
@[reassoc]
theorem orderedRootLocusIsoGraphLocus_hom_comp_ι :
    (orderedRootLocusIsoGraphLocus R d m c).hom ≫
        orderedGraphLocusι R d m c =
      orderedRootLocusι R d m c := by
  rw [orderedRootLocusIsoGraphLocus, orderedGraphLocusι,
    orderedRootLocusι, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact Ideal.quotientKerAlgEquivOfSurjective_mk
    (f := ambientToOrderedRootAlgHom R d m c)
    (ambientToOrderedRoot_surjective R d m c) x

end MazurTorsion.AlgebraicGeometry.Jacobian.SplitComponentGraphQuotient
