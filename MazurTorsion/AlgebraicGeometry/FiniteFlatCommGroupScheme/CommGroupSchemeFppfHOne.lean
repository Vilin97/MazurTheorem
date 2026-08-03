/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfHOneCommGroup

/-!
# Global fppf `H¹` for ambient commutative group schemes

Global fppf `H¹` only uses the represented commutative-group-valued point sheaf.  Finiteness
and flatness of the representing scheme are not needed to define that coefficient sheaf or its
cohomology.  This file exposes the construction for an arbitrary commutative group scheme over
the base while preserving the existing finite-flat API by definitional adapters.

The broader wrapper is needed for Mazur's pre-admissible groups over `Spec ℤ`: those groups are
quasi-finite over the bad prime and need not be finite over the whole base.  No quasi-finite
extension, elementary-factor classification, or cohomology calculation is asserted here.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.CommGroupScheme

universe v u

variable {S : Scheme.{u}}

/-- The group of points of an ambient commutative group scheme on a test scheme over its base. -/
abbrev Point (G : CommGroupScheme S) (T : Over S) := T ⟶ G.X

/-- The represented commutative-group-valued point presheaf of an ambient commutative group
scheme.  Unlike the older finite-flat wrapper, this definition makes no finiteness claim. -/
noncomputable def commPointPresheaf (G : CommGroupScheme S) :
    (Over S)ᵒᵖ ⥤ CommGrpCat.{u} where
  obj T := CommGrpCat.of (G.Point T.unop)
  map f := CommGrpCat.ofHom ((yonedaGrpObj G.X).map f).hom

/-- The represented point presheaf, forgotten from commutative groups to groups. -/
noncomputable def pointPresheaf (G : CommGroupScheme S) :
    (Over S)ᵒᵖ ⥤ GrpCat.{u} :=
  G.commPointPresheaf ⋙ forget₂ CommGrpCat GrpCat

@[simp]
lemma pointPresheaf_obj (G : CommGroupScheme S) (T : Over S) :
    G.pointPresheaf.obj (Opposite.op T) = GrpCat.of (G.Point T) :=
  rfl

/-- The point presheaf of every commutative group scheme is an fppf sheaf.  This is the
subcanonical representability argument and does not require the structure map to be finite. -/
theorem pointPresheaf_isFppfSheaf (G : CommGroupScheme S) :
    Presieve.IsSheaf (Scheme.fppfTopology.over S) (G.pointPresheaf ⋙ forget GrpCat) := by
  letI : (G.pointPresheaf ⋙ forget GrpCat).IsRepresentable :=
    (yonedaGrpObjRepresentableBy G.X).isRepresentable
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

/-- Global relative fppf `H¹` of an ambient commutative group scheme. -/
abbrev FppfHOne (G : CommGroupScheme S) : Type _ :=
  Scheme.FppfHOne.{u, v, u} S G.pointPresheaf

/-- The canonical common-refinement group law on global fppf `H¹`. -/
noncomputable instance (priority := 90) fppfHOneCommGroup (G : CommGroupScheme S) :
    CommGroup G.FppfHOne.{v} :=
  Scheme.FppfHOne.commGroup G.commPointPresheaf

end AlgebraicGeometry.CommGroupScheme

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme

universe v u

variable {S : Scheme.{u}}

/-- The ambient and finite-flat point-presheaf wrappers agree definitionally. -/
theorem commPointPresheaf_toCommGroupScheme (G : FiniteFlatCommGroupScheme S) :
    CommGroupScheme.commPointPresheaf G.obj = commPointPresheaf G :=
  rfl

/-- The existing finite-flat global fppf `H¹` is the ambient construction on the underlying
commutative group scheme.  This is a compatibility adapter, not a second cohomology theory. -/
noncomputable def fppfHOneMulEquivToCommGroupScheme
    (G : FiniteFlatCommGroupScheme S) :
    G.FppfHOne.{v} ≃* CommGroupScheme.FppfHOne.{v} G.obj :=
  MulEquiv.refl _

end AlgebraicGeometry.FiniteFlatCommGroupScheme
