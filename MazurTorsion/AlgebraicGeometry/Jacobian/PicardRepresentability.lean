/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
import MazurTorsion.AlgebraicGeometry.Jacobian.EulerCharacteristicDegree

/-!
# Representability interface for `Pic⁰`

The underlying functor of a sheaf of commutative groups determines a
commutative group object on any representing scheme.  Mathlib's
`CommGrpObj.ofRepresentableBy` performs this Yoneda transport; this file
specializes it to the degree-zero relative Picard sheaf.

No representing scheme is postulated here.  `Representation` is explicit
data supplied by the symmetric-power representability theorem.  Its named
downstream consumer is `PicardIdentityComponent`.
-/

noncomputable section

open CategoryTheory
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.RelativePicard

universe u

variable {S X : Scheme.{u}}

/-- The degree-zero Picard sheaf, in multiplicative notation and viewed as a
presheaf. -/
noncomputable def degreeZeroCommPresheaf
    (p : X ⟶ S) (d : DegreeMap p) :
    (Over S)ᵒᵖ ⥤ CommGrpCat.{u + 1} :=
  (degreeZeroSheaf p d).obj ⋙ AddCommGrpCat.toCommGrp

/-- Data saying that an `S`-scheme represents the degree-zero Picard sheaf. -/
abbrev Representation
    (p : X ⟶ S) (d : DegreeMap p) (J : Over S) :=
  ((degreeZeroCommPresheaf p d) ⋙ forget CommGrpCat).RepresentableBy J

/-- A representing scheme inherits the commutative group-object structure of
the degree-zero Picard functor. -/
@[instance_reducible]
noncomputable def commGrpObjOfRepresentation
    (p : X ⟶ S) (d : DegreeMap p) (J : Over S)
    (hJ : Representation p d J) : CommGrpObj J :=
  CommGrpObj.ofRepresentableBy J (degreeZeroCommPresheaf p d) hJ

/-- The group-object part of the structure transported by Yoneda. -/
@[instance_reducible]
noncomputable def grpObjOfRepresentation
    (p : X ⟶ S) (d : DegreeMap p) (J : Over S)
    (hJ : Representation p d J) : GrpObj J := by
  letI := commGrpObjOfRepresentation p d J hJ
  infer_instance

/-- The commutativity proof transported by Yoneda. -/
theorem isCommMonObjOfRepresentation
    (p : X ⟶ S) (d : DegreeMap p) (J : Over S)
    (hJ : Representation p d J) :
    letI := grpObjOfRepresentation p d J hJ
    IsCommMonObj J := by
  letI := commGrpObjOfRepresentation p d J hJ
  infer_instance

end MazurTorsion.AlgebraicGeometry.Jacobian.RelativePicard
