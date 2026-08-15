/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.PicardRepresentability

/-!
# The represented degree-zero Picard scheme

Given an actual representability proof for the degree-zero relative Picard
sheaf, this file selects its representing `S`-scheme and transports the
commutative group structure by Yoneda.  Representability remains an explicit
typeclass hypothesis; this file does not manufacture it.

The named downstream consumers are `PicardGeometry` and `AbelJacobi`.
-/

noncomputable section

open CategoryTheory
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.PicardIdentityComponent

universe u

open RelativePicard

variable {S X : Scheme.{u}} (p : X ⟶ S) (d : DegreeMap p)

/-- The underlying type-valued degree-zero Picard functor. -/
noncomputable abbrev underlyingFunctor : (Over S)ᵒᵖ ⥤ Type (u + 1) :=
  degreeZeroCommPresheaf p d ⋙ forget CommGrpCat

/-- The chosen representing scheme for `Pic⁰`, conditional on the
representability theorem. -/
noncomputable def scheme [Functor.IsRepresentable (underlyingFunctor p d)] : Over S :=
  (underlyingFunctor p d).reprX

/-- The chosen Yoneda representation of `Pic⁰`. -/
noncomputable def representation [Functor.IsRepresentable (underlyingFunctor p d)] :
    Representation p d (scheme p d) :=
  (underlyingFunctor p d).representableBy

/-- The commutative group object on the represented `Pic⁰`. -/
@[instance_reducible]
noncomputable def commGrpObj [Functor.IsRepresentable (underlyingFunctor p d)] :
    CommGrpObj (scheme p d) :=
  commGrpObjOfRepresentation p d (scheme p d) (representation p d)

/-- The group-scheme structure on the represented `Pic⁰`. -/
@[instance_reducible]
noncomputable def grpObj [Functor.IsRepresentable (underlyingFunctor p d)] :
    GrpObj (scheme p d) := by
  letI := commGrpObj p d
  infer_instance

/-- The represented `Pic⁰` group object is commutative. -/
theorem isCommMonObj [Functor.IsRepresentable (underlyingFunctor p d)] :
    letI := grpObj p d
    IsCommMonObj (scheme p d) := by
  letI := commGrpObj p d
  infer_instance

end MazurTorsion.AlgebraicGeometry.Jacobian.PicardIdentityComponent
