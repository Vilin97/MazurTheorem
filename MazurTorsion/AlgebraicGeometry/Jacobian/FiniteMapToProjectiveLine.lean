/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.SmoothCurveReduced
import MazurTorsion.Upstream.ProperCurveCohomologyFinite

/-!
# A canonical finite map from a proper smooth curve to `P¹`

The choices in this file are not mathematical structure on the curve.  They
select one codimension-one point, one uniformizer, and hence one nonconstant
rational function in order to expose a finite map to the projective line.
The symmetric-power construction is the named downstream consumer.
-/

universe u

open CategoryTheory

namespace MazurTorsion.AlgebraicGeometry.Jacobian.FiniteMapToProjectiveLine

open _root_.AlgebraicGeometry
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.SchemeWeilDivisor
open MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

variable (K : Type u) [Field K] (C : Over (Spec (.of K)))
variable [GeometricallyIrreducible C.hom] [IsProper C.hom]
variable [SmoothOfRelativeDimension 1 C.hom]

local instance : IsIntegral C.left :=
  SmoothCurveReduced.scheme_isIntegral_of_geometricallyIrreducible_of_smoothRelativeDimension_one
    K C.left C.hom

/-- A selected codimension-one point of the curve. -/
noncomputable def codimensionOnePoint : CodimensionOnePoint C.left :=
  Classical.choice (SmoothCurveReduced.nonempty_codimensionOnePoint K C.left C.hom)

/-- A selected finite morphism from the curve to the projective line. -/
noncomputable def hom : C.left ⟶ ProjectiveLine.scheme K :=
  rationalFunctionMorphism K C.left C.hom
    (nonGlobalRationalFunctionAt K C.left C.hom (codimensionOnePoint K C))

instance hom_isFinite : IsFinite (hom K C) :=
  rationalFunctionMorphismAt_isFinite K C.left C.hom (codimensionOnePoint K C)

omit [IsProper C.hom] in
/-- The selected finite morphism is a morphism over the ground field. -/
theorem hom_comp_structureMap :
    hom K C ≫ ProjectiveLine.structureMap K = C.hom := by
  exact rationalFunctionMorphism_comp_structureMap K C.left C.hom
    (nonGlobalRationalFunctionAt K C.left C.hom (codimensionOnePoint K C))

/-- The finite map packaged as an arrow in schemes over `Spec K`. -/
noncomputable def overHom :
    C ⟶ Over.mk (ProjectiveLine.structureMap K) :=
  Over.homMk (hom K C) (hom_comp_structureMap K C)

end MazurTorsion.AlgebraicGeometry.Jacobian.FiniteMapToProjectiveLine
