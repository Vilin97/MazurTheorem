/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.PermutationPower
import MazurTorsion.AlgebraicGeometry.Jacobian.SplitFiniteBaseChange
import MazurTorsion.AlgebraicGeometry.Jacobian.SplitFiniteSymmetricQuotient

/-!
# Sheet tuples carried by points of a split finite power

A point of an ordered power of a split finite object chooses one sheet in
every coordinate.  We extract that tuple using the topological coproduct
equivalence, prove the exact reconstruction formula, and package its
permutation orbit as the corresponding split symmetric-power component.

The named downstream consumer is the exact coherent support point in
`FiniteSupportEtaleCoordinates`.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.SplitFinitePowerPoint

open SplitFiniteBaseChange
open SplitFiniteSymmetricQuotient

variable (S : Scheme.{u}) (d m : ℕ) (X : Over S)
variable (E : X ≅ splitFinite S m)
variable (p : (PermutationPower.power S (Fin d) X).left)

/-- The coproduct coordinate of the transported `i`-th point. -/
noncomputable def splitPowerPointSigmaCoordinate (i : Fin d) :
    Σ _ : ULift.{u} (Fin m), S :=
  (sigmaMk (fun _ : ULift.{u} (Fin m) ↦ S)).symm
    (E.hom.left
      ((Pi.π (fun _ : Fin d ↦ X) i).left p))

/-- The sheet label selected by the `i`-th coordinate. -/
noncomputable def splitPowerPointTuple : Fin d → Fin m :=
  fun i ↦ (splitPowerPointSigmaCoordinate S d m X E p i).1.down

/-- The point on the common base lying under the transported `i`-th
coordinate. -/
noncomputable def splitPowerPointBase (i : Fin d) : S :=
  (splitPowerPointSigmaCoordinate S d m X E p i).2

/-- Transporting a coordinate through the split presentation is exactly the
inclusion of its extracted sheet and base point. -/
theorem splitPowerPoint_decomposition (i : Fin d) :
    E.hom.left ((Pi.π (fun _ : Fin d ↦ X) i).left p) =
      Sigma.ι (fun _ : ULift.{u} (Fin m) ↦ S)
        (ULift.up (splitPowerPointTuple S d m X E p i))
        (splitPowerPointBase S d m X E p i) := by
  let z := E.hom.left ((Pi.π (fun _ : Fin d ↦ X) i).left p)
  let a := (sigmaMk (fun _ : ULift.{u} (Fin m) ↦ S)).symm z
  have ha : (ULift.up a.1.down : ULift.{u} (Fin m)) = a.1 := by
    cases a.1
    rfl
  change z = Sigma.ι (fun _ : ULift.{u} (Fin m) ↦ S)
    (ULift.up a.1.down) a.2
  rw [ha]
  rw [← sigmaMk_mk]
  exact (sigmaMk (fun _ : ULift.{u} (Fin m) ↦ S)).apply_symm_apply z |>.symm

/-- Every extracted sheet point lies over the original common base point of
the ordered relative power. -/
theorem splitPowerPointBase_eq_structureMap (i : Fin d) :
    splitPowerPointBase S d m X E p i =
      (PermutationPower.power S (Fin d) X).hom p := by
  have hE := E.hom.w
  have hEPoint := congrArg
    (fun f : X.left ⟶ S ↦ f ((Pi.π (fun _ : Fin d ↦ X) i).left p)) hE
  have hPi := (Pi.π (fun _ : Fin d ↦ X) i).w
  have hPiPoint := congrArg
    (fun f : (PermutationPower.power S (Fin d) X).left ⟶ S ↦ f p) hPi
  change (splitFinite S m).hom
      (E.hom.left ((Pi.π (fun _ : Fin d ↦ X) i).left p)) =
    X.hom ((Pi.π (fun _ : Fin d ↦ X) i).left p) at hEPoint
  rw [splitPowerPoint_decomposition S d m X E p i] at hEPoint
  have hSheetMap := Sigma.ι_desc (fun _ : ULift.{u} (Fin m) ↦ 𝟙 S)
    (ULift.up (splitPowerPointTuple S d m X E p i))
  have hSheetPoint := congrArg
    (fun f : S ⟶ S ↦ f (splitPowerPointBase S d m X E p i)) hSheetMap
  change (splitFinite S m).hom
      (Sigma.ι (fun _ : ULift.{u} (Fin m) ↦ S)
        (ULift.up (splitPowerPointTuple S d m X E p i))
        (splitPowerPointBase S d m X E p i)) =
    splitPowerPointBase S d m X E p i at hSheetPoint
  rw [hSheetPoint] at hEPoint
  change splitPowerPointBase S d m X E p i =
    X.hom ((Pi.π (fun _ : Fin d ↦ X) i).left p) at hEPoint
  change X.hom ((Pi.π (fun _ : Fin d ↦ X) i).left p) =
    (PermutationPower.power S (Fin d) X).hom p at hPiPoint
  exact hEPoint.trans hPiPoint

local instance : MulAction (Equiv.Perm (Fin d)) (Fin d → Fin m) :=
  tuplePermutationAction d (Fin m)

/-- The symmetric-power component selected by the exact ordered point. -/
noncomputable def splitPowerPointComponent : splitComponentIndex d m :=
  Quotient.mk'' (splitPowerPointTuple S d m X E p)

/-- The selected component is represented by the extracted sheet tuple. -/
theorem splitPowerPointComponent_out_orbitRel :
    MulAction.orbitRel (Equiv.Perm (Fin d)) (Fin d → Fin m)
      (splitPowerPointComponent S d m X E p).out
      (splitPowerPointTuple S d m X E p) :=
  Quotient.exact
    ((show Quotient.mk''
        (splitPowerPointComponent S d m X E p).out =
      Quotient.mk'' (splitPowerPointTuple S d m X E p) from
        (splitPowerPointComponent S d m X E p).out_eq.trans rfl))

end MazurTorsion.AlgebraicGeometry.Jacobian.SplitFinitePowerPoint
