/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import MazurTorsion.AlgebraicGeometry.Jacobian.PermutationPower

/-!
# The ordered incidence divisor on a relative power

Let `X ⟶ S` be separated and let `X^d` denote its `d`-fold relative
power.  Inside `X ×_S X^d`, the ordered incidence divisor is the union of
the `d` coordinate graphs

```text
{(x, (x₀, …, x_{d-1})) | x = xᵢ}.
```

This file constructs that union scheme-theoretically.  A coordinate graph is
the equalizer of the first projection and the corresponding coordinate of
the second projection.  Separatedness makes its inclusion a closed
immersion.  The product of the graph ideal sheaves defines their
scheme-theoretic union and has the expected union of supports.

The named downstream consumer is the descent step in `PicardRepresentability`:
the permutation-invariance of this ordered family will descend it along the
finite quotient `X^d ⟶ Sym^d_S(X)` to the universal effective divisor.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.UniversalEffectiveDivisor

open PermutationPower

variable (S : Scheme.{u}) (d : ℕ) (X : Over S)

/-- The ambient relative product `X ×_S X^d`. -/
noncomputable abbrev orderedAmbient : Over S :=
  X ⨯ power S (Fin d) X

/-- The first projection `X ×_S X^d ⟶ X`. -/
noncomputable abbrev pointProjection : orderedAmbient S d X ⟶ X :=
  Limits.prod.fst

/-- The `i`-th coordinate of the second projection
`X ×_S X^d ⟶ X^d ⟶ X`. -/
noncomputable def coordinateProjection (i : Fin d) :
    orderedAmbient S d X ⟶ X :=
  Limits.prod.snd ≫ Pi.π (fun _ : Fin d ↦ X) i

/-- The `i`-th coordinate graph, constructed as an equalizer in schemes over
`S`. -/
noncomputable abbrev coordinateGraph (i : Fin d) : Over S :=
  equalizer (pointProjection S d X) (coordinateProjection S d X i)

/-- The inclusion of the `i`-th coordinate graph into the ambient product. -/
noncomputable abbrev coordinateGraphι (i : Fin d) :
    coordinateGraph S d X i ⟶ orderedAmbient S d X :=
  equalizer.ι (pointProjection S d X) (coordinateProjection S d X i)

/-- A coordinate graph is a closed subscheme when `X ⟶ S` is separated. -/
instance coordinateGraphι_isClosedImmersion [IsSeparated X.hom] (i : Fin d) :
    IsClosedImmersion (coordinateGraphι S d X i).left := by
  infer_instance

/-- The ideal sheaf of the `i`-th coordinate graph in `X ×_S X^d`. -/
noncomputable def coordinateGraphIdeal [IsSeparated X.hom] (i : Fin d) :
    (orderedAmbient S d X).left.IdealSheafData :=
  (coordinateGraphι S d X i).left.ker

/-- The ideal sheaf of the ordered incidence family.  The product is the
scheme-theoretic union of the finitely many coordinate graph ideals. -/
noncomputable def orderedIncidenceIdeal [IsSeparated X.hom] :
    (orderedAmbient S d X).left.IdealSheafData :=
  Finset.univ.prod (coordinateGraphIdeal S d X)

/-- The ordered incidence closed subscheme of `X ×_S X^d`. -/
noncomputable def orderedIncidence [IsSeparated X.hom] : Scheme.{u} :=
  (orderedIncidenceIdeal S d X).subscheme

/-- The closed immersion of the ordered incidence family into
`X ×_S X^d`. -/
noncomputable def orderedIncidenceι [IsSeparated X.hom] :
    orderedIncidence S d X ⟶ (orderedAmbient S d X).left :=
  (orderedIncidenceIdeal S d X).subschemeι

instance orderedIncidenceι_isClosedImmersion [IsSeparated X.hom] :
    IsClosedImmersion (orderedIncidenceι S d X) := by
  change IsClosedImmersion
    ((orderedIncidenceIdeal S d X).subschemeι)
  infer_instance

/-- The support of the ordered incidence ideal is the union of the supports
of the coordinate graphs. -/
theorem orderedIncidenceIdeal_support [IsSeparated X.hom] :
    (orderedIncidenceIdeal S d X).support =
      ⨆ i : Fin d, (coordinateGraphIdeal S d X i).support := by
  classical
  have h (s : Finset (Fin d)) :
      (s.prod (coordinateGraphIdeal S d X)).support =
        s.sup (fun i ↦ (coordinateGraphIdeal S d X i).support) := by
    induction s using Finset.induction_on with
    | empty =>
        exact Scheme.IdealSheafData.support_top
    | @insert i s hi ih =>
        rw [Finset.prod_insert hi, Scheme.IdealSheafData.support_mul,
          Finset.sup_insert, ih]
  rw [orderedIncidenceIdeal, h, Finset.sup_eq_iSup]
  simp

/-- In degree zero the ordered incidence family is empty. -/
theorem orderedIncidenceIdeal_zero [IsSeparated X.hom] :
    orderedIncidenceIdeal S 0 X = ⊤ := by
  classical
  simp [orderedIncidenceIdeal]

end MazurTorsion.AlgebraicGeometry.Jacobian.UniversalEffectiveDivisor
