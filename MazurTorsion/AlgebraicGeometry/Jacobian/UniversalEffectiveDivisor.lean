/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
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

/-- Scheme-theoretic transport of ideal sheaves along an isomorphism
preserves products.  The general direct-image operation on ideals need not
be multiplicative; invertibility of the morphism is essential here. -/
theorem idealSheaf_map_mul_of_isIso {Y Z : Scheme.{u}}
    (I J : Y.IdealSheafData) (f : Y ⟶ Z) [IsIso f] :
    (I * J).map f = I.map f * J.map f := by
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : Z.affineOpens ↦ U) (iSup_affineOpens_eq_top Z)
  intro U
  rw [Scheme.IdealSheafData.ideal_mul]
  simp only [Pi.mul_apply]
  rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom,
    Scheme.IdealSheafData.ideal_map_of_isAffineHom,
    Scheme.IdealSheafData.ideal_map_of_isAffineHom]
  rw [Scheme.IdealSheafData.ideal_mul]
  simp only [Pi.mul_apply]
  let e := (asIso (f.app U)).commRingCatIsoToRingEquiv
  have he (K L : Ideal Γ(Y, f ⁻¹ᵁ (U : Z.Opens))) :
      (K * L).comap e.toRingHom =
        K.comap e.toRingHom * L.comap e.toRingHom := by
    change (K * L).comap
        (e : Γ(Z, (U : Z.Opens)) →+* Γ(Y, f ⁻¹ᵁ (U : Z.Opens))) =
      K.comap (e : Γ(Z, (U : Z.Opens)) →+* Γ(Y, f ⁻¹ᵁ (U : Z.Opens))) *
        L.comap (e : Γ(Z, (U : Z.Opens)) →+* Γ(Y, f ⁻¹ᵁ (U : Z.Opens)))
    rw [Ideal.comap_coe e, Ideal.comap_coe e, Ideal.comap_coe e,
      ← Ideal.map_symm e, Ideal.map_mul, Ideal.map_symm, Ideal.map_symm]
  exact he _ _

/-- Transport of a finite product of ideal sheaves along an isomorphism is
the product of the transported ideals. -/
theorem idealSheaf_map_finsetProd_of_isIso {Y Z : Scheme.{u}}
    {I : Type*} (s : Finset I) (F : I → Y.IdealSheafData)
    (f : Y ⟶ Z) [IsIso f] :
    (s.prod F).map f = s.prod (fun i ↦ (F i).map f) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi,
        idealSheaf_map_mul_of_isIso, ih]

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

/-- A permutation of the ordered coordinates, acting trivially on the
distinguished point in `X ×_S X^d`. -/
noncomputable def orderedAmbientPermutationHom (g : Equiv.Perm (Fin d)) :
    orderedAmbient S d X ⟶ orderedAmbient S d X :=
  Limits.prod.map (𝟙 X) (permutationHom S (Fin d) X g)

@[reassoc]
theorem orderedAmbientPermutationHom_comp_pointProjection
    (g : Equiv.Perm (Fin d)) :
    orderedAmbientPermutationHom S d X g ≫ pointProjection S d X =
      pointProjection S d X := by
  exact Limits.prod.map_fst (𝟙 X) (permutationHom S (Fin d) X g)

@[reassoc]
theorem orderedAmbientPermutationHom_comp_coordinateProjection
    (g : Equiv.Perm (Fin d)) (i : Fin d) :
    orderedAmbientPermutationHom S d X g ≫ coordinateProjection S d X i =
      coordinateProjection S d X (g i) := by
  rw [coordinateProjection, ← Category.assoc, orderedAmbientPermutationHom,
    Limits.prod.map_snd, Category.assoc,
    permutationHom_comp_π]
  rfl

theorem orderedAmbientPermutationHom_one :
    orderedAmbientPermutationHom S d X 1 = 𝟙 (orderedAmbient S d X) := by
  rw [orderedAmbientPermutationHom, permutationHom_one]
  exact Limits.prod.map_id_id

theorem orderedAmbientPermutationHom_mul (g h : Equiv.Perm (Fin d)) :
    orderedAmbientPermutationHom S d X (g * h) =
      orderedAmbientPermutationHom S d X g ≫
        orderedAmbientPermutationHom S d X h := by
  apply Limits.prod.hom_ext
  · simp [orderedAmbientPermutationHom]
  · simp [orderedAmbientPermutationHom, permutationHom_mul]

/-- Permuting the ordered coordinates is an automorphism of the ambient
relative product. -/
noncomputable def orderedAmbientPermutationIso (g : Equiv.Perm (Fin d)) :
    orderedAmbient S d X ≅ orderedAmbient S d X where
  hom := orderedAmbientPermutationHom S d X g
  inv := orderedAmbientPermutationHom S d X g⁻¹
  hom_inv_id := by
    rw [← orderedAmbientPermutationHom_mul, mul_inv_cancel,
      orderedAmbientPermutationHom_one]
  inv_hom_id := by
    rw [← orderedAmbientPermutationHom_mul, inv_mul_cancel,
      orderedAmbientPermutationHom_one]

instance orderedAmbientPermutationHom_isIso (g : Equiv.Perm (Fin d)) :
    IsIso (orderedAmbientPermutationHom S d X g) := by
  change IsIso (orderedAmbientPermutationIso S d X g).hom
  infer_instance

instance orderedAmbientPermutationHom_left_isIso (g : Equiv.Perm (Fin d)) :
    IsIso (orderedAmbientPermutationHom S d X g).left := by
  change IsIso ((Over.forget S).map (orderedAmbientPermutationHom S d X g))
  infer_instance

/-- The `i`-th coordinate graph, constructed as an equalizer in schemes over
`S`. -/
noncomputable abbrev coordinateGraph (i : Fin d) : Over S :=
  equalizer (pointProjection S d X) (coordinateProjection S d X i)

/-- The inclusion of the `i`-th coordinate graph into the ambient product. -/
noncomputable abbrev coordinateGraphι (i : Fin d) :
    coordinateGraph S d X i ⟶ orderedAmbient S d X :=
  equalizer.ι (pointProjection S d X) (coordinateProjection S d X i)

/-- A permutation identifies the graph of coordinate `g i` with the graph
of coordinate `i`. -/
noncomputable def coordinateGraphReindexHom
    (g : Equiv.Perm (Fin d)) (i : Fin d) :
    coordinateGraph S d X (g i) ⟶ coordinateGraph S d X i :=
  equalizer.lift
    (coordinateGraphι S d X (g i) ≫ orderedAmbientPermutationHom S d X g)
    (by
      rw [Category.assoc, Category.assoc,
        orderedAmbientPermutationHom_comp_pointProjection,
        orderedAmbientPermutationHom_comp_coordinateProjection]
      exact equalizer.condition _ _)

@[reassoc (attr := simp)]
theorem coordinateGraphReindexHom_comp_ι
    (g : Equiv.Perm (Fin d)) (i : Fin d) :
    coordinateGraphReindexHom S d X g i ≫ coordinateGraphι S d X i =
      coordinateGraphι S d X (g i) ≫ orderedAmbientPermutationHom S d X g :=
  equalizer.lift_ι _ _

/-- The inverse coordinate-graph reindexing map. -/
noncomputable def coordinateGraphReindexInvHom
    (g : Equiv.Perm (Fin d)) (i : Fin d) :
    coordinateGraph S d X i ⟶ coordinateGraph S d X (g i) :=
  equalizer.lift
    (coordinateGraphι S d X i ≫ orderedAmbientPermutationHom S d X g⁻¹)
    (by
      rw [Category.assoc, Category.assoc,
        orderedAmbientPermutationHom_comp_pointProjection,
        orderedAmbientPermutationHom_comp_coordinateProjection]
      simpa using equalizer.condition
        (pointProjection S d X) (coordinateProjection S d X i))

@[reassoc (attr := simp)]
theorem coordinateGraphReindexInvHom_comp_ι
    (g : Equiv.Perm (Fin d)) (i : Fin d) :
    coordinateGraphReindexInvHom S d X g i ≫ coordinateGraphι S d X (g i) =
      coordinateGraphι S d X i ≫ orderedAmbientPermutationHom S d X g⁻¹ :=
  equalizer.lift_ι _ _

/-- Coordinate graphs are carried isomorphically to one another by a
permutation of the ordered power. -/
noncomputable def coordinateGraphReindexIso
    (g : Equiv.Perm (Fin d)) (i : Fin d) :
    coordinateGraph S d X (g i) ≅ coordinateGraph S d X i where
  hom := coordinateGraphReindexHom S d X g i
  inv := coordinateGraphReindexInvHom S d X g i
  hom_inv_id := by
    apply equalizer.hom_ext
    simp only [Category.assoc, coordinateGraphReindexInvHom_comp_ι,
      coordinateGraphReindexHom_comp_ι_assoc]
    rw [← orderedAmbientPermutationHom_mul, mul_inv_cancel,
      orderedAmbientPermutationHom_one, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply equalizer.hom_ext
    simp only [Category.assoc, coordinateGraphReindexHom_comp_ι,
      coordinateGraphReindexInvHom_comp_ι_assoc]
    rw [← orderedAmbientPermutationHom_mul, inv_mul_cancel,
      orderedAmbientPermutationHom_one, Category.comp_id, Category.id_comp]

instance coordinateGraphReindexHom_isIso
    (g : Equiv.Perm (Fin d)) (i : Fin d) :
    IsIso (coordinateGraphReindexHom S d X g i) := by
  change IsIso (coordinateGraphReindexIso S d X g i).hom
  infer_instance

instance coordinateGraphReindexHom_left_isIso
    (g : Equiv.Perm (Fin d)) (i : Fin d) :
    IsIso (coordinateGraphReindexHom S d X g i).left := by
  change IsIso ((Over.forget S).map (coordinateGraphReindexHom S d X g i))
  infer_instance

/-- A coordinate graph is a closed subscheme when `X ⟶ S` is separated. -/
instance coordinateGraphι_isClosedImmersion [IsSeparated X.hom] (i : Fin d) :
    IsClosedImmersion (coordinateGraphι S d X i).left := by
  infer_instance

/-- The ideal sheaf of the `i`-th coordinate graph in `X ×_S X^d`. -/
noncomputable def coordinateGraphIdeal [IsSeparated X.hom] (i : Fin d) :
    (orderedAmbient S d X).left.IdealSheafData :=
  (coordinateGraphι S d X i).left.ker

/-- A coordinate permutation transports the ideal of graph `g i` to the
ideal of graph `i`. -/
theorem coordinateGraphIdeal_map_permutation [IsSeparated X.hom]
    (g : Equiv.Perm (Fin d)) (i : Fin d) :
    (coordinateGraphIdeal S d X (g i)).map
        (orderedAmbientPermutationHom S d X g).left =
      coordinateGraphIdeal S d X i := by
  rw [coordinateGraphIdeal, coordinateGraphIdeal,
    Scheme.IdealSheafData.map_ker]
  have h := congrArg Over.Hom.left
    (coordinateGraphReindexHom_comp_ι S d X g i)
  change
    (coordinateGraphReindexHom S d X g i).left ≫
        (coordinateGraphι S d X i).left =
      (coordinateGraphι S d X (g i)).left ≫
        (orderedAmbientPermutationHom S d X g).left at h
  rw [← h]
  exact Scheme.Hom.ker_comp_of_isIso
    (coordinateGraphReindexHom S d X g i).left
    (coordinateGraphι S d X i).left

/-- The ideal sheaf of the ordered incidence family.  The product is the
scheme-theoretic union of the finitely many coordinate graph ideals. -/
noncomputable def orderedIncidenceIdeal [IsSeparated X.hom] :
    (orderedAmbient S d X).left.IdealSheafData :=
  Finset.univ.prod (coordinateGraphIdeal S d X)

/-- The ordered incidence ideal is invariant under every permutation of the
ordered coordinates. -/
theorem orderedIncidenceIdeal_map_permutation [IsSeparated X.hom]
    (g : Equiv.Perm (Fin d)) :
    (orderedIncidenceIdeal S d X).map
        (orderedAmbientPermutationHom S d X g).left =
      orderedIncidenceIdeal S d X := by
  classical
  rw [orderedIncidenceIdeal, idealSheaf_map_finsetProd_of_isIso]
  rw [← Equiv.prod_comp g (fun i ↦
    (coordinateGraphIdeal S d X i).map
      (orderedAmbientPermutationHom S d X g).left)]
  simp_rw [coordinateGraphIdeal_map_permutation]

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
