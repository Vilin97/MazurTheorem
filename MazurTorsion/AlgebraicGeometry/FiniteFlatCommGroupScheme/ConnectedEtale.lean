/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Algebra.Exact.Basic
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.Affine

/-!
# Connected--étale sequences of finite-flat commutative group schemes

This is the first downstream consumer of the finite-flat commutative group-scheme API.  It records
an already-constructed connected--étale sequence and asks for exactness at the middle term on
geometric points.  Construction of the identity component and the maximal finite-étale quotient
is intentionally not smuggled into this datum; those are separate existence and descent problems.

No quotient machinery is introduced here.  The current consumer only needs a supplied quotient
object and projection, pointwise kernel exactness, base change of the underlying finite-flat
objects, and an isomorphism from the quotient to a constructed affine Hopf realization.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonObj

namespace AlgebraicGeometry
namespace FiniteFlatCommGroupScheme

universe u

variable {S T : Scheme.{u}}

/-- Data and verified properties of a connected--étale sequence
`G⁰ ⟶ G ⟶ Gᵉᵗ` over `S`.

Exactness is asserted only at the middle term: an `X`-point of `G` maps to the identity in `Gᵉᵗ`
exactly when it comes from an `X`-point of `G⁰`.  Surjectivity on raw `X`-points is not required;
quotient maps are generally only locally surjective in the relevant flat topology. -/
structure ConnectedEtaleDatum (G : FiniteFlatCommGroupScheme S) where
  /-- The geometrically connected finite-flat subgroup. -/
  connectedPart : FiniteFlatCommGroupScheme S
  /-- The finite-étale quotient. -/
  etaleQuotient : FiniteFlatCommGroupScheme S
  /-- Inclusion of the connected part. -/
  inclusion : connectedPart ⟶ G
  /-- Projection to the étale quotient. -/
  project : G ⟶ etaleQuotient
  /-- Geometric connectedness of the connected term. -/
  geometricallyConnected : GeometricallyConnected connectedPart.structureMap
  /-- Étaleness of the quotient term. -/
  etale : Etale etaleQuotient.structureMap
  /-- Exactness at `G` on points of every test scheme over `S`. -/
  exactOnPoints : ∀ X : Over S,
    Function.MulExact (mapPoint inclusion X) (mapPoint project X)

namespace ConnectedEtaleDatum

variable {G : FiniteFlatCommGroupScheme S} (D : G.ConnectedEtaleDatum)

/-- A point coming from the connected part maps to the identity in the étale quotient. -/
theorem project_include_point_eq_one (X : Over S) (x : D.connectedPart.Point X) :
    mapPoint D.project X (mapPoint D.inclusion X x) = 1 :=
  (D.exactOnPoints X).apply_apply_eq_one x

/-- Pointwise kernel characterization supplied by a connected--étale sequence. -/
theorem project_point_eq_one_iff (X : Over S) (x : G.Point X) :
    AlgebraicGeometry.FiniteFlatCommGroupScheme.mapPoint D.project X x = 1 ↔
      x ∈ Set.range (mapPoint D.inclusion X) :=
  D.exactOnPoints X x

/-- Base change of the connected term has the expected pointwise order.  This consumes the BASIC
base-change and rank API without asserting that the entire connected--étale sequence has already
been proved stable under base change. -/
theorem connectedPart_orderAt_baseChange (f : T ⟶ S) (t : T) :
    ((baseChange f).obj D.connectedPart).orderAt t = D.connectedPart.orderAt (f t) :=
  orderAt_baseChange f D.connectedPart t

/-- The geometric connectedness certificate on the connected term survives base change. -/
theorem connectedPart_geometricallyConnected_baseChange (f : T ⟶ S) :
    GeometricallyConnected ((baseChange f).obj D.connectedPart).structureMap := by
  letI : GeometricallyConnected D.connectedPart.structureMap := D.geometricallyConnected
  change GeometricallyConnected (pullback.snd D.connectedPart.structureMap f)
  infer_instance

/-- Base change of the étale term has the expected pointwise order. -/
theorem etaleQuotient_orderAt_baseChange (f : T ⟶ S) (t : T) :
    ((baseChange f).obj D.etaleQuotient).orderAt t = D.etaleQuotient.orderAt (f t) :=
  orderAt_baseChange f D.etaleQuotient t

/-- The étaleness certificate on the quotient term survives base change. -/
theorem etaleQuotient_etale_baseChange (f : T ⟶ S) :
    Etale ((baseChange f).obj D.etaleQuotient).structureMap := by
  letI : Etale D.etaleQuotient.structureMap := D.etale
  change Etale (pullback.snd D.etaleQuotient.structureMap f)
  infer_instance

variable {R : Type u} [CommRing R]
variable {G : FiniteFlatCommGroupScheme (Spec (.of R))}

/-- Compatibility bridge for pre-existing geometric objects carrying an explicit finite-free
Hopf presentation: every affine test point is killed by its geometric order. -/
theorem etaleQuotient_point_pow_orderAt_eq_one
    (D : G.ConnectedEtaleDatum)
    (P : D.etaleQuotient.AffineFiniteFreePresentation)
    (B : Type u) [CommRing B] [Algebra R B]
    (x : D.etaleQuotient.Point (AffineCommGroupScheme.testObject (R := R) B))
    (s : Spec (.of R)) :
    x ^ D.etaleQuotient.orderAt s = 1 :=
  P.point_pow_orderAt_eq_one B x s

/-- Compatibility consumer for an explicitly supplied Hopf presentation: combining middle
exactness with its geometric order theorem puts the quotient order-power in the connected part. -/
theorem point_pow_orderAt_mem_connectedPart_range
    (D : G.ConnectedEtaleDatum)
    (P : D.etaleQuotient.AffineFiniteFreePresentation)
    (B : Type u) [CommRing B] [Algebra R B]
    (x : G.Point (AffineCommGroupScheme.testObject (R := R) B))
    (s : Spec (.of R)) :
    x ^ D.etaleQuotient.orderAt s ∈ Set.range
      (mapPoint D.inclusion (AffineCommGroupScheme.testObject (R := R) B)) := by
  rw [← D.project_point_eq_one_iff]
  rw [map_pow]
  exact D.etaleQuotient_point_pow_orderAt_eq_one P B
    (mapPoint D.project (AffineCommGroupScheme.testObject (R := R) B) x) s

/-- A genuine realization consumer: if the étale quotient is isomorphic to the group scheme
constructed from finite-free Hopf coordinates, its geometric order-power lands in the connected
part.  No independently supplied point-group or rank compatibility data is used. -/
theorem point_pow_orderAt_mem_connectedPart_range_of_realizedEtaleQuotient
    (D : G.ConnectedEtaleDatum)
    (A : AffineFiniteFreeCommGroupScheme R)
    (e : D.etaleQuotient ≅ A.realize)
    (B : Type u) [CommRing B] [Algebra R B]
    (x : G.Point (AffineCommGroupScheme.testObject (R := R) B))
    (s : Spec (.of R)) :
    x ^ D.etaleQuotient.orderAt s ∈ Set.range
      (mapPoint D.inclusion (AffineCommGroupScheme.testObject (R := R) B)) := by
  rw [← D.project_point_eq_one_iff, map_pow]
  let X := AffineCommGroupScheme.testObject (R := R) B
  let y := mapPoint D.project X x
  apply (pointMulEquivOfIso e X).injective
  rw [map_pow, map_one, congrFun (orderAt_eq_of_iso e) s]
  simpa [y, X] using
    AlgebraicGeometry.AffineFiniteFreeCommGroupScheme.realize_point_pow_orderAt_eq_one
      A B (pointMulEquivOfIso e X y) s

/-- The finite-locally-free descent theorem is consumed geometrically here: a constant order on
a realized finite-flat étale quotient kills the quotient image of every middle point, so that
power lies in the connected part. -/
theorem point_pow_mem_connectedPart_range_of_realizedConstantOrderEtaleQuotient
    (D : G.ConnectedEtaleDatum)
    (A : AffineFiniteFlatCommGroupScheme R)
    (e : D.etaleQuotient ≅ A.realize)
    (n : ℕ) (hA : A.realize.HasConstantOrder n)
    (B : Type u) [CommRing B] [Algebra R B]
    (x : G.Point (AffineCommGroupScheme.testObject (R := R) B)) :
    x ^ n ∈ Set.range
      (mapPoint D.inclusion (AffineCommGroupScheme.testObject (R := R) B)) := by
  rw [← D.project_point_eq_one_iff, map_pow]
  let X := AffineCommGroupScheme.testObject (R := R) B
  let y := mapPoint D.project X x
  apply (pointMulEquivOfIso e X).injective
  rw [map_pow, map_one]
  simpa [y, X] using
    AlgebraicGeometry.AffineFiniteFlatCommGroupScheme.realize_point_pow_eq_one_of_hasConstantOrder
      A n hA B (pointMulEquivOfIso e X y)

/-- Scalar-extension consumer for the full geometric base-change API: a quotient identified with the
geometric pullback of a realized group is transported across `realizeBaseChangeIso`; constant
order then makes the corresponding power land in the connected part. -/
theorem point_pow_mem_connectedPart_range_of_baseChangedRealizedEtaleQuotient
    {K : Type u} [CommRing K] [Algebra R K]
    {Gₖ : FiniteFlatCommGroupScheme (Spec (.of K))}
    (D : Gₖ.ConnectedEtaleDatum)
    (A : AffineFiniteFlatCommGroupScheme R)
    (n : ℕ) (hA : A.realize.HasConstantOrder n)
    (e : D.etaleQuotient ≅
      (FiniteFlatCommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj A.realize)
    (B : Type u) [CommRing B] [Algebra K B]
    (x : Gₖ.Point (AffineCommGroupScheme.testObject (R := K) B)) :
    x ^ n ∈ Set.range
      (mapPoint D.inclusion (AffineCommGroupScheme.testObject (R := K) B)) :=
  D.point_pow_mem_connectedPart_range_of_realizedConstantOrderEtaleQuotient
    (A.baseChange (K := K))
      (e ≪≫ AlgebraicGeometry.AffineFiniteFlatCommGroupScheme.realizeBaseChangeIso A) n
      (AlgebraicGeometry.AffineFiniteFlatCommGroupScheme.baseChange_realize_hasConstantOrder
        A n hA) B x

/-- When the scheme-theoretic kernel of the connected--étale projection is known finite and
flat, the BASIC kernel construction supplies its certified group-scheme presentation. -/
theorem project_kernelPresentation_exists
    (D : G.ConnectedEtaleDatum)
    [IsFinite (kernelStructureMap D.project)] [Flat (kernelStructureMap D.project)] :
    Nonempty (KernelPresentation D.project) :=
  AlgebraicGeometry.FiniteFlatCommGroupScheme.kernelPresentation_exists_of_finite_flat D.project

end ConnectedEtaleDatum

end FiniteFlatCommGroupScheme
end AlgebraicGeometry
