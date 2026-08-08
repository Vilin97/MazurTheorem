/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.Spectrum.Prime.Topology
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.AdmissibleFiltration
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.ConnectedEtale

/-!
# Connected--etale structure on admissible factors in the closed characteristic

Over a field of characteristic `p`, the two actual order-`p` group schemes occurring in an
admissible filtration have the expected connected--etale structure.  The constant group scheme
is finite etale.  The group scheme `mu_p` is geometrically connected: after every field extension
its group-algebra coordinates have no nontrivial idempotents.

The first construction applies these geometric results to an `AdmissibleSimpleFactor` over
`ZMod p`.  The final construction gives the actual middle connected--etale sequence of an fppf
extension with multiplicative kernel and constant quotient.  Both construct their maps and prove
pointwise exactness rather than asking the caller for a connected--etale certificate.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry
namespace FiniteFlatCommGroupScheme

universe u

/-- An isomorphism of finite-flat group schemes induces an isomorphism of their underlying
schemes. -/
def schemeIsoOfFiniteFlatIso {S : Scheme.{u}}
    {G H : FiniteFlatCommGroupScheme S} (e : G ≅ H) :
    G.scheme ≅ H.scheme where
  hom := hom e.hom
  inv := hom e.inv
  hom_inv_id := by rw [← hom_comp, e.hom_inv_id, hom_id]
  inv_hom_id := by rw [← hom_comp, e.inv_hom_id, hom_id]

/-- Etaleness of the structure map is invariant under an isomorphism of finite-flat group
schemes. -/
theorem etale_structureMap_of_iso {S : Scheme.{u}}
    {G H : FiniteFlatCommGroupScheme S} (e : G ≅ H)
    (hH : Etale H.structureMap) : Etale G.structureMap := by
  letI : Etale H.structureMap := hH
  rw [← hom_comp_structureMap e.hom]
  change Etale ((schemeIsoOfFiniteFlatIso e).hom ≫ H.structureMap)
  infer_instance

/-- Geometric connectedness of the structure map is invariant under an isomorphism of
finite-flat group schemes. -/
theorem geometricallyConnected_structureMap_of_iso {S : Scheme.{u}}
    {G H : FiniteFlatCommGroupScheme S} (e : G ≅ H)
    (hH : GeometricallyConnected H.structureMap) :
    GeometricallyConnected G.structureMap := by
  refine ⟨?_⟩
  intro K _ y Z fst snd h
  apply hH.geometrically_connectedSpace y
    (fst ≫ (schemeIsoOfFiniteFlatIso e).hom) snd
  exact h.of_iso (Iso.refl _) (schemeIsoOfFiniteFlatIso e) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (hom_comp_structureMap e.hom).symm (by simp)

/-- Every represented constant finite group scheme is etale over its base. -/
theorem constantScheme_etale (R : Type u) [CommRing R]
    (A : Type u) [CommGroup A] [Fintype A] :
    Etale (constantScheme R A).structureMap := by
  change Etale
    (Spec.map (CommRingCat.ofHom
      (algebraMap R (ConstantCoordinates R A))))
  rw [HasRingHomProperty.Spec_iff (P := @Etale)]
  change Algebra.Etale R (ConstantCoordinates R A)
  letI : Algebra.Etale R (A → R) := inferInstance
  exact Algebra.Etale.of_equiv (ULift.algEquiv (R := R)).symm

/-- The constant scheme on the one-element cyclic group is the terminal finite-flat group used
in the explicit connected--etale sequences below. -/
abbrev trivialConstantScheme (R : Type) [CommRing R] :
    FiniteFlatCommGroupScheme (Spec (.of R)) :=
  constantScheme R (Multiplicative (ZMod 1))

/-- Evaluation at the unique index identifies the coordinates of a one-point constant scheme
with the base ring. -/
def trivialConstantCoordinatesAlgEquiv (R : Type) [CommRing R] :
    ConstantCoordinates R (Multiplicative (ZMod 1)) ≃ₐ[R] R :=
  (ULift.algEquiv (R := R)).trans
    { toFun := fun f ↦ f 1
      invFun := fun r _ ↦ r
      left_inv := fun f ↦ by
        funext i
        rw [Subsingleton.elim i 1]
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl }

/-- Over a field, the one-point constant scheme is connected. -/
theorem connectedSpace_trivialConstantScheme (K : Type) [Field K] :
    ConnectedSpace (trivialConstantScheme K).scheme := by
  let e : (trivialConstantScheme K).scheme ≅ Spec (.of K) :=
    (Scheme.Spec.mapIso
      (trivialConstantCoordinatesAlgEquiv K).toRingEquiv.toCommRingCatIso.op).symm
  rw [e.hom.homeomorph.connectedSpace_iff]
  infer_instance

/-- The one-point constant group over `ZMod p` is geometrically connected. -/
theorem trivialConstantScheme_geometricallyConnected {p : ℕ} [NeZero p] :
    GeometricallyConnected (trivialConstantScheme (ZMod p)).structureMap := by
  refine ⟨(geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms).2 ?_⟩
  intro K _ _
  let e := constantBaseChangeIso
    (R := ZMod p) (K := K) (Multiplicative (ZMod 1))
  dsimp only [trivialConstantScheme]
  change ConnectedSpace
    ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) K)))).obj
      (trivialConstantScheme (ZMod p))).scheme
  rw [(schemeIsoOfFiniteFlatIso e).hom.homeomorph.connectedSpace_iff]
  exact connectedSpace_trivialConstantScheme K

/-- The one-point constant group is etale. -/
theorem trivialConstantScheme_etale (R : Type) [CommRing R] :
    Etale (trivialConstantScheme R).structureMap :=
  constantScheme_etale R (Multiplicative (ZMod 1))

/-- The zero homomorphism sends every represented point to the identity. -/
@[simp]
theorem mapPoint_zeroHom_eq_one {S : Scheme.{u}}
    (G H : FiniteFlatCommGroupScheme S) (X : Over S) (x : G.Point X) :
    mapPoint (zeroHom G H) X x = 1 := by
  apply Over.OverMorphism.ext
  change x.left ≫ hom (zeroHom G H) = (1 : H.Point X).left
  rw [hom_zeroHom, ← Category.assoc, x.w]
  rfl

namespace MuClosedFiber

variable {p : ℕ} [NeZero p]

/-- The augmentation of the group algebra underlying `mu_p`. -/
def augmentation (K : Type u) [CommRing K] :
    MonoidAlgebra K (Multiplicative (ZMod p)) →ₐ[K] K :=
  MonoidAlgebra.lift K K (Multiplicative (ZMod p)) 1

omit [NeZero p] in
@[simp]
theorem augmentation_single (K : Type u) [CommRing K]
    (g : Multiplicative (ZMod p)) (a : K) :
    augmentation (p := p) K (MonoidAlgebra.single g a) = a := by
  simp [augmentation]

/-- Every element of the cyclic group underlying `mu_p` has `p`th power one. -/
theorem group_pow_eq_one (g : Multiplicative (ZMod p)) : g ^ p = 1 := by
  simpa [Nat.card_congr Multiplicative.ofAdd, Nat.card_zmod] using
    (pow_card_eq_one' (x := g))

/-- In characteristic `p`, Frobenius on the group algebra factors through the augmentation. -/
theorem pow_eq_single_augmentation_pow
    (hp : p.Prime) (K : Type u) [Field K] [Algebra (ZMod p) K]
    (x : MonoidAlgebra K (Multiplicative (ZMod p))) :
    x ^ p = MonoidAlgebra.single 1 ((augmentation (p := p) K x) ^ p) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : CharP K p := charP_of_injective_algebraMap
    (algebraMap (ZMod p) K).injective p
  have halgebraMap : Function.Injective
      (algebraMap K (MonoidAlgebra K (Multiplicative (ZMod p)))) := by
    intro a b hab
    have hcoeff := congrArg
      (fun z : MonoidAlgebra K (Multiplicative (ZMod p)) ↦ z.coeff 1) hab
    simpa using hcoeff
  letI : CharP (MonoidAlgebra K (Multiplicative (ZMod p))) p :=
    charP_of_injective_algebraMap halgebraMap p
  have hx : x = ∑ g ∈ x.coeff.support,
      MonoidAlgebra.single g (x.coeff g) := by
    exact (MonoidAlgebra.sum_coeff_single x).symm
  rw [hx]
  simp only [map_sum, augmentation_single]
  rw [sum_pow_char, sum_pow_char]
  change _ = (MonoidAlgebra.singleAddHom
    (R := K) (M := Multiplicative (ZMod p)) 1)
      (∑ i ∈ x.coeff.support, x.coeff i ^ p)
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro g hg
  rw [MonoidAlgebra.single_pow, group_pow_eq_one]
  rfl

/-- The augmentation ideal of the characteristic-`p` group algebra consists of nilpotents. -/
theorem isNilpotent_of_augmentation_eq_zero
    (hp : p.Prime) (K : Type u) [Field K] [Algebra (ZMod p) K]
    {x : MonoidAlgebra K (Multiplicative (ZMod p))}
    (hx : augmentation (p := p) K x = 0) : IsNilpotent x := by
  refine ⟨p, ?_⟩
  simp [pow_eq_single_augmentation_pow hp K x, hx, zero_pow hp.ne_zero]

/-- The characteristic-`p` group algebra of the cyclic group of order `p` has no nontrivial
idempotents. -/
theorem idempotent_eq_zero_or_eq_one
    (hp : p.Prime) (K : Type u) [Field K] [Algebra (ZMod p) K]
    {e : MonoidAlgebra K (Multiplicative (ZMod p))}
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  by_cases hε : augmentation (p := p) K e = 0
  · exact Or.inl (he.eq_zero_of_isNilpotent
      (isNilpotent_of_augmentation_eq_zero hp K hε))
  · right
    have hεidem : IsIdempotentElem (augmentation (p := p) K e) :=
      he.map (augmentation (p := p) K)
    have hεone : augmentation (p := p) K e = 1 :=
      (IsIdempotentElem.iff_eq_one_of_isUnit
        (isUnit_iff_ne_zero.mpr hε)).mp hεidem
    have hsub : augmentation (p := p) K (1 - e) = 0 := by simp [hεone]
    have hone_sub : 1 - e = 0 :=
      he.one_sub.eq_zero_of_isNilpotent
        (isNilpotent_of_augmentation_eq_zero hp K hsub)
    exact (sub_eq_zero.mp hone_sub).symm

/-- The affine scheme underlying `mu_p` remains connected after every field extension of
`ZMod p`. -/
theorem connectedSpace_muScheme
    (hp : p.Prime) (K : Type) [Field K] [Algebra (ZMod p) K] :
    ConnectedSpace (muScheme K p).scheme := by
  change ConnectedSpace (PrimeSpectrum (MonoidAlgebra K (Multiplicative (ZMod p))))
  rw [connectedSpace_iff_clopen]
  constructor
  · infer_instance
  · intro s hs
    obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.mp hs
    rcases idempotent_eq_zero_or_eq_one hp K he with rfl | rfl
    · left
      simp
    · right
      simp

/-- The actual group scheme `mu_p` over `ZMod p` is geometrically connected. -/
theorem geometricallyConnected_muScheme (hp : p.Prime) :
    GeometricallyConnected (muScheme (ZMod p) p).structureMap := by
  refine ⟨(geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms).2 ?_⟩
  intro K _ _
  let e := muBaseChangeIso (R := ZMod p) (K := K) p
  change ConnectedSpace
    ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) K)))).obj
      (muScheme (ZMod p) p)).scheme
  rw [(schemeIsoOfFiniteFlatIso e).hom.homeomorph.connectedSpace_iff]
  exact connectedSpace_muScheme hp K

end MuClosedFiber

namespace AdmissibleSimpleFactor

variable {p : ℕ} [NeZero p]
variable {Q : FiniteFlatCommGroupScheme (Spec (.of (ZMod p)))}

/-- The actual connected--etale sequence of an admissible order-`p` factor on the closed
characteristic-`p` fibre.  The constant factor is entirely etale, while `mu_p` is entirely
connected. -/
def connectedEtaleDatumClosedFiber
    (F : AdmissibleSimpleFactor (ZMod p) p Q) (hp : p.Prime) :
    Q.ConnectedEtaleDatum := by
  cases F with
  | constant e =>
      exact
        { connectedPart := trivialConstantScheme (ZMod p)
          etaleQuotient := Q
          inclusion := zeroHom (trivialConstantScheme (ZMod p)) Q
          project := 𝟙 Q
          geometricallyConnected := trivialConstantScheme_geometricallyConnected
          etale := etale_structureMap_of_iso e
            (constantScheme_etale (ZMod p) (Multiplicative (ZMod p)))
          exactOnPoints := fun X x ↦ by
            constructor
            · intro hx
              refine ⟨1, ?_⟩
              rw [mapPoint_zeroHom_eq_one]
              simpa only [mapPoint_id, MonoidHom.id_apply] using hx.symm
            · rintro ⟨y, rfl⟩
              exact mapPoint_zeroHom_eq_one
                (trivialConstantScheme (ZMod p)) Q X y }
  | multiplicative e =>
      exact
        { connectedPart := Q
          etaleQuotient := trivialConstantScheme (ZMod p)
          inclusion := 𝟙 Q
          project := zeroHom Q (trivialConstantScheme (ZMod p))
          geometricallyConnected := geometricallyConnected_structureMap_of_iso e
            (MuClosedFiber.geometricallyConnected_muScheme hp)
          etale := trivialConstantScheme_etale (ZMod p)
          exactOnPoints := fun X x ↦ by
            constructor
            · intro _
              exact ⟨x, by simp⟩
            · intro _
              exact mapPoint_zeroHom_eq_one Q (trivialConstantScheme (ZMod p)) X x }

end AdmissibleSimpleFactor

namespace FppfQuotientPresentation

variable {p : ℕ} [NeZero p]
variable {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod p)))}

/-- An actual multiplicative-kernel, constant-quotient fppf extension over the closed
characteristic-`p` fibre is its connected--etale sequence.  The geometric properties come from
the concrete `mu_p` and constant models, while exactness is the scheme-theoretic kernel
exactness already carried by the quotient presentation. -/
def connectedEtaleDatumClosedFiberOfMuKernelConstantQuotient
    (D : FppfQuotientPresentation G) (hp : p.Prime)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme (ZMod p) p)
    (quotientIso : D.quotient ≅
      constantScheme (ZMod p) (Multiplicative (ZMod p))) :
    G.ConnectedEtaleDatum where
  connectedPart := D.kernelPresentation.kernel
  etaleQuotient := D.quotient
  inclusion := D.kernelPresentation.inclusion
  project := D.project
  geometricallyConnected := geometricallyConnected_structureMap_of_iso kernelIso
    (MuClosedFiber.geometricallyConnected_muScheme hp)
  etale := etale_structureMap_of_iso quotientIso
    (constantScheme_etale (ZMod p) (Multiplicative (ZMod p)))
  exactOnPoints := D.project_point_eq_one_iff

/-- The constant quotient exponent puts every `p`th power in the actual connected kernel of a
multiplicative--constant extension.  This is a pointwise connected--etale consequence, stronger
than the undifferentiated `p²` exponent bound. -/
theorem point_pow_mem_connectedPart_range_of_muKernel_constantQuotient
    (D : FppfQuotientPresentation G) (hp : p.Prime)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme (ZMod p) p)
    (quotientIso : D.quotient ≅
      constantScheme (ZMod p) (Multiplicative (ZMod p)))
    (B : Type) [CommRing B] [Algebra (ZMod p) B]
    (x : G.Point (AffineCommGroupScheme.testObject (R := ZMod p) B)) :
    x ^ p ∈ Set.range
      (mapPoint D.kernelPresentation.inclusion
        (AffineCommGroupScheme.testObject (R := ZMod p) B)) := by
  letI : Fact p.Prime := ⟨hp⟩
  let C := D.connectedEtaleDatumClosedFiberOfMuKernelConstantQuotient hp
    kernelIso quotientIso
  change x ^ p ∈ Set.range
    (mapPoint C.inclusion (AffineCommGroupScheme.testObject (R := ZMod p) B))
  apply (C.project_point_eq_one_iff _ _).mp
  change mapPoint D.project
    (AffineCommGroupScheme.testObject (R := ZMod p) B) (x ^ p) = 1
  rw [map_pow]
  exact (AdmissibleSimpleFactor.constant quotientIso).point_pow_eq_one B
    (mapPoint D.project (AffineCommGroupScheme.testObject (R := ZMod p) B) x)

/-- The connected--etale refinement recovers the full `p²` exponent law: the first `p`th
power lands in the connected `mu_p` kernel, and the second is killed there. -/
theorem point_pow_sq_eq_one_of_muKernel_constantQuotient
    (D : FppfQuotientPresentation G) (hp : p.Prime)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme (ZMod p) p)
    (quotientIso : D.quotient ≅
      constantScheme (ZMod p) (Multiplicative (ZMod p)))
    (B : Type) [CommRing B] [Algebra (ZMod p) B]
    (x : G.Point (AffineCommGroupScheme.testObject (R := ZMod p) B)) :
    x ^ (p * p) = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  let X := AffineCommGroupScheme.testObject (R := ZMod p) B
  obtain ⟨y, hy⟩ :=
    D.point_pow_mem_connectedPart_range_of_muKernel_constantQuotient hp
      kernelIso quotientIso B x
  have hkernel : y ^ p = 1 :=
    (AdmissibleSimpleFactor.multiplicative kernelIso).point_pow_eq_one B y
  calc
    x ^ (p * p) = (x ^ p) ^ p := pow_mul x p p
    _ = (mapPoint D.kernelPresentation.inclusion X y) ^ p := by rw [hy]
    _ = mapPoint D.kernelPresentation.inclusion X (y ^ p) := (map_pow _ _ _).symm
    _ = mapPoint D.kernelPresentation.inclusion X 1 := by rw [hkernel]
    _ = 1 := map_one _

/-- Base change of a multiplicative--constant quotient presentation to `ZMod p` has the actual
connected--etale sequence.  The named base-change isomorphisms identify both factors, so no
stability law for a caller-supplied connected--etale datum is assumed. -/
def connectedEtaleDatumClosedFiberOfMuKernelConstantQuotientBaseChange
    {R : Type} [CommRing R] [Algebra R (ZMod p)]
    {G : FiniteFlatCommGroupScheme (Spec (.of R))}
    (D : FppfQuotientPresentation G) (hp : p.Prime)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme R p)
    (quotientIso : D.quotient ≅
      constantScheme R (Multiplicative (ZMod p))) :
    ((baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap R (ZMod p))))).obj G).ConnectedEtaleDatum := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R (ZMod p)))
  let Dp := D.baseChangePresentation f
  exact Dp.connectedEtaleDatumClosedFiberOfMuKernelConstantQuotient hp
    ((baseChange f).mapIso kernelIso ≪≫ muBaseChangeIso (R := R) (K := ZMod p) p)
    ((baseChange f).mapIso quotientIso ≪≫
      constantBaseChangeIso (R := R) (K := ZMod p) (Multiplicative (ZMod p)))

/-- On the actual closed fibre of a multiplicative--constant quotient presentation, the `p`th
power of every affine point lies in the base-changed geometric kernel. -/
theorem baseChange_point_pow_mem_connectedPart_range_of_muKernel_constantQuotient
    {R : Type} [CommRing R] [Algebra R (ZMod p)]
    {G : FiniteFlatCommGroupScheme (Spec (.of R))}
    (D : FppfQuotientPresentation G) (hp : p.Prime)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme R p)
    (quotientIso : D.quotient ≅
      constantScheme R (Multiplicative (ZMod p)))
    (B : Type) [CommRing B] [Algebra (ZMod p) B]
    (x : ((baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap R (ZMod p))))).obj G).Point
        (AffineCommGroupScheme.testObject (R := ZMod p) B)) :
    x ^ p ∈ Set.range
      (mapPoint
        ((baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap R (ZMod p))))).map
            D.kernelPresentation.inclusion)
        (AffineCommGroupScheme.testObject (R := ZMod p) B)) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R (ZMod p)))
  let Dp := D.baseChangePresentation f
  exact Dp.point_pow_mem_connectedPart_range_of_muKernel_constantQuotient hp
    ((baseChange f).mapIso kernelIso ≪≫ muBaseChangeIso (R := R) (K := ZMod p) p)
    ((baseChange f).mapIso quotientIso ≪≫
      constantBaseChangeIso (R := R) (K := ZMod p) (Multiplicative (ZMod p))) B x

end FppfQuotientPresentation

end FiniteFlatCommGroupScheme
end AlgebraicGeometry
