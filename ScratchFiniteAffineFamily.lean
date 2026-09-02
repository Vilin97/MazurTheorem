import Mathlib.Algebra.Algebra.Pi
import Mathlib.AlgebraicGeometry.Cover.Sigma
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.MultiplicativeCocycleDescent

open CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

namespace AlgebraicGeometry.CommGroupScheme.MultiplicativeCocycleDescent
namespace FiniteAffineFamily

open AffineCommGroupScheme
open CategoryTheory.PresheafOfGroups
open AlgebraicGeometry.Scheme

private local instance flatIsZariskiLocalAtSource :
    IsZariskiLocalAtSource (@Flat) :=
  HasRingHomProperty.instIsZariskiLocalAtSource
    (P := @Flat) (Q := RingHom.Flat)

private local instance locallyOfFinitePresentationIsZariskiLocalAtSource :
    IsZariskiLocalAtSource (@LocallyOfFinitePresentation) :=
  HasRingHomProperty.instIsZariskiLocalAtSource
    (P := @LocallyOfFinitePresentation) (Q := RingHom.FinitePresentation)

private local instance fppfPropertyIsZariskiLocalAtSource :
    IsZariskiLocalAtSource (@Flat ⊓ @LocallyOfFinitePresentation) :=
  MorphismProperty.IsLocalAtSource.inf _ _

private local instance fppfPrecoverageRespectsIso :
    Precoverage.RespectsIso fppfPrecoverage :=
  Precoverage.instRespectsIsoOfIsStableUnderBaseChange

private local instance fppfPropertyPrecoverageRespectsIso :
    Precoverage.RespectsIso
      (precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) := by
  change Precoverage.RespectsIso fppfPrecoverage
  exact fppfPrecoverageRespectsIso

variable {A : Type u} [CommRing A]
variable {I : Type u} [Finite I]
variable (B : I → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]

/-- The product algebra associated to a finite affine family. -/
abbrev ProductAlgebra := ∀ i, B i

/-- The family of affine test objects associated to `B`. -/
abbrev componentFamily : I → Over (Spec (.of A)) :=
  fun i ↦ testObject (R := A) (B i)

/-- The singleton affine test family associated to the product algebra. -/
abbrev productFamily : Unit → Over (Spec (.of A)) :=
  fun _ ↦ testObject (R := A) (ProductAlgebra B)

/-- Each component maps canonically to the spectrum of the product algebra. Thus the original
family refines the singleton product family, in this direction only. -/
noncomputable def componentToProductRefinement :
    FamilyRefinement (componentFamily (A := A) B) (productFamily (A := A) B) where
  index _ := ()
  map i := testObjectMap (Pi.evalAlgHom A B i)

/-- Pull a represented multiplicative cocycle on the singleton product family back to the
original finite affine family. -/
noncomputable def pullbackRepresentedCocycle
    (c : RepresentedMultiplicativeOneCocycle (A := A) (B := ProductAlgebra B)) :
    OneCocycle (pointPresheaf (multiplicativeScheme A)) (componentFamily B) :=
  (componentToProductRefinement (A := A) B).pullbackOneCocycle c

omit [Finite I] in
@[simp]
theorem pullbackRepresentedCocycle_ev
    (c : RepresentedMultiplicativeOneCocycle (A := A) (B := ProductAlgebra B))
    (i j : I) {T : Over (Spec (.of A))}
    (a : T ⟶ componentFamily (A := A) B i)
    (b : T ⟶ componentFamily (A := A) B j) :
    (pullbackRepresentedCocycle (A := A) B c).ev i j a b =
      c.ev () () (a ≫ testObjectMap (Pi.evalAlgHom A B i))
        (b ≫ testObjectMap (Pi.evalAlgHom A B j)) :=
  rfl

/-- The pre-zero-hypercover underlying the canonical affine family. -/
def componentPrecover : PreZeroHypercover.{u} (Spec (.of A)) where
  I₀ := I
  X i := Spec (.of (B i))
  f i := Spec.map (CommRingCat.ofHom (algebraMap A (B i)))

/-- Promote a covering finite affine family to an fppf cover. -/
def componentCover
    (hB : (componentPrecover B).presieve₀ ∈ fppfPrecoverage (Spec (.of A))) :
    Scheme.Cover.{u} fppfPrecoverage (Spec (.of A)) where
  __ := componentPrecover B
  mem₀ := hB

/-- The pre-zero-hypercover whose sole member is the spectrum of the product algebra. -/
def productPrecover : PreZeroHypercover.{u} (Spec (.of A)) where
  I₀ := PUnit.{u + 1}
  X _ := Spec (.of (ProductAlgebra B))
  f _ := Spec.map (CommRingCat.ofHom (algebraMap A (ProductAlgebra B)))

omit [Finite I] in
private theorem sigmaSpec_comp_productStructureMap :
    sigmaSpec (fun i ↦ CommRingCat.of (B i)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (ProductAlgebra B))) =
      Sigma.desc (fun i ↦
        Spec.map (CommRingCat.ofHom (algebraMap A (B i)))) := by
  apply Sigma.hom_ext
  intro i
  rw [← Category.assoc, ι_sigmaSpec, Sigma.ι_desc]
  rw [← Spec.map_comp, Spec.map_inj]
  ext a
  rfl

private noncomputable def productSigmaIso :
    (∐ fun i ↦ Spec (.of (B i))) ≅ Spec (.of (ProductAlgebra B)) :=
  asIso (sigmaSpec (fun i ↦ CommRingCat.of (B i)))

/-- The collapsed disjoint-union cover is canonically isomorphic to the singleton spectrum of
the finite product algebra. -/
noncomputable def sigmaProductPrecoverIso
    (hB : (componentPrecover B).presieve₀ ∈ fppfPrecoverage (Spec (.of A))) :
    (componentCover B hB).sigma.toPreZeroHypercover ≅ productPrecover B :=
  PreZeroHypercover.isoMk (Equiv.refl PUnit.{u + 1})
    (fun _ ↦ productSigmaIso B)
    (fun _ ↦ sigmaSpec_comp_productStructureMap B)

/-- The singleton spectrum of the product algebra is an fppf cover whenever the original
finite affine family is an fppf cover. -/
noncomputable def productCover
    (hB : (componentPrecover B).presieve₀ ∈ fppfPrecoverage (Spec (.of A))) :
    Scheme.Cover.{u} fppfPrecoverage (Spec (.of A)) where
  __ := productPrecover B
  mem₀ := (componentCover B hB).sigma.presieve₀_mem_of_iso
    (sigmaProductPrecoverIso B hB)

/-- The original finite affine fppf cover refines the singleton product cover. -/
noncomputable def toProductCover
    (hB : (componentPrecover B).presieve₀ ∈ fppfPrecoverage (Spec (.of A))) :
    (componentCover B hB).Hom (productCover B hB) :=
  PreZeroHypercover.Hom.comp
    (Scheme.Cover.toSigma (componentCover B hB))
    (sigmaProductPrecoverIso B hB).hom

@[simp]
theorem toProductCover_h₀
    (hB : (componentPrecover B).presieve₀ ∈ fppfPrecoverage (Spec (.of A)))
    (i : I) :
    (toProductCover B hB).h₀ i =
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom B i)) := by
  change Sigma.ι (fun i ↦ Spec (.of (B i))) i ≫
      sigmaSpec (fun i ↦ CommRingCat.of (B i)) = _
  exact ι_sigmaSpec (fun i ↦ CommRingCat.of (B i)) i

/-- The product cover's `PUnit`-indexed over-family refines the `Unit`-indexed singleton family
used by the represented-cocycle evaluator. The component map is the identity. -/
def productCoverToRepresentedSingleton
    (hB : (componentPrecover B).presieve₀ ∈ fppfPrecoverage (Spec (.of A))) :
    FamilyRefinement (productCover B hB).overFamily
      (productFamily (A := A) B) where
  index _ := ()
  map _ := 𝟙 _

@[simp]
theorem coverRefinementToRepresentedSingleton_map
    (hB : (componentPrecover B).presieve₀ ∈ fppfPrecoverage (Spec (.of A)))
    (i : I) :
    ((productCoverToRepresentedSingleton B hB).comp
      (Scheme.Cover.Hom.toOverFamilyRefinement (toProductCover B hB))).map i =
        (componentToProductRefinement (A := A) B).map i := by
  apply Over.OverMorphism.ext
  change (toProductCover B hB).h₀ i ≫ 𝟙 _ =
    Spec.map (CommRingCat.ofHom (Pi.evalAlgHom A B i).toRingHom)
  rw [Category.comp_id, toProductCover_h₀]
  rfl

/-- A represented cocycle on `Spec (∏ i, B i)` regarded as a cocycle on the actual singleton
fppf product cover. -/
noncomputable def productCoverCocycle
    (hB : (componentPrecover B).presieve₀ ∈ fppfPrecoverage (Spec (.of A)))
    (c : RepresentedMultiplicativeOneCocycle (A := A) (B := ProductAlgebra B)) :
    OneCocycle (pointPresheaf (multiplicativeScheme A))
      (productCover B hB).overFamily :=
  (productCoverToRepresentedSingleton B hB).pullbackOneCocycle c

/-- The cocycle on the original component cover obtained from the singleton product cover. -/
noncomputable def componentCoverCocycle
    (hB : (componentPrecover B).presieve₀ ∈ fppfPrecoverage (Spec (.of A)))
    (c : RepresentedMultiplicativeOneCocycle (A := A) (B := ProductAlgebra B)) :
    OneCocycle (pointPresheaf (multiplicativeScheme A))
      (componentCover B hB).overFamily :=
  (Scheme.Cover.Hom.toOverFamilyRefinement (toProductCover B hB)).pullbackOneCocycle
    (productCoverCocycle B hB c)

@[simp]
theorem componentCoverCocycle_ev
    (hB : (componentPrecover B).presieve₀ ∈ fppfPrecoverage (Spec (.of A)))
    (c : RepresentedMultiplicativeOneCocycle (A := A) (B := ProductAlgebra B))
    (i j : I) {T : Over (Spec (.of A))}
    (a : T ⟶ (componentCover B hB).overFamily i)
    (b : T ⟶ (componentCover B hB).overFamily j) :
    (componentCoverCocycle B hB c).ev i j a b =
      c.ev () () (a ≫ testObjectMap (Pi.evalAlgHom A B i))
        (b ≫ testObjectMap (Pi.evalAlgHom A B j)) := by
  rw [componentCoverCocycle, productCoverCocycle,
    ← FamilyRefinement.pullbackOneCocycle_comp]
  change c.ev () ()
      (a ≫ ((productCoverToRepresentedSingleton B hB).comp
        (Scheme.Cover.Hom.toOverFamilyRefinement (toProductCover B hB))).map i)
      (b ≫ ((productCoverToRepresentedSingleton B hB).comp
        (Scheme.Cover.Hom.toOverFamilyRefinement (toProductCover B hB))).map j) = _
  rw [coverRefinementToRepresentedSingleton_map,
    coverRefinementToRepresentedSingleton_map]
  rfl

/-- Pulling a represented singleton-product cocycle along the genuine cover refinement defines
the same global fppf `H¹` class. This is the global cohomology consumer of the finite-product
comparison. -/
theorem productCoverCocycle_globalClass_pullback
    (hB : (componentPrecover B).presieve₀ ∈ fppfPrecoverage (Spec (.of A)))
    (c : RepresentedMultiplicativeOneCocycle (A := A) (B := ProductAlgebra B)) :
    Scheme.FppfHOne.mk (componentCover B hB)
        (componentCoverCocycle B hB c).class =
      Scheme.FppfHOne.mk (productCover B hB)
        (productCoverCocycle B hB c).class :=
  Scheme.FppfHOne.class_pullback
    (productCover B hB) (componentCover B hB) (toProductCover B hB)
    (productCoverCocycle B hB c).class

end FiniteAffineFamily
end AlgebraicGeometry.CommGroupScheme.MultiplicativeCocycleDescent
