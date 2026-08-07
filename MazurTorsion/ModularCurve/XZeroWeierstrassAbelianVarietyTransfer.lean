/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassGeometricIntegrality

/-!
# Transporting a Weierstrass group law from an abelian variety

This file isolates the honest output expected from a pointed genus-one Abel--Jacobi theorem.
An isomorphism from the concrete projective cubic to an abelian variety transports the latter's
group-object structure.  If the canonical coordinate point map agrees, after that isomorphism,
with a genuine monoid homomorphism on rational points, its zero and addition laws follow by
cancelling the isomorphism.

The final definitions feed this transported structure directly to the checked finite-flat
`Gamma_0(N)` consumer.  The file also transports finiteness of rational points from a concrete
elliptic Weierstrass model across a supplied scheme isomorphism.  No rational-point bijection is
used to manufacture a scheme isomorphism: the scheme isomorphism and the multiplicative point
comparison are explicit hypotheses.
-/

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

/-- Finiteness of the affine rational points of an elliptic Weierstrass model transfers to the
rational points of any abelian variety whose underlying scheme is isomorphic to the concrete
projective cubic.

The proof uses the checked comparison between affine coordinates and scheme-valued points, then
postcomposes with the supplied scheme isomorphism.  In particular, this theorem does not construct
an isomorphism from point-set data. -/
theorem rationalPoint_finite_of_iso
    (W : WeierstrassCurve K) [W.IsElliptic]
    (A : TauCeti.AlgebraicGeometry.AbelianVariety K)
    (e : toOver W ≅ A.toOver)
    (hfinite : Finite W.toAffine.Point) :
    Finite (AbelianVarietyRationalPoint A) := by
  classical
  letI := hfinite
  apply Finite.of_surjective
    (fun P : W.toAffine.Point ↦
      projectivePointOverMorphism W
          ((WeierstrassCurve.Projective.Point.toAffineAddEquiv W).symm P) ≫
        e.hom)
  intro g
  obtain ⟨P, hP⟩ :=
    projectivePointOverMorphism_surjective W (g ≫ e.inv)
  refine ⟨WeierstrassCurve.Projective.Point.toAffineAddEquiv W P, ?_⟩
  simp only [AddEquiv.symm_apply_apply]
  rw [hP]
  simp

/-- Transport the group-object structure of an abelian variety across a genuine isomorphism of
schemes over the base field. -/
@[instance_reducible]
noncomputable def grpObjOfAbelianVarietyIso
    (W : WeierstrassCurve K)
    (A : TauCeti.AlgebraicGeometry.AbelianVariety K)
    (e : toOver W ≅ A.toOver) : GrpObj (toOver W) :=
  GrpObj.ofIso e.symm

/-- A pointed Abel--Jacobi isomorphism whose point map is multiplicative supplies the exact
zero/addition compatibility required by the concrete cubic's finite-flat consumer. -/
theorem canonicalPointGroupLawCompatibility_of_abelianVarietyIso
    (W : WeierstrassCurve K) [DecidableEq K] [W.IsElliptic]
    (A : TauCeti.AlgebraicGeometry.AbelianVariety K)
    (e : toOver W ≅ A.toOver)
    (φ : Multiplicative W.toProjective.Point →*
      AbelianVarietyRationalPoint A)
    (hφ : ∀ P,
      projectivePointOverMorphism W P ≫ e.hom =
        φ (Multiplicative.ofAdd P)) :
    letI := grpObjOfAbelianVarietyIso W A e
    CanonicalPointGroupLawCompatibility W := by
  letI := grpObjOfAbelianVarietyIso W A e
  haveI : IsMonHom e.symm.hom := CategoryTheory.isMonHom_ofIso e.symm
  haveI : IsMonHom e.hom := by
    simpa using (inferInstance : IsMonHom e.symm.inv)
  constructor
  · intro
    change projectivePointOverMorphism W 0 =
      (1 : AffineCommGroupScheme.testObject (R := K) K ⟶ toOver W)
    apply (cancel_mono e.hom).1
    rw [hφ]
    exact φ.map_one.trans <| by
      simpa only [CategoryTheory.IsMonHom.monoidHom_apply] using
        ((CategoryTheory.IsMonHom.monoidHom e.hom
          (AffineCommGroupScheme.testObject (R := K) K)).map_one).symm
  · intro _ P Q
    change projectivePointOverMorphism W (P + Q) =
      projectivePointOverMorphism W P * projectivePointOverMorphism W Q
    apply (cancel_mono e.hom).1
    rw [hφ]
    rw [show (projectivePointOverMorphism W P * projectivePointOverMorphism W Q) ≫ e.hom =
        (projectivePointOverMorphism W P ≫ e.hom) *
          (projectivePointOverMorphism W Q ≫ e.hom) by
      simpa only [CategoryTheory.IsMonHom.monoidHom_apply] using
        (CategoryTheory.IsMonHom.monoidHom e.hom
          (AffineCommGroupScheme.testObject (R := K) K)).map_mul
            (projectivePointOverMorphism W P) (projectivePointOverMorphism W Q)]
    rw [hφ, hφ]
    exact φ.map_mul (Multiplicative.ofAdd P) (Multiplicative.ofAdd Q)

/-- Real downstream consumer of the transported group-object interface: the standard-chart
geometric-integrality proof and an exact coordinate torsion point produce a finite-flat split
`Gamma_0(N)` subgroup. -/
noncomputable def standardChartSplitGammaZeroPackageOfAbelianVarietyIso
    {N : ℕ} [NeZero N] (W : WeierstrassCurve K)
    [DecidableEq K] [W.IsElliptic]
    (hchart : ∀ (L : Type u) [Field L] [Algebra K L],
      StandardChartBaseChangeWitness W L)
    (A : TauCeti.AlgebraicGeometry.AbelianVariety K)
    (e : toOver W ≅ A.toOver)
    (φ : Multiplicative W.toProjective.Point →*
      AbelianVarietyRationalPoint A)
    (hφ : ∀ P,
      projectivePointOverMorphism W P ≫ e.hom =
        φ (Multiplicative.ofAdd P))
    (P : W.toAffine.Point) (hP : addOrderOf P = N) :
    StandardChartSplitGammaZeroPackage (N := N) W := by
  letI := grpObjOfAbelianVarietyIso W A e
  exact standardChartSplitGammaZeroPackage W hchart
    (canonicalPointGroupLawCompatibility_of_abelianVarietyIso W A e φ hφ) P hP

/-- The subgroup produced from the pointed abelian-variety isomorphism has the requested
constant geometric order. -/
theorem standardChartSplitGammaZeroPackageOfAbelianVarietyIso_hasConstantOrder
    {N : ℕ} [NeZero N] (W : WeierstrassCurve K)
    [DecidableEq K] [W.IsElliptic]
    (hchart : ∀ (L : Type u) [Field L] [Algebra K L],
      StandardChartBaseChangeWitness W L)
    (A : TauCeti.AlgebraicGeometry.AbelianVariety K)
    (e : toOver W ≅ A.toOver)
    (φ : Multiplicative W.toProjective.Point →*
      AbelianVarietyRationalPoint A)
    (hφ : ∀ P,
      projectivePointOverMorphism W P ≫ e.hom =
        φ (Multiplicative.ofAdd P))
    (P : W.toAffine.Point) (hP : addOrderOf P = N) :
    (standardChartSplitGammaZeroPackageOfAbelianVarietyIso
      W hchart A e φ hφ P hP).datum.subgroup.carrier.HasConstantOrder N := by
  letI := grpObjOfAbelianVarietyIso W A e
  simpa [standardChartSplitGammaZeroPackageOfAbelianVarietyIso] using
    standardChartSplitGammaZeroPackage_hasConstantOrder W hchart
      (canonicalPointGroupLawCompatibility_of_abelianVarietyIso W A e φ hφ) P hP

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
