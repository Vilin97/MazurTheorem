/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteSubsetFreeSheafTermComparison
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Comparing the ordered-cover resolution with finite free sheaf terms

The normalized ordered-cover term is a finite coproduct of coefficient
presheaves represented by the corresponding finite intersections.
After sheafification, these coefficient presheaves are the usual free
module sheaves used in the finite-subset source complex.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace


noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {R : Type u} [CommRing R]
variable {T : TopCat.{u}}
variable {ι : Type u} [Fintype ι] [LinearOrder ι]

/-- A linear map from the rank-one free module is determined by the
image of `1`. -/
noncomputable def rankOneHomEquiv (M : ModuleCat.{u} R) :
    ((ModuleCat.of R R) ⟶ M) ≃ M :=
  ModuleCat.homEquiv.trans
    (LinearMap.ringLmapEquivSelf R ℤ M)

/-- The rank-one coyoneda functor is the underlying-type functor. -/
noncomputable def rankOneCoyonedaIsoForget :
    coyoneda.obj (op (ModuleCat.of R R)) ≅
      forget (ModuleCat.{u} R) :=
  NatIso.ofComponents
    (fun M => (rankOneHomEquiv (R := R) M).toIso)
    (fun f => by
      ext g
      rfl)

/-- The coproduct-of-copies construction and the finitely-supported
free-module construction are canonically isomorphic: they are both
left adjoint to the underlying-type functor. -/
noncomputable def sigmaConstIsoFreeModule :
    sigmaConst.obj (ModuleCat.of R R) ≅ ModuleCat.free R :=
  Adjunction.leftAdjointUniq
    ((sigmaConstAdj (ModuleCat.of R R)).ofNatIsoRight
      (rankOneCoyonedaIsoForget (R := R)))
    (ModuleCat.adj R)

/-- On one represented open, the coefficient presheaf built from
coproducts of copies of `R` sheafifies to the existing represented free
module sheaf. -/
noncomputable def sheafifiedRepresentedSigmaIsoFreeModuleSheaf
    (V : Opens T) :
    (moduleSheafification (R := R) (T := T)).obj
        (yoneda.obj V ⋙
          sigmaConst.obj (ModuleCat.of R R)) ≅
      freeModuleSheaf (R := R) V :=
  (moduleSheafification (R := R) (T := T)).mapIso
    (Functor.isoWhiskerLeft (yoneda.obj V)
      (sigmaConstIsoFreeModule (R := R)))

/-- Normalize the composite discrete diagram appearing after applying
sheafification to a finite coproduct. -/
noncomputable def sheafifiedFiniteSubsetDiagramIso
    (U : ι → Opens T) (q : ℕ) :
    colimit
        (Discrete.functor
            (fun I : Simplex (ι := ι) q =>
              yoneda.obj (intersection U I.1) ⋙
                sigmaConst.obj (ModuleCat.of R R)) ⋙
          moduleSheafification (R := R) (T := T)) ≅
      ∐ fun I : Simplex (ι := ι) q =>
        (moduleSheafification (R := R) (T := T)).obj
          (yoneda.obj (intersection U I.1) ⋙
            sigmaConst.obj (ModuleCat.of R R)) :=
  colim.mapIso
    (NatIso.ofComponents
      (fun _ => Iso.refl _)
      (fun {X Y} f => by
        obtain rfl : X = Y :=
          Discrete.ext (Discrete.eq_of_hom f)
        obtain rfl : f = 𝟙 X := Subsingleton.elim _ _
        simp))

/-- Sheafification of the finite-subset represented presheaf term is
the existing finite coproduct `term` of represented free module
sheaves. -/
noncomputable def sheafifiedFiniteSubsetSigmaTermIso
    (U : ι → Opens T) (q : ℕ) :
    (moduleSheafification (R := R) (T := T)).obj
        (finiteSubsetSigmaPresheafTerm (R := R) U q) ≅
      term (R := R) U q :=
  preservesColimitIso
      (moduleSheafification (R := R) (T := T))
      (Discrete.functor
        (fun I : Simplex (ι := ι) q =>
          yoneda.obj (intersection U I.1) ⋙
            sigmaConst.obj (ModuleCat.of R R))) ≪≫
    sheafifiedFiniteSubsetDiagramIso (R := R) U q ≪≫
    Limits.Sigma.mapIso
      (fun I : Simplex (ι := ι) q =>
        sheafifiedRepresentedSigmaIsoFreeModuleSheaf
          (R := R) (T := T) (intersection U I.1))

/-- Each term of the sheafified ordered-cover complex is canonically
the corresponding finite free sheaf term. -/
noncomputable def sheafifiedOrderedCoverTermIso
    (U : ι → Opens T) (q : ℕ) :
    (sheafifiedOrderedCoverComplex (R := R) U).X q ≅
      term (R := R) U q :=
  (moduleSheafification (R := R) (T := T)).mapIso
      (orderedCoverNormalizedTermIsoFiniteSubset
        (R := R) U q) ≪≫
    sheafifiedFiniteSubsetSigmaTermIso (R := R) U q

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf
