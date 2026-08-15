/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteSubsetCechTranspose
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentSectionsOverBase
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistAdditiveStandardCech
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistIntegerAcyclicCover
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistStandardCechComplex
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Additive section Čech comparison for integer Serre twists

Over an arbitrary commutative base ring, sections of an integer Serre
twist on a nonempty standard intersection are additively equivalent to
Laurent monomials.  This file packages the actual normalized section
Čech complex in canonical `ℤ`-modules and isolates the restriction
naturality needed to identify it with the additive Laurent complex.

Using only the additive structure avoids imposing a domain or
characteristic-zero hypothesis on the base.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace


noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafCechComparison
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

/-- Equality transport between section groups, retaining their additive
structure. -/
def sectionValueCastAddEquiv
    {X : Scheme} (M : X.Modules)
    {U V : X.Opens} (h : U = V) :
    Γ(M, U) ≃+ Γ(M, V) := by
  subst V
  exact AddEquiv.refl _

/-- The open used by the finite-subset construction is the corresponding
standard projective intersection. -/
lemma standardCoverIntersection_eq_standardIntersection
    (k : Type) [CommRing k] (d : ℕ)
    (I : Finset (Fin (d + 1))) :
    intersection (standardChart k) I =
      standardIntersection k (fun i : ↥I => i.1) := by
  change finiteIntersection (standardChart k) I =
    standardIntersection k (fun i : ↥I => i.1)
  exact finiteIntersection_standardChart k d I

/-- The additive group of sections of `𝒪(m)` on one finite standard-cover
intersection. -/
abbrev additiveStandardSectionModule
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) : Type :=
  Γ(OInt k d m, intersection (standardChart k) I)

/-- Restriction of twist sections, regarded as a `ℤ`-linear map. -/
noncomputable def additiveStandardSectionRestriction
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    {I J : Finset (Fin (d + 1))} (hIJ : I ⊆ J) :
    additiveStandardSectionModule k d m I →ₗ[ℤ]
      additiveStandardSectionModule k d m J :=
  ((OInt k d m).presheaf.map
    (homOfLE
      (intersection_anti (standardChart k) hIJ)).op).hom.toIntLinearMap

@[simp]
lemma additiveStandardSectionRestriction_apply
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    {I J : Finset (Fin (d + 1))} (hIJ : I ⊆ J)
    (x : additiveStandardSectionModule k d m I) :
    additiveStandardSectionRestriction k d m hIJ x =
      (OInt k d m).presheaf.map
        (homOfLE
          (intersection_anti (standardChart k) hIJ)).op x :=
  rfl

/-- Functoriality of additive restriction on the standard
intersections. -/
lemma additiveStandardSectionRestriction_comp
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    {I J K : Finset (Fin (d + 1))}
    (hIJ : I ⊆ J) (hJK : J ⊆ K)
    (x : additiveStandardSectionModule k d m I) :
    additiveStandardSectionRestriction k d m hJK
        (additiveStandardSectionRestriction k d m hIJ x) =
      additiveStandardSectionRestriction k d m
        (hIJ.trans hJK) x := by
  let a :=
    (homOfLE
      (intersection_anti (standardChart k) hIJ)).op
  let b :=
    (homOfLE
      (intersection_anti (standardChart k) hJK)).op
  let c :=
    (homOfLE
      (intersection_anti (standardChart k)
        (hIJ.trans hJK))).op
  have hmap :
      (OInt k d m).presheaf.map a ≫
          (OInt k d m).presheaf.map b =
        (OInt k d m).presheaf.map c := by
    rw [← (OInt k d m).presheaf.map_comp]
    congr 1
  exact congrArg
    (fun f => f.hom x) hmap

/-- The normalized standard-cover section complex, retaining only
canonical integer-module structure. -/
noncomputable def additiveStandardSectionCechComplex
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ) :
    CochainComplex (ModuleCat ℤ) ℕ :=
  let A : Finset (Fin (d + 1)) → Type :=
    additiveStandardSectionModule k d m
  let res : ∀ {I J : Finset (Fin (d + 1))},
      I ⊆ J → A I →ₗ[ℤ] A J :=
    fun {_ _} hIJ =>
      additiveStandardSectionRestriction k d m hIJ
  let hres : ∀ {I J K : Finset (Fin (d + 1))}
      (hIJ : I ⊆ J) (hJK : J ⊆ K) (x : A I),
      res hJK (res hIJ x) =
        res (hIJ.trans hJK) x :=
    fun hIJ hJK x =>
      additiveStandardSectionRestriction_comp
        k d m hIJ hJK x
  finiteSubsetCechComplex
    (ι := Fin (d + 1)) (R := ℤ) A res hres

/-- Laurent coordinates on the sections attached to one standard-cover
simplex. -/
def additiveStandardCoverSectionsLinearEquiv
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    {q : ℕ} (I : Simplex (ι := Fin (d + 1)) q) :
    additiveStandardSectionModule k d m I.1 ≃ₗ[ℤ]
      MonomialModule (ι := Fin (d + 1)) k m I.1 := by
  let j : ↥I.1 := standardCoverSimplexChosenVertex I
  letI : Nonempty ↥I.1 := ⟨j⟩
  exact
    ((sectionValueCastAddEquiv
      (OInt k d m)
      (standardCoverIntersection_eq_standardIntersection
        k d I.1)).trans
        (integerIntersectionLaurentSectionsAddEquivOver
          k d m I.1 j)).toIntLinearEquiv

/-- The exact restriction-naturality statement needed to compare actual
twist sections with the Laurent-coordinate complex. -/
structure AdditiveStandardCoverCoordinatesNatural
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ) : Prop where
  restriction :
    ∀ {q : ℕ}
      (J : Simplex (ι := Fin (d + 1)) (q + 1))
      (j : ↥J.1)
      (x : additiveStandardSectionModule k d m
        (J.1.erase j.1)),
      additiveStandardCoverSectionsLinearEquiv k d m J
          (additiveStandardSectionRestriction k d m
            (Finset.erase_subset j.1 J.1) x) =
        additiveRestriction (k := k) (d := m)
          (Finset.erase_subset j.1 J.1)
          (additiveStandardCoverSectionsLinearEquiv
            k d m (J.erase j.1 j.2) x)

/-- Restriction-natural Laurent coordinates identify the actual additive
section complex with the finite-subset Laurent complex. -/
noncomputable def additiveStandardSectionCechComplexIsoLaurent
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    (hcoord : AdditiveStandardCoverCoordinatesNatural k d m) :
    additiveStandardSectionCechComplex k d m ≅
      additiveStandardLaurentCechComplex
        (ι := Fin (d + 1)) (k := k) m := by
  let A : Finset (Fin (d + 1)) → Type :=
    additiveStandardSectionModule k d m
  let resA : ∀ {I J : Finset (Fin (d + 1))},
      I ⊆ J → A I →ₗ[ℤ] A J :=
    fun {_ _} hIJ =>
      additiveStandardSectionRestriction k d m hIJ
  let B := fun I : Finset (Fin (d + 1)) =>
    MonomialModule (ι := Fin (d + 1)) k m I
  let resB : ∀ {I J : Finset (Fin (d + 1))},
      I ⊆ J → B I →ₗ[ℤ] B J :=
    fun {_ _} hIJ =>
      additiveRestriction (k := k) (d := m) hIJ
  let hresA : ∀ {I J K : Finset (Fin (d + 1))}
      (hIJ : I ⊆ J) (hJK : J ⊆ K) (x : A I),
      resA hJK (resA hIJ x) =
        resA (hIJ.trans hJK) x :=
    fun hIJ hJK x =>
      additiveStandardSectionRestriction_comp
        k d m hIJ hJK x
  let hresB : ∀ {I J K : Finset (Fin (d + 1))}
      (hIJ : I ⊆ J) (hJK : J ⊆ K) (x : B I),
      resB hJK (resB hIJ x) =
        resB (hIJ.trans hJK) x :=
    fun hIJ hJK x =>
      additiveRestriction_comp
        (k := k) (d := m) hIJ hJK x
  change
    finiteSubsetCechComplex A resA hresA ≅
      finiteSubsetCechComplex B resB hresB
  exact
    (finiteSubsetCechComplexIsoPi
      (ι := Fin (d + 1)) (R := ℤ)
      A resA hresA).trans <|
      (finiteSubsetPiCechComplexIsoOfLinearEquiv
        (ι := Fin (d + 1)) (R := ℤ)
        A resA B resB
        hresA hresB
        (fun I =>
          additiveStandardCoverSectionsLinearEquiv k d m I)
        hcoord.restriction).trans <|
        (finiteSubsetCechComplexIsoPi
          (ι := Fin (d + 1)) (R := ℤ)
          B resB hresB).symm

/-- The actual additive section complex is the explicit additive Laurent
Čech complex. -/
noncomputable def additiveStandardSectionCechComplexIsoExplicit
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    (hcoord : AdditiveStandardCoverCoordinatesNatural k d m) :
    additiveStandardSectionCechComplex k d m ≅
      additiveLaurentCechComplex
        (ι := Fin (d + 1)) (R := k) m :=
  (additiveStandardSectionCechComplexIsoLaurent
      k d m hcoord).trans
    (additiveStandardLaurentCechComplexIso
      (ι := Fin (d + 1)) (k := k) m)

/-- In nonnegative degree, positive homology of the actual standard-cover
section complex vanishes once the coordinate naturality is supplied. -/
theorem additiveStandardSectionPositiveHomology_subsingleton
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    (hcoord : AdditiveStandardCoverCoordinatesNatural k d m)
    (hm : 0 ≤ m) (q : ℕ) :
    Subsingleton
      ((additiveStandardSectionCechComplex k d m).homology
        (q + 1)) := by
  let complexIso :=
    additiveStandardSectionCechComplexIsoExplicit
      k d m hcoord
  let e :=
    isoOfQuasiIsoAt complexIso.hom (q + 1)
  let htarget :
      Subsingleton
        ((additiveLaurentCechComplex
          (ι := Fin (d + 1)) (R := k) m).homology
            (q + 1)) :=
    additiveLaurentCechPositiveHomology_subsingleton
      (ι := Fin (d + 1)) (R := k) hm q
  exact
    ⟨fun x y => by
      have hxy : e.hom x = e.hom y :=
        htarget.elim _ _
      have hinv :=
        congrArg (fun z => e.inv z) hxy
      simpa using hinv⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
