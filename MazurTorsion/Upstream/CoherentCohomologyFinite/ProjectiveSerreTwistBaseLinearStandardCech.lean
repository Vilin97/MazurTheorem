/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteSubsetCechTranspose
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentCechCategoricalTotalFiniteness
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentSectionsBaseLinear
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistAdditiveSectionCechComparison
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistBaseChartLinearity

/-!
# Base-linear standard Čech complexes for projective Serre twists

For projective space over an arbitrary commutative ring, the sections of
an integer Serre twist on every nonempty standard intersection carry the
module structure induced by the structure morphism.  The Laurent
trivializations are linear for this action.  This file packages the
normalized standard-cover complex in those base-linear coordinates.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open scoped BigOperators


noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

local instance projectiveSpaceOverBase
    (k : Type) [CommRing k] (d : ℕ) :
    (scheme k d).Over (Spec (CommRingCat.of k)) :=
  ⟨toSpec k d⟩

/-- Equality transport between values of a module-valued presheaf. -/
def modulePresheafValueCastLinearEquivOver
    {k : Type} [CommRing k] {T : TopCat}
    (P : (Opens T)ᵒᵖ ⥤ ModuleCat k)
    {U V : Opens T} (h : U = V) :
    P.obj (op U) ≃ₗ[k] P.obj (op V) := by
  subst V
  exact LinearEquiv.refl k _

/-- Sections of `O(m)` on one finite standard-cover intersection, with
the coefficient-ring module structure supplied by the structure map. -/
abbrev baseStandardSectionModule
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) : Type :=
  (moduleSheaf (k := k) (OInt k d m)).obj.obj
    (op (intersection (standardChart k) I))

/-- Base-linear restriction of twist sections between standard
intersections. -/
noncomputable def baseStandardSectionRestriction
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    {I J : Finset (Fin (d + 1))} (hIJ : I ⊆ J) :
    baseStandardSectionModule k d m I →ₗ[k]
      baseStandardSectionModule k d m J :=
  ((moduleSheaf (k := k) (OInt k d m)).obj.map
    (homOfLE
      (intersection_anti (standardChart k) hIJ)).op).hom

@[simp]
lemma baseStandardSectionRestriction_apply
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    {I J : Finset (Fin (d + 1))} (hIJ : I ⊆ J)
    (x : baseStandardSectionModule k d m I) :
    baseStandardSectionRestriction k d m hIJ x =
      (moduleSheaf (k := k) (OInt k d m)).obj.map
        (homOfLE
          (intersection_anti (standardChart k) hIJ)).op x :=
  rfl

/-- Functoriality of base-linear restriction. -/
lemma baseStandardSectionRestriction_comp
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    {I J K : Finset (Fin (d + 1))}
    (hIJ : I ⊆ J) (hJK : J ⊆ K)
    (x : baseStandardSectionModule k d m I) :
    baseStandardSectionRestriction k d m hJK
        (baseStandardSectionRestriction k d m hIJ x) =
      baseStandardSectionRestriction k d m
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
      (moduleSheaf (k := k) (OInt k d m)).obj.map a ≫
          (moduleSheaf (k := k) (OInt k d m)).obj.map b =
        (moduleSheaf (k := k) (OInt k d m)).obj.map c := by
    rw [← (moduleSheaf (k := k) (OInt k d m)).obj.map_comp]
    congr 1
  exact congrArg (fun f => f.hom x) hmap

/-- The normalized base-linear standard-cover section complex. -/
noncomputable def baseStandardSectionCechComplex
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ) :
    CochainComplex (ModuleCat k) ℕ :=
  finiteSubsetCechComplex
    (R := k)
    (baseStandardSectionModule k d m)
    (fun {_ _} hIJ =>
      baseStandardSectionRestriction k d m hIJ)
    (baseStandardSectionRestriction_comp k d m)

/-- The dependent finite-subset presentation of Laurent cochains is
linearly equivalent to the sigma-indexed presentation. -/
noncomputable def baseFiniteSubsetLaurentCochainLinearEquiv
    (k : Type) [CommRing k] (d q : ℕ) (m : ℤ) :
    FiniteSubsetCochain
        (fun I : Finset (Fin (d + 1)) =>
          MonomialModule (ι := Fin (d + 1)) k m I) q ≃ₗ[k]
      Cochain (ι := Fin (d + 1)) k m q :=
  (sigmaFinsuppLequivDFinsupp k).symm

@[simp]
lemma baseFiniteSubsetLaurentCochainLinearEquiv_single
    (k : Type) [CommRing k] (d q : ℕ) (m : ℤ)
    (I : Simplex (ι := Fin (d + 1)) q)
    (a : AdmissibleExponent (ι := Fin (d + 1)) m I.1)
    (r : k) :
    baseFiniteSubsetLaurentCochainLinearEquiv k d q m
        (DFinsupp.single I (Finsupp.single a r)) =
      Finsupp.single ⟨I, a⟩ r := by
  apply (sigmaFinsuppLequivDFinsupp k).injective
  simp [baseFiniteSubsetLaurentCochainLinearEquiv]

/-- The finite-subset Laurent cochain equivalence intertwines the two
cochain differentials. -/
lemma baseFiniteSubsetLaurentCochainLinearEquiv_differential
    (k : Type) [CommRing k] (d q : ℕ) (m : ℤ) :
    (baseFiniteSubsetLaurentCochainLinearEquiv
      k d (q + 1) m).toLinearMap.comp
        (finiteSubsetDifferential
          (R := k)
          (fun I : Finset (Fin (d + 1)) =>
            MonomialModule (ι := Fin (d + 1)) k m I)
          (fun {_ _} hIJ => restriction (R := k) hIJ) q) =
      (differential
        (ι := Fin (d + 1)) (R := k) m q).comp
        (baseFiniteSubsetLaurentCochainLinearEquiv
          k d q m).toLinearMap := by
  apply DFinsupp.lhom_ext
  intro I x
  induction x using Finsupp.induction_linear with
  | zero =>
      simp
  | add x y hx hy =>
      simp only [DFinsupp.single_add, map_add, hx, hy]
  | single a r =>
      have hsource :
          baseFiniteSubsetLaurentCochainLinearEquiv k d q m
              (DFinsupp.single I (Finsupp.single a r)) =
            Finsupp.single ⟨I, a⟩ r :=
        baseFiniteSubsetLaurentCochainLinearEquiv_single
          k d q m I a r
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      apply Eq.trans
        (b := differential
          (ι := Fin (d + 1)) (R := k) m q
          (Finsupp.single ⟨I, a⟩ r))
      · rw [finiteSubsetDifferential_component,
          finiteSubsetComponentDifferential,
          LinearMap.sum_apply, map_sum,
          differential_single, basisCoboundary,
          Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [LinearMap.smul_apply, LinearMap.comp_apply,
          DFinsupp.lsingle_apply, restriction_single,
          map_smul]
        have htarget :
            baseFiniteSubsetLaurentCochainLinearEquiv
                k d (q + 1) m
                (DFinsupp.single (I.insert j.1 j.2)
                  (Finsupp.single
                    (exponentInclusion
                      (I.subset_insert j.1 j.2) a) r)) =
              Finsupp.single
                ⟨I.insert j.1 j.2,
                  exponentInclusion
                    (I.subset_insert j.1 j.2) a⟩ r :=
          baseFiniteSubsetLaurentCochainLinearEquiv_single
            k d (q + 1) m _ _ r
        calc
          _ = insertionSign (R := k) I.1 j.1 •
              Finsupp.single
                ⟨I.insert j.1 j.2,
                  exponentInclusion
                    (I.subset_insert j.1 j.2) a⟩ r :=
            congrArg
              (fun z =>
                insertionSign (R := k) I.1 j.1 • z)
              htarget
          _ = _ := by
            rw [Finsupp.smul_single',
              Finsupp.smul_single']
            congr 1
            exact mul_comm _ _
      · exact congrArg
          (differential
            (ι := Fin (d + 1)) (R := k) m q)
          hsource.symm

/-- The finite-subset Laurent complex is the explicit Laurent Čech
complex over the same coefficient ring. -/
noncomputable def baseFiniteSubsetLaurentCechComplexIsoLaurent
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ) :
    finiteSubsetCechComplex
        (R := k)
        (fun I : Finset (Fin (d + 1)) =>
          MonomialModule (ι := Fin (d + 1)) k m I)
        (fun {_ _} hIJ => restriction (R := k) hIJ)
        (fun _ _ x =>
          LinearMap.congr_fun
            (restriction_comp (R := k) (d := m) _ _) x) ≅
      laurentCechComplex
        (ι := Fin (d + 1)) (R := k) m :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q =>
      (baseFiniteSubsetLaurentCochainLinearEquiv
        k d q m).toModuleIso)
    (by
      rintro i j (hij : i + 1 = j)
      subst hij
      simp only [finiteSubsetCechComplex,
        CochainComplex.of_d, laurentCechComplex_d]
      apply ModuleCat.hom_ext
      exact
        (baseFiniteSubsetLaurentCochainLinearEquiv_differential
          k d i m).symm)

/-- Base-linear Laurent coordinates on the sections belonging to one
simplex of the standard projective cover. -/
noncomputable def baseStandardCoverSectionsLinearEquiv
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    {q : ℕ} (I : Simplex (ι := Fin (d + 1)) q) :
    baseStandardSectionModule k d m I.1 ≃ₗ[k]
      MonomialModule (ι := Fin (d + 1)) k m I.1 := by
  let j : ↥I.1 := standardCoverSimplexChosenVertex I
  letI : Nonempty ↥I.1 := ⟨j⟩
  exact
    (modulePresheafValueCastLinearEquivOver
      (moduleSheaf (k := k) (OInt k d m)).obj
      ((standardCoverIntersection_eq_standardIntersection
          k d I.1).trans
        (standardFinsetIntersection_eq_laurentOpen
          k d I.1))).trans
      (integerChartLaurentSectionsLinearEquivOver
        k d m I.1 j)

/-- Restriction-natural base-linear Laurent coordinates. -/
structure BaseStandardCoverCoordinatesNatural
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ) : Prop where
  restriction :
    ∀ {q : ℕ}
      (J : Simplex (ι := Fin (d + 1)) (q + 1))
      (j : ↥J.1)
      (x : baseStandardSectionModule k d m
        (J.1.erase j.1)),
      baseStandardCoverSectionsLinearEquiv k d m J
          (baseStandardSectionRestriction k d m
            (Finset.erase_subset j.1 J.1) x) =
        restriction (R := k)
          (Finset.erase_subset j.1 J.1)
          (baseStandardCoverSectionsLinearEquiv
            k d m (J.erase j.1 j.2) x)

/-- Restriction-natural coordinates identify the geometric section
complex with the Laurent finite-subset complex. -/
noncomputable def baseStandardSectionCechComplexIsoLaurentFiniteSubset
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    (hcoord : BaseStandardCoverCoordinatesNatural k d m) :
    baseStandardSectionCechComplex k d m ≅
      finiteSubsetCechComplex
        (R := k)
        (fun I : Finset (Fin (d + 1)) =>
          MonomialModule (ι := Fin (d + 1)) k m I)
        (fun {_ _} hIJ => restriction (R := k) hIJ)
        (fun _ _ x =>
          LinearMap.congr_fun
            (restriction_comp (R := k) (d := m) _ _) x) := by
  let A := baseStandardSectionModule k d m
  let resA : ∀ {I J : Finset (Fin (d + 1))},
      I ⊆ J → A I →ₗ[k] A J :=
    fun {_ _} hIJ =>
      baseStandardSectionRestriction k d m hIJ
  let B := fun I : Finset (Fin (d + 1)) =>
    MonomialModule (ι := Fin (d + 1)) k m I
  let resB : ∀ {I J : Finset (Fin (d + 1))},
      I ⊆ J → B I →ₗ[k] B J :=
    fun {_ _} hIJ => restriction (R := k) hIJ
  let hresA : ∀ {I J K : Finset (Fin (d + 1))}
      (hIJ : I ⊆ J) (hJK : J ⊆ K) (x : A I),
      resA hJK (resA hIJ x) =
        resA (hIJ.trans hJK) x :=
    fun hIJ hJK x =>
      baseStandardSectionRestriction_comp
        k d m hIJ hJK x
  let hresB : ∀ {I J K : Finset (Fin (d + 1))}
      (hIJ : I ⊆ J) (hJK : J ⊆ K) (x : B I),
      resB hJK (resB hIJ x) =
        resB (hIJ.trans hJK) x :=
    fun hIJ hJK x =>
      LinearMap.congr_fun
        (restriction_comp (R := k) (d := m) hIJ hJK) x
  change
    finiteSubsetCechComplex A resA hresA ≅
      finiteSubsetCechComplex B resB hresB
  exact
    (finiteSubsetCechComplexIsoPi
      (R := k) A resA hresA).trans <|
      (finiteSubsetPiCechComplexIsoOfLinearEquiv
        (R := k)
        A resA B resB hresA hresB
        (fun I =>
          baseStandardCoverSectionsLinearEquiv k d m I)
        hcoord.restriction).trans <|
        (finiteSubsetCechComplexIsoPi
          (R := k) B resB hresB).symm

/-- The base-linear geometric section complex is the explicit Laurent
Čech complex. -/
noncomputable def baseStandardSectionCechComplexIsoLaurent
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    (hcoord : BaseStandardCoverCoordinatesNatural k d m) :
    baseStandardSectionCechComplex k d m ≅
      laurentCechComplex
        (ι := Fin (d + 1)) (R := k) m :=
  (baseStandardSectionCechComplexIsoLaurentFiniteSubset
      k d m hcoord).trans
    (baseFiniteSubsetLaurentCechComplexIsoLaurent
      k d m)

/-- Over a Noetherian coefficient ring, every homology module of the
base-linear standard section complex is finite. -/
theorem baseStandardSectionCechHomology_finite
    (k : Type) [CommRing k] [IsNoetherianRing k]
    (d : ℕ) (m : ℤ)
    (hcoord : BaseStandardCoverCoordinatesNatural k d m)
    (n : ℕ) :
    Module.Finite k
      ((baseStandardSectionCechComplex k d m).homology n) := by
  let e :=
    (HomologicalComplex.homologyFunctor
      (ModuleCat k) (ComplexShape.up ℕ) n).mapIso
        (baseStandardSectionCechComplexIsoLaurent
          k d m hcoord)
  exact moduleFiniteOfLinearEquiv
    (laurentCechCategoricalHomologyFinite
      (ι := Fin (d + 1)) (R := k) m n)
    e.toLinearEquiv.symm

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
