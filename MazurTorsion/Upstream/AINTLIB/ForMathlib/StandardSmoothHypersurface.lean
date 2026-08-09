/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
/-
Port provenance: adapted from AINTLIB commit
f6037f1f861eb74bd32f3333348bafd42164a7c8, exact source blob
a1640ea5835d14050eea045a8ce3bacdb0504659.

Local repair: the source-level backward-definitional-equality transparency option
around `hypersurfacePresentation_jacobian_isUnit` is omitted.  The inline
relation-to-variable injectivity witness is factored through an explicitly typed
helper, so the naive presentation unfolds at this repository's immutable Mathlib pin.
Goal-state conversions flagged by the pinned linter use `change` in place of `show`.
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Smooth.StandardSmooth

/-!
# Localized hypersurfaces are standard smooth

For `f : MvPolynomial σ R` over a finite variable type, the hypersurface
`S := R[Xⱼ]/(f)` localized away from the image of a partial derivative `∂f/∂Xᵢ` is
standard smooth over `R` of relative dimension `#σ - 1`: the presentation with
variables `σ ⊕ {w}`, relations `(f, w·∂f/∂Xᵢ - 1)` and section `(Xᵢ, w)` has Jacobian
`(∂f/∂Xᵢ)²`, a unit after the localization.

This is the chartwise smoothness engine for the projective Weierstrass model
(AINTLIB ModularCurves T-A3b); upstream candidate.

## Main results

* `ModularCurves.hypersurfaceAwayEquiv`: the model quotient
  `R[Option σ]/(f, X none·∂f - 1)` is the localized hypersurface.
* `ModularCurves.isStandardSmoothOfRelativeDimension_hypersurface_away`: the localized
  hypersurface is standard smooth of relative dimension `#σ - 1` over `R`.
-/

open MvPolynomial

namespace ModularCurves

variable {R : Type*} [CommRing R] {σ : Type} [Fintype σ] [DecidableEq σ]
  (f : MvPolynomial σ R) (i : σ)

/-- The two relations of the localized hypersurface: `f` and `X none · ∂f/∂Xᵢ - 1`. -/
noncomputable def hypersurfaceRels : Fin 2 → MvPolynomial (Option σ) R :=
  ![rename Option.some f,
    X none * rename Option.some (pderiv i f) - 1]

/-- The model quotient presenting the localized hypersurface. -/
noncomputable abbrev HypersurfaceModel : Type _ :=
  MvPolynomial (Option σ) R ⧸ Ideal.span (Set.range (hypersurfaceRels f i))

omit [Fintype σ] [DecidableEq σ] in
/-- The chosen relation-to-variable map sends the hypersurface relation to `Xᵢ`
and the inverse relation to the new variable. -/
private lemma hypersurfaceMap_injective :
    Function.Injective (![Option.some i, none] : Fin 2 → Option σ) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all

/-- The naive presentation of the model quotient, with section `(Xᵢ, w)`. -/
noncomputable def hypersurfacePresentation :
    Algebra.PreSubmersivePresentation R (HypersurfaceModel f i) (Option σ) (Fin 2) :=
  Algebra.PreSubmersivePresentation.naive (v := hypersurfaceRels f i)
    ![Option.some i, none] (hypersurfaceMap_injective i)

omit [Fintype σ] [DecidableEq σ] in
lemma pderiv_none_rename_some (p : MvPolynomial σ R) :
    pderiv (none : Option σ) (rename Option.some p) = 0 :=
  pderiv_eq_zero_of_notMem_vars fun h => by
    obtain ⟨j, -, hj⟩ := mem_vars_rename _ _ h
    exact Option.some_ne_none j hj

omit [Fintype σ] [DecidableEq σ] in
lemma hypersurfacePresentation_jacobian_isUnit :
    IsUnit (hypersurfacePresentation f i).jacobian := by
  classical
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  have h00 : (hypersurfacePresentation f i).jacobiMatrix 0 0 =
      rename Option.some (pderiv i f) := by
    rw [hypersurfacePresentation,
      Algebra.PreSubmersivePresentation.jacobiMatrix_naive]
    change pderiv (Option.some i) (rename Option.some f) = _
    rw [pderiv_rename (Option.some_injective _)]
  have h10 : (hypersurfacePresentation f i).jacobiMatrix 1 0 = 0 := by
    rw [hypersurfacePresentation,
      Algebra.PreSubmersivePresentation.jacobiMatrix_naive]
    change pderiv none (rename Option.some f) = 0
    exact pderiv_none_rename_some f
  have h11 : (hypersurfacePresentation f i).jacobiMatrix 1 1 =
      rename Option.some (pderiv i f) := by
    rw [hypersurfacePresentation,
      Algebra.PreSubmersivePresentation.jacobiMatrix_naive]
    change pderiv none (X none * rename Option.some (pderiv i f) - 1) = _
    rw [map_sub, pderiv_mul, pderiv_X_self, one_mul, pderiv_none_rename_some,
      mul_zero, add_zero, Derivation.map_one_eq_zero, sub_zero]
  rw [Matrix.det_fin_two, h00, h10, h11, mul_zero, sub_zero, map_mul]
  refine (isUnit_iff_exists_inv.mpr ⟨algebraMap ((hypersurfacePresentation f i).Ring)
      (HypersurfaceModel f i) (X none), ?_⟩).mul
    (isUnit_iff_exists_inv.mpr ⟨algebraMap ((hypersurfacePresentation f i).Ring)
      (HypersurfaceModel f i) (X none), ?_⟩) <;>
  · rw [← map_mul, show ((algebraMap ((hypersurfacePresentation f i).Ring)
        (HypersurfaceModel f i)) : MvPolynomial (Option σ) R →+*
        HypersurfaceModel f i) = Ideal.Quotient.mk _ from rfl,
      ← map_one (Ideal.Quotient.mk (Ideal.span (Set.range (hypersurfaceRels f i)))),
      Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    refine Ideal.subset_span ⟨1, ?_⟩
    change X none * rename Option.some (pderiv i f) - 1 = _
    ring

/-- The submersive presentation of the model quotient. -/
noncomputable def hypersurfaceSubmersivePresentation :
    Algebra.SubmersivePresentation R (HypersurfaceModel f i) (Option σ) (Fin 2) where
  __ := hypersurfacePresentation f i
  jacobian_isUnit := hypersurfacePresentation_jacobian_isUnit f i

omit [DecidableEq σ] in
lemma hypersurfaceModel_isStandardSmoothOfRelativeDimension :
    Algebra.IsStandardSmoothOfRelativeDimension (Fintype.card σ - 1) R
      (HypersurfaceModel f i) := by
  refine (hypersurfaceSubmersivePresentation f i).isStandardSmoothOfRelativeDimension ?_
  change (hypersurfacePresentation f i).dimension = _
  rw [Algebra.Presentation.dimension]
  simp only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin]
  omega

section AwayEquiv

/-- The variable assignment underlying `hypersurfaceToAway`. -/
private noncomputable def toAwayAux :
    MvPolynomial (Option σ) R →ₐ[R] Localization.Away
      (Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f)) :=
  MvPolynomial.aeval fun o : Option σ => o.elim
    (IsLocalization.Away.invSelf (S := Localization.Away
      (Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f)))
      (Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f)))
    (fun j => algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {f})
      (MvPolynomial.X j)))

omit [Fintype σ] [DecidableEq σ] in
private lemma toAwayAux_rename (p : MvPolynomial σ R) :
    toAwayAux f i (rename Option.some p) =
      algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {f}) p) := by
  have h : (toAwayAux f i).comp (rename Option.some) =
      (IsScalarTower.toAlgHom R (MvPolynomial σ R ⧸ Ideal.span {f})
        (Localization.Away (Ideal.Quotient.mk (Ideal.span {f})
          (pderiv i f)))).comp (Ideal.Quotient.mkₐ R (Ideal.span {f})) := by
    refine MvPolynomial.algHom_ext fun j => ?_
    simp [toAwayAux]
  exact DFunLike.congr_fun h p

/-- The canonical `R`-algebra map from the model quotient to the localized
hypersurface, sending `Xⱼ ↦ Xⱼ` and the inverse variable to `1/∂f`. -/
private noncomputable def hypersurfaceToAway :
    HypersurfaceModel f i →ₐ[R] Localization.Away
      (Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f)) := by
  refine Ideal.Quotient.liftₐ _ (toAwayAux f i) fun a ha => ?_
  suffices h : Ideal.span (Set.range (hypersurfaceRels f i)) ≤
      RingHom.ker (toAwayAux f i).toRingHom from h ha
  rw [Ideal.span_le]
  rintro _ ⟨k, rfl⟩
  simp only [SetLike.mem_coe, RingHom.mem_ker]
  fin_cases k
  · change toAwayAux f i (hypersurfaceRels f i 0) = 0
    rw [show hypersurfaceRels f i 0 = rename Option.some f from rfl,
      toAwayAux_rename,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f),
      map_zero]
  · change toAwayAux f i (hypersurfaceRels f i 1) = 0
    rw [show hypersurfaceRels f i 1 =
      X none * rename Option.some (pderiv i f) - 1 from rfl]
    rw [map_sub, map_mul, toAwayAux_rename, map_one]
    rw [show toAwayAux f i (X (none : Option σ)) =
      IsLocalization.Away.invSelf (S := Localization.Away
        (Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f)))
        (Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f)) from
      MvPolynomial.aeval_X _ _]
    rw [mul_comm, IsLocalization.Away.mul_invSelf, sub_self]

omit [Fintype σ] [DecidableEq σ] in
private lemma hypersurfaceToAway_mk (p : MvPolynomial (Option σ) R) :
    hypersurfaceToAway f i (Ideal.Quotient.mk _ p) = toAwayAux f i p :=
  rfl

/-- The variable assignment `Xⱼ ↦ Xⱼ` into the model quotient. -/
private noncomputable def ofSAux :
    MvPolynomial σ R →ₐ[R] HypersurfaceModel f i :=
  MvPolynomial.aeval fun j => Ideal.Quotient.mk _ (X (Option.some j))

omit [Fintype σ] [DecidableEq σ] in
private lemma ofSAux_eq (p : MvPolynomial σ R) :
    ofSAux f i p = Ideal.Quotient.mk _ (rename Option.some p) := by
  have h : ofSAux f i =
      (Ideal.Quotient.mkₐ R (Ideal.span (Set.range (hypersurfaceRels f i)))).comp
        (MvPolynomial.rename (R := R) Option.some) := by
    refine MvPolynomial.algHom_ext fun j => ?_
    simp [ofSAux]
  exact DFunLike.congr_fun h p

/-- The `R`-algebra map from the hypersurface to the model quotient. -/
private noncomputable def hypersurfaceOfS :
    (MvPolynomial σ R ⧸ Ideal.span {f}) →ₐ[R] HypersurfaceModel f i := by
  refine Ideal.Quotient.liftₐ _ (ofSAux f i) fun a ha => ?_
  suffices h : Ideal.span {f} ≤ RingHom.ker (ofSAux f i).toRingHom from h ha
  rw [Ideal.span_le, Set.singleton_subset_iff]
  change ofSAux f i f = 0
  rw [ofSAux_eq]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨0, rfl⟩)

omit [Fintype σ] [DecidableEq σ] in
private lemma hypersurfaceOfS_mk (p : MvPolynomial σ R) :
    hypersurfaceOfS f i (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (rename Option.some p) :=
  ofSAux_eq f i p

omit [Fintype σ] [DecidableEq σ] in
private lemma hypersurfaceOfS_pderiv_isUnit :
    IsUnit (hypersurfaceOfS f i (Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f))) := by
  rw [hypersurfaceOfS_mk]
  refine isUnit_iff_exists_inv.mpr ⟨Ideal.Quotient.mk _ (X none), ?_⟩
  rw [← map_mul, ← map_one (Ideal.Quotient.mk
    (Ideal.span (Set.range (hypersurfaceRels f i)))),
    Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  refine Ideal.subset_span ⟨1, ?_⟩
  change X none * rename Option.some (pderiv i f) - 1 = _
  ring

/-- The `R`-algebra map from the localized hypersurface to the model quotient. -/
private noncomputable def hypersurfaceFromAway :
    Localization.Away (Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f)) →ₐ[R]
      HypersurfaceModel f i where
  toRingHom := Localization.awayLift
    (hypersurfaceOfS f i : _ →+* HypersurfaceModel f i)
    _ (hypersurfaceOfS_pderiv_isUnit f i)
  commutes' r := by
    rw [IsScalarTower.algebraMap_apply R (MvPolynomial σ R ⧸ Ideal.span {f})
      (Localization.Away (Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f)))]
    exact (IsLocalization.Away.lift_eq _ _ _).trans
      ((hypersurfaceOfS f i).commutes r)

omit [Fintype σ] [DecidableEq σ] in
private lemma hypersurfaceFromAway_algebraMap
    (x : MvPolynomial σ R ⧸ Ideal.span {f}) :
    hypersurfaceFromAway f i (algebraMap _ _ x) = hypersurfaceOfS f i x :=
  IsLocalization.Away.lift_eq _ (hypersurfaceOfS_pderiv_isUnit f i) x

omit [Fintype σ] [DecidableEq σ] in
private lemma hypersurfaceRel_mul_eq_one :
    Ideal.Quotient.mk (Ideal.span (Set.range (hypersurfaceRels f i)))
        (rename Option.some (pderiv i f)) *
      Ideal.Quotient.mk _ (X (none : Option σ)) = 1 := by
  rw [← map_mul, ← map_one (Ideal.Quotient.mk
    (Ideal.span (Set.range (hypersurfaceRels f i)))),
    Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  refine Ideal.subset_span ⟨1, ?_⟩
  change X none * rename Option.some (pderiv i f) - 1 = _
  ring

omit [Fintype σ] [DecidableEq σ] in
/-- The `X none` generator survives the round trip `fromAway ∘ toAway = id`: this is the
Eisenstein-style relation `w · ∂f = 1` in the model, so `w = w · ∂f · w⁻¹` collapses to
`w`. Extracted from `fromAway_toAway` (the harder of its two `algHom_ext` branches). -/
private lemma fromAway_toAway_apply_X_none :
    hypersurfaceFromAway f i (hypersurfaceToAway f i
      (Ideal.Quotient.mk (Ideal.span (Set.range (hypersurfaceRels f i)))
        (X (none : Option σ)))) =
      Ideal.Quotient.mk (Ideal.span (Set.range (hypersurfaceRels f i))) (X none) := by
  rw [hypersurfaceToAway_mk]
  rw [show toAwayAux f i (X (none : Option σ)) =
    IsLocalization.Away.invSelf (S := Localization.Away
      (Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f)))
      (Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f)) from
    MvPolynomial.aeval_X _ _]
  have h1 : hypersurfaceFromAway f i (algebraMap _ _
      (Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f))) *
      hypersurfaceFromAway f i (IsLocalization.Away.invSelf
        (S := Localization.Away (Ideal.Quotient.mk (Ideal.span {f})
          (pderiv i f))) (Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f))) =
      1 := by
    rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
  rw [hypersurfaceFromAway_algebraMap, hypersurfaceOfS_mk] at h1
  calc hypersurfaceFromAway f i (IsLocalization.Away.invSelf
        (S := Localization.Away (Ideal.Quotient.mk (Ideal.span {f})
          (pderiv i f))) (Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f)))
      = (Ideal.Quotient.mk _ (X (none : Option σ)) *
          Ideal.Quotient.mk _ (rename Option.some (pderiv i f))) *
          hypersurfaceFromAway f i (IsLocalization.Away.invSelf
            (S := Localization.Away (Ideal.Quotient.mk (Ideal.span {f})
              (pderiv i f)))
            (Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f))) := by
        rw [mul_comm (Ideal.Quotient.mk _ (X (none : Option σ))),
          hypersurfaceRel_mul_eq_one, one_mul]
    _ = Ideal.Quotient.mk _ (X (none : Option σ)) *
          (Ideal.Quotient.mk _ (rename Option.some (pderiv i f)) *
            hypersurfaceFromAway f i (IsLocalization.Away.invSelf
              (S := Localization.Away (Ideal.Quotient.mk (Ideal.span {f})
                (pderiv i f)))
              (Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f)))) :=
        mul_assoc _ _ _
    _ = Ideal.Quotient.mk _ (X (none : Option σ)) := by rw [h1, mul_one]

omit [Fintype σ] [DecidableEq σ] in
private lemma fromAway_toAway :
    (hypersurfaceFromAway f i).comp (hypersurfaceToAway f i) =
      AlgHom.id R (HypersurfaceModel f i) := by
  refine AlgHom.ext fun x => ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h : ((hypersurfaceFromAway f i).comp (hypersurfaceToAway f i)).comp
      (Ideal.Quotient.mkₐ R (Ideal.span (Set.range (hypersurfaceRels f i)))) =
      Ideal.Quotient.mkₐ R (Ideal.span (Set.range (hypersurfaceRels f i))) := by
    refine MvPolynomial.algHom_ext fun o => ?_
    rcases o with _ | j
    · exact fromAway_toAway_apply_X_none f i
    · change hypersurfaceFromAway f i (hypersurfaceToAway f i
        (Ideal.Quotient.mk _ (X (Option.some j)))) = Ideal.Quotient.mk _ (X (.some j))
      rw [hypersurfaceToAway_mk]
      rw [show toAwayAux f i (X (Option.some j)) = algebraMap _ _
        (Ideal.Quotient.mk (Ideal.span {f}) (X j)) from MvPolynomial.aeval_X _ _]
      rw [hypersurfaceFromAway_algebraMap, hypersurfaceOfS_mk, rename_X]
  exact DFunLike.congr_fun h p

omit [Fintype σ] [DecidableEq σ] in
private lemma toAway_fromAway :
    (hypersurfaceToAway f i).comp (hypersurfaceFromAway f i) =
      AlgHom.id R (Localization.Away (Ideal.Quotient.mk (Ideal.span {f})
        (pderiv i f))) := by
  refine IsLocalization.algHom_ext
    (Submonoid.powers (Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f))) ?_
  refine AlgHom.ext fun s => ?_
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective s
  change hypersurfaceToAway f i (hypersurfaceFromAway f i
      (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {f}) q))) =
    algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {f}) q)
  rw [hypersurfaceFromAway_algebraMap, hypersurfaceOfS_mk, hypersurfaceToAway_mk,
    toAwayAux_rename]

/-- The model quotient `R[Option σ]/(f, X none·∂f - 1)` is the hypersurface
localized away from `∂f/∂Xᵢ`. -/
noncomputable def hypersurfaceAwayEquiv :
    HypersurfaceModel f i ≃ₐ[R] Localization.Away
      (Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f)) :=
  AlgEquiv.ofAlgHom (hypersurfaceToAway f i) (hypersurfaceFromAway f i)
    (toAway_fromAway f i) (fromAway_toAway f i)

omit [DecidableEq σ] in
/-- **Localized hypersurfaces are standard smooth** of relative dimension `#σ - 1`:
inverting a partial derivative of `f` on `R[Xⱼ]/(f)` yields a standard smooth
`R`-algebra. -/
theorem isStandardSmoothOfRelativeDimension_away_pderiv :
    Algebra.IsStandardSmoothOfRelativeDimension (Fintype.card σ - 1) R
      (Localization.Away (Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f))) :=
  haveI := hypersurfaceModel_isStandardSmoothOfRelativeDimension f i
  Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv _
    (hypersurfaceAwayEquiv f i)

end AwayEquiv

end ModularCurves
