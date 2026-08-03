/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.SupportedFppfCokernel

/-!
# Localization of bad-fibre fppf quotient sheaves

The quotient sheaves constructed in `SupportedFppfCokernel` vanish after restriction to the
principal open complement of the bad fibre.  This file packages that condition as an honest full
subcategory of fppf sheaves and derives the localization interface needed in Mazur's page-49
argument.

For an open subscheme `U ⊆ S`, Mathlib's functor on relative fppf sites is both continuous and
cocontinuous.  Its sheaf restriction functor is consequently a left adjoint, so it preserves
finite colimits; it already preserves all limits.  It therefore preserves exact sequences of
abelian sheaves.  Applying this to the checked point-cokernel sequence proves that its restriction
to `U` remains exact.  If the quotient is supported on the closed complement, exactness makes the
restricted subgroup map epic.  Open subgroup inclusions are also monic on represented point
sheaves, hence that restricted map is an isomorphism.

For a level element `level : R`, `levelClosedFiber level` is the actual closed subscheme
`Spec (R / (level))`; its closed immersion has range `V(level)`, the complement of `D(level)`.
The constant-flat and multiplicative-flat quotient sheaves are packaged in the supported full
subcategory, and both localization isomorphisms are constructed as concrete consumers.

There is currently no open-closed recollement or extension-by-zero API for fppf sheaves in the
checked Mathlib dependency.  Accordingly, this file does **not** claim that a supported quotient
is a pushforward from the closed fibre, nor that it is representable.  The boundary proved here is
the exact categorical support statement: restriction to the open complement is zero, the
restricted sequence is exact, and the two represented terms become isomorphic there.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.CommGroupScheme

universe u

variable {S : Scheme.{u}} {G H : CommGroupScheme S}

/-! ### Sheaves supported on a closed complement -/

/-- The property that an fppf sheaf on `S` is supported on the closed complement of `U`: its
restriction to the relative fppf site over `U` is zero. -/
def fppfSheafSupportedOnClosedComplementProperty (U : S.Opens) :
    ObjectProperty
      (Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}) :=
  fun F ↦ IsZero ((Scheme.fppfTopology.overMapPullback
    AddCommGrpCat.{u + 1} U.ι).obj F)

/-- The full subcategory of abelian fppf sheaves supported on the closed complement of `U`.
Membership is the checked vanishing of restriction, not a representability assertion. -/
abbrev SupportedFppfSheafOnClosedComplement (U : S.Opens) :=
  (fppfSheafSupportedOnClosedComplementProperty U).FullSubcategory

/-- Package a point-cokernel sheaf whose restriction to `U` has been proved zero as a sheaf
supported on the closed complement. -/
noncomputable def pointCokernelSupportedFppfSheaf
    (f : G ⟶ H) (U : S.Opens)
    (h : IsZero (pointCokernelFppfSheafOverOpen f U)) :
    SupportedFppfSheafOnClosedComplement U :=
  ⟨pointCokernelFppfSheaf f, h⟩

@[simp]
theorem pointCokernelSupportedFppfSheaf_obj
    (f : G ⟶ H) (U : S.Opens)
    (h : IsZero (pointCokernelFppfSheafOverOpen f U)) :
    (pointCokernelSupportedFppfSheaf f U h).obj = pointCokernelFppfSheaf f :=
  rfl

/-! ### Exact restriction and the localization isomorphism -/

/-- Restriction along an open immersion preserves finite colimits of abelian fppf sheaves.

This is derived from the continuous-cocontinuous sheaf adjunction for `Over.map U.ι`; it is not
an assumed exactness field. -/
noncomputable instance fppfOverOpenRestriction_preservesFiniteColimits (U : S.Opens) :
    PreservesFiniteColimits
      (Scheme.fppfTopology.overMapPullback AddCommGrpCat.{u + 1} U.ι) := by
  let F := Scheme.fppfTopology.overMapPullback AddCommGrpCat.{u + 1} U.ι
  let adj := (Over.map U.ι).sheafAdjunctionCocontinuous
    AddCommGrpCat.{u + 1}
    (Scheme.fppfTopology.over U.toScheme)
    (Scheme.fppfTopology.over S)
  letI : F.IsLeftAdjoint := adj.isLeftAdjoint
  infer_instance

/-- The represented additive point sheaf restricted to an open subscheme. -/
noncomputable abbrev addPointFppfSheafOverOpen (G : CommGroupScheme S) (U : S.Opens) :
    Sheaf (Scheme.fppfTopology.over U.toScheme) AddCommGrpCat.{u + 1} :=
  (Scheme.fppfTopology.overMapPullback AddCommGrpCat.{u + 1} U.ι).obj
    (addPointFppfSheaf G)

/-- The map of represented additive point sheaves after restriction to an open subscheme. -/
noncomputable abbrev addPointFppfMapOverOpen (f : G ⟶ H) (U : S.Opens) :
    addPointFppfSheafOverOpen G U ⟶ addPointFppfSheafOverOpen H U :=
  (Scheme.fppfTopology.overMapPullback AddCommGrpCat.{u + 1} U.ι).map
    (addPointFppfMap f)

/-- Restriction of the point-cokernel sequence to the relative fppf site over `U`. -/
noncomputable def pointCokernelFppfSequenceOverOpen (f : G ⟶ H) (U : S.Opens) :
    ShortComplex
      (Sheaf (Scheme.fppfTopology.over U.toScheme) AddCommGrpCat.{u + 1}) :=
  (pointCokernelFppfSequence f).map
    (Scheme.fppfTopology.overMapPullback AddCommGrpCat.{u + 1} U.ι)

/-- Open-site restriction preserves the checked point-cokernel exact sequence. -/
theorem pointCokernelFppfSequenceOverOpen_exact (f : G ⟶ H) (U : S.Opens) :
    (pointCokernelFppfSequenceOverOpen f U).Exact :=
  (pointCokernelFppfSequence_exact f).map _

/-- A monomorphism of the underlying schemes is injective on every test-scheme point set. -/
theorem mapPoint_injective_of_mono
    (f : G ⟶ H) [Mono f.hom.hom.hom.left] (T : Over S) :
    Function.Injective (mapPoint f T) := by
  letI : Mono f.hom.hom.hom := Over.mono_of_mono_left _
  intro x y h
  apply (cancel_mono f.hom.hom.hom).1
  exact h

/-- A monomorphism of the underlying schemes induces a monomorphism of represented additive
point fppf sheaves. -/
theorem addPointFppfMap_mono_of_mono
    (f : G ⟶ H) [Mono f.hom.hom.hom.left] :
    Mono (addPointFppfMap f) := by
  haveI : Mono (commPointPresheafMap f) := by
    rw [NatTrans.mono_iff_mono_app]
    intro T
    apply ConcreteCategory.mono_of_injective
    exact mapPoint_injective_of_mono f T.unop
  haveI : Mono (addPointPresheafMap f) := by
    dsimp [addPointPresheafMap]
    infer_instance
  dsimp [addPointFppfMap]
  infer_instance

/-- For a monic group-scheme map, the point-cokernel construction is a short exact sequence of
fppf sheaves, not merely an exact pair at the middle term. -/
theorem pointCokernelFppfSequence_shortExact_of_mono
    (f : G ⟶ H) [Mono f.hom.hom.hom.left] :
    (pointCokernelFppfSequence f).ShortExact := by
  haveI : Mono (addPointFppfMap f) := addPointFppfMap_mono_of_mono f
  exact
    { exact := pointCokernelFppfSequence_exact f
      mono_f := by
        change Mono (addPointFppfMap f)
        infer_instance
      epi_g := by
        change Epi (pointCokernelFppfProjection f)
        infer_instance }

/-- The short exact point-cokernel sequence stays short exact after open-site restriction. -/
theorem pointCokernelFppfSequenceOverOpen_shortExact_of_mono
    (f : G ⟶ H) [Mono f.hom.hom.hom.left] (U : S.Opens) :
    (pointCokernelFppfSequenceOverOpen f U).ShortExact :=
  (pointCokernelFppfSequence_shortExact_of_mono f).map_of_exact _

/-- If the point-cokernel sheaf is supported on the closed complement of `U`, then the subgroup
map on represented point sheaves becomes an isomorphism over `U`. -/
theorem addPointFppfMapOverOpen_isIso_of_supported
    (f : G ⟶ H) [Mono f.hom.hom.hom.left] (U : S.Opens)
    (h : IsZero (pointCokernelFppfSheafOverOpen f U)) :
    IsIso (addPointFppfMapOverOpen f U) := by
  let F := Scheme.fppfTopology.overMapPullback AddCommGrpCat.{u + 1} U.ι
  haveI : Mono (addPointFppfMap f) := addPointFppfMap_mono_of_mono f
  haveI : Mono (F.map (addPointFppfMap f)) := by infer_instance
  haveI : Epi (F.map (addPointFppfMap f)) := by
    apply (pointCokernelFppfSequenceOverOpen_exact f U).epi_f
    exact h.eq_zero_of_tgt _
  exact isIso_of_mono_of_epi _

end AlgebraicGeometry.CommGroupScheme

namespace AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme

universe u

open CommGroupScheme

/-! ### The actual bad closed fibre -/

/-- The closed fibre cut out by a level element. -/
noncomputable abbrev levelClosedFiber {R : Type u} [CommRing R] (level : R) : Scheme :=
  Spec (.of (R ⧸ Ideal.span {level}))

/-- The canonical closed immersion of the level fibre into the affine base. -/
noncomputable def levelClosedFiberι {R : Type u} [CommRing R] (level : R) :
    levelClosedFiber level ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {level})))

instance levelClosedFiberι_isClosedImmersion
    {R : Type u} [CommRing R] (level : R) :
    IsClosedImmersion (levelClosedFiberι level) := by
  dsimp [levelClosedFiberι]
  exact IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of R)
    (Ideal.span ({level} : Set R))

/-- The closed level fibre has exactly the expected underlying set `V(level)`. -/
theorem levelClosedFiberι_range
    {R : Type u} [CommRing R] (level : R) :
    Set.range (levelClosedFiberι level) = PrimeSpectrum.zeroLocus {level} := by
  dsimp [levelClosedFiberι]
  change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {level}))) = _
  rw [range_comap_of_surjective (R ⧸ Ideal.span {level})
      (Ideal.Quotient.mk (Ideal.span {level})) Ideal.Quotient.mk_surjective,
    Ideal.mk_ker, PrimeSpectrum.zeroLocus_span]

/-- The principal open `D(level)` is the complement of the underlying closed level fibre. -/
theorem levelOpen_complement_eq_levelClosedFiberι_range
    {R : Type u} [CommRing R] (level : R) :
    ((levelOpen level : Set (Spec (.of R)))ᶜ) =
      Set.range (levelClosedFiberι level) := by
  rw [levelClosedFiberι_range]
  change (PrimeSpectrum.basicOpen level : Set (PrimeSpectrum R))ᶜ = _
  rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl, compl_compl]

/-! ### Constant-flat consumer -/

section ConstantFlat

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]

/-- The constant-flat quotient sheaf, packaged as supported on the actual bad closed fibre. -/
noncomputable def constantFlatPointCokernelSupportedOnBadFiber (level : R) :
    SupportedFppfSheafOnClosedComplement (levelOpen level) :=
  pointCokernelSupportedFppfSheaf
    (constantFlatInclusion (G := G) level) (levelOpen level)
    (constantFlatPointCokernelFppfSheafAway_isZero (G := G) level)

@[simp]
theorem constantFlatPointCokernelSupportedOnBadFiber_obj (level : R) :
    (constantFlatPointCokernelSupportedOnBadFiber (G := G) level).obj =
      constantFlatPointCokernelFppfSheaf (G := G) level :=
  rfl

/-- The constant-flat point-cokernel sequence localized to `D(level)`. -/
noncomputable abbrev constantFlatPointCokernelFppfSequenceAway (level : R) :=
  pointCokernelFppfSequenceOverOpen
    (constantFlatInclusion (G := G) level) (levelOpen level)

/-- The localized constant-flat sequence remains exact. -/
theorem constantFlatPointCokernelFppfSequenceAway_exact (level : R) :
    (constantFlatPointCokernelFppfSequenceAway (G := G) level).Exact :=
  pointCokernelFppfSequenceOverOpen_exact _ _

/-- The localized constant-flat sequence is short exact. -/
theorem constantFlatPointCokernelFppfSequenceAway_shortExact (level : R) :
    (constantFlatPointCokernelFppfSequenceAway (G := G) level).ShortExact :=
  pointCokernelFppfSequenceOverOpen_shortExact_of_mono _ _

/-- The quotient term in the localized constant-flat sequence is zero. -/
theorem constantFlatPointCokernelFppfSequenceAway_X₃_isZero (level : R) :
    IsZero (constantFlatPointCokernelFppfSequenceAway (G := G) level).X₃ :=
  constantFlatPointCokernelFppfSheafAway_isZero (G := G) level

/-- Over `D(level)`, the constant-flat open subgroup and its ambient constant group define
isomorphic represented additive point fppf sheaves. -/
theorem constantFlatAddPointFppfMapAway_isIso (level : R) :
    IsIso (addPointFppfMapOverOpen
      (constantFlatInclusion (G := G) level) (levelOpen level)) :=
  addPointFppfMapOverOpen_isIso_of_supported _ _
    (constantFlatPointCokernelFppfSheafAway_isZero (G := G) level)

/-- The concrete localization isomorphism supplied by the preceding theorem. -/
noncomputable def constantFlatAddPointFppfIsoAway (level : R) :
    addPointFppfSheafOverOpen (constantFlat R G level).obj (levelOpen level) ≅
      addPointFppfSheafOverOpen
        (FiniteFlatCommGroupScheme.constantScheme R G).obj (levelOpen level) := by
  letI := constantFlatAddPointFppfMapAway_isIso (G := G) level
  exact asIso (addPointFppfMapOverOpen
    (constantFlatInclusion (G := G) level) (levelOpen level))

end ConstantFlat

/-! ### Multiplicative-flat consumer -/

section MultiplicativeFlat

variable {coeffPrime level : ℕ} [NeZero coeffPrime]

/-- The multiplicative-flat quotient sheaf, packaged as supported on the level closed fibre. -/
noncomputable def muFlatPointCokernelSupportedOnBadFiber
    (datum : MuFlatDatum coeffPrime level) :
    SupportedFppfSheafOnClosedComplement (levelOpen (level : ℤ)) :=
  pointCokernelSupportedFppfSheaf
    (muFlatInclusion coeffPrime level datum) (levelOpen (level : ℤ))
    (muFlatPointCokernelFppfSheafAway_isZero datum)

@[simp]
theorem muFlatPointCokernelSupportedOnBadFiber_obj
    (datum : MuFlatDatum coeffPrime level) :
    (muFlatPointCokernelSupportedOnBadFiber datum).obj =
      muFlatPointCokernelFppfSheaf datum :=
  rfl

/-- The multiplicative-flat point-cokernel sequence localized to `D(level)`. -/
noncomputable abbrev muFlatPointCokernelFppfSequenceAway
    (datum : MuFlatDatum coeffPrime level) :=
  pointCokernelFppfSequenceOverOpen
    (muFlatInclusion coeffPrime level datum) (levelOpen (level : ℤ))

/-- The localized multiplicative-flat sequence remains exact. -/
theorem muFlatPointCokernelFppfSequenceAway_exact
    (datum : MuFlatDatum coeffPrime level) :
    (muFlatPointCokernelFppfSequenceAway datum).Exact :=
  pointCokernelFppfSequenceOverOpen_exact _ _

/-- The localized multiplicative-flat sequence is short exact. -/
theorem muFlatPointCokernelFppfSequenceAway_shortExact
    (datum : MuFlatDatum coeffPrime level) :
    (muFlatPointCokernelFppfSequenceAway datum).ShortExact :=
  pointCokernelFppfSequenceOverOpen_shortExact_of_mono _ _

/-- The quotient term in the localized multiplicative-flat sequence is zero. -/
theorem muFlatPointCokernelFppfSequenceAway_X₃_isZero
    (datum : MuFlatDatum coeffPrime level) :
    IsZero (muFlatPointCokernelFppfSequenceAway datum).X₃ :=
  muFlatPointCokernelFppfSheafAway_isZero datum

/-- Over `D(level)`, the multiplicative-flat open subgroup and `mu_p` define isomorphic
represented additive point fppf sheaves. -/
theorem muFlatAddPointFppfMapAway_isIso
    (datum : MuFlatDatum coeffPrime level) :
    IsIso (addPointFppfMapOverOpen
      (muFlatInclusion coeffPrime level datum) (levelOpen (level : ℤ))) :=
  addPointFppfMapOverOpen_isIso_of_supported _ _
    (muFlatPointCokernelFppfSheafAway_isZero datum)

/-- The concrete multiplicative-flat localization isomorphism. -/
noncomputable def muFlatAddPointFppfIsoAway
    (datum : MuFlatDatum coeffPrime level) :
    addPointFppfSheafOverOpen (muFlat coeffPrime level datum).obj
        (levelOpen (level : ℤ)) ≅
      addPointFppfSheafOverOpen (FiniteFlatCommGroupScheme.muScheme ℤ coeffPrime).obj
        (levelOpen (level : ℤ)) := by
  letI := muFlatAddPointFppfMapAway_isIso datum
  exact asIso (addPointFppfMapOverOpen
    (muFlatInclusion coeffPrime level datum) (levelOpen (level : ℤ)))

end MultiplicativeFlat

end AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme
