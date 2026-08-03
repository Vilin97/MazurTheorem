/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Over
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.SupportedPointCokernel

/-!
# Fppf sheaf cokernels for bad-fibre quotient terms

Mazur's bad-level localization sequences have quotient terms which are fppf sheaves, even when
they are not represented by quasi-finite flat group schemes.  This file sheafifies the pointwise
cokernel constructed in `SupportedPointCokernel` and proves that the resulting projection is
locally surjective, epic, and the actual cokernel in an exact sequence.

The relative fppf site of schemes over `S : Scheme.{u}` is large enough that Mathlib's concrete
sheafification construction applies to `AddCommGrpCat.{u + 1}`, not directly to
`AddCommGrpCat.{u}`.  We therefore apply the standard fully faithful universe-lift functor before
sheafification.  The represented ambient point presheaf remains an fppf sheaf after this lift;
`representedAddPointFppfSheafIso` records its canonical identification with its sheafification.
No mathematical coefficient change is involved.

The constant-flat and multiplicative-flat sections provide concrete downstream consumers.  The
imported point-cokernel layer turns the checked `contains_levelOpen` inequalities into actual
point factorizations and proves objectwise vanishing on every test scheme over `D(level)`.  Here
we transport that vanishing through site restriction and sheafification, proving that the actual
fppf cokernel sheaves restrict to zero over `D(level)`.  Thus these quotient sheaves are genuinely
supported on the bad fibre; the next localization step is to control them there.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.CommGroupScheme

universe u

variable {S : Scheme.{u}} {G H : CommGroupScheme S}

/-- The represented additive point presheaf, lifted to the universe in which concrete
sheafification on the relative fppf site is available. -/
noncomputable abbrev addPointPresheafUlift (G : CommGroupScheme S) :
    Functor (Over S)ᵒᵖ AddCommGrpCat.{u + 1} :=
  addPointPresheaf G ⋙ AddCommGrpCat.uliftFunctor.{u + 1}

/-- Universe lifting preserves the representable fppf sheaf condition. -/
theorem addPointPresheafUlift_isFppfSheaf (G : CommGroupScheme S) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (addPointPresheafUlift G) := by
  apply (Presheaf.isSheaf_iff_isSheaf_forget (Scheme.fppfTopology.over S)
    (addPointPresheafUlift G) (forget AddCommGrpCat.{u + 1})).mpr
  rw [isSheaf_iff_isSheaf_of_type]
  exact (Presieve.isSheaf_comp_uliftFunctor_iff
    (Scheme.fppfTopology.over S)).2 G.pointPresheaf_isFppfSheaf

/-- The represented additive point fppf sheaf itself, before applying the chosen sheafification
functor. -/
noncomputable def representedAddPointFppfSheaf (G : CommGroupScheme S) :
    Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1} :=
  ⟨addPointPresheafUlift G, addPointPresheafUlift_isFppfSheaf G⟩

/-- The chosen sheafification of the represented additive point presheaf. -/
noncomputable abbrev addPointFppfSheaf (G : CommGroupScheme S) :
    Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1} :=
  (presheafToSheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).obj
    (addPointPresheafUlift G)

/-- A represented point sheaf is canonically isomorphic to its chosen sheafification. -/
noncomputable def representedAddPointFppfSheafIso (G : CommGroupScheme S) :
    representedAddPointFppfSheaf G ≅ addPointFppfSheaf G :=
  sheafificationIso (representedAddPointFppfSheaf G)

/-- The fppf sheafification of the pointwise cokernel of `f`.  This is an honest sheaf quotient;
no representability assertion is made. -/
noncomputable abbrev pointCokernelFppfSheaf (f : G ⟶ H) :
    Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1} :=
  (presheafToSheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).obj
    (pointCokernelPresheaf f ⋙ AddCommGrpCat.uliftFunctor.{u + 1})

/-- A test scheme over an open subscheme pulls that open back to its whole carrier. -/
theorem overMap_opensInclusion_preimage_eq_top (U : S.Opens)
    (T : Over U.toScheme) :
    ((Over.map U.ι).obj T).hom ⁻¹ᵁ U = ⊤ := by
  change (T.hom ≫ U.ι) ⁻¹ᵁ U = ⊤
  rw [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self]
  simp

/-- Restrict the universe-lifted point-cokernel presheaf along an open immersion. -/
def pointCokernelPresheafUliftOverOpen (f : G ⟶ H) (U : S.Opens) :
    (Over U.toScheme)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (Over.map U.ι).op ⋙
    (pointCokernelPresheaf f ⋙ AddCommGrpCat.uliftFunctor.{u + 1})

/-- Restriction of the actual fppf cokernel sheaf along an open immersion. -/
noncomputable abbrev pointCokernelFppfSheafOverOpen
    (f : G ⟶ H) (U : S.Opens) :
    Sheaf (Scheme.fppfTopology.over U.toScheme) AddCommGrpCat.{u + 1} :=
  (Scheme.fppfTopology.overMapPullback AddCommGrpCat.{u + 1} U.ι).obj
    (pointCokernelFppfSheaf f)

/-- If the restricted point-cokernel presheaf vanishes, then so does the restriction of its
actual fppf sheafification.  The comparison is the continuous-pushforward/sheafification
compatibility for the open-immersion map of relative sites. -/
theorem pointCokernelFppfSheafOverOpen_isZero
    (f : G ⟶ H) (U : S.Opens)
    (h : IsZero (pointCokernelPresheafUliftOverOpen f U)) :
    IsZero (pointCokernelFppfSheafOverOpen f U) := by
  let P : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
    pointCokernelPresheaf f ⋙ AddCommGrpCat.uliftFunctor.{u + 1}
  let F := Over.map U.ι
  let J := Scheme.fppfTopology.over U.toScheme
  let K := Scheme.fppfTopology.over S
  have hsheaf :
      IsZero ((presheafToSheaf J AddCommGrpCat.{u + 1}).obj (F.op ⋙ P)) :=
    Functor.map_isZero (presheafToSheaf J AddCommGrpCat.{u + 1}) h
  let e := F.pushforwardContinuousSheafificationCompatibility
    AddCommGrpCat.{u + 1} J K
  exact hsheaf.of_iso (e.app P).symm

/-- The map of represented point sheafifications induced by a commutative group-scheme map. -/
noncomputable abbrev addPointFppfMap (f : G ⟶ H) :
    addPointFppfSheaf G ⟶ addPointFppfSheaf H :=
  (presheafToSheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).map
    (Functor.whiskerRight (addPointPresheafMap f)
      AddCommGrpCat.uliftFunctor.{u + 1})

/-- The canonical projection from the ambient point sheafification to the fppf cokernel sheaf. -/
noncomputable abbrev pointCokernelFppfProjection (f : G ⟶ H) :
    addPointFppfSheaf H ⟶ pointCokernelFppfSheaf f :=
  (presheafToSheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).map
    (Functor.whiskerRight (pointCokernelProjection f)
      AddCommGrpCat.uliftFunctor.{u + 1})

/-- The fppf cokernel projection is genuinely locally surjective. -/
instance pointCokernelFppfProjection_isLocallySurjective (f : G ⟶ H) :
    Sheaf.IsLocallySurjective (pointCokernelFppfProjection f) := by
  rw [Presheaf.isLocallySurjective_presheafToSheaf_map_iff]
  apply Presheaf.isLocallySurjective_of_surjective
  intro T
  rw [← AddCommGrpCat.epi_iff_surjective]
  dsimp
  infer_instance

/-- Genuine local surjectivity makes the fppf cokernel projection an epimorphism of sheaves. -/
instance pointCokernelFppfProjection_epi (f : G ⟶ H) :
    Epi (pointCokernelFppfProjection f) := by
  apply Sheaf.epi_of_isLocallySurjective

/-- The canonical projection with source written as the actual represented ambient point sheaf. -/
noncomputable def representedPointCokernelFppfProjection (f : G ⟶ H) :
    representedAddPointFppfSheaf H ⟶ pointCokernelFppfSheaf f :=
  (representedAddPointFppfSheafIso H).hom ≫ pointCokernelFppfProjection f

instance representedPointCokernelFppfProjection_isLocallySurjective (f : G ⟶ H) :
    Sheaf.IsLocallySurjective (representedPointCokernelFppfProjection f) := by
  dsimp [representedPointCokernelFppfProjection]
  infer_instance

instance representedPointCokernelFppfProjection_epi (f : G ⟶ H) :
    Epi (representedPointCokernelFppfProjection f) := by
  apply Sheaf.epi_of_isLocallySurjective

/-- The short complex from the represented point sheafifications to their fppf cokernel sheaf. -/
noncomputable def pointCokernelFppfSequence (f : G ⟶ H) :
    ShortComplex (Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}) :=
  ShortComplex.mk (addPointFppfMap f) (pointCokernelFppfProjection f) (by
    rw [← Functor.map_comp]
    rw [← Functor.whiskerRight_comp]
    simp)

/-- Sheafification and universe lifting both preserve the actual pointwise cokernel, so the
resulting sequence of fppf sheaves is exact. -/
theorem pointCokernelFppfSequence_exact (f : G ⟶ H) :
    (pointCokernelFppfSequence f).Exact := by
  apply ShortComplex.exact_of_g_is_cokernel
  let c : CokernelCofork (addPointPresheafMap f) :=
    CokernelCofork.ofπ (pointCokernelProjection f) (cokernel.condition _)
  let U := (whiskeringRight (Over S)ᵒᵖ AddCommGrpCat.{u}
    AddCommGrpCat.{u + 1}).obj AddCommGrpCat.uliftFunctor.{u + 1}
  let c₁ := c.map U
  let c₂ := c₁.map
    (presheafToSheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1})
  change IsColimit c₂
  exact c₁.mapIsColimit
    (c.mapIsColimit (cokernelIsCokernel _) U)
    (presheafToSheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1})

end AlgebraicGeometry.CommGroupScheme

namespace AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme

universe u

open CommGroupScheme

/-- The principal open complement of a level, regarded as an open subscheme of the affine base. -/
abbrev levelOpen {R : Type u} [CommRing R] (level : R) :
    (Spec (.of R)).Opens :=
  PrimeSpectrum.basicOpen level

section ConstantFlat

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]

/-- The actual fppf cokernel sheaf attached to the constant-flat open subgroup. -/
noncomputable abbrev constantFlatPointCokernelFppfSheaf (level : R) :=
  pointCokernelFppfSheaf (constantFlatInclusion (G := G) level)

/-- The canonical locally-surjective map from the represented constant ambient point sheaf. -/
noncomputable abbrev constantFlatRepresentedPointCokernelFppfProjection (level : R) :=
  representedPointCokernelFppfProjection (constantFlatInclusion (G := G) level)

theorem constantFlatRepresentedPointCokernelFppfProjection_locallySurjective (level : R) :
    Sheaf.IsLocallySurjective
      (constantFlatRepresentedPointCokernelFppfProjection (G := G) level) :=
  inferInstance

theorem constantFlatRepresentedPointCokernelFppfProjection_epi (level : R) :
    Epi (constantFlatRepresentedPointCokernelFppfProjection (G := G) level) :=
  inferInstance

/-- The constant-flat fppf sheaf-cokernel sequence is categorically exact. -/
theorem constantFlatPointCokernelFppfSequence_exact (level : R) :
    (pointCokernelFppfSequence (constantFlatInclusion (G := G) level)).Exact :=
  pointCokernelFppfSequence_exact _

/-- Restriction of the constant-flat point-cokernel presheaf to `D(level)`. -/
def constantFlatPointCokernelPresheafAway (level : R) :
    (Over (levelOpen level).toScheme)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (Over.map (levelOpen level).ι).op ⋙
    constantFlatPointCokernelPresheaf (G := G) level

/-- The constant-flat point-cokernel presheaf vanishes after restriction to `D(level)`. -/
theorem constantFlatPointCokernelPresheafAway_isZero (level : R) :
    IsZero (constantFlatPointCokernelPresheafAway (G := G) level) := by
  apply Functor.isZero
  intro T
  exact constantFlatPointCokernelPresheaf_obj_isZero_away
    (G := G) level
    (Opposite.op ((Over.map (levelOpen level).ι).obj T.unop))
    (CommGroupScheme.overMap_opensInclusion_preimage_eq_top
      (levelOpen level) T.unop)

/-- Universe-lifted restriction used by concrete fppf sheafification. -/
def constantFlatPointCokernelPresheafUliftAway (level : R) :
    (Over (levelOpen level).toScheme)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  constantFlatPointCokernelPresheafAway (G := G) level ⋙
    AddCommGrpCat.uliftFunctor.{u + 1}

/-- Universe lifting preserves vanishing of the restricted constant-flat presheaf. -/
theorem constantFlatPointCokernelPresheafUliftAway_isZero (level : R) :
    IsZero (constantFlatPointCokernelPresheafUliftAway (G := G) level) := by
  apply Functor.isZero
  intro T
  exact Functor.map_isZero AddCommGrpCat.uliftFunctor.{u + 1}
    ((constantFlatPointCokernelPresheafAway_isZero (G := G) level).obj T)

/-- Restriction of the actual constant-flat fppf cokernel sheaf to `D(level)`. -/
noncomputable abbrev constantFlatPointCokernelFppfSheafAway (level : R) :
    Sheaf (Scheme.fppfTopology.over (levelOpen level).toScheme)
      AddCommGrpCat.{u + 1} :=
  CommGroupScheme.pointCokernelFppfSheafOverOpen
    (constantFlatInclusion (G := G) level) (levelOpen level)

/-- The actual constant-flat fppf cokernel sheaf is supported on the bad fibre: its restriction
to `D(level)` is zero. -/
theorem constantFlatPointCokernelFppfSheafAway_isZero (level : R) :
    IsZero (constantFlatPointCokernelFppfSheafAway (G := G) level) := by
  apply CommGroupScheme.pointCokernelFppfSheafOverOpen_isZero
  exact constantFlatPointCokernelPresheafUliftAway_isZero (G := G) level

end ConstantFlat

section MultiplicativeFlat

variable {coeffPrime level : ℕ} [NeZero coeffPrime]

/-- The actual fppf cokernel sheaf attached to the multiplicative-flat open subgroup. -/
noncomputable abbrev muFlatPointCokernelFppfSheaf
    (datum : MuFlatDatum coeffPrime level) :=
  pointCokernelFppfSheaf (muFlatInclusion coeffPrime level datum)

/-- The canonical locally-surjective map from the represented roots-of-unity point sheaf. -/
noncomputable abbrev muFlatRepresentedPointCokernelFppfProjection
    (datum : MuFlatDatum coeffPrime level) :=
  representedPointCokernelFppfProjection (muFlatInclusion coeffPrime level datum)

theorem muFlatRepresentedPointCokernelFppfProjection_locallySurjective
    (datum : MuFlatDatum coeffPrime level) :
    Sheaf.IsLocallySurjective
      (muFlatRepresentedPointCokernelFppfProjection datum) :=
  inferInstance

theorem muFlatRepresentedPointCokernelFppfProjection_epi
    (datum : MuFlatDatum coeffPrime level) :
    Epi (muFlatRepresentedPointCokernelFppfProjection datum) :=
  inferInstance

/-- The multiplicative-flat fppf sheaf-cokernel sequence is categorically exact. -/
theorem muFlatPointCokernelFppfSequence_exact
    (datum : MuFlatDatum coeffPrime level) :
    (pointCokernelFppfSequence (muFlatInclusion coeffPrime level datum)).Exact :=
  pointCokernelFppfSequence_exact _

/-- Restriction of the multiplicative-flat point-cokernel presheaf to `D(level)`. -/
def muFlatPointCokernelPresheafAway
    (datum : MuFlatDatum coeffPrime level) :=
  (Over.map (levelOpen (level : ℤ)).ι).op ⋙
    muFlatPointCokernelPresheaf datum

/-- The multiplicative-flat point-cokernel presheaf vanishes after restriction to `D(level)`. -/
theorem muFlatPointCokernelPresheafAway_isZero
    (datum : MuFlatDatum coeffPrime level) :
    IsZero (muFlatPointCokernelPresheafAway datum) := by
  apply Functor.isZero
  intro T
  exact muFlatPointCokernelPresheaf_obj_isZero_away datum
    (Opposite.op
      ((Over.map (levelOpen (level : ℤ)).ι).obj T.unop))
    (CommGroupScheme.overMap_opensInclusion_preimage_eq_top
      (levelOpen (level : ℤ)) T.unop)

/-- Universe-lifted restriction used by concrete fppf sheafification. -/
def muFlatPointCokernelPresheafUliftAway
    (datum : MuFlatDatum coeffPrime level) :=
  CommGroupScheme.pointCokernelPresheafUliftOverOpen
    (muFlatInclusion coeffPrime level datum)
    (levelOpen (level : ℤ))

/-- Universe lifting preserves vanishing of the restricted multiplicative-flat presheaf. -/
theorem muFlatPointCokernelPresheafUliftAway_isZero
    (datum : MuFlatDatum coeffPrime level) :
    IsZero (muFlatPointCokernelPresheafUliftAway datum) := by
  apply Functor.isZero
  intro T
  exact Functor.map_isZero AddCommGrpCat.uliftFunctor
    ((muFlatPointCokernelPresheafAway_isZero datum).obj T)

/-- Restriction of the actual multiplicative-flat fppf cokernel sheaf to `D(level)`. -/
noncomputable abbrev muFlatPointCokernelFppfSheafAway
    (datum : MuFlatDatum coeffPrime level) :=
  CommGroupScheme.pointCokernelFppfSheafOverOpen
    (muFlatInclusion coeffPrime level datum)
    (levelOpen (level : ℤ))

/-- The actual multiplicative-flat fppf cokernel sheaf is supported on the bad fibre: its
restriction to `D(level)` is zero. -/
theorem muFlatPointCokernelFppfSheafAway_isZero
    (datum : MuFlatDatum coeffPrime level) :
    IsZero (muFlatPointCokernelFppfSheafAway datum) := by
  apply CommGroupScheme.pointCokernelFppfSheafOverOpen_isZero
  exact muFlatPointCokernelPresheafUliftAway_isZero datum

end MultiplicativeFlat

end AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme
