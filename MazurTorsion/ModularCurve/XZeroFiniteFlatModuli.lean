/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.ConstantSections
import MazurTorsion.GroupTheory.IndependentCyclicGenerators
import MazurTorsion.ModularCurve.XZeroModuli
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Finite-flat split cyclic subgroup data for `X₀(N)`

The pinned Mathlib represents Weierstrass curves and their point groups by
coordinates, but does not construct the corresponding projective scheme or
its group-scheme law.  The project does, however, have genuine finite-flat
commutative group schemes, their base change, and explicit constant group
schemes.  This file connects those two layers without identifying them.

We first define an actual finite-locally-free closed subgroup of an arbitrary
commutative group scheme.  Over an affine base, a split cyclic subgroup is one
whose finite-flat carrier is isomorphic to the constant group scheme on
`ZMod N`.  This is a restricted `Γ₀(N)` datum: a general cyclic subgroup need
only become constant fppf-locally, and at primes dividing `N` the usual
generalized cyclicity condition requires still more care.

The final section records the precise remaining Weierstrass scheme interface:
a commutative group scheme with the expected rational point group.  The
extension of an injective finite constant family of rational sections to a
closed subgroup-scheme immersion is constructed in the imported finite-flat
group-scheme layer.  Given the remaining interface, a marked point of exact
order `N` constructs a genuine split finite-flat `Γ₀(N)` datum.  The checked
point comparison proves that its rational points recover exactly the existing
point-group carrier.

No representability of `X₀(N)`, elliptic quotient `E/C`, Atkin--Lehner action,
or closure of split data under that action is asserted here.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli

universe u

namespace CommGroupScheme

variable {S : Scheme.{u}}

/-- Points of an arbitrary commutative group scheme on a test scheme over the
same base. -/
abbrev Point (G : AlgebraicGeometry.CommGroupScheme S) (X : Over S) :=
  X ⟶ G.X

/-- The underlying scheme morphism of a commutative group-scheme morphism. -/
abbrev underlyingHom {G H : AlgebraicGeometry.CommGroupScheme S}
    (f : G ⟶ H) : G.X.left ⟶ H.X.left :=
  f.hom.hom.hom.left

/-- A commutative group-scheme morphism acts on every test-point group. -/
def mapPoint {G H : AlgebraicGeometry.CommGroupScheme S} (f : G ⟶ H)
    (X : Over S) : Point G X →* Point H X :=
  IsMonHom.monoidHom f.hom.hom.hom X

@[simp]
theorem mapPoint_apply {G H : AlgebraicGeometry.CommGroupScheme S}
    (f : G ⟶ H) (X : Over S) (x : Point G X) :
    mapPoint f X x = x ≫ f.hom.hom.hom :=
  rfl

end CommGroupScheme

section Subgroup

variable {S T : Scheme.{u}}
  (E : AlgebraicGeometry.CommGroupScheme S)

/-- A finite-locally-free closed subgroup of a commutative group scheme.

The carrier is a genuine finite-flat commutative group scheme and the
inclusion is a group-scheme morphism whose underlying scheme map is a closed
immersion. -/
structure FiniteLocallyFreeSubgroup where
  /-- The finite-flat carrier. -/
  carrier : AlgebraicGeometry.FiniteFlatCommGroupScheme S
  /-- Its homomorphism into the ambient group scheme. -/
  inclusion : carrier.obj ⟶ E
  /-- The homomorphism is a subgroup-scheme inclusion. -/
  inclusion_isClosedImmersion :
    IsClosedImmersion (CommGroupScheme.underlyingHom inclusion)

namespace FiniteLocallyFreeSubgroup

variable {E}

/-- Base change of a finite-locally-free closed subgroup. -/
def baseChange (C : FiniteLocallyFreeSubgroup E) (f : T ⟶ S) :
    FiniteLocallyFreeSubgroup ((Over.pullback f).mapCommGrp.obj E) where
  carrier :=
    (AlgebraicGeometry.FiniteFlatCommGroupScheme.baseChange f).obj C.carrier
  inclusion := (Over.pullback f).mapCommGrp.map C.inclusion
  inclusion_isClosedImmersion := by
    exact MorphismProperty.overPullbackMap f C.inclusion.hom.hom.hom
      C.inclusion_isClosedImmersion

@[simp]
theorem baseChange_carrier (C : FiniteLocallyFreeSubgroup E) (f : T ⟶ S) :
    (C.baseChange f).carrier =
      (AlgebraicGeometry.FiniteFlatCommGroupScheme.baseChange f).obj C.carrier :=
  rfl

@[simp]
theorem baseChange_inclusion (C : FiniteLocallyFreeSubgroup E) (f : T ⟶ S) :
    (C.baseChange f).inclusion = (Over.pullback f).mapCommGrp.map C.inclusion :=
  rfl

end FiniteLocallyFreeSubgroup

end Subgroup

section SplitCyclic

variable (K : Type u) [Field K]
  (N : ℕ) [NeZero N]

/-- Universe-compatible indexing group for the constant cyclic scheme. -/
abbrev CyclicIndex := ULift.{u} (Multiplicative (ZMod N))

/-- Forget the universe lift on the cyclic indexing group. -/
def cyclicIndexDown : CyclicIndex.{u} N →* Multiplicative (ZMod N) where
  toFun z := z.down
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Include the standard cyclic group into its universe lift. -/
def cyclicIndexUp : Multiplicative (ZMod N) →* CyclicIndex.{u} N where
  toFun z := ULift.up z
  map_one' := rfl
  map_mul' _ _ := rfl

omit [NeZero N] in
@[simp]
theorem cyclicIndexDown_up (z : Multiplicative (ZMod N)) :
    cyclicIndexDown.{u} N (cyclicIndexUp.{u} N z) = z :=
  rfl

/-- The constant finite-flat multiplicative group attached to the additive
cyclic group `ZMod N`. -/
abbrev cyclicConstant :
    AlgebraicGeometry.FiniteFlatCommGroupScheme
      (AlgebraicGeometry.Spec (.of K)) :=
  AlgebraicGeometry.FiniteFlatCommGroupScheme.constantScheme K
    (CyclicIndex.{u} N)

/-- The constant cyclic group scheme has geometric order `N`. -/
theorem cyclicConstant_orderAt
    (s : AlgebraicGeometry.Spec (.of K)) :
    (cyclicConstant K N).orderAt s = N := by
  simp [cyclicConstant]

/-- The constant cyclic group scheme has constant order `N`. -/
theorem cyclicConstant_hasConstantOrder :
    (cyclicConstant K N).HasConstantOrder N := by
  funext s
  exact cyclicConstant_orderAt K N s

variable {K N}
  (E : AlgebraicGeometry.CommGroupScheme
    (AlgebraicGeometry.Spec (.of K)))

/-- A split cyclic subgroup-scheme of order `N`.

Only existence of a constant trivialization is retained.  In particular this
structure does not choose a generator, as appropriate for `Γ₀(N)` rather than
`Γ₁(N)`. -/
structure SplitCyclicSubgroup
    extends FiniteLocallyFreeSubgroup E where
  /-- The carrier is a split constant cyclic group scheme. -/
  isSplit : Nonempty (toFiniteLocallyFreeSubgroup.carrier ≅ cyclicConstant K N)

namespace SplitCyclicSubgroup

variable {E}

/-- A split cyclic subgroup has constant geometric order `N`. -/
theorem hasConstantOrder (C : SplitCyclicSubgroup E (N := N)) :
    C.carrier.HasConstantOrder N := by
  obtain ⟨e⟩ := C.isSplit
  have he :=
    AlgebraicGeometry.FiniteFlatCommGroupScheme.orderAt_eq_of_iso e
  funext s
  rw [congrFun he s]
  exact cyclicConstant_orderAt K N s

/-- Scalar extension of a split cyclic subgroup remains split cyclic. -/
def baseChange {L : Type u} [Field L] [Algebra K L]
    (C : SplitCyclicSubgroup E (N := N)) :
    SplitCyclicSubgroup
      ((Over.pullback
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap K L)))).mapCommGrp.obj E)
      (N := N) where
  toFiniteLocallyFreeSubgroup :=
    C.toFiniteLocallyFreeSubgroup.baseChange
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap K L)))
  isSplit := by
    obtain ⟨e⟩ := C.isSplit
    exact ⟨
      (AlgebraicGeometry.FiniteFlatCommGroupScheme.baseChange
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap K L)))).mapIso e ≪≫
        AlgebraicGeometry.FiniteFlatCommGroupScheme.constantBaseChangeIso
          (R := K) (K := L) (CyclicIndex.{u} N)⟩

end SplitCyclicSubgroup

end SplitCyclic

section ConstantEmbedding

variable (K : Type u) [Field K]
  (E : AlgebraicGeometry.CommGroupScheme
    (AlgebraicGeometry.Spec (.of K)))
  (G : Type u) [CommGroup G] [Fintype G]

private abbrev baseTestObject :
    Over (AlgebraicGeometry.Spec (.of K)) :=
  AlgebraicGeometry.AffineCommGroupScheme.testObject (R := K) K

/-- The distinguished rational points of a constant group scheme form a
homomorphism from its indexing group. -/
def constantPointHom :
    G →* CommGroupScheme.Point
      (AlgebraicGeometry.FiniteFlatCommGroupScheme.constantScheme K G).obj
      (baseTestObject K) where
  toFun :=
    AlgebraicGeometry.FiniteFlatCommGroupScheme.constantGeometricPoint K G
  map_one' := by
    let x :=
      AlgebraicGeometry.FiniteFlatCommGroupScheme.constantGeometricPoint K G 1
    have h :=
      AlgebraicGeometry.FiniteFlatCommGroupScheme.constantPoint_mul K G 1 1
    have hone : (1 : G) * 1 = 1 := one_mul 1
    rw [hone] at h
    change x = x * x at h
    apply mul_left_cancel (a := x)
    simpa using h.symm
  map_mul' :=
    AlgebraicGeometry.FiniteFlatCommGroupScheme.constantPoint_mul K G

variable (f : G →* CommGroupScheme.Point E (baseTestObject K))

/-- A scheme-theoretic extension of an injective finite family of rational
group sections.

This is the exact construction supplied by a separated group-scheme model:
the constant finite-flat group maps into the ambient group scheme, its map is
a closed immersion, and it agrees with the given sections on rational points.
-/
structure ConstantClosedEmbedding where
  /-- The group-scheme morphism extending the rational sections. -/
  hom :
    (AlgebraicGeometry.FiniteFlatCommGroupScheme.constantScheme K G).obj ⟶ E
  /-- Distinct constant sections form a closed finite subgroup. -/
  hom_isClosedImmersion :
    IsClosedImmersion (CommGroupScheme.underlyingHom hom)
  /-- The extension agrees with every distinguished constant point. -/
  map_constantPoint : ∀ g : G,
    CommGroupScheme.mapPoint hom (baseTestObject K)
        (AlgebraicGeometry.FiniteFlatCommGroupScheme.constantGeometricPoint K G g) =
      f g

/-- An injective finite group of rational sections gives a closed constant
subgroup scheme.  The group-scheme homomorphism and its closed-immersion proof
are supplied by the checked componentwise extension theorem. -/
def constantClosedEmbeddingOfInjective
    (hinj : Function.Injective f) :
    ConstantClosedEmbedding K E G f where
  hom :=
    AlgebraicGeometry.FiniteFlatCommGroupScheme.extendConstantHom K E G f
  hom_isClosedImmersion :=
    AlgebraicGeometry.FiniteFlatCommGroupScheme.extendConstantHom_isClosedImmersion
      K E G f hinj
  map_constantPoint :=
    AlgebraicGeometry.FiniteFlatCommGroupScheme.extendConstantHom_map_point
      K E G f

namespace ConstantClosedEmbedding

variable {K E G f}

/-- A constant closed embedding of `ZMod N` is a split cyclic subgroup. -/
def toSplitCyclicSubgroup
    {N : ℕ} [NeZero N]
    {f : CyclicIndex.{u} N →*
      CommGroupScheme.Point E (baseTestObject K)}
    (D : ConstantClosedEmbedding K E (CyclicIndex.{u} N) f) :
    SplitCyclicSubgroup E (N := N) where
  carrier := cyclicConstant K N
  inclusion := D.hom
  inclusion_isClosedImmersion := D.hom_isClosedImmersion
  isSplit := ⟨Iso.refl _⟩

end ConstantClosedEmbedding

end ConstantEmbedding

section WeierstrassInterface

open XZeroModuli

variable {K : Type u} [Field K] [DecidableEq K]
  {N : ℕ} [NeZero N]
  (W : WeierstrassCurve K) [W.IsElliptic]

/-- The exact scheme-theoretic interface still missing from the pinned
Weierstrass-coordinate API: a commutative group scheme whose rational points
are the checked coordinate point group. -/
structure WeierstrassGroupSchemeInterface where
  /-- The projective commutative group scheme associated to `W`. -/
  groupScheme : AlgebraicGeometry.CommGroupScheme
    (AlgebraicGeometry.Spec (.of K))
  /-- Comparison between checked coordinate points and scheme-valued rational
  points. -/
  rationalPointEquiv :
    Multiplicative W.toAffine.Point ≃*
      CommGroupScheme.Point groupScheme (baseTestObject K)

namespace WeierstrassGroupSchemeInterface

/-- Extend an injective finite family of coordinate points to a closed
constant subgroup of the associated group scheme. -/
def extendConstant
    {W' : WeierstrassCurve K}
    (M : WeierstrassGroupSchemeInterface W')
    (G : Type u) [CommGroup G] [Fintype G]
    (f : G →* Multiplicative W'.toAffine.Point)
    (hinj : Function.Injective f) :
    ConstantClosedEmbedding K M.groupScheme G
      (M.rationalPointEquiv.toMonoidHom.comp f) :=
  constantClosedEmbeddingOfInjective K M.groupScheme G
    (M.rationalPointEquiv.toMonoidHom.comp f) (by
      intro a b hab
      exact hinj (M.rationalPointEquiv.injective hab))

/-- The additive homomorphism sending `1 : ZMod N` to a point killed by
`N`. -/
def torsionAddHom (P : W.toAffine.Point)
    (hP : addOrderOf P = N) :
    ZMod N →+ W.toAffine.Point := by
  have hzero : N • P = 0 := by
    rw [← hP]
    exact addOrderOf_nsmul_eq_zero P
  exact MazurTorsion.IndependentCyclicGenerators.zmodHom N P hzero

/-- The universe-lifted multiplicative parameterization used by the constant
group-scheme construction. -/
def torsionParameterization (P : W.toAffine.Point)
    (hP : addOrderOf P = N) :
    CyclicIndex.{u} N →* Multiplicative W.toAffine.Point :=
  (torsionAddHom W P hP).toMultiplicative.comp
    (cyclicIndexDown.{u} N)

omit [NeZero N] [W.IsElliptic] in
/-- Exact order makes the constant cyclic parameterization injective. -/
theorem torsionParameterization_injective (P : W.toAffine.Point)
    (hP : addOrderOf P = N) :
    Function.Injective (torsionParameterization W P hP) := by
  have hzero : N • P = 0 := by
    rw [← hP]
    exact addOrderOf_nsmul_eq_zero P
  intro a b hab
  have hz : a.down.toAdd = b.down.toAdd :=
    (MazurTorsion.IndependentCyclicGenerators.zmodHom_injective
      N P hzero hP) (congrArg Multiplicative.toAdd hab)
  exact ULift.ext a b (Multiplicative.ext hz)

omit [NeZero N] [W.IsElliptic] in
@[simp]
theorem torsionParameterization_one (P : W.toAffine.Point)
    (hP : addOrderOf P = N) :
    torsionParameterization W P hP
        (cyclicIndexUp.{u} N (Multiplicative.ofAdd 1)) =
      Multiplicative.ofAdd P := by
  have hzero : N • P = 0 := by
    rw [← hP]
    exact addOrderOf_nsmul_eq_zero P
  exact congrArg Multiplicative.ofAdd
    (MazurTorsion.IndependentCyclicGenerators.zmodHom_one N P hzero)

omit [NeZero N] [W.IsElliptic] in
/-- The point-group image of the cyclic parameterization is exactly the
subgroup generated by `P`. -/
theorem torsionParameterization_additive_range (P : W.toAffine.Point)
    (hP : addOrderOf P = N) :
    (torsionAddHom W P hP).range =
      AddSubgroup.zmultiples P := by
  have hzero : N • P = 0 := by
    rw [← hP]
    exact addOrderOf_nsmul_eq_zero P
  apply le_antisymm
  · rintro x ⟨z, rfl⟩
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
    rw [torsionAddHom,
      MazurTorsion.IndependentCyclicGenerators.zmodHom_intCast]
    exact AddSubgroup.zsmul_mem_zmultiples P k
  · apply AddSubgroup.zmultiples_le_of_mem
    refine ⟨1, ?_⟩
    unfold torsionAddHom
    convert MazurTorsion.IndependentCyclicGenerators.zmodHom_one
      N P hzero using 1

/-- A split finite-flat `Γ₀(N)` source datum relative to a supplied
Weierstrass group-scheme interface.  This is deliberately not named a full
`X₀(N)` point. -/
structure SplitGammaZeroDatum
    (M : WeierstrassGroupSchemeInterface W) where
  /-- The finite-locally-free split cyclic subgroup. -/
  subgroup : SplitCyclicSubgroup M.groupScheme (N := N)

/-- A marked rational point of exact order `N` constructs a genuine split
finite-flat cyclic subgroup-scheme after the missing Weierstrass scheme
interface is supplied. -/
def splitGammaZeroDatumOfTorsion
    (M : WeierstrassGroupSchemeInterface W)
    (P : W.toAffine.Point) (hP : addOrderOf P = N) :
    SplitGammaZeroDatum W M (N := N) where
  subgroup :=
    (M.extendConstant (CyclicIndex.{u} N)
      (torsionParameterization W P hP)
      (torsionParameterization_injective W P hP)).toSplitCyclicSubgroup

omit [W.IsElliptic] in
/-- The constructed subgroup-scheme has constant geometric order `N`. -/
theorem splitGammaZeroDatumOfTorsion_hasConstantOrder
    (M : WeierstrassGroupSchemeInterface W)
    (P : W.toAffine.Point) (hP : addOrderOf P = N) :
    (splitGammaZeroDatumOfTorsion W M P hP).subgroup.carrier.HasConstantOrder N :=
  (splitGammaZeroDatumOfTorsion W M P hP).subgroup.hasConstantOrder

omit [W.IsElliptic] in
/-- The constructed closed subgroup sends every constant point `z` to the
corresponding multiple of `P` under the rational-point comparison. -/
theorem splitGammaZeroDatumOfTorsion_map_constantPoint
    (M : WeierstrassGroupSchemeInterface W)
    (P : W.toAffine.Point) (hP : addOrderOf P = N)
    (z : CyclicIndex.{u} N) :
    CommGroupScheme.mapPoint
        (splitGammaZeroDatumOfTorsion W M P hP).subgroup.inclusion
        (baseTestObject K)
        (AlgebraicGeometry.FiniteFlatCommGroupScheme.constantGeometricPoint
          K (CyclicIndex.{u} N) z) =
      M.rationalPointEquiv (torsionParameterization W P hP z) := by
  exact (M.extendConstant (CyclicIndex.{u} N)
    (torsionParameterization W P hP)
    (torsionParameterization_injective W P hP)).map_constantPoint z

omit [W.IsElliptic] in
/-- In particular, the distinguished constant generator maps to the marked
rational torsion point. -/
theorem splitGammaZeroDatumOfTorsion_map_one
    (M : WeierstrassGroupSchemeInterface W)
    (P : W.toAffine.Point) (hP : addOrderOf P = N) :
    CommGroupScheme.mapPoint
        (splitGammaZeroDatumOfTorsion W M P hP).subgroup.inclusion
        (baseTestObject K)
        (AlgebraicGeometry.FiniteFlatCommGroupScheme.constantGeometricPoint
          K (CyclicIndex.{u} N)
            (cyclicIndexUp.{u} N (Multiplicative.ofAdd 1))) =
      M.rationalPointEquiv (Multiplicative.ofAdd P) := by
  rw [splitGammaZeroDatumOfTorsion_map_constantPoint,
    torsionParameterization_one]

/-- Pull the constructed subgroup's rational constant points back through the
model comparison. -/
def splitGammaZeroDatumPointMonoidHom
    (M : WeierstrassGroupSchemeInterface W)
    (P : W.toAffine.Point) (hP : addOrderOf P = N) :
    CyclicIndex.{u} N →* Multiplicative W.toAffine.Point :=
  M.rationalPointEquiv.symm.toMonoidHom.comp <|
    (CommGroupScheme.mapPoint
      (splitGammaZeroDatumOfTorsion W M P hP).subgroup.inclusion
      (baseTestObject K)).comp <|
    constantPointHom K (CyclicIndex.{u} N)

omit [W.IsElliptic] in
/-- The pulled-back scheme-point map is the original constant cyclic
parameterization. -/
theorem splitGammaZeroDatumPointMonoidHom_eq
    (M : WeierstrassGroupSchemeInterface W)
    (P : W.toAffine.Point) (hP : addOrderOf P = N) :
    splitGammaZeroDatumPointMonoidHom W M P hP =
      torsionParameterization W P hP := by
  apply MonoidHom.ext
  intro z
  change M.rationalPointEquiv.symm
      (CommGroupScheme.mapPoint
        (splitGammaZeroDatumOfTorsion W M P hP).subgroup.inclusion
        (baseTestObject K)
        (AlgebraicGeometry.FiniteFlatCommGroupScheme.constantGeometricPoint
          K (CyclicIndex.{u} N) z)) = torsionParameterization W P hP z
  apply M.rationalPointEquiv.injective
  rw [M.rationalPointEquiv.apply_symm_apply]
  exact splitGammaZeroDatumOfTorsion_map_constantPoint W M P hP z

/-- Pulling back along the canonical universe lift gives an additive map on
`ZMod N`. -/
def splitGammaZeroDatumPointHom
    (M : WeierstrassGroupSchemeInterface W)
    (P : W.toAffine.Point) (hP : addOrderOf P = N) :
    ZMod N →+ W.toAffine.Point where
  toFun z := Multiplicative.toAdd
    (splitGammaZeroDatumPointMonoidHom W M P hP
      (cyclicIndexUp.{u} N (Multiplicative.ofAdd z)))
  map_zero' := by
    change Multiplicative.toAdd
      (splitGammaZeroDatumPointMonoidHom W M P hP
        (cyclicIndexUp.{u} N (Multiplicative.ofAdd 0))) = 0
    rw [show cyclicIndexUp.{u} N (Multiplicative.ofAdd (0 : ZMod N)) = 1 by rfl,
      (splitGammaZeroDatumPointMonoidHom W M P hP).map_one]
    exact toAdd_one (α := W.toAffine.Point)
  map_add' x y := by
    change Multiplicative.toAdd
        (splitGammaZeroDatumPointMonoidHom W M P hP
          (cyclicIndexUp.{u} N (Multiplicative.ofAdd (x + y)))) =
      Multiplicative.toAdd
          (splitGammaZeroDatumPointMonoidHom W M P hP
            (cyclicIndexUp.{u} N (Multiplicative.ofAdd x))) +
        Multiplicative.toAdd
          (splitGammaZeroDatumPointMonoidHom W M P hP
            (cyclicIndexUp.{u} N (Multiplicative.ofAdd y)))
    rw [show Multiplicative.ofAdd (x + y) =
        Multiplicative.ofAdd x * Multiplicative.ofAdd y by rfl,
      map_mul, map_mul]
    exact toAdd_mul _ _

omit [W.IsElliptic] in
/-- The scheme-theoretically constructed additive rational-point map is the
original homomorphism sending `1` to `P`. -/
theorem splitGammaZeroDatumPointHom_eq
    (M : WeierstrassGroupSchemeInterface W)
    (P : W.toAffine.Point) (hP : addOrderOf P = N) :
    splitGammaZeroDatumPointHom W M P hP = torsionAddHom W P hP := by
  ext z
  change Multiplicative.toAdd
      (splitGammaZeroDatumPointMonoidHom W M P hP
        (cyclicIndexUp.{u} N (Multiplicative.ofAdd z))) = _
  rw [splitGammaZeroDatumPointMonoidHom_eq]
  rfl

omit [W.IsElliptic] in
/-- The rational point image of the constructed finite-flat subgroup is
exactly the carrier used by the existing split point-level `Γ₀(N)` datum. -/
theorem splitGammaZeroDatumPointHom_range
    (M : WeierstrassGroupSchemeInterface W)
    (P : W.toAffine.Point) (hP : addOrderOf P = N) :
    (splitGammaZeroDatumPointHom W M P hP).range =
      (RationalCyclicSubgroup.ofPoint P hP).carrier := by
  rw [splitGammaZeroDatumPointHom_eq,
    torsionParameterization_additive_range,
    RationalCyclicSubgroup.ofPoint_carrier]

end WeierstrassGroupSchemeInterface

end WeierstrassInterface

end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
