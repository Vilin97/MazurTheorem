/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.AdmissibleCohomology
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfConnecting

/-!
# Quotient connecting homomorphisms and the low-degree sequence

An actual fppf quotient projection is itself a singleton fppf cover.  Pulling that cover back
along a global quotient section supplies canonical local lifts, so the choice-independent
construction in `FppfConnecting` gives the genuine connecting homomorphism.  This bridge also
packages the represented-point groups and global fppf `H¹` groups into the existing finite
`p`-group low-degree sequence.

The certified kernel property proves left injectivity and exactness at the middle degree-zero
term.  Exactness at the quotient degree-zero term and the two following `H¹` terms remains
explicit input: the two checked image-in-kernel laws do not masquerade as the missing reverse
inclusions.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme

universe u

variable {S : Scheme.{u}} {G H : FiniteFlatCommGroupScheme S} {f : G ⟶ H}

namespace FppfQuotientPresentation

variable {G : FiniteFlatCommGroupScheme S}

/-- The quotient projection itself, regarded as a singleton fppf cover of the quotient scheme. -/
abbrev projectCover (D : FppfQuotientPresentation G) :
    Scheme.Cover.{u} Scheme.fppfPrecoverage D.quotient.scheme := by
  letI : Flat (hom D.project) := D.project_flat
  letI : Surjective (hom D.project) := D.project_surjective
  letI : LocallyOfFinitePresentation (hom D.project) := D.project_lfp
  exact (hom D.project).cover ⟨D.project_flat, D.project_lfp⟩

/-- A checked fppf quotient projection is locally surjective on represented points.  The lift is
the second projection from the actual pullback of the quotient cover along the target section. -/
def locallyLiftable (D : FppfQuotientPresentation G) :
    D.kernelPresentation.LocallyLiftable.{u} where
  localLift q := by
    letI : Precoverage.IsStableUnderBaseChange Scheme.fppfPrecoverage :=
      Scheme.instIsStableUnderBaseChangeFppfPrecoverage
    let 𝒱 := D.projectCover
    let 𝒬 := 𝒱.pullback₁ q.left
    have hq : q.left ≫ D.quotient.structureMap = (baseObject S).hom :=
      Over.w q
    exact
      { cover := 𝒬
        lift := fun _ ↦
          Over.homMk (pullback.snd q.left (hom D.project)) (by
          change pullback.snd q.left (hom D.project) ≫ G.structureMap =
            pullback.fst q.left (hom D.project)
          rw [← hom_comp_structureMap D.project, ← Category.assoc,
            ← pullback.condition, Category.assoc, hq]
          change pullback.fst q.left (hom D.project) ≫ 𝟙 S =
            pullback.fst q.left (hom D.project)
          exact Category.comp_id _)
        maps_to := fun i ↦ by
          ext
          change pullback.snd q.left (hom D.project) ≫ hom D.project =
            (coverToBase 𝒬 i).left ≫ q.left
          exact (pullback.condition :
            pullback.fst q.left (hom D.project) ≫ q.left =
              pullback.snd q.left (hom D.project) ≫ hom D.project).symm
      }

/-- The canonical connecting homomorphism of an actual checked fppf quotient presentation.  Its
value is the kernel torsor of the tautological local lifts on the pulled-back quotient cover. -/
def boundaryHom (D : FppfQuotientPresentation G) :
    BasePoint D.quotient →* D.kernelPresentation.kernel.FppfHOne.{u} :=
  D.locallyLiftable.boundaryHom

@[simp]
theorem boundaryHom_apply (D : FppfQuotientPresentation G) (q : BasePoint D.quotient) :
    D.boundaryHom q = (D.locallyLiftable.localLift q).boundaryClass :=
  rfl

/-- A globally lifted quotient section has trivial connecting class. -/
@[simp]
theorem boundaryHom_project (D : FppfQuotientPresentation G) (x : BasePoint G) :
    D.boundaryHom (mapPoint D.project (baseObject S) x) = 1 :=
  D.locallyLiftable.boundaryHom_mapPoint x

/-- The constructed quotient boundary maps to zero after extending its kernel torsor to the
middle finite-flat group scheme. -/
@[simp]
theorem fppfHOneMap_boundaryHom (D : FppfQuotientPresentation G)
    (q : BasePoint D.quotient) :
    fppfHOneMap D.kernelPresentation.inclusion (D.boundaryHom q) = 1 :=
  D.locallyLiftable.fppfHOneMap_boundaryHom q

end FppfQuotientPresentation

namespace FinitePGroup

/-- Finiteness and a certified base-`p` logarithm for an already specified commutative group.
Unlike `FinitePGroup`, this structure does not replace the carrier by an abstract type, so it is
suited to packaging the actual represented-point and fppf-cohomology groups in a consumer. -/
structure CertifiedData (p : ℕ) (A : Type u) [CommGroup A] where
  finite : Finite A
  length : ℕ
  card_eq : Nat.card A = p ^ length

/-- Package certified data while preserving the specified carrier definitionally. -/
def CertifiedData.toFinitePGroup {p : ℕ} {A : Type u} [CommGroup A]
    (D : CertifiedData p A) : FinitePGroup p where
  carrier := A
  commGroup := inferInstance
  finite := D.finite
  length := D.length
  card_eq := D.card_eq

/-- Raise a certified carrier by one universe while preserving its cardinal certificate.  This
is needed because the global Čech quotient defining fppf `H¹` lives one universe above the
represented-point groups. -/
def CertifiedData.toULiftFinitePGroup {p : ℕ} {A : Type u} [CommGroup A]
    (D : CertifiedData p A) : FinitePGroup.{u + 1} p := by
  letI : Finite A := D.finite
  exact
    { carrier := ULift.{u + 1} A
      commGroup := inferInstance
      finite := inferInstance
      length := D.length
      card_eq := by
        rw [Nat.card_congr Equiv.ulift]
        exact D.card_eq }

/-- Raise both source and target of a homomorphism by one universe. -/
def uliftMonoidHom {A B : Type u} [CommGroup A] [CommGroup B] (g : A →* B) :
    ULift.{u + 1} A →* ULift.{u + 1} B :=
  MulEquiv.ulift.symm.toMonoidHom.comp
    (g.comp MulEquiv.ulift.toMonoidHom)

/-- Use a homomorphism on the underlying value of a universe-raised source. -/
def downMonoidHom {A : Type u} {B : Type (u + 1)} [CommGroup A] [CommGroup B]
    (g : A →* B) : ULift.{u + 1} A →* B :=
  g.comp MulEquiv.ulift.toMonoidHom

/-- Multiplicative exactness is unchanged when all three terms are universe-raised. -/
theorem mulExact_ulift {A B C : Type u} [CommGroup A] [CommGroup B] [CommGroup C]
    {g : A →* B} {h : B →* C} (e : Function.MulExact g h) :
    Function.MulExact (uliftMonoidHom g) (uliftMonoidHom h) := by
  rintro ⟨y⟩
  constructor
  · intro hy
    have hy' : h y = 1 := congrArg ULift.down hy
    obtain ⟨x, hx⟩ := (e y).mp hy'
    exact ⟨ULift.up x, by
      change ULift.up (g x) = ULift.up y
      rw [hx]⟩
  · rintro ⟨⟨x⟩, hx⟩
    have hx' : g x = y := congrArg ULift.down hx
    have hy : h y = 1 := (e y).mpr ⟨x, hx'⟩
    apply ULift.ext
    exact hy

/-- Raising only the source of the first map leaves exactness at its target unchanged. -/
theorem mulExact_downMonoidHom {A : Type u} {B C : Type (u + 1)}
    [CommGroup A] [CommGroup B] [CommGroup C]
    {g : A →* B} {h : B →* C} (e : Function.MulExact g h) :
    Function.MulExact (downMonoidHom g) h := by
  intro y
  rw [e y]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨ULift.up x, rfl⟩
  · rintro ⟨⟨x⟩, hx⟩
    exact ⟨x, hx⟩

/-- Injectivity is unchanged when a homomorphism is universe-raised. -/
theorem uliftMonoidHom_injective {A B : Type u} [CommGroup A] [CommGroup B]
    {g : A →* B} (hg : Function.Injective g) :
    Function.Injective (uliftMonoidHom g) := by
  rintro ⟨x⟩ ⟨y⟩ hxy
  apply ULift.ext
  exact hg (congrArg ULift.down hxy)

end FinitePGroup

namespace FppfLowDegreeExactSequence

/-- Build the concrete five-term group sequence attached to a certified finite-flat kernel and
its constructed connecting homomorphism.  The middle `H⁰` exactness and left injectivity are
discharged by the scheme-theoretic kernel universal property.  The three descent-sensitive
remaining exactness assertions stay explicit inputs; this constructor does not disguise them as
formal consequences of the group packages. -/
def ofKernelPresentation {p : ℕ} (P : KernelPresentation f)
    (E : P.LocallyLiftable.{u})
    (kernelHZeroData : FinitePGroup.CertifiedData p (BasePoint P.kernel))
    (middleHZeroData : FinitePGroup.CertifiedData p (BasePoint G))
    (quotientHZeroData : FinitePGroup.CertifiedData p (BasePoint H))
    (kernelHOneData : FinitePGroup.CertifiedData p P.kernel.FppfHOne.{u})
    (middleHOneData : FinitePGroup.CertifiedData p G.FppfHOne.{u})
    (quotientHOneData : FinitePGroup.CertifiedData p H.FppfHOne.{u})
    (exact_quotientHZero : Function.MulExact
      (FinitePGroup.uliftMonoidHom (mapPoint f (baseObject S)))
      (FinitePGroup.downMonoidHom E.boundaryHom))
    (exact_kernelHOne : Function.MulExact
      E.boundaryHom (fppfHOneMap P.inclusion))
    (exact_middleHOne : Function.MulExact
      (fppfHOneMap P.inclusion) (fppfHOneMap f)) :
    FppfLowDegreeExactSequence.{u + 1} p where
  kernelHZero := kernelHZeroData.toULiftFinitePGroup
  middleHZero := middleHZeroData.toULiftFinitePGroup
  quotientHZero := quotientHZeroData.toULiftFinitePGroup
  kernelHOne := kernelHOneData.toFinitePGroup
  middleHOne := middleHOneData.toFinitePGroup
  quotientHOne := quotientHOneData.toFinitePGroup
  includeHZero := FinitePGroup.uliftMonoidHom
    (mapPoint P.inclusion (baseObject S))
  projectHZero := FinitePGroup.uliftMonoidHom (mapPoint f (baseObject S))
  boundary := FinitePGroup.downMonoidHom E.boundaryHom
  includeHOne := fppfHOneMap P.inclusion
  projectHOne := fppfHOneMap f
  includeHZero_injective := FinitePGroup.uliftMonoidHom_injective
    (P.inclusion_point_injective (baseObject S))
  exact_middleHZero := FinitePGroup.mulExact_ulift
    (P.point_mulExact (baseObject S))
  exact_quotientHZero := exact_quotientHZero
  exact_kernelHOne := FinitePGroup.mulExact_downMonoidHom exact_kernelHOne
  exact_middleHOne := exact_middleHOne

/-- The concrete low-degree sequence constructor for an actual fppf quotient presentation.  It
uses the quotient's pulled-back singleton cover and the resulting checked boundary homomorphism;
only the three genuinely descent-sensitive full exactness statements remain arguments. -/
def ofFppfQuotientPresentation {p : ℕ} {G : FiniteFlatCommGroupScheme S}
    (D : FppfQuotientPresentation G)
    (kernelHZeroData : FinitePGroup.CertifiedData p
      (BasePoint D.kernelPresentation.kernel))
    (middleHZeroData : FinitePGroup.CertifiedData p (BasePoint G))
    (quotientHZeroData : FinitePGroup.CertifiedData p (BasePoint D.quotient))
    (kernelHOneData : FinitePGroup.CertifiedData p
      D.kernelPresentation.kernel.FppfHOne.{u})
    (middleHOneData : FinitePGroup.CertifiedData p G.FppfHOne.{u})
    (quotientHOneData : FinitePGroup.CertifiedData p D.quotient.FppfHOne.{u})
    (exact_quotientHZero : Function.MulExact
      (FinitePGroup.uliftMonoidHom (mapPoint D.project (baseObject S)))
      (FinitePGroup.downMonoidHom D.boundaryHom))
    (exact_kernelHOne : Function.MulExact D.boundaryHom
      (fppfHOneMap D.kernelPresentation.inclusion))
    (exact_middleHOne : Function.MulExact
      (fppfHOneMap D.kernelPresentation.inclusion) (fppfHOneMap D.project)) :
    FppfLowDegreeExactSequence.{u + 1} p :=
  ofKernelPresentation D.kernelPresentation D.locallyLiftable
    kernelHZeroData middleHZeroData quotientHZeroData
    kernelHOneData middleHOneData quotientHOneData
    exact_quotientHZero exact_kernelHOne exact_middleHOne

end FppfLowDegreeExactSequence

end AlgebraicGeometry.FiniteFlatCommGroupScheme
