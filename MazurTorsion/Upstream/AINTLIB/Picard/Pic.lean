/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Localization.Monoidal.Braided
import Mathlib.CategoryTheory.Monoidal.Skeleton
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SheafOfModulesMonoidal

/-!
# The Picard group of a scheme

Stage P2 of the AINTLIB ModularCurves T-PIC0 stream (GME 2.2.2, p. 108): the Picard
group. Source of record, verbatim: *"We write `E_T` for `E ×_S T` and `Pic(E_T)` for the
group of isomorphism classes of all invertible sheaves on `E_T`."*

With the [GAP1-W-MONO] leaf sorry-free (`sheafificationW_isMonoidal` +
`sheafificationW_isLocalization`), mathlib's `LocalizedMonoidal` hands the category of
sheaves of modules over a sheaf of commutative rings its symmetric monoidal structure —
the previously `Nonempty`-wrapped payoff, now as data (the v10.8 no-sorried-monoidal-DATA
discipline is satisfied, not bypassed). Following mathlib's own packaging
(`CategoryTheory.Sheaf.monoidalCategory` in `Sites/Monoidal.lean`) these are `def`s, not
global instances, to stay merge-safe against a future upstream instance.

The Picard group is then the group of ⊗-invertible iso-classes, following mathlib's
`CommRing.Pic` pattern (`RingTheory/PicardGroup.lean`): the units of the ⊗-monoid on the
skeleton, `Pic X := (Skeleton X.Modules)ˣ`. An element is an iso-class `[M]` together
with an inverse class; commutativity comes from the braiding.

## Main definitions

* `PresheafOfModules.sheafOfModulesMonoidalCategory` / `…SymmetricCategory`: the
  symmetric monoidal structure on `SheafOfModules` over a sheaf of commutative rings.
* `AlgebraicGeometry.Scheme.Modules.monoidalCategory` / `…symmetricCategory`: the same,
  on `X.Modules` for a scheme `X`.
* `AlgebraicGeometry.Scheme.Pic`: the Picard group of a scheme, with its `CommGroup`
  structure.

The comparison with the cover-local `IsInvertible` predicate of
`Picard/InvertibleSheaf.lean` — GME's "the formation of an invertible sheaf is local",
(2.17) — is the registered follow-up [PIC-P2-CMP]; its invertible-to-unit direction
constructs the dual sheaf, which is coordinated with the Cartier-duality lane
(v10.36 two-route edge: never build duality twice).
-/

universe u

open CategoryTheory MonoidalCategory

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  (S : Cᵒᵖ ⥤ CommRingCat.{u})
  (hS : Presheaf.IsSheaf J (S ⋙ forget₂ CommRingCat RingCat))

/-- **The monoidal category of sheaves of modules** over a sheaf of commutative rings:
mathlib's `LocalizedMonoidal` applied to the sheafification localization
(`sheafificationW_isLocalization`) with the ⊗-stable localizing class
(`sheafificationW_isMonoidal`, the [GAP1-W-MONO] leaf). A `def`, not an instance, per the
`CategoryTheory.Sheaf.monoidalCategory` precedent — activate with
`attribute [local instance]` or `letI`. -/
@[implicit_reducible]
noncomputable def sheafOfModulesMonoidalCategory :
    MonoidalCategory
      (SheafOfModules.{u} (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u})) :=
  inferInstanceAs (MonoidalCategory (LocalizedMonoidal
    (L := sheafification.{u}
      (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).obj))
    (W := sheafificationW.{u}
      (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).obj))
    (Iso.refl _)))

/-- The symmetric monoidal structure on sheaves of modules (the braiding descends from
the symmetric structure on presheaves of modules through the localization). -/
@[implicit_reducible]
noncomputable def sheafOfModulesSymmetricCategory :
    letI := sheafOfModulesMonoidalCategory S hS
    SymmetricCategory
      (SheafOfModules.{u} (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u})) :=
  inferInstanceAs (SymmetricCategory (LocalizedMonoidal
    (L := sheafification.{u}
      (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).obj))
    (W := sheafificationW.{u}
      (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).obj))
    (Iso.refl _)))

end PresheafOfModules

namespace AlgebraicGeometry.Scheme

namespace Modules

/-- The monoidal category structure on `𝒪ₓ`-modules (transport of
`PresheafOfModules.sheafOfModulesMonoidalCategory` across the structure-eta identification
`X.ringCatSheaf = ⟨X.sheaf.obj ⋙ forget₂, _⟩`). A `def`, not an instance — activate with
`letI` / `attribute [local instance]`. -/
@[implicit_reducible]
noncomputable def monoidalCategory (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  PresheafOfModules.sheafOfModulesMonoidalCategory X.sheaf.obj X.ringCatSheaf.property

/-- The symmetric monoidal structure on `𝒪ₓ`-modules. -/
@[implicit_reducible]
noncomputable def symmetricCategory (X : Scheme.{u}) :
    letI := monoidalCategory X
    SymmetricCategory X.Modules :=
  PresheafOfModules.sheafOfModulesSymmetricCategory X.sheaf.obj X.ringCatSheaf.property

end Modules

/-- **The Picard group of a scheme** (GME 2.2.2 (2.16), p. 108: `Pic(E_T)` is "the group
of isomorphism classes of all invertible sheaves") — following mathlib's `CommRing.Pic`
pattern, the units of the ⊗-monoid of iso-classes of `𝒪ₓ`-modules: an element is an
iso-class `[𝓛]` together with an inverse class `[𝓛⁻¹]`. The comparison with the
cover-local `IsInvertible` predicate is the registered follow-up [PIC-P2-CMP] (its
invertible-to-unit direction constructs the dual — Cartier-duality-lane coordinated). -/
noncomputable def Pic (X : Scheme.{u}) : Type _ :=
  letI := Modules.monoidalCategory X
  (Skeleton X.Modules)ˣ

noncomputable instance (X : Scheme.{u}) : CommGroup (Pic X) :=
  letI := Modules.monoidalCategory X
  letI := Modules.symmetricCategory X
  inferInstanceAs (CommGroup (Skeleton X.Modules)ˣ)

end AlgebraicGeometry.Scheme
