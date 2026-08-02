/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.Basic

/-!
# Elementary operations on finite-flat commutative group schemes

This file records operations that exist formally for every commutative group object.  In
particular, `powerEnd G n` is multiplication by `n` in multiplicative notation.  Its action on
points is proved from the internal group law, so later kernel examples consume the geometric
finite-flat API rather than an unrelated pointwise definition.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry
namespace FiniteFlatCommGroupScheme

universe u

variable {S : Scheme.{u}}

/-- The zero homomorphism, sending every point to the identity section. -/
noncomputable abbrev zeroHom (G H : FiniteFlatCommGroupScheme S) : G ⟶ H :=
  ObjectProperty.homMk (InducedCategory.homMk
    ((default : G.obj.toGrp ⟶ Grp.trivial (Over S)) ≫
      (default : Grp.trivial (Over S) ⟶ H.obj.toGrp)))

@[simp]
theorem hom_zeroHom (G H : FiniteFlatCommGroupScheme S) :
    hom (zeroHom G H) = G.structureMap ≫ η[H.obj.X].left :=
  rfl

/-- Base change preserves the zero homomorphism. -/
@[simp]
theorem baseChange_zeroHom {T : Scheme.{u}} (t : T ⟶ S)
    (G H : FiniteFlatCommGroupScheme S) :
    (baseChange t).map (zeroHom G H) =
      zeroHom ((baseChange t).obj G) ((baseChange t).obj H) := by
  ext
  change Over.Hom.left ((Over.pullback t).map (1 : G.obj.X ⟶ H.obj.X)) =
    Over.Hom.left (1 : ((Over.pullback t).mapCommGrp.obj G.obj).X ⟶
      ((Over.pullback t).mapCommGrp.obj H.obj).X)
  rw [(Over.pullback t).map_one]
  rfl

/-- The kernel of the zero homomorphism is represented by its whole source.  This is a genuine
scheme-theoretic kernel presentation, not merely a pointwise calculation. -/
noncomputable def zeroKernelPresentation (G H : FiniteFlatCommGroupScheme S) :
    KernelPresentation (zeroHom G H) := by
  let se : SplitMono (η[H.obj.X].left) :=
    SplitMono.mk H.structureMap (by exact (η[H.obj.X]).w)
  letI : Mono (η[H.obj.X].left) := se.mono
  let sq : IsPullback (𝟙 G.scheme) G.structureMap
      (hom (zeroHom G H)) (η[H.obj.X].left) :=
    IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  exact
    { kernel := G
      inclusion := 𝟙 G
      schemeIso := sq.isoPullback
      schemeIso_hom_structureMap := IsPullback.isoPullback_hom_snd sq
      schemeIso_hom_kernelι := by
        exact IsPullback.isoPullback_hom_fst sq }

/-- The source object in the zero-kernel presentation commutes strictly with base change. -/
@[simp]
theorem zeroKernelPresentation_baseChange_kernel {T : Scheme.{u}} (t : T ⟶ S)
    (G H : FiniteFlatCommGroupScheme S) :
    (baseChange t).obj (zeroKernelPresentation G H).kernel =
      (zeroKernelPresentation ((baseChange t).obj G) ((baseChange t).obj H)).kernel :=
  rfl

/-- The inclusion in the zero-kernel presentation is compatible with base change, not merely
its source object. -/
@[simp]
theorem zeroKernelPresentation_baseChange_inclusion {T : Scheme.{u}} (t : T ⟶ S)
    (G H : FiniteFlatCommGroupScheme S) :
    (baseChange t).map (zeroKernelPresentation G H).inclusion =
      (zeroKernelPresentation ((baseChange t).obj G) ((baseChange t).obj H)).inclusion := by
  change (baseChange t).map (𝟙 G) = 𝟙 ((baseChange t).obj G)
  exact (baseChange t).map_id G

/-- Multiplication by `n` on a finite-flat commutative group scheme, in multiplicative notation. -/
def powerEnd (G : FiniteFlatCommGroupScheme S) (n : ℕ) : G ⟶ G :=
  ObjectProperty.homMk (InducedCategory.homMk ((𝟙 G.obj.toGrp) ^ n))

@[simp]
theorem powerEnd_one (G : FiniteFlatCommGroupScheme S) :
    powerEnd G 1 = 𝟙 G := by
  ext
  simp [powerEnd]

@[simp]
theorem mapPoint_powerEnd (G : FiniteFlatCommGroupScheme S) (n : ℕ)
    (X : Over S) (x : G.Point X) :
    mapPoint (powerEnd G n) X x = x ^ n := by
  change x ≫ (((𝟙 G.obj.toGrp) ^ n).hom.hom) = x ^ n
  rw [Grp.Hom.hom_pow, Mon.Hom.hom_pow]
  rw [MonObj.comp_pow]
  simp

end FiniteFlatCommGroupScheme
end AlgebraicGeometry
