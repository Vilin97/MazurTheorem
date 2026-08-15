/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ExtAdjunction
import MazurTorsion.Upstream.CoherentCohomologyFinite.TopologicalSheafBaseLinearClosedEmbedding
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Constant-source Ext across a closed embedding

For sheaves of modules over a fixed coefficient ring, inverse image
commutes with the constant-sheaf functor.  Combining this with exactness
of direct image along a closed embedding gives the base-linear Ext
comparison used by projective-factorization arguments.
-/


open CategoryTheory Limits TopologicalSpace

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.TopCat

variable {R : Type u} [CommRing R]
variable {X Y : TopCat.{u}}

/-- The inverse image of the top open is the top open, written in the
opposite category in the direction used by global sections. -/
noncomputable def opensMapTopIso
    (f : X ⟶ Y) :
    Opposite.op ((Opens.map f).obj (⊤ : Opens Y)) ≅
      Opposite.op (⊤ : Opens X) :=
  (eqToIso (Opens.map_top f).symm).op

/-- Global sections of a direct image are canonically the global
sections of the original sheaf. -/
noncomputable def pushforwardSectionsIso
    (f : X ⟶ Y) :
    TopCat.Sheaf.pushforward (ModuleCat.{u} R) f ⋙
        (sheafSections
          (Opens.grothendieckTopology Y)
          (ModuleCat.{u} R)).obj
            (Opposite.op (⊤ : Opens Y)) ≅
      (sheafSections
        (Opens.grothendieckTopology X)
        (ModuleCat.{u} R)).obj
          (Opposite.op (⊤ : Opens X)) :=
  NatIso.ofComponents
    (fun F =>
      F.presheaf.mapIso
        (opensMapTopIso f))
    (fun {F G} α => by
      change
        α.hom.app
              (Opposite.op
                ((Opens.map f).obj
                  (⊤ : Opens Y))) ≫
            G.presheaf.map
              (opensMapTopIso f).hom =
          F.presheaf.map
              (opensMapTopIso f).hom ≫
            α.hom.app
              (Opposite.op (⊤ : Opens X))
      exact
        (α.hom.naturality
          (opensMapTopIso f).hom).symm)

/-- The composite "constant sheaf on the target, then pull back" is
left adjoint to global sections on the source. -/
noncomputable def constantPullbackAdjunction
    (f : X ⟶ Y) :
    constantSheaf
        (Opens.grothendieckTopology Y)
        (ModuleCat.{u} R) ⋙
      TopCat.Sheaf.pullback
        (ModuleCat.{u} R) f ⊣
    (sheafSections
      (Opens.grothendieckTopology X)
      (ModuleCat.{u} R)).obj
        (Opposite.op (⊤ : Opens X)) :=
  ((constantSheafAdj
      (Opens.grothendieckTopology Y)
      (ModuleCat.{u} R)
      (isTerminalTop :
        IsTerminal (⊤ : Opens Y))).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction
      (ModuleCat.{u} R) f)).ofNatIsoRight
        (pushforwardSectionsIso (R := R) f)

/-- Pullback commutes with the constant sheaf functor. -/
noncomputable def constantSheafPullbackIso
    (f : X ⟶ Y) :
    constantSheaf
        (Opens.grothendieckTopology Y)
        (ModuleCat.{u} R) ⋙
      TopCat.Sheaf.pullback
        (ModuleCat.{u} R) f ≅
    constantSheaf
      (Opens.grothendieckTopology X)
      (ModuleCat.{u} R) :=
  (constantPullbackAdjunction (R := R) f).leftAdjointUniq
    (constantSheafAdj
      (Opens.grothendieckTopology X)
      (ModuleCat.{u} R)
      (isTerminalTop :
        IsTerminal (⊤ : Opens X)))

/-- In particular, pullback carries the constant rank-one sheaf to the
constant rank-one sheaf. -/
noncomputable def constantRankOnePullbackIso
    (f : X ⟶ Y) :
    (TopCat.Sheaf.pullback
      (ModuleCat.{u} R) f).obj
        ((constantSheaf
          (Opens.grothendieckTopology Y)
          (ModuleCat.{u} R)).obj
            (ModuleCat.of R R)) ≅
      (constantSheaf
        (Opens.grothendieckTopology X)
        (ModuleCat.{u} R)).obj
          (ModuleCat.of R R) :=
  (constantSheafPullbackIso (R := R) f).app
    (ModuleCat.of R R)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.TopCat
