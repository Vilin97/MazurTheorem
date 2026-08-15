/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Finite étale neighborhoods of points in an étale chart

Zariski's main theorem isolates a quasi-finite point, after an étale base
change, in an open-and-closed component finite over the new base.  For an
étale coordinate morphism the selected component remains étale, hence is
finite étale and can be fed directly to the fpqc splitting calculation.

The named downstream consumer is the finite-divisor chart construction in
`PointedIncidenceDescent`.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.EtaleFiniteNeighborhood

/-- An étale morphism is locally quasi-finite.  This is kept as an explicit
theorem rather than a global instance so it cannot perturb unrelated instance
search. -/
theorem locallyQuasiFinite_of_etale
    {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] : LocallyQuasiFinite f :=
  { quasiFinite_appLE := by
      intro U hU V hV e
      have h := f.etale_appLE hU hV e
      algebraize [(f.appLE U V e).hom]
      exact RingHom.quasiFinite_algebraMap.mpr inferInstance }

/-- Every point of an étale separated morphism is isolated, after an étale
base change, in a finite étale open-and-closed component of the pullback. -/
theorem exists_isCompl_finiteEtale
    {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] [IsSeparated f] (x : X) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S), Etale g ∧ f x ∈ Set.range g ∧
      ∃ (V W : (pullback f g).Opens) (v : V),
        IsCompl V W ∧ IsFinite (V.ι ≫ pullback.snd f g) ∧
          Etale (V.ι ≫ pullback.snd f g) ∧
            pullback.fst f g v.1 = x := by
  letI : LocallyQuasiFinite f := locallyQuasiFinite_of_etale f
  obtain ⟨U, g, hg, hs, V, W, v, hVW, hfinite, hv⟩ :=
    exists_etale_isCompl_of_quasiFiniteAt f rfl (f.quasiFiniteAt x)
  refine ⟨U, g, hg, hs, V, W, v, hVW, hfinite, ?_, hv⟩
  infer_instance

end MazurTorsion.AlgebraicGeometry.Jacobian.EtaleFiniteNeighborhood
