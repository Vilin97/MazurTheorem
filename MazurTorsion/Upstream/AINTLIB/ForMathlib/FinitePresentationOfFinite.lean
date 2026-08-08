/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-!
# Finite presentation from module-finite + module-projective ([A711-FP])

A module-finite, module-projective algebra over an **arbitrary** commutative ring is of
algebra-level finite presentation. This is the content of Katz–Mazur's warning (App.
A7.1.1, defering to SGA III Exp. V Thm 4.1): *"In the absence of noetherian hypotheses,
this is rather delicate."*

The two ingredients are mathlib's:
* `Module.finitePresentation_of_projective` — finite projective ⟹ finitely presented as a
  module (Stacks 00NX (2)⟹(1); deliberately not an instance upstream);
* `Algebra.FinitePresentation.of_finitePresentation` — finitely presented as a module ⟹
  finitely presented as an algebra (EGA IV₁ 1.4.7, via the free intermediate algebra of
  1.4.7.1 = the `S'` of Stacks 0564's proof; `RingTheory/Finiteness/ModuleFinitePresentation.lean`).

Sole consumer today: the general-base étale torsor theorem
(`ForMathlib/InvariantTorsor.lean`, `Algebra.Etale.of_isFreeAlgebraAction`), which needs
exactly `Algebra.FinitePresentation Aᴳ A` from f.g.-projectivity of a free-action Galois
extension `A/Aᴳ` — Stacks 08WD (3)⟹(1) assembles étale from unramified + flat + FP.

Decomposition artifact: `.mathlib-quality/decomposition-a711-fp.md` ([STREAM-FP], fable-FP).
-/

/-- **[A711-FP]** A module-finite, module-projective algebra over an arbitrary commutative
ring is of finite presentation as an algebra — no noetherian hypothesis (KM A7.1.1's
"rather delicate" point; EGA IV₁ 1.4.7 + Stacks 00NX). -/
theorem Algebra.FinitePresentation.of_finite_of_projective
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Module.Projective R A] :
    Algebra.FinitePresentation R A :=
  haveI : Module.FinitePresentation R A := Module.finitePresentation_of_projective R A
  Algebra.FinitePresentation.of_finitePresentation R A
