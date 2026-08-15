/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Quasicoherent modules and open restrictions

The source solution supplied a site-theoretic proof that restriction along an
open immersion preserves quasicoherence.  That API is part of the exact pinned
Mathlib: `AlgebraicGeometry.Scheme.Modules.restrictUnitIso` compares the unit
modules, and `isQuasicoherent_restrictFunctor` is the required instance.  This
compatibility module keeps the source import boundary while using the
maintained definitions instead of redeclaring their former backport.
-/
