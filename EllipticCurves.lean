/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import EllipticCurves.Examples.ExceptionalCubicReduction
import EllipticCurves.IntegralModel
import EllipticCurves.Mathlib.AdicCompletionExtension
import EllipticCurves.Mathlib.AdicFormalGroupLog
import EllipticCurves.Mathlib.AdicValuation
import EllipticCurves.Mathlib.Basic
import EllipticCurves.Mathlib.Chabauty.AdicTopology
import EllipticCurves.Mathlib.Chabauty.ExpConverge
import EllipticCurves.Mathlib.Chabauty.FormalGroupLaw
import EllipticCurves.Mathlib.Chabauty.FormalGroupLaw.Basic
import EllipticCurves.Mathlib.Chabauty.FormalGroupLaw.Invariance
import EllipticCurves.Mathlib.Chabauty.FormalGroupLaw.Log
import EllipticCurves.Mathlib.Chabauty.FormalGroupLaw.Points
import EllipticCurves.Mathlib.Chabauty.LocalRing
import EllipticCurves.Mathlib.Chabauty.LogIso
import EllipticCurves.Mathlib.Chabauty.MvPSeries
import EllipticCurves.Mathlib.Chabauty.MvPowerSeriesComp
import EllipticCurves.Mathlib.Chabauty.MvPowerSeriesPDeriv
import EllipticCurves.Mathlib.Chabauty.PSeries
import EllipticCurves.Mathlib.Chabauty.PadicInt
import EllipticCurves.Mathlib.Chabauty.PadicValNat
import EllipticCurves.Mathlib.EllipticCurvePoint
import EllipticCurves.ReductionAtPrime
import EllipticCurves.VariableChange
import EllipticCurves.WeierstrassFormalGroup.Chord
import EllipticCurves.WeierstrassFormalGroup.Eval
import EllipticCurves.WeierstrassFormalGroup.Filtration
import EllipticCurves.WeierstrassFormalGroup.Foundations
import EllipticCurves.WeierstrassFormalGroup.GroupLaw
import EllipticCurves.WeierstrassFormalGroup.Reduction
import EllipticCurves.WeierstrassFormalGroup.ThirdPoint

/-!
# Exact-pin elliptic-curve audit aggregate

This root makes the retained elliptic-curve reduction cone and its integration
harness available as an explicit CI and release-audit target. It is not a
default Lake target or a curated public facade. Downstream modules should
import the narrow `EllipticCurves.*` module that owns the required API; the
compatibility `public import` in `EllipticCurves.VariableChange` is an explicit
exception. The source exposition scans these files independently of this
aggregate.

`PORTING.md` is the authoritative source-to-destination manifest and records
which files are retained ports, exact-pin adaptations, compatibility modules,
or project-owned harnesses.
-/
