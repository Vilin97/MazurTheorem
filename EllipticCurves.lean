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
