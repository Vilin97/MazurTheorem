/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Basic opens of affine spectra

This is the option-free declaration used by the local quasicoherent-module
port.  It is the initial slice of AINTLIB's `SpecBasicOpenAway` module; the
later gluing API and its compatibility option are intentionally omitted.
-/

open AlgebraicGeometry

/-- A basic open of `Spec A`, packaged as a scheme open. -/
abbrev specBasicOpen (A : CommRingCat) (f : A) : (Spec A).Opens :=
  PrimeSpectrum.basicOpen f
