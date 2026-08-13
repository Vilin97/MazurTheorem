/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

module
public import Mathlib.Algebra.Ring.Rat

/-!
# Polynomial data for the order-twenty-seven trisection certificate

The two public rational polynomials used by the checked trisection proof and
its downstream third-leg certificate.
-/

public meta section
/--
Elaborate generated order-27 rational polynomials with fixed operation
instances.

The leaf chunks contain thousands of explicit additions, subtractions,
multiplications, negations, and natural powers over `ℚ`. Replacing those
operators bottom-up with locally bound standard projections avoids repeating
the same typeclass search at every node.

The generated term still reduces to the ordinary `Rat` instances. This keeps
unfolding compatible with downstream `ring` proofs while making elaboration
linear in the size of each chunk.

The syntax is exported because Lean macros must cross the module boundary to
serve the 24 generated `Part` modules. Its order-27-specific name and fixed
result type keep that interface narrow. Consumers should use it only for
generated order-27 polynomial definitions.
It deliberately introduces no notation for ordinary source terms.
-/
macro:0 "order27_rat% " body:term:0 : term => do
      let body : Lean.TSyntax `term := ⟨← body.raw.rewriteBottomUpM fun stx => do
        match stx with
        | `($a + $b) => `(ratAdd $a $b) | `($a - $b) => `(ratSub $a $b)
        | `($a * $b) => `(ratMul $a $b) | `($a ^ $b) => `(ratPow $a $b)
        | `(-$a) => `(ratNeg $a) | _ => pure stx⟩
      `(let ratAdd : ℚ → ℚ → ℚ := HAdd.hAdd (self := @instHAdd ℚ Rat.instAdd)
        let ratSub : ℚ → ℚ → ℚ := HSub.hSub (self := @instHSub ℚ Rat.instSub)
        let ratMul : ℚ → ℚ → ℚ := HMul.hMul (self := @instHMul ℚ Rat.instMul)
        let ratPow : ℚ → ℕ → ℚ := HPow.hPow (self := @instHPow ℚ ℕ Rat.instPowNat)
        let ratNeg : ℚ → ℚ := Neg.neg (self := Rat.instNeg)
        $body)
end

@[expose] public section
namespace MazurTorsion.Kubert

/-- The two-division value `4ξ³ + b₂ξ² + 2b₄ξ + b₆` of the family. -/
def famTwoDivision (f ξ : ℚ) : ℚ :=
  f ^ 2 * (f * (f * (f * (f * (f * (f * (f * (f - 4) + 2 * ξ + 8) - 6 * ξ - 10) + ξ * (ξ + 8) + 8)
    + ξ * (-6 * ξ - 8) - 4) + ξ * (9 * ξ + 6) + 1) + ξ * (-10 * ξ - 4)) + ξ * (6 * ξ + 2))
    + ξ ^ 2 * (4 * ξ + 1)

/-- The trisection polynomial of the family: a point triples to an
abscissa-zero point only if this vanishes. -/
def trisectionPoly (f ξ : ℚ) : ℚ :=
  f ^ 2 * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (
    f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f - 13) + 3 * ξ + 84) - 39 * ξ
    - 358) + ξ * (3 * ξ + 249) + 1126) + ξ * (-45 * ξ - 1044) - 2772) + ξ * (ξ * (ξ + 309) + 3231)
    + 5531) + ξ * (ξ * (-18 * ξ - 1341) - 7851) - 9143) + ξ * (ξ * (144 * ξ + 4200) + 15543) + 12696
    ) + ξ * (ξ * (-702 * ξ - 10182) - 25668) - 14932) + ξ * (ξ * (2426 * ξ + 19929) + 35898) + 14932
    ) + ξ * (ξ * (-6435 * ξ - 32373) - 42912) - 12696) + ξ * (ξ * (ξ * (12 * ξ + 13688) + 44478)
    + 44046) + 9143) + ξ * (ξ * (ξ * (-144 * ξ - 23955) - 52374) - 38838) - 5531) + ξ * (ξ * (ξ * (
    756 * ξ + 35022) + 53328) + 29313) + 2772) + ξ * (ξ * (ξ * (-2487 * ξ - 43163) - 47184) - 18783)
    - 1126) + ξ * (ξ * (ξ * (5853 * ξ + 45091) + 36297) + 10077) + 358) + ξ * (ξ * (ξ * (ξ * (-6 * ξ
    - 10476) - 40068) - 24159) - 4428) - 84) + ξ * (ξ * (ξ * (ξ * (90 * ξ + 14730) + 30372) + 13749)
    + 1539) + 13) + ξ * (ξ * (ξ * (ξ * (ξ * (-ξ - 426) - 16539) - 19699) - 6549) - 399) - 1) + ξ * (
    ξ * (ξ * (ξ * (ξ * (9 * ξ + 1164) + 14922) + 10962) + 2520) + 69)) + ξ * (ξ * (ξ * (ξ * (ξ * (
    -31 * ξ - 2166) - 10818) - 5227) - 738) - 6)) + ξ ^ 2 * (ξ * (ξ * (ξ * (65 * ξ + 2916) + 6279)
    + 2103) + 147)) + ξ ^ 2 * (ξ * (ξ * (ξ * (-123 * ξ - 2916) - 2916) - 681) - 15)) + ξ ^ 3 * (
    ξ * (ξ * (210 * ξ + 2166) + 1098) + 159)) + ξ ^ 3 * (ξ * (ξ * (ξ * (-6 * ξ - 297) - 1170) - 345)
    - 20)) + ξ ^ 4 * (ξ * (ξ * (18 * ξ + 321) + 444) + 90)) + ξ ^ 4 * (ξ * (ξ * (-24 * ξ - 243)
    - 114) - 15)) + ξ ^ 5 * (ξ * (24 * ξ + 122) + 24)) + ξ ^ 5 * (ξ * (-18 * ξ - 33) - 6))
    + ξ ^ 6 * (12 * ξ + 2)) + ξ ^ 6 * (-6 * ξ - 1)) + ξ ^ 9

end MazurTorsion.Kubert

end
