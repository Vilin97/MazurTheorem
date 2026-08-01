#!/usr/bin/env bash

set -euo pipefail

# These polynomial certificates and their final consumers each use several
# gigabytes while elaborating. Keep one Lean compiler active at a time on
# standard CI runners, and start a fresh Lake process for every module.
export LEAN_NUM_THREADS=1

readonly stage_a_modules=(
  MazurTorsion.Kubert.OrderTwentySevenLegStagesA.NumeratorSquare
  MazurTorsion.Kubert.OrderTwentySevenLegStagesA.NumeratorCubeSteps0To7
  MazurTorsion.Kubert.OrderTwentySevenLegStagesA.NumeratorCubeSteps8To15
  MazurTorsion.Kubert.OrderTwentySevenLegStagesA.NumeratorCubeSteps16To23
  MazurTorsion.Kubert.OrderTwentySevenLegStagesA.NumeratorCubeSteps24To31
  MazurTorsion.Kubert.OrderTwentySevenLegStagesA.NumeratorCubeSteps32To35
  MazurTorsion.Kubert.OrderTwentySevenLegStagesA.NumeratorCubeSteps36To40
  MazurTorsion.Kubert.OrderTwentySevenLegStagesA.NumeratorCubeSteps32To40
  MazurTorsion.Kubert.OrderTwentySevenLegStagesA.NumeratorCube
  MazurTorsion.Kubert.OrderTwentySevenLegStagesA.DenominatorSquare
  MazurTorsion.Kubert.OrderTwentySevenLegStagesA.DenominatorCube
  MazurTorsion.Kubert.OrderTwentySevenLegStagesA
)

readonly stage_b_prerequisite_modules=(
  MazurTorsion.Kubert.OrderTwentySevenLegStagesB.TTwoSteps0To6
  MazurTorsion.Kubert.OrderTwentySevenLegStagesB.TTwoSteps7To9
  MazurTorsion.Kubert.OrderTwentySevenLegStagesB.TTwoSteps10To13
  MazurTorsion.Kubert.OrderTwentySevenLegStagesB.TTwoSteps7To13
  MazurTorsion.Kubert.OrderTwentySevenLegStagesB.TTwo
  MazurTorsion.Kubert.OrderTwentySevenLegStagesB.TOneSteps0To4
  MazurTorsion.Kubert.OrderTwentySevenLegStagesB.TOneSteps5To9
  MazurTorsion.Kubert.OrderTwentySevenLegStagesB.TOne
  MazurTorsion.Kubert.OrderTwentySevenLegStagesB.WTwoXSteps0To1
  MazurTorsion.Kubert.OrderTwentySevenLegStagesB.WTwoXSteps2To4
  MazurTorsion.Kubert.OrderTwentySevenLegStagesB.WTwoX
  MazurTorsion.Kubert.OrderTwentySevenLegStagesB.WOneXSteps0To2
  MazurTorsion.Kubert.OrderTwentySevenLegStagesB.WOneXSteps3To5
  MazurTorsion.Kubert.OrderTwentySevenLegStagesB.WOneX
  MazurTorsion.Kubert.OrderTwentySevenLegStagesB.WZeroXSteps
  MazurTorsion.Kubert.OrderTwentySevenLegStagesB.WZeroX
  MazurTorsion.Kubert.OrderTwentySevenLegStagesB.Bands0To5
  MazurTorsion.Kubert.OrderTwentySevenLegStagesB.Bands6To11
  MazurTorsion.Kubert.OrderTwentySevenLegStagesB.Bands12To17
  MazurTorsion.Kubert.OrderTwentySevenLegStagesB.Bands18To23
  MazurTorsion.Kubert.OrderTwentySevenLegStagesB.Scalars
)

readonly final_modules=(
  MazurTorsion.Kubert.OrderTwentySevenLegStagesB.Zero
  MazurTorsion.Kubert.OrderTwentySevenLegStagesB.MNumOne
  MazurTorsion.Kubert.OrderTwentySevenLegStagesB.MNumTwo
  MazurTorsion.Kubert.OrderTwentySevenLegStagesB.MNumThree
  MazurTorsion.Kubert.OrderTwentySevenLegStagesB.MNumFour
  MazurTorsion.Kubert.OrderTwentySevenLegStagesB.MNum
  MazurTorsion.Kubert.OrderTwentySevenLegStagesB.KernelCubic
  MazurTorsion.Kubert.OrderTwentySevenLegStagesB.DenominatorNonzero
  MazurTorsion.Kubert.OrderTwentySevenLegStagesB
  MazurTorsion.Kubert.OrderTwentySevenLegStagesC
  MazurTorsion.Kubert.OrderTwentySevenLegStagesD.Bezout
  MazurTorsion.Kubert.OrderTwentySevenLegStagesD.NumeratorDenominator
  MazurTorsion.Kubert.OrderTwentySevenLegStagesD.NumeratorDenominatorSquare
  MazurTorsion.Kubert.OrderTwentySevenLegStagesD.DenominatorPowers
  MazurTorsion.Kubert.OrderTwentySevenLegStagesD.WeightsHigh
  MazurTorsion.Kubert.OrderTwentySevenLegStagesD.WeightOne
  MazurTorsion.Kubert.OrderTwentySevenLegStagesD.WeightZero
  MazurTorsion.Kubert.OrderTwentySevenLegStagesD.CoefficientPowers
  MazurTorsion.Kubert.OrderTwentySevenLegStagesD.ZeroSum
  MazurTorsion.Kubert.OrderTwentySevenLegStagesD.BigIdentity
  MazurTorsion.Kubert.OrderTwentySevenLegStagesD
  MazurTorsion.Kubert.OrderTwentySevenThirdLeg
  MazurTorsion.Kubert.OrderTwentySeven
)

build_modules() {
  local certificate_module
  for certificate_module in "$@"; do
    echo "Building ${certificate_module}"
    lake build "${certificate_module}"
  done
}

case "${1:-all}" in
  stage-a)
    build_modules "${stage_a_modules[@]}"
    ;;
  stage-b-prerequisites)
    build_modules "${stage_b_prerequisite_modules[@]}"
    ;;
  final)
    build_modules "${final_modules[@]}"
    ;;
  all)
    build_modules "${stage_a_modules[@]}"
    build_modules "${stage_b_prerequisite_modules[@]}"
    build_modules "${final_modules[@]}"
    ;;
  *)
    echo "usage: $0 [stage-a|stage-b-prerequisites|final|all]" >&2
    exit 2
    ;;
esac
