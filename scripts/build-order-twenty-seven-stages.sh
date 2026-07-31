#!/usr/bin/env bash

set -euo pipefail

# These independent polynomial certificates each use several gigabytes while
# elaborating. Keep one Lean compiler active at a time on standard CI runners.
export LEAN_NUM_THREADS=1

readonly certificate_modules=(
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
)

for certificate_module in "${certificate_modules[@]}"; do
  echo "Building ${certificate_module}"
  lake build "${certificate_module}"
done
