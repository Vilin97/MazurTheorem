/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData2
import Mathlib.Tactic.NormNum

/-!
# Recurrence 2 lookup certificate: B2 source coefficients, high half

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2B2_coeff_74 :
    remainder3Coefficient2.coeff 74 =
      -((48380612 * 10 ^ 70 +
        5807736123651960748029311842457560255736945738204410330523200568952260) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_75 :
    remainder3Coefficient2.coeff 75 =
      ((52399116 * 10 ^ 70 +
        7770562787171192347484713869695582412439151555427480508975751709820955) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_76 :
    remainder3Coefficient2.coeff 76 =
      ((107166672 * 10 ^ 70 +
        5440105407199975529011841541270732034051950886271738620517456422152047) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_77 :
    remainder3Coefficient2.coeff 77 =
      -((841933614 * 10 ^ 70 +
        5195486471546444844639582432741639081154222478481994343614119951929873) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_78 :
    remainder3Coefficient2.coeff 78 =
      ((3107058602 * 10 ^ 70 +
        8575533537966814752107681158725330531559295349324840267049168204212129) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_79 :
    remainder3Coefficient2.coeff 79 =
      -((8773527652 * 10 ^ 70 +
        1230941836863563003666073305004776276234976737873801757428613106117883) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_80 :
    remainder3Coefficient2.coeff 80 =
      ((20998415085 * 10 ^ 70 +
        9919551749454457773268112361470632809987902168684317820942572855625756) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_81 :
    remainder3Coefficient2.coeff 81 =
      -((44381318534 * 10 ^ 70 +
        9991263522080593701675830045279755086470509237212549004952614599067836) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_82 :
    remainder3Coefficient2.coeff 82 =
      ((84619708782 * 10 ^ 70 +
        5182960830123775269160213699923146932640641182513694132981459534339840) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_83 :
    remainder3Coefficient2.coeff 83 =
      -((147421930894 * 10 ^ 70 +
        7706039837280037719223729477628176833507078285282096993655663177966866) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_84 :
    remainder3Coefficient2.coeff 84 =
      ((236666170457 * 10 ^ 70 +
        6729176633787840805536982086739222216021383988402340329014646659614868) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_85 :
    remainder3Coefficient2.coeff 85 =
      -((352179049125 * 10 ^ 70 +
        2965591377213287177576881910496550810869277228925378637784289444061185) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_86 :
    remainder3Coefficient2.coeff 86 =
      ((487895867774 * 10 ^ 70 +
        8172552623183993860838773198665262867925026377947262128756387467729355) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_87 :
    remainder3Coefficient2.coeff 87 =
      -((631322318862 * 10 ^ 70 +
        7745520386782674434168398018887582965950172115711016381395623210886699) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_88 :
    remainder3Coefficient2.coeff 88 =
      ((764957633435 * 10 ^ 70 +
        5262921675886643795518394449271592980846168144490216083156286725179810) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_89 :
    remainder3Coefficient2.coeff 89 =
      -((869666016974 * 10 ^ 70 +
        9247515814676320711805214435858709310274527504992268040365030782945048) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_90 :
    remainder3Coefficient2.coeff 90 =
      ((929150495622 * 10 ^ 70 +
        0607486260275725415665031661219655566975464158435763998554034408554480) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_91 :
    remainder3Coefficient2.coeff 91 =
      -((934095095674 * 10 ^ 70 +
        9192471828259133872859662088215163160511923113444117696730716028180224) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_92 :
    remainder3Coefficient2.coeff 92 =
      ((884531678433 * 10 ^ 70 +
        8692901094669615449669766070519250450292523084406166617076303714279159) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_93 :
    remainder3Coefficient2.coeff 93 =
      -((789611610993 * 10 ^ 70 +
        1799268872997803709586067011435150914429479252792584491414568389724059) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_94 :
    remainder3Coefficient2.coeff 94 =
      ((664942061269 * 10 ^ 70 +
        9135338432189625888500495771915866405248649841807175754422661512499891) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_95 :
    remainder3Coefficient2.coeff 95 =
      -((528520392947 * 10 ^ 70 +
        4997527372842096920042464534806899023615255895802918082215516192145774) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_96 :
    remainder3Coefficient2.coeff 96 =
      ((396680569299 * 10 ^ 70 +
        8762561882331514688247223528604670263469644760728124408662115906623395) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_97 :
    remainder3Coefficient2.coeff 97 =
      -((281241665706 * 10 ^ 70 +
        8056806788737292238830452277858362790864191804878612755888438156771610) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_98 :
    remainder3Coefficient2.coeff 98 =
      ((188411640372 * 10 ^ 70 +
        9949346202045504220818498858162623313256366101561117504765028790497700) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_99 :
    remainder3Coefficient2.coeff 99 =
      -((119297396032 * 10 ^ 70 +
        8987229107472584980350730821716258482294929301075098159562646123036503) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_100 :
    remainder3Coefficient2.coeff 100 =
      ((71405769206 * 10 ^ 70 +
        6029865589604113091419977440487922673444086032763502423849396950279416) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_101 :
    remainder3Coefficient2.coeff 101 =
      -((40408775765 * 10 ^ 70 +
        4661435721225872224038364036391109826680982581666362786191551875430469) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_102 :
    remainder3Coefficient2.coeff 102 =
      ((21621758313 * 10 ^ 70 +
        9531823907399361439529348444260659020277621502005525504665463291009353) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_103 :
    remainder3Coefficient2.coeff 103 =
      -((10938910645 * 10 ^ 70 +
        0154930183536201085638951475155070008832443978726648528516074363443685) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_104 :
    remainder3Coefficient2.coeff 104 =
      ((5231979799 * 10 ^ 70 +
        0311232815505304664380859811791115565533207489647734100299043137156138) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_105 :
    remainder3Coefficient2.coeff 105 =
      -((2365008918 * 10 ^ 70 +
        1178437391060507335313003191109706233441566022648438160414367711400991) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_106 :
    remainder3Coefficient2.coeff 106 =
      ((1009804210 * 10 ^ 70 +
        3165083692827076657670753797373804887895297423411954063969389581151368) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_107 :
    remainder3Coefficient2.coeff 107 =
      -((406917943 * 10 ^ 70 +
        6436706490024028444350089890583884145684810998237906683449509258064080) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_108 :
    remainder3Coefficient2.coeff 108 =
      ((154560466 * 10 ^ 70 +
        4960767846161518367809748171508613227035233358423742338650833991643039) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_109 :
    remainder3Coefficient2.coeff 109 =
      -((55240906 * 10 ^ 70 +
        2841964684254711041690876799138153832260128413836379376381369612946193) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_110 :
    remainder3Coefficient2.coeff 110 =
      ((18535256 * 10 ^ 70 +
        0904930368592815932380381576355851551316029050931749931300118178605900) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_111 :
    remainder3Coefficient2.coeff 111 =
      -((5821512 * 10 ^ 70 +
        8906236695980483756084115106517291392548948680941089857212726578660303) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_112 :
    remainder3Coefficient2.coeff 112 =
      ((1705206 * 10 ^ 70 +
        1253393681835039412989419604298863122129266837879542283424132438243727) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_113 :
    remainder3Coefficient2.coeff 113 =
      -((463720 * 10 ^ 70 +
        6126802533542607293997760943851314674432049460003414568296716125593865) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_114 :
    remainder3Coefficient2.coeff 114 =
      ((116429 * 10 ^ 70 +
        9929306790927109332300531702373845252155692296120035775140746680497093) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_115 :
    remainder3Coefficient2.coeff 115 =
      -((26805 * 10 ^ 70 +
        3974593728480433715158939486055239104791127235534198899486263968825702) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_116 :
    remainder3Coefficient2.coeff 116 =
      ((5609 * 10 ^ 70 +
        8287185765485529213994082243262581584135657387543776870949233940638251) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_117 :
    remainder3Coefficient2.coeff 117 =
      -((1054 * 10 ^ 70 +
        9445995579726899352496198976701305591064216596749616103919801888854209) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_118 :
    remainder3Coefficient2.coeff 118 =
      ((175 * 10 ^ 70 +
        3428219162708042442929021584283905383289737567132038310659234492806248) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_119 :
    remainder3Coefficient2.coeff 119 =
      -((25 * 10 ^ 70 +
        0847183531193488012110421608822055089562893084198397695106008999443863) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_120 :
    remainder3Coefficient2.coeff 120 =
      ((2 * 10 ^ 70 +
        9347117917665943159179787044301639136720281522779247972409835369510261) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_121 :
    remainder3Coefficient2.coeff 121 =
      (-2446500681235254820503020803171739951147113076143029101929298950265299 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_122 :
    remainder3Coefficient2.coeff 122 =
      (53313951655807229356091123970641619108721066463092394318897182995114 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_123 :
    remainder3Coefficient2.coeff 123 =
      (27739334662807329564267888375865993661995166764506857963097879248305 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_124 :
    remainder3Coefficient2.coeff 124 =
      (-6572864111312376157183801082731963573243496346867076686409667113807 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_125 :
    remainder3Coefficient2.coeff 125 =
      (934681107860434837000953261878398686818274156008261289171673950871 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_126 :
    remainder3Coefficient2.coeff 126 =
      (-98631113392338475087316148944972009748966393538867971507679983646 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_127 :
    remainder3Coefficient2.coeff 127 =
      (8070972681488537876096594324281849283907104357091359639643098128 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_128 :
    remainder3Coefficient2.coeff 128 =
      (-513168991194838191484932827443203554829686858690826486174294323 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_129 :
    remainder3Coefficient2.coeff 129 =
      (24887956221358816884567392188078705225648221779419059150477356 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_130 :
    remainder3Coefficient2.coeff 130 =
      (-888796707805812581979468384138402810818976447442320188418243 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_131 :
    remainder3Coefficient2.coeff 131 =
      (22102615787889023365940715477631828559349160837530666583016 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_132 :
    remainder3Coefficient2.coeff 132 =
      (-349215718451208953719573869056996934238274938879200054710 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_133 :
    remainder3Coefficient2.coeff 133 =
      (2892042315176818529738807354915088841226469430894035494 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_134 :
    remainder3Coefficient2.coeff 134 =
      (-3984496954486262589407169793306672512000502855155540 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_135 :
    remainder3Coefficient2.coeff 135 =
      (-103101870016126360746150005911720546492853629670543 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_136 :
    remainder3Coefficient2.coeff 136 =
      (536387544838059037062928334334550440874733909731 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_137 :
    remainder3Coefficient2.coeff 137 =
      (100574681677421432279576674671370954256997612 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_138 :
    remainder3Coefficient2.coeff 138 =
      (-5622196839184792936462092408424956837028696 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_139 :
    remainder3Coefficient2.coeff 139 =
      (12655902568973616262798152588184214229432 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_140 :
    remainder3Coefficient2.coeff 140 =
      (-10521605408537418559835170422339834894 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_141 :
    remainder3Coefficient2.coeff 141 =
      (3222330311416572061294843994497685 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_142 :
    remainder3Coefficient2.coeff 142 =
      (-301677638040674755667972554263 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_143 :
    remainder3Coefficient2.coeff 143 =
      (6373118709373069341699962 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_144 :
    remainder3Coefficient2.coeff 144 =
      (-18614232357864327257 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_145 :
    remainder3Coefficient2.coeff 145 =
      (2740936995785 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_146 :
    remainder3Coefficient2.coeff 146 =
      (-2406 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
