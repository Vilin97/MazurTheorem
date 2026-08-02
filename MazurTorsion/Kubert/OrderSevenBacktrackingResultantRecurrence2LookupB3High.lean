/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData2
import Mathlib.Tactic.NormNum

/-!
# Recurrence 2 lookup certificate: B3 source coefficients, high half

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2B3_coeff_72 :
    remainder3Coefficient3.coeff 72 =
      -((1388328 * 10 ^ 70 +
        5238043731030330790713940511319626048720629589588888271371062127741683) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_73 :
    remainder3Coefficient3.coeff 73 =
      ((3360117 * 10 ^ 70 +
        3022606147947843767961852344442669454883776315937090545525310171456890) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_74 :
    remainder3Coefficient3.coeff 74 =
      -((4737072 * 10 ^ 70 +
        6090936146674134016235557954779411823888514787882540198733169481900505) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_75 :
    remainder3Coefficient3.coeff 75 =
      -((2624724 * 10 ^ 70 +
        9349164207924627981058158461225611093231614953451919208579934556741577) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_76 :
    remainder3Coefficient3.coeff 76 =
      ((43858091 * 10 ^ 70 +
        6870627634708516910743861745028824489961175600550351050985118436273973) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_77 :
    remainder3Coefficient3.coeff 77 =
      -((179070266 * 10 ^ 70 +
        9589498380276133033847446918678790611709121963201680665644583381614252) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_78 :
    remainder3Coefficient3.coeff 78 =
      ((527990088 * 10 ^ 70 +
        8340514526258673613044406660446078556554308736616617662304479479782250) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_79 :
    remainder3Coefficient3.coeff 79 =
      -((1294338858 * 10 ^ 70 +
        2705179224593434311536208709660555789228417679677276709994176807432123) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_80 :
    remainder3Coefficient3.coeff 80 =
      ((2775345610 * 10 ^ 70 +
        6047690258437353814777402512605564537582046174681702184106457413755760) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_81 :
    remainder3Coefficient3.coeff 81 =
      -((5336866711 * 10 ^ 70 +
        5558757960545479947487715642796348842243313869284298765413118950184842) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_82 :
    remainder3Coefficient3.coeff 82 =
      ((9338342491 * 10 ^ 70 +
        4547747692476729917418390690293248150863797874617264376888690357768491) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_83 :
    remainder3Coefficient3.coeff 83 =
      -((15008426021 * 10 ^ 70 +
        4766007516029025019068720450815586742536111508786637735926736770902335) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_84 :
    remainder3Coefficient3.coeff 84 =
      ((22298983744 * 10 ^ 70 +
        6311333400278246490275490085439078114621156373188308191957210496629154) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_85 :
    remainder3Coefficient3.coeff 85 =
      -((30770908587 * 10 ^ 70 +
        3962394517062641398577928956726232725723719748535595804909727287053652) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_86 :
    remainder3Coefficient3.coeff 86 =
      ((39573349213 * 10 ^ 70 +
        6647448009893839264751098020944987601677521124506095793071558236422206) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_87 :
    remainder3Coefficient3.coeff 87 =
      -((47556504033 * 10 ^ 70 +
        6437609330922112075418285296579677968383349922242309221418675982505726) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_88 :
    remainder3Coefficient3.coeff 88 =
      ((53509432096 * 10 ^ 70 +
        3488480646638594542506252603333993793146798225841484164917439507800935) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_89 :
    remainder3Coefficient3.coeff 89 =
      -((56458084786 * 10 ^ 70 +
        4190690510083077567293854758366535306520954639804725071428367092560777) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_90 :
    remainder3Coefficient3.coeff 90 =
      ((55923495037 * 10 ^ 70 +
        1663278726519594183031856054849549265228373579997183202001302428425105) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_91 :
    remainder3Coefficient3.coeff 91 =
      -((52046919244 * 10 ^ 70 +
        0245729891983109826167165713221345673216761280993553561034618732248381) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_92 :
    remainder3Coefficient3.coeff 92 =
      ((45537700168 * 10 ^ 70 +
        7927812796731397167037375330900616752007443513407796330531380045117922) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_93 :
    remainder3Coefficient3.coeff 93 =
      -((37468036573 * 10 ^ 70 +
        1299261936766892806590124135272301940041866259433318211287855773886541) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_94 :
    remainder3Coefficient3.coeff 94 =
      ((28993920886 * 10 ^ 70 +
        1927255211693879492053562977904542102246011966678349916340599005430064) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_95 :
    remainder3Coefficient3.coeff 95 =
      -((21098908481 * 10 ^ 70 +
        7149769175338205653853808985071008687124120075140711826138067180319495) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_96 :
    remainder3Coefficient3.coeff 96 =
      ((14433794727 * 10 ^ 70 +
        5297024171563371299886010988785669209358853038954413551689331821253507) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_97 :
    remainder3Coefficient3.coeff 97 =
      -((9277620451 * 10 ^ 70 +
        4688901997793636199505446776353229134476728368971836344352104289483319) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_98 :
    remainder3Coefficient3.coeff 98 =
      ((5598843840 * 10 ^ 70 +
        0487964921127558627460459444195679199005768810394975681682793531194724) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_99 :
    remainder3Coefficient3.coeff 99 =
      -((3169045638 * 10 ^ 70 +
        1798051743178479959276351563307044660311974116271001215314755904898043) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_100 :
    remainder3Coefficient3.coeff 100 =
      ((1680225593 * 10 ^ 70 +
        0595853467055537199043237604617995086573765094092148094341971452703797) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_101 :
    remainder3Coefficient3.coeff 101 =
      -((833128963 * 10 ^ 70 +
        0849637918252301393369488890104479012971264621242663842813454319699453) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_102 :
    remainder3Coefficient3.coeff 102 =
      ((385551666 * 10 ^ 70 +
        5802135723426507085892522511470511019193367561640069117603190196179010) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_103 :
    remainder3Coefficient3.coeff 103 =
      -((166101569 * 10 ^ 70 +
        9297761118541732804207642645869441274853708845063294583493587360428220) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_104 :
    remainder3Coefficient3.coeff 104 =
      ((66401860 * 10 ^ 70 +
        9132041892649150005780483092285101251834636417139194287863524890218134) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_105 :
    remainder3Coefficient3.coeff 105 =
      -((24528687 * 10 ^ 70 +
        2579494794711164493822023948181353957641425698090298702202763332428513) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_106 :
    remainder3Coefficient3.coeff 106 =
      ((8325256 * 10 ^ 70 +
        7572990935712375096305050418191634016510237177049359517726662164307610) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_107 :
    remainder3Coefficient3.coeff 107 =
      -((2575608 * 10 ^ 70 +
        4359140767751522153471209456351734930541495077954072566961230423326291) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_108 :
    remainder3Coefficient3.coeff 108 =
      ((717577 * 10 ^ 70 +
        9352112322493007564405383946748036764751487537894299807560164342323475) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_109 :
    remainder3Coefficient3.coeff 109 =
      -((176428 * 10 ^ 70 +
        4169942141516794254625106998496771725351030659813117162976573989894870) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_110 :
    remainder3Coefficient3.coeff 110 =
      ((36791 * 10 ^ 70 +
        8324021014412159551117731191087868242145449506185478836464720893206693) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_111 :
    remainder3Coefficient3.coeff 111 =
      -((5877 * 10 ^ 70 +
        0610913316811161165320622211908368657604232622606418763067929277288747) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_112 :
    remainder3Coefficient3.coeff 112 =
      ((430 * 10 ^ 70 +
        2808007910672461271958621805881394611136629638456596163558895095506436) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_113 :
    remainder3Coefficient3.coeff 113 =
      ((143 * 10 ^ 70 +
        3357835678070583064988300991178019401959915876652541887820763526814519) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_114 :
    remainder3Coefficient3.coeff 114 =
      -((81 * 10 ^ 70 +
        7802592660912823625378828639395904673124044039367492061682729383192345) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_115 :
    remainder3Coefficient3.coeff 115 =
      ((25 * 10 ^ 70 +
        6830603734648461069625921244941520037381800577978632773618583405051344) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_116 :
    remainder3Coefficient3.coeff 116 =
      -((6 * 10 ^ 70 +
        2146558126475951742091459752987887047106399082475107324835575852357657) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_117 :
    remainder3Coefficient3.coeff 117 =
      ((1 * 10 ^ 70 +
        2478290413189209613386529064564346453881849061384461516582119428712943) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_118 :
    remainder3Coefficient3.coeff 118 =
      (-2130607953765346486575979173587208401909940944070864743814160704988401 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_119 :
    remainder3Coefficient3.coeff 119 =
      (311562609388111263872074625058641185381641076702746853194821516905497 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_120 :
    remainder3Coefficient3.coeff 120 =
      (-38960786157044998051481637794162861979218679962776265995678533141867 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_121 :
    remainder3Coefficient3.coeff 121 =
      (4136596077373626026460261570569508027070071107107547736180324465103 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_122 :
    remainder3Coefficient3.coeff 122 =
      (-368471479737378690063548259471548224159713335063659997557754145579 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_123 :
    remainder3Coefficient3.coeff 123 =
      (27074914537599357484718731902120870451633524112286446682375692616 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_124 :
    remainder3Coefficient3.coeff 124 =
      (-1604070201724773159251597259559365940215432279655332514103025681 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_125 :
    remainder3Coefficient3.coeff 125 =
      (74319461457584823064126825817146334370811950632684689276279227 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_126 :
    remainder3Coefficient3.coeff 126 =
      (-2583260145960009593741024175832818295951192540568447153431089 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_127 :
    remainder3Coefficient3.coeff 127 =
      (63517628334480963461838776082852917472358213369521692408986 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_128 :
    remainder3Coefficient3.coeff 128 =
      (-1008134748447768781584022993480510525609644882614813968103 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_129 :
    remainder3Coefficient3.coeff 129 =
      (8589632255858115315314958759907205405785857325245156640 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_130 :
    remainder3Coefficient3.coeff 130 =
      (-15073910588387535089979214015962316457358706139149486 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_131 :
    remainder3Coefficient3.coeff 131 =
      (-291052500416767275599138103498844807961572638140070 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_132 :
    remainder3Coefficient3.coeff 132 =
      (1674129651746526608831712981374666865668376926300 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_133 :
    remainder3Coefficient3.coeff 133 =
      (-184976099149246181142891522461286707584146859 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_134 :
    remainder3Coefficient3.coeff 134 =
      (-16928129819723046431748708882310310971802853 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_135 :
    remainder3Coefficient3.coeff 135 =
      (41524351678912399764784036074579321890738 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_136 :
    remainder3Coefficient3.coeff 136 =
      (-37355076014988173036934365236226010977 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_137 :
    remainder3Coefficient3.coeff 137 =
      (12630803349999293373479468844937253 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_138 :
    remainder3Coefficient3.coeff 138 =
      (-1353108127151867760064049878816 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_139 :
    remainder3Coefficient3.coeff 139 =
      (34612852489926112713304677 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_140 :
    remainder3Coefficient3.coeff 140 =
      (-134652616023164963796 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_141 :
    remainder3Coefficient3.coeff 141 =
      (34032965680161 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_142 :
    remainder3Coefficient3.coeff 142 =
      (-51783 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
