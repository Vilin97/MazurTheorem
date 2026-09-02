/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData2
import Mathlib.Tactic.NormNum

/-!
# Recurrence 2 lookup certificate: B0 source coefficients, high half

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2B0_coeff_78 :
    remainder3Coefficient0.coeff 78 =
      ((637265554 * 10 ^ 70 +
        3282697507054098880371590413640098565564533962612427941948736179061248) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_79 :
    remainder3Coefficient0.coeff 79 =
      -((5031553879 * 10 ^ 70 +
        0393813884086211108635282259215299900350178106990631385272414836887462) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_80 :
    remainder3Coefficient0.coeff 80 =
      ((18818123497 * 10 ^ 70 +
        4120523759381199418842667518119761069584320583760568653061355197891663) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_81 :
    remainder3Coefficient0.coeff 81 =
      -((53984454480 * 10 ^ 70 +
        6811164544346815931077803689983026155988049170761101468716449152852654) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_82 :
    remainder3Coefficient0.coeff 82 =
      ((131496338158 * 10 ^ 70 +
        4975580411685665925306576885383876271381976106390185088995350036226044) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_83 :
    remainder3Coefficient0.coeff 83 =
      -((283296131962 * 10 ^ 70 +
        3624223922612719819140228645599802013120937393586924233622809071147118) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_84 :
    remainder3Coefficient0.coeff 84 =
      ((551432569883 * 10 ^ 70 +
        3414817309441740525901669871318255178687825615833589108515931765379326) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_85 :
    remainder3Coefficient0.coeff 85 =
      -((982337165000 * 10 ^ 70 +
        2842268045067928307601056453411895545475235805828187397690464187019978) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_86 :
    remainder3Coefficient0.coeff 86 =
      ((1615390851536 * 10 ^ 70 +
        2124440216079338858528841092923698896994648198128599585321933507688391) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_87 :
    remainder3Coefficient0.coeff 87 =
      -((2467298259771 * 10 ^ 70 +
        7824925062618263418929687987715868218696519945238350744394649053882099) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_88 :
    remainder3Coefficient0.coeff 88 =
      ((3516655367512 * 10 ^ 70 +
        2033587120505110880403502016910954759245948424965759432154930537538922) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_89 :
    remainder3Coefficient0.coeff 89 =
      -((4694980766891 * 10 ^ 70 +
        2672815048823497379023329058984347663344774370127978105716918838826127) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_90 :
    remainder3Coefficient0.coeff 90 =
      ((5889875167925 * 10 ^ 70 +
        1732090932462756142994987227470378401137868957962566949052247962058830) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_91 :
    remainder3Coefficient0.coeff 91 =
      -((6962363957684 * 10 ^ 70 +
        8753243718206642823848292474709570948204395678589619280115382516285324) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_92 :
    remainder3Coefficient0.coeff 92 =
      ((7775006646944 * 10 ^ 70 +
        1271781763613081059113780969293778483475067120470317565586744881191969) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_93 :
    remainder3Coefficient0.coeff 93 =
      -((8222517424411 * 10 ^ 70 +
        3453057363360237729600562523297152011695800243201475928438641391323414) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_94 :
    remainder3Coefficient0.coeff 94 =
      ((8254977743358 * 10 ^ 70 +
        5876047809859239589397583704250627237971723867666555166478842713669344) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_95 :
    remainder3Coefficient0.coeff 95 =
      -((7886290900831 * 10 ^ 70 +
        9389329793144120444348503412512015638338885692480594619933748151825207) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_96 :
    remainder3Coefficient0.coeff 96 =
      ((7186161758741 * 10 ^ 70 +
        6195823642756731283672918981396625831551497803412791111407407499243582) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_97 :
    remainder3Coefficient0.coeff 97 =
      -((6259826820350 * 10 ^ 70 +
        9287325825363707077757076047763491948404540761367423412158541667877138) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_98 :
    remainder3Coefficient0.coeff 98 =
      ((5223283262019 * 10 ^ 70 +
        8375180849827500216389394710718433113262620150797868060086010432185611) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_99 :
    remainder3Coefficient0.coeff 99 =
      -((4181675720428 * 10 ^ 70 +
        4487997184491297910580978624859397280650449284020085939805016537121909) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_100 :
    remainder3Coefficient0.coeff 100 =
      ((3215569218501 * 10 ^ 70 +
        6652634743605926884083993085912259417191408995184205690703384129195208) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_101 :
    remainder3Coefficient0.coeff 101 =
      -((2376024447935 * 10 ^ 70 +
        0439984669377098056042127913340264298475916025841369295483046621340362) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_102 :
    remainder3Coefficient0.coeff 102 =
      ((1686537652037 * 10 ^ 70 +
        2639563131287106271952671683664243208591892802651358470329547719388728) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_103 :
    remainder3Coefficient0.coeff 103 =
      -((1148816109053 * 10 ^ 70 +
        8496635571322553799349159890504376240458533771882012393258257312819157) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_104 :
    remainder3Coefficient0.coeff 104 =
      ((749731605604 * 10 ^ 70 +
        0079523803003289733801098294690379738804613869586231936849966490454629) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_105 :
    remainder3Coefficient0.coeff 105 =
      -((467793694218 * 10 ^ 70 +
        5549123077764746854956975534097579090798864594354813203874342078531782) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_106 :
    remainder3Coefficient0.coeff 106 =
      ((278396228989 * 10 ^ 70 +
        6585025574778165916113156451102909859251474770631920500927437296205371) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_107 :
    remainder3Coefficient0.coeff 107 =
      -((157630914836 * 10 ^ 70 +
        7956723587824565004165031538085554706244798510673407453791285161808265) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_108 :
    remainder3Coefficient0.coeff 108 =
      ((84701085674 * 10 ^ 70 +
        3521030817930811536018712083082159780463815449718891062788700093784844) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_109 :
    remainder3Coefficient0.coeff 109 =
      -((43085362281 * 10 ^ 70 +
        4861337576523389200278686498248800050127435208616555976542856075108934) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_110 :
    remainder3Coefficient0.coeff 110 =
      ((20697815446 * 10 ^ 70 +
        5339680743551319089030616022609445083443493320200485441591694469275402) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_111 :
    remainder3Coefficient0.coeff 111 =
      -((9368537551 * 10 ^ 70 +
        7402831066700830220230779874814266368052112627961790098551186292677762) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_112 :
    remainder3Coefficient0.coeff 112 =
      ((3986572840 * 10 ^ 70 +
        2929959663196554827000207119551579165819291385530935944272871231301355) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_113 :
    remainder3Coefficient0.coeff 113 =
      -((1591302814 * 10 ^ 70 +
        6501764937509219606675639165927048343089575355276839535699262296719279) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_114 :
    remainder3Coefficient0.coeff 114 =
      ((594535354 * 10 ^ 70 +
        7948251466012727094255100250555954330598620983016004020153505202647983) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_115 :
    remainder3Coefficient0.coeff 115 =
      -((207447769 * 10 ^ 70 +
        2605407839113645381870498466686183308682133541356084259978633855899602) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_116 :
    remainder3Coefficient0.coeff 116 =
      ((67446199 * 10 ^ 70 +
        0907623585363458366112947308473564960929398356230375635079126179452507) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_117 :
    remainder3Coefficient0.coeff 117 =
      -((20384773 * 10 ^ 70 +
        4819215826421435314192094498992896357031348647856186438074115378109371) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_118 :
    remainder3Coefficient0.coeff 118 =
      ((5713576 * 10 ^ 70 +
        9510060078692401921468047597800136099127910548317546758145869716383679) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_119 :
    remainder3Coefficient0.coeff 119 =
      -((1481504 * 10 ^ 70 +
        2078440609075985919940138919909089519674066290142820247383085196128127) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_120 :
    remainder3Coefficient0.coeff 120 =
      ((354522 * 10 ^ 70 +
        2914893712326206528796479084098997714334778175052955882894646241038904) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_121 :
    remainder3Coefficient0.coeff 121 =
      -((78118 * 10 ^ 70 +
        0638840573974600871508196653912903116876024338642130622120750037433134) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_122 :
    remainder3Coefficient0.coeff 122 =
      ((15819 * 10 ^ 70 +
        8288556425185236400140464479511140692366474006193806836523494698068047) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_123 :
    remainder3Coefficient0.coeff 123 =
      -((2940 * 10 ^ 70 +
        6486499099729956300950206526716081741152804858236072771958329847869630) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_124 :
    remainder3Coefficient0.coeff 124 =
      ((501 * 10 ^ 70 +
        5743261313349696684144127279389992962815447726472509388863282654896318) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_125 :
    remainder3Coefficient0.coeff 125 =
      -((78 * 10 ^ 70 +
        5670058579752082037762826501661006933927038226813934010398924281667696) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_126 :
    remainder3Coefficient0.coeff 126 =
      ((11 * 10 ^ 70 +
        3218082722740306109096795283920026113796946052082605525289866910205118) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_127 :
    remainder3Coefficient0.coeff 127 =
      -((1 * 10 ^ 70 +
        5030194968541871038434252452760894584665599963720825971855744422440578) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_128 :
    remainder3Coefficient0.coeff 128 =
      (1834827527184728066937284515735569308140319670438270299778071166717767 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_129 :
    remainder3Coefficient0.coeff 129 =
      (-204025618344663817048914574886865361097987480803804696192799852734959 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_130 :
    remainder3Coefficient0.coeff 130 =
      (20198801752175316049811777180007732333864490316687238813135479047170 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_131 :
    remainder3Coefficient0.coeff 131 =
      (-1702446196019049729108408376329147576875929173287432278190303921572 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_132 :
    remainder3Coefficient0.coeff 132 =
      (111276423164953787066102218819162935182149174135000407027111793574 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_133 :
    remainder3Coefficient0.coeff 133 =
      (-4139802210795116435144972353740749138052802559496185808778173681 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_134 :
    remainder3Coefficient0.coeff 134 =
      (-151124331760411728556559511211740112853960585305662203599722374 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_135 :
    remainder3Coefficient0.coeff 135 =
      (41243569877879273185902978459566132734664168360527059732092987 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_136 :
    remainder3Coefficient0.coeff 136 =
      (-3862183401125520033506848253432213202056041276232465423771467 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_137 :
    remainder3Coefficient0.coeff 137 =
      (229990070726724836385075136060987756387867673675465768566161 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_138 :
    remainder3Coefficient0.coeff 138 =
      (-9290697854385371177486367979965834868714849010537332656527 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_139 :
    remainder3Coefficient0.coeff 139 =
      (248727234973674867513257277298321151413727299366901080327 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_140 :
    remainder3Coefficient0.coeff 140 =
      (-4078153179376266612559525887827345638572102738839086124 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_141 :
    remainder3Coefficient0.coeff 141 =
      (33809467951087185928507141418130229292018171920903153 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_142 :
    remainder3Coefficient0.coeff 142 =
      (-37817579212424531880147848185303768933624033934741 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_143 :
    remainder3Coefficient0.coeff 143 =
      (-1246244779211640409521911260108607639113011879035 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_144 :
    remainder3Coefficient0.coeff 144 =
      (5925938749583198575776933513034738181026733413 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_145 :
    remainder3Coefficient0.coeff 145 =
      (2887992996509810155902212709188379207670954 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_146 :
    remainder3Coefficient0.coeff 146 =
      (-63885184880089663970531341606708629746598 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_147 :
    remainder3Coefficient0.coeff 147 =
      (131521815278795812666703554559090676741 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_148 :
    remainder3Coefficient0.coeff 148 =
      (-99880414820312230247369694394082213 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_149 :
    remainder3Coefficient0.coeff 149 =
      (27137546393774277028731104945873 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_150 :
    remainder3Coefficient0.coeff 150 =
      (-2142134801952946451436700965 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_151 :
    remainder3Coefficient0.coeff 151 =
      (34993556805095373359551 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_152 :
    remainder3Coefficient0.coeff 152 =
      (-67212899013694767 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_153 :
    remainder3Coefficient0.coeff 153 =
      (3578955260 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_154 :
    remainder3Coefficient0.coeff 154 =
      (-1 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
