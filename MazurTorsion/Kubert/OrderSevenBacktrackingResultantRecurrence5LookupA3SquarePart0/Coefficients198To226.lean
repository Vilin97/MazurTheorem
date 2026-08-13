/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA3SquarePart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: A3Square coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence5A3_coeff_0
  recurrence5A3_coeff_1
  recurrence5A3_coeff_2
  recurrence5A3_coeff_3
  recurrence5A3_coeff_4
  recurrence5A3_coeff_5
  recurrence5A3_coeff_6
  recurrence5A3_coeff_7
  recurrence5A3_coeff_8
  recurrence5A3_coeff_9
  recurrence5A3_coeff_10
  recurrence5A3_coeff_11
  recurrence5A3_coeff_12
  recurrence5A3_coeff_13
  recurrence5A3_coeff_14
  recurrence5A3_coeff_15
  recurrence5A3_coeff_16
  recurrence5A3_coeff_17
  recurrence5A3_coeff_18
  recurrence5A3_coeff_19
  recurrence5A3_coeff_20
  recurrence5A3_coeff_21
  recurrence5A3_coeff_22
  recurrence5A3_coeff_23
  recurrence5A3_coeff_24
  recurrence5A3_coeff_25
  recurrence5A3_coeff_26
  recurrence5A3_coeff_27
  recurrence5A3_coeff_28
  recurrence5A3_coeff_29
  recurrence5A3_coeff_30
  recurrence5A3_coeff_31
  recurrence5A3_coeff_32
  recurrence5A3_coeff_33
  recurrence5A3_coeff_34
  recurrence5A3_coeff_35
  recurrence5A3_coeff_36
  recurrence5A3_coeff_37
  recurrence5A3_coeff_38
  recurrence5A3_coeff_39
  recurrence5A3_coeff_40
  recurrence5A3_coeff_41
  recurrence5A3_coeff_42
  recurrence5A3_coeff_43
  recurrence5A3_coeff_44
  recurrence5A3_coeff_45
  recurrence5A3_coeff_46
  recurrence5A3_coeff_47
  recurrence5A3_coeff_48
  recurrence5A3_coeff_49
  recurrence5A3_coeff_50
  recurrence5A3_coeff_51
  recurrence5A3_coeff_52
  recurrence5A3_coeff_53
  recurrence5A3_coeff_54
  recurrence5A3_coeff_55
  recurrence5A3_coeff_56
  recurrence5A3_coeff_57
  recurrence5A3_coeff_58
  recurrence5A3_coeff_59
  recurrence5A3_coeff_60
  recurrence5A3_coeff_61
  recurrence5A3_coeff_62
  recurrence5A3_coeff_63

attribute [local simp]
  recurrence5A3_coeff_64
  recurrence5A3_coeff_65
  recurrence5A3_coeff_66
  recurrence5A3_coeff_67
  recurrence5A3_coeff_68
  recurrence5A3_coeff_69
  recurrence5A3_coeff_70
  recurrence5A3_coeff_71
  recurrence5A3_coeff_72
  recurrence5A3_coeff_73
  recurrence5A3_coeff_74
  recurrence5A3_coeff_75
  recurrence5A3_coeff_76
  recurrence5A3_coeff_77
  recurrence5A3_coeff_78
  recurrence5A3_coeff_79
  recurrence5A3_coeff_80
  recurrence5A3_coeff_81
  recurrence5A3_coeff_82
  recurrence5A3_coeff_83
  recurrence5A3_coeff_84
  recurrence5A3_coeff_85
  recurrence5A3_coeff_86
  recurrence5A3_coeff_87
  recurrence5A3_coeff_88
  recurrence5A3_coeff_89
  recurrence5A3_coeff_90
  recurrence5A3_coeff_91
  recurrence5A3_coeff_92
  recurrence5A3_coeff_93
  recurrence5A3_coeff_94
  recurrence5A3_coeff_95
  recurrence5A3_coeff_96
  recurrence5A3_coeff_97
  recurrence5A3_coeff_98
  recurrence5A3_coeff_99
  recurrence5A3_coeff_100
  recurrence5A3_coeff_101
  recurrence5A3_coeff_102
  recurrence5A3_coeff_103
  recurrence5A3_coeff_104
  recurrence5A3_coeff_105
  recurrence5A3_coeff_106
  recurrence5A3_coeff_107
  recurrence5A3_coeff_108
  recurrence5A3_coeff_109
  recurrence5A3_coeff_110
  recurrence5A3_coeff_111
  recurrence5A3_coeff_112
  recurrence5A3_coeff_113
  recurrence5A3_coeff_114
  recurrence5A3_coeff_115
  recurrence5A3_coeff_116
  recurrence5A3_coeff_117
  recurrence5A3_coeff_118
  recurrence5A3_coeff_119
  recurrence5A3_coeff_120
  recurrence5A3_coeff_121
  recurrence5A3_coeff_122
  recurrence5A3_coeff_123
  recurrence5A3_coeff_124
  recurrence5A3_coeff_125
  recurrence5A3_coeff_126
  recurrence5A3_coeff_127

attribute [local simp]
  recurrence5A3_coeff_128
  recurrence5A3_coeff_129
  recurrence5A3_coeff_130
  recurrence5A3_coeff_131
  recurrence5A3_coeff_132
  recurrence5A3_coeff_133
  recurrence5A3_coeff_134
  recurrence5A3_coeff_135
  recurrence5A3_coeff_136
  recurrence5A3_coeff_137
  recurrence5A3_coeff_138
  recurrence5A3_coeff_139
  recurrence5A3_coeff_140
  recurrence5A3_coeff_141
  recurrence5A3_coeff_142
  recurrence5A3_coeff_143
  recurrence5A3_coeff_144
  recurrence5A3_coeff_145
  recurrence5A3_coeff_146
  recurrence5A3_coeff_147
  recurrence5A3_coeff_148
  recurrence5A3_coeff_149
  recurrence5A3_coeff_150
  recurrence5A3_coeff_151
  recurrence5A3_coeff_152
  recurrence5A3_coeff_153
  recurrence5A3_coeff_154
  recurrence5A3_coeff_155
  recurrence5A3_coeff_156
  recurrence5A3_coeff_157
  recurrence5A3_coeff_158
  recurrence5A3_coeff_159
  recurrence5A3_coeff_160
  recurrence5A3_coeff_161
  recurrence5A3_coeff_162
  recurrence5A3_coeff_163
  recurrence5A3_coeff_164

private theorem recurrence5A3Square_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (198 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (198 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_198 :
    recurrence5A3Square.coeff 198 =
      -(((5854962965970539960692350176768358415929564648006178317720213 * 10 ^ 70 +
        2151694220550362963030388092244548740823084130472979477337000291908761) * 10 ^ 70 +
        5336156219102710445194773345608836187031711829284945181457539884581333) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 199 = 34 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 3 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_198_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_198_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (199 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (199 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_199 :
    recurrence5A3Square.coeff 199 =
      (((3529650839839117481991085417492177795523181220181161657000982 * 10 ^ 70 +
        3549561976029487334648673230148105351152485047431662457157357290520295) * 10 ^ 70 +
        8400904228185774956077976613627476572191493761961954980054012501116194) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 200 = 35 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 2 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_199_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_199_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (200 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (200 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_200 :
    recurrence5A3Square.coeff 200 =
      -(((2031425359192790476137600652948868417244070351281947479769261 * 10 ^ 70 +
        3496580799191041603442544040164916236768682212680808682257678932317979) * 10 ^ 70 +
        7519199766932589848777544837018274491704959293867659652336132368579047) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 201 = 36 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 1 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_200_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_200_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (201 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (201 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_201 :
    recurrence5A3Square.coeff 201 =
      (((1118101446674178105072408813795805097084767864609131291870959 * 10 ^ 70 +
        2718483571752904253766009209419277003658275579916106770685716697832346) * 10 ^ 70 +
        8101380399521506760754572810318784663493725641029629761994161692993156) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 202 = 37 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_201_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_201_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (202 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (202 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_202 :
    recurrence5A3Square.coeff 202 =
      -(((587776085034489181742722704362152415022671325208888741659143 * 10 ^ 70 +
        7407647591709426007324830850478747383931326856565915243108546491158947) * 10 ^ 70 +
        5770382269619844225999035064787523851079132422340502912342917328363400) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 203 = 38 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 31 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_202_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_202_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (203 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (203 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_203 :
    recurrence5A3Square.coeff 203 =
      (((293724495020284414742646707318533091051348636003840799794347 * 10 ^ 70 +
        0848957046153631202925748598011923816653635632768907748713825389404190) * 10 ^ 70 +
        9587573184102620602297883228382699756718449048510737060829855276623504) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 204 = 39 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 30 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_203_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_203_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (204 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (204 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_204 :
    recurrence5A3Square.coeff 204 =
      -(((138146235916756014185233960276830315276604659227619718950042 * 10 ^ 70 +
        5621815214009538176359639016930255616691817302773722261190002112407061) * 10 ^ 70 +
        3301498636217317506355315237792281465266561878775536786081262567223106) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 205 = 40 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 29 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_204_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_204_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (205 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (205 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_205 :
    recurrence5A3Square.coeff 205 =
      (((59931615319374241767326672524370710038306975290437454049528 * 10 ^ 70 +
        7440097757870403308896179313275423597982904468841654785735738144888850) * 10 ^ 70 +
        7760579398933309833241004641828713496709220593672530267603798516292862) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 206 = 41 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 28 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_205_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_205_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (206 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (206 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_206 :
    recurrence5A3Square.coeff 206 =
      -(((22914586769981557950246554087972311189008050161231720830279 * 10 ^ 70 +
        7926597319396733789269471782790881428292590685695793556198707163180052) * 10 ^ 70 +
        0319661169039109044608324629669152682338070708565897518853734000876014) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 207 = 42 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 27 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_206_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_206_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (207 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (207 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_207 :
    recurrence5A3Square.coeff 207 =
      (((6731369246930313602685835123634922289792745043722707048388 * 10 ^ 70 +
        0732706282695275527434783660026488741324047999644938363481640863482616) * 10 ^ 70 +
        9749892902928182452770237320994581283328814298508179892579379576435278) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 208 = 43 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 26 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_207_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_207_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (208 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (208 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_208 :
    recurrence5A3Square.coeff 208 =
      -(((467110432716333619273927970094717356228540193505189280638 * 10 ^ 70 +
        0073280821615806920862195282976508134186585692154920159147302227396376) * 10 ^ 70 +
        0127659044095977391138687251443728738735081071148392406371533227781138) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 209 = 44 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 25 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_208_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_208_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (209 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (209 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_209 :
    recurrence5A3Square.coeff 209 =
      -(((1429763217149544081871020217819506377314314363194472312655 * 10 ^ 70 +
        2704442104185773581299873302702121986794469920239816070555035238922577) * 10 ^ 70 +
        3161167998444256910652466351806593018932792193090182120058384057647620) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 210 = 45 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 24 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_209_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_209_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (210 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (210 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_210 :
    recurrence5A3Square.coeff 210 =
      (((1617307332044024782745970452879310057193144124250651412839 * 10 ^ 70 +
        4444739749277732709266995631056153579859771368344941770327622469415568) * 10 ^ 70 +
        6441966623150463089491583774186506059060430442014504040101632580208630) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 211 = 46 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 23 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_210_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_210_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (211 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (211 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_211 :
    recurrence5A3Square.coeff 211 =
      -(((1273576612115461003392454228112259966788798432688880640597 * 10 ^ 70 +
        6936558912361851468075072141823349206288764675865241186365954613516729) * 10 ^ 70 +
        2714362406862929629431234780658842875655134603132655628125589694632496) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 212 = 47 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 22 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_211_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_211_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (212 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (212 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_212 :
    recurrence5A3Square.coeff 212 =
      (((864229645484271579707317395321720879462866700144347582286 * 10 ^ 70 +
        5833979170191483996272174138365220131189731496669862554024512242952481) * 10 ^ 70 +
        3831928111162587755099597829505962832883481591195493878552608970892129) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 213 = 48 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 21 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_212_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_212_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (213 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (213 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_213 :
    recurrence5A3Square.coeff 213 =
      -(((537291077426076647307224153769029499729321498364986281415 * 10 ^ 70 +
        1308785514056070383626003157641489046357813296420328598683772479834389) * 10 ^ 70 +
        7985421111113724447875094722186302111529392023559604933013360383889956) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 214 = 49 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 20 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_213_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_213_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (214 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (214 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_214 :
    recurrence5A3Square.coeff 214 =
      (((314118366479036277206287405150093316606508846496231224643 * 10 ^ 70 +
        3499099353601243422945060497297648483885625698913192331188199818615048) * 10 ^ 70 +
        2359436178444118264332469906364503507120249635808556086920529378139176) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 215 = 50 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 19 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_214_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_214_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (215 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (215 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_215 :
    recurrence5A3Square.coeff 215 =
      -(((175012018588993423799011552077475955944490310495376031350 * 10 ^ 70 +
        6273256964686908273041603041432356335896946979170196605165649000144141) * 10 ^ 70 +
        2299682090664432159306488312650284856947184979346659261620976485988898) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 216 = 51 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 18 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_215_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_215_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (216 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (216 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_216 :
    recurrence5A3Square.coeff 216 =
      (((93624237253306707627581667445594295377018896745704616653 * 10 ^ 70 +
        7153373162677362050465416334983490579363535999500776248494433248403253) * 10 ^ 70 +
        8216001819229903372954493649727480499353752440603151321264818795449888) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 217 = 52 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 17 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_216_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_216_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 53,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (217 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (217 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_217 :
    recurrence5A3Square.coeff 217 =
      -(((48301683586353311190834066546538797934869372262681652681 * 10 ^ 70 +
        6766433316626920552027532818752376308442617859878330833860941722459376) * 10 ^ 70 +
        2916945120679827676284128003840514813396830415645795436370002825720110) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 218 = 53 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 16 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_217_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_217_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 54,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (218 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (218 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_218 :
    recurrence5A3Square.coeff 218 =
      (((24093216566173387368632616370739996423407835149317026632 * 10 ^ 70 +
        1646908569486428632738759641589487637251118359702920272253950613067396) * 10 ^ 70 +
        1240659926648550910691118398254140804226698902107228458979359754954763) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 219 = 54 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 15 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_218_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_218_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 55,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (219 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (219 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_219 :
    recurrence5A3Square.coeff 219 =
      -(((11634967875776707200779703184680047438899699745578394664 * 10 ^ 70 +
        3665067275435640215702996276237448686630695241167699497058356162760583) * 10 ^ 70 +
        9297617529956802863052285531563934742393063430503334180415804354372668) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 220 = 55 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 14 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_219_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_219_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 56,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (220 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (220 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_220 :
    recurrence5A3Square.coeff 220 =
      (((5442226222184442181022090389434098931140587687063668512 * 10 ^ 70 +
        3212941975014319931583593597890625019164956987962300936934450230948893) * 10 ^ 70 +
        0595164195662066107904580517682071005426620000539647367268258574348266) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 221 = 56 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 13 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_220_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_220_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 57,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (221 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (221 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_221 :
    recurrence5A3Square.coeff 221 =
      -(((2465108799776060159298239468653878378689171468462338266 * 10 ^ 70 +
        4033922956080004122413582367714588462161857783785998194627890438878644) * 10 ^ 70 +
        0254881036569507116881406067943759404679147190750771959268826227231080) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 222 = 57 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 12 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_221_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_221_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 58,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (222 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (222 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_222 :
    recurrence5A3Square.coeff 222 =
      (((1080416654695396955216837384590593432977152084487628607 * 10 ^ 70 +
        5351069845601064579351605469813805208994374062108528835594639777402731) * 10 ^ 70 +
        8001076633225130037156676121389643820785260787219509680109800172974581) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 223 = 58 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 11 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_222_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_222_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 59,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (223 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (223 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_223 :
    recurrence5A3Square.coeff 223 =
      -(((457543485806284131044013816400958949230193828866963174 * 10 ^ 70 +
        1212176691362584648481060205714136178004900882611299264566078998326938) * 10 ^ 70 +
        8926132646635553798433425073844365784898365414481822551158778353662890) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 224 = 59 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 10 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_223_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_223_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 60,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (224 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (224 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_224 :
    recurrence5A3Square.coeff 224 =
      (((186835514282463161218474385329571653255473007466068745 * 10 ^ 70 +
        1736990535502648469029649287251855144628759060159764860680830513223728) * 10 ^ 70 +
        8583433976169974785165586435471184177310826363745540971080773570858511) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 225 = 60 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 9 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_224_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_224_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 61,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (225 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (225 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_225 :
    recurrence5A3Square.coeff 225 =
      -(((73350452192243548026873980533639164248273316908141114 * 10 ^ 70 +
        8347215043818725235399138572730869609592573060580871711349733752374136) * 10 ^ 70 +
        2965828945300128914676533020393090203337343216062467165316333052023910) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 226 = 61 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 8 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_225_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_225_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 62,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (226 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (226 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_226 :
    recurrence5A3Square.coeff 226 =
      (((27572018997020516490081561002710623332273845057601440 * 10 ^ 70 +
        3888734135939594201927074789832156959837910715219924742158803638995549) * 10 ^ 70 +
        8591416631759839059855517503321589572056126191379844836319586521784128) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 227 = 62 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 7 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_226_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_226_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
