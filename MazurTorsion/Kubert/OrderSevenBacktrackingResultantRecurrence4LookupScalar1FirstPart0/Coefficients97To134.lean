/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3A4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1FirstPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1First coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4B0_coeff_1
  recurrence4B0_coeff_10
  recurrence4B0_coeff_100
  recurrence4B0_coeff_101
  recurrence4B0_coeff_102
  recurrence4B0_coeff_103
  recurrence4B0_coeff_104
  recurrence4B0_coeff_105
  recurrence4B0_coeff_106
  recurrence4B0_coeff_107
  recurrence4B0_coeff_108
  recurrence4B0_coeff_109
  recurrence4B0_coeff_11
  recurrence4B0_coeff_110
  recurrence4B0_coeff_111
  recurrence4B0_coeff_112
  recurrence4B0_coeff_113
  recurrence4B0_coeff_114
  recurrence4B0_coeff_115
  recurrence4B0_coeff_116
  recurrence4B0_coeff_117
  recurrence4B0_coeff_118
  recurrence4B0_coeff_119
  recurrence4B0_coeff_12
  recurrence4B0_coeff_120
  recurrence4B0_coeff_121
  recurrence4B0_coeff_122
  recurrence4B0_coeff_123
  recurrence4B0_coeff_124
  recurrence4B0_coeff_125
  recurrence4B0_coeff_126
  recurrence4B0_coeff_127
  recurrence4B0_coeff_128
  recurrence4B0_coeff_129
  recurrence4B0_coeff_13
  recurrence4B0_coeff_130
  recurrence4B0_coeff_131
  recurrence4B0_coeff_132
  recurrence4B0_coeff_133
  recurrence4B0_coeff_134
  recurrence4B0_coeff_135
  recurrence4B0_coeff_136
  recurrence4B0_coeff_137
  recurrence4B0_coeff_138
  recurrence4B0_coeff_139
  recurrence4B0_coeff_14
  recurrence4B0_coeff_140
  recurrence4B0_coeff_141
  recurrence4B0_coeff_142
  recurrence4B0_coeff_143
  recurrence4B0_coeff_144
  recurrence4B0_coeff_145
  recurrence4B0_coeff_146
  recurrence4B0_coeff_147
  recurrence4B0_coeff_148
  recurrence4B0_coeff_149
  recurrence4B0_coeff_15
  recurrence4B0_coeff_150
  recurrence4B0_coeff_151
  recurrence4B0_coeff_152
  recurrence4B0_coeff_153
  recurrence4B0_coeff_154
  recurrence4B0_coeff_155
  recurrence4B0_coeff_156

attribute [local simp]
  recurrence4B0_coeff_157
  recurrence4B0_coeff_158
  recurrence4B0_coeff_159
  recurrence4B0_coeff_16
  recurrence4B0_coeff_160
  recurrence4B0_coeff_161
  recurrence4B0_coeff_162
  recurrence4B0_coeff_163
  recurrence4B0_coeff_164
  recurrence4B0_coeff_165
  recurrence4B0_coeff_166
  recurrence4B0_coeff_167
  recurrence4B0_coeff_168
  recurrence4B0_coeff_169
  recurrence4B0_coeff_17
  recurrence4B0_coeff_170
  recurrence4B0_coeff_18
  recurrence4B0_coeff_19
  recurrence4B0_coeff_2
  recurrence4B0_coeff_20
  recurrence4B0_coeff_21
  recurrence4B0_coeff_22
  recurrence4B0_coeff_23
  recurrence4B0_coeff_24
  recurrence4B0_coeff_25
  recurrence4B0_coeff_26
  recurrence4B0_coeff_27
  recurrence4B0_coeff_28
  recurrence4B0_coeff_29
  recurrence4B0_coeff_3
  recurrence4B0_coeff_30
  recurrence4B0_coeff_31
  recurrence4B0_coeff_32
  recurrence4B0_coeff_33
  recurrence4B0_coeff_34
  recurrence4B0_coeff_35
  recurrence4B0_coeff_36
  recurrence4B0_coeff_37
  recurrence4B0_coeff_38
  recurrence4B0_coeff_39
  recurrence4B0_coeff_4
  recurrence4B0_coeff_40
  recurrence4B0_coeff_41
  recurrence4B0_coeff_42
  recurrence4B0_coeff_43
  recurrence4B0_coeff_44
  recurrence4B0_coeff_45
  recurrence4B0_coeff_46
  recurrence4B0_coeff_47
  recurrence4B0_coeff_48
  recurrence4B0_coeff_49
  recurrence4B0_coeff_5
  recurrence4B0_coeff_50
  recurrence4B0_coeff_51
  recurrence4B0_coeff_52
  recurrence4B0_coeff_53
  recurrence4B0_coeff_54
  recurrence4B0_coeff_55
  recurrence4B0_coeff_56
  recurrence4B0_coeff_57
  recurrence4B0_coeff_58
  recurrence4B0_coeff_59
  recurrence4B0_coeff_6
  recurrence4B0_coeff_60

attribute [local simp]
  recurrence4B0_coeff_61
  recurrence4B0_coeff_62
  recurrence4B0_coeff_63
  recurrence4B0_coeff_64
  recurrence4B0_coeff_65
  recurrence4B0_coeff_66
  recurrence4B0_coeff_67
  recurrence4B0_coeff_68
  recurrence4B0_coeff_69
  recurrence4B0_coeff_7
  recurrence4B0_coeff_70
  recurrence4B0_coeff_71
  recurrence4B0_coeff_72
  recurrence4B0_coeff_73
  recurrence4B0_coeff_74
  recurrence4B0_coeff_75
  recurrence4B0_coeff_76
  recurrence4B0_coeff_77
  recurrence4B0_coeff_78
  recurrence4B0_coeff_79
  recurrence4B0_coeff_8
  recurrence4B0_coeff_80
  recurrence4B0_coeff_81
  recurrence4B0_coeff_82
  recurrence4B0_coeff_83
  recurrence4B0_coeff_84
  recurrence4B0_coeff_85
  recurrence4B0_coeff_86
  recurrence4B0_coeff_87
  recurrence4B0_coeff_88
  recurrence4B0_coeff_89
  recurrence4B0_coeff_9
  recurrence4B0_coeff_90
  recurrence4B0_coeff_91
  recurrence4B0_coeff_92
  recurrence4B0_coeff_93
  recurrence4B0_coeff_94
  recurrence4B0_coeff_95
  recurrence4B0_coeff_96
  recurrence4B0_coeff_97
  recurrence4B0_coeff_98
  recurrence4B0_coeff_99
  recurrence4B3A4_coeff_0
  recurrence4B3A4_coeff_1
  recurrence4B3A4_coeff_10
  recurrence4B3A4_coeff_100
  recurrence4B3A4_coeff_101
  recurrence4B3A4_coeff_102
  recurrence4B3A4_coeff_103
  recurrence4B3A4_coeff_104
  recurrence4B3A4_coeff_105
  recurrence4B3A4_coeff_106
  recurrence4B3A4_coeff_107
  recurrence4B3A4_coeff_108
  recurrence4B3A4_coeff_109
  recurrence4B3A4_coeff_11
  recurrence4B3A4_coeff_110
  recurrence4B3A4_coeff_111
  recurrence4B3A4_coeff_112
  recurrence4B3A4_coeff_113
  recurrence4B3A4_coeff_114
  recurrence4B3A4_coeff_115
  recurrence4B3A4_coeff_116
  recurrence4B3A4_coeff_117

attribute [local simp]
  recurrence4B3A4_coeff_118
  recurrence4B3A4_coeff_119
  recurrence4B3A4_coeff_12
  recurrence4B3A4_coeff_120
  recurrence4B3A4_coeff_121
  recurrence4B3A4_coeff_122
  recurrence4B3A4_coeff_123
  recurrence4B3A4_coeff_124
  recurrence4B3A4_coeff_125
  recurrence4B3A4_coeff_126
  recurrence4B3A4_coeff_127
  recurrence4B3A4_coeff_128
  recurrence4B3A4_coeff_129
  recurrence4B3A4_coeff_13
  recurrence4B3A4_coeff_130
  recurrence4B3A4_coeff_131
  recurrence4B3A4_coeff_132
  recurrence4B3A4_coeff_133
  recurrence4B3A4_coeff_134
  recurrence4B3A4_coeff_135
  recurrence4B3A4_coeff_136
  recurrence4B3A4_coeff_137
  recurrence4B3A4_coeff_138
  recurrence4B3A4_coeff_139
  recurrence4B3A4_coeff_14
  recurrence4B3A4_coeff_140
  recurrence4B3A4_coeff_141
  recurrence4B3A4_coeff_142
  recurrence4B3A4_coeff_143
  recurrence4B3A4_coeff_144
  recurrence4B3A4_coeff_145
  recurrence4B3A4_coeff_146
  recurrence4B3A4_coeff_147
  recurrence4B3A4_coeff_148
  recurrence4B3A4_coeff_149
  recurrence4B3A4_coeff_15
  recurrence4B3A4_coeff_150
  recurrence4B3A4_coeff_151
  recurrence4B3A4_coeff_152
  recurrence4B3A4_coeff_153
  recurrence4B3A4_coeff_154
  recurrence4B3A4_coeff_155
  recurrence4B3A4_coeff_156
  recurrence4B3A4_coeff_157
  recurrence4B3A4_coeff_158
  recurrence4B3A4_coeff_159
  recurrence4B3A4_coeff_16
  recurrence4B3A4_coeff_160
  recurrence4B3A4_coeff_161
  recurrence4B3A4_coeff_162
  recurrence4B3A4_coeff_163
  recurrence4B3A4_coeff_164
  recurrence4B3A4_coeff_165
  recurrence4B3A4_coeff_166
  recurrence4B3A4_coeff_167
  recurrence4B3A4_coeff_168
  recurrence4B3A4_coeff_169
  recurrence4B3A4_coeff_17
  recurrence4B3A4_coeff_18
  recurrence4B3A4_coeff_19
  recurrence4B3A4_coeff_2
  recurrence4B3A4_coeff_20
  recurrence4B3A4_coeff_21
  recurrence4B3A4_coeff_22

attribute [local simp]
  recurrence4B3A4_coeff_23
  recurrence4B3A4_coeff_24
  recurrence4B3A4_coeff_25
  recurrence4B3A4_coeff_26
  recurrence4B3A4_coeff_27
  recurrence4B3A4_coeff_28
  recurrence4B3A4_coeff_29
  recurrence4B3A4_coeff_3
  recurrence4B3A4_coeff_30
  recurrence4B3A4_coeff_31
  recurrence4B3A4_coeff_32
  recurrence4B3A4_coeff_33
  recurrence4B3A4_coeff_34
  recurrence4B3A4_coeff_35
  recurrence4B3A4_coeff_36
  recurrence4B3A4_coeff_37
  recurrence4B3A4_coeff_38
  recurrence4B3A4_coeff_39
  recurrence4B3A4_coeff_4
  recurrence4B3A4_coeff_40
  recurrence4B3A4_coeff_41
  recurrence4B3A4_coeff_42
  recurrence4B3A4_coeff_43
  recurrence4B3A4_coeff_44
  recurrence4B3A4_coeff_45
  recurrence4B3A4_coeff_46
  recurrence4B3A4_coeff_47
  recurrence4B3A4_coeff_48
  recurrence4B3A4_coeff_49
  recurrence4B3A4_coeff_5
  recurrence4B3A4_coeff_50
  recurrence4B3A4_coeff_51
  recurrence4B3A4_coeff_52
  recurrence4B3A4_coeff_53
  recurrence4B3A4_coeff_54
  recurrence4B3A4_coeff_55
  recurrence4B3A4_coeff_56
  recurrence4B3A4_coeff_57
  recurrence4B3A4_coeff_58
  recurrence4B3A4_coeff_59
  recurrence4B3A4_coeff_6
  recurrence4B3A4_coeff_60
  recurrence4B3A4_coeff_61
  recurrence4B3A4_coeff_62
  recurrence4B3A4_coeff_63
  recurrence4B3A4_coeff_64
  recurrence4B3A4_coeff_65
  recurrence4B3A4_coeff_66
  recurrence4B3A4_coeff_67
  recurrence4B3A4_coeff_68
  recurrence4B3A4_coeff_69
  recurrence4B3A4_coeff_7
  recurrence4B3A4_coeff_70
  recurrence4B3A4_coeff_71
  recurrence4B3A4_coeff_72
  recurrence4B3A4_coeff_73
  recurrence4B3A4_coeff_74
  recurrence4B3A4_coeff_75
  recurrence4B3A4_coeff_76
  recurrence4B3A4_coeff_77
  recurrence4B3A4_coeff_78
  recurrence4B3A4_coeff_79
  recurrence4B3A4_coeff_8
  recurrence4B3A4_coeff_80

attribute [local simp]
  recurrence4B3A4_coeff_81
  recurrence4B3A4_coeff_82
  recurrence4B3A4_coeff_83
  recurrence4B3A4_coeff_84
  recurrence4B3A4_coeff_85
  recurrence4B3A4_coeff_86
  recurrence4B3A4_coeff_87
  recurrence4B3A4_coeff_88
  recurrence4B3A4_coeff_89
  recurrence4B3A4_coeff_9
  recurrence4B3A4_coeff_90
  recurrence4B3A4_coeff_91
  recurrence4B3A4_coeff_92
  recurrence4B3A4_coeff_93
  recurrence4B3A4_coeff_94
  recurrence4B3A4_coeff_95
  recurrence4B3A4_coeff_96
  recurrence4B3A4_coeff_97
  recurrence4B3A4_coeff_98
  recurrence4B3A4_coeff_99

private theorem recurrence4Scalar1First_coeff_97_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (97 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (97 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_97 :
    recurrence4Scalar1First.coeff 97 =
      -((((129392609310479171255 * 10 ^ 70 +
        5397891265511915293218200672376495475581431235959383523580902625903332) * 10 ^ 70 +
        1084328841548516342918549791064357767747418659332969479277536182131522) * 10 ^ 70 +
        3312260529996916898195707416175557544536219036200809355056910966614480) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 98,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (97 - x)) = _
  rw [show 98 = 1 +
    97 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 97 = 32 +
      65 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 65 = 32 +
      33 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_97_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_98_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (98 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (98 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_98 :
    recurrence4Scalar1First.coeff 98 =
      ((((1863750949562697238326 * 10 ^ 70 +
        9747946708394149619297007467656441252156373517013749352762782922709870) * 10 ^ 70 +
        5902414752728270576256174036001109242028098295229599297300503011924818) * 10 ^ 70 +
        7809998613803063478836194445083635722024117796793826896425507191626350) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 99,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (98 - x)) = _
  rw [show 99 = 1 +
    98 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 98 = 32 +
      66 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 66 = 32 +
      34 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_98_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_99_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (99 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (99 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_99 :
    recurrence4Scalar1First.coeff 99 =
      -((((25819274771531981660998 * 10 ^ 70 +
        5917577828013675450950733545342609951309378896453798145414294975140105) * 10 ^ 70 +
        1870010111710032578482085480158938246116384370410470609547354672996298) * 10 ^ 70 +
        1444786738847538675338876256286880963892657205577614287090928563146216) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 100,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (99 - x)) = _
  rw [show 100 = 1 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_99_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_100_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (100 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (100 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_100 :
    recurrence4Scalar1First.coeff 100 =
      ((((344869907367034617635578 * 10 ^ 70 +
        0794008286255646590837432012008624275682360657444202551996750961551310) * 10 ^ 70 +
        5878378917576422300375574886438566326898637061287265268502166229878281) * 10 ^ 70 +
        6001147161366260064947118649554541356349504917124788946893426345548540) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 101,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (100 - x)) = _
  rw [show 101 = 1 +
    100 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 100 = 32 +
      68 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 68 = 32 +
      36 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_100_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_101_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (101 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (101 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_101 :
    recurrence4Scalar1First.coeff 101 =
      -((((4450114320154813275349324 * 10 ^ 70 +
        0195669553807137564629899664354405261609474980131023428012283476309517) * 10 ^ 70 +
        4874070745918843363824091664276375937586093829560843256418003592564892) * 10 ^ 70 +
        8156535801311350594009935570615894878381560384274807219833222784541812) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 102,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (101 - x)) = _
  rw [show 102 = 1 +
    101 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_101_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_102_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (102 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (102 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_102 :
    recurrence4Scalar1First.coeff 102 =
      ((((55562359351580482281880358 * 10 ^ 70 +
        2538014636209657951000381002725515753619902001055571113224286315705805) * 10 ^ 70 +
        2858442022717081708296300584242132706143643781067250601082739293804711) * 10 ^ 70 +
        4509183624576928239657013578072719876108940030513348557983065102860976) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 103,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (102 - x)) = _
  rw [show 103 = 1 +
    102 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 102 = 32 +
      70 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 70 = 32 +
      38 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_102_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_103_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (103 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (103 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_103 :
    recurrence4Scalar1First.coeff 103 =
      -((((672134381912668617900538843 * 10 ^ 70 +
        0877304522789447356766380393278902812176992419505475807635592667919772) * 10 ^ 70 +
        1577562451702101406886794862725478407701704212784187951785979337497399) * 10 ^ 70 +
        3313265495835860426212121850729639435885077361305561431205249024798872) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 104,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (103 - x)) = _
  rw [show 104 = 1 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_103_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_104_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (104 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (104 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_104 :
    recurrence4Scalar1First.coeff 104 =
      ((((7886465543777286245390717622 * 10 ^ 70 +
        2456002336363050199692812675592266012952144072909754082128850191275009) * 10 ^ 70 +
        2270509039693993167071110772197164972417109449818706313580295235496514) * 10 ^ 70 +
        9299217849829733138053626109090174715741436907484957394238021504843635) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 105,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (104 - x)) = _
  rw [show 105 = 1 +
    104 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 104 = 32 +
      72 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 72 = 32 +
      40 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_104_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_105_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (105 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (105 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_105 :
    recurrence4Scalar1First.coeff 105 =
      -((((89841630451946888951333371658 * 10 ^ 70 +
        4632901658323283634877259100320916471438352338423969207746508952055600) * 10 ^ 70 +
        6233928022217904867290348081736879627914022725323678402585463097686101) * 10 ^ 70 +
        4625503721983433654297629528752907963532313177215244803366476754744013) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 106,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (105 - x)) = _
  rw [show 106 = 1 +
    105 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 32 +
      41 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_105_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_106_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (106 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (106 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_106 :
    recurrence4Scalar1First.coeff 106 =
      ((((994506197374288656392520707558 * 10 ^ 70 +
        7816206403701599124118784411233787101160139802020018421660213919896224) * 10 ^ 70 +
        2707374974177589115545809175288750796016840309230944355521512971089649) * 10 ^ 70 +
        8362673410474489539240256877985051256009096257570079153124642377671622) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 107,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (106 - x)) = _
  rw [show 107 = 1 +
    106 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 106 = 32 +
      74 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 74 = 32 +
      42 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_106_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_107_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (107 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (107 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_107 :
    recurrence4Scalar1First.coeff 107 =
      -((((10705232218363285836132549097511 * 10 ^ 70 +
        8625767559104082193605946571655382823042624136657748619278871143012649) * 10 ^ 70 +
        9878258535573054833395458700418793899073926348284794064150228647391229) * 10 ^ 70 +
        4133550346819777209649147129390487651592434685649786211658533222276538) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 108,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (107 - x)) = _
  rw [show 108 = 1 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_107_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_108_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (108 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (108 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_108 :
    recurrence4Scalar1First.coeff 108 =
      ((((112133085308131377798562473227151 * 10 ^ 70 +
        3202989519828741253340526893194970062009114733615819958082813413592054) * 10 ^ 70 +
        9473991767699910839592006985168736523316437140041243921453484488315071) * 10 ^ 70 +
        4043116353868747911590962734285492139361964917538430414383275370750839) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 109,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (108 - x)) = _
  rw [show 109 = 1 +
    108 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 108 = 32 +
      76 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 76 = 32 +
      44 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_108_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_109_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (109 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (109 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_109 :
    recurrence4Scalar1First.coeff 109 =
      -((((1143623794498633207427570047928014 * 10 ^ 70 +
        3367412819250727513578298835033260609314611178203536968346734262830215) * 10 ^ 70 +
        8353905257789950456386770773076644892229890356097849862767415150014236) * 10 ^ 70 +
        9944519637419500825932263089306876112839351160845931756826193220748244) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 110,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (109 - x)) = _
  rw [show 110 = 1 +
    109 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_109_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_110_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (110 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (110 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_110 :
    recurrence4Scalar1First.coeff 110 =
      ((((11362762349448780000661267038844991 * 10 ^ 70 +
        4792842592110432622476892760244347528935561940016727163975991217478591) * 10 ^ 70 +
        5157735328563493097030971764405309002473111119412255242581635874728616) * 10 ^ 70 +
        6493916021165774606009556112981040823100514012095990756162382598353445) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 111,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (110 - x)) = _
  rw [show 111 = 1 +
    110 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 110 = 32 +
      78 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 78 = 32 +
      46 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_110_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_111_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (111 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (111 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_111 :
    recurrence4Scalar1First.coeff 111 =
      -((((110041417431940752062548289781863081 * 10 ^ 70 +
        4376000872706055480594082439054610886935238489441791069722199777796866) * 10 ^ 70 +
        5343598599847382854445237329861073952564498350724393389933142327534977) * 10 ^ 70 +
        4055736621520895260207776871949691592949879553460630481654028767985504) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 112,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (111 - x)) = _
  rw [show 112 = 1 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_111_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_112_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (112 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (112 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_112 :
    recurrence4Scalar1First.coeff 112 =
      ((((1039210649645158129342724207349436539 * 10 ^ 70 +
        0675327868202785716494982007433380980451961409183442015315332590512932) * 10 ^ 70 +
        8410666444730780784417850403763074289503083395362251101487444642996238) * 10 ^ 70 +
        1626090808410985954525747049790809848235587120806469157941142155708212) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 113,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (112 - x)) = _
  rw [show 113 = 1 +
    112 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 112 = 32 +
      80 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 80 = 32 +
      48 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_112_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_113_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (113 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (113 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_113 :
    recurrence4Scalar1First.coeff 113 =
      -((((9574488718705527583313003381759024036 * 10 ^ 70 +
        1772958540739158462755651300559094633886838413075368224598504786646622) * 10 ^ 70 +
        1497011261300464983482117231622744639645836953241979654910474651493168) * 10 ^ 70 +
        2396489504339665486511867998104218436295055093619296511986658626545990) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 114,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (113 - x)) = _
  rw [show 114 = 1 +
    113 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_113_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_114_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (114 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (114 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_114 :
    recurrence4Scalar1First.coeff 114 =
      ((((86093283663389167705052223604753506184 * 10 ^ 70 +
        8180885802184394612034695813511938174858377792235030297057198167769520) * 10 ^ 70 +
        4518379302800767477064797494496855205833547550523031149640535973567839) * 10 ^ 70 +
        6997042187857693164593384707393299683341731609257640608580616273980491) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 115,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (114 - x)) = _
  rw [show 115 = 1 +
    114 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_114_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_115_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (115 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (115 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_115 :
    recurrence4Scalar1First.coeff 115 =
      -((((755841812347524707791789486722902811970 * 10 ^ 70 +
        2313932438509953532844888391372960877874710293175429849784863740809772) * 10 ^ 70 +
        0915353159351981642811527577001579500794480670548975856859704317686149) * 10 ^ 70 +
        4914495223397829897298181578209773152483308189376005639138422448451909) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 116,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (115 - x)) = _
  rw [show 116 = 1 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_115_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_116_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (116 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (116 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_116 :
    recurrence4Scalar1First.coeff 116 =
      ((((6481227434593589119034719502682847909510 * 10 ^ 70 +
        4190647407638107449324980367684880443377461679285607425429804477330933) * 10 ^ 70 +
        0259652434009283856510273918342020348525241521362293656855557488618958) * 10 ^ 70 +
        2979480794080300456935905366160820853248844432424332572138158778741604) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 117,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (116 - x)) = _
  rw [show 117 = 1 +
    116 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 116 = 32 +
      84 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 84 = 32 +
      52 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_116_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_117_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (117 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (117 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_117 :
    recurrence4Scalar1First.coeff 117 =
      -((((54299595374493603404768267819279033465989 * 10 ^ 70 +
        3230496376719790082153287443354291932313758855379417561708032391945486) * 10 ^ 70 +
        8531464538595565136065800200267074662098517908961256295887692327128733) * 10 ^ 70 +
        0377011971778623409064642096054011535832646149811985968071677496380558) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 118,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (117 - x)) = _
  rw [show 118 = 1 +
    117 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 117 = 32 +
      85 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_117_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_118_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (118 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (118 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_118 :
    recurrence4Scalar1First.coeff 118 =
      ((((444620620084843664776221108172005724405082 * 10 ^ 70 +
        8891454405036674598346279745783508469083894974768476001067936062251653) * 10 ^ 70 +
        7832113437750631484078318759002347654835773919168879769250164872848843) * 10 ^ 70 +
        0154147844976888223327024133017614215254460747077888212816998854685836) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 119,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (118 - x)) = _
  rw [show 119 = 1 +
    118 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_118_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_119_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (119 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (119 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_119 :
    recurrence4Scalar1First.coeff 119 =
      -((((3559345492510574305286155949738986283724689 * 10 ^ 70 +
        9785494557175688727278993183876967963344696183494558916196708934712648) * 10 ^ 70 +
        1163761808941880101073586215435746770088080629025020526059991948036457) * 10 ^ 70 +
        4082066528598026375730309504365925879036753566350026614731215740385847) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 120,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (119 - x)) = _
  rw [show 120 = 1 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_119_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_120_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (120 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (120 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_120 :
    recurrence4Scalar1First.coeff 120 =
      ((((27865440205704561106671880266331660639554772 * 10 ^ 70 +
        3370511549709318033879969437674430247075440119027214779172696340675301) * 10 ^ 70 +
        8538493560286128522263932192332117504351507795193925774101386184303700) * 10 ^ 70 +
        6540199861227365696349849809594480748733562300841438849519104075365286) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 121,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (120 - x)) = _
  rw [show 121 = 1 +
    120 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 120 = 32 +
      88 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 88 = 32 +
      56 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_120_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_121_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (121 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (121 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_121 :
    recurrence4Scalar1First.coeff 121 =
      -((((213402220541188117021738720135525701376873725 * 10 ^ 70 +
        3195002614652583217529796957152862825341957819925995159147940993581465) * 10 ^ 70 +
        9754067148978080052320022623599994773302676758662991679665391065920397) * 10 ^ 70 +
        7909592110648289365572465099386808273197753284917671703868291957370010) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 122,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (121 - x)) = _
  rw [show 122 = 1 +
    121 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 121 = 32 +
      89 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_121_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_122_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (122 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (122 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_122 :
    recurrence4Scalar1First.coeff 122 =
      ((((1599138621320932665533618517659131533598494749 * 10 ^ 70 +
        6276688145478707450576452086793565157400462475715390701402257346158440) * 10 ^ 70 +
        6921519567692069082208509110279211037215290325221969024481233369427278) * 10 ^ 70 +
        3423562218076665826054109831297944864614337820009383766261963752961575) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 123,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (122 - x)) = _
  rw [show 123 = 1 +
    122 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_122_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_123_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (123 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (123 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_123 :
    recurrence4Scalar1First.coeff 123 =
      -((((11728422131036760979055434019656060727493132337 * 10 ^ 70 +
        0470482778370215623755898193819705412405547660447826332533773833588494) * 10 ^ 70 +
        3577929683691389020639754272791636446899086803605102959409259802621883) * 10 ^ 70 +
        8283396622928748186713530478663327909930426768976907568544028058063915) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 124,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (123 - x)) = _
  rw [show 124 = 1 +
    123 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 32 +
      59 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_123_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_124_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (124 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (124 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_124 :
    recurrence4Scalar1First.coeff 124 =
      ((((84210671164746861265692740138135081968916477335 * 10 ^ 70 +
        2038565427723129686147254829558356990051920622350411158009119599806344) * 10 ^ 70 +
        2704253658127996664923560705002250786786275042087866997190005101967209) * 10 ^ 70 +
        9049763819429630316188662541471719419388167743219832899208870904589209) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 125,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (124 - x)) = _
  rw [show 125 = 1 +
    124 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 124 = 32 +
      92 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 92 = 32 +
      60 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_124_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_125_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (125 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (125 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_125 :
    recurrence4Scalar1First.coeff 125 =
      -((((592069149871077944726042632882237271680532215611 * 10 ^ 70 +
        5697571668130487289124798704004279377765866039811229677356417735088668) * 10 ^ 70 +
        6624257869832752439393002219426321899172575745321120870312603898032679) * 10 ^ 70 +
        7325733928855340777780862866801782317841002213222847096216657453796735) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 126,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (125 - x)) = _
  rw [show 126 = 1 +
    125 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 125 = 32 +
      93 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 93 = 32 +
      61 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_125_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_126_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (126 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (126 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_126 :
    recurrence4Scalar1First.coeff 126 =
      ((((4077138039877318614774858929442855274114289010636 * 10 ^ 70 +
        9718672019072308557317509350229596194323265004046584895073211883669071) * 10 ^ 70 +
        8906846516690705970076365052177092677752493778499722308551753430085110) * 10 ^ 70 +
        9676536369136901693238776336583707195978410903749102007315675204216506) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 127,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (126 - x)) = _
  rw [show 127 = 1 +
    126 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 126 = 32 +
      94 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 94 = 32 +
      62 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_126_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_127_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (127 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (127 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_127 :
    recurrence4Scalar1First.coeff 127 =
      -((((27505051128543725880570684193317394368527297314575 * 10 ^ 70 +
        7010588356332171293268131107097890348586999730659431598969974914430492) * 10 ^ 70 +
        2130206575819946838446021090654780816686097411062302719401433458584568) * 10 ^ 70 +
        0722008889885019228153669022391828554406003504039330097823385944597382) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 128,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (127 - x)) = _
  rw [show 128 = 1 +
    127 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_127_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_128_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (128 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (128 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_128 :
    recurrence4Scalar1First.coeff 128 =
      ((((181817891527707098846432927691679648742411161127561 * 10 ^ 70 +
        0029818053124029450692731603179398356827722166665610541112978881760194) * 10 ^ 70 +
        2139722958714758538170551189437974402861624600937779973028449112622041) * 10 ^ 70 +
        8511961783480584082066244781556191138022185463367688450476713542552153) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 129,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (128 - x)) = _
  rw [show 129 = 1 +
    128 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 128 = 32 +
      96 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_128_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_129_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (129 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (129 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_129 :
    recurrence4Scalar1First.coeff 129 =
      -((((1177925542687752629402567305462750200947795891047821 * 10 ^ 70 +
        1550680416783910814452048135909343571423744451712222404712517176715697) * 10 ^ 70 +
        6367483892531759165016255622720108975358372338928388052301641180812010) * 10 ^ 70 +
        7055250316185455831326001214005585974284275273621352130796666688467012) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 130,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (129 - x)) = _
  rw [show 130 = 1 +
    129 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 129 = 32 +
      97 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 97 = 32 +
      65 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 65 = 32 +
      33 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_129_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_130_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (130 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (130 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_130 :
    recurrence4Scalar1First.coeff 130 =
      ((((7480715227982912333719891211069455695838505808963028 * 10 ^ 70 +
        9163878707298754905672243553952187119293033074093084028702086529155996) * 10 ^ 70 +
        2920425523276744790772567705595064612781484976303936027831875647351060) * 10 ^ 70 +
        2249201593555804363365951338966943896782642929609103862748307959232454) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 131,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (130 - x)) = _
  rw [show 131 = 1 +
    130 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 130 = 32 +
      98 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 98 = 32 +
      66 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 66 = 32 +
      34 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_130_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_131_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (131 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (131 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_131 :
    recurrence4Scalar1First.coeff 131 =
      -((((46579699521249231083764034393895772957866822295494769 * 10 ^ 70 +
        6509125954134831907212605642652025904713790486741891535779820667333563) * 10 ^ 70 +
        4073819818130922616688527742222992741781148732648648123299995553794215) * 10 ^ 70 +
        7527987310568998061508299575575319285949389185071472437031433513516242) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 132,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (131 - x)) = _
  rw [show 132 = 1 +
    131 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_131_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_132_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (132 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (132 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_132 :
    recurrence4Scalar1First.coeff 132 =
      ((((284419976367939857043706345313491960229599930684122044 * 10 ^ 70 +
        0751894841951167893560682077874698988400576464749874688706436638426257) * 10 ^ 70 +
        8389959985342835655867144978053235442315516382964209748357798627281869) * 10 ^ 70 +
        2275616440559155122826178227221724196749557435359823398362550847874295) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 133,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (132 - x)) = _
  rw [show 133 = 1 +
    132 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 132 = 32 +
      100 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 100 = 32 +
      68 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 68 = 32 +
      36 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_132_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_133_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (133 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (133 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_133 :
    recurrence4Scalar1First.coeff 133 =
      -((((1703383477936989462958709295834383069095002002388675762 * 10 ^ 70 +
        4929341397790767443629927551123715716187507602226353516083920759756228) * 10 ^ 70 +
        6170876363453909977863215906213802524284807090564730332684739338438148) * 10 ^ 70 +
        1911929158115984378746262509942981048639020474621594686297597903770815) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 134,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (133 - x)) = _
  rw [show 134 = 1 +
    133 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_133_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_134_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (134 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (134 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_134 :
    recurrence4Scalar1First.coeff 134 =
      ((((10007609814354419190568853620788779728902495442073110801 * 10 ^ 70 +
        4899511491715272833159046193543833898987372562409231746474545371022627) * 10 ^ 70 +
        4700753356086079180068952633024543761474862251474027064462942108476553) * 10 ^ 70 +
        8903789905950511096561777405507316168987231858261305917949879595978255) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 135,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (134 - x)) = _
  rw [show 135 = 1 +
    134 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 32 +
      70 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 70 = 32 +
      38 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_134_prefix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
