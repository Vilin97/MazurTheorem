/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA3
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: B1A3 coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence5B1_coeff_0
  recurrence5B1_coeff_1
  recurrence5B1_coeff_2
  recurrence5B1_coeff_3
  recurrence5B1_coeff_4
  recurrence5B1_coeff_5
  recurrence5B1_coeff_6
  recurrence5B1_coeff_7
  recurrence5B1_coeff_8
  recurrence5B1_coeff_9
  recurrence5B1_coeff_10
  recurrence5B1_coeff_11
  recurrence5B1_coeff_12
  recurrence5B1_coeff_13
  recurrence5B1_coeff_14
  recurrence5B1_coeff_15
  recurrence5B1_coeff_16
  recurrence5B1_coeff_17
  recurrence5B1_coeff_18
  recurrence5B1_coeff_19
  recurrence5B1_coeff_20
  recurrence5B1_coeff_21
  recurrence5B1_coeff_22
  recurrence5B1_coeff_23
  recurrence5B1_coeff_24
  recurrence5B1_coeff_25
  recurrence5B1_coeff_26
  recurrence5B1_coeff_27
  recurrence5B1_coeff_28
  recurrence5B1_coeff_29
  recurrence5B1_coeff_30
  recurrence5B1_coeff_31
  recurrence5B1_coeff_32
  recurrence5B1_coeff_33
  recurrence5B1_coeff_34
  recurrence5B1_coeff_35
  recurrence5B1_coeff_36
  recurrence5B1_coeff_37
  recurrence5B1_coeff_38
  recurrence5B1_coeff_39
  recurrence5B1_coeff_40
  recurrence5B1_coeff_41
  recurrence5B1_coeff_42
  recurrence5B1_coeff_43
  recurrence5B1_coeff_44
  recurrence5B1_coeff_45
  recurrence5B1_coeff_46
  recurrence5B1_coeff_47
  recurrence5B1_coeff_48
  recurrence5B1_coeff_49
  recurrence5B1_coeff_50
  recurrence5B1_coeff_51
  recurrence5B1_coeff_52
  recurrence5B1_coeff_53
  recurrence5B1_coeff_54
  recurrence5B1_coeff_55
  recurrence5B1_coeff_56
  recurrence5B1_coeff_57
  recurrence5B1_coeff_58
  recurrence5B1_coeff_59
  recurrence5B1_coeff_60
  recurrence5B1_coeff_61
  recurrence5B1_coeff_62
  recurrence5B1_coeff_63

attribute [local simp]
  recurrence5B1_coeff_64
  recurrence5B1_coeff_65
  recurrence5B1_coeff_66
  recurrence5B1_coeff_67
  recurrence5B1_coeff_68
  recurrence5B1_coeff_69
  recurrence5B1_coeff_70
  recurrence5B1_coeff_71
  recurrence5B1_coeff_72
  recurrence5B1_coeff_73
  recurrence5B1_coeff_74
  recurrence5B1_coeff_75
  recurrence5B1_coeff_76
  recurrence5B1_coeff_77
  recurrence5B1_coeff_78
  recurrence5B1_coeff_79
  recurrence5B1_coeff_80
  recurrence5B1_coeff_81
  recurrence5B1_coeff_82
  recurrence5B1_coeff_83
  recurrence5B1_coeff_84
  recurrence5B1_coeff_85
  recurrence5B1_coeff_86
  recurrence5B1_coeff_87
  recurrence5B1_coeff_88
  recurrence5B1_coeff_89
  recurrence5B1_coeff_90
  recurrence5B1_coeff_91
  recurrence5B1_coeff_92
  recurrence5B1_coeff_93
  recurrence5B1_coeff_94
  recurrence5B1_coeff_95
  recurrence5B1_coeff_96
  recurrence5B1_coeff_97
  recurrence5B1_coeff_98
  recurrence5B1_coeff_99
  recurrence5B1_coeff_100
  recurrence5B1_coeff_101
  recurrence5B1_coeff_102
  recurrence5B1_coeff_103
  recurrence5B1_coeff_104
  recurrence5B1_coeff_105
  recurrence5B1_coeff_106
  recurrence5B1_coeff_107
  recurrence5B1_coeff_108
  recurrence5B1_coeff_109
  recurrence5B1_coeff_110
  recurrence5B1_coeff_111
  recurrence5B1_coeff_112
  recurrence5B1_coeff_113
  recurrence5B1_coeff_114
  recurrence5B1_coeff_115
  recurrence5B1_coeff_116
  recurrence5B1_coeff_117
  recurrence5B1_coeff_118
  recurrence5B1_coeff_119
  recurrence5B1_coeff_120
  recurrence5B1_coeff_121
  recurrence5B1_coeff_122
  recurrence5B1_coeff_123
  recurrence5B1_coeff_124
  recurrence5B1_coeff_125
  recurrence5B1_coeff_126
  recurrence5B1_coeff_127

attribute [local simp]
  recurrence5B1_coeff_128
  recurrence5B1_coeff_129
  recurrence5B1_coeff_130
  recurrence5B1_coeff_131
  recurrence5B1_coeff_132
  recurrence5B1_coeff_133
  recurrence5B1_coeff_134
  recurrence5B1_coeff_135
  recurrence5B1_coeff_136
  recurrence5B1_coeff_137
  recurrence5B1_coeff_138
  recurrence5B1_coeff_139
  recurrence5B1_coeff_140
  recurrence5B1_coeff_141
  recurrence5B1_coeff_142
  recurrence5B1_coeff_143
  recurrence5B1_coeff_144
  recurrence5B1_coeff_145
  recurrence5B1_coeff_146
  recurrence5B1_coeff_147
  recurrence5B1_coeff_148
  recurrence5B1_coeff_149
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

attribute [local simp]
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

attribute [local simp]
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

private theorem recurrence5B1A3_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 55,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (219 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (219 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_219 :
    recurrence5B1A3.coeff 219 =
      ((((35951 * 10 ^ 70 +
        3118675644860620319225091479549013132107584358666302394984941168722911) * 10 ^ 70 +
        3032956186719212211918777841462795937904475017141234177762537877871920) * 10 ^ 70 +
        4183203191266750708426957004966634747738409509516853575241795253500681) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 101 = 31 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_219_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_219_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 56,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (220 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (220 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_220 :
    recurrence5B1A3.coeff 220 =
      -((((12544 * 10 ^ 70 +
        5802096953116866652678962306672942973594221143320558275263690971470329) * 10 ^ 70 +
        6955558849429970588269868835269789503675975357708088298443997306057317) * 10 ^ 70 +
        0587362053479474232615860245317548126162520875892368763535416375528349) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 101 = 30 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_220_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_220_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 57,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (221 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (221 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_221 :
    recurrence5B1A3.coeff 221 =
      ((((4315 * 10 ^ 70 +
        9818466504075883589036845643209886948801551887317126722933946548581588) * 10 ^ 70 +
        4880075929843660877884508788475088574236111068764898354174189702636384) * 10 ^ 70 +
        1688710275540048251597882638620964796517719675698443512794459488757671) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 101 = 29 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_221_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_221_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 58,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (222 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (222 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_222 :
    recurrence5B1A3.coeff 222 =
      -((((1552 * 10 ^ 70 +
        8557354242219947629874973674511936322378626938767140336255212084187980) * 10 ^ 70 +
        2576872519109749265604728723995683075241660302467585647249213458567121) * 10 ^ 70 +
        6928044234584701112585027839091526431272019570262852774960250178697471) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 101 = 28 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_222_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_222_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 59,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (223 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (223 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_223 :
    recurrence5B1A3.coeff 223 =
      ((((611 * 10 ^ 70 +
        3480169978689023373046416890263292502835060961606302546397466425093874) * 10 ^ 70 +
        7535383884168204448372781245257190985860283943410707027052101871238733) * 10 ^ 70 +
        6981987294849212285823587456722252623445955773531893425078419550468075) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 101 = 27 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_223_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_223_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 60,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (224 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (224 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_224 :
    recurrence5B1A3.coeff 224 =
      -((((262 * 10 ^ 70 +
        0256561621415979361047330410342763940777236062191268625737410289660808) * 10 ^ 70 +
        9602210117554102800432482878388422727218848495856269870584494314165853) * 10 ^ 70 +
        0047454167096911174689107599741478838885189417684682380413714601118591) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 101 = 26 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_224_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_224_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 61,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (225 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (225 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_225 :
    recurrence5B1A3.coeff 225 =
      ((((116 * 10 ^ 70 +
        5129716151385273179220081614999270447961421794704310372398640625348765) * 10 ^ 70 +
        3698189057899938547064252660827236146033671097872574584791781657283725) * 10 ^ 70 +
        5575884424035952352620229693143869179796365817633933528962053878730902) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 101 = 25 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_225_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_225_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 62,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (226 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (226 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_226 :
    recurrence5B1A3.coeff 226 =
      -((((51 * 10 ^ 70 +
        0923954443775438820476598297355664784214491101104886318808999868743177) * 10 ^ 70 +
        7209873000629790736399632852120565017463841333305255096008744578010210) * 10 ^ 70 +
        2542693524696463434403968248147910303614540099579767912079917402867923) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 101 = 24 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_226_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_226_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 63,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (227 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (227 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_227 :
    recurrence5B1A3.coeff 227 =
      ((((21 * 10 ^ 70 +
        3880916150814198567586987364572496961431850885499482367059568038487036) * 10 ^ 70 +
        9154381398972914337455624875033487509074147064144387549109419211610506) * 10 ^ 70 +
        5358693351895151198000620307940039659076802453669248816929145894418151) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 228 = 63 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 23 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_227_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_227_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 64,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (228 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (228 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_228 :
    recurrence5B1A3.coeff 228 =
      -((((8 * 10 ^ 70 +
        4061536160283592427177415873922911931755860521843181676371789027654666) * 10 ^ 70 +
        6401737175640957882236609888596626462405464306549948923911281743642165) * 10 ^ 70 +
        8602275986093369092627749666519643874589626879589680781228605310791776) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 229 = 64 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 22 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_228_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_228_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 65,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (229 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (229 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_229 :
    recurrence5B1A3.coeff 229 =
      ((((3 * 10 ^ 70 +
        0763881109877504823943549245346599066981631102282016092944574744997005) * 10 ^ 70 +
        5021397477710226741358232203302878787668543404670070378581792787871051) * 10 ^ 70 +
        9162915799584579724324205442528699576495700600028670399769694060329441) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 230 = 65 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 21 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_229_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_229_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 66,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (230 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (230 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_230 :
    recurrence5B1A3.coeff 230 =
      -((((1 * 10 ^ 70 +
        0426469233724267973650248229204817656494317684298414165278099141254526) * 10 ^ 70 +
        3183327058893288339133218411657616316658807968640278009020473659427804) * 10 ^ 70 +
        4365294609060355419227084985394374070490641865205450799972871992816884) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 231 = 66 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 20 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_230_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_230_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 67,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (231 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (231 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_231 :
    recurrence5B1A3.coeff 231 =
      (((3251844503781042287943583140459955720839225600755400582089327429289963 * 10 ^ 70 +
        1937980981785545954360552385926835863730211558079110699875526077520839) * 10 ^ 70 +
        4151570230489482099767855954367279107633794722770518255073464256089287) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 232 = 67 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 19 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_231_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_231_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 68,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (232 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (232 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_232 :
    recurrence5B1A3.coeff 232 =
      -(((923040751412546974342642955460150684495817313057679631329600991291227 * 10 ^ 70 +
        5833719114913825788218489458394660840200958932493304509025690040701977) * 10 ^ 70 +
        2652259407864002904143891821440069125534395847485450350334783323857197) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 233 = 68 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 18 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_232_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_232_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 69,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (233 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (233 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_233 :
    recurrence5B1A3.coeff 233 =
      (((232989721236876376503676837485093108360721051507667739339023237101933 * 10 ^ 70 +
        3724148369671614706554411483088365386645106313330367293544102689353070) * 10 ^ 70 +
        6007698197649876553430914818205263115723418181020535374362011126691258) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 234 = 69 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 17 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_233_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_233_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 70,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (234 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (234 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_234 :
    recurrence5B1A3.coeff 234 =
      -(((49310114580512913318516730391498355201595932347078299150901401591898 * 10 ^ 70 +
        5919154669117887751281921697687180725328560999881949911123341293373871) * 10 ^ 70 +
        4731145015356504169548461427634113917610216427375567813301987364953905) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 235 = 70 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 16 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_234_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_234_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 71,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (235 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (235 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_235 :
    recurrence5B1A3.coeff 235 =
      (((7018237985084526268570713850161856309491701638916566661920603249633 * 10 ^ 70 +
        0070654227464787426857827761679532481299095354892251007105539685781739) * 10 ^ 70 +
        0277200561018344332797549524683157861246455256477740494244602498476005) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 236 = 71 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 15 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_235_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_235_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 72,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (236 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (236 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_236 :
    recurrence5B1A3.coeff 236 =
      (((489614818401720676169121317839849405701209857805474344789130721253 * 10 ^ 70 +
        8184749042557964466212967600000891739101973108763628858963949935737409) * 10 ^ 70 +
        3780926495793422174592573329093147807369324058934668279925403815001018) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 237 = 72 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 14 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_236_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_236_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 73,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (237 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 88,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (237 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_237 :
    recurrence5B1A3.coeff 237 =
      -(((950903621692018595437334231641734223245750407472586205293641883362 * 10 ^ 70 +
        6313083469670326395296319108361928223583952110184019450871268521441489) * 10 ^ 70 +
        5573478702846059991433669522965415145438490143397182384225162640639928) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 238 = 73 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 13 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_237_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_237_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 74,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (238 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 89,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (238 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_238 :
    recurrence5B1A3.coeff 238 =
      (((525715659494047063481696746511244550334356314951122179464252116949 * 10 ^ 70 +
        6105334328912167074118907019808740130283230484587543927622105602696778) * 10 ^ 70 +
        4615761842989487465193924291094705780273250997549607531604494100174625) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 239 = 74 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 12 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_238_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_238_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (239 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 90,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (239 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_239 :
    recurrence5B1A3.coeff 239 =
      -(((229282645424757351963784283268312003106416672022318999725291167708 * 10 ^ 70 +
        9955494200651637152711949084733732268315471972204143103019935647126137) * 10 ^ 70 +
        8376738382838011987989399791268324685428798822605095291295189478968366) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 240 = 75 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 11 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_239_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_239_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (240 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 91,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (240 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_240 :
    recurrence5B1A3.coeff 240 =
      (((90127677547455537796580514874498453838767271880054562658357399722 * 10 ^ 70 +
        9253874603493813084642547123284153159139022445170667461918330021373115) * 10 ^ 70 +
        6339616597134254385384742191007476054228138564301445968919358943049603) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 241 = 76 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 10 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_240_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_240_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (241 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 92,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (241 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_241 :
    recurrence5B1A3.coeff 241 =
      -(((33173473854275275089690699159822270983269855765991711815594204283 * 10 ^ 70 +
        6946182271357785143039444478625275792018443269899010124578199839593839) * 10 ^ 70 +
        6133895729674018730502849511080524979749798145583071401417295700378770) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 242 = 77 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 9 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_241_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_241_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (242 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 93,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (242 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_242 :
    recurrence5B1A3.coeff 242 =
      (((11466826372692799700755837295663083394133959045819233208296848170 * 10 ^ 70 +
        1995015958645885299475080622380170103476929885474562788692068036323930) * 10 ^ 70 +
        4081531957591936825760260134361007617817342621564685266712167111553341) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 243 = 78 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 8 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_242_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_242_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (243 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 94,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (243 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_243 :
    recurrence5B1A3.coeff 243 =
      -(((3645113703147113321394905243093900478117525207907628236445325946 * 10 ^ 70 +
        2048166783976689743498372047902494971282362841593393076233480712487541) * 10 ^ 70 +
        6329619831798832547236894046219587618536399518578639181645266007894821) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 244 = 79 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 7 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_243_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_243_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (244 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 95,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (244 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_244 :
    recurrence5B1A3.coeff 244 =
      (((1010240319841801871861621035749438380421221668122351530522432818 * 10 ^ 70 +
        8378387762761993490163766463420708247266284487754328878429764196854670) * 10 ^ 70 +
        2682336553320304638793487728616134666465628284163163219244631479188888) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 245 = 80 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 6 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_244_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_244_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (245 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 96,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (245 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_245 :
    recurrence5B1A3.coeff 245 =
      -(((208959655280479353996173629970585109686075290653894987859230658 * 10 ^ 70 +
        0511308859606580179144802520643969945843801432509756640982865682273552) * 10 ^ 70 +
        3603595836206238877786304918895592852513634275532019806103281773081202) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 246 = 81 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 5 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_245_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_245_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (246 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 97,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (246 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_246 :
    recurrence5B1A3.coeff 246 =
      (((6302348766471834381199600983900926704164586084485254398759090 * 10 ^ 70 +
        1776363309636702671648056442721581798355122848818532669595790860958381) * 10 ^ 70 +
        9548211710917565863636775269363799371214974569546824684917464713321277) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 247 = 82 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 4 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_246_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_246_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (247 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 98,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (247 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_247 :
    recurrence5B1A3.coeff 247 =
      (((24988081459147572477704718330338381322052952727468766238355952 * 10 ^ 70 +
        9188661199405780237303888373505976119169426566830629392671010605875562) * 10 ^ 70 +
        3644007278302418583113294546550267956716984710334304156901498397935892) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 248 = 83 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 3 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_247_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_247_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (248 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 99,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (248 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_248 :
    recurrence5B1A3.coeff 248 =
      -(((18652565855021311832565117627247790656941819116770945439699642 * 10 ^ 70 +
        6957995390988853114698168756686718061559717169019215326608558472072772) * 10 ^ 70 +
        8809597053795625482399260850468075674528071658821636863219273877263885) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 249 = 84 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 2 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_248_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_248_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (249 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 100,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (249 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_249 :
    recurrence5B1A3.coeff 249 =
      (((9787882877166086042803163413686281492011554005093507034525303 * 10 ^ 70 +
        9131598193056849923165331054620019065573984421292190224619501652196062) * 10 ^ 70 +
        9164531577998027320021144195178293534952733764629772763341324106372335) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 250 = 85 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 1 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_249_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_249_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (250 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 101,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (250 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_250 :
    recurrence5B1A3.coeff 250 =
      -(((4396224080611218279190953374315844860314459971755934074354241 * 10 ^ 70 +
        1570132643944625066515912884928376082221212877186731832094040589511385) * 10 ^ 70 +
        6386868378060280243624763481200694545271160327547991995085480711092053) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 251 = 86 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_250_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_250_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (251 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 102,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (251 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_251 :
    recurrence5B1A3.coeff 251 =
      (((1796872365988712913361594128185947804275644092099863039340322 * 10 ^ 70 +
        1674064231966056268837555397618887549751242279047544534331107341062260) * 10 ^ 70 +
        3333229719555363967324903479686299655390011090174796140328906200908407) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 252 = 87 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 31 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_251_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_251_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (252 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 103,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (252 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_252 :
    recurrence5B1A3.coeff 252 =
      -(((686785680737208259588380231048787337002041443338010506073198 * 10 ^ 70 +
        3105047114815716842115335351643342724364478750828995896931482847074319) * 10 ^ 70 +
        8610916875720089436376254435030967267277499557357191594990476134264945) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 253 = 88 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 30 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_252_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_252_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (253 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 104,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (253 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_253 :
    recurrence5B1A3.coeff 253 =
      (((248619770863465526384534297640206343602867012686060172413715 * 10 ^ 70 +
        9368067480808235899875048595349541433127956041067775987009276251654245) * 10 ^ 70 +
        6484705719693195284110796571135988823642093419057589312628036915764550) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 254 = 89 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 29 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_253_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_253_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (254 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 105,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (254 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_254 :
    recurrence5B1A3.coeff 254 =
      -(((85654133995425191919049075860460654518078679416729451031426 * 10 ^ 70 +
        5428088628495058556598659311112459775222271901468137728861358991043626) * 10 ^ 70 +
        1053205744686272190745369989374270852559823618543309579553759644147045) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 255 = 90 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 28 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_254_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_254_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (255 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 106,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (255 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_255 :
    recurrence5B1A3.coeff 255 =
      (((28105257502745943342400847112543300014456703233581558542467 * 10 ^ 70 +
        9123208334465934586551634420049506620889392841617394410489418289115570) * 10 ^ 70 +
        0085870111179113421363398550641151215873576604063982265706936013170753) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 256 = 91 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 27 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_255_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_255_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (256 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 107,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (256 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_256 :
    recurrence5B1A3.coeff 256 =
      -(((8784803782284297966793976967043370702708333301215332154426 * 10 ^ 70 +
        1617463971556573117641978507162303434702924733727772327044726422295097) * 10 ^ 70 +
        8062011017482514394075841979942209041733357556280831630116307997671142) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 257 = 92 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 26 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_256_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_256_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (257 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 108,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (257 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_257 :
    recurrence5B1A3.coeff 257 =
      (((2622549227548208764684738597070899531207457026016751164909 * 10 ^ 70 +
        1962058750279721193524488162519735674368337634742413422004751781455795) * 10 ^ 70 +
        2428158698089018258749388184428557832507564620420551255322304139864684) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 258 = 93 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 25 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_257_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_257_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (258 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 109,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (258 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_258 :
    recurrence5B1A3.coeff 258 =
      -(((752789863039568591776032006247531582071257123341134639654 * 10 ^ 70 +
        8566584500194606915165186464423977931000355997245142585832598067664759) * 10 ^ 70 +
        9447511638393500630418335628430781529208087442018605293771121569826039) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 259 = 94 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 24 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_258_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (259 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 110,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (259 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_259 :
    recurrence5B1A3.coeff 259 =
      (((209695049450279403120231047875219031723001199379027412215 * 10 ^ 70 +
        2977329129811734702422680487562545719557706583754753089939735217699340) * 10 ^ 70 +
        4970870464735266477482311044356932264216510663158500501711214168534149) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 260 = 95 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 23 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_259_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 96,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (260 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 111,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (260 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_260 :
    recurrence5B1A3.coeff 260 =
      -(((56980031439122655163269634911747546607529584512773458876 * 10 ^ 70 +
        5711449771695118323860205884662086895418997321540733864015336847965491) * 10 ^ 70 +
        8847842019086255901354490146659311383273241006608494501236106085851049) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 261 = 96 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 22 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_260_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 97,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (261 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 112,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (261 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_261 :
    recurrence5B1A3.coeff 261 =
      (((14962250971449136005810656541096266701603961041658521044 * 10 ^ 70 +
        1570029946936408813627824691683467068248464504779756179308578160157247) * 10 ^ 70 +
        5782334683456796067669614320949410539125169005831843525255969099268075) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 262 = 97 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 21 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_261_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 98,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (262 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 113,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (262 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_262 :
    recurrence5B1A3.coeff 262 =
      -(((3666949657715607900748033124219921040963603538529346476 * 10 ^ 70 +
        1921763646364603891230907549427350085120249097521586256932112697588517) * 10 ^ 70 +
        7330919651085843680473564947319885775006542967582115874458708528084943) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 263 = 98 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 20 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_262_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (263 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 114,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (263 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_263 :
    recurrence5B1A3.coeff 263 =
      (((776158142179262978525418330327028409396544395172929782 * 10 ^ 70 +
        2184380724006963934498731747138601315257288234621459065135948370515295) * 10 ^ 70 +
        2343136160504162068788390026854937877725519287428614939610313499570159) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 264 = 99 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 19 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_263_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (264 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 115,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (264 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_264 :
    recurrence5B1A3.coeff 264 =
      -(((113942802637748792721812962758256529210816930076386302 * 10 ^ 70 +
        6977226363310218691006818216670028659181344083585272906764011170510417) * 10 ^ 70 +
        3387936651896918523062321439835382751597550088973368103253430594240898) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 265 = 100 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 18 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_264_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (265 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 116,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (265 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_265 :
    recurrence5B1A3.coeff 265 =
      -(((3779385106731543662677591497146079448556787981746563 * 10 ^ 70 +
        8841725451619111620978226523523508613516010237585494822809700104652146) * 10 ^ 70 +
        9811363609811993563600500624185116322964149602636942981457540358100249) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 266 = 101 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 17 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_265_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (266 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 117,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (266 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_266 :
    recurrence5B1A3.coeff 266 =
      (((11125669438942822075913624119863805583701827355514186 * 10 ^ 70 +
        4073218751605446931516597679504099388271060042141570717321693816988453) * 10 ^ 70 +
        3450352808797243873845117283554665499978206016213014256547696767759964) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 267 = 102 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 16 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_266_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (267 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 118,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (267 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_267 :
    recurrence5B1A3.coeff 267 =
      -(((5308183387112132258165918602485522534303594800346540 * 10 ^ 70 +
        8306719330035716980218144930494375576536862244415161956200490365245604) * 10 ^ 70 +
        4685484171530338964673089688120588697597592711436642430444363233683238) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 268 = 103 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 15 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_267_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (268 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 119,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (268 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_268 :
    recurrence5B1A3.coeff 268 =
      (((1779720437340663989105845447660270622839867522789036 * 10 ^ 70 +
        5443556688384962482136467351343574108038525776139492263907507198035183) * 10 ^ 70 +
        9446946710989200216854366754878672419465904142097048234745324277581388) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 269 = 104 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 14 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_268_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 105,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (269 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 120,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (269 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_269 :
    recurrence5B1A3.coeff 269 =
      -(((477608412082865821567382613135624880351582135474384 * 10 ^ 70 +
        0298652756299786546080731305308848105893774326657486738831121366543599) * 10 ^ 70 +
        8947390601285130467422022548437498716332195268807974375174209313606856) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 270 = 105 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 13 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_269_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 106,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (270 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 121,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (270 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_270 :
    recurrence5B1A3.coeff 270 =
      (((104535147508478177595575186191842693036209370970312 * 10 ^ 70 +
        1437648287868424324412100942423303337674175232699519442519162173452726) * 10 ^ 70 +
        8085617760795728635143070298347418865562522950195789434958469175911793) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 271 = 106 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 12 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_270_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 107,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (271 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 122,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (271 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_271 :
    recurrence5B1A3.coeff 271 =
      -(((17848309834517362711885843980296130355908021716516 * 10 ^ 70 +
        2099491440799990786852922408372906752421953753347117629589199760076011) * 10 ^ 70 +
        2622525814923420186509109398431773608806290624841840621935880326854613) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 272 = 107 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 11 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_271_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 108,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (272 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 123,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (272 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_272 :
    recurrence5B1A3.coeff 272 =
      (((1916974133109029056796063624141372888218272403570 * 10 ^ 70 +
        4728846838734473307510973989112620616413294380948983722263459787437536) * 10 ^ 70 +
        0393914578729398850773241809001557361816265119024665808192717362487700) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 273 = 108 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 10 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_272_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 109,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (273 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 124,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (273 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_273 :
    recurrence5B1A3.coeff 273 =
      (((84763215901586602806071944165662650349182824650 * 10 ^ 70 +
        6235205481709839389014955949363228981129668104273915960927612449276761) * 10 ^ 70 +
        5891334280803680672620440258705060174506361333414609848527016805988359) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 274 = 109 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 9 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_273_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 110,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (274 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 125,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (274 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_274 :
    recurrence5B1A3.coeff 274 =
      -(((109896183989224809397330889211773567591928558166 * 10 ^ 70 +
        6930108157039595693491351630803748771858761651881806925949335857906532) * 10 ^ 70 +
        1379645620360540802283247668550894959214986976856238439518707547005740) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 275 = 110 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 8 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_274_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 111,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (275 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 126,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (275 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_275 :
    recurrence5B1A3.coeff 275 =
      (((34290419424637060702301959246401603463021975775 * 10 ^ 70 +
        7022222513895178166107389466037537911387173979286318501461208435293636) * 10 ^ 70 +
        6671805484285387415738803681767533427437472774107574633246050782980121) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 276 = 111 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 7 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_275_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 112,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (276 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 127,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (276 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_276 :
    recurrence5B1A3.coeff 276 =
      -(((7340156291606014285980642098696442742152959125 * 10 ^ 70 +
        4066422400240118944777197482482604115584108032226540606354206303193941) * 10 ^ 70 +
        8949759604050024101691817079345318176438337443423510570447398113773642) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 277 = 112 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 6 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_276_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 113,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (277 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 128,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (277 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_277 :
    recurrence5B1A3.coeff 277 =
      (((1197226914672921332829147419046622444155060166 * 10 ^ 70 +
        5795183430908128141438645965791801825792726877263860951435689399776315) * 10 ^ 70 +
        9181816607356230294283467082823538537908046457552499887781008220375339) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 278 = 113 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 5 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_277_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 114,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (278 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 129,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (278 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_278 :
    recurrence5B1A3.coeff 278 =
      -(((146960024950009233814831152882057112522302729 * 10 ^ 70 +
        4095126289908869583613890439636590553370093772617787250054982833948611) * 10 ^ 70 +
        6241847080381727975877565826113379623546570395407086042010639572760029) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 279 = 114 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 4 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_278_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 115,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (279 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 130,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (279 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_279 :
    recurrence5B1A3.coeff 279 =
      (((11752250781501416886315757953530086692782529 * 10 ^ 70 +
        3956715524688269072293386068840775112572291030015889497221596352119231) * 10 ^ 70 +
        8885202431421630352786202767868590363633049982210052126806943645051951) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 280 = 115 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 3 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_279_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 116,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (280 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 131,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (280 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_280 :
    recurrence5B1A3.coeff 280 =
      -(((91023144751545565069002976788696585112925 * 10 ^ 70 +
        0503453540696676288686040059804116224948270950872849439850582144268479) * 10 ^ 70 +
        4755290000703346772800135567508575946266096375217033715881073918494196) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 281 = 116 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 2 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_280_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 117,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (281 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 132,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (281 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_281 :
    recurrence5B1A3.coeff 281 =
      -(((151511515096175992175654008867533885743534 * 10 ^ 70 +
        4724409286237010461959172196661289591623371316904581580674771161181091) * 10 ^ 70 +
        5242190740846091763921059978182659744103459811160750511496749332877977) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 282 = 117 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 1 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_281_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 118,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (282 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 133,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (282 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_282 :
    recurrence5B1A3.coeff 282 =
      (((28322529162538561339605513948916308644870 * 10 ^ 70 +
        9906118074037943778958592057876017945103280929153104683638153421644591) * 10 ^ 70 +
        9398407176887822976845217547181911928998481733012784314405071680538395) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 283 = 118 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_282_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 119,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (283 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 134,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (283 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_283 :
    recurrence5B1A3.coeff 283 =
      -(((3005783595527446424334224393852130847987 * 10 ^ 70 +
        0830584679449162054156245236785196790898066794829521398645062353648893) * 10 ^ 70 +
        5666185919506075027370246745415976912646889705664040765512035998265703) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 284 = 119 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 31 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_283_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 120,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (284 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 135,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (284 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_284 :
    recurrence5B1A3.coeff 284 =
      (((189709517692873298673756037290286697679 * 10 ^ 70 +
        7131799231192801935969905292057508824784475599182254883470154598296867) * 10 ^ 70 +
        1863017736172288420058543050022312151000856574465855497797249912400437) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 285 = 120 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 30 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_284_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 121,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (285 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 136,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (285 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_285 :
    recurrence5B1A3.coeff 285 =
      -(((3181042501523791694361784089755705919 * 10 ^ 70 +
        8669632713429795022100632993713873655355107130719366014800345506653668) * 10 ^ 70 +
        2150357353658087015688673745525386170640912424413163047839213253845927) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 286 = 121 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 29 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_285_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 122,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (286 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 137,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (286 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_286 :
    recurrence5B1A3.coeff 286 =
      -(((670328115877349173312697496792508977 * 10 ^ 70 +
        5531512241572101107017387368283076505853293094746100651761226463589212) * 10 ^ 70 +
        7845325135011856946168229844868549027455393667283631593422011947129375) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 287 = 122 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 28 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_286_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 123,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (287 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 138,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (287 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_287 :
    recurrence5B1A3.coeff 287 =
      (((71590980495994071922533935956020078 * 10 ^ 70 +
        0682860149257635287281162587700479956056630031051582490660014466640293) * 10 ^ 70 +
        7139827419348769213465926870275675878681432070940106359804009774405624) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 288 = 123 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 27 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_287_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 124,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (288 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 139,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (288 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_288 :
    recurrence5B1A3.coeff 288 =
      -(((3027533570916477639929408606902976 * 10 ^ 70 +
        7197788563485756982978707820735240830337962987805578641033979926130723) * 10 ^ 70 +
        6413474243365004720616424783195743615249736998298566684436426176708467) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 289 = 124 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 26 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_288_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 125,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (289 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 140,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (289 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_289 :
    recurrence5B1A3.coeff 289 =
      (((12294322996422638500307801529064 * 10 ^ 70 +
        5150456713503566848702383371035939592544946533038854751832635040413015) * 10 ^ 70 +
        3245069895940509785374364059600486705854726880917264948421471929196122) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 290 = 125 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 25 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_289_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 126,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (290 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 141,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (290 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_290 :
    recurrence5B1A3.coeff 290 =
      (((3609668825832431999660680359487 * 10 ^ 70 +
        9500696446761927088624180513542684013424847768501816854052489506214027) * 10 ^ 70 +
        3124129521824637174481791907080321097507449048964417025047410360740450) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 291 = 126 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 24 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_290_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 127,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (291 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 142,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (291 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_291 :
    recurrence5B1A3.coeff 291 =
      -(((82014777860819581889282478452 * 10 ^ 70 +
        9838450430020613385680942113269226265417956619410412084138825921681241) * 10 ^ 70 +
        9627438926358239669037709561214746837000071628257305700732458900851174) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 292 = 127 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 23 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_291_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 128,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (292 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 143,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (292 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_292 :
    recurrence5B1A3.coeff 292 =
      -(((1165483899498461129077160968 * 10 ^ 70 +
        6830007306698892250537132398349875182812014594840795977049374339344096) * 10 ^ 70 +
        8886498281097903259477108790366818865588390770120276462266139341372270) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 293 = 128 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 22 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_292_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 129,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (293 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 144,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (293 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_293 :
    recurrence5B1A3.coeff 293 =
      (((15884072902681779161632498 * 10 ^ 70 +
        0108470172076277866197695016784597222609610317290382164798869677856614) * 10 ^ 70 +
        4651755114106010905081544525669227809289939052761380421390623448725181) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 294 = 129 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 21 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_293_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 130,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (294 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 145,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (294 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_294 :
    recurrence5B1A3.coeff 294 =
      (((200650488224102264202256 * 10 ^ 70 +
        1338001855996970271426370917232917068813499379233110349575564103834575) * 10 ^ 70 +
        4408694611227243423181640503801512723500181086332461489761595978331156) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 295 = 130 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 20 +
      145 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_294_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 131,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (295 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 146,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (295 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_295 :
    recurrence5B1A3.coeff 295 =
      -(((76609740528066331346 * 10 ^ 70 +
        6159409570030755241190174036136442616664236350986206683760812403279859) * 10 ^ 70 +
        0180148591796618403047183040560803694093249129123217790318150232742592) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 296 = 131 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 19 +
      146 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_295_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 132,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (296 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 147,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (296 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_296 :
    recurrence5B1A3.coeff 296 =
      -(((6476795519958517763 * 10 ^ 70 +
        4843240478644887619790389666960421607036521182494022195247395174640356) * 10 ^ 70 +
        9126938465417477457188640783752833232491115417120867582452736567623067) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 297 = 132 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 18 +
      147 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_296_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 133,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (297 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 148,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (297 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_297 :
    recurrence5B1A3.coeff 297 =
      -(((12351241368713734 * 10 ^ 70 +
        2451950017655881776714177853121003447480790647411004520950703276309109) * 10 ^ 70 +
        7782384148955723409326134986072161607360732262268638302091129729666807) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 298 = 133 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 17 +
      148 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_297_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 134,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (298 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 149,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (298 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_298 :
    recurrence5B1A3.coeff 298 =
      (((57915773350426 * 10 ^ 70 +
        9944193120989440904409484793789081760511792238046829347170657559204139) * 10 ^ 70 +
        3569802927378436589976780916681454506836358807379262528309522147174938) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 299 = 134 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 16 +
      149 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_298_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 135,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (299 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 150,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (299 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_299 :
    recurrence5B1A3.coeff 299 =
      (((134724563757 * 10 ^ 70 +
        2229277478365174689052227125927571510565093550925090748127642056848639) * 10 ^ 70 +
        3542805442627489341024143574540235695432825945441546238744369036020253) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 300 = 135 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 15 +
      150 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_299_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 136,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (300 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 151,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (300 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_300 :
    recurrence5B1A3.coeff 300 =
      -(((255714932 * 10 ^ 70 +
        8148266865856813201377244413530297796139641552277041268188581680001955) * 10 ^ 70 +
        3710919517794335327150804626282475752019543032501824603279218843887460) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 301 = 136 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 14 +
      151 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_300_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 137,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (301 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 152,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (301 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_301 :
    recurrence5B1A3.coeff 301 =
      -(((454113 * 10 ^ 70 +
        8623732074313474460771831203176534712132431293013772408701477794210962) * 10 ^ 70 +
        6156594973932941437495027654678561554352651027821703053706166186848775) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 302 = 137 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 13 +
      152 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_301_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 138,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (302 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 153,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (302 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_302 :
    recurrence5B1A3.coeff 302 =
      (((614 * 10 ^ 70 +
        8087206497370945598287405693839182008022659631500952351850032883635476) * 10 ^ 70 +
        1567110350725248293194109058502648991500277492438515900530629191467536) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 303 = 138 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 12 +
      153 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_302_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 139,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (303 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 154,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (303 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_303 :
    recurrence5B1A3.coeff 303 =
      ((2733547569229180702934422067726889200566060827284897081026568213384736 * 10 ^ 70 +
        1189157103770620711057012235176138187322936295166111372291820878922584) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 304 = 139 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 11 +
      154 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_303_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 140,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (304 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 155,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (304 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_304 :
    recurrence5B1A3.coeff 304 =
      -((2644492595546306892211628890844981106951915344699932289702745134134 * 10 ^ 70 +
        6809610095172233234748914778831986421141456324176420888352272279385068) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 305 = 140 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 10 +
      155 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_304_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 141,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (305 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 156,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (305 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_305 :
    recurrence5B1A3.coeff 305 =
      ((7666190964088414772699155564738811924719889583017140011278415 * 10 ^ 70 +
        9824838106834250852128276016413390484840644769093337325788589406513543) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 306 = 141 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 9 +
      156 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_305_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 142,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (306 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 157,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (306 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_306 :
    recurrence5B1A3.coeff 306 =
      ((57347160067525136976372805740083259450918883536138618109236 * 10 ^ 70 +
        9038921800502905353606449662866629199371351376427436935943618082672000) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 307 = 142 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 8 +
      157 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_306_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 143,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (307 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 158,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (307 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_307 :
    recurrence5B1A3.coeff 307 =
      -((1155231654492364480394069936679724423954047942491747136 * 10 ^ 70 +
        2513897210411721683768322908134836534686327983560691503720693086878460) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 308 = 143 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 7 +
      158 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_307_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 144,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (308 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 159,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (308 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_308 :
    recurrence5B1A3.coeff 308 =
      -((34398705033879381097982418830509391086909523573532 * 10 ^ 70 +
        0748233718868526224641492539107056795552034307690829696956241359055801) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 309 = 144 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 6 +
      159 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_308_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 145,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (309 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 160,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (309 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_309 :
    recurrence5B1A3.coeff 309 =
      ((215015399502368050795659987526356979941521567 * 10 ^ 70 +
        0824288257470526709720318319317340098626360046981476500260988775227353) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 310 = 145 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 5 +
      160 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_309_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 146,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (310 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 161,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (310 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_310 :
    recurrence5B1A3.coeff 310 =
      ((206967408019792044053139986914498949691 * 10 ^ 70 +
        7426372909971919893693141609140417938600952774111519574727313424586321) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 311 = 146 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 4 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_310_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 147,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (311 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 162,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (311 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_311 :
    recurrence5B1A3.coeff 311 =
      -((215841817127047757417089589817969 * 10 ^ 70 +
        6534773939361196324091995033050905916047127618514255444111813367865914) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 312 = 147 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 3 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_311_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 148,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (312 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 163,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (312 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_312 :
    recurrence5B1A3.coeff 312 =
      -((2983748584247354453598460 * 10 ^ 70 +
        7044222996973995346056732224350565306593598213239436843820748594142133) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 313 = 148 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 2 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_312_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 149,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (313 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 164,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (313 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_313 :
    recurrence5B1A3.coeff 313 =
      ((248126233697070452 * 10 ^ 70 +
        7087092616189355522336704302718340073582840467932303636082363886151610) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 314 = 149 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 1 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_313_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
