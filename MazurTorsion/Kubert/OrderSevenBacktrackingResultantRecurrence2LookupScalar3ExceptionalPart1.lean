/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupExceptionalProduct
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupC3
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar3Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2ExceptionalProduct_coeff_0
  recurrence2ExceptionalProduct_coeff_1
  recurrence2ExceptionalProduct_coeff_2
  recurrence2ExceptionalProduct_coeff_3
  recurrence2ExceptionalProduct_coeff_4
  recurrence2ExceptionalProduct_coeff_5
  recurrence2ExceptionalProduct_coeff_6
  recurrence2ExceptionalProduct_coeff_7
  recurrence2ExceptionalProduct_coeff_8
  recurrence2ExceptionalProduct_coeff_9
  recurrence2ExceptionalProduct_coeff_10
  recurrence2ExceptionalProduct_coeff_11
  recurrence2ExceptionalProduct_coeff_12
  recurrence2ExceptionalProduct_coeff_13
  recurrence2ExceptionalProduct_coeff_14
  recurrence2ExceptionalProduct_coeff_15
  recurrence2ExceptionalProduct_coeff_16
  recurrence2ExceptionalProduct_coeff_17
  recurrence2ExceptionalProduct_coeff_18
  recurrence2ExceptionalProduct_coeff_19
  recurrence2ExceptionalProduct_coeff_20
  recurrence2ExceptionalProduct_coeff_21
  recurrence2ExceptionalProduct_coeff_22
  recurrence2ExceptionalProduct_coeff_23
  recurrence2ExceptionalProduct_coeff_24
  recurrence2ExceptionalProduct_coeff_25
  recurrence2ExceptionalProduct_coeff_26
  recurrence2ExceptionalProduct_coeff_27
  recurrence2ExceptionalProduct_coeff_28
  recurrence2ExceptionalProduct_coeff_29
  recurrence2ExceptionalProduct_coeff_30
  recurrence2ExceptionalProduct_coeff_31
  recurrence2ExceptionalProduct_coeff_32
  recurrence2ExceptionalProduct_coeff_33
  recurrence2ExceptionalProduct_coeff_34
  recurrence2ExceptionalProduct_coeff_35
  recurrence2ExceptionalProduct_coeff_36
  recurrence2ExceptionalProduct_coeff_37
  recurrence2ExceptionalProduct_coeff_38
  recurrence2ExceptionalProduct_coeff_39
  recurrence2ExceptionalProduct_coeff_40
  recurrence2ExceptionalProduct_coeff_41
  recurrence2ExceptionalProduct_coeff_42
  recurrence2ExceptionalProduct_coeff_43
  recurrence2ExceptionalProduct_coeff_44
  recurrence2ExceptionalProduct_coeff_45
  recurrence2ExceptionalProduct_coeff_46
  recurrence2ExceptionalProduct_coeff_47
  recurrence2ExceptionalProduct_coeff_48
  recurrence2ExceptionalProduct_coeff_49
  recurrence2ExceptionalProduct_coeff_50
  recurrence2ExceptionalProduct_coeff_51
  recurrence2ExceptionalProduct_coeff_52
  recurrence2ExceptionalProduct_coeff_53
  recurrence2ExceptionalProduct_coeff_54
  recurrence2ExceptionalProduct_coeff_55
  recurrence2ExceptionalProduct_coeff_56
  recurrence2ExceptionalProduct_coeff_57
  recurrence2ExceptionalProduct_coeff_58
  recurrence2ExceptionalProduct_coeff_59
  recurrence2ExceptionalProduct_coeff_60
  recurrence2ExceptionalProduct_coeff_61
  recurrence2ExceptionalProduct_coeff_62
  recurrence2ExceptionalProduct_coeff_63
  recurrence2ExceptionalProduct_coeff_64
  recurrence2ExceptionalProduct_coeff_65
  recurrence2ExceptionalProduct_coeff_66
  recurrence2ExceptionalProduct_coeff_67
  recurrence2ExceptionalProduct_coeff_68
  recurrence2ExceptionalProduct_coeff_69
  recurrence2ExceptionalProduct_coeff_70
  recurrence2ExceptionalProduct_coeff_71
  recurrence2ExceptionalProduct_coeff_72
  recurrence2ExceptionalProduct_coeff_73
  recurrence2ExceptionalProduct_coeff_74
  recurrence2ExceptionalProduct_coeff_75
  recurrence2ExceptionalProduct_coeff_76
  recurrence2ExceptionalProduct_coeff_77
  recurrence2ExceptionalProduct_coeff_78
  recurrence2ExceptionalProduct_coeff_79
  recurrence2ExceptionalProduct_coeff_80
  recurrence2ExceptionalProduct_coeff_81
  recurrence2ExceptionalProduct_coeff_82
  recurrence2ExceptionalProduct_coeff_83
  recurrence2ExceptionalProduct_coeff_84
  recurrence2ExceptionalProduct_coeff_85
  recurrence2ExceptionalProduct_coeff_86
  recurrence2ExceptionalProduct_coeff_87
  recurrence2ExceptionalProduct_coeff_88
  recurrence2ExceptionalProduct_coeff_89
  recurrence2ExceptionalProduct_coeff_90
  recurrence2ExceptionalProduct_coeff_91
  recurrence2ExceptionalProduct_coeff_92
  recurrence2ExceptionalProduct_coeff_93
  recurrence2ExceptionalProduct_coeff_94
  recurrence2ExceptionalProduct_coeff_95
  recurrence2ExceptionalProduct_coeff_96
  recurrence2ExceptionalProduct_coeff_97
  recurrence2ExceptionalProduct_coeff_98
  recurrence2ExceptionalProduct_coeff_99
  recurrence2ExceptionalProduct_coeff_100
  recurrence2ExceptionalProduct_coeff_101
  recurrence2ExceptionalProduct_coeff_102
  recurrence2ExceptionalProduct_coeff_103
  recurrence2ExceptionalProduct_coeff_104
  recurrence2ExceptionalProduct_coeff_105
  recurrence2ExceptionalProduct_coeff_106
  recurrence2ExceptionalProduct_coeff_107
  recurrence2ExceptionalProduct_coeff_108
  recurrence2ExceptionalProduct_coeff_109
  recurrence2ExceptionalProduct_coeff_110
  recurrence2ExceptionalProduct_coeff_111
  recurrence2ExceptionalProduct_coeff_112
  recurrence2ExceptionalProduct_coeff_113
  recurrence2ExceptionalProduct_coeff_114
  recurrence2ExceptionalProduct_coeff_115
  recurrence2ExceptionalProduct_coeff_116
  recurrence2ExceptionalProduct_coeff_117
  recurrence2ExceptionalProduct_coeff_118
  recurrence2ExceptionalProduct_coeff_119
  recurrence2ExceptionalProduct_coeff_120
  recurrence2ExceptionalProduct_coeff_121
  recurrence2ExceptionalProduct_coeff_122
  recurrence2ExceptionalProduct_coeff_123
  recurrence2ExceptionalProduct_coeff_124
  recurrence2ExceptionalProduct_coeff_125
  recurrence2ExceptionalProduct_coeff_126
  recurrence2ExceptionalProduct_coeff_127
  recurrence2ExceptionalProduct_coeff_128
  recurrence2ExceptionalProduct_coeff_129
  recurrence2ExceptionalProduct_coeff_130
  recurrence2ExceptionalProduct_coeff_131
  recurrence2ExceptionalProduct_coeff_132
  recurrence2ExceptionalProduct_coeff_133
  recurrence2ExceptionalProduct_coeff_134
  recurrence2ExceptionalProduct_coeff_135
  recurrence2ExceptionalProduct_coeff_136
  recurrence2ExceptionalProduct_coeff_137
  recurrence2ExceptionalProduct_coeff_138
  recurrence2ExceptionalProduct_coeff_139
  recurrence2ExceptionalProduct_coeff_140
  recurrence2ExceptionalProduct_coeff_141
  recurrence2ExceptionalProduct_coeff_142
  recurrence2ExceptionalProduct_coeff_143
  recurrence2ExceptionalProduct_coeff_144
  recurrence2ExceptionalProduct_coeff_145
  recurrence2ExceptionalProduct_coeff_146
  recurrence2ExceptionalProduct_coeff_147
  recurrence2ExceptionalProduct_coeff_148
  recurrence2ExceptionalProduct_coeff_149
  recurrence2ExceptionalProduct_coeff_150
  recurrence2ExceptionalProduct_coeff_151
  recurrence2ExceptionalProduct_coeff_152
  recurrence2ExceptionalProduct_coeff_153
  recurrence2ExceptionalProduct_coeff_154
  recurrence2ExceptionalProduct_coeff_155
  recurrence2ExceptionalProduct_coeff_156
  recurrence2ExceptionalProduct_coeff_157
  recurrence2ExceptionalProduct_coeff_158
  recurrence2ExceptionalProduct_coeff_159
  recurrence2ExceptionalProduct_coeff_160
  recurrence2ExceptionalProduct_coeff_161
  recurrence2ExceptionalProduct_coeff_162
  recurrence2ExceptionalProduct_coeff_163
  recurrence2ExceptionalProduct_coeff_164
  recurrence2ExceptionalProduct_coeff_165
  recurrence2ExceptionalProduct_coeff_166
  recurrence2ExceptionalProduct_coeff_167
  recurrence2ExceptionalProduct_coeff_168
  recurrence2ExceptionalProduct_coeff_169
  recurrence2ExceptionalProduct_coeff_170
  recurrence2ExceptionalProduct_coeff_171
  recurrence2ExceptionalProduct_coeff_172
  recurrence2ExceptionalProduct_coeff_173
  recurrence2ExceptionalProduct_coeff_174
  recurrence2ExceptionalProduct_coeff_175
  recurrence2ExceptionalProduct_coeff_176
  recurrence2ExceptionalProduct_coeff_177
  recurrence2ExceptionalProduct_coeff_178
  recurrence2ExceptionalProduct_coeff_179
  recurrence2ExceptionalProduct_coeff_180
  recurrence2ExceptionalProduct_coeff_181
  recurrence2ExceptionalProduct_coeff_182
  recurrence2ExceptionalProduct_coeff_183
  recurrence2ExceptionalProduct_coeff_184
  recurrence2ExceptionalProduct_coeff_185
  recurrence2ExceptionalProduct_coeff_186
  recurrence2ExceptionalProduct_coeff_187
  recurrence2ExceptionalProduct_coeff_188
  recurrence2ExceptionalProduct_coeff_189
  recurrence2ExceptionalProduct_coeff_190
  recurrence2ExceptionalProduct_coeff_191
  recurrence2ExceptionalProduct_coeff_192
  recurrence2ExceptionalProduct_coeff_193
  recurrence2C3_coeff_0
  recurrence2C3_coeff_1
  recurrence2C3_coeff_2
  recurrence2C3_coeff_3
  recurrence2C3_coeff_4
  recurrence2C3_coeff_5
  recurrence2C3_coeff_6
  recurrence2C3_coeff_7
  recurrence2C3_coeff_8
  recurrence2C3_coeff_9
  recurrence2C3_coeff_10
  recurrence2C3_coeff_11
  recurrence2C3_coeff_12
  recurrence2C3_coeff_13
  recurrence2C3_coeff_14
  recurrence2C3_coeff_15
  recurrence2C3_coeff_16
  recurrence2C3_coeff_17
  recurrence2C3_coeff_18
  recurrence2C3_coeff_19
  recurrence2C3_coeff_20
  recurrence2C3_coeff_21
  recurrence2C3_coeff_22
  recurrence2C3_coeff_23
  recurrence2C3_coeff_24
  recurrence2C3_coeff_25
  recurrence2C3_coeff_26
  recurrence2C3_coeff_27
  recurrence2C3_coeff_28
  recurrence2C3_coeff_29
  recurrence2C3_coeff_30
  recurrence2C3_coeff_31
  recurrence2C3_coeff_32
  recurrence2C3_coeff_33
  recurrence2C3_coeff_34
  recurrence2C3_coeff_35
  recurrence2C3_coeff_36
  recurrence2C3_coeff_37
  recurrence2C3_coeff_38
  recurrence2C3_coeff_39
  recurrence2C3_coeff_40
  recurrence2C3_coeff_41
  recurrence2C3_coeff_42
  recurrence2C3_coeff_43
  recurrence2C3_coeff_44
  recurrence2C3_coeff_45
  recurrence2C3_coeff_46
  recurrence2C3_coeff_47
  recurrence2C3_coeff_48
  recurrence2C3_coeff_49
  recurrence2C3_coeff_50
  recurrence2C3_coeff_51
  recurrence2C3_coeff_52
  recurrence2C3_coeff_53
  recurrence2C3_coeff_54
  recurrence2C3_coeff_55
  recurrence2C3_coeff_56
  recurrence2C3_coeff_57
  recurrence2C3_coeff_58
  recurrence2C3_coeff_59
  recurrence2C3_coeff_60
  recurrence2C3_coeff_61
  recurrence2C3_coeff_62
  recurrence2C3_coeff_63
  recurrence2C3_coeff_64
  recurrence2C3_coeff_65
  recurrence2C3_coeff_66
  recurrence2C3_coeff_67
  recurrence2C3_coeff_68
  recurrence2C3_coeff_69
  recurrence2C3_coeff_70
  recurrence2C3_coeff_71
  recurrence2C3_coeff_72
  recurrence2C3_coeff_73
  recurrence2C3_coeff_74
  recurrence2C3_coeff_75
  recurrence2C3_coeff_76
  recurrence2C3_coeff_77
  recurrence2C3_coeff_78
  recurrence2C3_coeff_79
  recurrence2C3_coeff_80
  recurrence2C3_coeff_81
  recurrence2C3_coeff_82
  recurrence2C3_coeff_83
  recurrence2C3_coeff_84
  recurrence2C3_coeff_85
  recurrence2C3_coeff_86
  recurrence2C3_coeff_87
  recurrence2C3_coeff_88
  recurrence2C3_coeff_89
  recurrence2C3_coeff_90
  recurrence2C3_coeff_91
  recurrence2C3_coeff_92
  recurrence2C3_coeff_93
  recurrence2C3_coeff_94
  recurrence2C3_coeff_95
  recurrence2C3_coeff_96
  recurrence2C3_coeff_97
  recurrence2C3_coeff_98
  recurrence2C3_coeff_99
  recurrence2C3_coeff_100
  recurrence2C3_coeff_101
  recurrence2C3_coeff_102
  recurrence2C3_coeff_103
  recurrence2C3_coeff_104
  recurrence2C3_coeff_105
  recurrence2C3_coeff_106
  recurrence2C3_coeff_107
  recurrence2C3_coeff_108
  recurrence2C3_coeff_109
  recurrence2C3_coeff_110
  recurrence2C3_coeff_111
  recurrence2C3_coeff_112
  recurrence2C3_coeff_113
  recurrence2C3_coeff_114
  recurrence2C3_coeff_115
  recurrence2C3_coeff_116
  recurrence2C3_coeff_117
  recurrence2C3_coeff_118
  recurrence2C3_coeff_119
  recurrence2C3_coeff_120
  recurrence2C3_coeff_121
  recurrence2C3_coeff_122
  recurrence2C3_coeff_123
  recurrence2C3_coeff_124
  recurrence2C3_coeff_125
  recurrence2C3_coeff_126
  recurrence2C3_coeff_127
  recurrence2C3_coeff_128
  recurrence2C3_coeff_129
  recurrence2C3_coeff_130
  recurrence2C3_coeff_131
  recurrence2C3_coeff_132
  recurrence2C3_coeff_133
  recurrence2C3_coeff_134
  recurrence2C3_coeff_135
  recurrence2C3_coeff_136
  recurrence2C3_coeff_137
  recurrence2C3_coeff_138
  recurrence2C3_coeff_139
  recurrence2C3_coeff_140
  recurrence2C3_coeff_141
  recurrence2C3_coeff_142
  recurrence2C3_coeff_143
  recurrence2C3_coeff_144
  recurrence2C3_coeff_145
  recurrence2C3_coeff_146
  recurrence2C3_coeff_147
  recurrence2C3_coeff_148
  recurrence2C3_coeff_149
  recurrence2C3_coeff_150
  recurrence2C3_coeff_151
  recurrence2C3_coeff_152
  recurrence2C3_coeff_153
  recurrence2C3_coeff_154
  recurrence2C3_coeff_155
  recurrence2C3_coeff_156
  recurrence2C3_coeff_157
  recurrence2C3_coeff_158
  recurrence2C3_coeff_159
  recurrence2C3_coeff_160
  recurrence2C3_coeff_161
  recurrence2C3_coeff_162
  recurrence2C3_coeff_163
  recurrence2C3_coeff_164
  recurrence2C3_coeff_165
  recurrence2C3_coeff_166
  recurrence2C3_coeff_167
  recurrence2C3_coeff_168
  recurrence2C3_coeff_169
  recurrence2C3_coeff_170
  recurrence2C3_coeff_171
  recurrence2C3_coeff_172
  recurrence2C3_coeff_173
  recurrence2C3_coeff_174
  recurrence2C3_coeff_175
  recurrence2C3_coeff_176
  recurrence2C3_coeff_177
  recurrence2C3_coeff_178
  recurrence2C3_coeff_179
  recurrence2C3_coeff_180
  recurrence2C3_coeff_181
  recurrence2C3_coeff_182

private theorem recurrence2Scalar3Exceptional_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (231 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (231 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_231 :
    recurrence2Scalar3Exceptional.coeff 231 =
      (((12957158075663960194200655702434773035177256410387717411022 * 10 ^ 70 +
        9655032796159165635654766297170458392788150935988452571311541631915701) * 10 ^ 70 +
        2077655828254162430764270247922285350974599881089465685090124091384085) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 232 = 49 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 17 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_231_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_231_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (232 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (232 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_232 :
    recurrence2Scalar3Exceptional.coeff 232 =
      (((2224019137007319522126086341697327339042235107858205999736 * 10 ^ 70 +
        0586746372493717633022541609600136316225811005366102459891736366527847) * 10 ^ 70 +
        7469299044689618145485223902460947610185133016491097730680420472165299) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 233 = 50 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 16 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_232_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_232_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (233 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (233 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_233 :
    recurrence2Scalar3Exceptional.coeff 233 =
      -(((9356815670274335496880946201465161693926779918718387413495 * 10 ^ 70 +
        9765191792840187349735496804199809263599633791617992848376996131832868) * 10 ^ 70 +
        7427844212445746890947444703546136030294244145451018535368465464181749) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 234 = 51 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 15 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_233_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_233_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (234 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (234 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_234 :
    recurrence2Scalar3Exceptional.coeff 234 =
      (((11105152343626154668045888774375321300956600145965534893986 * 10 ^ 70 +
        2250818916725213695628128427486505227771011797582140903556110616180129) * 10 ^ 70 +
        9290150480274792020267839016193356034464011094533215390451307660279276) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 235 = 52 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 14 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_234_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_234_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (235 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (235 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_235 :
    recurrence2Scalar3Exceptional.coeff 235 =
      -(((9860173595990458143173182506872034452476137251360596358241 * 10 ^ 70 +
        0188841321093815122605597055409418336979163916072609011048014260261227) * 10 ^ 70 +
        9675589986441578905830508204059937434902105800394811196310216027615491) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 236 = 53 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 13 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_235_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_235_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (236 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (236 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_236 :
    recurrence2Scalar3Exceptional.coeff 236 =
      (((7410966626328815223509944617131441708448292492839557825405 * 10 ^ 70 +
        7040494963897801866620539416552227447095831880466125138056809195517200) * 10 ^ 70 +
        3574285541250808888587354553367972740244451193354698490224702325990100) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 237 = 54 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 12 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_236_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_236_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (237 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (237 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_237 :
    recurrence2Scalar3Exceptional.coeff 237 =
      -(((4878326235987292619531224938942710714070893764497675898663 * 10 ^ 70 +
        7090042421035727935908720771314538001239479611175468193342196722925417) * 10 ^ 70 +
        7775650309650609594788201999155011080190746432945506105245869561705373) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 238 = 55 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 11 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_237_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_237_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (238 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (238 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_238 :
    recurrence2Scalar3Exceptional.coeff 238 =
      (((2816238961166758967911856083502705730543824223892373065097 * 10 ^ 70 +
        4088058255452708664896806041171209164103600245690212958141882660265038) * 10 ^ 70 +
        4774884009985873896417861684612239299719510228139492417588583834228058) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 239 = 56 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 10 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_238_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_238_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (239 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (239 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_239 :
    recurrence2Scalar3Exceptional.coeff 239 =
      -(((1384736432242239428054842961091859187483851124289373532333 * 10 ^ 70 +
        9995219006846068915691811084302865748823339062727460932420015932784035) * 10 ^ 70 +
        7422780779353285188424150619493131028357776479165793169378362265502958) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 240 = 57 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 9 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_239_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_239_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (240 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (240 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_240 :
    recurrence2Scalar3Exceptional.coeff 240 =
      (((522381708162302907850482450629921399932114228093917011016 * 10 ^ 70 +
        6572738653441974839879978861153066923322199361227854136311233651540778) * 10 ^ 70 +
        6538793663035042241722485710099465172604962276178322322265879985424031) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 241 = 58 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 8 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_240_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_240_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (241 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (241 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_241 :
    recurrence2Scalar3Exceptional.coeff 241 =
      -(((79295232486217077589317082407215067683073883710740732854 * 10 ^ 70 +
        2436741099732080718685593285713485544840561197482231428654241982726441) * 10 ^ 70 +
        0353976610064903818598285788095217796977213346793520962443956140764339) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 242 = 59 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 7 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_241_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_241_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (242 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (242 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_242 :
    recurrence2Scalar3Exceptional.coeff 242 =
      -(((100289344383751128713864617161448814315573168443310813465 * 10 ^ 70 +
        4304815453609453516655995565600580822064215843331468018710342864840807) * 10 ^ 70 +
        5922954222489996351060547602861054011279211277594589230687921081108507) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 243 = 60 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 6 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_242_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_242_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (243 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (243 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_243 :
    recurrence2Scalar3Exceptional.coeff 243 =
      (((139171282482993687715507559274493978595627818616944638940 * 10 ^ 70 +
        9874812294118946048617418029431427901023825783692633545194526605344396) * 10 ^ 70 +
        8140308493189715193492366102171908332898009617425225829555307397948161) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 244 = 61 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 5 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_243_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_243_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (244 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (244 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_244 :
    recurrence2Scalar3Exceptional.coeff 244 =
      -(((117900048618193484901483453358293991809591480209934271774 * 10 ^ 70 +
        2699688023177504178160525092030739429657822905456219584349275810586901) * 10 ^ 70 +
        3556267283031590338154421304714362264046627457304356066026789629420845) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 245 = 62 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 4 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_244_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_244_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (245 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (245 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_245 :
    recurrence2Scalar3Exceptional.coeff 245 =
      (((80982394731794698860555308145301562760685944398100540962 * 10 ^ 70 +
        8157892269386699396849412547297378346372792753933482525895568534585158) * 10 ^ 70 +
        4939115561310296072344458194992436297860881576056119723242633762721960) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 246 = 63 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 3 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_245_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_245_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (246 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (246 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_246 :
    recurrence2Scalar3Exceptional.coeff 246 =
      -(((48233804573770303145734944093112835354328753191664593277 * 10 ^ 70 +
        4410559790119041216932526715406538375906668615559081785010055730022638) * 10 ^ 70 +
        1469065141314339345450891657195056003799769266464013180672253541188244) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 247 = 64 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 2 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_246_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_246_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (247 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (247 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_247 :
    recurrence2Scalar3Exceptional.coeff 247 =
      (((25405861019127677275238671800048889634368734347941046043 * 10 ^ 70 +
        8542973252132911220663606268423032099660332128221984959455739497396186) * 10 ^ 70 +
        5108556031718656131782626007536855541828769899813570979700111633849359) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 248 = 65 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 1 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_247_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_247_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (248 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (248 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_248 :
    recurrence2Scalar3Exceptional.coeff 248 =
      -(((11793042466377658825544099950917618001796188684318108329 * 10 ^ 70 +
        7582001559468195832033263325682549718082408422125742863074706611619696) * 10 ^ 70 +
        2744782306454290698241620425453400866619130199789593337406739672162065) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 249 = 66 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_248_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_248_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (249 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (249 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_249 :
    recurrence2Scalar3Exceptional.coeff 249 =
      (((4682331102484454763868582250290960337968564619937820245 * 10 ^ 70 +
        1167561196790125069050177233956792136657560630457051237777025769261167) * 10 ^ 70 +
        1492086758212303970419727224723110795209029384255760572923792336453742) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 250 = 67 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 31 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_249_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_249_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (250 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (250 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_250 :
    recurrence2Scalar3Exceptional.coeff 250 =
      -(((1442480701673880241765693588652322439534419879521200960 * 10 ^ 70 +
        0537889954576602993128111781957572000030261237740681178039739929848126) * 10 ^ 70 +
        5670969460707095572314772254918662919605033939999277664807352416619746) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 251 = 68 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 30 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_250_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_250_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (251 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (251 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_251 :
    recurrence2Scalar3Exceptional.coeff 251 =
      (((201287531205853770649235532353396230888976004895467392 * 10 ^ 70 +
        9048871306540834329347061156573503581711341932789848160362316015884495) * 10 ^ 70 +
        3779049286635973577598564534464908852014480642397441072187100487467491) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 252 = 69 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 29 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_251_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_251_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (252 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (252 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_252 :
    recurrence2Scalar3Exceptional.coeff 252 =
      (((149978173085476751588289920302515041538963788334592357 * 10 ^ 70 +
        0996875448061073096184530191630647820842339309982172600123971770975864) * 10 ^ 70 +
        2398754446758113380514128179360185592525548620855510737686976751792167) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 253 = 70 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 28 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_252_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_252_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (253 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (253 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_253 :
    recurrence2Scalar3Exceptional.coeff 253 =
      -(((175001788676926896678071638684588452977185516001718886 * 10 ^ 70 +
        3545406785781641460682957526243772679794918349073417364528547523652014) * 10 ^ 70 +
        7095612946404690741978300797455941835406110496518249533589230507567131) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 254 = 71 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 27 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_253_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_253_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (254 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (254 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_254 :
    recurrence2Scalar3Exceptional.coeff 254 =
      (((117755291597731359401463120722276571251344861881567581 * 10 ^ 70 +
        6338473832289138737561577667976643371562638828660341866958756103731559) * 10 ^ 70 +
        2121764129984372474811028855554007110220402904271372205686227183328099) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 255 = 72 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 26 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_254_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_254_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (255 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (255 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_255 :
    recurrence2Scalar3Exceptional.coeff 255 =
      -(((62889207455403801776776645308637491741399850682126519 * 10 ^ 70 +
        9806999769913343586224013817253981672524859239174318131792126133568920) * 10 ^ 70 +
        6762271174156720806288613789788429660319697367700850684688893309587854) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 256 = 73 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 25 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_255_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_255_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (256 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (256 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_256 :
    recurrence2Scalar3Exceptional.coeff 256 =
      (((28459680651774683243112492699947470410780718952025208 * 10 ^ 70 +
        2320727832169359459251356693625858979137081063135412877224027354415126) * 10 ^ 70 +
        8868926619848487547134354240487004319496491472816895027889432250787249) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 257 = 74 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 24 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_256_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_256_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (257 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (257 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_257 :
    recurrence2Scalar3Exceptional.coeff 257 =
      -(((10981355822420863484832390005185582540112696111148474 * 10 ^ 70 +
        2688509447714166877431956959878169314499527318124684133151281914323384) * 10 ^ 70 +
        7927670189583712008755033469896951921555387246229229005266217741708680) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 258 = 75 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 23 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_257_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_257_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (258 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (258 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_258 :
    recurrence2Scalar3Exceptional.coeff 258 =
      (((3467655162679000879683393917486636709355607315793633 * 10 ^ 70 +
        9062487264663038974960226505975044517593166719839081824146107655200838) * 10 ^ 70 +
        1201652053655212643920339767581492920297797120530413661580252412097977) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 259 = 76 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 22 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_258_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (259 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (259 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_259 :
    recurrence2Scalar3Exceptional.coeff 259 =
      -(((753021961240643154775853298816984738277832643698946 * 10 ^ 70 +
        2897830841203948010700417213316562060416675453185269327872472521146648) * 10 ^ 70 +
        8566654981905775203547749387610599210171111294088290905083357048583527) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 260 = 77 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 21 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_259_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (260 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (260 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_260 :
    recurrence2Scalar3Exceptional.coeff 260 =
      -(((13680124187573761531654813352501682809021210237681 * 10 ^ 70 +
        4752631357836435802955852138602027782994889993995727854744109742869400) * 10 ^ 70 +
        0605996386075663686827864976116847588487018712283148742524798277610504) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 261 = 78 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 20 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_260_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (261 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (261 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_261 :
    recurrence2Scalar3Exceptional.coeff 261 =
      (((130905704340158568957134224920511778054773199919525 * 10 ^ 70 +
        8730060586301257124552333488394311695384394277561190047936440862578240) * 10 ^ 70 +
        0802519577640067896326014217717002140821295082929539210465573911481028) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 262 = 79 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 19 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_261_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (262 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (262 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_262 :
    recurrence2Scalar3Exceptional.coeff 262 =
      -(((92030443608458536342994974377209726549420893154155 * 10 ^ 70 +
        9208445344927608664060677690423594389360640981173805863287358164671974) * 10 ^ 70 +
        6724121996936426927050653698463457196407847415024664247891973423093613) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 263 = 80 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 18 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_262_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (263 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (263 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_263 :
    recurrence2Scalar3Exceptional.coeff 263 =
      (((45427548110480653247833547401705963309787422988877 * 10 ^ 70 +
        3926118190338373163206279105435205676317513435989647055722825154940343) * 10 ^ 70 +
        2667991416444846425981780377809379319513467617897739679541918598773458) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 264 = 81 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 17 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_263_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (264 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (264 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_264 :
    recurrence2Scalar3Exceptional.coeff 264 =
      -(((18288676639309147657558967271986523619781007840973 * 10 ^ 70 +
        9609976933850125541705463579406388892042510971585824292034562759112770) * 10 ^ 70 +
        4621099211061975354852105415603197558921457308702620138148101042550522) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 265 = 82 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 16 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_264_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (265 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (265 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_265 :
    recurrence2Scalar3Exceptional.coeff 265 =
      (((6223882649547690311918378706681390230968962328174 * 10 ^ 70 +
        4806774624869061416262765954378961709030337539251232401180556654842809) * 10 ^ 70 +
        1918324852065327189457344073607600159473857991101860946394901096903321) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 266 = 83 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 15 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_265_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (266 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (266 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_266 :
    recurrence2Scalar3Exceptional.coeff 266 =
      -(((1789819969922247298185363440242654929756032779241 * 10 ^ 70 +
        0803705517028096071971730292220675176730085565617402874099242259908208) * 10 ^ 70 +
        3735601165254000141231825919771292706155340040599479914576107120798657) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 267 = 84 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 14 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_266_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (267 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (267 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_267 :
    recurrence2Scalar3Exceptional.coeff 267 =
      (((425498575780203037390851819410938976517934059135 * 10 ^ 70 +
        3534246052733328127413824746862600674778709536130394304007574102548711) * 10 ^ 70 +
        1084902440268325193964048229922210507099700973611108927186021250106680) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 268 = 85 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 13 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_267_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (268 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (268 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_268 :
    recurrence2Scalar3Exceptional.coeff 268 =
      -(((80938280138793195116189490832060853757136367630 * 10 ^ 70 +
        0209365456726378577921431510389466742908660079579082790211141053263331) * 10 ^ 70 +
        7424987567748008045993806304907058085667113201047716617245646730753306) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 269 = 86 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 12 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_268_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (269 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (269 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_269 :
    recurrence2Scalar3Exceptional.coeff 269 =
      (((12726458008400655442344340980933395539358485597 * 10 ^ 70 +
        3180314695696913682712392937193436691934188858598269450429429698341685) * 10 ^ 70 +
        6443563506996995435598941708610670618160699444902540545076838963301266) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 270 = 87 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 11 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_269_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (270 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (270 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_270 :
    recurrence2Scalar3Exceptional.coeff 270 =
      -(((2281889332628833386365871253442439942372019606 * 10 ^ 70 +
        0894615302880964158409220875061736327168984917488086859836400263341492) * 10 ^ 70 +
        5441788046941236874835641266506859965826992430658717365805100405366152) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 271 = 88 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 10 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_270_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (271 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (271 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_271 :
    recurrence2Scalar3Exceptional.coeff 271 =
      (((205464026878101052462435063116122542438888684 * 10 ^ 70 +
        0092641547209720423266810049970912891714444960275979320067969335970407) * 10 ^ 70 +
        2657205206330663379127590295429789863576614710293696602605127062532514) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 272 = 89 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 9 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_271_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (272 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (272 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_272 :
    recurrence2Scalar3Exceptional.coeff 272 =
      (((765778595882456889491225259340095600716281804 * 10 ^ 70 +
        9463457987544010565834453307722423805575095968527122463385541772775151) * 10 ^ 70 +
        7982531435802646166643607295079778308723131626386402032398164423926724) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 273 = 90 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 8 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_272_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (273 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (273 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_273 :
    recurrence2Scalar3Exceptional.coeff 273 =
      -(((1037313226967227244787424967394511622822380443 * 10 ^ 70 +
        3190726538362232238693488403853871137286469099167600670904042744059202) * 10 ^ 70 +
        6744762694984238383135571409860705665127939353155273499255320175773307) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 274 = 91 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 7 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_273_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (274 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (274 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_274 :
    recurrence2Scalar3Exceptional.coeff 274 =
      (((829624270278740067483357722349554127294010531 * 10 ^ 70 +
        4013191346762903010005652508724089814074169191371851099347842030762059) * 10 ^ 70 +
        9101800068790262537996523714441944924187260272074726393865891515047541) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 275 = 92 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 6 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_274_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (275 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (275 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_275 :
    recurrence2Scalar3Exceptional.coeff 275 =
      -(((488771774650832135479752482782326191137504936 * 10 ^ 70 +
        9294912450384944184547358375002138520898440183448189041657979727428478) * 10 ^ 70 +
        0259424685121931027881204763791559627102611968619931296255537933646348) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 276 = 93 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 5 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_275_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (276 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (276 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_276 :
    recurrence2Scalar3Exceptional.coeff 276 =
      (((221007978730176244356985708403843128497532455 * 10 ^ 70 +
        3922605904288521932133693936008129974022717139866864194062706338830908) * 10 ^ 70 +
        2412616517513103311817128200534217497819534029247549752004503884415947) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 277 = 94 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 4 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_276_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (277 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (277 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_277 :
    recurrence2Scalar3Exceptional.coeff 277 =
      -(((71812207135649821231708465867188579102377734 * 10 ^ 70 +
        6329208613496939192346374480085930653088072779681383876353138994250486) * 10 ^ 70 +
        9897796404706476418834976334340311829373730615955263866340346550612432) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 278 = 95 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 3 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_277_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (278 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (278 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_278 :
    recurrence2Scalar3Exceptional.coeff 278 =
      (((9942033438979607047569627113926039729096920 * 10 ^ 70 +
        1717209383262077677277789618582994076193096575714162313503141712840627) * 10 ^ 70 +
        3405934530724143885149701279042804168369503599301051409487363409745138) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 279 = 96 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 2 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_278_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (279 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (279 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_279 :
    recurrence2Scalar3Exceptional.coeff 279 =
      (((6922814771216284549987438387483208803299525 * 10 ^ 70 +
        3405061619646909019814625406347511961194155019724987140296682356541793) * 10 ^ 70 +
        3148171140358526744820355107685640341349709885779663253333721100065144) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 280 = 97 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 1 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_279_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (280 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (280 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_280 :
    recurrence2Scalar3Exceptional.coeff 280 =
      -(((7125616222550667644531956783990812739285531 * 10 ^ 70 +
        4688377822185049039984732682321358269927594053661154484139187576729023) * 10 ^ 70 +
        3821380064996593647602832011091057689222400039566818096144518708232515) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 281 = 98 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_280_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (281 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (281 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_281 :
    recurrence2Scalar3Exceptional.coeff 281 =
      (((3921165518767038915491479337616569328567981 * 10 ^ 70 +
        6330391657436555182251475409237581025299304086809053878070849103561074) * 10 ^ 70 +
        1884617611607607971583183792552114592594918256972941430085386560854794) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 282 = 99 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 31 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_281_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (282 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (282 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_282 :
    recurrence2Scalar3Exceptional.coeff 282 =
      -(((1524069763043601208447732237665755822368673 * 10 ^ 70 +
        6996157579695054395182672688805779559640711939266008502072929444937518) * 10 ^ 70 +
        7405192527954735069128932282080870425683259898451955854975228933647204) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 283 = 100 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 30 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_282_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (283 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (283 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_283 :
    recurrence2Scalar3Exceptional.coeff 283 =
      (((389153140583808574683453532661067536261312 * 10 ^ 70 +
        6052248643289635479976707494644445320043502324479256510485238511132797) * 10 ^ 70 +
        4380685984971439587775146871920931637757527318583719178636470144997510) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 284 = 101 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 29 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_283_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (284 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (284 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_284 :
    recurrence2Scalar3Exceptional.coeff 284 =
      -(((14330568683557188646310729530922269189635 * 10 ^ 70 +
        3377842285798941712754332238935333999274502921413884943928992498249785) * 10 ^ 70 +
        1702164162399598718377418250943443054518743766518893773383038288426859) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 285 = 102 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 28 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_284_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (285 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (285 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_285 :
    recurrence2Scalar3Exceptional.coeff 285 =
      -(((51385667559515234753821031435947196549660 * 10 ^ 70 +
        5891030632412504913709687739951582772709132656630930155691965193905765) * 10 ^ 70 +
        4555990904292845733478115327523221005943728163129527867823330532930221) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 286 = 103 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 27 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_285_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (286 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (286 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_286 :
    recurrence2Scalar3Exceptional.coeff 286 =
      (((35138617151578258091198490639167405531019 * 10 ^ 70 +
        7617354331997456402995847712985407743224103647410962956855120550222833) * 10 ^ 70 +
        6892323299913238513558423117926243289104738948518167146216367473210562) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 287 = 104 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 26 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_286_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (287 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (287 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_287 :
    recurrence2Scalar3Exceptional.coeff 287 =
      -(((14638312302715397192058998077447063626192 * 10 ^ 70 +
        4059532059740825907586964862370283250502706968103477698604622074365901) * 10 ^ 70 +
        5983297164628719853443954181732114203726336912094451173950679471893835) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 288 = 105 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 25 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_287_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (288 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (288 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_288 :
    recurrence2Scalar3Exceptional.coeff 288 =
      (((4129256506699342075029172631448412391283 * 10 ^ 70 +
        3140217455583524895730501831558550070736161830972436505605970788998127) * 10 ^ 70 +
        9304889061170227623053587699280265123915855145942027184071067818279833) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 289 = 106 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 24 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_288_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (289 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (289 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_289 :
    recurrence2Scalar3Exceptional.coeff 289 =
      -(((552377538546982097357194067603810352492 * 10 ^ 70 +
        9765745195469281976363353854365324414201342117208057269371144489786585) * 10 ^ 70 +
        7843181504283556937616277279806023350710816784305309817733636143991288) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 290 = 107 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 23 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_289_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (290 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (290 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_290 :
    recurrence2Scalar3Exceptional.coeff 290 =
      -(((186189464103484026421319825199632449151 * 10 ^ 70 +
        7920496574139078311027085966836097195789353811288288193065517230430367) * 10 ^ 70 +
        9001540431063093127958356934839097355873226555225512239515643808266835) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 291 = 108 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 22 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_290_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (291 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (291 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_291 :
    recurrence2Scalar3Exceptional.coeff 291 =
      (((165555835247616358499489248537370853720 * 10 ^ 70 +
        5817343160730388194297050752225670051818158473337035428927425502447020) * 10 ^ 70 +
        0782107622556683115109979606925145489893476286660456104824629720754862) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 292 = 109 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 21 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_291_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (292 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (292 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_292 :
    recurrence2Scalar3Exceptional.coeff 292 =
      -(((67622959534130947005903008044208317656 * 10 ^ 70 +
        2207033172792078322873303161881692231720954698420523420786971318798394) * 10 ^ 70 +
        0565887188907540338654593689809779873577049942183881154191741399023655) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 293 = 110 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 20 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_292_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (293 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (293 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_293 :
    recurrence2Scalar3Exceptional.coeff 293 =
      (((17624950041122965933668921664281184924 * 10 ^ 70 +
        0019240791013985302018178249395824452952494242290466323291610343689126) * 10 ^ 70 +
        8278799041433705540327067192628880216118931992132077916164232372914273) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 294 = 111 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 19 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_293_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (294 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (294 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_294 :
    recurrence2Scalar3Exceptional.coeff 294 =
      -(((2128343119554699645945926974941926143 * 10 ^ 70 +
        0396900154055749620209686282837450197829805819996892720085195662177579) * 10 ^ 70 +
        9821909930580855697817847350257808852913109442065107866737015191399549) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 295 = 112 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 18 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_294_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (295 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (295 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_295 :
    recurrence2Scalar3Exceptional.coeff 295 =
      -(((613337516852119081204956721738957064 * 10 ^ 70 +
        3450669184399919254628789971807204590355100911471904399129445455345908) * 10 ^ 70 +
        8065375900866066315345604894416517850984347589340962235172049929563959) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 296 = 113 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 17 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_295_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (296 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (296 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_296 :
    recurrence2Scalar3Exceptional.coeff 296 =
      (((470222574969730027558924601153272282 * 10 ^ 70 +
        6855258398603586321912800875612501591285470412259960812469243371127756) * 10 ^ 70 +
        5713278346492923871170408181595355135132205764112924363871912619612164) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 297 = 114 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 16 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_296_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (297 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (297 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_297 :
    recurrence2Scalar3Exceptional.coeff 297 =
      -(((158754859395659130822127352993248344 * 10 ^ 70 +
        9666503002201658591755041440409857497452676837606393443050665460760461) * 10 ^ 70 +
        5230435576381910148874089442107773554292132550887711331924653145725291) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 298 = 115 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 15 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_297_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (298 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (298 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_298 :
    recurrence2Scalar3Exceptional.coeff 298 =
      (((31315577765430492339634964709895512 * 10 ^ 70 +
        5305895887242262174363910871568862353317474191942257154149170609826113) * 10 ^ 70 +
        5971908394369747430654120919693740555761283613917222447613564224955932) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 299 = 116 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 14 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_298_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (299 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (299 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_299 :
    recurrence2Scalar3Exceptional.coeff 299 =
      -(((1185903059780953569901756633584901 * 10 ^ 70 +
        2311035943667069335254098287213696746007323598647968792580978742292894) * 10 ^ 70 +
        0727893618076353141400665215435977038152610378601925194640885973219262) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 300 = 117 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 13 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_299_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (300 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (300 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_300 :
    recurrence2Scalar3Exceptional.coeff 300 =
      -(((1719899521203314074502581195242152 * 10 ^ 70 +
        8247232041497803169185226719333414093365442539546180297900456385337281) * 10 ^ 70 +
        6431068998672147467136872174278463030532678302032370610159114002080338) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 301 = 118 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 12 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_300_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (301 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (301 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_301 :
    recurrence2Scalar3Exceptional.coeff 301 =
      (((735968159483126522632950018325020 * 10 ^ 70 +
        2802152539723580275979510791111827327941692842486315723919197625020974) * 10 ^ 70 +
        4359829805983645967125494325550724352219255335495765588994166258658899) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 302 = 119 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 11 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_301_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (302 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (302 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_302 :
    recurrence2Scalar3Exceptional.coeff 302 =
      -(((163041603536041863668420892897848 * 10 ^ 70 +
        8750391088384324459158776596462001669707935170211857900444877895631794) * 10 ^ 70 +
        8015219190794478996970277629605490507139361013392544883502277139054307) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 303 = 120 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 10 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_302_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (303 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (303 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_303 :
    recurrence2Scalar3Exceptional.coeff 303 =
      (((14184689242642976213465136103448 * 10 ^ 70 +
        2655044401629101371544675717749331377823933029794934377649642404370727) * 10 ^ 70 +
        4549148635124437419539300132425442308814900002110507435378306232907487) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 304 = 121 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 9 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_303_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (304 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (304 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_304 :
    recurrence2Scalar3Exceptional.coeff 304 =
      (((4240815240078593535913241483891 * 10 ^ 70 +
        8602570452210476320520687066831231716603477060983501927672993918149863) * 10 ^ 70 +
        3488489965847033183518095239313504184269613063670114960996311172206598) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 305 = 122 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 8 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_304_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (305 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (305 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_305 :
    recurrence2Scalar3Exceptional.coeff 305 =
      -(((2111577665767913287536644415335 * 10 ^ 70 +
        6259910847332565788607490913840794814442454511955875977097335796976617) * 10 ^ 70 +
        9797155314946012278669575609705547261150439691734117903745553736517020) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 306 = 123 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 7 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_305_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (306 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (306 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_306 :
    recurrence2Scalar3Exceptional.coeff 306 =
      (((445098831818119039400159794321 * 10 ^ 70 +
        5342221196331431618330785515068329228040642097477958489755285198327349) * 10 ^ 70 +
        3620559671775593643792344631601327253423914961557788444176854525658253) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 307 = 124 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 6 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_306_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (307 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (307 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_307 :
    recurrence2Scalar3Exceptional.coeff 307 =
      -(((34122751958129011253211351454 * 10 ^ 70 +
        0317697398825117808837412420428882614045746895800205642762462585867851) * 10 ^ 70 +
        3020879275344514031138815647433577264517546094166416910399344896549896) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 308 = 125 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 5 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_307_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (308 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (308 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_308 :
    recurrence2Scalar3Exceptional.coeff 308 =
      -(((9656759258236155650610026104 * 10 ^ 70 +
        9550342196359538609139415559273389294333583513743836586829061157120948) * 10 ^ 70 +
        1313390071485300064040373801723919761866072243699781071110014524631354) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 309 = 126 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 4 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_308_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (309 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (309 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_309 :
    recurrence2Scalar3Exceptional.coeff 309 =
      (((3975307792740728796062104907 * 10 ^ 70 +
        8911055577250854567912517849661110761761117237376926845904453342461201) * 10 ^ 70 +
        9565104480752980642484910444530628090604490499573840892779222876650053) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 310 = 127 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 3 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_309_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (310 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (310 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_310 :
    recurrence2Scalar3Exceptional.coeff 310 =
      -(((645707799401380989676394836 * 10 ^ 70 +
        0331245126783241378487650867251932925236686565848078535449564513388835) * 10 ^ 70 +
        1901590969254104980871113103954885909583851403380782732957131345152687) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 311 = 128 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 2 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_310_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (311 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (311 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_311 :
    recurrence2Scalar3Exceptional.coeff 311 =
      (((14502847665268101387809272 * 10 ^ 70 +
        5501990490342498164323296299942521742615899583016664061640981735004721) * 10 ^ 70 +
        1810307207736641251975325029499616293723051506601782633754942300597605) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 312 = 129 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 1 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_311_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (312 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (312 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_312 :
    recurrence2Scalar3Exceptional.coeff 312 =
      (((18184661988017653898494843 * 10 ^ 70 +
        8613778291820083932596806924329965526437211536504918297664867897639226) * 10 ^ 70 +
        1958163218453368924984922409396098642738317836315494058319433441783838) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 313 = 130 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_312_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (313 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (313 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_313 :
    recurrence2Scalar3Exceptional.coeff 313 =
      -(((4378586020902044179471843 * 10 ^ 70 +
        9490096588277390213824596965455508096808332910919258725213534458842239) * 10 ^ 70 +
        1881940969542920918603797718781696741974211779534301299812843269761747) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 314 = 131 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 31 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_313_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (314 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (314 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_314 :
    recurrence2Scalar3Exceptional.coeff 314 =
      (((362619573673863331335265 * 10 ^ 70 +
        1507165753536465208158680072908473150092304424851868184497981298071994) * 10 ^ 70 +
        9711383654634158251854071515459919326095961092683140858958104967405130) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 315 = 132 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 30 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_314_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (315 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (315 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_315 :
    recurrence2Scalar3Exceptional.coeff 315 =
      (((49290144641088923002317 * 10 ^ 70 +
        4307264165334683868367147405623524549089738291939809016648165011997344) * 10 ^ 70 +
        2270772995009613533691330986927775422556948302481005837676504386548349) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 316 = 133 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 29 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_315_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (316 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (316 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_316 :
    recurrence2Scalar3Exceptional.coeff 316 =
      -(((17972815460320302398830 * 10 ^ 70 +
        7201270876283223463985522936742761021589399493312204103830318999502028) * 10 ^ 70 +
        0490277262220974835911443988535902160055498934682360749413270098185717) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 317 = 134 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 28 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_316_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (317 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (317 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_317 :
    recurrence2Scalar3Exceptional.coeff 317 =
      (((1846192571141687709395 * 10 ^ 70 +
        1628142404251798606078260433917584214221896695745326509686113320965347) * 10 ^ 70 +
        5504274470602472747421182559727232440487058854845645523981821905256466) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 318 = 135 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 27 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_317_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (318 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (318 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_318 :
    recurrence2Scalar3Exceptional.coeff 318 =
      (((105217693871032964878 * 10 ^ 70 +
        4343291077767357578921994351101980298935311728805943554642580494281449) * 10 ^ 70 +
        2579650605745543830129376988477494274631206988464049927833572737200113) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 319 = 136 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 26 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_318_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (319 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (319 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_319 :
    recurrence2Scalar3Exceptional.coeff 319 =
      -(((52514457794853290416 * 10 ^ 70 +
        5690824183415309777551650563533578910992749609701361562124215025429664) * 10 ^ 70 +
        7677866030679165625458504762245581442489869681633870932461470957402999) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 320 = 137 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 25 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_319_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (320 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (320 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_320 :
    recurrence2Scalar3Exceptional.coeff 320 =
      (((4983945515923579229 * 10 ^ 70 +
        0862375241597179048679256610190390142209320228827177370925624002710070) * 10 ^ 70 +
        5191066461964921057440980736841105309476027641000634627277023596954814) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 321 = 138 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 24 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_320_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (321 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (321 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_321 :
    recurrence2Scalar3Exceptional.coeff 321 =
      (((307256225893155883 * 10 ^ 70 +
        4339558456223457008293003331039840957859431612416880795288701792919841) * 10 ^ 70 +
        4525390640605082703863430630371116653361627883034567346393868310261731) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 322 = 139 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 23 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_321_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (322 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (322 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_322 :
    recurrence2Scalar3Exceptional.coeff 322 =
      -(((113881808366572830 * 10 ^ 70 +
        0848762813201843720913207334131739596600313482194118891211751463527242) * 10 ^ 70 +
        6754060209857795452302758799349515878436327235573030261151847263433037) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 323 = 140 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 22 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_322_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (323 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (323 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_323 :
    recurrence2Scalar3Exceptional.coeff 323 =
      (((6783009172846291 * 10 ^ 70 +
        0521927382188234268731617686945411531947630247697344723155338264319742) * 10 ^ 70 +
        7082044862210872841113014936336864339078290235751344947728864963873024) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 324 = 141 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 21 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_323_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (324 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (324 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_324 :
    recurrence2Scalar3Exceptional.coeff 324 =
      (((950493797488273 * 10 ^ 70 +
        1680405628816914502065651633802378815499165154277234461219159785009573) * 10 ^ 70 +
        4818284782856685368733500511536231436051736526045108019901536833249656) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 325 = 142 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 20 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_324_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (325 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (325 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_325 :
    recurrence2Scalar3Exceptional.coeff 325 =
      -(((159553747124672 * 10 ^ 70 +
        7148724192475715856426775679824788019820645523470395442368302027852075) * 10 ^ 70 +
        7834020336149988247225397964913104105148682804693327462867469560890174) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 326 = 143 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 19 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_325_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (326 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (326 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_326 :
    recurrence2Scalar3Exceptional.coeff 326 =
      -(((86134860872 * 10 ^ 70 +
        1339483130024800522459015620311354435507012563578773157231323000103778) * 10 ^ 70 +
        9959357559256514013362679521439080558039890604690018039764965443837350) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 327 = 144 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 18 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_326_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 145,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (327 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (327 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_327 :
    recurrence2Scalar3Exceptional.coeff 327 =
      (((1687765405172 * 10 ^ 70 +
        5866470758904406523602237001817458533165477117702557383714785895166664) * 10 ^ 70 +
        1163150633211544428134261140346556663231218330722698631934513025985028) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 328 = 145 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 17 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_327_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 146,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (328 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (328 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_328 :
    recurrence2Scalar3Exceptional.coeff 328 =
      -(((79957426489 * 10 ^ 70 +
        2636583478019509936644912257291340431109612335454349411054630783103409) * 10 ^ 70 +
        3617118709401598176800721322906115303851293235469250581172180603268526) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 329 = 146 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 16 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_328_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 147,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (329 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (329 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_329 :
    recurrence2Scalar3Exceptional.coeff 329 =
      -(((11811454326 * 10 ^ 70 +
        4457873891767390240807604083779642538869883044450231328768604782932895) * 10 ^ 70 +
        3317009058138894399378952416457986625433897863774985305744478653814935) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 330 = 147 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 15 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_329_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 148,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (330 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (330 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_330 :
    recurrence2Scalar3Exceptional.coeff 330 =
      (((975085711 * 10 ^ 70 +
        2394795276943653692654001118765087564938764393525526095035721195333643) * 10 ^ 70 +
        9979243808698867611047024160143910739148382363099348141156497710074744) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 331 = 148 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 14 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_330_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 149,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (331 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (331 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_331 :
    recurrence2Scalar3Exceptional.coeff 331 =
      (((67644858 * 10 ^ 70 +
        3163081864546963331209946989254349111114006392657307278649747774003544) * 10 ^ 70 +
        6760216104949666079701871229754740943167472899000250390737141804205975) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 332 = 149 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 13 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_331_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 150,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (332 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (332 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_332 :
    recurrence2Scalar3Exceptional.coeff 332 =
      -(((7064388 * 10 ^ 70 +
        5360024405033725036406087625548567429334154600564038263164130927070977) * 10 ^ 70 +
        3875066791003954831804793525881259906275109672501453547537289340876325) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 333 = 150 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 12 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_332_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 151,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (333 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (333 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_333 :
    recurrence2Scalar3Exceptional.coeff 333 =
      -(((402242 * 10 ^ 70 +
        9327336412219542433261022659559125416985014792343469526329647631502876) * 10 ^ 70 +
        6737602674406546623225052612040906739817029279480051766178498150270642) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 334 = 151 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 11 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_333_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 152,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (334 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (334 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_334 :
    recurrence2Scalar3Exceptional.coeff 334 =
      (((34343 * 10 ^ 70 +
        0980348928803532061703556069385295805641469758444913920697881048490045) * 10 ^ 70 +
        7301723371428184219188717541650602811904115041496564334056894310179547) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 335 = 152 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 10 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_334_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 153,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (335 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (335 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_335 :
    recurrence2Scalar3Exceptional.coeff 335 =
      (((2558 * 10 ^ 70 +
        5333609156069619124659147382472567121236660661218392648846612823418517) * 10 ^ 70 +
        9748666710032208250446504259659781753268774893879825414040894979581601) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 336 = 153 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 9 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_335_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 154,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (336 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (336 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_336 :
    recurrence2Scalar3Exceptional.coeff 336 =
      -(((80 * 10 ^ 70 +
        1757258233696569605485324792993035411043520129541714179945099019610221) * 10 ^ 70 +
        4963386628685288419783235883340070813422104460056120298344515837872215) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 337 = 154 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 8 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_336_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 155,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (337 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (337 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_337 :
    recurrence2Scalar3Exceptional.coeff 337 =
      -(((12 * 10 ^ 70 +
        7346499732764452483108839994726661914160653054797039945415870240905574) * 10 ^ 70 +
        5754639562355583445692924972738183135124549134731515529339304761978749) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 338 = 155 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 7 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_337_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 156,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (338 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 145,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (338 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_338 :
    recurrence2Scalar3Exceptional.coeff 338 =
      -((2840189895340002962312746131548153954972940200572156687726696131045608 * 10 ^ 70 +
        6972656973582448965771357006156982975679233914212473854132635300594979) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 339 = 156 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 6 +
      145 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_338_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 157,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (339 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 146,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (339 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_339 :
    recurrence2Scalar3Exceptional.coeff 339 =
      ((240326590842088190744578907375669803312619161600262258499296570402389 * 10 ^ 70 +
        0057565387402109072372214171884906346187894868415192207073033301987310) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 340 = 157 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 5 +
      146 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_339_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 158,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (340 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 147,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (340 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_340 :
    recurrence2Scalar3Exceptional.coeff 340 =
      ((22248407190491508971513859902761638533367316536316684451879218505915 * 10 ^ 70 +
        3843517676138750458632720623692090488978914003643718326785928752311998) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 341 = 158 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 4 +
      147 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_340_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 159,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (341 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 148,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (341 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_341 :
    recurrence2Scalar3Exceptional.coeff 341 =
      ((958593598828548150057401159793470577815469425535528720012714664797 * 10 ^ 70 +
        2171447808323868222610513168726171399559674832823894498389200358644417) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 342 = 159 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 3 +
      148 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_341_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 160,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (342 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 149,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (342 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_342 :
    recurrence2Scalar3Exceptional.coeff 342 =
      ((27198416126871994525131420649331751570751756717507597178600027784 * 10 ^ 70 +
        9531075680260545215723472048706721915379112401714471216764966009144587) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 343 = 160 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 2 +
      149 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_342_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 161,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (343 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 150,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (343 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_343 :
    recurrence2Scalar3Exceptional.coeff 343 =
      ((557916738887624504655523819001995629033654732013706818013994895 * 10 ^ 70 +
        3901712702859659706095720251185865606915682204850366608808300761243793) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 344 = 161 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 1 +
      150 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_343_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 162,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (344 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 151,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (344 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_344 :
    recurrence2Scalar3Exceptional.coeff 344 =
      ((8605456358572908073356457387622534918375739204468673486693789 * 10 ^ 70 +
        5242983968532527473871386028945245476139548796750580981776087780942226) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 345 = 162 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_344_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 163,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (345 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 152,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (345 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_345 :
    recurrence2Scalar3Exceptional.coeff 345 =
      ((101612434929577365977223212731873264037907440617901787695374 * 10 ^ 70 +
        0867813162583111586053268106880109540384138681016492058161947685017677) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 346 = 163 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 31 +
      152 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_345_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 164,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (346 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 153,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (346 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_346 :
    recurrence2Scalar3Exceptional.coeff 346 =
      ((923570904691216235005924573453807784047384235122772543447 * 10 ^ 70 +
        9216402445229540010244160585013700406155764363758671682639956321657535) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 347 = 164 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 30 +
      153 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_346_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 165,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (347 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 154,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (347 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_347 :
    recurrence2Scalar3Exceptional.coeff 347 =
      ((6426764575193164454625256914389724958905175090136482915 * 10 ^ 70 +
        8792926389589612812543493223653593117069305833406035161331356662422647) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 348 = 165 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 29 +
      154 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_347_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 166,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (348 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 155,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (348 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_348 :
    recurrence2Scalar3Exceptional.coeff 348 =
      ((33552681580011259217427356470536537432330841638060674 * 10 ^ 70 +
        1028629124774477337159827497278740332989366635046177260323986330031612) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 349 = 166 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 28 +
      155 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_348_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 167,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (349 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 156,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (349 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_349 :
    recurrence2Scalar3Exceptional.coeff 349 =
      ((124903954485799370129506294144337366778360057259805 * 10 ^ 70 +
        6691574903377265239325749628831294599550179414836604923560552903251761) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 350 = 167 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 27 +
      156 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_349_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 168,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (350 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 157,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (350 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_350 :
    recurrence2Scalar3Exceptional.coeff 350 =
      ((284467443988108052740201559015193693062115610310 * 10 ^ 70 +
        6376762842436432844671691044210246498913724337662786540732050552924913) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 351 = 168 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 26 +
      157 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_350_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 169,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (351 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 158,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (351 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_351 :
    recurrence2Scalar3Exceptional.coeff 351 =
      ((96919329309575115810363266522407302331545213 * 10 ^ 70 +
        2312851464262507535853743944339175065469211680096033228784024728808055) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 352 = 169 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 25 +
      158 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_351_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 170,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (352 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 159,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (352 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_352 :
    recurrence2Scalar3Exceptional.coeff 352 =
      -((1907997367312922042608726897106117592033684 * 10 ^ 70 +
        6114086830331997199725491548882764479926003578277373605483362425682620) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 353 = 170 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 24 +
      159 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_352_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 171,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (353 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 160,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (353 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_353 :
    recurrence2Scalar3Exceptional.coeff 353 =
      -((7106454853494958141238177927955034222765 * 10 ^ 70 +
        7274676712152151911145410350243746025415209371401942583715799653363650) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 354 = 171 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 23 +
      160 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_353_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 172,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (354 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 161,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (354 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_354 :
    recurrence2Scalar3Exceptional.coeff 354 =
      -((10424474607868737328921212849089691116 * 10 ^ 70 +
        9790647676228808475345944975039489685927105423249219348568390331875525) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 355 = 172 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 22 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_354_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 173,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (355 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 162,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (355 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_355 :
    recurrence2Scalar3Exceptional.coeff 355 =
      ((4940439777968443037030153383344809 * 10 ^ 70 +
        7915828551603944280790637060256514769655078196668834085506387978165824) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 356 = 173 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 21 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_355_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 174,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (356 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 163,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (356 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_356 :
    recurrence2Scalar3Exceptional.coeff 356 =
      ((48297956634529289014665888790364 * 10 ^ 70 +
        4876671688425523392760270891281002962400178943745755924034595607791063) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 357 = 174 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 20 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_356_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 175,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (357 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 164,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (357 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_357 :
    recurrence2Scalar3Exceptional.coeff 357 =
      ((81129653760573399311333001261 * 10 ^ 70 +
        3113372952868521827594539801035263665257596273640105686575439882835632) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 358 = 175 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 19 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_357_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 176,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (358 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 165,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (358 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_358 :
    recurrence2Scalar3Exceptional.coeff 358 =
      ((34333195538514120053093030 * 10 ^ 70 +
        6846552690021819296732933142354123575575680057861819925231014031992371) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 359 = 176 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 18 +
      165 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_358_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 177,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (359 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 166,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (359 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_359 :
    recurrence2Scalar3Exceptional.coeff 359 =
      -((86655218248311165663849 * 10 ^ 70 +
        0971808851767326104265813945969265719595165839736754458484933041666531) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 360 = 177 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 17 +
      166 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_359_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 178,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (360 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 167,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (360 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_360 :
    recurrence2Scalar3Exceptional.coeff 360 =
      -((172908079401735005663 * 10 ^ 70 +
        1457197213112020936634632755076519751514725627191116913877389628694130) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 361 = 178 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 16 +
      167 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_360_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 179,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (361 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 168,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (361 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_361 :
    recurrence2Scalar3Exceptional.coeff 361 =
      -((153082333270124634 * 10 ^ 70 +
        2250509333767950467862510423401599178092354787603795010513861845663014) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 362 = 179 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 15 +
      168 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_361_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 180,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (362 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 169,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (362 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_362 :
    recurrence2Scalar3Exceptional.coeff 362 =
      -((78691694018128 * 10 ^ 70 +
        8455751709903878040925708229393823141112825237976829858435676791226815) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 363 = 180 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 14 +
      169 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_362_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 181,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (363 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 170,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (363 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_363 :
    recurrence2Scalar3Exceptional.coeff 363 =
      -((24551936777 * 10 ^ 70 +
        8465120289327752543933855826758355937263890317880191113094818533263217) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 364 = 181 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 13 +
      170 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_363_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 182,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (364 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 171,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (364 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_364 :
    recurrence2Scalar3Exceptional.coeff 364 =
      -((4607328 * 10 ^ 70 +
        5300993054559788516292117597967019935296321196107596911654359100711592) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 365 = 182 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 12 +
      171 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_364_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 183,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (365 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 172,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (365 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_365 :
    recurrence2Scalar3Exceptional.coeff 365 =
      -((505 * 10 ^ 70 +
        4878857782894039382841266157355483153263516127269833803255046094114382) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 366 = 183 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 11 +
      172 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_365_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 184,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (366 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 173,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (366 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_366 :
    recurrence2Scalar3Exceptional.coeff 366 =
      (-314360548704161721232711598665403869432812482847758332073976232516527 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 367 = 184 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 10 +
      173 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_366_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 185,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (367 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 174,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (367 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_367 :
    recurrence2Scalar3Exceptional.coeff 367 =
      (-10410397204066192364460051365504577706061046438508635194153972870 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 368 = 185 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 9 +
      174 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_367_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 186,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (368 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 175,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (368 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_368 :
    recurrence2Scalar3Exceptional.coeff 368 =
      (-162282759350867435952606765182298523381676141578943905061015 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 369 = 186 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 8 +
      175 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_368_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 187,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (369 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 176,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (369 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_369 :
    recurrence2Scalar3Exceptional.coeff 369 =
      (-1068873158294425762268180727250779896172024106199360369 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 370 = 187 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 7 +
      176 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_369_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 188,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (370 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 177,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (370 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_370 :
    recurrence2Scalar3Exceptional.coeff 370 =
      (-3165235645754014046010262867403287390685644340487 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 371 = 188 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 6 +
      177 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_370_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 189,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (371 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 178,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (371 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_371 :
    recurrence2Scalar3Exceptional.coeff 371 =
      (-3818780553013805840581005380943155647737877 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 372 = 189 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 5 +
      178 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_371_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 190,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (372 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_372_suffix_zero :
    (∑ x ∈ Finset.range 179,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (372 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_372 :
    recurrence2Scalar3Exceptional.coeff 372 =
      (-991462750806985695491116848863711095 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 373 = 190 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 4 +
      179 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_372_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_372_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 191,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (373 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_373_suffix_zero :
    (∑ x ∈ Finset.range 180,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (373 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_373 :
    recurrence2Scalar3Exceptional.coeff 373 =
      (-10602472227767369736371076242 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 374 = 191 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 3 +
      180 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_373_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_373_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 192,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (374 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_374_suffix_zero :
    (∑ x ∈ Finset.range 181,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (374 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_374 :
    recurrence2Scalar3Exceptional.coeff 374 =
      (-26247306779745334905 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 375 = 192 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 2 +
      181 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_374_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_374_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 193,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (375 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_375_suffix_zero :
    (∑ x ∈ Finset.range 182,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (375 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_375 :
    recurrence2Scalar3Exceptional.coeff 375 =
      (-18890099430 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 376 = 193 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 1 +
      182 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_375_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_375_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
