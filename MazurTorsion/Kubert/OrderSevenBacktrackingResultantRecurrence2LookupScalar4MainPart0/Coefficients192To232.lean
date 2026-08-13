/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB4
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupQuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar4MainPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar4Main coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2B4_coeff_0
  recurrence2B4_coeff_1
  recurrence2B4_coeff_2
  recurrence2B4_coeff_3
  recurrence2B4_coeff_4
  recurrence2B4_coeff_5
  recurrence2B4_coeff_6
  recurrence2B4_coeff_7
  recurrence2B4_coeff_8
  recurrence2B4_coeff_9
  recurrence2B4_coeff_10
  recurrence2B4_coeff_11
  recurrence2B4_coeff_12
  recurrence2B4_coeff_13
  recurrence2B4_coeff_14
  recurrence2B4_coeff_15
  recurrence2B4_coeff_16
  recurrence2B4_coeff_17
  recurrence2B4_coeff_18
  recurrence2B4_coeff_19
  recurrence2B4_coeff_20
  recurrence2B4_coeff_21
  recurrence2B4_coeff_22
  recurrence2B4_coeff_23
  recurrence2B4_coeff_24
  recurrence2B4_coeff_25
  recurrence2B4_coeff_26
  recurrence2B4_coeff_27
  recurrence2B4_coeff_28
  recurrence2B4_coeff_29
  recurrence2B4_coeff_30
  recurrence2B4_coeff_31
  recurrence2B4_coeff_32
  recurrence2B4_coeff_33
  recurrence2B4_coeff_34
  recurrence2B4_coeff_35
  recurrence2B4_coeff_36
  recurrence2B4_coeff_37
  recurrence2B4_coeff_38
  recurrence2B4_coeff_39
  recurrence2B4_coeff_40
  recurrence2B4_coeff_41
  recurrence2B4_coeff_42
  recurrence2B4_coeff_43
  recurrence2B4_coeff_44
  recurrence2B4_coeff_45
  recurrence2B4_coeff_46
  recurrence2B4_coeff_47
  recurrence2B4_coeff_48
  recurrence2B4_coeff_49
  recurrence2B4_coeff_50
  recurrence2B4_coeff_51
  recurrence2B4_coeff_52
  recurrence2B4_coeff_53
  recurrence2B4_coeff_54
  recurrence2B4_coeff_55
  recurrence2B4_coeff_56
  recurrence2B4_coeff_57
  recurrence2B4_coeff_58
  recurrence2B4_coeff_59
  recurrence2B4_coeff_60
  recurrence2B4_coeff_61
  recurrence2B4_coeff_62
  recurrence2B4_coeff_63
  recurrence2B4_coeff_64
  recurrence2B4_coeff_65
  recurrence2B4_coeff_66
  recurrence2B4_coeff_67
  recurrence2B4_coeff_68
  recurrence2B4_coeff_69
  recurrence2B4_coeff_70
  recurrence2B4_coeff_71
  recurrence2B4_coeff_72
  recurrence2B4_coeff_73
  recurrence2B4_coeff_74
  recurrence2B4_coeff_75
  recurrence2B4_coeff_76
  recurrence2B4_coeff_77
  recurrence2B4_coeff_78
  recurrence2B4_coeff_79
  recurrence2B4_coeff_80
  recurrence2B4_coeff_81
  recurrence2B4_coeff_82
  recurrence2B4_coeff_83
  recurrence2B4_coeff_84
  recurrence2B4_coeff_85
  recurrence2B4_coeff_86
  recurrence2B4_coeff_87
  recurrence2B4_coeff_88
  recurrence2B4_coeff_89
  recurrence2B4_coeff_90
  recurrence2B4_coeff_91
  recurrence2B4_coeff_92
  recurrence2B4_coeff_93
  recurrence2B4_coeff_94
  recurrence2B4_coeff_95
  recurrence2B4_coeff_96
  recurrence2B4_coeff_97
  recurrence2B4_coeff_98
  recurrence2B4_coeff_99
  recurrence2B4_coeff_100
  recurrence2B4_coeff_101
  recurrence2B4_coeff_102
  recurrence2B4_coeff_103
  recurrence2B4_coeff_104
  recurrence2B4_coeff_105
  recurrence2B4_coeff_106
  recurrence2B4_coeff_107
  recurrence2B4_coeff_108
  recurrence2B4_coeff_109
  recurrence2B4_coeff_110
  recurrence2B4_coeff_111
  recurrence2B4_coeff_112
  recurrence2B4_coeff_113
  recurrence2B4_coeff_114
  recurrence2B4_coeff_115
  recurrence2B4_coeff_116
  recurrence2B4_coeff_117
  recurrence2B4_coeff_118
  recurrence2B4_coeff_119
  recurrence2B4_coeff_120
  recurrence2B4_coeff_121
  recurrence2B4_coeff_122
  recurrence2B4_coeff_123
  recurrence2B4_coeff_124
  recurrence2B4_coeff_125
  recurrence2B4_coeff_126
  recurrence2B4_coeff_127
  recurrence2B4_coeff_128
  recurrence2B4_coeff_129
  recurrence2B4_coeff_130
  recurrence2B4_coeff_131
  recurrence2B4_coeff_132
  recurrence2B4_coeff_133
  recurrence2B4_coeff_134
  recurrence2B4_coeff_135
  recurrence2B4_coeff_136
  recurrence2B4_coeff_137
  recurrence2B4_coeff_138
  recurrence2QuotientConstant_coeff_0
  recurrence2QuotientConstant_coeff_1
  recurrence2QuotientConstant_coeff_2
  recurrence2QuotientConstant_coeff_3
  recurrence2QuotientConstant_coeff_4
  recurrence2QuotientConstant_coeff_5
  recurrence2QuotientConstant_coeff_6
  recurrence2QuotientConstant_coeff_7
  recurrence2QuotientConstant_coeff_8
  recurrence2QuotientConstant_coeff_9
  recurrence2QuotientConstant_coeff_10
  recurrence2QuotientConstant_coeff_11
  recurrence2QuotientConstant_coeff_12
  recurrence2QuotientConstant_coeff_13
  recurrence2QuotientConstant_coeff_14
  recurrence2QuotientConstant_coeff_15
  recurrence2QuotientConstant_coeff_16
  recurrence2QuotientConstant_coeff_17
  recurrence2QuotientConstant_coeff_18
  recurrence2QuotientConstant_coeff_19
  recurrence2QuotientConstant_coeff_20
  recurrence2QuotientConstant_coeff_21
  recurrence2QuotientConstant_coeff_22
  recurrence2QuotientConstant_coeff_23
  recurrence2QuotientConstant_coeff_24
  recurrence2QuotientConstant_coeff_25
  recurrence2QuotientConstant_coeff_26
  recurrence2QuotientConstant_coeff_27
  recurrence2QuotientConstant_coeff_28
  recurrence2QuotientConstant_coeff_29
  recurrence2QuotientConstant_coeff_30
  recurrence2QuotientConstant_coeff_31
  recurrence2QuotientConstant_coeff_32
  recurrence2QuotientConstant_coeff_33
  recurrence2QuotientConstant_coeff_34
  recurrence2QuotientConstant_coeff_35
  recurrence2QuotientConstant_coeff_36
  recurrence2QuotientConstant_coeff_37
  recurrence2QuotientConstant_coeff_38
  recurrence2QuotientConstant_coeff_39
  recurrence2QuotientConstant_coeff_40
  recurrence2QuotientConstant_coeff_41
  recurrence2QuotientConstant_coeff_42
  recurrence2QuotientConstant_coeff_43
  recurrence2QuotientConstant_coeff_44
  recurrence2QuotientConstant_coeff_45
  recurrence2QuotientConstant_coeff_46
  recurrence2QuotientConstant_coeff_47
  recurrence2QuotientConstant_coeff_48
  recurrence2QuotientConstant_coeff_49
  recurrence2QuotientConstant_coeff_50
  recurrence2QuotientConstant_coeff_51
  recurrence2QuotientConstant_coeff_52
  recurrence2QuotientConstant_coeff_53
  recurrence2QuotientConstant_coeff_54
  recurrence2QuotientConstant_coeff_55
  recurrence2QuotientConstant_coeff_56
  recurrence2QuotientConstant_coeff_57
  recurrence2QuotientConstant_coeff_58
  recurrence2QuotientConstant_coeff_59
  recurrence2QuotientConstant_coeff_60
  recurrence2QuotientConstant_coeff_61
  recurrence2QuotientConstant_coeff_62
  recurrence2QuotientConstant_coeff_63
  recurrence2QuotientConstant_coeff_64
  recurrence2QuotientConstant_coeff_65
  recurrence2QuotientConstant_coeff_66
  recurrence2QuotientConstant_coeff_67
  recurrence2QuotientConstant_coeff_68
  recurrence2QuotientConstant_coeff_69
  recurrence2QuotientConstant_coeff_70
  recurrence2QuotientConstant_coeff_71
  recurrence2QuotientConstant_coeff_72
  recurrence2QuotientConstant_coeff_73
  recurrence2QuotientConstant_coeff_74
  recurrence2QuotientConstant_coeff_75
  recurrence2QuotientConstant_coeff_76
  recurrence2QuotientConstant_coeff_77
  recurrence2QuotientConstant_coeff_78
  recurrence2QuotientConstant_coeff_79
  recurrence2QuotientConstant_coeff_80
  recurrence2QuotientConstant_coeff_81
  recurrence2QuotientConstant_coeff_82
  recurrence2QuotientConstant_coeff_83
  recurrence2QuotientConstant_coeff_84
  recurrence2QuotientConstant_coeff_85
  recurrence2QuotientConstant_coeff_86
  recurrence2QuotientConstant_coeff_87
  recurrence2QuotientConstant_coeff_88
  recurrence2QuotientConstant_coeff_89
  recurrence2QuotientConstant_coeff_90
  recurrence2QuotientConstant_coeff_91
  recurrence2QuotientConstant_coeff_92
  recurrence2QuotientConstant_coeff_93
  recurrence2QuotientConstant_coeff_94
  recurrence2QuotientConstant_coeff_95
  recurrence2QuotientConstant_coeff_96
  recurrence2QuotientConstant_coeff_97
  recurrence2QuotientConstant_coeff_98
  recurrence2QuotientConstant_coeff_99
  recurrence2QuotientConstant_coeff_100
  recurrence2QuotientConstant_coeff_101
  recurrence2QuotientConstant_coeff_102
  recurrence2QuotientConstant_coeff_103
  recurrence2QuotientConstant_coeff_104
  recurrence2QuotientConstant_coeff_105
  recurrence2QuotientConstant_coeff_106
  recurrence2QuotientConstant_coeff_107
  recurrence2QuotientConstant_coeff_108
  recurrence2QuotientConstant_coeff_109
  recurrence2QuotientConstant_coeff_110
  recurrence2QuotientConstant_coeff_111
  recurrence2QuotientConstant_coeff_112
  recurrence2QuotientConstant_coeff_113
  recurrence2QuotientConstant_coeff_114
  recurrence2QuotientConstant_coeff_115
  recurrence2QuotientConstant_coeff_116
  recurrence2QuotientConstant_coeff_117
  recurrence2QuotientConstant_coeff_118
  recurrence2QuotientConstant_coeff_119
  recurrence2QuotientConstant_coeff_120
  recurrence2QuotientConstant_coeff_121
  recurrence2QuotientConstant_coeff_122
  recurrence2QuotientConstant_coeff_123
  recurrence2QuotientConstant_coeff_124
  recurrence2QuotientConstant_coeff_125
  recurrence2QuotientConstant_coeff_126
  recurrence2QuotientConstant_coeff_127
  recurrence2QuotientConstant_coeff_128
  recurrence2QuotientConstant_coeff_129
  recurrence2QuotientConstant_coeff_130
  recurrence2QuotientConstant_coeff_131
  recurrence2QuotientConstant_coeff_132
  recurrence2QuotientConstant_coeff_133
  recurrence2QuotientConstant_coeff_134
  recurrence2QuotientConstant_coeff_135
  recurrence2QuotientConstant_coeff_136
  recurrence2QuotientConstant_coeff_137
  recurrence2QuotientConstant_coeff_138
  recurrence2QuotientConstant_coeff_139
  recurrence2QuotientConstant_coeff_140
  recurrence2QuotientConstant_coeff_141
  recurrence2QuotientConstant_coeff_142
  recurrence2QuotientConstant_coeff_143
  recurrence2QuotientConstant_coeff_144
  recurrence2QuotientConstant_coeff_145
  recurrence2QuotientConstant_coeff_146
  recurrence2QuotientConstant_coeff_147
  recurrence2QuotientConstant_coeff_148
  recurrence2QuotientConstant_coeff_149
  recurrence2QuotientConstant_coeff_150
  recurrence2QuotientConstant_coeff_151
  recurrence2QuotientConstant_coeff_152
  recurrence2QuotientConstant_coeff_153
  recurrence2QuotientConstant_coeff_154
  recurrence2QuotientConstant_coeff_155
  recurrence2QuotientConstant_coeff_156
  recurrence2QuotientConstant_coeff_157
  recurrence2QuotientConstant_coeff_158
  recurrence2QuotientConstant_coeff_159
  recurrence2QuotientConstant_coeff_160
  recurrence2QuotientConstant_coeff_161
  recurrence2QuotientConstant_coeff_162
  recurrence2QuotientConstant_coeff_163
  recurrence2QuotientConstant_coeff_164
  recurrence2QuotientConstant_coeff_165
  recurrence2QuotientConstant_coeff_166
  recurrence2QuotientConstant_coeff_167
  recurrence2QuotientConstant_coeff_168
  recurrence2QuotientConstant_coeff_169
  recurrence2QuotientConstant_coeff_170
  recurrence2QuotientConstant_coeff_171
  recurrence2QuotientConstant_coeff_172
  recurrence2QuotientConstant_coeff_173
  recurrence2QuotientConstant_coeff_174
  recurrence2QuotientConstant_coeff_175
  recurrence2QuotientConstant_coeff_176
  recurrence2QuotientConstant_coeff_177
  recurrence2QuotientConstant_coeff_178
  recurrence2QuotientConstant_coeff_179
  recurrence2QuotientConstant_coeff_180
  recurrence2QuotientConstant_coeff_181
  recurrence2QuotientConstant_coeff_182
  recurrence2QuotientConstant_coeff_183
  recurrence2QuotientConstant_coeff_184
  recurrence2QuotientConstant_coeff_185
  recurrence2QuotientConstant_coeff_186
  recurrence2QuotientConstant_coeff_187
  recurrence2QuotientConstant_coeff_188
  recurrence2QuotientConstant_coeff_189
  recurrence2QuotientConstant_coeff_190
  recurrence2QuotientConstant_coeff_191
  recurrence2QuotientConstant_coeff_192
  recurrence2QuotientConstant_coeff_193
  recurrence2QuotientConstant_coeff_194
  recurrence2QuotientConstant_coeff_195
  recurrence2QuotientConstant_coeff_196
  recurrence2QuotientConstant_coeff_197
  recurrence2QuotientConstant_coeff_198
  recurrence2QuotientConstant_coeff_199
  recurrence2QuotientConstant_coeff_200
  recurrence2QuotientConstant_coeff_201
  recurrence2QuotientConstant_coeff_202
  recurrence2QuotientConstant_coeff_203
  recurrence2QuotientConstant_coeff_204
  recurrence2QuotientConstant_coeff_205
  recurrence2QuotientConstant_coeff_206
  recurrence2QuotientConstant_coeff_207
  recurrence2QuotientConstant_coeff_208
  recurrence2QuotientConstant_coeff_209
  recurrence2QuotientConstant_coeff_210
  recurrence2QuotientConstant_coeff_211
  recurrence2QuotientConstant_coeff_212
  recurrence2QuotientConstant_coeff_213
  recurrence2QuotientConstant_coeff_214
  recurrence2QuotientConstant_coeff_215
  recurrence2QuotientConstant_coeff_216
  recurrence2QuotientConstant_coeff_217
  recurrence2QuotientConstant_coeff_218
  recurrence2QuotientConstant_coeff_219
  recurrence2QuotientConstant_coeff_220
  recurrence2QuotientConstant_coeff_221
  recurrence2QuotientConstant_coeff_222
  recurrence2QuotientConstant_coeff_223
  recurrence2QuotientConstant_coeff_224
  recurrence2QuotientConstant_coeff_225
  recurrence2QuotientConstant_coeff_226
  recurrence2QuotientConstant_coeff_227
  recurrence2QuotientConstant_coeff_228
  recurrence2QuotientConstant_coeff_229
  recurrence2QuotientConstant_coeff_230
  recurrence2QuotientConstant_coeff_231
  recurrence2QuotientConstant_coeff_232
  recurrence2QuotientConstant_coeff_233

private theorem recurrence2Scalar4Main_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (192 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_192 :
    recurrence2Scalar4Main.coeff 192 =
      (((595442742478422790540862986142029941028013673350716158712310 * 10 ^ 70 +
        4596212849631422884359744985128205835848763349567657101939075138255839) * 10 ^ 70 +
        8182084435948249656882941278429881152900653340869862012061584434338289) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 193 = 0 +
    193 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 193 = 32 +
      161 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 161 = 32 +
      129 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 129 = 32 +
      97 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 97 = 32 +
      65 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 65 = 11 +
      54 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_192_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (193 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_193 :
    recurrence2Scalar4Main.coeff 193 =
      (((356637604802278782534481861122952628524747315583194138607677 * 10 ^ 70 +
        2555135205364082179764794024079141848668726933313758760182060734806642) * 10 ^ 70 +
        2951094965988321409707796470739012571618562451377840412601769931763303) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 194 = 0 +
    194 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 194 = 32 +
      162 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 162 = 32 +
      130 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 130 = 32 +
      98 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 98 = 32 +
      66 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 66 = 11 +
      55 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_193_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (194 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_194 :
    recurrence2Scalar4Main.coeff 194 =
      -(((5005616538541674126512034976647968451258548335972860733933725 * 10 ^ 70 +
        4360983744485750056588266008514024823810686908491506029641854029125797) * 10 ^ 70 +
        0646322232003253411003384487852037547346956460227066091031593775204909) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 195 = 0 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 11 +
      56 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_194_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (195 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_195 :
    recurrence2Scalar4Main.coeff 195 =
      (((16972282629349193790070418129969980534978438353291633144932743 * 10 ^ 70 +
        4702463683075123496397448957584960938237363064388485818760300424131013) * 10 ^ 70 +
        2745046338820000006631744456485249989508628166015240919020890970600822) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 196 = 0 +
    196 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 196 = 32 +
      164 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 164 = 32 +
      132 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 132 = 32 +
      100 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 100 = 32 +
      68 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 68 = 11 +
      57 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_195_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (196 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_196 :
    recurrence2Scalar4Main.coeff 196 =
      -(((35330546598809857532058602315112329751271560476231583043827784 * 10 ^ 70 +
        8358016929842067533146565222464572782885370449403301293164018757823983) * 10 ^ 70 +
        0534727297353281602464753652895289507977114042232415372149213416785335) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 197 = 0 +
    197 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 197 = 32 +
      165 by norm_num, Finset.sum_range_add]
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
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_196_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (197 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_197 :
    recurrence2Scalar4Main.coeff 197 =
      (((36886451828229405142579893785483572984225594935548891721544666 * 10 ^ 70 +
        0689458877503750295312435353108135873749506030236304072371059041616118) * 10 ^ 70 +
        9083170561980851162503402903773516035365191242732170383176111904376215) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 198 = 0 +
    198 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 32 +
      70 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 70 = 11 +
      59 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_197_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (198 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_198 :
    recurrence2Scalar4Main.coeff 198 =
      (((59196412474005496883051113343137771972788911731602769942988009 * 10 ^ 70 +
        2813220399449236371949109501184023501517478925916322374711297535606770) * 10 ^ 70 +
        0878000908646804463898490037045640266419334603864071287609405236352071) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 199 = 0 +
    199 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 199 = 32 +
      167 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 167 = 32 +
      135 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 11 +
      60 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_198_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (199 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_199 :
    recurrence2Scalar4Main.coeff 199 =
      -(((430462263395051876308629265385714443016343344909976327655037615 * 10 ^ 70 +
        5776860442383060467117924464036181000029678300502398113660930924774394) * 10 ^ 70 +
        2895216729136995302526546702051321542872007357887708173562718342446216) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 200 = 0 +
    200 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 200 = 32 +
      168 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 168 = 32 +
      136 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 136 = 32 +
      104 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 104 = 32 +
      72 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 72 = 11 +
      61 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_199_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (200 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_200 :
    recurrence2Scalar4Main.coeff 200 =
      (((1319612339968506391153318041833171086039261999280816039491750918 * 10 ^ 70 +
        5946823212108777205429934312486479993045548026791388142330932790209664) * 10 ^ 70 +
        5300118040826173030894331482839743659419610784531106225509364241719540) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 201 = 0 +
    201 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 201 = 32 +
      169 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 11 +
      62 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_200_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (201 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_201 :
    recurrence2Scalar4Main.coeff 201 =
      -(((2736672205854154540378726813980123972545919627667761138487091820 * 10 ^ 70 +
        1059278290159295071844879505371474801200233248379374169530047172323069) * 10 ^ 70 +
        2459407191557795741236041446465932538228455442263734050653187836162899) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 202 = 0 +
    202 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 106 = 32 +
      74 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 74 = 11 +
      63 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_201_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (202 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_202 :
    recurrence2Scalar4Main.coeff 202 =
      (((3541169468720030731959187492738432972374497004505310662644065364 * 10 ^ 70 +
        0174819209985307894054908298848810707745794415818708521151194673636011) * 10 ^ 70 +
        2370823514419504720107623331294930108619138807602949566575812945341419) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 203 = 0 +
    203 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 203 = 32 +
      171 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 171 = 32 +
      139 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 139 = 32 +
      107 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 11 +
      64 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_202_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (203 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_203 :
    recurrence2Scalar4Main.coeff 203 =
      (((489221560446293924382067304111450833867034283519965820054501507 * 10 ^ 70 +
        7680351299707838417159981075391671847587321576969231932957839910740444) * 10 ^ 70 +
        3293192448049473638843974118183069087216986079563216767159910238683388) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 204 = 0 +
    204 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 204 = 32 +
      172 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 172 = 32 +
      140 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 140 = 32 +
      108 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 108 = 32 +
      76 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 76 = 11 +
      65 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_203_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (204 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_204 :
    recurrence2Scalar4Main.coeff 204 =
      -(((19513071629685158149558348971145478120592317812634633232787056359 * 10 ^ 70 +
        8989897356503300413745657344980496545765823255293071344763523535257415) * 10 ^ 70 +
        0940272431419305507391910209092629739562591109941989529249647762349086) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 205 = 0 +
    205 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 205 = 32 +
      173 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 11 +
      66 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_204_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (205 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_205 :
    recurrence2Scalar4Main.coeff 205 =
      (((71564090147867462350814619497270511975724458934488996087508027002 * 10 ^ 70 +
        2533709648260473873949307593335204784776368006720934039414381167524631) * 10 ^ 70 +
        3531978104391101472429064688331793140014358906053851233720968681341489) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 206 = 0 +
    206 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 206 = 32 +
      174 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 174 = 32 +
      142 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 142 = 32 +
      110 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 110 = 32 +
      78 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 78 = 11 +
      67 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_205_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (206 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_206 :
    recurrence2Scalar4Main.coeff 206 =
      -(((177764928260033109637054267563987071590650099208232511326498264459 * 10 ^ 70 +
        0555697837318634948511187618899609390877902401483906769160533644981068) * 10 ^ 70 +
        1882037768268210964653435163209765818279468642998939184882738935709092) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 207 = 0 +
    207 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 207 = 32 +
      175 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 175 = 32 +
      143 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 143 = 32 +
      111 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 11 +
      68 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_206_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (207 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_207 :
    recurrence2Scalar4Main.coeff 207 =
      (((338188291400152325655720822037482648863331064186641059699306015386 * 10 ^ 70 +
        7344260356038755998568579547503951009183241786283635058304675427723708) * 10 ^ 70 +
        5766178217369981641243301136191449419649923697570244905044997795144680) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 208 = 0 +
    208 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 208 = 32 +
      176 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 176 = 32 +
      144 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 144 = 32 +
      112 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 112 = 32 +
      80 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 80 = 11 +
      69 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_207_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (208 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_208 :
    recurrence2Scalar4Main.coeff 208 =
      -(((466974333623585108826761650749619474966132758473664984146314660979 * 10 ^ 70 +
        4678358058593334893328877162030289007801296053701608109808744810096175) * 10 ^ 70 +
        5719805403714788546751467682815231757755384957498377795917529110176122) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 209 = 0 +
    209 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 209 = 32 +
      177 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 11 +
      70 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_208_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (209 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_209 :
    recurrence2Scalar4Main.coeff 209 =
      (((258765033036518806025245775548447560402612567513828374559083898542 * 10 ^ 70 +
        9838939423243977721124784329537603315400127498973141259334998083729169) * 10 ^ 70 +
        9817851532297948609402279881442155774987539480286854009538014387219459) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 210 = 0 +
    210 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 210 = 32 +
      178 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 178 = 32 +
      146 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 11 +
      71 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_209_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (210 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_210 :
    recurrence2Scalar4Main.coeff 210 =
      (((1036824822882421268527095061927086341137774389973118862734763011875 * 10 ^ 70 +
        8559896363984433014862217792359278524135633684099314437170813167086861) * 10 ^ 70 +
        3467299291983984694316896393687638315316570102313174542674403540105191) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 211 = 0 +
    211 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 211 = 32 +
      179 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 11 +
      72 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_210_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (211 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_211 :
    recurrence2Scalar4Main.coeff 211 =
      -(((4926378202729796066536637050380581375078109000975482993984661691617 * 10 ^ 70 +
        8567084944100304138199065233119159400627921641067404644846533068778917) * 10 ^ 70 +
        6465215470829614558978033396506568211310324973721984632862811469944637) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 212 = 0 +
    212 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 212 = 32 +
      180 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 180 = 32 +
      148 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 148 = 32 +
      116 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 116 = 32 +
      84 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 84 = 11 +
      73 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_211_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (212 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_212 :
    recurrence2Scalar4Main.coeff 212 =
      (((13993898334596636799403528293241672446770843162633777063694021410402 * 10 ^ 70 +
        6825167569284059315416248897972503614082638391331670879884103179436291) * 10 ^ 70 +
        1566852316040394955716111297113466376982049299374683864947179188576555) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 213 = 0 +
    213 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 213 = 32 +
      181 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 181 = 32 +
      149 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 149 = 32 +
      117 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 117 = 32 +
      85 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 85 = 11 +
      74 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_212_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (213 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_213 :
    recurrence2Scalar4Main.coeff 213 =
      -(((32040771469225682043105964077981709567567885056530216467838660988512 * 10 ^ 70 +
        2501006190188335674422630023202781094154823588705858601557608956056879) * 10 ^ 70 +
        4329107238556216567540088323100159485510752142406360363084459661323349) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 214 = 0 +
    214 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 214 = 32 +
      182 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 182 = 32 +
      150 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 11 +
      75 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_213_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (214 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_214 :
    recurrence2Scalar4Main.coeff 214 =
      (((63705467741336647195915285546962385020881388011524300612436978782829 * 10 ^ 70 +
        4077433604869593021827164786642802392342778180042006513060946184199798) * 10 ^ 70 +
        6132368006421539671355290590946899246703396488453912054515736888994869) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 215 = 0 +
    215 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 215 = 32 +
      183 by norm_num, Finset.sum_range_add]
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
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_214_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (215 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_215 :
    recurrence2Scalar4Main.coeff 215 =
      -(((113093178801298498765829387688643798362142934290345129497522263755081 * 10 ^ 70 +
        6752131199231814893292519677367333932385263380318806461269585648834503) * 10 ^ 70 +
        7794030032117735208247169560675251714273462106544195757128858230114936) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 216 = 0 +
    216 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 216 = 32 +
      184 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 184 = 32 +
      152 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 152 = 32 +
      120 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 120 = 32 +
      88 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 88 = 11 +
      77 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_215_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (216 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_216 :
    recurrence2Scalar4Main.coeff 216 =
      (((180918871548576413265724697274230403995333948733216348170438510064859 * 10 ^ 70 +
        2887451425750768937681065320628362636409711917287691838015739015662604) * 10 ^ 70 +
        7685896353177886329041830804065685329852785237012755009803980142561706) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 217 = 0 +
    217 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 217 = 32 +
      185 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 185 = 32 +
      153 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 153 = 32 +
      121 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 121 = 32 +
      89 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 89 = 11 +
      78 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_216_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (217 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_217 :
    recurrence2Scalar4Main.coeff 217 =
      -(((259854294532578150075246362015233907701784699842550882654041586321723 * 10 ^ 70 +
        9827568890261866407354151269275336807334851663608687500477430683048069) * 10 ^ 70 +
        4997974699739867569479982039043678995167450922703608192753566560008996) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 218 = 0 +
    218 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 32 +
      154 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 11 +
      79 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_217_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (218 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_218 :
    recurrence2Scalar4Main.coeff 218 =
      (((328260373579093058744661113510228659784648734409583070771067595919758 * 10 ^ 70 +
        0669212485257232600234071813554173560701403297235656900917282138368459) * 10 ^ 70 +
        2797302928077651703539855269449034015961500120430765670650220357220953) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 219 = 0 +
    219 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 219 = 32 +
      187 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 11 +
      80 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_218_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (219 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_219 :
    recurrence2Scalar4Main.coeff 219 =
      -(((343288183394694642518484767159498763409328585112194207476196859548726 * 10 ^ 70 +
        9057228444557774781604784662555113627102333083044116807585074147366735) * 10 ^ 70 +
        1029962191645006392860072390954474036564729161290087170947933403466150) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 220 = 0 +
    220 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 220 = 32 +
      188 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 188 = 32 +
      156 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 156 = 32 +
      124 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 124 = 32 +
      92 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 92 = 11 +
      81 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_219_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (220 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_220 :
    recurrence2Scalar4Main.coeff 220 =
      (((235305201677771155678053165092831706371689525179974524269840110646566 * 10 ^ 70 +
        1470870972655057315305471748037949387518756161524335518131275374528073) * 10 ^ 70 +
        5955526672136428180376209501660836072097295340282383628430863454132198) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 221 = 0 +
    221 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 221 = 32 +
      189 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 189 = 32 +
      157 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 157 = 32 +
      125 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 125 = 32 +
      93 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 93 = 11 +
      82 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_220_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (221 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_221 :
    recurrence2Scalar4Main.coeff 221 =
      (((93563043618153505547987815469175528917862493966508441682046602246497 * 10 ^ 70 +
        6573759812410943850503366507515848892714449736891180000760402692043623) * 10 ^ 70 +
        4077717065167199132963225938444037459468445567021844531860048498381486) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 222 = 0 +
    222 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 222 = 32 +
      190 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 190 = 32 +
      158 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 158 = 32 +
      126 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 126 = 32 +
      94 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 94 = 11 +
      83 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_221_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (222 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_222 :
    recurrence2Scalar4Main.coeff 222 =
      -(((763730577712869530213127500442131311435163203710292713817442438124997 * 10 ^ 70 +
        3260647150083108505906268633293325517873662880972683566606457838709393) * 10 ^ 70 +
        4098337572981833972819264268851181329971485002052846901929476366052717) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 223 = 0 +
    223 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 223 = 32 +
      191 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 11 +
      84 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_222_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (223 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_223 :
    recurrence2Scalar4Main.coeff 223 =
      (((1902992841808837530681720373615730696895554451786700683757792747131934 * 10 ^ 70 +
        5722343140719724962984034578010063941247814020986145398570061788303518) * 10 ^ 70 +
        5209822766404628608870599263910639079801487441219081938719315533888709) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 224 = 0 +
    224 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 224 = 32 +
      192 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 192 = 32 +
      160 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 160 = 32 +
      128 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 128 = 32 +
      96 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 96 = 11 +
      85 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_223_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (224 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_224 :
    recurrence2Scalar4Main.coeff 224 =
      -(((3621588019868893534226399203726696846962191125348141860199757201225155 * 10 ^ 70 +
        5115145214126933946649652303613929414930900979073848118101426634128625) * 10 ^ 70 +
        1682063874542512393475052183028630087333780553686890831499131854915041) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 225 = 0 +
    225 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 225 = 32 +
      193 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 193 = 32 +
      161 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 161 = 32 +
      129 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 129 = 32 +
      97 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 97 = 11 +
      86 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_224_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (225 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_225 :
    recurrence2Scalar4Main.coeff 225 =
      (((5980147142530380927333991879646105341086702088150201682316148990371873 * 10 ^ 70 +
        6290959905501195228790557893439584884132004212442658782184555611574217) * 10 ^ 70 +
        1064495508243630573591445853715956371559381075083357742921566564767507) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 226 = 0 +
    226 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 226 = 32 +
      194 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 194 = 32 +
      162 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 162 = 32 +
      130 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 130 = 32 +
      98 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 98 = 11 +
      87 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_225_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 88,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (226 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_226 :
    recurrence2Scalar4Main.coeff 226 =
      -(((8956523768613645238369057059153073367233132260721689172002621162743652 * 10 ^ 70 +
        9587003286992281080806566750210100338738235997203311878482302856743366) * 10 ^ 70 +
        5093463876250747535686966542280016440105527041975301656712509079009451) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 227 = 0 +
    227 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 227 = 32 +
      195 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 11 +
      88 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_226_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 89,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (227 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_227 :
    recurrence2Scalar4Main.coeff 227 =
      ((((1 * 10 ^ 70 +
        2420048692817636811046743994304587802198310426922111435481984659600225) * 10 ^ 70 +
        9086345866081550397922994502678499476442582931364162811203386706410993) * 10 ^ 70 +
        3636345061351638095959309287405349904302017721146072850068508326044690) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 228 = 0 +
    228 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 228 = 32 +
      196 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 196 = 32 +
      164 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 164 = 32 +
      132 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 132 = 32 +
      100 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 100 = 11 +
      89 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_227_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 90,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (228 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_228 :
    recurrence2Scalar4Main.coeff 228 =
      -((((1 * 10 ^ 70 +
        6122368946936604984980984948236427585774543964093263579333492276600482) * 10 ^ 70 +
        0160908315379607190125997537194160526036315160594297969402623508426330) * 10 ^ 70 +
        0665970738898403089255058358519099734699725304192107092617996487771553) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 229 = 0 +
    229 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 229 = 32 +
      197 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 197 = 32 +
      165 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 11 +
      90 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_228_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 91,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (229 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_229 :
    recurrence2Scalar4Main.coeff 229 =
      ((((1 * 10 ^ 70 +
        9711904799407735771481095837912624600697049920145212038489178352857498) * 10 ^ 70 +
        8589141170691503070699225797237842027687785626831679726205062589350618) * 10 ^ 70 +
        3766889142527414550121429840699478957965422425450121011308195662593377) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 230 = 0 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 11 +
      91 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_229_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 92,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (230 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_230 :
    recurrence2Scalar4Main.coeff 230 =
      -((((2 * 10 ^ 70 +
        2774095033267714646538919063841421400589161295907506935971233836419975) * 10 ^ 70 +
        6139048825416294894464374878699036156376562673503691256263887910265457) * 10 ^ 70 +
        4965471653146423774907924098788641556815961209744665495550353397846622) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 231 = 0 +
    231 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 231 = 32 +
      199 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 199 = 32 +
      167 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 167 = 32 +
      135 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 11 +
      92 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_230_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 93,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (231 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_231 :
    recurrence2Scalar4Main.coeff 231 =
      ((((2 * 10 ^ 70 +
        4892996607894148789467920867950578824466032546248167817965652775744140) * 10 ^ 70 +
        6213819982119581026608594652125917058496073595136145036570427488046108) * 10 ^ 70 +
        7747977165927669436679894534308661636081828987227028083363705295884986) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 232 = 0 +
    232 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 232 = 32 +
      200 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 200 = 32 +
      168 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 168 = 32 +
      136 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 136 = 32 +
      104 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 104 = 11 +
      93 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_231_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Main_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 94,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (232 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_232 :
    recurrence2Scalar4Main.coeff 232 =
      -((((2 * 10 ^ 70 +
        5723280489061886330056861171536976452641346188235717082266230782392539) * 10 ^ 70 +
        8410852488596618025254023693770570958913017039134882237644087830296447) * 10 ^ 70 +
        4551006252388443808618392084716443150570734161627146502879730711672511) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 233 = 0 +
    233 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 233 = 32 +
      201 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 201 = 32 +
      169 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 11 +
      94 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_232_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
