/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupQuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar1MainPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar1Main coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2B1_coeff_0
  recurrence2B1_coeff_1
  recurrence2B1_coeff_2
  recurrence2B1_coeff_3
  recurrence2B1_coeff_4
  recurrence2B1_coeff_5
  recurrence2B1_coeff_6
  recurrence2B1_coeff_7
  recurrence2B1_coeff_8
  recurrence2B1_coeff_9
  recurrence2B1_coeff_10
  recurrence2B1_coeff_11
  recurrence2B1_coeff_12
  recurrence2B1_coeff_13
  recurrence2B1_coeff_14
  recurrence2B1_coeff_15
  recurrence2B1_coeff_16
  recurrence2B1_coeff_17
  recurrence2B1_coeff_18
  recurrence2B1_coeff_19
  recurrence2B1_coeff_20
  recurrence2B1_coeff_21
  recurrence2B1_coeff_22
  recurrence2B1_coeff_23
  recurrence2B1_coeff_24
  recurrence2B1_coeff_25
  recurrence2B1_coeff_26
  recurrence2B1_coeff_27
  recurrence2B1_coeff_28
  recurrence2B1_coeff_29
  recurrence2B1_coeff_30
  recurrence2B1_coeff_31
  recurrence2B1_coeff_32
  recurrence2B1_coeff_33
  recurrence2B1_coeff_34
  recurrence2B1_coeff_35
  recurrence2B1_coeff_36
  recurrence2B1_coeff_37
  recurrence2B1_coeff_38
  recurrence2B1_coeff_39
  recurrence2B1_coeff_40
  recurrence2B1_coeff_41
  recurrence2B1_coeff_42
  recurrence2B1_coeff_43
  recurrence2B1_coeff_44
  recurrence2B1_coeff_45
  recurrence2B1_coeff_46
  recurrence2B1_coeff_47
  recurrence2B1_coeff_48
  recurrence2B1_coeff_49
  recurrence2B1_coeff_50
  recurrence2B1_coeff_51
  recurrence2B1_coeff_52
  recurrence2B1_coeff_53
  recurrence2B1_coeff_54
  recurrence2B1_coeff_55
  recurrence2B1_coeff_56
  recurrence2B1_coeff_57
  recurrence2B1_coeff_58
  recurrence2B1_coeff_59
  recurrence2B1_coeff_60
  recurrence2B1_coeff_61
  recurrence2B1_coeff_62
  recurrence2B1_coeff_63
  recurrence2B1_coeff_64
  recurrence2B1_coeff_65
  recurrence2B1_coeff_66
  recurrence2B1_coeff_67
  recurrence2B1_coeff_68
  recurrence2B1_coeff_69
  recurrence2B1_coeff_70
  recurrence2B1_coeff_71
  recurrence2B1_coeff_72
  recurrence2B1_coeff_73
  recurrence2B1_coeff_74
  recurrence2B1_coeff_75
  recurrence2B1_coeff_76
  recurrence2B1_coeff_77
  recurrence2B1_coeff_78
  recurrence2B1_coeff_79
  recurrence2B1_coeff_80
  recurrence2B1_coeff_81
  recurrence2B1_coeff_82
  recurrence2B1_coeff_83
  recurrence2B1_coeff_84
  recurrence2B1_coeff_85
  recurrence2B1_coeff_86
  recurrence2B1_coeff_87
  recurrence2B1_coeff_88
  recurrence2B1_coeff_89
  recurrence2B1_coeff_90
  recurrence2B1_coeff_91
  recurrence2B1_coeff_92
  recurrence2B1_coeff_93
  recurrence2B1_coeff_94
  recurrence2B1_coeff_95
  recurrence2B1_coeff_96
  recurrence2B1_coeff_97
  recurrence2B1_coeff_98
  recurrence2B1_coeff_99
  recurrence2B1_coeff_100
  recurrence2B1_coeff_101
  recurrence2B1_coeff_102
  recurrence2B1_coeff_103
  recurrence2B1_coeff_104
  recurrence2B1_coeff_105
  recurrence2B1_coeff_106
  recurrence2B1_coeff_107
  recurrence2B1_coeff_108
  recurrence2B1_coeff_109
  recurrence2B1_coeff_110
  recurrence2B1_coeff_111
  recurrence2B1_coeff_112
  recurrence2B1_coeff_113
  recurrence2B1_coeff_114
  recurrence2B1_coeff_115
  recurrence2B1_coeff_116
  recurrence2B1_coeff_117
  recurrence2B1_coeff_118
  recurrence2B1_coeff_119
  recurrence2B1_coeff_120
  recurrence2B1_coeff_121
  recurrence2B1_coeff_122
  recurrence2B1_coeff_123
  recurrence2B1_coeff_124
  recurrence2B1_coeff_125
  recurrence2B1_coeff_126
  recurrence2B1_coeff_127
  recurrence2B1_coeff_128
  recurrence2B1_coeff_129
  recurrence2B1_coeff_130
  recurrence2B1_coeff_131
  recurrence2B1_coeff_132
  recurrence2B1_coeff_133
  recurrence2B1_coeff_134
  recurrence2B1_coeff_135
  recurrence2B1_coeff_136
  recurrence2B1_coeff_137
  recurrence2B1_coeff_138
  recurrence2B1_coeff_139
  recurrence2B1_coeff_140
  recurrence2B1_coeff_141
  recurrence2B1_coeff_142
  recurrence2B1_coeff_143
  recurrence2B1_coeff_144
  recurrence2B1_coeff_145
  recurrence2B1_coeff_146
  recurrence2B1_coeff_147
  recurrence2B1_coeff_148
  recurrence2B1_coeff_149
  recurrence2B1_coeff_150
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

private theorem recurrence2Scalar1Main_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (195 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_195 :
    recurrence2Scalar1Main.coeff 195 =
      (((412645496293888699171064079314228157050111379446970066096457072 * 10 ^ 70 +
        8480008591313949157066663556641401144718985506954254157007018022601394) * 10 ^ 70 +
        4267406067494721858270824485297196333386653251092596264847651574428946) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 68 = 23 +
      45 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_195_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (196 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_196 :
    recurrence2Scalar1Main.coeff 196 =
      -(((352291647584392994161201735479366129156545422034131959886946959 * 10 ^ 70 +
        8877088682623850811712063955740580666530682707625101494329309913555265) * 10 ^ 70 +
        9367311442159688177674113225673360465177935695442157767216746496910135) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 69 = 23 +
      46 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_196_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (197 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_197 :
    recurrence2Scalar1Main.coeff 197 =
      -(((1235495839541026873859491390491464559317489154791864661779571736 * 10 ^ 70 +
        5914308030505865774311795898212906138228262062803076029688505004081851) * 10 ^ 70 +
        0326220445728312709579165149382538443864782558891883558690547432163789) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 70 = 23 +
      47 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_197_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (198 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_198 :
    recurrence2Scalar1Main.coeff 198 =
      (((6980233606135199643528056068897943017052630599586923836743743937 * 10 ^ 70 +
        2156335904611049987858720904508236032654850084267000704350387840720245) * 10 ^ 70 +
        8236736921342051823693357594304329526914638273992147757513415734883694) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 71 = 23 +
      48 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_198_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (199 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_199 :
    recurrence2Scalar1Main.coeff 199 =
      -(((19597068102068607155645316494256254721417454807874455082163650105 * 10 ^ 70 +
        0303704847485928157814262682476969674037049962788821680906108468669917) * 10 ^ 70 +
        0808054298725058701077206950942610965351470130650341781526716308383203) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 72 = 23 +
      49 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_199_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (200 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_200 :
    recurrence2Scalar1Main.coeff 200 =
      (((34457678637971689932419582195658117334108361084489203530740886180 * 10 ^ 70 +
        6156436935618790458059979527954996184784096103617090809356415369630205) * 10 ^ 70 +
        0909014125520685637613082328493157738991552359325638372613600331742129) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 73 = 23 +
      50 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_200_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (201 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_201 :
    recurrence2Scalar1Main.coeff 201 =
      -(((19092072046893101928308097897961861944408226060890920361659338482 * 10 ^ 70 +
        3451045366114291817265309299006206603616145412723844260546071066512114) * 10 ^ 70 +
        4076634264567409066119807288861938270802294681325987269077277906590087) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 74 = 23 +
      51 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_201_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (202 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_202 :
    recurrence2Scalar1Main.coeff 202 =
      -(((123634760017121994258548069885800418082026883665582503325171388206 * 10 ^ 70 +
        7284129718744735490776635312403285895556404542920150774962365517235784) * 10 ^ 70 +
        3505513616945979180381659307111355516843820886781482020370438567067957) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 75 = 23 +
      52 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_202_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (203 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_203 :
    recurrence2Scalar1Main.coeff 203 =
      (((586799587985841740430295681785035052643683948818067976227308214851 * 10 ^ 70 +
        5582276632302031170588000288979602542116022862964362478782784265044231) * 10 ^ 70 +
        1596892341854615994039655522916987204146865497764941445219423852456736) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 76 = 23 +
      53 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_203_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (204 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_204 :
    recurrence2Scalar1Main.coeff 204 =
      -(((1592032179392165290587256440133199242567332647529518064738689971579 * 10 ^ 70 +
        0539890895666167660318478575592444881211244712973809529619259454301400) * 10 ^ 70 +
        8951325125148779618073369389996528675743335943753920729266153075692746) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 77 = 23 +
      54 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_204_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (205 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_205 :
    recurrence2Scalar1Main.coeff 205 =
      (((2993379611455368361859822788624519116626410743612267893572816403691 * 10 ^ 70 +
        2869488049333552815475308366782187615924349778486944607059605580987520) * 10 ^ 70 +
        7904053570265466044357416892298242688471155162069294383680601195186393) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 78 = 23 +
      55 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_205_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (206 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_206 :
    recurrence2Scalar1Main.coeff 206 =
      -(((3153430352361727679235849747456110583433439022455882172528055573694 * 10 ^ 70 +
        7624397987224783463609325970765170550052164563551373325298449085682782) * 10 ^ 70 +
        7987457321344848109714399781111046966421179285602100198295929884541274) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 79 = 23 +
      56 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_206_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (207 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_207 :
    recurrence2Scalar1Main.coeff 207 =
      -(((3321422515512505423663068704403367001883630869037060760241548579641 * 10 ^ 70 +
        2770626323817987429989381257970318042920093665881895054232022719530069) * 10 ^ 70 +
        7477629944215181121050140755947112357893452284865560230130893708590465) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 80 = 23 +
      57 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_207_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (208 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_208 :
    recurrence2Scalar1Main.coeff 208 =
      (((28776031131713211046211456759592857857683832763855903638835065636387 * 10 ^ 70 +
        5409517958336141860696473625800724722017928778067824106859819485030005) * 10 ^ 70 +
        4063268282939476140121776224743098358706716752900689693520363629475815) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 81 = 23 +
      58 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_208_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (209 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_209 :
    recurrence2Scalar1Main.coeff 209 =
      -(((94267270901318899610835942642301734142864198292519309569087312560987 * 10 ^ 70 +
        3447188549030444424069741264560419434339659315523893590644174937092419) * 10 ^ 70 +
        3672837870949367282284934764028311104925922166894191134128433581632189) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 82 = 23 +
      59 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_209_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (210 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_210 :
    recurrence2Scalar1Main.coeff 210 =
      (((222637180527994681587190668029343983763226926998952500976757942618943 * 10 ^ 70 +
        1476937314127117537832940488285302595683324473488105739364148700129095) * 10 ^ 70 +
        4050304650813031850455058096666698330625753450862178629714816869154181) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 83 = 23 +
      60 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_210_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (211 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_211 :
    recurrence2Scalar1Main.coeff 211 =
      -(((407100185168065928236563046452389852866490092787886287345670213467780 * 10 ^ 70 +
        9478512329762640761992442859329659488007062927264065763164700269571073) * 10 ^ 70 +
        7643700709008724232564361400843439941201580904746865037768098485860329) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 84 = 23 +
      61 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_211_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (212 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_212 :
    recurrence2Scalar1Main.coeff 212 =
      (((528078252195714816471344691003330253356288978330429667435538175644407 * 10 ^ 70 +
        4953887390845987209717218462036305838520133399249556334518288124720497) * 10 ^ 70 +
        6586532711640458118180045842135802017147644681929260626907669822426445) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 85 = 23 +
      62 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_212_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (213 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_213 :
    recurrence2Scalar1Main.coeff 213 =
      -(((181166222123597029740641560782580511190094779143520223666701500624643 * 10 ^ 70 +
        2524220255764504539020101553780200598511885339059845607546721308616427) * 10 ^ 70 +
        8587907572730981742672644137085569583372254983822266402016146980344475) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 86 = 23 +
      63 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_213_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (214 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_214 :
    recurrence2Scalar1Main.coeff 214 =
      -(((1618516322792476896773901049503801310168195587660676019709435842949419 * 10 ^ 70 +
        0831608651720236719677776703397106420731118226402268889150876545531948) * 10 ^ 70 +
        8203332561399510793356975135123396803175395417274546985303297244101486) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 87 = 23 +
      64 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_214_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (215 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_215 :
    recurrence2Scalar1Main.coeff 215 =
      (((6858330933875202306519299223694481102390861961402932520076146401432044 * 10 ^ 70 +
        6588522776688872481940181329553973145969424339924714650003669182084987) * 10 ^ 70 +
        9096549070345969904058367321217948493854863993207197502663015066246083) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 88 = 23 +
      65 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_215_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (216 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_216 :
    recurrence2Scalar1Main.coeff 216 =
      -((((1 * 10 ^ 70 +
        8996759389885912229599450269956226308308631811532694065001761550562588) * 10 ^ 70 +
        8650769520523524740611147444315929248605605499220173903624759618661780) * 10 ^ 70 +
        0877339874847300201220533353023016735507699862863839040095817396849453) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 89 = 23 +
      66 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_216_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (217 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_217 :
    recurrence2Scalar1Main.coeff 217 =
      ((((4 * 10 ^ 70 +
        3251539883790307213667779079343593147471670792442157425722374092550303) * 10 ^ 70 +
        5626415322855040298479011591583759882267608636471980603107675821736234) * 10 ^ 70 +
        8003488779608812002230033699757309960031538987161567217367064813887249) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 90 = 23 +
      67 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_217_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (218 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_218 :
    recurrence2Scalar1Main.coeff 218 =
      -((((8 * 10 ^ 70 +
        6276325414366965722571654072813453365422766967386149902056427809298374) * 10 ^ 70 +
        7783700368282825922185337232857029127584691443709310640494394854818563) * 10 ^ 70 +
        3170403119424809943935190871009152711336219554016942962995901055605795) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 91 = 23 +
      68 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_218_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (219 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_219 :
    recurrence2Scalar1Main.coeff 219 =
      ((((15 * 10 ^ 70 +
        4585428244743827628583106701798993644836562368696596979779247669325571) * 10 ^ 70 +
        7392861378990737569219774013934270291487418508953398701598569913646425) * 10 ^ 70 +
        2604619237214130859179620772619134480248368512207584856327095378269670) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 92 = 23 +
      69 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_219_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (220 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_220 :
    recurrence2Scalar1Main.coeff 220 =
      -((((25 * 10 ^ 70 +
        0976259729552279913458568303528210405323802221589666655878309395015412) * 10 ^ 70 +
        5469492902544638257825551170373456204959727593210566555678315910906985) * 10 ^ 70 +
        1257532986419433231624774398958818676930718885436708250445121327169647) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 93 = 23 +
      70 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_220_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (221 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_221 :
    recurrence2Scalar1Main.coeff 221 =
      ((((36 * 10 ^ 70 +
        8338657384600994829466724155016610262145756685488116976153854218489894) * 10 ^ 70 +
        4320692645631063706188778350595646506816103120743759987606983107805485) * 10 ^ 70 +
        3874560841677717715248328636655684691376583764800452673152486627480099) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 94 = 23 +
      71 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_221_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (222 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_222 :
    recurrence2Scalar1Main.coeff 222 =
      -((((48 * 10 ^ 70 +
        0780917347272623406891882903554143135339559547000888019396677529983627) * 10 ^ 70 +
        1396267200764560809637557136122947928108453510778810200684690634237135) * 10 ^ 70 +
        2316317265826697373708841157016325051579804406024003555685572647191536) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 95 = 23 +
      72 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_222_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (223 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_223 :
    recurrence2Scalar1Main.coeff 223 =
      ((((53 * 10 ^ 70 +
        3018172311160924104274317624935278860733878980774527798141260773281655) * 10 ^ 70 +
        1764084759110118943978727774835032845041336095714053808724257127000954) * 10 ^ 70 +
        6554581505948743328433910630489657097759806239220846639829010146449208) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 96 = 23 +
      73 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_223_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (224 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_224 :
    recurrence2Scalar1Main.coeff 224 =
      -((((43 * 10 ^ 70 +
        0361270464652415241149404501694104320563154529378215911557222249166336) * 10 ^ 70 +
        0461562906957102812532386060943515303299427778262750947410969532743193) * 10 ^ 70 +
        6942213265982444091195879290571347323942337430905888043660692227285160) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 97 = 23 +
      74 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_224_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (225 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_225 :
    recurrence2Scalar1Main.coeff 225 =
      ((((3 * 10 ^ 70 +
        3072353631615462930331368487471974555147048653830315047223273705551794) * 10 ^ 70 +
        7206818089723514352863041615898078394483271029707503373017212838012239) * 10 ^ 70 +
        9193040353627386541240178383358201349312618584933990134450327323142192) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 98 = 23 +
      75 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_225_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (226 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_226 :
    recurrence2Scalar1Main.coeff 226 =
      ((((84 * 10 ^ 70 +
        0257390087905342719844770293941242679579581122847733486012217273151039) * 10 ^ 70 +
        6736795346513580275958821684750561420767915964259735476349445459783830) * 10 ^ 70 +
        7696856991885511768151192315279736055848298719681660356254148909067228) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 99 = 23 +
      76 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_226_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (227 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_227 :
    recurrence2Scalar1Main.coeff 227 =
      -((((239 * 10 ^ 70 +
        5977744778695279865405524581373651818382916525237047721833009120855095) * 10 ^ 70 +
        2170219986545314249481517047885244016390827769868226716985454796496766) * 10 ^ 70 +
        6354942455124484178850434919450695620659939413651713365589033535878199) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 100 = 23 +
      77 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_227_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (228 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_228 :
    recurrence2Scalar1Main.coeff 228 =
      ((((483 * 10 ^ 70 +
        3031979405898075157791891223244305359721713829583295701001729511972507) * 10 ^ 70 +
        6069865157147855497883956142922486564456574595710961427514826088585612) * 10 ^ 70 +
        4431322656276395300164700127286047799925343811412740543314471595786246) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 101 = 23 +
      78 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_228_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (229 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_229 :
    recurrence2Scalar1Main.coeff 229 =
      -((((829 * 10 ^ 70 +
        6595337086387056851058053599683650021749008463732077293475977253171831) * 10 ^ 70 +
        3824600843762811612724134795372940543747942374695603190910607650705493) * 10 ^ 70 +
        6360054794186721308298492990998221031961480836754817904296549170532590) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 102 = 23 +
      79 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_229_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (230 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_230 :
    recurrence2Scalar1Main.coeff 230 =
      ((((1282 * 10 ^ 70 +
        4341672815820912171872857424842302578619068161449149253864110385142464) * 10 ^ 70 +
        3736210345187895443234007679822742115134708793769274240756987794429836) * 10 ^ 70 +
        1472863046149323175551681990029578979034871539135913898053036230934065) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 103 = 23 +
      80 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_230_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (231 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_231 :
    recurrence2Scalar1Main.coeff 231 =
      -((((1829 * 10 ^ 70 +
        6833086370342075237084479000343920656017088797920936700748844660287278) * 10 ^ 70 +
        6097211672280311118618984177544643173945154364888192031180597966354163) * 10 ^ 70 +
        4752142676953896282593322828581396999916524263861180424734883093696803) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 104 = 23 +
      81 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_231_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (232 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_232 :
    recurrence2Scalar1Main.coeff 232 =
      ((((2440 * 10 ^ 70 +
        6404195417811885287523562130965247187153091512682589972111119885448072) * 10 ^ 70 +
        8073436129085885405907242249155482435262034675780470733833106291892331) * 10 ^ 70 +
        9492491205750292644735464852484271343847286386675726818799272311078901) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 105 = 23 +
      82 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_232_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (233 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_233 :
    recurrence2Scalar1Main.coeff 233 =
      -((((3065 * 10 ^ 70 +
        8167101879986834998305243149704569943811437122199497521662321553391711) * 10 ^ 70 +
        4374977798092868317984829257224832631530477612874177845959407630023586) * 10 ^ 70 +
        7719157549565329454516225942597257467699803488604657923096787448026777) : ℚ) := by
  unfold recurrence2Scalar1Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 234 = 0 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
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
    rw [show 106 = 23 +
      83 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_233_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (234 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (234 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_234 :
    recurrence2Scalar1Main.coeff 234 =
      ((((3641 * 10 ^ 70 +
        1590124141371229042657258950066280853577840209498475565439355878163277) * 10 ^ 70 +
        4973105433094246749726423011822273529468643290291364906524724688044419) * 10 ^ 70 +
        8640922430853500488385399789856413435714008778745571682418072634818589) : ℚ) := by
  unfold recurrence2Scalar1Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 235 = 1 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
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
    rw [show 106 = 22 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_234_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_234_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
