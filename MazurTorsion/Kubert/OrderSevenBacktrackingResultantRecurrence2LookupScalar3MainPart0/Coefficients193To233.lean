/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB3
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupQuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar3MainPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar3Main coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2B3_coeff_0
  recurrence2B3_coeff_1
  recurrence2B3_coeff_2
  recurrence2B3_coeff_3
  recurrence2B3_coeff_4
  recurrence2B3_coeff_5
  recurrence2B3_coeff_6
  recurrence2B3_coeff_7
  recurrence2B3_coeff_8
  recurrence2B3_coeff_9
  recurrence2B3_coeff_10
  recurrence2B3_coeff_11
  recurrence2B3_coeff_12
  recurrence2B3_coeff_13
  recurrence2B3_coeff_14
  recurrence2B3_coeff_15
  recurrence2B3_coeff_16
  recurrence2B3_coeff_17
  recurrence2B3_coeff_18
  recurrence2B3_coeff_19
  recurrence2B3_coeff_20
  recurrence2B3_coeff_21
  recurrence2B3_coeff_22
  recurrence2B3_coeff_23
  recurrence2B3_coeff_24
  recurrence2B3_coeff_25
  recurrence2B3_coeff_26
  recurrence2B3_coeff_27
  recurrence2B3_coeff_28
  recurrence2B3_coeff_29
  recurrence2B3_coeff_30
  recurrence2B3_coeff_31
  recurrence2B3_coeff_32
  recurrence2B3_coeff_33
  recurrence2B3_coeff_34
  recurrence2B3_coeff_35
  recurrence2B3_coeff_36
  recurrence2B3_coeff_37
  recurrence2B3_coeff_38
  recurrence2B3_coeff_39
  recurrence2B3_coeff_40
  recurrence2B3_coeff_41
  recurrence2B3_coeff_42
  recurrence2B3_coeff_43
  recurrence2B3_coeff_44
  recurrence2B3_coeff_45
  recurrence2B3_coeff_46
  recurrence2B3_coeff_47
  recurrence2B3_coeff_48
  recurrence2B3_coeff_49
  recurrence2B3_coeff_50
  recurrence2B3_coeff_51
  recurrence2B3_coeff_52
  recurrence2B3_coeff_53
  recurrence2B3_coeff_54
  recurrence2B3_coeff_55
  recurrence2B3_coeff_56
  recurrence2B3_coeff_57
  recurrence2B3_coeff_58
  recurrence2B3_coeff_59
  recurrence2B3_coeff_60
  recurrence2B3_coeff_61
  recurrence2B3_coeff_62
  recurrence2B3_coeff_63
  recurrence2B3_coeff_64
  recurrence2B3_coeff_65
  recurrence2B3_coeff_66
  recurrence2B3_coeff_67
  recurrence2B3_coeff_68
  recurrence2B3_coeff_69
  recurrence2B3_coeff_70
  recurrence2B3_coeff_71
  recurrence2B3_coeff_72
  recurrence2B3_coeff_73
  recurrence2B3_coeff_74
  recurrence2B3_coeff_75
  recurrence2B3_coeff_76
  recurrence2B3_coeff_77
  recurrence2B3_coeff_78
  recurrence2B3_coeff_79
  recurrence2B3_coeff_80
  recurrence2B3_coeff_81
  recurrence2B3_coeff_82
  recurrence2B3_coeff_83
  recurrence2B3_coeff_84
  recurrence2B3_coeff_85
  recurrence2B3_coeff_86
  recurrence2B3_coeff_87
  recurrence2B3_coeff_88
  recurrence2B3_coeff_89
  recurrence2B3_coeff_90
  recurrence2B3_coeff_91
  recurrence2B3_coeff_92
  recurrence2B3_coeff_93
  recurrence2B3_coeff_94
  recurrence2B3_coeff_95
  recurrence2B3_coeff_96
  recurrence2B3_coeff_97
  recurrence2B3_coeff_98
  recurrence2B3_coeff_99
  recurrence2B3_coeff_100
  recurrence2B3_coeff_101
  recurrence2B3_coeff_102
  recurrence2B3_coeff_103
  recurrence2B3_coeff_104
  recurrence2B3_coeff_105
  recurrence2B3_coeff_106
  recurrence2B3_coeff_107
  recurrence2B3_coeff_108
  recurrence2B3_coeff_109
  recurrence2B3_coeff_110
  recurrence2B3_coeff_111
  recurrence2B3_coeff_112
  recurrence2B3_coeff_113
  recurrence2B3_coeff_114
  recurrence2B3_coeff_115
  recurrence2B3_coeff_116
  recurrence2B3_coeff_117
  recurrence2B3_coeff_118
  recurrence2B3_coeff_119
  recurrence2B3_coeff_120
  recurrence2B3_coeff_121
  recurrence2B3_coeff_122
  recurrence2B3_coeff_123
  recurrence2B3_coeff_124
  recurrence2B3_coeff_125
  recurrence2B3_coeff_126
  recurrence2B3_coeff_127
  recurrence2B3_coeff_128
  recurrence2B3_coeff_129
  recurrence2B3_coeff_130
  recurrence2B3_coeff_131
  recurrence2B3_coeff_132
  recurrence2B3_coeff_133
  recurrence2B3_coeff_134
  recurrence2B3_coeff_135
  recurrence2B3_coeff_136
  recurrence2B3_coeff_137
  recurrence2B3_coeff_138
  recurrence2B3_coeff_139
  recurrence2B3_coeff_140
  recurrence2B3_coeff_141
  recurrence2B3_coeff_142
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

private theorem recurrence2Scalar3Main_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (193 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_193 :
    recurrence2Scalar3Main.coeff 193 =
      (((7301992695299001316703198460388135553728618067195985799562513 * 10 ^ 70 +
        0923375329033568322111373585460811405303856748945393017143988407199519) * 10 ^ 70 +
        9719720847914541167773117170490304349622382840458711678655868405761836) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 66 = 15 +
      51 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_193_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (194 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_194 :
    recurrence2Scalar3Main.coeff 194 =
      -(((8887753612172579844192206622439442562716040712792633202792009 * 10 ^ 70 +
        5754295382824216713221790330129362084086532462821554060548166714214593) * 10 ^ 70 +
        5088201932695442031278667732436668012407000456497403798932464651012920) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 67 = 15 +
      52 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_194_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (195 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_195 :
    recurrence2Scalar3Main.coeff 195 =
      -(((11591641582185166639212682747198104829491151555392082000096696 * 10 ^ 70 +
        6366258197451839988638232187807276935969580210241009534783472318590397) * 10 ^ 70 +
        0795874395142639854117631454727254917983750089735774647095707528267232) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 68 = 15 +
      53 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_195_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (196 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_196 :
    recurrence2Scalar3Main.coeff 196 =
      (((99206092870155315372884897110134496242921100085793996961950024 * 10 ^ 70 +
        8250441719822203775320629359800197101458397477105539048777913096151574) * 10 ^ 70 +
        4854892388013193344221761240807111603654314020156129629429298574921371) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 69 = 15 +
      54 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_196_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (197 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_197 :
    recurrence2Scalar3Main.coeff 197 =
      -(((311410677690717600156058848577804928776213259612041147982577483 * 10 ^ 70 +
        1129484540105774180733311779460532210965008576570498260856313058180913) * 10 ^ 70 +
        5532591438967011213150935106755511018762389651695947701763756987368693) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 70 = 15 +
      55 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_197_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (198 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_198 :
    recurrence2Scalar3Main.coeff 198 =
      (((609806307112725055764508266313380454289419165346132250576452711 * 10 ^ 70 +
        8431547783834317224867036218905750720914032631770149088908809932695855) * 10 ^ 70 +
        2857202705644962385418308973137701502686790084317834812546883926921150) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 71 = 15 +
      56 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_198_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (199 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_199 :
    recurrence2Scalar3Main.coeff 199 =
      -(((535800684655971970880251889562175198145648379805451700585149354 * 10 ^ 70 +
        4847633880464052420920239337075032803145642018809226773020172889533463) * 10 ^ 70 +
        0766324981517307811306835730003775440451375803611308493347458779161128) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 72 = 15 +
      57 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_199_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (200 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_200 :
    recurrence2Scalar3Main.coeff 200 =
      -(((1412376319287922859005866195418026463802134297559994360845690289 * 10 ^ 70 +
        6702499266747119024294834752106884748360959489899969066188189736667503) * 10 ^ 70 +
        3824825443883816867332626385428925781249640162104276352101572218086158) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 73 = 15 +
      58 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_200_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (201 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_201 :
    recurrence2Scalar3Main.coeff 201 =
      (((8412766427181781192419757768110016704173268210229698567355426583 * 10 ^ 70 +
        8358134084752538500523723841790756535083425311241258726711686183416885) * 10 ^ 70 +
        0464076517246355682057749410121221784658763636065316030053891466678017) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 74 = 15 +
      59 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_201_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (202 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_202 :
    recurrence2Scalar3Main.coeff 202 =
      -(((24563621546589636210340619763296186472806937750063609215628983659 * 10 ^ 70 +
        7802873343322735593582441241743893578114893898292830775683657310260483) * 10 ^ 70 +
        2236935916477594323926571749364034339066983178902205954323834696959154) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 75 = 15 +
      60 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_202_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (203 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_203 :
    recurrence2Scalar3Main.coeff 203 =
      (((49140163239598231066095467579816833795287886343252463847537448553 * 10 ^ 70 +
        7215971202756440482768885821469647817209839330587594166598466694775433) * 10 ^ 70 +
        7700954410650130165666218059508570119357073930967807200552038010037262) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 76 = 15 +
      61 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_203_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (204 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_204 :
    recurrence2Scalar3Main.coeff 204 =
      -(((59451399445788166318374032105653640574689948667694757586448701042 * 10 ^ 70 +
        1386350313138483799258672259334918803783690776016882523144174625237865) * 10 ^ 70 +
        6800940177874070218184543034974839363115512449264763636080066017101985) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 77 = 15 +
      62 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_204_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (205 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_205 :
    recurrence2Scalar3Main.coeff 205 =
      -(((24680904611689541127869669128742400521775839701447965668661391674 * 10 ^ 70 +
        0090386696109506295423298246630013056779924660165358483272808230833300) * 10 ^ 70 +
        1687633381567491276574422266654133538651488662772659275661778879902370) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 78 = 15 +
      63 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_205_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (206 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_206 :
    recurrence2Scalar3Main.coeff 206 =
      (((392624972731296863894755649336504866440576648426369397009197928264 * 10 ^ 70 +
        1254730427540361024241776076015405804034720718630033744394884899232989) * 10 ^ 70 +
        1621705987487290609049315872777768208382643643121599461208624235127642) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 79 = 15 +
      64 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_206_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (207 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_207 :
    recurrence2Scalar3Main.coeff 207 =
      -(((1375949853357741385243612079790120920344041394934309769808389540643 * 10 ^ 70 +
        1295678807490611533532521383261491548833209054830151561469335505564127) * 10 ^ 70 +
        5255984306585488659864677333187588013405084366779961344805922021185901) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 80 = 15 +
      65 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_207_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (208 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_208 :
    recurrence2Scalar3Main.coeff 208 =
      (((3353511793523122292422297762032460553032666408665548185029464430012 * 10 ^ 70 +
        6647880813157854903149617583830727514537154769165565346194903385935206) * 10 ^ 70 +
        2137803277582467222976805967497038161122682824549144917709284164018786) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 81 = 15 +
      66 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_208_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (209 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_209 :
    recurrence2Scalar3Main.coeff 209 =
      -(((6290580096448221648006691690863659044451755658441921951209554460798 * 10 ^ 70 +
        2716341593353393580086146947575380110136616113901299645239685852221866) * 10 ^ 70 +
        6529837803732921143911427329399304913648740465842391870387883987993169) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 82 = 15 +
      67 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_209_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (210 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_210 :
    recurrence2Scalar3Main.coeff 210 =
      (((8505155613703505605687895102924253274918079888809591382616641662054 * 10 ^ 70 +
        6173923109356633751284585716073681820004047412991774560379272776184030) * 10 ^ 70 +
        3112433822698076765054552803245237018457119949825727310413861543591009) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 83 = 15 +
      68 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_210_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (211 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_211 :
    recurrence2Scalar3Main.coeff 211 =
      -(((4120250773636624739207700561864843205288879294983476734439404917669 * 10 ^ 70 +
        2069485656550505460074751700594722413325015639567872826232014520946302) * 10 ^ 70 +
        3263001955293239077422834171952495993765612556593476401412201099570427) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 84 = 15 +
      69 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_211_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (212 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_212 :
    recurrence2Scalar3Main.coeff 212 =
      -(((21272775209916010224754638669298364884260534320862590433232450480440 * 10 ^ 70 +
        0659352692905283932031025795843985544521274897001946344851267265060375) * 10 ^ 70 +
        8759738613125900110819630741484453977234063114520584973147087723886133) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 85 = 15 +
      70 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_212_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (213 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_213 :
    recurrence2Scalar3Main.coeff 213 =
      (((96685761833268677543338157579830254412976701680880725900923921804369 * 10 ^ 70 +
        8023256364342368573594289046541872749408311922591704675708192381113016) * 10 ^ 70 +
        2687347040830188764872353091265530442700903634452699875489120460487135) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 86 = 15 +
      71 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_213_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (214 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_214 :
    recurrence2Scalar3Main.coeff 214 =
      -(((272199574867059547862476679753968284896426235113772475177685254307533 * 10 ^ 70 +
        4268243428746263365795700613708758865318318025367766728518346880326266) * 10 ^ 70 +
        2191481757447890722797988351435495353281178213093197908607026316600738) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 87 = 15 +
      72 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_214_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (215 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_215 :
    recurrence2Scalar3Main.coeff 215 =
      (((622272929054969794757880616691328292277765672580580349201707580656540 * 10 ^ 70 +
        7790919492649185851613762432065405165605410546469740956804741381465793) * 10 ^ 70 +
        3126916032030874378525566006110915488065019099468536975290728728953770) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 88 = 15 +
      73 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_215_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (216 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_216 :
    recurrence2Scalar3Main.coeff 216 =
      -(((1239424044250439921465155065205131343596820931390863740299833178325611 * 10 ^ 70 +
        7243859344115737616137846741595201903881140207639284031504057952368740) * 10 ^ 70 +
        5038465858993438421345447813968211329332799507027074831480497549155205) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 89 = 15 +
      74 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_216_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (217 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_217 :
    recurrence2Scalar3Main.coeff 217 =
      (((2209055638905605829035835182814189467499675978627772236192274817155151 * 10 ^ 70 +
        5710976707090005717013411338464235686138303015290920155639712989206665) * 10 ^ 70 +
        9364911292860017021987690034467189819729408733846883556442831382435130) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 90 = 15 +
      75 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_217_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (218 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_218 :
    recurrence2Scalar3Main.coeff 218 =
      -(((3555234612332340129737488842262415792662279571309839465262873305771929 * 10 ^ 70 +
        7172644202699035931028688373454880009467320289821710882655428221129514) * 10 ^ 70 +
        0791504530742875310636691113043254933702528447096313861378193148541245) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 91 = 15 +
      76 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_218_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (219 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_219 :
    recurrence2Scalar3Main.coeff 219 =
      (((5150255047662665903014486178024037997316188740657384188118725165726420 * 10 ^ 70 +
        0908829650791281757531903241107536721368562091091133082921312985700530) * 10 ^ 70 +
        0327336910805564455189435081996182435624018322851050307102777304756261) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 92 = 15 +
      77 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_219_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (220 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_220 :
    recurrence2Scalar3Main.coeff 220 =
      -(((6589768130051102449672589185444425462955025371359150378023598732248805 * 10 ^ 70 +
        7710861577099557968440961256000592410031828902942976252062180546928633) * 10 ^ 70 +
        1360542591837765183403720988107354543024320584605035199481549987437943) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 93 = 15 +
      78 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_220_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (221 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_221 :
    recurrence2Scalar3Main.coeff 221 =
      (((7050684018068733805075220237962643214159136516383043664598259472498440 * 10 ^ 70 +
        0199630496862201640751742286412124188644862514232884426095484831157239) * 10 ^ 70 +
        2844505857207947465108720285569259939542243272868153120195686085273740) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 94 = 15 +
      79 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_221_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (222 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_222 :
    recurrence2Scalar3Main.coeff 222 =
      -(((5168716470740956523977789324714793052712473849720989995267008078305442 * 10 ^ 70 +
        8483865653778379699941905907103305700358859592749627623416429597208295) * 10 ^ 70 +
        7211809276631209786482729246958773439099729812103563492329394461637641) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 95 = 15 +
      80 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_222_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (223 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_223 :
    recurrence2Scalar3Main.coeff 223 =
      -(((1009366321362714398674228019377850865899534756407076904170064524803453 * 10 ^ 70 +
        6225990244442857277266049321370120355130353124967780666128976968848425) * 10 ^ 70 +
        1640807476637323546051002464980832429903502520294983785206404225549790) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 96 = 15 +
      81 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_223_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (224 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_224 :
    recurrence2Scalar3Main.coeff 224 =
      ((((1 * 10 ^ 70 +
        3935613923709828595809058989882796589512350057975312403405397063677945) * 10 ^ 70 +
        9064951824285026484869195552214027518646350064783444839955090157824503) * 10 ^ 70 +
        7244091442752909411510761686856051884585323059334765562064639934749222) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 97 = 15 +
      82 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_224_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (225 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_225 :
    recurrence2Scalar3Main.coeff 225 =
      -((((3 * 10 ^ 70 +
        6280793616482342619982377093767137729942985946320363685560788558528768) * 10 ^ 70 +
        2255429402928173134187094045493343318314748167655945380126523904514554) * 10 ^ 70 +
        7608022659989811649003831281178681423870145058581595913296758536058583) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 98 = 15 +
      83 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_225_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (226 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_226 :
    recurrence2Scalar3Main.coeff 226 =
      ((((7 * 10 ^ 70 +
        0448127251408493313004704718527580006097174763148467075654451322011504) * 10 ^ 70 +
        9490805849943188824579189090793027979798224182206038402461854508198554) * 10 ^ 70 +
        6206538033778773008960617866212291019867875937215224978022002325417829) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 99 = 15 +
      84 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_226_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (227 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_227 :
    recurrence2Scalar3Main.coeff 227 =
      -((((11 * 10 ^ 70 +
        7923384545632506246753389521621235805525766740945645336921205130082413) * 10 ^ 70 +
        1477010978848874031073768552975741324948769997172268530328162587446721) * 10 ^ 70 +
        5258085228908404023254025884626481358632729736491729777808957172670013) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 100 = 15 +
      85 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_227_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (228 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_228 :
    recurrence2Scalar3Main.coeff 228 =
      ((((17 * 10 ^ 70 +
        8573153026499881298530328628112553466781967285265770488899833613568851) * 10 ^ 70 +
        5101034552946660147010233389673893267292149150473365773739406789870963) * 10 ^ 70 +
        0253737626349007364840539181114381021311249025081941418552686534211306) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 101 = 15 +
      86 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_228_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (229 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_229 :
    recurrence2Scalar3Main.coeff 229 =
      -((((25 * 10 ^ 70 +
        0061694452959635648594759998631490476832646679897418842292799789777135) * 10 ^ 70 +
        5842126487706038182970179196386609831119497601641173149966791601741789) * 10 ^ 70 +
        8414124541612182460767211588697406709743156516863656960131616073339809) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 102 = 15 +
      87 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_229_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 88,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (230 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_230 :
    recurrence2Scalar3Main.coeff 230 =
      ((((32 * 10 ^ 70 +
        7579882808971532453785511882872861950793142058288085418276081754239108) * 10 ^ 70 +
        0662527990397035315925614397046025594931783078822165962204850003433997) * 10 ^ 70 +
        7957689262465146163548229792860359601188729305949320483819010689084566) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 103 = 15 +
      88 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_230_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 89,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (231 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_231 :
    recurrence2Scalar3Main.coeff 231 =
      -((((40 * 10 ^ 70 +
        4048026507539076339296510733514585626264569191835547582938313996868118) * 10 ^ 70 +
        9667869012876786437742419754205229512420294608513350190143068351961363) * 10 ^ 70 +
        8383194373481905480640019005426371673822679849905514212187604358577235) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 104 = 15 +
      89 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_231_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 90,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (232 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_232 :
    recurrence2Scalar3Main.coeff 232 =
      ((((47 * 10 ^ 70 +
        0863513843709600032690730539501261145626646417193899676419008063675821) * 10 ^ 70 +
        6183681470188042563361350325933317872893838061813937830051980821313589) * 10 ^ 70 +
        4432540564513955784585260869339939136741233756576587068186687254647313) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 105 = 15 +
      90 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_232_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 91,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (233 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_233 :
    recurrence2Scalar3Main.coeff 233 =
      -((((51 * 10 ^ 70 +
        9130268859450496790779173341053864063559668681565128704216296897810501) * 10 ^ 70 +
        5461054375509823247347216566963964832872875624915445994419331304433288) * 10 ^ 70 +
        1610173706025507708330488092909610692914533065595523730428348312047620) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 106 = 15 +
      91 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_233_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
