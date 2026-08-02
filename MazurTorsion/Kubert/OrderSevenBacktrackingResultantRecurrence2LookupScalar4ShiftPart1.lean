/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB5A6
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar4Shift coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

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
  recurrence2B5A6_coeff_0
  recurrence2B5A6_coeff_1
  recurrence2B5A6_coeff_2
  recurrence2B5A6_coeff_3
  recurrence2B5A6_coeff_4
  recurrence2B5A6_coeff_5
  recurrence2B5A6_coeff_6
  recurrence2B5A6_coeff_7
  recurrence2B5A6_coeff_8
  recurrence2B5A6_coeff_9
  recurrence2B5A6_coeff_10
  recurrence2B5A6_coeff_11
  recurrence2B5A6_coeff_12
  recurrence2B5A6_coeff_13
  recurrence2B5A6_coeff_14
  recurrence2B5A6_coeff_15
  recurrence2B5A6_coeff_16
  recurrence2B5A6_coeff_17
  recurrence2B5A6_coeff_18
  recurrence2B5A6_coeff_19
  recurrence2B5A6_coeff_20
  recurrence2B5A6_coeff_21
  recurrence2B5A6_coeff_22
  recurrence2B5A6_coeff_23
  recurrence2B5A6_coeff_24
  recurrence2B5A6_coeff_25
  recurrence2B5A6_coeff_26
  recurrence2B5A6_coeff_27
  recurrence2B5A6_coeff_28
  recurrence2B5A6_coeff_29
  recurrence2B5A6_coeff_30
  recurrence2B5A6_coeff_31
  recurrence2B5A6_coeff_32
  recurrence2B5A6_coeff_33
  recurrence2B5A6_coeff_34
  recurrence2B5A6_coeff_35
  recurrence2B5A6_coeff_36
  recurrence2B5A6_coeff_37
  recurrence2B5A6_coeff_38
  recurrence2B5A6_coeff_39
  recurrence2B5A6_coeff_40
  recurrence2B5A6_coeff_41
  recurrence2B5A6_coeff_42
  recurrence2B5A6_coeff_43
  recurrence2B5A6_coeff_44
  recurrence2B5A6_coeff_45
  recurrence2B5A6_coeff_46
  recurrence2B5A6_coeff_47
  recurrence2B5A6_coeff_48
  recurrence2B5A6_coeff_49
  recurrence2B5A6_coeff_50
  recurrence2B5A6_coeff_51
  recurrence2B5A6_coeff_52
  recurrence2B5A6_coeff_53
  recurrence2B5A6_coeff_54
  recurrence2B5A6_coeff_55
  recurrence2B5A6_coeff_56
  recurrence2B5A6_coeff_57
  recurrence2B5A6_coeff_58
  recurrence2B5A6_coeff_59
  recurrence2B5A6_coeff_60
  recurrence2B5A6_coeff_61
  recurrence2B5A6_coeff_62
  recurrence2B5A6_coeff_63
  recurrence2B5A6_coeff_64
  recurrence2B5A6_coeff_65
  recurrence2B5A6_coeff_66
  recurrence2B5A6_coeff_67
  recurrence2B5A6_coeff_68
  recurrence2B5A6_coeff_69
  recurrence2B5A6_coeff_70
  recurrence2B5A6_coeff_71
  recurrence2B5A6_coeff_72
  recurrence2B5A6_coeff_73
  recurrence2B5A6_coeff_74
  recurrence2B5A6_coeff_75
  recurrence2B5A6_coeff_76
  recurrence2B5A6_coeff_77
  recurrence2B5A6_coeff_78
  recurrence2B5A6_coeff_79
  recurrence2B5A6_coeff_80
  recurrence2B5A6_coeff_81
  recurrence2B5A6_coeff_82
  recurrence2B5A6_coeff_83
  recurrence2B5A6_coeff_84
  recurrence2B5A6_coeff_85
  recurrence2B5A6_coeff_86
  recurrence2B5A6_coeff_87
  recurrence2B5A6_coeff_88
  recurrence2B5A6_coeff_89
  recurrence2B5A6_coeff_90
  recurrence2B5A6_coeff_91
  recurrence2B5A6_coeff_92
  recurrence2B5A6_coeff_93
  recurrence2B5A6_coeff_94
  recurrence2B5A6_coeff_95
  recurrence2B5A6_coeff_96
  recurrence2B5A6_coeff_97
  recurrence2B5A6_coeff_98
  recurrence2B5A6_coeff_99
  recurrence2B5A6_coeff_100
  recurrence2B5A6_coeff_101
  recurrence2B5A6_coeff_102
  recurrence2B5A6_coeff_103
  recurrence2B5A6_coeff_104
  recurrence2B5A6_coeff_105
  recurrence2B5A6_coeff_106
  recurrence2B5A6_coeff_107
  recurrence2B5A6_coeff_108
  recurrence2B5A6_coeff_109
  recurrence2B5A6_coeff_110
  recurrence2B5A6_coeff_111
  recurrence2B5A6_coeff_112
  recurrence2B5A6_coeff_113
  recurrence2B5A6_coeff_114
  recurrence2B5A6_coeff_115
  recurrence2B5A6_coeff_116
  recurrence2B5A6_coeff_117
  recurrence2B5A6_coeff_118
  recurrence2B5A6_coeff_119
  recurrence2B5A6_coeff_120
  recurrence2B5A6_coeff_121
  recurrence2B5A6_coeff_122
  recurrence2B5A6_coeff_123
  recurrence2B5A6_coeff_124
  recurrence2B5A6_coeff_125
  recurrence2B5A6_coeff_126
  recurrence2B5A6_coeff_127
  recurrence2B5A6_coeff_128
  recurrence2B5A6_coeff_129
  recurrence2B5A6_coeff_130
  recurrence2B5A6_coeff_131
  recurrence2B5A6_coeff_132
  recurrence2B5A6_coeff_133
  recurrence2B5A6_coeff_134
  recurrence2B5A6_coeff_135
  recurrence2B5A6_coeff_136
  recurrence2B5A6_coeff_137
  recurrence2B5A6_coeff_138
  recurrence2B5A6_coeff_139
  recurrence2B5A6_coeff_140
  recurrence2B5A6_coeff_141
  recurrence2B5A6_coeff_142
  recurrence2B5A6_coeff_143
  recurrence2B5A6_coeff_144
  recurrence2B5A6_coeff_145
  recurrence2B5A6_coeff_146
  recurrence2B5A6_coeff_147
  recurrence2B5A6_coeff_148
  recurrence2B5A6_coeff_149
  recurrence2B5A6_coeff_150
  recurrence2B5A6_coeff_151
  recurrence2B5A6_coeff_152
  recurrence2B5A6_coeff_153
  recurrence2B5A6_coeff_154
  recurrence2B5A6_coeff_155
  recurrence2B5A6_coeff_156
  recurrence2B5A6_coeff_157
  recurrence2B5A6_coeff_158
  recurrence2B5A6_coeff_159
  recurrence2B5A6_coeff_160
  recurrence2B5A6_coeff_161
  recurrence2B5A6_coeff_162
  recurrence2B5A6_coeff_163
  recurrence2B5A6_coeff_164
  recurrence2B5A6_coeff_165
  recurrence2B5A6_coeff_166
  recurrence2B5A6_coeff_167
  recurrence2B5A6_coeff_168
  recurrence2B5A6_coeff_169
  recurrence2B5A6_coeff_170
  recurrence2B5A6_coeff_171
  recurrence2B5A6_coeff_172
  recurrence2B5A6_coeff_173
  recurrence2B5A6_coeff_174
  recurrence2B5A6_coeff_175
  recurrence2B5A6_coeff_176
  recurrence2B5A6_coeff_177
  recurrence2B5A6_coeff_178
  recurrence2B5A6_coeff_179
  recurrence2B5A6_coeff_180
  recurrence2B5A6_coeff_181
  recurrence2B5A6_coeff_182
  recurrence2B5A6_coeff_183
  recurrence2B5A6_coeff_184
  recurrence2B5A6_coeff_185
  recurrence2B5A6_coeff_186
  recurrence2B5A6_coeff_187
  recurrence2B5A6_coeff_188
  recurrence2B5A6_coeff_189
  recurrence2B5A6_coeff_190
  recurrence2B5A6_coeff_191
  recurrence2B5A6_coeff_192
  recurrence2B5A6_coeff_193
  recurrence2B5A6_coeff_194
  recurrence2B5A6_coeff_195
  recurrence2B5A6_coeff_196
  recurrence2B5A6_coeff_197
  recurrence2B5A6_coeff_198
  recurrence2B5A6_coeff_199
  recurrence2B5A6_coeff_200
  recurrence2B5A6_coeff_201
  recurrence2B5A6_coeff_202
  recurrence2B5A6_coeff_203
  recurrence2B5A6_coeff_204
  recurrence2B5A6_coeff_205
  recurrence2B5A6_coeff_206
  recurrence2B5A6_coeff_207
  recurrence2B5A6_coeff_208
  recurrence2B5A6_coeff_209
  recurrence2B5A6_coeff_210
  recurrence2B5A6_coeff_211
  recurrence2B5A6_coeff_212
  recurrence2B5A6_coeff_213
  recurrence2B5A6_coeff_214
  recurrence2B5A6_coeff_215
  recurrence2B5A6_coeff_216
  recurrence2B5A6_coeff_217
  recurrence2B5A6_coeff_218
  recurrence2B5A6_coeff_219
  recurrence2B5A6_coeff_220
  recurrence2B5A6_coeff_221
  recurrence2B5A6_coeff_222
  recurrence2B5A6_coeff_223
  recurrence2B5A6_coeff_224
  recurrence2B5A6_coeff_225
  recurrence2B5A6_coeff_226
  recurrence2B5A6_coeff_227
  recurrence2B5A6_coeff_228
  recurrence2B5A6_coeff_229

private theorem recurrence2Scalar4Shift_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (233 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 91,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (233 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_233 :
    recurrence2Scalar4Shift.coeff 233 =
      -(((3697747303609449161532725258324405666646636145865784684046834031899062 * 10 ^ 70 +
        6888248251788118160756442031184312638822198640916631618146659960042227) * 10 ^ 70 +
        2562649836309418278402536346623624248606042399148817165426514663550310) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 234 = 4 +
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
  rw [recurrence2Scalar4Shift_coeff_233_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_233_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (234 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 92,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (234 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_234 :
    recurrence2Scalar4Shift.coeff 234 =
      (((1617778337640174904446982413317664108607222304868168542326605029687526 * 10 ^ 70 +
        6655003814863823557787413531154869832876527326321473934344460324393163) * 10 ^ 70 +
        1531145190881708278605988891041505288232487546625685548561148308909305) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 235 = 5 +
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
    rw [show 102 = 10 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_234_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_234_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (235 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 93,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (235 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_235 :
    recurrence2Scalar4Shift.coeff 235 =
      (((623892504992805310106264766458853722492877611500174805188734121453171 * 10 ^ 70 +
        8903756195786656804319181364941398237196128194198568826030898984102694) * 10 ^ 70 +
        4093192585299647352121527581574404918935520996326523520885889934630273) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 236 = 6 +
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
    rw [show 102 = 9 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_235_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_235_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (236 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 94,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (236 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_236 :
    recurrence2Scalar4Shift.coeff 236 =
      -(((2793056919492907278413648533146895412940998170847781714575048760675947 * 10 ^ 70 +
        5971111672218581950235451943718298523453722552806644378652949901305699) * 10 ^ 70 +
        0952271237934818598930571094391511973465713671116221070281806693418752) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 237 = 7 +
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
    rw [show 102 = 8 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_236_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_236_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (237 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 95,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (237 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_237 :
    recurrence2Scalar4Shift.coeff 237 =
      (((4669803872888036657193476984330319075051224137703334272110192864203077 * 10 ^ 70 +
        1282947399598724042767707440618796212573304873814305465720762686121601) * 10 ^ 70 +
        6796142605671457666918661751352710651426267573682815581035301582754233) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 238 = 8 +
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
    rw [show 102 = 7 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_237_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_237_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (238 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 96,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (238 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_238 :
    recurrence2Scalar4Shift.coeff 238 =
      -(((6083394620445621334897961448076223020632233041805410998508482434846919 * 10 ^ 70 +
        7674435048505426836800996038009157698326904944373162900702745871338387) * 10 ^ 70 +
        9953259068786768281283422294670078926989138470042567649205714181796266) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 239 = 9 +
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
    rw [show 102 = 6 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_238_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_238_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (239 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 97,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (239 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_239 :
    recurrence2Scalar4Shift.coeff 239 =
      (((6936115794764979082196733855796736506792311175652772004086203563455491 * 10 ^ 70 +
        9313636485713303035564251657509883621868160126535666998186893133410794) * 10 ^ 70 +
        5052297229352095477933953824223150699161042856670871229307124990782589) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 240 = 10 +
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
    rw [show 102 = 5 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_239_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_239_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (240 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 98,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (240 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_240 :
    recurrence2Scalar4Shift.coeff 240 =
      -(((7211810530134946576142359670241258735207025631360745135026624996606513 * 10 ^ 70 +
        6782083768740868143877751779961135828864899287900629303336549528535151) * 10 ^ 70 +
        6223809662203501672425406407946270264757755459281612052738366358510189) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 241 = 11 +
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
    rw [show 102 = 4 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_240_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_240_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (241 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 99,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (241 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_241 :
    recurrence2Scalar4Shift.coeff 241 =
      (((6968734765322294017876488448427882148341879564234391883337045800951229 * 10 ^ 70 +
        2591567704575504824090652298546030449343443941442635482489123714773957) * 10 ^ 70 +
        6429613137871434469654390563052472810528691751442240542712853619397100) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 242 = 12 +
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
    rw [show 102 = 3 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_241_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_241_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (242 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 100,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (242 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_242 :
    recurrence2Scalar4Shift.coeff 242 =
      -(((6320051536946651878113244444361130792257664894275470291497730077169447 * 10 ^ 70 +
        8865057090195039149310801151560295971346151668810232194037441699777670) * 10 ^ 70 +
        3842336844720836466824117227111696064540019481501097776339371962769736) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 243 = 13 +
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
    rw [show 102 = 2 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_242_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_242_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (243 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 101,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (243 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_243 :
    recurrence2Scalar4Shift.coeff 243 =
      (((5407668294477552313890529832213886968740128684632824086404765188631400 * 10 ^ 70 +
        6382383022472690558750186355515712092072489249048147919609886260764187) * 10 ^ 70 +
        3024871379905234711691334149206341523159365262405301917705029813076201) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 244 = 14 +
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
    rw [show 102 = 1 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_243_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_243_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (244 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 102,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (244 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_244 :
    recurrence2Scalar4Shift.coeff 244 =
      -(((4375748235168519679297056414088234321664793184468494027101956504822491 * 10 ^ 70 +
        7444910737503297273827187851901653331718153668771311911761342002691821) * 10 ^ 70 +
        7099761437780204381169629511534106428646801566771949618494935210697188) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 245 = 15 +
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
  rw [recurrence2Scalar4Shift_coeff_244_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_244_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (245 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 103,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (245 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_245 :
    recurrence2Scalar4Shift.coeff 245 =
      (((3349185292993493076651949087063991262375896557468091114904083350959814 * 10 ^ 70 +
        1638287729866925071297635243296832027310455619094835237259719812739842) * 10 ^ 70 +
        3449172674587722900142142071220169576899618181535587547596901379483555) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 246 = 16 +
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
    rw [show 134 = 31 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_245_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_245_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (246 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 104,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (246 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_246 :
    recurrence2Scalar4Shift.coeff 246 =
      -(((2420193377265609822663959497858989628786796832289216779553160813932439 * 10 ^ 70 +
        8754130604829891573466321393812408327412831839878213991659736125481702) * 10 ^ 70 +
        7052777164692693004258201976782703991411901403208638877909483703423301) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 247 = 17 +
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
    rw [show 134 = 30 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_246_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_246_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (247 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 105,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (247 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_247 :
    recurrence2Scalar4Shift.coeff 247 =
      (((1643705176954451554961503921166710916386446558598464789435722314243458 * 10 ^ 70 +
        6165674042939729244964274377795728581727476506205085549780188604803491) * 10 ^ 70 +
        4042272527921055016545121438310529315782494447794040438063732308447669) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 248 = 18 +
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
    rw [show 134 = 29 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_247_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_247_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (248 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 106,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (248 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_248 :
    recurrence2Scalar4Shift.coeff 248 =
      -(((1040215824936643627809959633039104910278611448997776236006039204911144 * 10 ^ 70 +
        4494628489891964021684459260134847866072777944576579835278811549354455) * 10 ^ 70 +
        8194861509542852822249189028798469129455859223499514461828305599219115) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 249 = 19 +
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
    rw [show 134 = 28 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_248_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_248_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (249 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 107,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (249 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_249 :
    recurrence2Scalar4Shift.coeff 249 =
      (((603481820133818388090236254296395875435940379680338142839949701363291 * 10 ^ 70 +
        8030524059170329627176339127664905508010125112197110950990461139442131) * 10 ^ 70 +
        5412564904709923650726139077274528981985805356033927533925289893821995) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 250 = 20 +
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
    rw [show 134 = 27 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_249_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_249_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (250 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 108,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (250 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_250 :
    recurrence2Scalar4Shift.coeff 250 =
      -(((310195089701854530568316478356282733931617701101166571319196315922315 * 10 ^ 70 +
        0066566303656996349258705701969884993856466530760894290300499159564632) * 10 ^ 70 +
        7603594592304814242236077179444489790908397439499487082287553865508308) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 251 = 21 +
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
    rw [show 134 = 26 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_250_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_250_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (251 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 109,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (251 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_251 :
    recurrence2Scalar4Shift.coeff 251 =
      (((129211211096792149119263164352966477268388008649791686827782031184934 * 10 ^ 70 +
        8105713076062411713906394695626970400256374644566385613210656808261337) * 10 ^ 70 +
        0948918829327654990544058482364969624873644529508190476281454322376407) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 252 = 22 +
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
    rw [show 134 = 25 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_251_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_251_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (252 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 110,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (252 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_252 :
    recurrence2Scalar4Shift.coeff 252 =
      -(((28782611092067639630255459975749708315044002226001559045528331943740 * 10 ^ 70 +
        9624022910754497006181774325573973121076267425905215468495024966193544) * 10 ^ 70 +
        0133077166095719907762917235609676051071042859232305938245960082184143) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 253 = 23 +
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
    rw [show 134 = 24 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_252_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_252_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (253 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 111,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (253 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_253 :
    recurrence2Scalar4Shift.coeff 253 =
      -(((18814640466712922354264348352739952636653664986644888230749208597075 * 10 ^ 70 +
        4005674114508972714690631155253958332955519243786682243568736431136285) * 10 ^ 70 +
        1603555724416994555901141041305431585956180705579953167539804520349527) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 254 = 24 +
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
    rw [show 134 = 23 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_253_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_253_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (254 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 112,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (254 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_254 :
    recurrence2Scalar4Shift.coeff 254 =
      (((35121167818444049785977884810302953209477488960520546486810744493591 * 10 ^ 70 +
        5291854326051415854563233546044958759557836173715546774356573080185047) * 10 ^ 70 +
        7323261771843607266691289244811836905624848323056192140625755263107363) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 255 = 25 +
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
    rw [show 134 = 22 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_254_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_254_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (255 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 113,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (255 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_255 :
    recurrence2Scalar4Shift.coeff 255 =
      -(((35216690520587175725169262199791863344853858419550028626239579726436 * 10 ^ 70 +
        6932293263362076008696948734490792655735840844315106915576529666103643) * 10 ^ 70 +
        8311624471301841205082119669850758992002395803256258578524785619220668) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 256 = 26 +
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
    rw [show 134 = 21 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_255_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_255_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (256 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 114,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (256 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_256 :
    recurrence2Scalar4Shift.coeff 256 =
      (((28594023766893776893768287977512387780447946489475180231283611932112 * 10 ^ 70 +
        7919329677702085357391999299593916864857955753038802100699940719185820) * 10 ^ 70 +
        5297899108881110777291380886369485085449916544293972362912336754785976) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 257 = 27 +
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
    rw [show 134 = 20 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_256_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_256_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (257 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 115,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (257 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_257 :
    recurrence2Scalar4Shift.coeff 257 =
      -(((20527999506137011547938767427341497190267582816620660816376425826164 * 10 ^ 70 +
        6665102083092308531725805744822041585030159714931422458728034571541631) * 10 ^ 70 +
        3215838948957849770506715254122882948470348692310223644260169919045483) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 258 = 28 +
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
    rw [show 134 = 19 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_257_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_257_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (258 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 116,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (258 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_258 :
    recurrence2Scalar4Shift.coeff 258 =
      (((13469369689880399989408827605337794338340523453155545922646819093682 * 10 ^ 70 +
        1514168361194981141224559762745361799664132849411761338517132804280690) * 10 ^ 70 +
        2857363178465317348323963574929206834731609551240402468617457382491065) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 259 = 29 +
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
    rw [show 134 = 18 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_258_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (259 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 117,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (259 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_259 :
    recurrence2Scalar4Shift.coeff 259 =
      -(((8201495501531809691395886363695795132132391907237661379230947963782 * 10 ^ 70 +
        5210762217214707594994900291725201981093785374502754859575796922550951) * 10 ^ 70 +
        1688446718280263844036623194603147435940546787453314659762259336068710) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 260 = 30 +
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
    rw [show 134 = 17 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_259_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (260 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 118,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (260 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_260 :
    recurrence2Scalar4Shift.coeff 260 =
      (((4668093530264469285183162778508173408685794227924646002767055572148 * 10 ^ 70 +
        8293907846289568563972397937041119504201982554715734257482924842559185) * 10 ^ 70 +
        9090575798121864259727997615312815118829704375468330906543512919115267) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 261 = 31 +
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
    rw [show 134 = 16 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_260_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (261 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 119,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (261 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_261 :
    recurrence2Scalar4Shift.coeff 261 =
      -(((2490389748468634223920912434891651861807796534828584214065245294008 * 10 ^ 70 +
        9028443131785673522473871052624971252275078860712378872368957745431785) * 10 ^ 70 +
        8185869199471422974032661589444843328797534929749161210821513628539613) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 262 = 32 +
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
    rw [show 134 = 15 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_261_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (262 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 120,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (262 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_262 :
    recurrence2Scalar4Shift.coeff 262 =
      (((1244433318854504717186422819102962260011003861736763880878183686666 * 10 ^ 70 +
        9181548440635540008556220176359419054122887334572029486551671659476946) * 10 ^ 70 +
        4093933044356516595422983611126298928310368341220404397098512374348219) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 263 = 33 +
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
    rw [show 134 = 14 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_262_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (263 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 121,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (263 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_263 :
    recurrence2Scalar4Shift.coeff 263 =
      -(((579970965651524778057913769909767029807651321701882028599941645054 * 10 ^ 70 +
        1826497761766359644115860787101773782424495147826846585859686891769415) * 10 ^ 70 +
        6047091109856650934812851290676564629613459471381599830374724918052193) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 264 = 34 +
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
    rw [show 134 = 13 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_263_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (264 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 122,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (264 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_264 :
    recurrence2Scalar4Shift.coeff 264 =
      (((249767623981559587542087773197600401174753435811565692601911760282 * 10 ^ 70 +
        2447485800139895667624350685012322983192156983774725141983603960277463) * 10 ^ 70 +
        4635030692332039347508541851951033123625973056623557741338861779771741) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 265 = 35 +
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
    rw [show 134 = 12 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_264_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (265 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 123,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (265 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_265 :
    recurrence2Scalar4Shift.coeff 265 =
      -(((97562307736093801238100500888519906317768683416940106184187734969 * 10 ^ 70 +
        3257647925738693649705682387020775432535549108754789598713506772049244) * 10 ^ 70 +
        8311540288080734455308014649427280793151439555188317907260891015612148) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 266 = 36 +
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
    rw [show 134 = 11 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_265_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (266 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 124,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (266 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_266 :
    recurrence2Scalar4Shift.coeff 266 =
      (((33186791671368097683250762518879093076636454552666303687506312469 * 10 ^ 70 +
        8567976703254638696038481023335506680747357400363357508109773038420631) * 10 ^ 70 +
        2004304927768557905967124447680347373585163684899575195490650993906434) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 267 = 37 +
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
    rw [show 134 = 10 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_266_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (267 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 125,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (267 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_267 :
    recurrence2Scalar4Shift.coeff 267 =
      -(((8763691747098821267199672366555062245114485633955418025060484346 * 10 ^ 70 +
        9003645566613952261809178894045614109647369195417143563160016883760498) * 10 ^ 70 +
        4199192552346090049174009296039209690629091468950165617240532780184125) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 268 = 38 +
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
    rw [show 134 = 9 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_267_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (268 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 126,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (268 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_268 :
    recurrence2Scalar4Shift.coeff 268 =
      (((881593143801992991918797849036214081480389719818315807717056199 * 10 ^ 70 +
        7265445386056394970998181376326462807590258948339886499109697537864475) * 10 ^ 70 +
        3236271496363933871124116843177344106429806067671014263352257398551355) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 269 = 39 +
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
    rw [show 134 = 8 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_268_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (269 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 127,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (269 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_269 :
    recurrence2Scalar4Shift.coeff 269 =
      (((941064219476994122303343434511329757226236097666416952166106391 * 10 ^ 70 +
        6236115720724931142871918723561950113890980654279725310003419934218491) * 10 ^ 70 +
        5711848585003856661302854554332196592721034682861126359488204137558554) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 270 = 40 +
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
    rw [show 134 = 7 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_269_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (270 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 128,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (270 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_270 :
    recurrence2Scalar4Shift.coeff 270 =
      -(((935019924607153287331028096202278751439438310987060046175461573 * 10 ^ 70 +
        8729285280872996070849418276794429826253623346251417855387232239034218) * 10 ^ 70 +
        6834513581828089549821838382880256622941518406988555012861600196289285) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 271 = 41 +
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
    rw [show 134 = 6 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_270_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (271 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 129,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (271 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_271 :
    recurrence2Scalar4Shift.coeff 271 =
      (((585385653853939263887161918068802903705608841195407989382216837 * 10 ^ 70 +
        3095105726916515541063420753437106827531877244914029109799967259062340) * 10 ^ 70 +
        1284313628290996919825899625878239340716139754513626564369558411962936) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 272 = 42 +
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
    rw [show 134 = 5 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_271_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (272 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 130,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (272 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_272 :
    recurrence2Scalar4Shift.coeff 272 =
      -(((302235038072818931126349169553021762820193937717299775599902675 * 10 ^ 70 +
        6766792601553793967659591095643304829310844829276925676752881568455092) * 10 ^ 70 +
        2757723633782905973678712121639460079558129949513658410147823445782296) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 273 = 43 +
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
    rw [show 134 = 4 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_272_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (273 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 131,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (273 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_273 :
    recurrence2Scalar4Shift.coeff 273 =
      (((137741359230420451149117517213816430767877375815090551000769553 * 10 ^ 70 +
        1796429423361248762274855743913706361986783464241891459766994950912379) * 10 ^ 70 +
        2481279567553163859187295703942069424271117518798393673825181424392219) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 274 = 44 +
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
    rw [show 134 = 3 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_273_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (274 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 132,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (274 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_274 :
    recurrence2Scalar4Shift.coeff 274 =
      -(((56836051038600617201725179652428721297884792384553154065024356 * 10 ^ 70 +
        1334587341987051223882381303922584475266637191327292983067630481136385) * 10 ^ 70 +
        6043601777183635620553255187334260594301423731680642459991412018983756) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 275 = 45 +
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
    rw [show 134 = 2 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_274_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (275 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 133,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (275 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_275 :
    recurrence2Scalar4Shift.coeff 275 =
      (((21433740524665530606585612759335753184468980727467217720763181 * 10 ^ 70 +
        8614092551752324076572068849335355664397686856874397462233449957000553) * 10 ^ 70 +
        6539707470647734625242293644882444911617628302711142712120760719404145) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 276 = 46 +
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
    rw [show 134 = 1 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_275_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (276 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 134,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (276 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_276 :
    recurrence2Scalar4Shift.coeff 276 =
      -(((7389143420215542812463990751642926021123568347054750811811822 * 10 ^ 70 +
        8866494558845121105106993878849315587663017279209993567491606627416041) * 10 ^ 70 +
        6262763047320555022424447590610615465145085343755222269549206859795731) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 277 = 47 +
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
  rw [recurrence2Scalar4Shift_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_276_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (277 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 135,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (277 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_277 :
    recurrence2Scalar4Shift.coeff 277 =
      (((2309507331610841722234484090654944648087484621465063329267464 * 10 ^ 70 +
        4112854293674488188063065950574537638601206433065040576845035095271916) * 10 ^ 70 +
        2319437545797492418832869518302676803888326665871369549073304140001219) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 278 = 48 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 31 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_277_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (278 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 136,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (278 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_278 :
    recurrence2Scalar4Shift.coeff 278 =
      -(((640542371751855846637919977144976319554836807853997478210372 * 10 ^ 70 +
        1954121447888525507247629160383222542264880216032969442882319137851619) * 10 ^ 70 +
        5934394092478481324862935727302434066431541051960853929135435235873976) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 279 = 49 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 30 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_278_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (279 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 137,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (279 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_279 :
    recurrence2Scalar4Shift.coeff 279 =
      (((149541685491664366139491047735279726342239108688596593110420 * 10 ^ 70 +
        2340309096584191567041193160190054877789593737113045249381785336978728) * 10 ^ 70 +
        0774266259885809492564357890793764319703874167172320624086674592542874) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 280 = 50 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 29 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_279_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (280 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 138,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (280 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_280 :
    recurrence2Scalar4Shift.coeff 280 =
      -(((24721753304055674262132791706509734221821911960081253758382 * 10 ^ 70 +
        4896630243846070605734143793579114054594604591534369852028849606728401) * 10 ^ 70 +
        3541515301370114888852724466035699816295936995082177731901771240903034) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 281 = 51 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 28 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_280_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (281 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 139,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (281 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_281 :
    recurrence2Scalar4Shift.coeff 281 =
      -(((93353788642221593534207235156270968814871894967637860119 * 10 ^ 70 +
        1501858797527613852842008638893921548567729800987592787783991453852722) * 10 ^ 70 +
        9685230962388684002171924813449406153718816468625799916273521032378374) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 282 = 52 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 27 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_281_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 53,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (282 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 140,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (282 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_282 :
    recurrence2Scalar4Shift.coeff 282 =
      (((2374153773533081190883377524803047795228867321398567290301 * 10 ^ 70 +
        7223273422128670029549335154554861654552641503566113384550866407228910) * 10 ^ 70 +
        1933890474355440771082328368769177839376613695731606322182439871121167) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 283 = 53 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 26 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_282_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 54,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (283 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 141,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (283 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_283 :
    recurrence2Scalar4Shift.coeff 283 =
      -(((1324248440869642633846259144751523237133691118847651378140 * 10 ^ 70 +
        9937436191281376148638020636612066946704728073209232399170881694452297) * 10 ^ 70 +
        1314020126885904054592074637490234468961548447325947518830755739333515) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 284 = 54 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 25 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_283_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 55,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (284 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 142,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (284 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_284 :
    recurrence2Scalar4Shift.coeff 284 =
      (((521467053667239320636310927873658236352777045942220730721 * 10 ^ 70 +
        4805467759025402583098844218536356761539117397370000341269282101296227) * 10 ^ 70 +
        4911865956715945600460189133777005243052012077720889172993924029242303) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 285 = 55 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 24 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_284_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 56,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (285 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 143,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (285 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_285 :
    recurrence2Scalar4Shift.coeff 285 =
      -(((170033781571061891369788368993081871018933632755457361756 * 10 ^ 70 +
        7476031524590697763671404778101921279458817953378708048561403910104858) * 10 ^ 70 +
        9935329271160553118638974963684580670633575025991716735984545523587636) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 286 = 56 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 23 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_285_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 57,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (286 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 144,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (286 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_286 :
    recurrence2Scalar4Shift.coeff 286 =
      (((47804985698350432143620582090153662083514247115363661213 * 10 ^ 70 +
        0983010907936660541048575175915185088171162951905937204596382647176517) * 10 ^ 70 +
        5523458875861683947284845716209670077706246441451685672821332440047018) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 287 = 57 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 22 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_286_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 58,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (287 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 145,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (287 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_287 :
    recurrence2Scalar4Shift.coeff 287 =
      -(((11610623487594542566850269332577016082763804985104121087 * 10 ^ 70 +
        0856813980181974325427888497678482548587504990399802704134077975985870) * 10 ^ 70 +
        2438132941288883489403131443969250070056607616913406122633205397747448) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 288 = 58 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 21 +
      145 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_287_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 59,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (288 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 146,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (288 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_288 :
    recurrence2Scalar4Shift.coeff 288 =
      (((2358318638391241228220001927173380893496454021175569772 * 10 ^ 70 +
        3069087203630121530659640744420265685487686300578808588188542997367033) * 10 ^ 70 +
        4754625744501346990989801346957181631159588990161140750473098865035151) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 289 = 59 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 20 +
      146 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_288_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 60,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (289 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 147,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (289 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_289 :
    recurrence2Scalar4Shift.coeff 289 =
      -(((355963233603097422240414984865968605635005985522852587 * 10 ^ 70 +
        1918264087845982813003455396225439591076320515847340903931927118783250) * 10 ^ 70 +
        0429392535517489567685868029447864852893724783979389187871923438584973) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 290 = 60 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 19 +
      147 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_289_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 61,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (290 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 148,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (290 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_290 :
    recurrence2Scalar4Shift.coeff 290 =
      (((17128136702190546193812232750803888597058964690076500 * 10 ^ 70 +
        3315231755348792552854977063696284525208452153101549934096977938685418) * 10 ^ 70 +
        3133012583053420457485856361198693025459153413418051896186736431753914) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 291 = 61 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 18 +
      148 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_290_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 62,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (291 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 149,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (291 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_291 :
    recurrence2Scalar4Shift.coeff 291 =
      (((13337154653081201044237715110814295511858452334153668 * 10 ^ 70 +
        3978861381051106708450101577605586740451934096559872440492921186740530) * 10 ^ 70 +
        1911676389043525762217431279900721467560148214715543369840947387396685) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 292 = 62 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 17 +
      149 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_291_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 63,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (292 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 150,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (292 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_292 :
    recurrence2Scalar4Shift.coeff 292 =
      -(((6743424852778523331417008004635843218348038282555573 * 10 ^ 70 +
        3585150357806781630214649792031792863358328108106093085297938506129987) * 10 ^ 70 +
        7449967970514857947040559544539205764941791535171845445703527872308109) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 293 = 63 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 16 +
      150 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_292_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 64,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (293 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 151,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (293 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_293 :
    recurrence2Scalar4Shift.coeff 293 =
      (((2133390281255526967903273141897676725378565902776207 * 10 ^ 70 +
        0169129921598421020742772705040203452994044387096087563777058492766665) * 10 ^ 70 +
        3628731385726895156606482046404119190885702796896937007629910293865443) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 294 = 64 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 15 +
      151 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_293_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 65,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (294 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 152,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (294 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_294 :
    recurrence2Scalar4Shift.coeff 294 =
      -(((533601317594521033399574886313294258272818709544665 * 10 ^ 70 +
        4763348999418786273042715223800336800453358976735491548122477173535555) * 10 ^ 70 +
        1893676924844330531760335829989316461072530273250349813179210498736481) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 295 = 65 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 14 +
      152 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_294_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 66,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (295 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 153,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (295 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_295 :
    recurrence2Scalar4Shift.coeff 295 =
      (((110258756366130742668107103846923487846573173975924 * 10 ^ 70 +
        0157772419561042986523617597847884526134287658074100584482233408642718) * 10 ^ 70 +
        6815956096360475383301790230472524782209494874170007756079219298817832) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 296 = 66 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 13 +
      153 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_295_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 67,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (296 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 154,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (296 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_296 :
    recurrence2Scalar4Shift.coeff 296 =
      -(((18420645399584009482243711836036032609794699916876 * 10 ^ 70 +
        7307373514496663735814036860931034233255218221803473385010688976949978) * 10 ^ 70 +
        5490077707359664270227604491746348081097732570801203167050825995441985) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 297 = 67 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 12 +
      154 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_296_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 68,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (297 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 155,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (297 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_297 :
    recurrence2Scalar4Shift.coeff 297 =
      (((2179422365886486134348317089949227245450650318752 * 10 ^ 70 +
        1628362229848749923007235250439825172357353410815488889596698190389219) * 10 ^ 70 +
        0550961675577297055912966787239460583031766098607418930088458403738219) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 298 = 68 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 11 +
      155 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_297_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 69,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (298 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 156,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (298 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_298 :
    recurrence2Scalar4Shift.coeff 298 =
      -(((45633366001094955902410162417243649728610998057 * 10 ^ 70 +
        8440954596743643445502450317029396707049804677740304822190385144370467) * 10 ^ 70 +
        5846638701571275029386081062097203456427734398680947440861146496519945) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 299 = 69 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 10 +
      156 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_298_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 70,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (299 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 157,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (299 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_299 :
    recurrence2Scalar4Shift.coeff 299 =
      -(((67674409684653836291896309403445112984741030582 * 10 ^ 70 +
        1921617213562958342332703545563354148067526433365893589122859614418329) * 10 ^ 70 +
        6873101165429969258838803835027208908925261118504505661268110385681785) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 300 = 70 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 9 +
      157 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_299_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 71,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (300 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 158,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (300 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_300 :
    recurrence2Scalar4Shift.coeff 300 =
      (((24939193210780447497604447045624329433138664328 * 10 ^ 70 +
        1946880070531197042162116907585174619179238435680999450856677752721438) * 10 ^ 70 +
        4322404234245670409619666464677086186627555534583185924875011464892876) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 301 = 71 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 8 +
      158 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_300_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 72,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (301 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 159,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (301 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_301 :
    recurrence2Scalar4Shift.coeff 301 =
      -(((6011611110526513660149756794669875186553443717 * 10 ^ 70 +
        2463278037830452037888053400343296824601046231888173329674936019274222) * 10 ^ 70 +
        6950506114746177319470775668364787428713564663033029205517544443363008) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 302 = 72 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 7 +
      159 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_301_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 73,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (302 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 160,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (302 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_302 :
    recurrence2Scalar4Shift.coeff 302 =
      (((1145290374869774145947921199709782022380267077 * 10 ^ 70 +
        0934923568222825979606178110130406978759448936263188514314331575256367) * 10 ^ 70 +
        9459604681573714839260244676598853457518514048812730868385016329124528) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 303 = 73 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 6 +
      160 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_302_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 74,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (303 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 161,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (303 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_303 :
    recurrence2Scalar4Shift.coeff 303 =
      -(((178591451315305569246247780964111604195777270 * 10 ^ 70 +
        5886939635283527748421763538422558816172479062132406394608299870673877) * 10 ^ 70 +
        0492899267973111647791649124515164765450530980291280783942491564772236) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 304 = 74 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 5 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_303_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (304 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 162,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (304 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_304 :
    recurrence2Scalar4Shift.coeff 304 =
      (((22169980683515453382366054960806258559928575 * 10 ^ 70 +
        8734159627248979146249099733385903191683521230444654699244593709389148) * 10 ^ 70 +
        7804608782876022105190700577355603447304706402970934308318924082279873) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 305 = 75 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 4 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_304_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (305 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 163,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (305 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_305 :
    recurrence2Scalar4Shift.coeff 305 =
      -(((1885826539433721509329173026109540052979632 * 10 ^ 70 +
        8007137196034569212938985913077847176929508487014351589134714569611615) * 10 ^ 70 +
        4080196730389428883757428998174790615945562308250624399260136978144663) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 306 = 76 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 3 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_305_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (306 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 164,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (306 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_306 :
    recurrence2Scalar4Shift.coeff 306 =
      (((11057244888595468090508373753914321925849 * 10 ^ 70 +
        4400394684741926874902748788038876713172759858531426568280266908675479) * 10 ^ 70 +
        3515582605772660496188212021101020428460225393571635132163747613008047) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 307 = 77 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 2 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_306_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (307 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 165,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (307 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_307 :
    recurrence2Scalar4Shift.coeff 307 =
      (((35819195749819141432660950100646018688330 * 10 ^ 70 +
        5532897623216876870818739700521647890905388716032047956385290962196848) * 10 ^ 70 +
        5283825094639016200169451625634081998629649840484125822868990301475588) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 308 = 78 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 1 +
      165 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_307_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (308 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 166,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (308 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_308 :
    recurrence2Scalar4Shift.coeff 308 =
      -(((8965085383093432793310991101121250128856 * 10 ^ 70 +
        8736989066675764488102073577095850239430758891324141495338978398845404) * 10 ^ 70 +
        9177365189549922912470210643096471085584430939794727051569998973139895) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 309 = 79 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_308_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (309 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 167,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (309 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_309 :
    recurrence2Scalar4Shift.coeff 309 =
      (((1473282450604524928764385991055865511218 * 10 ^ 70 +
        1577039041959032495940881925250354999101389821381031689722589254255762) * 10 ^ 70 +
        2961241043627054358231650338268351530041219120986842899257435108205245) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 310 = 80 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 31 +
      167 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_309_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (310 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 168,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (310 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_310 :
    recurrence2Scalar4Shift.coeff 310 =
      -(((186135465818924786925727348050945658900 * 10 ^ 70 +
        6544425830825438405675642881922815129650930230982245701521795357746182) * 10 ^ 70 +
        8385859760238495698631791384437695228460182960856862069468923588427158) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 311 = 81 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 30 +
      168 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_310_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (311 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 169,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (311 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_311 :
    recurrence2Scalar4Shift.coeff 311 =
      (((18213434735494388941087991994578891374 * 10 ^ 70 +
        8249101930275196559980316099738430151248251663460744244996827950676624) * 10 ^ 70 +
        3641078307536674966780275780409591682604137480323100128783107943413885) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 312 = 82 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 29 +
      169 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_311_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (312 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 170,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (312 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_312 :
    recurrence2Scalar4Shift.coeff 312 =
      -(((1236119533976088127498582460779464127 * 10 ^ 70 +
        1981335205935901657309684407548749900858296568590791568046164810178945) * 10 ^ 70 +
        4274779012907006610356706361916236195285723371961696454129262981766763) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 313 = 83 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 28 +
      170 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_312_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (313 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 171,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (313 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_313 :
    recurrence2Scalar4Shift.coeff 313 =
      (((21950055095868905594382465243356709 * 10 ^ 70 +
        4586362036948190055061613570459957693925407104582089977826152431382513) * 10 ^ 70 +
        1088169086940167733774942427607370361562182002398861752236531118328380) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 314 = 84 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 27 +
      171 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_313_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (314 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 172,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (314 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_314 :
    recurrence2Scalar4Shift.coeff 314 =
      (((8894563880452419676089106850015975 * 10 ^ 70 +
        0600628313029610826000871765820254461106534505891408968593217683241415) * 10 ^ 70 +
        4878972364355874481698794664101672992326424122135392473094728802954728) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 315 = 85 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 26 +
      172 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_314_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (315 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 173,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (315 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_315 :
    recurrence2Scalar4Shift.coeff 315 =
      -(((1676022483341003611333383912977050 * 10 ^ 70 +
        8160378656705522712981487238258957676964055399281275453874490354484212) * 10 ^ 70 +
        8202553190787977662999755150453809643910951982266913827204566777324592) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 316 = 86 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 25 +
      173 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_315_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (316 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 174,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (316 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_316 :
    recurrence2Scalar4Shift.coeff 316 =
      (((186845502115647990724023934667057 * 10 ^ 70 +
        6462561428452043828636831377088766518355280625131423191944824877180600) * 10 ^ 70 +
        8707404475187622463810909620402209711141335417859943013171130945770001) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 317 = 87 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 24 +
      174 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_316_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (317 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 175,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (317 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_317 :
    recurrence2Scalar4Shift.coeff 317 =
      -(((14833999417213202349570281797353 * 10 ^ 70 +
        1274201553187001403323477528684133278783365207994415206249527970168729) * 10 ^ 70 +
        4869410503747493942931324313270524189005922853129979162996655834532255) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 318 = 88 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 23 +
      175 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_317_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (318 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 176,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (318 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_318 :
    recurrence2Scalar4Shift.coeff 318 =
      (((794818589538113363714110850006 * 10 ^ 70 +
        8538555380483115635388135997909310663310801575007562078627372982987190) * 10 ^ 70 +
        2429041645758023009376207982017378015290600479584221567141089476221519) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 319 = 89 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 22 +
      176 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_318_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (319 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 177,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (319 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_319 :
    recurrence2Scalar4Shift.coeff 319 =
      -(((15122366422211861040830262797 * 10 ^ 70 +
        4302007772414043778299835625283008192345158022851557240439983915481537) * 10 ^ 70 +
        9491885803271156255567532371363290929458174891076551058670399218593023) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 320 = 90 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 21 +
      177 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_319_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (320 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 178,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (320 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_320 :
    recurrence2Scalar4Shift.coeff 320 =
      -(((2225366037047929959986202952 * 10 ^ 70 +
        6210993403409932743712364791853640759723803746816284727712683921617984) * 10 ^ 70 +
        4642636705986367336957397282554813402307592919078522047374602797622135) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 321 = 91 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 20 +
      178 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_320_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (321 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 179,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (321 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_321 :
    recurrence2Scalar4Shift.coeff 321 =
      (((305451495797320627408452692 * 10 ^ 70 +
        0663838879895611431857033339489627118897276033371584202236046577800907) * 10 ^ 70 +
        9680791153626665220715107378209878798238201455141561847673851572957919) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 322 = 92 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 19 +
      179 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_321_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (322 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 180,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (322 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_322 :
    recurrence2Scalar4Shift.coeff 322 =
      -(((21740552965139200008651689 * 10 ^ 70 +
        3923429433448601914537405394268996929981872486733009282831069877881833) * 10 ^ 70 +
        9921817705047710822991183449015142403142944636909969443096996818117894) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 323 = 93 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 18 +
      180 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_322_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (323 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 181,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (323 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_323 :
    recurrence2Scalar4Shift.coeff 323 =
      (((967180525808139614917594 * 10 ^ 70 +
        1800057486971414325270454092381910707895588910136284655778836387563773) * 10 ^ 70 +
        1001255536631308867289207147677936180666335402095700293574608616031849) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 324 = 94 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 17 +
      181 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_323_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (324 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 182,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (324 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_324 :
    recurrence2Scalar4Shift.coeff 324 =
      -(((18842427101357941343196 * 10 ^ 70 +
        3547928244509460039930248327046630625719397181702544921516367626081014) * 10 ^ 70 +
        0005278353517716714348634981849475717206231988719113283222573687256030) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 325 = 95 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 16 +
      182 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_324_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 96,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (325 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 183,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (325 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_325 :
    recurrence2Scalar4Shift.coeff 325 =
      -(((887107056760758530464 * 10 ^ 70 +
        2870245635797301492237285375390808898083428901098890592392900822450148) * 10 ^ 70 +
        8199705927616653175237375352015941938504674894841879464746851179430609) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 326 = 96 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 15 +
      183 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_325_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 97,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (326 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 184,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (326 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_326 :
    recurrence2Scalar4Shift.coeff 326 =
      (((96731116432805337857 * 10 ^ 70 +
        1030264477598055137850434012187012521474709194607035343398983325060840) * 10 ^ 70 +
        1499127228550021149576633395446653614706230020708565142004392154361852) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 327 = 97 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 14 +
      184 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_326_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 98,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (327 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 185,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (327 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_327 :
    recurrence2Scalar4Shift.coeff 327 =
      -(((4297382788160724339 * 10 ^ 70 +
        8574716297939116502477232396571559610047408335075769009010673791978802) * 10 ^ 70 +
        0163094591965042213743469951692551926505967737097706890185103798646637) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 328 = 98 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 13 +
      185 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_327_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (328 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 186,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (328 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_328 :
    recurrence2Scalar4Shift.coeff 328 =
      (((94762487626908762 * 10 ^ 70 +
        1837280876470010059609681128866265190070500912355967566917120569115879) * 10 ^ 70 +
        0154379303913442470615113372120749483269263839555413268568522189118093) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 329 = 99 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 12 +
      186 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_328_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (329 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 187,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (329 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_329 :
    recurrence2Scalar4Shift.coeff 329 =
      (((392137868862818 * 10 ^ 70 +
        8075014458538778057976973824063482855951254765447450638875346435891851) * 10 ^ 70 +
        0694912840059164120618977447732929580090653561231941048998217341228550) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 330 = 100 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 11 +
      187 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_329_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (330 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 188,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (330 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_330 :
    recurrence2Scalar4Shift.coeff 330 =
      -(((100600563589410 * 10 ^ 70 +
        2131550592102984041130362540286315428325441888867885974053560976903428) * 10 ^ 70 +
        2499891113850143309000423870727585484868110810038483154654104112497960) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 331 = 101 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 10 +
      188 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_330_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (331 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 189,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (331 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_331 :
    recurrence2Scalar4Shift.coeff 331 =
      (((3192449178508 * 10 ^ 70 +
        8455314463870412907949482967471394528866738342949318096564379229956703) * 10 ^ 70 +
        1725955828328306637224337864312601477395446088603856115412696503530482) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 332 = 102 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 9 +
      189 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_331_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (332 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 190,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (332 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_332 :
    recurrence2Scalar4Shift.coeff 332 =
      -(((37191253039 * 10 ^ 70 +
        1218777068301382413604259159648695116212334314463511469055441534205146) * 10 ^ 70 +
        3610016107105746392595927410078841607549603230413890965563788065048126) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 333 = 103 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 8 +
      190 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_332_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (333 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 191,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (333 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_333 :
    recurrence2Scalar4Shift.coeff 333 =
      -(((471626477 * 10 ^ 70 +
        1173670196184783179230875359865773957724940615301437832006249249639096) * 10 ^ 70 +
        2994632864353203656018659109685912735461034103966867764171902807171490) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 334 = 104 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 7 +
      191 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_333_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 105,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (334 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 192,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (334 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_334 :
    recurrence2Scalar4Shift.coeff 334 =
      (((21724136 * 10 ^ 70 +
        1084561810039582667699531298832286784163887481111813884259337423001004) * 10 ^ 70 +
        3211220598967295939668327028769389368491371390899754949774923922150475) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 335 = 105 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 6 +
      192 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_334_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 106,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (335 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 193,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (335 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_335 :
    recurrence2Scalar4Shift.coeff 335 =
      -(((231361 * 10 ^ 70 +
        2737702089164082387422686230484202661674095125480011545157126523073092) * 10 ^ 70 +
        0257429742028394636526164177734695495202516747533635651254780988907691) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 336 = 106 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 5 +
      193 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_335_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 107,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (336 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 194,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (336 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_336 :
    recurrence2Scalar4Shift.coeff 336 =
      -(((1183 * 10 ^ 70 +
        6038779030765461092120236733549054297442059877425177465420044073143070) * 10 ^ 70 +
        3653834300390366362893559461740654354259565504473549800856473587102137) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 337 = 107 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 4 +
      194 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_336_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 108,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (337 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 195,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (337 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_337 :
    recurrence2Scalar4Shift.coeff 337 =
      (((44 * 10 ^ 70 +
        7974700795508891559924017591120903058616666673176128237180014350411785) * 10 ^ 70 +
        6962556387932237128526947706260126388372481534527637623329242126714086) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 338 = 108 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 3 +
      195 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_337_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 109,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (338 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 196,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (338 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_338 :
    recurrence2Scalar4Shift.coeff 338 =
      -((2010467790918751426729790995261767781648617484617133623608961485912887 * 10 ^ 70 +
        1065843207797227528078858261732212907155126035431764754653048603995892) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 339 = 109 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 2 +
      196 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_338_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 110,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (339 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 197,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (339 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_339 :
    recurrence2Scalar4Shift.coeff 339 =
      -((27092778422582420047159761510933363761037050688026834623100314227367 * 10 ^ 70 +
        5574387381802305450011018982781919704224466667361928134489444531913975) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 340 = 110 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 1 +
      197 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_339_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 111,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (340 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 198,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (340 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_340 :
    recurrence2Scalar4Shift.coeff 340 =
      ((247959936107936939307679625782472485632802634947089552306177528434 * 10 ^ 70 +
        3636009895967931174421668751798404766993982455953955445258679658048355) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 341 = 111 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_340_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 112,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (341 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 199,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (341 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_341 :
    recurrence2Scalar4Shift.coeff 341 =
      ((618835728075804100613972608294658829827582333843923604103227197 * 10 ^ 70 +
        2786761437402599834969872485567029364495375964864809000160065959628326) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 342 = 112 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 31 +
      199 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_341_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 113,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (342 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 200,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (342 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_342 :
    recurrence2Scalar4Shift.coeff 342 =
      -((11598300852757111695840754218323022410794466075317594412777341 * 10 ^ 70 +
        9639094240452553579272608332762223991115348100702554367401446808016201) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 343 = 113 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 30 +
      200 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_342_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 114,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (343 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 201,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (343 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_343 :
    recurrence2Scalar4Shift.coeff 343 =
      ((2875066744423741979729697407300131890626806150036686536917 * 10 ^ 70 +
        4548100747363058597941327174657738744596252974043229452837551614497859) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 344 = 114 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 29 +
      201 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_343_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 115,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (344 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 202,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (344 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_344 :
    recurrence2Scalar4Shift.coeff 344 =
      ((284381655395112861651212376068202827284203894702257565290 * 10 ^ 70 +
        5909402931790571569643857869658576193284576857775408512282073372969113) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 345 = 115 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 28 +
      202 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_344_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 116,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (345 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 203,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (345 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_345 :
    recurrence2Scalar4Shift.coeff 345 =
      -((454039281333182902959921428956202761078083987681677960 * 10 ^ 70 +
        0766966338618364599421151963312829175698302246252415143008632196952719) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 346 = 116 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 27 +
      203 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_345_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 117,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (346 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 204,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (346 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_346 :
    recurrence2Scalar4Shift.coeff 346 =
      -((3780698635482209521730229938963839537139581441734822 * 10 ^ 70 +
        3475311676100368779966431395795106624430555587048962098821844136615446) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 347 = 117 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 26 +
      204 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_346_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 118,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (347 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 205,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (347 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_347 :
    recurrence2Scalar4Shift.coeff 347 =
      ((10115929511026028008669692567667567154965374757942 * 10 ^ 70 +
        2500185753192574891842217237818739831832182169982387275589669359379144) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 348 = 118 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 25 +
      205 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_347_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 119,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (348 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 206,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (348 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_348 :
    recurrence2Scalar4Shift.coeff 348 =
      ((23559574505245762064031491001932721059084166296 * 10 ^ 70 +
        6586881104198056868617813137297140263127971062429267334309426185019926) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 349 = 119 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 24 +
      206 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_348_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 120,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (349 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 207,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (349 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_349 :
    recurrence2Scalar4Shift.coeff 349 =
      -((103576290948433649557071332409530523290073653 * 10 ^ 70 +
        3149467318652046159738832609937650034520567653627765928224036322187053) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 350 = 120 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 23 +
      207 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_349_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 121,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (350 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 208,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (350 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_350 :
    recurrence2Scalar4Shift.coeff 350 =
      -((8086055618844147231222349710362810745101 * 10 ^ 70 +
        1101329120200674163353302787910482989486021497395919499459184803514733) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 351 = 121 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 22 +
      208 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_350_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 122,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (351 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 209,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (351 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_351 :
    recurrence2Scalar4Shift.coeff 351 =
      ((465934593345737040056523684251097239237 * 10 ^ 70 +
        5109603463771844490609734519916934683486334896293063485440314058185629) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 352 = 122 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 21 +
      209 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_351_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 123,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (352 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 210,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (352 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_352 :
    recurrence2Scalar4Shift.coeff 352 =
      -((556714190925077326658241931318099256 * 10 ^ 70 +
        1294662942511547319505248529550527120141843794489460152472481469711946) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 353 = 123 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 20 +
      210 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_352_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 124,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (353 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 211,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (353 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_353 :
    recurrence2Scalar4Shift.coeff 353 =
      -((415641514637554953632228189316712 * 10 ^ 70 +
        1525725510547686573990243342696652134544092294612890968312526861149817) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 354 = 124 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 19 +
      211 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_353_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 125,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (354 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 212,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (354 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_354 :
    recurrence2Scalar4Shift.coeff 354 =
      ((1381134611657920292946349554409 * 10 ^ 70 +
        9128527915755355546407125267973531664695406052693634669853042867915302) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 355 = 125 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 18 +
      212 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_354_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 126,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (355 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 213,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (355 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_355 :
    recurrence2Scalar4Shift.coeff 355 =
      -((1035458519562533605323550195 * 10 ^ 70 +
        0052945530824791196701600906371440942343328892954426099903843773396909) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 356 = 126 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 17 +
      213 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_355_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 127,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (356 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 214,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (356 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_356 :
    recurrence2Scalar4Shift.coeff 356 =
      ((126969085097512940435577 * 10 ^ 70 +
        7381194753741331249604520660220894818378075284911667154254206195858411) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 357 = 127 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 16 +
      214 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_356_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 128,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (357 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 215,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (357 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_357 :
    recurrence2Scalar4Shift.coeff 357 =
      ((200869479597590441791 * 10 ^ 70 +
        9842103009744752091730672480573547461334902360004324233027311327995621) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 358 = 128 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 15 +
      215 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_357_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 129,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (358 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 216,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (358 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_358 :
    recurrence2Scalar4Shift.coeff 358 =
      -((102176227958694794 * 10 ^ 70 +
        5030246422355805660218404670348893320745767548225522565114784062458404) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 359 = 129 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 14 +
      216 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_358_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 130,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (359 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 217,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (359 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_359 :
    recurrence2Scalar4Shift.coeff 359 =
      ((17548329687178 * 10 ^ 70 +
        2955876025588938208083341272751709999790880307712356054609927730214369) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 360 = 130 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 13 +
      217 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_359_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 131,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (360 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 218,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (360 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_360 :
    recurrence2Scalar4Shift.coeff 360 =
      -((775566030 * 10 ^ 70 +
        6825608765542152552442704788561924043137876300102087064210664905657749) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 361 = 131 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 12 +
      218 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_360_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 132,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (361 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 219,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (361 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_361 :
    recurrence2Scalar4Shift.coeff 361 =
      -((72920 * 10 ^ 70 +
        8871713154925273142135964819313275041854953678858166995470308829303318) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 362 = 132 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 11 +
      219 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_361_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 133,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (362 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 220,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (362 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_362 :
    recurrence2Scalar4Shift.coeff 362 =
      ((6 * 10 ^ 70 +
        9576877640293435378780492167696296671680409095037518483307451232140058) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 363 = 133 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 10 +
      220 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_362_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 134,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (363 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 221,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (363 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_363 :
    recurrence2Scalar4Shift.coeff 363 =
      (-1729487505835721023550281411828590233472618139591610260476389913538 : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 364 = 134 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 9 +
      221 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_363_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 135,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (364 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 222,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (364 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_364 :
    recurrence2Scalar4Shift.coeff 364 =
      (11765337416034971224239694908216163863006796098191927987095020 : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 365 = 135 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 8 +
      222 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_364_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 136,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (365 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 223,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (365 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_365 :
    recurrence2Scalar4Shift.coeff 365 =
      (2429241908114965881865045257488899255784823183414966212 : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 366 = 136 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 7 +
      223 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_365_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 137,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (366 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 224,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (366 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_366 :
    recurrence2Scalar4Shift.coeff 366 =
      (-147601561346633531636556224107195142301589948520950 : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 367 = 137 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 6 +
      224 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_366_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 138,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (367 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 225,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (367 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_367 :
    recurrence2Scalar4Shift.coeff 367 =
      (146974715066711393874212455567930456804063324 : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 368 = 138 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 5 +
      225 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_367_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 139,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (368 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 226,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (368 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_368 :
    recurrence2Scalar4Shift.coeff 368 =
      (-29743089731242579360093948914621621102 : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 369 = 139 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 4 +
      226 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_368_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 140,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (369 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 227,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (369 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_369 :
    recurrence2Scalar4Shift.coeff 369 =
      (194811858269633467930311356394 : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 370 = 140 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 3 +
      227 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_369_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 141,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (370 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 228,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (370 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_370 :
    recurrence2Scalar4Shift.coeff 370 =
      (83858415682923613950 : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 371 = 141 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 2 +
      228 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_370_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 142,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (371 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 229,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (371 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_371 :
    recurrence2Scalar4Shift.coeff 371 =
      (-479004608307 : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 372 = 142 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 1 +
      229 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_371_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
