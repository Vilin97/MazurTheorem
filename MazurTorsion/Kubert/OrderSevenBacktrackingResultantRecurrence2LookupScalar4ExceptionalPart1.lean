/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupExceptionalProduct
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupC4
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar4Exceptional coefficient convolution

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
  recurrence2C4_coeff_0
  recurrence2C4_coeff_1
  recurrence2C4_coeff_2
  recurrence2C4_coeff_3
  recurrence2C4_coeff_4
  recurrence2C4_coeff_5
  recurrence2C4_coeff_6
  recurrence2C4_coeff_7
  recurrence2C4_coeff_8
  recurrence2C4_coeff_9
  recurrence2C4_coeff_10
  recurrence2C4_coeff_11
  recurrence2C4_coeff_12
  recurrence2C4_coeff_13
  recurrence2C4_coeff_14
  recurrence2C4_coeff_15
  recurrence2C4_coeff_16
  recurrence2C4_coeff_17
  recurrence2C4_coeff_18
  recurrence2C4_coeff_19
  recurrence2C4_coeff_20
  recurrence2C4_coeff_21
  recurrence2C4_coeff_22
  recurrence2C4_coeff_23
  recurrence2C4_coeff_24
  recurrence2C4_coeff_25
  recurrence2C4_coeff_26
  recurrence2C4_coeff_27
  recurrence2C4_coeff_28
  recurrence2C4_coeff_29
  recurrence2C4_coeff_30
  recurrence2C4_coeff_31
  recurrence2C4_coeff_32
  recurrence2C4_coeff_33
  recurrence2C4_coeff_34
  recurrence2C4_coeff_35
  recurrence2C4_coeff_36
  recurrence2C4_coeff_37
  recurrence2C4_coeff_38
  recurrence2C4_coeff_39
  recurrence2C4_coeff_40
  recurrence2C4_coeff_41
  recurrence2C4_coeff_42
  recurrence2C4_coeff_43
  recurrence2C4_coeff_44
  recurrence2C4_coeff_45
  recurrence2C4_coeff_46
  recurrence2C4_coeff_47
  recurrence2C4_coeff_48
  recurrence2C4_coeff_49
  recurrence2C4_coeff_50
  recurrence2C4_coeff_51
  recurrence2C4_coeff_52
  recurrence2C4_coeff_53
  recurrence2C4_coeff_54
  recurrence2C4_coeff_55
  recurrence2C4_coeff_56
  recurrence2C4_coeff_57
  recurrence2C4_coeff_58
  recurrence2C4_coeff_59
  recurrence2C4_coeff_60
  recurrence2C4_coeff_61
  recurrence2C4_coeff_62
  recurrence2C4_coeff_63
  recurrence2C4_coeff_64
  recurrence2C4_coeff_65
  recurrence2C4_coeff_66
  recurrence2C4_coeff_67
  recurrence2C4_coeff_68
  recurrence2C4_coeff_69
  recurrence2C4_coeff_70
  recurrence2C4_coeff_71
  recurrence2C4_coeff_72
  recurrence2C4_coeff_73
  recurrence2C4_coeff_74
  recurrence2C4_coeff_75
  recurrence2C4_coeff_76
  recurrence2C4_coeff_77
  recurrence2C4_coeff_78
  recurrence2C4_coeff_79
  recurrence2C4_coeff_80
  recurrence2C4_coeff_81
  recurrence2C4_coeff_82
  recurrence2C4_coeff_83
  recurrence2C4_coeff_84
  recurrence2C4_coeff_85
  recurrence2C4_coeff_86
  recurrence2C4_coeff_87
  recurrence2C4_coeff_88
  recurrence2C4_coeff_89
  recurrence2C4_coeff_90
  recurrence2C4_coeff_91
  recurrence2C4_coeff_92
  recurrence2C4_coeff_93
  recurrence2C4_coeff_94
  recurrence2C4_coeff_95
  recurrence2C4_coeff_96
  recurrence2C4_coeff_97
  recurrence2C4_coeff_98
  recurrence2C4_coeff_99
  recurrence2C4_coeff_100
  recurrence2C4_coeff_101
  recurrence2C4_coeff_102
  recurrence2C4_coeff_103
  recurrence2C4_coeff_104
  recurrence2C4_coeff_105
  recurrence2C4_coeff_106
  recurrence2C4_coeff_107
  recurrence2C4_coeff_108
  recurrence2C4_coeff_109
  recurrence2C4_coeff_110
  recurrence2C4_coeff_111
  recurrence2C4_coeff_112
  recurrence2C4_coeff_113
  recurrence2C4_coeff_114
  recurrence2C4_coeff_115
  recurrence2C4_coeff_116
  recurrence2C4_coeff_117
  recurrence2C4_coeff_118
  recurrence2C4_coeff_119
  recurrence2C4_coeff_120
  recurrence2C4_coeff_121
  recurrence2C4_coeff_122
  recurrence2C4_coeff_123
  recurrence2C4_coeff_124
  recurrence2C4_coeff_125
  recurrence2C4_coeff_126
  recurrence2C4_coeff_127
  recurrence2C4_coeff_128
  recurrence2C4_coeff_129
  recurrence2C4_coeff_130
  recurrence2C4_coeff_131
  recurrence2C4_coeff_132
  recurrence2C4_coeff_133
  recurrence2C4_coeff_134
  recurrence2C4_coeff_135
  recurrence2C4_coeff_136
  recurrence2C4_coeff_137
  recurrence2C4_coeff_138
  recurrence2C4_coeff_139
  recurrence2C4_coeff_140
  recurrence2C4_coeff_141
  recurrence2C4_coeff_142
  recurrence2C4_coeff_143
  recurrence2C4_coeff_144
  recurrence2C4_coeff_145
  recurrence2C4_coeff_146
  recurrence2C4_coeff_147
  recurrence2C4_coeff_148
  recurrence2C4_coeff_149
  recurrence2C4_coeff_150
  recurrence2C4_coeff_151
  recurrence2C4_coeff_152
  recurrence2C4_coeff_153
  recurrence2C4_coeff_154
  recurrence2C4_coeff_155
  recurrence2C4_coeff_156
  recurrence2C4_coeff_157
  recurrence2C4_coeff_158
  recurrence2C4_coeff_159
  recurrence2C4_coeff_160
  recurrence2C4_coeff_161
  recurrence2C4_coeff_162
  recurrence2C4_coeff_163
  recurrence2C4_coeff_164
  recurrence2C4_coeff_165
  recurrence2C4_coeff_166
  recurrence2C4_coeff_167
  recurrence2C4_coeff_168
  recurrence2C4_coeff_169
  recurrence2C4_coeff_170
  recurrence2C4_coeff_171
  recurrence2C4_coeff_172
  recurrence2C4_coeff_173
  recurrence2C4_coeff_174
  recurrence2C4_coeff_175
  recurrence2C4_coeff_176
  recurrence2C4_coeff_177
  recurrence2C4_coeff_178

private theorem recurrence2Scalar4Exceptional_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (230 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (230 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_230 :
    recurrence2Scalar4Exceptional.coeff 230 =
      (((61018860610778648489795085654532544766265488821978954950 * 10 ^ 70 +
        8856290925379039232125584811256234353990024108909589737625005455968187) * 10 ^ 70 +
        6779941036796946402488885772187811318070156715553284057029157446005299) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 231 = 52 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 14 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_230_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_230_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (231 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (231 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_231 :
    recurrence2Scalar4Exceptional.coeff 231 =
      -(((371464117425536904282104240703699352818047457212708949055 * 10 ^ 70 +
        8892123812768181278255876947666581457071126352376780995427861286778115) * 10 ^ 70 +
        5695086199339554533356910422357134132789508192559069549720015683252560) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 232 = 53 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 13 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_231_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_231_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (232 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (232 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_232 :
    recurrence2Scalar4Exceptional.coeff 232 =
      (((453886887655759068117984671959655089791703252884800079056 * 10 ^ 70 +
        5239133289109243896815416455860326053676258862094038917658057524200869) * 10 ^ 70 +
        1714451987504763735761313349188218229742074416154389843364836967024756) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 233 = 54 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 12 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_232_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_232_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (233 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (233 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_233 :
    recurrence2Scalar4Exceptional.coeff 233 =
      -(((407203940182814923386669442563537413644965020445676283251 * 10 ^ 70 +
        9141656806640676021264083217494565272220015547385592506555637031760573) * 10 ^ 70 +
        5259010342063083705508238579491366989562785327959295475497828383617545) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 234 = 55 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 11 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_233_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_233_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (234 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (234 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_234 :
    recurrence2Scalar4Exceptional.coeff 234 =
      (((307112321324222999258654948725958882639293911247440306371 * 10 ^ 70 +
        0593063124751202171725222641457991351621479703614460019316363971963397) * 10 ^ 70 +
        4849029371182080711960048615743333062093264489109991178135946167565689) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 235 = 56 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 10 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_234_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_234_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (235 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (235 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_235 :
    recurrence2Scalar4Exceptional.coeff 235 =
      -(((201861610761031274441077481543412695781470929784042990731 * 10 ^ 70 +
        3196029878741548750663186186716211017153355878928804890601171616771372) * 10 ^ 70 +
        5207035209328243704295815887345192270460031968936386939941721757913047) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 236 = 57 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 9 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_235_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_235_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (236 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (236 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_236 :
    recurrence2Scalar4Exceptional.coeff 236 =
      (((115718636918376423615425395485022236058613470848090569899 * 10 ^ 70 +
        5639489344357128766700547358255955052332699877700835218640008640660334) * 10 ^ 70 +
        2168993603400073416797623960461393525729095158702005603941970939699378) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 237 = 58 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 8 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_236_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_236_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (237 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (237 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_237 :
    recurrence2Scalar4Exceptional.coeff 237 =
      -(((55967529228447182363130041766554571379880160876816014011 * 10 ^ 70 +
        9871789032007427027589022315088095708860110654551518774943998477144333) * 10 ^ 70 +
        6040225290679753381906219294789612246128563036389314634603570944534262) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 238 = 59 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 7 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_237_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_237_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (238 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (238 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_238 :
    recurrence2Scalar4Exceptional.coeff 238 =
      (((20209978365248572984399379894335009916284409380354195104 * 10 ^ 70 +
        2018648819985063570394819024451766482336690989265875298961698393236529) * 10 ^ 70 +
        2840519678971634562841573581782281964036154419127613570781129814977926) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 239 = 60 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 6 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_238_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_238_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (239 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (239 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_239 :
    recurrence2Scalar4Exceptional.coeff 239 =
      -(((2119332177187025278604433443105868621566704081941381307 * 10 ^ 70 +
        8091407355896048952337316727137082660410418288223077343881884410247300) * 10 ^ 70 +
        1913424368111334156489972949490709495332308726968632726410553830075799) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 240 = 61 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 5 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_239_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_239_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (240 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (240 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_240 :
    recurrence2Scalar4Exceptional.coeff 240 =
      -(((4941298009733338781489923055688980258843921806139156242 * 10 ^ 70 +
        8555115898793595455124963739304108346445996758942748147716988675946906) * 10 ^ 70 +
        2845766069383371426346163884967157550682067659597142861551929422596986) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 241 = 62 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 4 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_240_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_240_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (241 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (241 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_241 :
    recurrence2Scalar4Exceptional.coeff 241 =
      (((6200903793737560732783672547889057087084708744087021873 * 10 ^ 70 +
        2174666247854686125980214591181357694030495032608517012433081655783667) * 10 ^ 70 +
        5398305442499995572722928396665676218867389903205570700307794012895587) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 242 = 63 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 3 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_241_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_241_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (242 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (242 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_242 :
    recurrence2Scalar4Exceptional.coeff 242 =
      -(((5065001271122000847692563511346649267108787112739571281 * 10 ^ 70 +
        7582817059525463696368020622817697376634659331116851002654768329612278) * 10 ^ 70 +
        8844025688421084661141408713950839632970290162596279626186393691198307) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 243 = 64 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 2 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_242_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_242_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (243 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (243 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_243 :
    recurrence2Scalar4Exceptional.coeff 243 =
      (((3386241784222754003455129614898291860781332625291265139 * 10 ^ 70 +
        1171396489854476452494397834832529551895347678224192277523100748867229) * 10 ^ 70 +
        3271174967585986109174307962222911532648967659432528068698355936973258) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 244 = 65 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 1 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_243_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_243_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (244 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (244 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_244 :
    recurrence2Scalar4Exceptional.coeff 244 =
      -(((1962300206128876470987872811227947489427721573138775354 * 10 ^ 70 +
        8907938948272253584257933165502070091975662251802544458315331250536447) * 10 ^ 70 +
        9086167811601135709868409560498801316410050832151704012982204777309979) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 245 = 66 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_244_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_244_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (245 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (245 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_245 :
    recurrence2Scalar4Exceptional.coeff 245 =
      (((999828914770475479496653453589168103321690989640514325 * 10 ^ 70 +
        4924132906801461062411948344503855521905954330496102293451405660662934) * 10 ^ 70 +
        2156840886067549846362787904134296483107420392978273982756064795918175) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 246 = 67 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 31 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_245_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_245_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (246 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (246 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_246 :
    recurrence2Scalar4Exceptional.coeff 246 =
      -(((443112010898769754341633303365494566557725995674108343 * 10 ^ 70 +
        8564404164604148834315624269733902464817267760780957816504252689873650) * 10 ^ 70 +
        7210938182727684191640398214202138530309338726035082245830657524637830) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 247 = 68 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 30 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_246_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_246_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (247 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (247 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_247 :
    recurrence2Scalar4Exceptional.coeff 247 =
      (((162825423424902527964442092311802134521055822274690018 * 10 ^ 70 +
        9795379408853316015199253232978815153212563108618143913886538736905555) * 10 ^ 70 +
        1347922877590076021367321342343939843479217299402102167400906694889698) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 248 = 69 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 29 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_247_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_247_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (248 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (248 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_248 :
    recurrence2Scalar4Exceptional.coeff 248 =
      -(((41620402360185900816815005869275350511771590078932010 * 10 ^ 70 +
        9337895402615587877282243170255877641764821723315634620023557799874107) * 10 ^ 70 +
        9698313923191526049211570555588090544659625787105357410235515614157548) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 249 = 70 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 28 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_248_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_248_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (249 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (249 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_249 :
    recurrence2Scalar4Exceptional.coeff 249 =
      -(((747400406011332661575000223651873812351605414293910 * 10 ^ 70 +
        7752961113159913660957047174840859225634634950901075766146371478723194) * 10 ^ 70 +
        5104544331215203870952627626591440467639441184430548457655215501883076) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 250 = 71 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 27 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_249_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_249_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (250 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (250 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_250 :
    recurrence2Scalar4Exceptional.coeff 250 =
      (((10041624376136906734445141245980917936116200459782579 * 10 ^ 70 +
        9763662031113331664872562121840111009900132102956732920657566641566308) * 10 ^ 70 +
        4130005162851477814783021043746207406018113023410604320354522673000912) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 251 = 72 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 26 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_250_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_250_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (251 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (251 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_251 :
    recurrence2Scalar4Exceptional.coeff 251 =
      -(((8484860784090358989101794293074434100383019201556147 * 10 ^ 70 +
        9906423262069630524166612325891901049039983779169041785580257527486116) * 10 ^ 70 +
        5677063847260192535675108972256254313225632829849778124204346305126750) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 252 = 73 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 25 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_251_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_251_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (252 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (252 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_252 :
    recurrence2Scalar4Exceptional.coeff 252 =
      (((5056836126659377951261092963854317019345731462766959 * 10 ^ 70 +
        8837683103459549563678689691327237456828742205888226311006091156065895) * 10 ^ 70 +
        2508756363301789361952399931885743000355413054525528761700633611099732) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 253 = 74 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 24 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_252_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_252_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (253 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (253 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_253 :
    recurrence2Scalar4Exceptional.coeff 253 =
      -(((2470039868257528424321356455374481243462640708781375 * 10 ^ 70 +
        3377352666256199214479360055220525613105689560852471099040189444548405) * 10 ^ 70 +
        5213213467375095937902584291018046993381561404489196750237811424592908) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 254 = 75 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  rw [recurrence2Scalar4Exceptional_coeff_253_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_253_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (254 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (254 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_254 :
    recurrence2Scalar4Exceptional.coeff 254 =
      (((1019807870319997500752343967018355726615981241552135 * 10 ^ 70 +
        8475135832986766477554126902307018192088594243391827459678578714027552) * 10 ^ 70 +
        2857832388443833985122254305580469830083385962413611857159779689415528) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 255 = 76 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 22 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_254_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_254_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (255 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (255 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_255 :
    recurrence2Scalar4Exceptional.coeff 255 =
      -(((348789332376061931792825777903971458605353640295909 * 10 ^ 70 +
        0396089532893117278862773837171162158505976993863504808431870473996272) * 10 ^ 70 +
        9788541325823936096127707156385707940158661050752624566195219551601785) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 256 = 77 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 21 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_255_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_255_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (256 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (256 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_256 :
    recurrence2Scalar4Exceptional.coeff 256 =
      (((88754457999326641625954903931535581536313817094018 * 10 ^ 70 +
        8551093926814303110774905084154630820257488905375682778576923278714943) * 10 ^ 70 +
        5626778890513037936822997885681690641152632203452278804944148718598250) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 257 = 78 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 20 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_256_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_256_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (257 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (257 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_257 :
    recurrence2Scalar4Exceptional.coeff 257 =
      -(((7939747545981148227806190290173769543701841779549 * 10 ^ 70 +
        4297835509939604902401665620078112693137424000009441516959515850744036) * 10 ^ 70 +
        7649342367060157410729820078425166341421666025650717869229738756323737) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 258 = 79 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 19 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_257_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_257_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (258 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (258 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_258 :
    recurrence2Scalar4Exceptional.coeff 258 =
      -(((8463500350994569559327435395460511120989134013498 * 10 ^ 70 +
        3045964629888300894238237346352698897830831395135869230861963558058181) * 10 ^ 70 +
        3694090414450281879659988652152046867269308567232971604568949618336832) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 259 = 80 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 18 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_258_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (259 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (259 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_259 :
    recurrence2Scalar4Exceptional.coeff 259 =
      (((7290169664303616317120299279561301463955016956333 * 10 ^ 70 +
        0918330830191001791493513142203484526807352623705171234444233385249526) * 10 ^ 70 +
        3173935879741437032519952684425571320427116422334465534771684311332953) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 260 = 81 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 17 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_259_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (260 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (260 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_260 :
    recurrence2Scalar4Exceptional.coeff 260 =
      -(((3867082328500726837612560928033312296897487527419 * 10 ^ 70 +
        9644143631163085740642453686071136115788240514204565765268941127544823) * 10 ^ 70 +
        2874385801957313990063276021809564288110622941817859609833930062616898) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 261 = 82 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 16 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_260_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (261 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (261 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_261 :
    recurrence2Scalar4Exceptional.coeff 261 =
      (((1629305643299178579691274881655089489995230209563 * 10 ^ 70 +
        9619219731149411566650547390311113820193703505107333593431198615422575) * 10 ^ 70 +
        3827336229734745001359955974558064068168019888306826048048359798206159) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 262 = 83 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  rw [recurrence2Scalar4Exceptional_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_261_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (262 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (262 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_262 :
    recurrence2Scalar4Exceptional.coeff 262 =
      -(((575022726094787759337198481519642167828018308406 * 10 ^ 70 +
        2632710713045506671719110345375200020118852681015113069629335336426476) * 10 ^ 70 +
        4025885879055168300527720898335846026143194151623310374814263034148513) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 263 = 84 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 14 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_262_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (263 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (263 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_263 :
    recurrence2Scalar4Exceptional.coeff 263 =
      (((167678852090430807723499534195808965197144357084 * 10 ^ 70 +
        2024315295733749452002813755788520404205485112878536041609873973774801) * 10 ^ 70 +
        4691917028930871549962132175614103248328699005330554960619679402409385) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 264 = 85 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 13 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_263_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (264 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (264 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_264 :
    recurrence2Scalar4Exceptional.coeff 264 =
      -(((35066649967830343182883750165194028346696709611 * 10 ^ 70 +
        5535750441454928343479647274189682576450113942700711937718403516583309) * 10 ^ 70 +
        0159750705734797593429233072010859281430036538869431437516320689969933) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 265 = 86 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 12 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_264_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (265 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (265 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_265 :
    recurrence2Scalar4Exceptional.coeff 265 =
      (((41779203627471408041033887357162194563447848 * 10 ^ 70 +
        7522918581010936690876960438961123527397614702594315070835566444640516) * 10 ^ 70 +
        2210209492836194273844319431835562839844486724574680201950138681076562) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 266 = 87 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  rw [recurrence2Scalar4Exceptional_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_265_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (266 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (266 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_266 :
    recurrence2Scalar4Exceptional.coeff 266 =
      (((5663117074125394913949533327198455175267390397 * 10 ^ 70 +
        1402482523424696665559764611208967899942348446721060114798215840620025) * 10 ^ 70 +
        6304216027090463506124828395248208620222843505538889463853765742647168) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 267 = 88 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 10 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_266_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (267 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (267 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_267 :
    recurrence2Scalar4Exceptional.coeff 267 =
      -(((4395670956357391282092658382521099031780905567 * 10 ^ 70 +
        6717291359145146525735959590750471568822000089100158139253027095477869) * 10 ^ 70 +
        2820179033920463460134423420731564368599250004148613601911860143402889) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 268 = 89 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 9 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_267_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (268 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (268 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_268 :
    recurrence2Scalar4Exceptional.coeff 268 =
      (((2399681086219680201456429550826046278096210481 * 10 ^ 70 +
        4116089505566809607731017482204298783884778886879412702295990705496168) * 10 ^ 70 +
        6909684737301049026442477216458587178118995841240349580616128402739976) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 269 = 90 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 8 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_268_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (269 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (269 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_269 :
    recurrence2Scalar4Exceptional.coeff 269 =
      -(((1022672917594052677251941978339286921128064745 * 10 ^ 70 +
        3519920645500179704785071776377585838895322793772537883053851383164042) * 10 ^ 70 +
        4246043003976822049869457878631992311416469483692741081684392190215879) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 270 = 91 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 7 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_269_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (270 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (270 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_270 :
    recurrence2Scalar4Exceptional.coeff 270 =
      (((303704807581783561222964197198021825892062320 * 10 ^ 70 +
        7928012524653107764093289758711809940990031161091605144255477914443917) * 10 ^ 70 +
        8080701977304376650147994765907404038684170282705829253434327959373193) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 271 = 92 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 6 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_270_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (271 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (271 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_271 :
    recurrence2Scalar4Exceptional.coeff 271 =
      -(((13148772155267050875992660449807724321785686 * 10 ^ 70 +
        4002792877627628131308130651664659821404424260509682529123917136284194) * 10 ^ 70 +
        9593145445626604128955665288720766901029691537699431608602578627227114) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 272 = 93 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 5 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_271_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (272 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (272 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_272 :
    recurrence2Scalar4Exceptional.coeff 272 =
      -(((61754002719692596931219113462119234920624746 * 10 ^ 70 +
        2893335767253272701038663542811100222478838590328972442709403402908435) * 10 ^ 70 +
        8119505713120501314508015629242958399782540022212778324080609293708713) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 273 = 94 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 4 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_272_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (273 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (273 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_273 :
    recurrence2Scalar4Exceptional.coeff 273 =
      (((55074507417185054895679285996560048419767848 * 10 ^ 70 +
        8664870422009210773487479640810807109538155566561829502509995458651737) * 10 ^ 70 +
        9048722746369586197206908818447433664116795468676951319131301168562875) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 274 = 95 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 3 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_273_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (274 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (274 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_274 :
    recurrence2Scalar4Exceptional.coeff 274 =
      -(((31573604516090731364220172237098011461979255 * 10 ^ 70 +
        6623187505291376907451558488132547922445184182443284773529378915103264) * 10 ^ 70 +
        5978899047712831707218527798941832107922624165572929657901723678456116) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 275 = 96 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 2 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_274_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (275 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (275 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_275 :
    recurrence2Scalar4Exceptional.coeff 275 =
      (((13627931195738996295079993569478683438969391 * 10 ^ 70 +
        6022841872847468794965130373736804510215437608902785949781646011765458) * 10 ^ 70 +
        5370403121510412845338669095678317611013099072809285384565818254937565) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 276 = 97 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 1 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_275_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (276 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (276 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_276 :
    recurrence2Scalar4Exceptional.coeff 276 =
      -(((4257302776231725624333446109857866305980674 * 10 ^ 70 +
        5561051417804602335252400810462723839751972629695643637311171675056457) * 10 ^ 70 +
        6081089177529457812502872947438843486202598232604476136949298803426794) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 277 = 98 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_276_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (277 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (277 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_277 :
    recurrence2Scalar4Exceptional.coeff 277 =
      (((613698195033000718976352412192445921545953 * 10 ^ 70 +
        8668276961712893938718973914628427345617913394704385143326757998378075) * 10 ^ 70 +
        7164632808516734827233978995927777502426536956776712510039872949880470) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 278 = 99 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 31 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_277_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (278 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (278 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_278 :
    recurrence2Scalar4Exceptional.coeff 278 =
      (((324150583235314750101557901624873535145168 * 10 ^ 70 +
        7528741108175957959104810085110898965576018585128119212464523641718848) * 10 ^ 70 +
        9828238928158421331401639464350061107043780158042944356580315083645493) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 279 = 100 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 30 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_278_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (279 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (279 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_279 :
    recurrence2Scalar4Exceptional.coeff 279 =
      -(((338491146251273752440975973535868758454778 * 10 ^ 70 +
        8826684255686406150956524570091405919380306995030979876222565243120932) * 10 ^ 70 +
        4556574050681414549569624027106004139757984613554851187493880758120609) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 280 = 101 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 29 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_279_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (280 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (280 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_280 :
    recurrence2Scalar4Exceptional.coeff 280 =
      (((182001511212667257440203076252246798634427 * 10 ^ 70 +
        0298483872065719718378877338443467620915600347763690898843900650533392) * 10 ^ 70 +
        0253929491545054450793286509208126356298537197694306509945805125478790) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 281 = 102 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 28 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_280_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (281 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (281 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_281 :
    recurrence2Scalar4Exceptional.coeff 281 =
      -(((69906162063173590450311187775360524416380 * 10 ^ 70 +
        9924688500643642770037921961884392236553934326827506321637969757413500) * 10 ^ 70 +
        1178924432301624378757215626431261491612950607837632758349836957854829) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 282 = 103 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 27 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_281_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (282 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (282 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_282 :
    recurrence2Scalar4Exceptional.coeff 282 =
      (((18756371758666819886151188738910072989119 * 10 ^ 70 +
        0117176408851346550368635497520127966472866493351096412960320693792904) * 10 ^ 70 +
        0637206102315852649644102632150790390804745108650287898207925016583871) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 283 = 104 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 26 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_282_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (283 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (283 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_283 :
    recurrence2Scalar4Exceptional.coeff 283 =
      -(((2065898800959257635316519378140697158128 * 10 ^ 70 +
        0000621958254531930174692630388569562659688885129342047791087683229742) * 10 ^ 70 +
        0383009199304060331456304623500777490728685055536107604342661184418263) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 284 = 105 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 25 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_283_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (284 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (284 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_284 :
    recurrence2Scalar4Exceptional.coeff 284 =
      -(((1228791816696165620291446478299935740081 * 10 ^ 70 +
        2263906508210333914845660717768199339101106010067165849214594589276081) * 10 ^ 70 +
        1619582745361205323911328763557877523974708499822015795346168010542608) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 285 = 106 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 24 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_284_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (285 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (285 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_285 :
    recurrence2Scalar4Exceptional.coeff 285 =
      (((989031115554345134990080095419919044429 * 10 ^ 70 +
        2260058143089994458159683369264880855864192094104900003802531739257694) * 10 ^ 70 +
        5346606266056545437383582205098553351794571978865694149293184158327727) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 286 = 107 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 23 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_285_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (286 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (286 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_286 :
    recurrence2Scalar4Exceptional.coeff 286 =
      -(((420051979905012158529395774186639470420 * 10 ^ 70 +
        9016955834560818686578441483849346698735270367468257491360212542981458) * 10 ^ 70 +
        1353003952009040035085198904873910233647930470590622688257687774333159) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 287 = 108 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 22 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_286_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (287 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (287 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_287 :
    recurrence2Scalar4Exceptional.coeff 287 =
      (((120536130145503844034897237229926842888 * 10 ^ 70 +
        0376273644667166362819567343119606650073455754386412130308201074091992) * 10 ^ 70 +
        8141870056944101369715927369539288282667432385377772484673646754823493) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 288 = 109 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 21 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_287_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (288 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (288 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_288 :
    recurrence2Scalar4Exceptional.coeff 288 =
      -(((19268200331628781670068967286786574396 * 10 ^ 70 +
        4548946063844529107054675538906884582424577625335338353498311327707434) * 10 ^ 70 +
        9644221385633460108023223385650865544364723728702340465347055442979994) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 289 = 110 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 20 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_288_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (289 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (289 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_289 :
    recurrence2Scalar4Exceptional.coeff 289 =
      -(((2399241627878615036183098833660284521 * 10 ^ 70 +
        6876103020310320568913844756216699179837028888146196839070584356220132) * 10 ^ 70 +
        0216091137997701077084366009290518349644792279858275356338185571710221) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 290 = 111 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 19 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_289_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (290 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (290 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_290 :
    recurrence2Scalar4Exceptional.coeff 290 =
      (((3097983821735091685776910435531178370 * 10 ^ 70 +
        3874840347441255710461053249862010888525563930351700133683149150933725) * 10 ^ 70 +
        9791475050823348616345642078237454283573709610231278797326914007200893) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 291 = 112 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 18 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_290_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (291 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (291 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_291 :
    recurrence2Scalar4Exceptional.coeff 291 =
      -(((1287053590092959492894595571832944824 * 10 ^ 70 +
        4991342595026275655868130956972529136301761880773344845141942607462772) * 10 ^ 70 +
        1571670126488948187300132980228020930482332648684866739415708146890224) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 292 = 113 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 17 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_291_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (292 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (292 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_292 :
    recurrence2Scalar4Exceptional.coeff 292 =
      (((333063619524255994739629858052331440 * 10 ^ 70 +
        3486904581208771865142224886621275507533317270510671290234329250786692) * 10 ^ 70 +
        9899686033579492418789444397656298294621922121172391636398661410472309) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 293 = 114 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 16 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_292_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (293 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (293 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_293 :
    recurrence2Scalar4Exceptional.coeff 293 =
      -(((43964221280592098368831906383469542 * 10 ^ 70 +
        3737381531369365613099301426589108056815216509729270476933643594695748) * 10 ^ 70 +
        7613280268503084366829623982019173479277115651270186874439875960408879) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 294 = 115 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 15 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_293_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (294 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (294 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_294 :
    recurrence2Scalar4Exceptional.coeff 294 =
      -(((7043454770392603905586580971329736 * 10 ^ 70 +
        9316869830387571866278466652991647549685692264873055934987052600297596) * 10 ^ 70 +
        4756855170692682077212331663478410103045761299752764820326334500150784) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 295 = 116 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 14 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_294_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (295 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (295 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_295 :
    recurrence2Scalar4Exceptional.coeff 295 =
      (((6266765281649131219079280429129283 * 10 ^ 70 +
        4038570785481171051737136565898710936532496757621377106789442198255668) * 10 ^ 70 +
        2725628190848368375701233119079623780365069530057494600918363595324738) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 296 = 117 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 13 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_295_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (296 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (296 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_296 :
    recurrence2Scalar4Exceptional.coeff 296 =
      -(((2055657104736391937007806964838965 * 10 ^ 70 +
        7259636100577795712296845235781949562996946163729523733794845620510574) * 10 ^ 70 +
        1210698896377276908180677413050161037116419805345185845178265336895312) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 297 = 118 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 12 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_296_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (297 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (297 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_297 :
    recurrence2Scalar4Exceptional.coeff 297 =
      (((388105885988547777947310814164395 * 10 ^ 70 +
        1308466935900560717855711139492686295292364198778179918438764874400457) * 10 ^ 70 +
        2729420108071494578838138570150804373344088937407598158574000034951074) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 298 = 119 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 11 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_297_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (298 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (298 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_298 :
    recurrence2Scalar4Exceptional.coeff 298 =
      -(((17087477113869536561407895182410 * 10 ^ 70 +
        8743111256027558509153133524620138992162515658855019736209093947135056) * 10 ^ 70 +
        3102271738386330986319561540296032049731454759341932903363870102180511) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 299 = 120 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 10 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_298_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (299 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (299 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_299 :
    recurrence2Scalar4Exceptional.coeff 299 =
      -(((16754834878383828236660302267840 * 10 ^ 70 +
        9504673262403408390491979239634306108395450593892452655832450888003922) * 10 ^ 70 +
        9801627590815786348257651884892751255497763271243488672435411124433974) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 300 = 121 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 9 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_299_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (300 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (300 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_300 :
    recurrence2Scalar4Exceptional.coeff 300 =
      (((6746520671037324941104535643170 * 10 ^ 70 +
        6891113415693446011652104997286799645621616052707209257089226324284357) * 10 ^ 70 +
        8662739797359910075980990025165205300332660695588410177358590987345376) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 301 = 122 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 8 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_300_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (301 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (301 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_301 :
    recurrence2Scalar4Exceptional.coeff 301 =
      -(((1358666180444138393781561548699 * 10 ^ 70 +
        2701442053569215507774777104280068426044513982465934760164256870362775) * 10 ^ 70 +
        6892866390662365383241285687408568016329835781603961050919865078388356) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 302 = 123 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 7 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_301_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (302 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (302 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_302 :
    recurrence2Scalar4Exceptional.coeff 302 =
      (((98864512071399308762125904057 * 10 ^ 70 +
        7495536265351181844033210103710210288146030146401301184859693453962368) * 10 ^ 70 +
        2526360931173534386697852624010546835559959195859965951635289292536992) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 303 = 124 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 6 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_302_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (303 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (303 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_303 :
    recurrence2Scalar4Exceptional.coeff 303 =
      (((32766955583636801473293166812 * 10 ^ 70 +
        8825026698353795664752006822215129823878584832874446151864070820490876) * 10 ^ 70 +
        3459710642005169996244212958512458241820414918835328104924217955410054) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 304 = 125 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 5 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_303_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (304 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (304 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_304 :
    recurrence2Scalar4Exceptional.coeff 304 =
      -(((13723045162287530729990968471 * 10 ^ 70 +
        1230834244950931327893889420219893123077898668792381431442178824416453) * 10 ^ 70 +
        0078226721525559492932786574749512354166907471262006724737357337320198) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 305 = 126 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 4 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_304_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (305 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (305 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_305 :
    recurrence2Scalar4Exceptional.coeff 305 =
      (((2436768679624799732541564726 * 10 ^ 70 +
        4299810000776234650907651196139013309224560611702306692331279492355889) * 10 ^ 70 +
        0604732115591593729219341901785913717623402107398692689157839872430829) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 306 = 127 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 3 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_305_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (306 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (306 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_306 :
    recurrence2Scalar4Exceptional.coeff 306 =
      -(((114181900743808803656815184 * 10 ^ 70 +
        2912194133526233545387116211543357165725022045795901242766254406787249) * 10 ^ 70 +
        1039868453815036630020242619539698491557511057377733201984932534548576) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 307 = 128 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 2 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_306_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (307 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (307 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_307 :
    recurrence2Scalar4Exceptional.coeff 307 =
      -(((58360203828778427671719044 * 10 ^ 70 +
        2054258947807795301712497268979215245893725669541101690891080118715259) * 10 ^ 70 +
        1206010860284052152252374197866248879977427423293416546801361015852996) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 308 = 129 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 1 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_307_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (308 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (308 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_308 :
    recurrence2Scalar4Exceptional.coeff 308 =
      (((17454679935190834136073580 * 10 ^ 70 +
        5985596262120935493650905982512818351739299515769231737502699658437768) * 10 ^ 70 +
        1463609370837559936581694163165642021024968967722444275590789459988404) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 309 = 130 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_308_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (309 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (309 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_309 :
    recurrence2Scalar4Exceptional.coeff 309 =
      -(((2047239259384618695710031 * 10 ^ 70 +
        8288823409509332263996888756453659815995348943651655185741850284166273) * 10 ^ 70 +
        5653848978468642123857716986414861654153869421370500812690771106388808) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 310 = 131 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 31 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_309_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (310 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (310 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_310 :
    recurrence2Scalar4Exceptional.coeff 310 =
      -(((79396303058886718942260 * 10 ^ 70 +
        3507675753922459224512225647273402544769508530529920603190011940679239) * 10 ^ 70 +
        6242774935308137138434389441969564404687664128560524453050249898886549) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 311 = 132 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 30 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_310_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (311 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (311 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_311 :
    recurrence2Scalar4Exceptional.coeff 311 =
      (((70922905403181874692839 * 10 ^ 70 +
        7827419638236324125382310091532641438993125033826106661052778440892106) * 10 ^ 70 +
        0313585491513013303230808208713964643854858357246913036736780157691367) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 312 = 133 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 29 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_311_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (312 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (312 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_312 :
    recurrence2Scalar4Exceptional.coeff 312 =
      -(((11028728769841125260325 * 10 ^ 70 +
        4530997699080166434166828959598081598843474750950071325444861356370261) * 10 ^ 70 +
        8175994000010658835162329636267216347240530622740696310567934813088538) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 313 = 134 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 28 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_312_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (313 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (313 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_313 :
    recurrence2Scalar4Exceptional.coeff 313 =
      (((230419752671849222238 * 10 ^ 70 +
        2452023412975544960715366490017918170600427610422426438847430309658483) * 10 ^ 70 +
        5865624157151843530324826948691246361066231929061864355396692399387884) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 314 = 135 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 27 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_313_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (314 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (314 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_314 :
    recurrence2Scalar4Exceptional.coeff 314 =
      (((203478117172534079685 * 10 ^ 70 +
        4728422495780180438966247815783730335580212915720445892381626039675378) * 10 ^ 70 +
        2624341382132923527409414354115630298164695719392157004320209075025963) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 315 = 136 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 26 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_314_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (315 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (315 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_315 :
    recurrence2Scalar4Exceptional.coeff 315 =
      -(((34804161199491201122 * 10 ^ 70 +
        3686364482911409709693290796470880539255135336753962435348095214298491) * 10 ^ 70 +
        9994251502272753074576024357349950607993944464977182301028189116383449) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 316 = 137 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 25 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_315_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (316 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (316 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_316 :
    recurrence2Scalar4Exceptional.coeff 316 =
      (((942744473185442137 * 10 ^ 70 +
        6159012656358879537921592142948413609206048978034911943325252153440092) * 10 ^ 70 +
        0788093166624296778016838238798842493854234174715498869030627212469174) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 317 = 138 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 24 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_316_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (317 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (317 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_317 :
    recurrence2Scalar4Exceptional.coeff 317 =
      (((485564953015535045 * 10 ^ 70 +
        8131440836727461603503726676107505688900370165053220135625139670463620) * 10 ^ 70 +
        4505410051399487002739358839147844307468723419465161375036710809593903) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 318 = 139 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 23 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_317_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (318 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (318 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_318 :
    recurrence2Scalar4Exceptional.coeff 318 =
      -(((70586241926598171 * 10 ^ 70 +
        6079219760199744794324971967558985543732908988079710348615732197179654) * 10 ^ 70 +
        7874417097825743436038821593980455274830720255664826582435986328762424) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 319 = 140 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 22 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_318_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (319 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (319 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_319 :
    recurrence2Scalar4Exceptional.coeff 319 =
      (((108149599527042 * 10 ^ 70 +
        5871046343508426363083591899296152439720019592025484132968618307011993) * 10 ^ 70 +
        7113823380267129460877983107063641135646319666928972764237080493185987) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 320 = 141 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 21 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_319_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (320 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (320 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_320 :
    recurrence2Scalar4Exceptional.coeff 320 =
      (((952056108967756 * 10 ^ 70 +
        6691030361562849735938092117232244932814333161022410557737521196337398) * 10 ^ 70 +
        3270018456059763841691627613933017254770084100052261824734644819280376) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 321 = 142 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 20 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_320_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (321 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (321 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_321 :
    recurrence2Scalar4Exceptional.coeff 321 =
      -(((79364098351968 * 10 ^ 70 +
        2791735762415572927439792506494335548697878411325094781544976599464085) * 10 ^ 70 +
        3964752219450897864043664257612591282337033825904016283629421858602685) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 322 = 143 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 19 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_321_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (322 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (322 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_322 :
    recurrence2Scalar4Exceptional.coeff 322 =
      -(((5282322125861 * 10 ^ 70 +
        3952360825936328389531066411997276634183387241645633186398543224100089) * 10 ^ 70 +
        3495017654567460714715660105413708962552773408117722485587387394021869) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 323 = 144 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 18 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_322_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 145,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (323 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (323 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_323 :
    recurrence2Scalar4Exceptional.coeff 323 =
      (((1160638722953 * 10 ^ 70 +
        7868592085330103734665570421949764409360622759079845859571936875757554) * 10 ^ 70 +
        8354898430429877269214856467320278268077645215591227310881273277033857) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 324 = 145 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 17 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_323_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 146,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (324 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (324 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_324 :
    recurrence2Scalar4Exceptional.coeff 324 =
      -(((8412202885 * 10 ^ 70 +
        6426594275933407260448855366564818025605455762154226120574383638499576) * 10 ^ 70 +
        7139451407978326155737019650984130738937041056942337874107782396796620) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 325 = 146 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 16 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_324_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 147,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (325 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (325 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_325 :
    recurrence2Scalar4Exceptional.coeff 325 =
      -(((9872940494 * 10 ^ 70 +
        8586488031739882481911731879968073729038568003035770161842146333934428) * 10 ^ 70 +
        0840214832004217945768168672744784606848911161794993308077442490613572) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 326 = 147 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 15 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_325_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 148,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (326 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (326 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_326 :
    recurrence2Scalar4Exceptional.coeff 326 =
      (((377843705 * 10 ^ 70 +
        3999189214988248660063153501668219744797673124363633321480587105183304) * 10 ^ 70 +
        8864016584194650206023683356123004316946776383406326545184326443333146) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 327 = 148 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 14 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_326_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 149,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (327 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (327 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_327 :
    recurrence2Scalar4Exceptional.coeff 327 =
      (((63702342 * 10 ^ 70 +
        7933409507175270525618628009158046251890930322663793077359288704835941) * 10 ^ 70 +
        7610153700378280880047790725816674333429274322510534987748950427148587) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 328 = 149 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 13 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_327_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 150,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (328 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (328 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_328 :
    recurrence2Scalar4Exceptional.coeff 328 =
      -(((3281878 * 10 ^ 70 +
        3828521645343743026011931869971169096247120723061850178247102903739805) * 10 ^ 70 +
        8861811631676652231555177802958735088322954480456978545704326517915409) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 329 = 150 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 12 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_328_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 151,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (329 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (329 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_329 :
    recurrence2Scalar4Exceptional.coeff 329 =
      -(((370591 * 10 ^ 70 +
        0711777030773383434522696952543739149132364372007026749557307760209351) * 10 ^ 70 +
        1263557860711562908788186503007945207600567210492510995114445230338898) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 330 = 151 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 11 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_329_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 152,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (330 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (330 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_330 :
    recurrence2Scalar4Exceptional.coeff 330 =
      (((15393 * 10 ^ 70 +
        1539273404340678490534184318235637768456587286452531208430293325804251) * 10 ^ 70 +
        2252243038431916472951788298997960037447895475649674773928993302584029) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 331 = 152 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 10 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_330_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 153,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (331 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (331 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_331 :
    recurrence2Scalar4Exceptional.coeff 331 =
      (((2029 * 10 ^ 70 +
        0431299390201364455692848454403817554071713950286254849577034418965301) * 10 ^ 70 +
        6214668924120915666546416542115768282484271435327867182669249290097051) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 332 = 153 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 9 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_331_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 154,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (332 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (332 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_332 :
    recurrence2Scalar4Exceptional.coeff 332 =
      -(((17 * 10 ^ 70 +
        9902750306295419048420291963130074878408307273230248246749562222548197) * 10 ^ 70 +
        4309812264136892754888363571236633513693556499145460493426147204140625) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 333 = 154 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 8 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_332_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 155,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (333 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (333 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_333 :
    recurrence2Scalar4Exceptional.coeff 333 =
      -(((8 * 10 ^ 70 +
        4686236529298110531125704113434925537608961728726116255069455629796338) * 10 ^ 70 +
        7541758924047384325304036201745552255984186445035017595762803109087965) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 334 = 155 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 7 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_333_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 156,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (334 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (334 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_334 :
    recurrence2Scalar4Exceptional.coeff 334 =
      -((2886801395711924498350490421249425380743193071840246167090949460753468 * 10 ^ 70 +
        8567263865361630449395235484342937804450351547290129402015610049837007) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 335 = 156 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 6 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_334_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 157,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (335 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (335 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_335 :
    recurrence2Scalar4Exceptional.coeff 335 =
      ((116069032453991659032121760953974672360334030585403780520163164276404 * 10 ^ 70 +
        2434008933464405946647082876555596653196920901514004264144379341882111) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 336 = 157 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 5 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_335_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 158,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (336 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (336 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_336 :
    recurrence2Scalar4Exceptional.coeff 336 =
      ((14603284496967528152152938545318463356786790406401575271432556114243 * 10 ^ 70 +
        6315155306098254351553522311974810031896391437393623729533456509672634) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 337 = 158 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 4 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_336_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 159,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (337 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (337 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_337 :
    recurrence2Scalar4Exceptional.coeff 337 =
      ((691979033307682220068129378015171041856422206778099653934542990096 * 10 ^ 70 +
        7940160444830582684704637837000391169507527741860669677814781755592641) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 338 = 159 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 3 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_337_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 160,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (338 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 145,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (338 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_338 :
    recurrence2Scalar4Exceptional.coeff 338 =
      ((20849441095888894010579929848524113707186268992175310231385417555 * 10 ^ 70 +
        3464982639666475803051936228964248126690116798252912376439361306987402) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 339 = 160 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 2 +
      145 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_338_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 161,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (339 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 146,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (339 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_339 :
    recurrence2Scalar4Exceptional.coeff 339 =
      ((448194042173330635537653426055045904947884501802371962185365474 * 10 ^ 70 +
        0979201070523969796984124322236670331079660323463722661281284937030485) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 340 = 161 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 1 +
      146 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_339_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 162,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (340 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 147,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (340 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_340 :
    recurrence2Scalar4Exceptional.coeff 340 =
      ((7197923914561939166096373465369559494328843787469239400732038 * 10 ^ 70 +
        6810726199026981526179879533952353095614062336542934451623639177970690) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 341 = 162 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_340_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 163,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (341 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 148,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (341 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_341 :
    recurrence2Scalar4Exceptional.coeff 341 =
      ((88199674571672187901093999421089936281805138630079558980330 * 10 ^ 70 +
        6039118618036955972095048392625338368782280631428899683576610715856598) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 342 = 163 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 31 +
      148 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_341_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 164,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (342 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 149,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (342 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_342 :
    recurrence2Scalar4Exceptional.coeff 342 =
      ((830791704622545757749030565314299608295783978746892633880 * 10 ^ 70 +
        0578935912682468390932542828020009472423802715218296664734786902506163) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 343 = 164 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 30 +
      149 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_342_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 165,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (343 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 150,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (343 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_343 :
    recurrence2Scalar4Exceptional.coeff 343 =
      ((5994119901606682643921309889057215410433825436021810335 * 10 ^ 70 +
        6062644531216409929742610645468461102067081641151112563289084245466622) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 344 = 165 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 29 +
      150 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_343_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 166,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (344 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 151,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (344 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_344 :
    recurrence2Scalar4Exceptional.coeff 344 =
      ((32546916810466160917919741515879254934309379972181912 * 10 ^ 70 +
        8792149314265784171798092451678267010729990736418366928171701789933808) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 345 = 166 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 28 +
      151 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_344_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 167,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (345 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 152,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (345 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_345 :
    recurrence2Scalar4Exceptional.coeff 345 =
      ((127142206760691542034699376087597550370300582060401 * 10 ^ 70 +
        8422272690111485256782606546937152787347829219352470328553077270283252) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 346 = 167 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 27 +
      152 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_345_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 168,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (346 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 153,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (346 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_346 :
    recurrence2Scalar4Exceptional.coeff 346 =
      ((313823954531756183361815971096438784436641354105 * 10 ^ 70 +
        9692275728116255381201010339414774869326839490234453045389453666760058) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 347 = 168 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 26 +
      153 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_346_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 169,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (347 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 154,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (347 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_347 :
    recurrence2Scalar4Exceptional.coeff 347 =
      ((210131585923257730688336600589122947798949878 * 10 ^ 70 +
        7970535466926744132581087983325579561973439346097234463039095729361770) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 348 = 169 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 25 +
      154 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_347_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 170,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (348 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 155,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (348 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_348 :
    recurrence2Scalar4Exceptional.coeff 348 =
      -((1743053084072876811621159186349096252357222 * 10 ^ 70 +
        9543165650438983959322230126235584661004459375044070471246798957479808) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 349 = 170 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 24 +
      155 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_348_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 171,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (349 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 156,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (349 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_349 :
    recurrence2Scalar4Exceptional.coeff 349 =
      -((7443389230383853460525359933342839521542 * 10 ^ 70 +
        7432847648420064450542529123833511991672553400867545102197780684200263) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 350 = 171 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 23 +
      156 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_349_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 172,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (350 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 157,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (350 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_350 :
    recurrence2Scalar4Exceptional.coeff 350 =
      -((12459063866979167151192518217327150535 * 10 ^ 70 +
        8179860991588439905688523137889949694674016623908838527672169569854546) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 351 = 172 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 22 +
      157 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_350_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 173,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (351 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 158,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (351 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_351 :
    recurrence2Scalar4Exceptional.coeff 351 =
      ((1574434912918844585532364579433209 * 10 ^ 70 +
        4753024267347351562016130408190451355360434403961543239843165879550634) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 352 = 173 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 21 +
      158 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_351_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 174,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (352 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 159,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (352 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_352 :
    recurrence2Scalar4Exceptional.coeff 352 =
      ((49347866865681395107451201929760 * 10 ^ 70 +
        9008899396447728292535900410590659753782806645524967022845880395421467) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 353 = 174 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 20 +
      159 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_352_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 175,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (353 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 160,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (353 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_353 :
    recurrence2Scalar4Exceptional.coeff 353 =
      ((94153351339516478072949445118 * 10 ^ 70 +
        2890881404539263134901352359966393355171892056827015541473231663961560) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 354 = 175 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 19 +
      160 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_353_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 176,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (354 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 161,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (354 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_354 :
    recurrence2Scalar4Exceptional.coeff 354 =
      ((53752501234608625648527559 * 10 ^ 70 +
        5678072068752906512372216686834647622096648439158145055021761308210922) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 355 = 176 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 18 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_354_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 177,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (355 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 162,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (355 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_355 :
    recurrence2Scalar4Exceptional.coeff 355 =
      -((82843784593566346081579 * 10 ^ 70 +
        0535782149348018402694376351088960356917856977852840609729541761760130) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 356 = 177 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 17 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_355_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 178,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (356 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 163,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (356 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_356 :
    recurrence2Scalar4Exceptional.coeff 356 =
      -((196877719029288602299 * 10 ^ 70 +
        5843364487800569657838984158020231738941120649569864612075521052332725) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 357 = 178 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 16 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_356_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 179,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (357 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 164,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (357 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_357 :
    recurrence2Scalar4Exceptional.coeff 357 =
      -((188689020300243295 * 10 ^ 70 +
        5332332516064785259100087364244069871120371289228578536382745422274911) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 358 = 179 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 15 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_357_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 180,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (358 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 165,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (358 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_358 :
    recurrence2Scalar4Exceptional.coeff 358 =
      -((103636615995708 * 10 ^ 70 +
        7670620791837187616514228130375884727904368710501977330471150777293348) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 359 = 180 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 14 +
      165 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_358_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 181,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (359 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 166,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (359 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_359 :
    recurrence2Scalar4Exceptional.coeff 359 =
      -((34526309222 * 10 ^ 70 +
        7843230013186428341720491478809918606131569386011375569444040152872780) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 360 = 181 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 13 +
      166 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_359_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 182,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (360 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 167,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (360 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_360 :
    recurrence2Scalar4Exceptional.coeff 360 =
      -((6945112 * 10 ^ 70 +
        5788767160738750974361603460341706964405445446764043980405197963847464) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 361 = 182 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 12 +
      167 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_360_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 183,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (361 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 168,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (361 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_361 :
    recurrence2Scalar4Exceptional.coeff 361 =
      -((820 * 10 ^ 70 +
        9175256953363857470343879651614168637789123547129117638015618821516203) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 362 = 183 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 11 +
      168 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_361_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 184,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (362 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 169,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (362 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_362 :
    recurrence2Scalar4Exceptional.coeff 362 =
      (-553579653869120253594481098387031836829607782707811626952184156645348 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 363 = 184 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 10 +
      169 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_362_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 185,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (363 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 170,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (363 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_363 :
    recurrence2Scalar4Exceptional.coeff 363 =
      (-20125022237489898250371401369318508091834256904817584990967126230 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 364 = 185 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 9 +
      170 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_363_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 186,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (364 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 171,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (364 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_364 :
    recurrence2Scalar4Exceptional.coeff 364 =
      (-352804146258149357695252210621796573535926531729387519626262 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 365 = 186 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 8 +
      171 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_364_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 187,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (365 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 172,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (365 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_365 :
    recurrence2Scalar4Exceptional.coeff 365 =
      (-2618820130382954920395923334285577735862410527799027583 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 366 = 187 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 7 +
      172 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_365_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 188,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (366 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 173,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (366 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_366 :
    recurrence2Scalar4Exceptional.coeff 366 =
      (-8740486410694444934977191240100770161277291264086 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 367 = 188 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 6 +
      173 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_366_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 189,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (367 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 174,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (367 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_367 :
    recurrence2Scalar4Exceptional.coeff 367 =
      (-12123905054827753052342908589940841118647278 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 368 = 189 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 5 +
      174 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_367_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 190,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (368 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 175,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (368 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_368 :
    recurrence2Scalar4Exceptional.coeff 368 =
      (-4314945562620242083762085958757723081 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 369 = 190 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 4 +
      175 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_368_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 191,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (369 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 176,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (369 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_369 :
    recurrence2Scalar4Exceptional.coeff 369 =
      (-73956985471302305627148037825 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 370 = 191 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 3 +
      176 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_369_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 192,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (370 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 177,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (370 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_370 :
    recurrence2Scalar4Exceptional.coeff 370 =
      (-202558992798770786248 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 371 = 192 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 2 +
      177 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_370_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 193,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (371 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 178,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (371 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_371 :
    recurrence2Scalar4Exceptional.coeff 371 =
      (-152365481437 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 372 = 193 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 1 +
      178 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_371_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
