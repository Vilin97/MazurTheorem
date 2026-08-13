/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2LeftPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar2Left coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4A2_coeff_0
  recurrence4A2_coeff_1
  recurrence4A2_coeff_10
  recurrence4A2_coeff_100
  recurrence4A2_coeff_101
  recurrence4A2_coeff_102
  recurrence4A2_coeff_103
  recurrence4A2_coeff_104
  recurrence4A2_coeff_105
  recurrence4A2_coeff_106
  recurrence4A2_coeff_107
  recurrence4A2_coeff_108
  recurrence4A2_coeff_109
  recurrence4A2_coeff_11
  recurrence4A2_coeff_110
  recurrence4A2_coeff_111
  recurrence4A2_coeff_112
  recurrence4A2_coeff_113
  recurrence4A2_coeff_114
  recurrence4A2_coeff_115
  recurrence4A2_coeff_116
  recurrence4A2_coeff_117
  recurrence4A2_coeff_118
  recurrence4A2_coeff_119
  recurrence4A2_coeff_12
  recurrence4A2_coeff_120
  recurrence4A2_coeff_121
  recurrence4A2_coeff_122
  recurrence4A2_coeff_123
  recurrence4A2_coeff_124
  recurrence4A2_coeff_125
  recurrence4A2_coeff_126
  recurrence4A2_coeff_127
  recurrence4A2_coeff_128
  recurrence4A2_coeff_129
  recurrence4A2_coeff_13
  recurrence4A2_coeff_130
  recurrence4A2_coeff_131
  recurrence4A2_coeff_132
  recurrence4A2_coeff_133
  recurrence4A2_coeff_134
  recurrence4A2_coeff_135
  recurrence4A2_coeff_136
  recurrence4A2_coeff_137
  recurrence4A2_coeff_138
  recurrence4A2_coeff_139
  recurrence4A2_coeff_14
  recurrence4A2_coeff_140
  recurrence4A2_coeff_141
  recurrence4A2_coeff_142
  recurrence4A2_coeff_143
  recurrence4A2_coeff_144
  recurrence4A2_coeff_145
  recurrence4A2_coeff_146
  recurrence4A2_coeff_147
  recurrence4A2_coeff_148
  recurrence4A2_coeff_149
  recurrence4A2_coeff_15
  recurrence4A2_coeff_150
  recurrence4A2_coeff_151
  recurrence4A2_coeff_152
  recurrence4A2_coeff_153
  recurrence4A2_coeff_154
  recurrence4A2_coeff_155

attribute [local simp]
  recurrence4A2_coeff_156
  recurrence4A2_coeff_157
  recurrence4A2_coeff_158
  recurrence4A2_coeff_159
  recurrence4A2_coeff_16
  recurrence4A2_coeff_160
  recurrence4A2_coeff_161
  recurrence4A2_coeff_162
  recurrence4A2_coeff_163
  recurrence4A2_coeff_164
  recurrence4A2_coeff_165
  recurrence4A2_coeff_166
  recurrence4A2_coeff_167
  recurrence4A2_coeff_168
  recurrence4A2_coeff_169
  recurrence4A2_coeff_17
  recurrence4A2_coeff_170
  recurrence4A2_coeff_171
  recurrence4A2_coeff_172
  recurrence4A2_coeff_173
  recurrence4A2_coeff_174
  recurrence4A2_coeff_175
  recurrence4A2_coeff_176
  recurrence4A2_coeff_177
  recurrence4A2_coeff_178
  recurrence4A2_coeff_179
  recurrence4A2_coeff_18
  recurrence4A2_coeff_180
  recurrence4A2_coeff_181
  recurrence4A2_coeff_182
  recurrence4A2_coeff_183
  recurrence4A2_coeff_184
  recurrence4A2_coeff_185
  recurrence4A2_coeff_186
  recurrence4A2_coeff_19
  recurrence4A2_coeff_2
  recurrence4A2_coeff_20
  recurrence4A2_coeff_21
  recurrence4A2_coeff_22
  recurrence4A2_coeff_23
  recurrence4A2_coeff_24
  recurrence4A2_coeff_25
  recurrence4A2_coeff_26
  recurrence4A2_coeff_27
  recurrence4A2_coeff_28
  recurrence4A2_coeff_29
  recurrence4A2_coeff_3
  recurrence4A2_coeff_30
  recurrence4A2_coeff_31
  recurrence4A2_coeff_32
  recurrence4A2_coeff_33
  recurrence4A2_coeff_34
  recurrence4A2_coeff_35
  recurrence4A2_coeff_36
  recurrence4A2_coeff_37
  recurrence4A2_coeff_38
  recurrence4A2_coeff_39
  recurrence4A2_coeff_4
  recurrence4A2_coeff_40
  recurrence4A2_coeff_41
  recurrence4A2_coeff_42
  recurrence4A2_coeff_43
  recurrence4A2_coeff_44
  recurrence4A2_coeff_45

attribute [local simp]
  recurrence4A2_coeff_46
  recurrence4A2_coeff_47
  recurrence4A2_coeff_48
  recurrence4A2_coeff_49
  recurrence4A2_coeff_5
  recurrence4A2_coeff_50
  recurrence4A2_coeff_51
  recurrence4A2_coeff_52
  recurrence4A2_coeff_53
  recurrence4A2_coeff_54
  recurrence4A2_coeff_55
  recurrence4A2_coeff_56
  recurrence4A2_coeff_57
  recurrence4A2_coeff_58
  recurrence4A2_coeff_59
  recurrence4A2_coeff_6
  recurrence4A2_coeff_60
  recurrence4A2_coeff_61
  recurrence4A2_coeff_62
  recurrence4A2_coeff_63
  recurrence4A2_coeff_64
  recurrence4A2_coeff_65
  recurrence4A2_coeff_66
  recurrence4A2_coeff_67
  recurrence4A2_coeff_68
  recurrence4A2_coeff_69
  recurrence4A2_coeff_7
  recurrence4A2_coeff_70
  recurrence4A2_coeff_71
  recurrence4A2_coeff_72
  recurrence4A2_coeff_73
  recurrence4A2_coeff_74
  recurrence4A2_coeff_75
  recurrence4A2_coeff_76
  recurrence4A2_coeff_77
  recurrence4A2_coeff_78
  recurrence4A2_coeff_79
  recurrence4A2_coeff_8
  recurrence4A2_coeff_80
  recurrence4A2_coeff_81
  recurrence4A2_coeff_82
  recurrence4A2_coeff_83
  recurrence4A2_coeff_84
  recurrence4A2_coeff_85
  recurrence4A2_coeff_86
  recurrence4A2_coeff_87
  recurrence4A2_coeff_88
  recurrence4A2_coeff_89
  recurrence4A2_coeff_9
  recurrence4A2_coeff_90
  recurrence4A2_coeff_91
  recurrence4A2_coeff_92
  recurrence4A2_coeff_93
  recurrence4A2_coeff_94
  recurrence4A2_coeff_95
  recurrence4A2_coeff_96
  recurrence4A2_coeff_97
  recurrence4A2_coeff_98
  recurrence4A2_coeff_99
  recurrence4LeadingSquare_coeff_0
  recurrence4LeadingSquare_coeff_1
  recurrence4LeadingSquare_coeff_10
  recurrence4LeadingSquare_coeff_100
  recurrence4LeadingSquare_coeff_101

attribute [local simp]
  recurrence4LeadingSquare_coeff_102
  recurrence4LeadingSquare_coeff_103
  recurrence4LeadingSquare_coeff_104
  recurrence4LeadingSquare_coeff_105
  recurrence4LeadingSquare_coeff_106
  recurrence4LeadingSquare_coeff_107
  recurrence4LeadingSquare_coeff_108
  recurrence4LeadingSquare_coeff_109
  recurrence4LeadingSquare_coeff_11
  recurrence4LeadingSquare_coeff_110
  recurrence4LeadingSquare_coeff_111
  recurrence4LeadingSquare_coeff_112
  recurrence4LeadingSquare_coeff_113
  recurrence4LeadingSquare_coeff_114
  recurrence4LeadingSquare_coeff_115
  recurrence4LeadingSquare_coeff_116
  recurrence4LeadingSquare_coeff_117
  recurrence4LeadingSquare_coeff_118
  recurrence4LeadingSquare_coeff_119
  recurrence4LeadingSquare_coeff_12
  recurrence4LeadingSquare_coeff_120
  recurrence4LeadingSquare_coeff_121
  recurrence4LeadingSquare_coeff_122
  recurrence4LeadingSquare_coeff_123
  recurrence4LeadingSquare_coeff_124
  recurrence4LeadingSquare_coeff_125
  recurrence4LeadingSquare_coeff_126
  recurrence4LeadingSquare_coeff_127
  recurrence4LeadingSquare_coeff_128
  recurrence4LeadingSquare_coeff_129
  recurrence4LeadingSquare_coeff_13
  recurrence4LeadingSquare_coeff_130
  recurrence4LeadingSquare_coeff_131
  recurrence4LeadingSquare_coeff_132
  recurrence4LeadingSquare_coeff_133
  recurrence4LeadingSquare_coeff_134
  recurrence4LeadingSquare_coeff_135
  recurrence4LeadingSquare_coeff_136
  recurrence4LeadingSquare_coeff_137
  recurrence4LeadingSquare_coeff_138
  recurrence4LeadingSquare_coeff_139
  recurrence4LeadingSquare_coeff_14
  recurrence4LeadingSquare_coeff_140
  recurrence4LeadingSquare_coeff_141
  recurrence4LeadingSquare_coeff_142
  recurrence4LeadingSquare_coeff_143
  recurrence4LeadingSquare_coeff_144
  recurrence4LeadingSquare_coeff_145
  recurrence4LeadingSquare_coeff_146
  recurrence4LeadingSquare_coeff_147
  recurrence4LeadingSquare_coeff_148
  recurrence4LeadingSquare_coeff_149
  recurrence4LeadingSquare_coeff_15
  recurrence4LeadingSquare_coeff_150
  recurrence4LeadingSquare_coeff_151
  recurrence4LeadingSquare_coeff_152
  recurrence4LeadingSquare_coeff_153
  recurrence4LeadingSquare_coeff_154
  recurrence4LeadingSquare_coeff_155
  recurrence4LeadingSquare_coeff_156
  recurrence4LeadingSquare_coeff_157
  recurrence4LeadingSquare_coeff_158
  recurrence4LeadingSquare_coeff_159
  recurrence4LeadingSquare_coeff_16

attribute [local simp]
  recurrence4LeadingSquare_coeff_160
  recurrence4LeadingSquare_coeff_161
  recurrence4LeadingSquare_coeff_162
  recurrence4LeadingSquare_coeff_163
  recurrence4LeadingSquare_coeff_164
  recurrence4LeadingSquare_coeff_165
  recurrence4LeadingSquare_coeff_166
  recurrence4LeadingSquare_coeff_167
  recurrence4LeadingSquare_coeff_168
  recurrence4LeadingSquare_coeff_169
  recurrence4LeadingSquare_coeff_17
  recurrence4LeadingSquare_coeff_170
  recurrence4LeadingSquare_coeff_171
  recurrence4LeadingSquare_coeff_172
  recurrence4LeadingSquare_coeff_173
  recurrence4LeadingSquare_coeff_174
  recurrence4LeadingSquare_coeff_175
  recurrence4LeadingSquare_coeff_176
  recurrence4LeadingSquare_coeff_177
  recurrence4LeadingSquare_coeff_178
  recurrence4LeadingSquare_coeff_179
  recurrence4LeadingSquare_coeff_18
  recurrence4LeadingSquare_coeff_180
  recurrence4LeadingSquare_coeff_181
  recurrence4LeadingSquare_coeff_182
  recurrence4LeadingSquare_coeff_183
  recurrence4LeadingSquare_coeff_184
  recurrence4LeadingSquare_coeff_185
  recurrence4LeadingSquare_coeff_186
  recurrence4LeadingSquare_coeff_187
  recurrence4LeadingSquare_coeff_188
  recurrence4LeadingSquare_coeff_189
  recurrence4LeadingSquare_coeff_19
  recurrence4LeadingSquare_coeff_190
  recurrence4LeadingSquare_coeff_191
  recurrence4LeadingSquare_coeff_192
  recurrence4LeadingSquare_coeff_193
  recurrence4LeadingSquare_coeff_194
  recurrence4LeadingSquare_coeff_195
  recurrence4LeadingSquare_coeff_196
  recurrence4LeadingSquare_coeff_197
  recurrence4LeadingSquare_coeff_198
  recurrence4LeadingSquare_coeff_199
  recurrence4LeadingSquare_coeff_2
  recurrence4LeadingSquare_coeff_20
  recurrence4LeadingSquare_coeff_200
  recurrence4LeadingSquare_coeff_201
  recurrence4LeadingSquare_coeff_202
  recurrence4LeadingSquare_coeff_203
  recurrence4LeadingSquare_coeff_204
  recurrence4LeadingSquare_coeff_205
  recurrence4LeadingSquare_coeff_206
  recurrence4LeadingSquare_coeff_207
  recurrence4LeadingSquare_coeff_208
  recurrence4LeadingSquare_coeff_209
  recurrence4LeadingSquare_coeff_21
  recurrence4LeadingSquare_coeff_210
  recurrence4LeadingSquare_coeff_211
  recurrence4LeadingSquare_coeff_212
  recurrence4LeadingSquare_coeff_213
  recurrence4LeadingSquare_coeff_214
  recurrence4LeadingSquare_coeff_215
  recurrence4LeadingSquare_coeff_216
  recurrence4LeadingSquare_coeff_217

attribute [local simp]
  recurrence4LeadingSquare_coeff_218
  recurrence4LeadingSquare_coeff_219
  recurrence4LeadingSquare_coeff_22
  recurrence4LeadingSquare_coeff_220
  recurrence4LeadingSquare_coeff_221
  recurrence4LeadingSquare_coeff_222
  recurrence4LeadingSquare_coeff_223
  recurrence4LeadingSquare_coeff_23
  recurrence4LeadingSquare_coeff_24
  recurrence4LeadingSquare_coeff_25
  recurrence4LeadingSquare_coeff_26
  recurrence4LeadingSquare_coeff_27
  recurrence4LeadingSquare_coeff_28
  recurrence4LeadingSquare_coeff_29
  recurrence4LeadingSquare_coeff_3
  recurrence4LeadingSquare_coeff_30
  recurrence4LeadingSquare_coeff_31
  recurrence4LeadingSquare_coeff_32
  recurrence4LeadingSquare_coeff_33
  recurrence4LeadingSquare_coeff_34
  recurrence4LeadingSquare_coeff_35
  recurrence4LeadingSquare_coeff_36
  recurrence4LeadingSquare_coeff_37
  recurrence4LeadingSquare_coeff_38
  recurrence4LeadingSquare_coeff_39
  recurrence4LeadingSquare_coeff_4
  recurrence4LeadingSquare_coeff_40
  recurrence4LeadingSquare_coeff_41
  recurrence4LeadingSquare_coeff_42
  recurrence4LeadingSquare_coeff_43
  recurrence4LeadingSquare_coeff_44
  recurrence4LeadingSquare_coeff_45
  recurrence4LeadingSquare_coeff_46
  recurrence4LeadingSquare_coeff_47
  recurrence4LeadingSquare_coeff_48
  recurrence4LeadingSquare_coeff_49
  recurrence4LeadingSquare_coeff_5
  recurrence4LeadingSquare_coeff_50
  recurrence4LeadingSquare_coeff_51
  recurrence4LeadingSquare_coeff_52
  recurrence4LeadingSquare_coeff_53
  recurrence4LeadingSquare_coeff_54
  recurrence4LeadingSquare_coeff_55
  recurrence4LeadingSquare_coeff_56
  recurrence4LeadingSquare_coeff_57
  recurrence4LeadingSquare_coeff_58
  recurrence4LeadingSquare_coeff_59
  recurrence4LeadingSquare_coeff_6
  recurrence4LeadingSquare_coeff_60
  recurrence4LeadingSquare_coeff_61
  recurrence4LeadingSquare_coeff_62
  recurrence4LeadingSquare_coeff_63
  recurrence4LeadingSquare_coeff_64
  recurrence4LeadingSquare_coeff_65
  recurrence4LeadingSquare_coeff_66
  recurrence4LeadingSquare_coeff_67
  recurrence4LeadingSquare_coeff_68
  recurrence4LeadingSquare_coeff_69
  recurrence4LeadingSquare_coeff_7
  recurrence4LeadingSquare_coeff_70
  recurrence4LeadingSquare_coeff_71
  recurrence4LeadingSquare_coeff_72
  recurrence4LeadingSquare_coeff_73
  recurrence4LeadingSquare_coeff_74

attribute [local simp]
  recurrence4LeadingSquare_coeff_75
  recurrence4LeadingSquare_coeff_76
  recurrence4LeadingSquare_coeff_77
  recurrence4LeadingSquare_coeff_78
  recurrence4LeadingSquare_coeff_79
  recurrence4LeadingSquare_coeff_8
  recurrence4LeadingSquare_coeff_80
  recurrence4LeadingSquare_coeff_81
  recurrence4LeadingSquare_coeff_82
  recurrence4LeadingSquare_coeff_83
  recurrence4LeadingSquare_coeff_84
  recurrence4LeadingSquare_coeff_85
  recurrence4LeadingSquare_coeff_86
  recurrence4LeadingSquare_coeff_87
  recurrence4LeadingSquare_coeff_88
  recurrence4LeadingSquare_coeff_89
  recurrence4LeadingSquare_coeff_9
  recurrence4LeadingSquare_coeff_90
  recurrence4LeadingSquare_coeff_91
  recurrence4LeadingSquare_coeff_92
  recurrence4LeadingSquare_coeff_93
  recurrence4LeadingSquare_coeff_94
  recurrence4LeadingSquare_coeff_95
  recurrence4LeadingSquare_coeff_96
  recurrence4LeadingSquare_coeff_97
  recurrence4LeadingSquare_coeff_98
  recurrence4LeadingSquare_coeff_99

theorem recurrence4Scalar2Left_coeff_158 :
    recurrence4Scalar2Left.coeff 158 =
      (((((56 * 10 ^ 70 +
        6602234807461048838365660753268266471014958582573746938975051409983092) * 10 ^ 70 +
        9898254968579238437619258742522275674137042661891563682560219285682569) * 10 ^ 70 +
        5538264277288728731734171654495304548211263721955907605458986268352663) * 10 ^ 70 +
        8539396837192802109822972697098380885972314417747581971305328911589608) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 159,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (158 - x)) = _
  rw [show 159 = 0 +
    159 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
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
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Left_coeff_159 :
    recurrence4Scalar2Left.coeff 159 =
      -(((((211 * 10 ^ 70 +
        9177025983972570504704063482862915856374056525033648803802134727355268) * 10 ^ 70 +
        2189846903037854890532924619139394362305484081755958987791054907502222) * 10 ^ 70 +
        0680033689913571229064580988398628758182677679211237944312823179594920) * 10 ^ 70 +
        2782740530661817696253568239014584171143212051107815361316688361551374) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 160,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (159 - x)) = _
  rw [show 160 = 0 +
    160 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 160 = 32 +
      128 by norm_num, Finset.sum_range_add]
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
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Left_coeff_160 :
    recurrence4Scalar2Left.coeff 160 =
      (((((779 * 10 ^ 70 +
        9943414229728036322621805506066282900972847553426712366495439157180994) * 10 ^ 70 +
        4107479593401394896725224084440088509486330931545627454138069546213931) * 10 ^ 70 +
        2971812363958023420281970468996377231683744457698690401623760194356491) * 10 ^ 70 +
        4614026239481282552482175332391461826015403722301442651386163857992681) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 161,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (160 - x)) = _
  rw [show 161 = 0 +
    161 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 65 = 32 +
      33 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Left_coeff_161 :
    recurrence4Scalar2Left.coeff 161 =
      -(((((2825 * 10 ^ 70 +
        4398891237828200239077468392181884185564867044914646013845312883617644) * 10 ^ 70 +
        0900862486934683779636327592584308883036793297498077221222181201874195) * 10 ^ 70 +
        0747457409892810701348628543244125018778589416460936509223298986564427) * 10 ^ 70 +
        3252171386214804843761048211826580116571376271360478125117736289209604) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 162,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (161 - x)) = _
  rw [show 162 = 0 +
    162 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 66 = 32 +
      34 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Left_coeff_162 :
    recurrence4Scalar2Left.coeff 162 =
      (((((10073 * 10 ^ 70 +
        6124641270802831583772904501439673377706248652097876613799350657848500) * 10 ^ 70 +
        5835090415163331412498235055007352258928415475946346980500317758864979) * 10 ^ 70 +
        7395067997675806616022332659142282170385619051140248031223647099109911) * 10 ^ 70 +
        0118993174709696072847231411902920936932735158368066470937751201483684) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 163,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (162 - x)) = _
  rw [show 163 = 0 +
    163 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Left_coeff_163 :
    recurrence4Scalar2Left.coeff 163 =
      -(((((35352 * 10 ^ 70 +
        6616007439792782837082519888640965759340614436438742466616403693200765) * 10 ^ 70 +
        0011210182429182820149732979660787862766221022041530378112242526163521) * 10 ^ 70 +
        4047373898629213467023317351335924169652295883099607169847199967542493) * 10 ^ 70 +
        7355244758555543131354817777324204643842892846284828299005321191391588) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 164,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (163 - x)) = _
  rw [show 164 = 0 +
    164 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 68 = 32 +
      36 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Left_coeff_164 :
    recurrence4Scalar2Left.coeff 164 =
      (((((122131 * 10 ^ 70 +
        8421882186051354335206094945947441859703568355761733144416095470023640) * 10 ^ 70 +
        3248308108632928469422604077791895214107079017764014258935346493366172) * 10 ^ 70 +
        4490527793783041138211131616050293764715471251364983591866550552107967) * 10 ^ 70 +
        8689723088772279742687274694410374447482448528721302477593183088846001) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 165,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (164 - x)) = _
  rw [show 165 = 0 +
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
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Left_coeff_165 :
    recurrence4Scalar2Left.coeff 165 =
      -(((((415371 * 10 ^ 70 +
        6808598996206970753704523309469328250340290671090465887013423324163335) * 10 ^ 70 +
        4049044811697322053457391564399809460741637056576194560170579284187682) * 10 ^ 70 +
        9610046987572770507763630446463618924014304975110085748865806474581733) * 10 ^ 70 +
        8806549214200826763146199853377851389479183208352004298772265189327665) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 166,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (165 - x)) = _
  rw [show 166 = 0 +
    166 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 70 = 32 +
      38 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Left_coeff_166 :
    recurrence4Scalar2Left.coeff 166 =
      (((((1390837 * 10 ^ 70 +
        5214608046898660907391609291141060211717174631329148041946428671091450) * 10 ^ 70 +
        8905421157699629734726849830508079816758170007420615567511445483319890) * 10 ^ 70 +
        5143598775615148118197052363560990255792196845177419715995678322203935) * 10 ^ 70 +
        0190646328201038150210443030435662935739523989960850554956063399659050) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 167,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (166 - x)) = _
  rw [show 167 = 0 +
    167 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Left_coeff_167 :
    recurrence4Scalar2Left.coeff 167 =
      -(((((4585396 * 10 ^ 70 +
        6510416368421928858450817088384672226832429489613710023698337749738999) * 10 ^ 70 +
        9345083985989080609833927713290443794124318666165499163163632935630402) * 10 ^ 70 +
        2160818571318678985834265063320263660643471683378616347347791422670420) * 10 ^ 70 +
        6636969795852454388494978074532141348249753170195623728888861201934868) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 168,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (167 - x)) = _
  rw [show 168 = 0 +
    168 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 72 = 32 +
      40 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Left_coeff_168 :
    recurrence4Scalar2Left.coeff 168 =
      (((((14885622 * 10 ^ 70 +
        4130080461682958391464355822920826526028435390810959551616409783333614) * 10 ^ 70 +
        7666567069083428690848067087111833380155954841390438115388772893647685) * 10 ^ 70 +
        1103820877955763074972904827406697893265399593443329730603522595817751) * 10 ^ 70 +
        1502076954524890744455590954014475460669328311091002523305137383666143) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 169,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (168 - x)) = _
  rw [show 169 = 0 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 73 = 32 +
      41 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Left_coeff_169 :
    recurrence4Scalar2Left.coeff 169 =
      -(((((47585472 * 10 ^ 70 +
        7525031231259433875308113006125022355493825698752652934012537507452535) * 10 ^ 70 +
        3688934449697434308135592764226822911700259737738662837812852385627694) * 10 ^ 70 +
        9911456408980001082194794269149256888654870759241769297268795113259151) * 10 ^ 70 +
        3534648548824913788631863533812002763056465333569328987486321420501881) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 170,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (169 - x)) = _
  rw [show 170 = 0 +
    170 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 74 = 32 +
      42 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Left_coeff_170 :
    recurrence4Scalar2Left.coeff 170 =
      (((((149804879 * 10 ^ 70 +
        6580156606518226539973157608660353892749229031055061734000694135344872) * 10 ^ 70 +
        8557530488504739440619376657922137403386809873696275093784855818108907) * 10 ^ 70 +
        1303545078644921818696457139445144771662556255282934989528131022289810) * 10 ^ 70 +
        4734884366136699353411052961763314055902251595303579194453102296412757) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 171,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (170 - x)) = _
  rw [show 171 = 0 +
    171 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Left_coeff_171 :
    recurrence4Scalar2Left.coeff 171 =
      -(((((464459414 * 10 ^ 70 +
        4389675184267077371446028501900242244017682715732326381392777464233685) * 10 ^ 70 +
        2081444928684278462002296496458956826051764017936054346246509424074807) * 10 ^ 70 +
        0910517109651311099785668201165638194663725054600510857109857672661712) * 10 ^ 70 +
        5848964243448120238754276464607287945973280864792910291902995674382603) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 172,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (171 - x)) = _
  rw [show 172 = 0 +
    172 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 76 = 32 +
      44 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Left_coeff_172 :
    recurrence4Scalar2Left.coeff 172 =
      (((((1418290084 * 10 ^ 70 +
        5045119954465286382776794275182864393768115586163054331758133054400568) * 10 ^ 70 +
        9073092756869077177994795597438058113197319338095919562799315292226336) * 10 ^ 70 +
        4378271241806574336327538672508589556942641159959916133453277616052684) * 10 ^ 70 +
        2259991371909429822401346665789932395710544221451698834252190719620186) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 173,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (172 - x)) = _
  rw [show 173 = 0 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Left_coeff_173 :
    recurrence4Scalar2Left.coeff 173 =
      -(((((4265817808 * 10 ^ 70 +
        7861658944269470689717044064153186832376743397390939019195469979017411) * 10 ^ 70 +
        2322942797387734740025640077159359452218264017422320510888427430932378) * 10 ^ 70 +
        9881929543551724821670573283397301072494315444832519245422068245474421) * 10 ^ 70 +
        4811794669302902601764198772709889965333139642165648851343277046002336) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 174,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (173 - x)) = _
  rw [show 174 = 0 +
    174 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 78 = 32 +
      46 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Left_coeff_174 :
    recurrence4Scalar2Left.coeff 174 =
      (((((12638139755 * 10 ^ 70 +
        4891487460306863203374125591631231424844721896187962189224796825614835) * 10 ^ 70 +
        3036780705436949170974937829305223776238317035877651518356165121993830) * 10 ^ 70 +
        4265452158159563896936201420894092054985585193784370643929539099838715) * 10 ^ 70 +
        3915114805249258960146642571907754286024465875171049127882703114778418) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 175,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (174 - x)) = _
  rw [show 175 = 0 +
    175 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Left_coeff_175 :
    recurrence4Scalar2Left.coeff 175 =
      -(((((36883364205 * 10 ^ 70 +
        0390433235303856281258687416133616572545066882472671696203698441027996) * 10 ^ 70 +
        5297062551799263627588027054417982367900133631354267694048042972921633) * 10 ^ 70 +
        4710694620342573851233689704133663093953219348093871985961927875437341) * 10 ^ 70 +
        6691280554381555406687744235325689987280360686337147601155430488840023) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 176,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (175 - x)) = _
  rw [show 176 = 0 +
    176 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 80 = 32 +
      48 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Left_coeff_176 :
    recurrence4Scalar2Left.coeff 176 =
      (((((106039233308 * 10 ^ 70 +
        1801668450727077561988696852355267887104833623965802319495337016859090) * 10 ^ 70 +
        7111070317188100088697194441095669209579071518257125512804709675706869) * 10 ^ 70 +
        3482734541723016090375445498806640684307508244516521365706425940379028) * 10 ^ 70 +
        6161616286153261867300678769296507999142892742654497394554111452327276) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 177,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (176 - x)) = _
  rw [show 177 = 0 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Left_coeff_177 :
    recurrence4Scalar2Left.coeff 177 =
      -(((((300339687288 * 10 ^ 70 +
        3100339352170976638508068687216349541696347222792884485541119168961188) * 10 ^ 70 +
        0145568120655604782876186227927208996502906001137898753783529530787907) * 10 ^ 70 +
        7218434908546727687134697183007460696568315579826254944497905810565126) * 10 ^ 70 +
        2103294547369496449143137557201101671643396340084209955537399528654924) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 178,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (177 - x)) = _
  rw [show 178 = 0 +
    178 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Left_coeff_178 :
    recurrence4Scalar2Left.coeff 178 =
      (((((838088049676 * 10 ^ 70 +
        6960653288051829836131858913333293030377420738761668145511081798128514) * 10 ^ 70 +
        0711799290094133858468868696036707070332026979597837851423193168242981) * 10 ^ 70 +
        3076432658167346224408185545614955676823977693074501360011856163660050) * 10 ^ 70 +
        9510371267277561083974752712146868865906534602997869971219615713709969) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 179,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (178 - x)) = _
  rw [show 179 = 0 +
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
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Left_coeff_179 :
    recurrence4Scalar2Left.coeff 179 =
      -(((((2304184850638 * 10 ^ 70 +
        7388114614755980921931413542257494806559478893247667196733234468863080) * 10 ^ 70 +
        9788192883041710299504862318108060540352132697521591040009401555285536) * 10 ^ 70 +
        0855801327759580369341459566694568411695927729897181695222281478761506) * 10 ^ 70 +
        0787135835419223462612650313774033578062948107421734295039552704341288) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 180,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (179 - x)) = _
  rw [show 180 = 0 +
    180 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 84 = 32 +
      52 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Left_coeff_180 :
    recurrence4Scalar2Left.coeff 180 =
      (((((6241873863135 * 10 ^ 70 +
        9695772020518217520477363069605463605358848808820431158601627958573561) * 10 ^ 70 +
        8849778729440670430186887126821175462065325152110471472776135631688361) * 10 ^ 70 +
        1188619899451302420765205018511658409106865852852690196607270639315013) * 10 ^ 70 +
        8072858534861610054337153746553914030687475527120794646000876818269182) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 181,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (180 - x)) = _
  rw [show 181 = 0 +
    181 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Left_coeff_181 :
    recurrence4Scalar2Left.coeff 181 =
      -(((((16661005925268 * 10 ^ 70 +
        4604274931627971881616356252655308213165927115704022996609031935619698) * 10 ^ 70 +
        9268998075959981799574916633320096485561364517353994078064108684286680) * 10 ^ 70 +
        8661407386244453607229925611757650292520306188728528994565291083555823) * 10 ^ 70 +
        7708160014198739145086602440312793034404451911480395687415494199012256) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 182,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (181 - x)) = _
  rw [show 182 = 0 +
    182 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Left_coeff_182 :
    recurrence4Scalar2Left.coeff 182 =
      (((((43822169501249 * 10 ^ 70 +
        6256594626385258820181063357266558411674925552916176733195131343712045) * 10 ^ 70 +
        2027679663671228470181405120017841275853639560382547514526418520646667) * 10 ^ 70 +
        8054518236155759028703645603483188930305465719314483944509421972241609) * 10 ^ 70 +
        2224288855143786750316762160213854610558715248060818779281791455980209) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 183,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (182 - x)) = _
  rw [show 183 = 0 +
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
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Left_coeff_183 :
    recurrence4Scalar2Left.coeff 183 =
      -(((((113582163107219 * 10 ^ 70 +
        6968318931007580075409845081028362909808622491401416524519307359478521) * 10 ^ 70 +
        2857414989371466189892691148836432370281065621032527798885408739817351) * 10 ^ 70 +
        6206284052951645967225186172411336506885197589073400696656236526557026) * 10 ^ 70 +
        9663241426287184915625374552259729791047717824294584819444405161416462) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 184,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (183 - x)) = _
  rw [show 184 = 0 +
    184 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 88 = 32 +
      56 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Left_coeff_184 :
    recurrence4Scalar2Left.coeff 184 =
      (((((290112541929000 * 10 ^ 70 +
        1543863206339278677678707446991841973724709619119354897233934666905700) * 10 ^ 70 +
        5040359546187365539718570981123616930996753145043674383615610869919526) * 10 ^ 70 +
        1189415434107932220921849846658759063582724973101925075583516572863071) * 10 ^ 70 +
        0277292996316434749760861674104817651780320271461075406203356277408418) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 185,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (184 - x)) = _
  rw [show 185 = 0 +
    185 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Left_coeff_185 :
    recurrence4Scalar2Left.coeff 185 =
      -(((((730262183491797 * 10 ^ 70 +
        5420317713874676626918747180008920400358003301673159836773180740244247) * 10 ^ 70 +
        1646836608805191966982049864578006740049875605171353406607771450636183) * 10 ^ 70 +
        9419105937685423012873043075377991018976671977990555244334391333212707) * 10 ^ 70 +
        9242453767295567069628404988185435502403110043379072835881482689176379) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 186,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (185 - x)) = _
  rw [show 186 = 0 +
    186 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Left_coeff_186 :
    recurrence4Scalar2Left.coeff 186 =
      (((((1811599610756624 * 10 ^ 70 +
        3882171581438688885367518253217136046453786494936763194968072070407520) * 10 ^ 70 +
        7299658035227502181547000497698829283107947588719371015138720217671424) * 10 ^ 70 +
        5810784102380175070901969748704096542847266765902117776179899890217692) * 10 ^ 70 +
        8620088429151773409024817095009625239080926800767186232838386161855346) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 187,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (186 - x)) = _
  rw [show 187 = 0 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 91 = 32 +
      59 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (187 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_187 :
    recurrence4Scalar2Left.coeff 187 =
      -(((((4429260511314907 * 10 ^ 70 +
        3921888613912083922424766584194996615695987052191236320130256566323704) * 10 ^ 70 +
        0336807653056114540754290564926777655752585129855835943022903966896688) * 10 ^ 70 +
        0411025301312997626863343134962743617003222660233725058942581728569075) * 10 ^ 70 +
        0261123922245601714219819998995336883008497095597574655737917694700890) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 188,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (187 - x)) = _
  rw [show 188 = 1 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 91 = 32 +
      59 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_187_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (188 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_188 :
    recurrence4Scalar2Left.coeff 188 =
      (((((10673323324514664 * 10 ^ 70 +
        9610320197350452788636172938731884927068565489793556485266021651055176) * 10 ^ 70 +
        1582562317606527943335976575717088452497030535637384025111409360120614) * 10 ^ 70 +
        0739097736945505084820822470595583031846012412316838905514300699693504) * 10 ^ 70 +
        0170154974095162202535692386421715635545083895759249896092184630863339) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 189,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (188 - x)) = _
  rw [show 189 = 2 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 91 = 32 +
      59 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_188_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (189 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_189 :
    recurrence4Scalar2Left.coeff 189 =
      -(((((25350160852196087 * 10 ^ 70 +
        1175471276862741672146065555412335337243872234753900363289743343360475) * 10 ^ 70 +
        1691386667786483543984857539811165697146385309394785810795913975332169) * 10 ^ 70 +
        7478831977385463463302413291112159449184687348888172616038629820584602) * 10 ^ 70 +
        9857020984421708939523874081058281974563280016596053922481528862112033) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 190,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (189 - x)) = _
  rw [show 190 = 3 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 91 = 32 +
      59 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_189_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (190 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_190 :
    recurrence4Scalar2Left.coeff 190 =
      (((((59345378524754538 * 10 ^ 70 +
        5606142198742005212797115135372066813434754864499777654328954422143473) * 10 ^ 70 +
        2716102936826538909947267332163696707203825579498305819706109068137048) * 10 ^ 70 +
        4420642310755533355478390958681936282214159251131261989536162352116292) * 10 ^ 70 +
        7753650833276428614431044328439948584805522376758021696808102411285848) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 191,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (190 - x)) = _
  rw [show 191 = 4 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 91 = 32 +
      59 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_190_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (191 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_191 :
    recurrence4Scalar2Left.coeff 191 =
      -(((((136939923055145526 * 10 ^ 70 +
        2427692991583306979876123138929150451947044068690014097884678271148321) * 10 ^ 70 +
        5183856625259795973967021719703809633049740615999640927688765435398187) * 10 ^ 70 +
        8374125303176151856308955067697039697029478519958463215613695068991172) * 10 ^ 70 +
        0872718775039336723257124261629579685821417028050224232777124481802593) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 192,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (191 - x)) = _
  rw [show 192 = 5 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 91 = 32 +
      59 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_191_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (192 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_192 :
    recurrence4Scalar2Left.coeff 192 =
      (((((311473744170595156 * 10 ^ 70 +
        2688427816357906881628829527928040328908455859659116313678960021207790) * 10 ^ 70 +
        2745242107722619691211596899629775694245847165812008374664757313265306) * 10 ^ 70 +
        0816918767561123387791252722000996679621026865497462150434304396523837) * 10 ^ 70 +
        2730671902797236474261024455054137278346759013301490688248281665170415) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 193,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (192 - x)) = _
  rw [show 193 = 6 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 91 = 32 +
      59 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_192_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (193 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_193 :
    recurrence4Scalar2Left.coeff 193 =
      -(((((698347416559014457 * 10 ^ 70 +
        6375930517575573132893181621394399231800639934895937633869318407243289) * 10 ^ 70 +
        9978750165558514306698264511819436507573391232049770761289171824478963) * 10 ^ 70 +
        9525503259912752602810007380759332306418510691810066251204815299283682) * 10 ^ 70 +
        3016928882408511721663151492150021059062551537677296669797529328337172) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 194,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (193 - x)) = _
  rw [show 194 = 7 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 91 = 32 +
      59 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_193_prefix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
