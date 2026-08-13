/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupExceptionalProduct
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupC0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar0ExceptionalPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar0Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
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
  recurrence2C0_coeff_0
  recurrence2C0_coeff_1
  recurrence2C0_coeff_2
  recurrence2C0_coeff_3
  recurrence2C0_coeff_4
  recurrence2C0_coeff_5
  recurrence2C0_coeff_6
  recurrence2C0_coeff_7
  recurrence2C0_coeff_8
  recurrence2C0_coeff_9
  recurrence2C0_coeff_10
  recurrence2C0_coeff_11
  recurrence2C0_coeff_12
  recurrence2C0_coeff_13
  recurrence2C0_coeff_14
  recurrence2C0_coeff_15
  recurrence2C0_coeff_16
  recurrence2C0_coeff_17
  recurrence2C0_coeff_18
  recurrence2C0_coeff_19
  recurrence2C0_coeff_20
  recurrence2C0_coeff_21
  recurrence2C0_coeff_22
  recurrence2C0_coeff_23
  recurrence2C0_coeff_24
  recurrence2C0_coeff_25
  recurrence2C0_coeff_26
  recurrence2C0_coeff_27
  recurrence2C0_coeff_28
  recurrence2C0_coeff_29
  recurrence2C0_coeff_30
  recurrence2C0_coeff_31
  recurrence2C0_coeff_32
  recurrence2C0_coeff_33
  recurrence2C0_coeff_34
  recurrence2C0_coeff_35
  recurrence2C0_coeff_36
  recurrence2C0_coeff_37
  recurrence2C0_coeff_38
  recurrence2C0_coeff_39
  recurrence2C0_coeff_40
  recurrence2C0_coeff_41
  recurrence2C0_coeff_42
  recurrence2C0_coeff_43
  recurrence2C0_coeff_44
  recurrence2C0_coeff_45
  recurrence2C0_coeff_46
  recurrence2C0_coeff_47
  recurrence2C0_coeff_48
  recurrence2C0_coeff_49
  recurrence2C0_coeff_50
  recurrence2C0_coeff_51
  recurrence2C0_coeff_52
  recurrence2C0_coeff_53
  recurrence2C0_coeff_54
  recurrence2C0_coeff_55
  recurrence2C0_coeff_56
  recurrence2C0_coeff_57
  recurrence2C0_coeff_58
  recurrence2C0_coeff_59
  recurrence2C0_coeff_60
  recurrence2C0_coeff_61
  recurrence2C0_coeff_62
  recurrence2C0_coeff_63
  recurrence2C0_coeff_64
  recurrence2C0_coeff_65
  recurrence2C0_coeff_66
  recurrence2C0_coeff_67
  recurrence2C0_coeff_68
  recurrence2C0_coeff_69
  recurrence2C0_coeff_70
  recurrence2C0_coeff_71
  recurrence2C0_coeff_72
  recurrence2C0_coeff_73
  recurrence2C0_coeff_74
  recurrence2C0_coeff_75
  recurrence2C0_coeff_76
  recurrence2C0_coeff_77
  recurrence2C0_coeff_78
  recurrence2C0_coeff_79
  recurrence2C0_coeff_80
  recurrence2C0_coeff_81
  recurrence2C0_coeff_82
  recurrence2C0_coeff_83
  recurrence2C0_coeff_84
  recurrence2C0_coeff_85
  recurrence2C0_coeff_86
  recurrence2C0_coeff_87
  recurrence2C0_coeff_88
  recurrence2C0_coeff_89
  recurrence2C0_coeff_90
  recurrence2C0_coeff_91
  recurrence2C0_coeff_92
  recurrence2C0_coeff_93
  recurrence2C0_coeff_94
  recurrence2C0_coeff_95
  recurrence2C0_coeff_96
  recurrence2C0_coeff_97
  recurrence2C0_coeff_98
  recurrence2C0_coeff_99
  recurrence2C0_coeff_100
  recurrence2C0_coeff_101
  recurrence2C0_coeff_102
  recurrence2C0_coeff_103
  recurrence2C0_coeff_104
  recurrence2C0_coeff_105
  recurrence2C0_coeff_106
  recurrence2C0_coeff_107
  recurrence2C0_coeff_108
  recurrence2C0_coeff_109
  recurrence2C0_coeff_110
  recurrence2C0_coeff_111
  recurrence2C0_coeff_112
  recurrence2C0_coeff_113
  recurrence2C0_coeff_114
  recurrence2C0_coeff_115
  recurrence2C0_coeff_116
  recurrence2C0_coeff_117
  recurrence2C0_coeff_118
  recurrence2C0_coeff_119
  recurrence2C0_coeff_120
  recurrence2C0_coeff_121
  recurrence2C0_coeff_122
  recurrence2C0_coeff_123
  recurrence2C0_coeff_124
  recurrence2C0_coeff_125
  recurrence2C0_coeff_126
  recurrence2C0_coeff_127
  recurrence2C0_coeff_128
  recurrence2C0_coeff_129
  recurrence2C0_coeff_130
  recurrence2C0_coeff_131
  recurrence2C0_coeff_132
  recurrence2C0_coeff_133
  recurrence2C0_coeff_134
  recurrence2C0_coeff_135
  recurrence2C0_coeff_136
  recurrence2C0_coeff_137
  recurrence2C0_coeff_138
  recurrence2C0_coeff_139
  recurrence2C0_coeff_140
  recurrence2C0_coeff_141
  recurrence2C0_coeff_142
  recurrence2C0_coeff_143
  recurrence2C0_coeff_144
  recurrence2C0_coeff_145
  recurrence2C0_coeff_146
  recurrence2C0_coeff_147
  recurrence2C0_coeff_148
  recurrence2C0_coeff_149
  recurrence2C0_coeff_150
  recurrence2C0_coeff_151
  recurrence2C0_coeff_152
  recurrence2C0_coeff_153
  recurrence2C0_coeff_154
  recurrence2C0_coeff_155
  recurrence2C0_coeff_156
  recurrence2C0_coeff_157
  recurrence2C0_coeff_158
  recurrence2C0_coeff_159
  recurrence2C0_coeff_160
  recurrence2C0_coeff_161
  recurrence2C0_coeff_162
  recurrence2C0_coeff_163
  recurrence2C0_coeff_164
  recurrence2C0_coeff_165
  recurrence2C0_coeff_166
  recurrence2C0_coeff_167
  recurrence2C0_coeff_168
  recurrence2C0_coeff_169
  recurrence2C0_coeff_170
  recurrence2C0_coeff_171
  recurrence2C0_coeff_172
  recurrence2C0_coeff_173
  recurrence2C0_coeff_174
  recurrence2C0_coeff_175
  recurrence2C0_coeff_176
  recurrence2C0_coeff_177
  recurrence2C0_coeff_178
  recurrence2C0_coeff_179
  recurrence2C0_coeff_180
  recurrence2C0_coeff_181
  recurrence2C0_coeff_182
  recurrence2C0_coeff_183
  recurrence2C0_coeff_184
  recurrence2C0_coeff_185
  recurrence2C0_coeff_186
  recurrence2C0_coeff_187
  recurrence2C0_coeff_188
  recurrence2C0_coeff_189
  recurrence2C0_coeff_190
  recurrence2C0_coeff_191
  recurrence2C0_coeff_192
  recurrence2C0_coeff_193
  recurrence2C0_coeff_194

theorem recurrence2Scalar0Exceptional_coeff_154 :
    recurrence2Scalar0Exceptional.coeff 154 =
      (((263567240398064708554890975522478550598769 * 10 ^ 70 +
        3006309159397929498204975957111326434333264493801334735646170614000911) * 10 ^ 70 +
        9696226851781401915004750990844958248110075766691603060025140281378165) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 155 = 0 +
    155 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_155 :
    recurrence2Scalar0Exceptional.coeff 155 =
      (((1688122837758947548030258865020997979049750 * 10 ^ 70 +
        7028512423052191331272847589941692458742229018585985173411135749679822) * 10 ^ 70 +
        9770146517153486254794381322047844237114790266393139403970865124924671) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 156 = 0 +
    156 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 156 = 32 +
      124 by norm_num, Finset.sum_range_add]
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_156 :
    recurrence2Scalar0Exceptional.coeff 156 =
      -(((10569308331471772631944334608603137801240975 * 10 ^ 70 +
        4655655712180185960660089918211625979782775752201416886950716721112743) * 10 ^ 70 +
        7680942551789565344133588106611844310735521403540113447950857314214745) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 157 = 0 +
    157 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 157 = 32 +
      125 by norm_num, Finset.sum_range_add]
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_157 :
    recurrence2Scalar0Exceptional.coeff 157 =
      (((31130762976263721476925566830776756310313013 * 10 ^ 70 +
        3254741843569516971447215582159071312404614717936552379173165504631176) * 10 ^ 70 +
        9328025920664026894010174692455234616343580531670526936132621655264699) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 158 = 0 +
    158 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 158 = 32 +
      126 by norm_num, Finset.sum_range_add]
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_158 :
    recurrence2Scalar0Exceptional.coeff 158 =
      -(((35629719512056277102192394999347451834095489 * 10 ^ 70 +
        9300373050026441735759523827584523454281939464845362488381136265317811) * 10 ^ 70 +
        5031093577901449791492116514877322076697406161278940543311369966659243) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_159 :
    recurrence2Scalar0Exceptional.coeff 159 =
      -(((146351450095604448399675476938601404803147892 * 10 ^ 70 +
        1819631397633507132219663001579199477554706752181298917674523033671175) * 10 ^ 70 +
        1049637863654845779909868593204137688276188712190992699369483539937289) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_160 :
    recurrence2Scalar0Exceptional.coeff 160 =
      (((1016382204647212290582133355280576691927188976 * 10 ^ 70 +
        0998956621846880379329038414733311272014388497383034614216428206666566) * 10 ^ 70 +
        0451771783574104893301865546630744336639839046327638647140350934755026) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_161 :
    recurrence2Scalar0Exceptional.coeff 161 =
      -(((3242178726160392755962240763807339235974733927 * 10 ^ 70 +
        9117711010704037263912018773358239425541409489328983569293002100797834) * 10 ^ 70 +
        0685776384436755378763566737926986954363644509556924980803131618259041) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_162 :
    recurrence2Scalar0Exceptional.coeff 162 =
      (((5270577575450016057497198350547265821132519641 * 10 ^ 70 +
        1589320955565877474107245874989279931169489482551496736006483458728915) * 10 ^ 70 +
        1085818475346884595304626248702000256452790500740742459766465566509085) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_163 :
    recurrence2Scalar0Exceptional.coeff 163 =
      (((5693930089835794806687993580880996969493154732 * 10 ^ 70 +
        2314416838397370522115526275952955514990048140491895061029766261590110) * 10 ^ 70 +
        0492697231217655335375760542202863312794665965910887700349020602796197) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_164 :
    recurrence2Scalar0Exceptional.coeff 164 =
      -(((72935950591219790176731359990317773954189896102 * 10 ^ 70 +
        7283900202195515801044229634802141424751274550220750288514965901783985) * 10 ^ 70 +
        4050972117394372674755854832128228397151452942397979475790321040109333) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_165 :
    recurrence2Scalar0Exceptional.coeff 165 =
      (((279726136319262357386168725555524576951616505431 * 10 ^ 70 +
        4595771855577960881987194849589253990753196123734600055021172331929027) * 10 ^ 70 +
        1360628263259958786847928094218263702346631604774170138370045321546311) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_166 :
    recurrence2Scalar0Exceptional.coeff 166 =
      -(((636071037010116363110942487775618903078956887078 * 10 ^ 70 +
        5100473810935767269169453141489130859588423611658477253964226881047561) * 10 ^ 70 +
        5252345405537927720012853640039608168326276327788866253613019085833214) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_167 :
    recurrence2Scalar0Exceptional.coeff 167 =
      (((515988136577248891100985848218971863669413121554 * 10 ^ 70 +
        9217266090160439330819991357685745561614496128946163895607352898934078) * 10 ^ 70 +
        0669256589316476794329187076226224081358820779567890421070089303632743) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_168 :
    recurrence2Scalar0Exceptional.coeff 168 =
      (((2895364549829434988121072640304427921408127382020 * 10 ^ 70 +
        4851321940534308015115976632568752274691991605833402274840907401883190) * 10 ^ 70 +
        7280207029543208565453304920981226563356331207029177862039329157515024) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_169 :
    recurrence2Scalar0Exceptional.coeff 169 =
      -(((17057905553064127389095033179369482586184569183056 * 10 ^ 70 +
        6607400197545184201395537284227363041808427178365159088232075870674794) * 10 ^ 70 +
        4058534430194518557217734479021970996210339358860125108700740796322192) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_170 :
    recurrence2Scalar0Exceptional.coeff 170 =
      (((53284324812538535046007919117052136247915106170568 * 10 ^ 70 +
        1171290363934980884020338454749920616051050332248632751548013936391110) * 10 ^ 70 +
        3149232683033922928545847427806585084629314828510790669972578962526874) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_171 :
    recurrence2Scalar0Exceptional.coeff 171 =
      -(((106069926122036759188010912914380853692997896813858 * 10 ^ 70 +
        5455312292516404618575818321610897221000751977037510938627465060507724) * 10 ^ 70 +
        8715500155831449824160261849215931162290129373527603571394161119237727) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_172 :
    recurrence2Scalar0Exceptional.coeff 172 =
      (((71469600225565034859081931154387570133965276043157 * 10 ^ 70 +
        9555014297190813807264179312697828329244667335737200990877807613053511) * 10 ^ 70 +
        2840872643171715424244024294895151534851916891829185474292964097670982) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_173 :
    recurrence2Scalar0Exceptional.coeff 173 =
      (((456895367408106373021220173544727255080266195904639 * 10 ^ 70 +
        7515306218395604796090347377394334958266561595349636745201249056914618) * 10 ^ 70 +
        0903347062889878198961584987127726215778544779651262719429123351241161) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_174 :
    recurrence2Scalar0Exceptional.coeff 174 =
      -(((2508231310300954946158571352270046298696936114950357 * 10 ^ 70 +
        9685865304574608240968052837933846340801729244902603897641138803980517) * 10 ^ 70 +
        7065394255965267452652359158438779608895816005301461662704184889752001) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_175 :
    recurrence2Scalar0Exceptional.coeff 175 =
      (((7777226248177319576094109700170250223003544617793319 * 10 ^ 70 +
        3078347541782281526368996063272218542423206345965924757835686701306266) * 10 ^ 70 +
        9601244037455211566410661729309956890944798121649501969070750985429444) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_176 :
    recurrence2Scalar0Exceptional.coeff 176 =
      -(((16847963889825867101987952879606852574164086839401710 * 10 ^ 70 +
        9163095631752163079697839867654750903955248252337144666957234761466712) * 10 ^ 70 +
        8903932402309024317754635291929208403700929952582266838000980625111843) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_177 :
    recurrence2Scalar0Exceptional.coeff 177 =
      (((21713995774241009355411167740708398808213878457818332 * 10 ^ 70 +
        7569359434553917725542066056657379456457706963438258785085655488260104) * 10 ^ 70 +
        6608824586330354253709241806560704579104371087036129982785769879258423) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_178 :
    recurrence2Scalar0Exceptional.coeff 178 =
      (((14271401771274096081063353025161854260912660537858267 * 10 ^ 70 +
        2706813029563008171288585584056552631849329947020406369431268930149225) * 10 ^ 70 +
        9624559540810408803767119889630654111803734756362998744169918456431489) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_179 :
    recurrence2Scalar0Exceptional.coeff 179 =
      -(((195323289610307982040490394465587950612146561030908890 * 10 ^ 70 +
        9321602094899942068341272812415371134672328786020932814593931161688482) * 10 ^ 70 +
        0900628556407226232323777363541512122293439368997516357215683132272113) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_180 :
    recurrence2Scalar0Exceptional.coeff 180 =
      (((740679618116486158988283279283702266496973372191628013 * 10 ^ 70 +
        8637546458703867864870371229536850971672722494769001759271761788783548) * 10 ^ 70 +
        4660793727269965194213172568947200095334767147316012752344763711638372) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_181 :
    recurrence2Scalar0Exceptional.coeff 181 =
      -(((1970986104542542092224099262221941431321695664000826449 * 10 ^ 70 +
        3127257209685581410378546714081100358347121056721969905732448086583004) * 10 ^ 70 +
        6239175933999617033997651110527600540414027052367720024957662681820359) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_182 :
    recurrence2Scalar0Exceptional.coeff 182 =
      (((4021935490378197170462955570589094740408580449924642684 * 10 ^ 70 +
        2080292553320968821785811137034475934156734818152625020569761696798007) * 10 ^ 70 +
        2359084951351885486868824789981389884741809312126193627526250944564810) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_183 :
    recurrence2Scalar0Exceptional.coeff 183 =
      -(((5815203308484961416177137039954275335357248813471974253 * 10 ^ 70 +
        9005517461346484523344271464242350489839643843920983360641412705692790) * 10 ^ 70 +
        1160390751043997064056123751526644243704669297250595860101445852116678) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_184 :
    recurrence2Scalar0Exceptional.coeff 184 =
      (((2479938348821282514674899494188889464199274218812464115 * 10 ^ 70 +
        1327631999229163528717901242078514346961681684697435471012309885409130) * 10 ^ 70 +
        4777279621388048646858946981094863233201784160010428158175073309208990) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_185 :
    recurrence2Scalar0Exceptional.coeff 185 =
      (((19760872290895235302213577503980045458704585213442408594 * 10 ^ 70 +
        0996277142514114106718787665754377683511831709321205388503860114392736) * 10 ^ 70 +
        3109887817221293687390877826460247005157840937378749420591592926184261) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_186 :
    recurrence2Scalar0Exceptional.coeff 186 =
      -(((91634076304203320240273132560478979259584562479178606879 * 10 ^ 70 +
        2502064627496925056442092186634350730451010095458508809384723792676347) * 10 ^ 70 +
        3171678977051606565121554075134966961167646034044574215817131297857783) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_187 :
    recurrence2Scalar0Exceptional.coeff 187 =
      (((269710012279109832547949661146324361252740333305653859693 * 10 ^ 70 +
        0707004354750202192973630702759015883995016172241800207996722592880786) * 10 ^ 70 +
        0454338909431702322851757938750599333164643222961638936311046771957943) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 188 = 0 +
    188 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 92 = 32 +
      60 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_188 :
    recurrence2Scalar0Exceptional.coeff 188 =
      -(((638245381164713530321931148871061878271360940980866868170 * 10 ^ 70 +
        7173555060628550812269163565433475502922728301845454862864201404728617) * 10 ^ 70 +
        3368425632448566750016987547232851534586474042615669387880756131591007) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 189 = 0 +
    189 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 93 = 32 +
      61 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_189 :
    recurrence2Scalar0Exceptional.coeff 189 =
      (((1285894321971524737063563731182433858907241939917983033488 * 10 ^ 70 +
        5661071805254472820363961684606569047363202324387131753357534433328893) * 10 ^ 70 +
        7996158555001485171321075949805017918483185580486290023541563340961187) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 190 = 0 +
    190 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 94 = 32 +
      62 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_190 :
    recurrence2Scalar0Exceptional.coeff 190 =
      -(((2225859036122617748230016713843893720635128737000705348584 * 10 ^ 70 +
        3753785587627633801839263363586040643815828751837003381590061251782287) * 10 ^ 70 +
        7332549568875418979009534760745746548409317011554247104868307457040590) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 191 = 0 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_191 :
    recurrence2Scalar0Exceptional.coeff 191 =
      (((3217580760681476818853180021137212857385665969893193447082 * 10 ^ 70 +
        6131341507783776618387393257750594410423645738122234061736171023560126) * 10 ^ 70 +
        4215635196369968244282293101906139145591812800386413389136592460675331) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 192 = 0 +
    192 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_192 :
    recurrence2Scalar0Exceptional.coeff 192 =
      -(((3453912710777920408438903895570244692829407253058285616378 * 10 ^ 70 +
        1784464202093398442230933911927481331833617845251849739062704247052678) * 10 ^ 70 +
        7050467038748629407033523420785092292271968849701554034135791305841347) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
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
    rw [show 65 = 32 +
      33 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Exceptional_coeff_193 :
    recurrence2Scalar0Exceptional.coeff 193 =
      (((1120807392975848370975966935504091014575764477060801003446 * 10 ^ 70 +
        8586510471928857963146352703442983587332414898743844634169569973339371) * 10 ^ 70 +
        6046680050703947773287142784149999398253108949810027012618979919182015) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
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
    rw [show 66 = 32 +
      34 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (194 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_194 :
    recurrence2Scalar0Exceptional.coeff 194 =
      (((7060331196679813748120535366970448648876237225893965938141 * 10 ^ 70 +
        8315344041647487897062387207070084608571535138673038062987165422598044) * 10 ^ 70 +
        5976458994011984572293034776017001511306595768124170757886771067198825) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
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
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_194_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (195 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (195 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_195 :
    recurrence2Scalar0Exceptional.coeff 195 =
      -(((26024036655647590939342182931518113107297050886910021384995 * 10 ^ 70 +
        5723918818583492641210649249244115961070484075643451332176049295535869) * 10 ^ 70 +
        7919344147078468312129854684628328756047239703716742119207484799469619) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 196 = 1 +
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
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 1 +
      2 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_195_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_195_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (196 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (196 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_196 :
    recurrence2Scalar0Exceptional.coeff 196 =
      (((61783158344621867191880024016471285234835173100966660595609 * 10 ^ 70 +
        2640555936183666840522449757011509547632236380767350580390071860895919) * 10 ^ 70 +
        5379190635508928770871833226454569815287768389842086542238810069921063) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 197 = 2 +
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
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_196_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_196_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (197 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (197 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_197 :
    recurrence2Scalar0Exceptional.coeff 197 =
      -(((119397300488893739993475138295338613016562068550572105429825 * 10 ^ 70 +
        1882052714973104979140025609283544837944796521184400818949305708300006) * 10 ^ 70 +
        9371118280270860940544731424228892212676720863881294490026273144526912) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 198 = 3 +
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
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 31 +
      4 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_197_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_197_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (198 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (198 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_198 :
    recurrence2Scalar0Exceptional.coeff 198 =
      (((198806196333239313266268685439859002723282712698146792254529 * 10 ^ 70 +
        9277696767519700667962567358101555566594299949535744467825901514789698) * 10 ^ 70 +
        2678229825975299205698832806611199271492746521335436943450324740187891) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 199 = 4 +
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
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 30 +
      5 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_198_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_198_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (199 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (199 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_199 :
    recurrence2Scalar0Exceptional.coeff 199 =
      -(((288224579320548274230929134126898848428787021095127465831119 * 10 ^ 70 +
        8086908344149032979067903224315004893192635703632413288013001501410611) * 10 ^ 70 +
        2387312290401914316260059582012581103616164665591176624854842610907564) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 200 = 5 +
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
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 29 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_199_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_199_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (200 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (200 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_200 :
    recurrence2Scalar0Exceptional.coeff 200 =
      (((355695446394165879829150453911958680683121008123229787095776 * 10 ^ 70 +
        9188506455299947261347466118131527618554744986093455739773221640990961) * 10 ^ 70 +
        1442348284380663981051325965689097712987346746761066908472546571688215) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 201 = 6 +
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
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 28 +
      7 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_200_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_200_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (201 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (201 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_201 :
    recurrence2Scalar0Exceptional.coeff 201 =
      -(((340808664023730928016336878461527252515700308060253512527799 * 10 ^ 70 +
        3766565935478641762163551442268549764278185684862945260018413489248281) * 10 ^ 70 +
        3504677645105146596106213561554410787843417578163013510343071495178407) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 202 = 7 +
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
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 27 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_201_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_201_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
