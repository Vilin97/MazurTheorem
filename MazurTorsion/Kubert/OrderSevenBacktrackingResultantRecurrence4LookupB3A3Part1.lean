/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA3
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: B3A3 coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4A3_coeff_100
  recurrence4A3_coeff_101
  recurrence4A3_coeff_102
  recurrence4A3_coeff_103
  recurrence4A3_coeff_104
  recurrence4A3_coeff_105
  recurrence4A3_coeff_106
  recurrence4A3_coeff_107
  recurrence4A3_coeff_108
  recurrence4A3_coeff_109
  recurrence4A3_coeff_110
  recurrence4A3_coeff_111
  recurrence4A3_coeff_112
  recurrence4A3_coeff_113
  recurrence4A3_coeff_114
  recurrence4A3_coeff_115
  recurrence4A3_coeff_116
  recurrence4A3_coeff_117
  recurrence4A3_coeff_118
  recurrence4A3_coeff_119
  recurrence4A3_coeff_120
  recurrence4A3_coeff_121
  recurrence4A3_coeff_122
  recurrence4A3_coeff_123
  recurrence4A3_coeff_124
  recurrence4A3_coeff_125
  recurrence4A3_coeff_126
  recurrence4A3_coeff_127
  recurrence4A3_coeff_128
  recurrence4A3_coeff_129
  recurrence4A3_coeff_130
  recurrence4A3_coeff_131
  recurrence4A3_coeff_132
  recurrence4A3_coeff_133
  recurrence4A3_coeff_134
  recurrence4A3_coeff_135
  recurrence4A3_coeff_136
  recurrence4A3_coeff_137
  recurrence4A3_coeff_138
  recurrence4A3_coeff_139
  recurrence4A3_coeff_140
  recurrence4A3_coeff_141
  recurrence4A3_coeff_142
  recurrence4A3_coeff_143
  recurrence4A3_coeff_144
  recurrence4A3_coeff_145
  recurrence4A3_coeff_146
  recurrence4A3_coeff_147
  recurrence4A3_coeff_148
  recurrence4A3_coeff_149
  recurrence4A3_coeff_150
  recurrence4A3_coeff_151
  recurrence4A3_coeff_152
  recurrence4A3_coeff_153
  recurrence4A3_coeff_154
  recurrence4A3_coeff_155
  recurrence4A3_coeff_156
  recurrence4A3_coeff_157
  recurrence4A3_coeff_158
  recurrence4A3_coeff_159
  recurrence4A3_coeff_160
  recurrence4A3_coeff_161
  recurrence4A3_coeff_162
  recurrence4A3_coeff_163

attribute [local simp]
  recurrence4A3_coeff_164
  recurrence4A3_coeff_165
  recurrence4A3_coeff_166
  recurrence4A3_coeff_167
  recurrence4A3_coeff_168
  recurrence4A3_coeff_169
  recurrence4A3_coeff_170
  recurrence4A3_coeff_171
  recurrence4A3_coeff_172
  recurrence4A3_coeff_173
  recurrence4A3_coeff_174
  recurrence4A3_coeff_175
  recurrence4A3_coeff_176
  recurrence4A3_coeff_177
  recurrence4A3_coeff_178
  recurrence4A3_coeff_179
  recurrence4A3_coeff_180
  recurrence4A3_coeff_181
  recurrence4A3_coeff_182
  recurrence4A3_coeff_52
  recurrence4A3_coeff_53
  recurrence4A3_coeff_54
  recurrence4A3_coeff_55
  recurrence4A3_coeff_56
  recurrence4A3_coeff_57
  recurrence4A3_coeff_58
  recurrence4A3_coeff_59
  recurrence4A3_coeff_60
  recurrence4A3_coeff_61
  recurrence4A3_coeff_62
  recurrence4A3_coeff_63
  recurrence4A3_coeff_64
  recurrence4A3_coeff_65
  recurrence4A3_coeff_66
  recurrence4A3_coeff_67
  recurrence4A3_coeff_68
  recurrence4A3_coeff_69
  recurrence4A3_coeff_70
  recurrence4A3_coeff_71
  recurrence4A3_coeff_72
  recurrence4A3_coeff_73
  recurrence4A3_coeff_74
  recurrence4A3_coeff_75
  recurrence4A3_coeff_76
  recurrence4A3_coeff_77
  recurrence4A3_coeff_78
  recurrence4A3_coeff_79
  recurrence4A3_coeff_80
  recurrence4A3_coeff_81
  recurrence4A3_coeff_82
  recurrence4A3_coeff_83
  recurrence4A3_coeff_84
  recurrence4A3_coeff_85
  recurrence4A3_coeff_86
  recurrence4A3_coeff_87
  recurrence4A3_coeff_88
  recurrence4A3_coeff_89
  recurrence4A3_coeff_90
  recurrence4A3_coeff_91
  recurrence4A3_coeff_92
  recurrence4A3_coeff_93
  recurrence4A3_coeff_94
  recurrence4A3_coeff_95
  recurrence4A3_coeff_96

attribute [local simp]
  recurrence4A3_coeff_97
  recurrence4A3_coeff_98
  recurrence4A3_coeff_99
  recurrence4B3_coeff_100
  recurrence4B3_coeff_101
  recurrence4B3_coeff_102
  recurrence4B3_coeff_103
  recurrence4B3_coeff_104
  recurrence4B3_coeff_105
  recurrence4B3_coeff_106
  recurrence4B3_coeff_107
  recurrence4B3_coeff_108
  recurrence4B3_coeff_109
  recurrence4B3_coeff_110
  recurrence4B3_coeff_111
  recurrence4B3_coeff_112
  recurrence4B3_coeff_113
  recurrence4B3_coeff_114
  recurrence4B3_coeff_115
  recurrence4B3_coeff_116
  recurrence4B3_coeff_117
  recurrence4B3_coeff_118
  recurrence4B3_coeff_119
  recurrence4B3_coeff_120
  recurrence4B3_coeff_121
  recurrence4B3_coeff_122
  recurrence4B3_coeff_123
  recurrence4B3_coeff_124
  recurrence4B3_coeff_125
  recurrence4B3_coeff_126
  recurrence4B3_coeff_127
  recurrence4B3_coeff_128
  recurrence4B3_coeff_129
  recurrence4B3_coeff_130
  recurrence4B3_coeff_131
  recurrence4B3_coeff_132
  recurrence4B3_coeff_133
  recurrence4B3_coeff_134
  recurrence4B3_coeff_135
  recurrence4B3_coeff_136
  recurrence4B3_coeff_137
  recurrence4B3_coeff_138
  recurrence4B3_coeff_139
  recurrence4B3_coeff_140
  recurrence4B3_coeff_141
  recurrence4B3_coeff_142
  recurrence4B3_coeff_143
  recurrence4B3_coeff_144
  recurrence4B3_coeff_145
  recurrence4B3_coeff_146
  recurrence4B3_coeff_147
  recurrence4B3_coeff_148
  recurrence4B3_coeff_149
  recurrence4B3_coeff_150
  recurrence4B3_coeff_151
  recurrence4B3_coeff_152
  recurrence4B3_coeff_153
  recurrence4B3_coeff_154
  recurrence4B3_coeff_155
  recurrence4B3_coeff_156
  recurrence4B3_coeff_157
  recurrence4B3_coeff_158
  recurrence4B3_coeff_159
  recurrence4B3_coeff_160

attribute [local simp]
  recurrence4B3_coeff_161
  recurrence4B3_coeff_162
  recurrence4B3_coeff_163
  recurrence4B3_coeff_164
  recurrence4B3_coeff_34
  recurrence4B3_coeff_35
  recurrence4B3_coeff_36
  recurrence4B3_coeff_37
  recurrence4B3_coeff_38
  recurrence4B3_coeff_39
  recurrence4B3_coeff_40
  recurrence4B3_coeff_41
  recurrence4B3_coeff_42
  recurrence4B3_coeff_43
  recurrence4B3_coeff_44
  recurrence4B3_coeff_45
  recurrence4B3_coeff_46
  recurrence4B3_coeff_47
  recurrence4B3_coeff_48
  recurrence4B3_coeff_49
  recurrence4B3_coeff_50
  recurrence4B3_coeff_51
  recurrence4B3_coeff_52
  recurrence4B3_coeff_53
  recurrence4B3_coeff_54
  recurrence4B3_coeff_55
  recurrence4B3_coeff_56
  recurrence4B3_coeff_57
  recurrence4B3_coeff_58
  recurrence4B3_coeff_59
  recurrence4B3_coeff_60
  recurrence4B3_coeff_61
  recurrence4B3_coeff_62
  recurrence4B3_coeff_63
  recurrence4B3_coeff_64
  recurrence4B3_coeff_65
  recurrence4B3_coeff_66
  recurrence4B3_coeff_67
  recurrence4B3_coeff_68
  recurrence4B3_coeff_69
  recurrence4B3_coeff_70
  recurrence4B3_coeff_71
  recurrence4B3_coeff_72
  recurrence4B3_coeff_73
  recurrence4B3_coeff_74
  recurrence4B3_coeff_75
  recurrence4B3_coeff_76
  recurrence4B3_coeff_77
  recurrence4B3_coeff_78
  recurrence4B3_coeff_79
  recurrence4B3_coeff_80
  recurrence4B3_coeff_81
  recurrence4B3_coeff_82
  recurrence4B3_coeff_83
  recurrence4B3_coeff_84
  recurrence4B3_coeff_85
  recurrence4B3_coeff_86
  recurrence4B3_coeff_87
  recurrence4B3_coeff_88
  recurrence4B3_coeff_89
  recurrence4B3_coeff_90
  recurrence4B3_coeff_91
  recurrence4B3_coeff_92
  recurrence4B3_coeff_93

attribute [local simp]
  recurrence4B3_coeff_94
  recurrence4B3_coeff_95
  recurrence4B3_coeff_96
  recurrence4B3_coeff_97
  recurrence4B3_coeff_98
  recurrence4B3_coeff_99

private theorem recurrence4B3A3_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (216 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (216 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_216 :
    recurrence4B3A3.coeff 216 =
      -(((162907507112988861466196978259514282638107941738360350109 * 10 ^ 70 +
        2493225316981760294620130013372181266301610777090458534960796851291147) * 10 ^ 70 +
        1575888792630358899830735195343151711895887559820782285176735080239030) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 217,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (216 - x)) = _
  rw [show 217 = 34 +
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
  rw [recurrence4B3A3_coeff_216_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_216_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (217 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (217 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_217 :
    recurrence4B3A3.coeff 217 =
      (((96928802240674423151420597880601914064756573826942238988 * 10 ^ 70 +
        4574162773091193872868937877956314742746474888761860434077736140086019) * 10 ^ 70 +
        1898433690205533107639954262481403939882591095913094528640016657571350) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 218,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (217 - x)) = _
  rw [show 218 = 35 +
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
  rw [recurrence4B3A3_coeff_217_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_217_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (218 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (218 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_218 :
    recurrence4B3A3.coeff 218 =
      -(((55545780931422231640323494561067333627973291044091735965 * 10 ^ 70 +
        3706713918425572904462746588522243484164690042458289222994993577520690) * 10 ^ 70 +
        3484460196822648312146688184894171415417599220454191692004579985951344) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 219,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (218 - x)) = _
  rw [show 219 = 36 +
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
  rw [recurrence4B3A3_coeff_218_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_218_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (219 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (219 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_219 :
    recurrence4B3A3.coeff 219 =
      (((30804251780684071664874590057773063344958189908537575911 * 10 ^ 70 +
        0371190364870268218808001061181705247203338630174447195597893896416059) * 10 ^ 70 +
        4103461634388802830723777911008650802234197472571665940100058506597853) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 220,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (219 - x)) = _
  rw [show 220 = 37 +
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
  rw [recurrence4B3A3_coeff_219_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_219_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (220 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (220 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_220 :
    recurrence4B3A3.coeff 220 =
      -(((16583591001733250402307113804725735324667506002767407891 * 10 ^ 70 +
        4434625070658671275728473367220184725341466933403263747507479248682046) * 10 ^ 70 +
        5093302501219238505443293845740196846597894105088624840731492299271350) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 221,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (220 - x)) = _
  rw [show 221 = 38 +
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
  rw [recurrence4B3A3_coeff_220_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_220_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (221 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (221 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_221 :
    recurrence4B3A3.coeff 221 =
      (((8684557911595689712582383311505491087486056107152693021 * 10 ^ 70 +
        9457660076038232542624042617082407235022389873883853737864896964985584) * 10 ^ 70 +
        6172144663836220684929006589969105885992109966426478074331586136956322) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 222,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (221 - x)) = _
  rw [show 222 = 39 +
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
  rw [recurrence4B3A3_coeff_221_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_221_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (222 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (222 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_222 :
    recurrence4B3A3.coeff 222 =
      -(((4430072578823469080338982769514912682096148732144099177 * 10 ^ 70 +
        2843682504665372762991425895759630138561937456338440847810722971214227) * 10 ^ 70 +
        7914360142609686163594839761557187214048423271934430960437355184769161) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 223,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (222 - x)) = _
  rw [show 223 = 40 +
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
  rw [recurrence4B3A3_coeff_222_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_222_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (223 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (223 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_223 :
    recurrence4B3A3.coeff 223 =
      (((2203194131743833870606146055660331018168606677132247978 * 10 ^ 70 +
        1396254489070417823299368203194040037021809765424528324715460761734974) * 10 ^ 70 +
        5568799933055365971801243433569310023575645751563877622355626442736482) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 224,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (223 - x)) = _
  rw [show 224 = 41 +
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
  rw [recurrence4B3A3_coeff_223_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_223_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (224 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (224 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_224 :
    recurrence4B3A3.coeff 224 =
      -(((1068829146535208598753090674483752294947771456404942101 * 10 ^ 70 +
        4140622421838989869617652007252236802429431677929711501361888489410967) * 10 ^ 70 +
        7368122823052459167060210963985747191474984885570803642167473872339640) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 225,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (224 - x)) = _
  rw [show 225 = 42 +
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
  rw [recurrence4B3A3_coeff_224_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_224_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (225 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (225 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_225 :
    recurrence4B3A3.coeff 225 =
      (((505941063026645620268866241986647795041967087083666898 * 10 ^ 70 +
        1510273691698359090468633012875699901728839285709958443639938270987654) * 10 ^ 70 +
        1828646215464553699807722367618090580370840235558665951635457535491514) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 226,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (225 - x)) = _
  rw [show 226 = 43 +
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
  rw [recurrence4B3A3_coeff_225_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_225_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (226 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (226 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_226 :
    recurrence4B3A3.coeff 226 =
      -(((233702320211071507747881107340708827712846254550438507 * 10 ^ 70 +
        6161787757844022913970159072461316923250200479030685144933756843175448) * 10 ^ 70 +
        1815496186804370003130392498463023750016333072544559056060737809391351) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 227,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (226 - x)) = _
  rw [show 227 = 44 +
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
  rw [recurrence4B3A3_coeff_226_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_226_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (227 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (227 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_227 :
    recurrence4B3A3.coeff 227 =
      (((105332513172760857666926433148495649970400778320653550 * 10 ^ 70 +
        7108483391184996710619342774232498682186438334304516042327096096234455) * 10 ^ 70 +
        9934025505069664385899102831012194156005275634521269298174269242385684) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 228,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (227 - x)) = _
  rw [show 228 = 45 +
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
  rw [recurrence4B3A3_coeff_227_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_227_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (228 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (228 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_228 :
    recurrence4B3A3.coeff 228 =
      -(((46313055379885746572070992908430272108856572935431634 * 10 ^ 70 +
        9736179066295727002707873088029360844180554588195335034157134874429952) * 10 ^ 70 +
        4779503124252308596753622808951378676760404259975784107759917327895727) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 229,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (228 - x)) = _
  rw [show 229 = 46 +
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
  rw [recurrence4B3A3_coeff_228_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_228_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (229 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (229 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_229 :
    recurrence4B3A3.coeff 229 =
      (((19858112859291337040757617360116221040167025903410814 * 10 ^ 70 +
        9225655450537633730818398683512972950029991934160489592684003709306566) * 10 ^ 70 +
        9833599861999876612129977445759690814435821852557749877155121388716907) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 230,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (229 - x)) = _
  rw [show 230 = 47 +
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
  rw [recurrence4B3A3_coeff_229_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_229_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (230 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (230 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_230 :
    recurrence4B3A3.coeff 230 =
      -(((8299798788497882845090496243497309834396614424069370 * 10 ^ 70 +
        8629837663539455382551628413152615362538844823630287956974216055183604) * 10 ^ 70 +
        1521844535545927187573315270470805479141943642646024781027775754286879) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 231,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (230 - x)) = _
  rw [show 231 = 48 +
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
  rw [recurrence4B3A3_coeff_230_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_230_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (231 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (231 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_231 :
    recurrence4B3A3.coeff 231 =
      (((3379424118605110592030091288106623952502344912276142 * 10 ^ 70 +
        4806242318821600248697761250943443922448284873337826380006522267364687) * 10 ^ 70 +
        0145201762857143567447093201902836381012333525735459331810420049035009) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 232,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (231 - x)) = _
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
    rw [show 87 = 20 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_231_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_231_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (232 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (232 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_232 :
    recurrence4B3A3.coeff 232 =
      -(((1339550803788073479545862164834254863410003914562032 * 10 ^ 70 +
        4613024162123842639457301018988455233284870805159661383993359146782353) * 10 ^ 70 +
        6339587362724563561163813085710382899967089528033614226075850944472501) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 233,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (232 - x)) = _
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
    rw [show 87 = 19 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_232_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_232_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (233 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (233 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_233 :
    recurrence4B3A3.coeff 233 =
      (((516477109792974964657795429219736710995708276605465 * 10 ^ 70 +
        5093426241437236188818750639341054462463632502797233103852195417455607) * 10 ^ 70 +
        4241511552822685547451657803203235700531840498131593815462652440943296) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 234,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (233 - x)) = _
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
    rw [show 87 = 18 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_233_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_233_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (234 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (234 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_234 :
    recurrence4B3A3.coeff 234 =
      -(((193499485590924828543595843043380051958925351562552 * 10 ^ 70 +
        1010109494554018608919784125926677915966417104116760623102583344056636) * 10 ^ 70 +
        5287198284930800171038733761425350289319916655484755106239399575700734) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 235,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (234 - x)) = _
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
    rw [show 87 = 17 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_234_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_234_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 53,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (235 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (235 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_235 :
    recurrence4B3A3.coeff 235 =
      (((70358928945900705999469451453440754764589908227622 * 10 ^ 70 +
        5280190185449314857018055456625661973872719568890244284632276030707016) * 10 ^ 70 +
        3850581522519208164318201460609823196922009341245255463655415942526226) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 236,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (235 - x)) = _
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
    rw [show 87 = 16 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_235_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_235_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 54,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (236 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (236 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_236 :
    recurrence4B3A3.coeff 236 =
      -(((24793395671674182220349841982905440879036575679813 * 10 ^ 70 +
        4522901246741982483204974697137521362077189115625174188720701191029514) * 10 ^ 70 +
        1362041763288578316831340250807962820531917265685540372315621087770559) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 237,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (236 - x)) = _
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
    rw [show 87 = 15 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_236_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_236_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 55,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (237 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (237 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_237 :
    recurrence4B3A3.coeff 237 =
      (((8452135478762506549854407247831469553100501406244 * 10 ^ 70 +
        4264380587085079735778940141003883804472769925575815283740908294307277) * 10 ^ 70 +
        3991728911085732944295712180624940402145795093439023344137316265066453) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 238,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (237 - x)) = _
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
    rw [show 87 = 14 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_237_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_237_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 56,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (238 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (238 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_238 :
    recurrence4B3A3.coeff 238 =
      -(((2781582081597005723336220331730998402762651373974 * 10 ^ 70 +
        9679937482811853220535084083091887738994697673633202043692969214446229) * 10 ^ 70 +
        9105893568062922150144836322794782241154077376761704514267047008151933) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 239,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (238 - x)) = _
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
    rw [show 87 = 13 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_238_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_238_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 57,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (239 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (239 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_239 :
    recurrence4B3A3.coeff 239 =
      (((881497931794979144307467635608021654975361031817 * 10 ^ 70 +
        4228044218152357587447488128004833386752078869126065802815448480369163) * 10 ^ 70 +
        5921533752568505255610092899852699810026042234248651899377199183834964) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 240,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (239 - x)) = _
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
    rw [show 87 = 12 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_239_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_239_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 58,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (240 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (240 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_240 :
    recurrence4B3A3.coeff 240 =
      -(((268226284412860833754279430764742168829096776264 * 10 ^ 70 +
        6110818923222585654081150874609481656548188138063810825834351738375560) * 10 ^ 70 +
        6593191340017840100344379431805138692824003688368776190483586727575411) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 241,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (240 - x)) = _
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
    rw [show 87 = 11 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_240_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_240_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 59,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (241 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (241 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_241 :
    recurrence4B3A3.coeff 241 =
      (((78126989037989882809247196336486495792915687688 * 10 ^ 70 +
        0925145587517179372176474322497611212019003335682616596916170410800716) * 10 ^ 70 +
        3273982621964341472315226847946884846076873608513275332362437573360283) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 242,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (241 - x)) = _
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
    rw [show 87 = 10 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_241_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_241_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 60,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (242 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (242 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_242 :
    recurrence4B3A3.coeff 242 =
      -(((21725751717057152860128714676475204002233738627 * 10 ^ 70 +
        1409980880555282415585334882551916151293985979792756658885134458048876) * 10 ^ 70 +
        2650057846204600622163799092484736066787571442486288595349207066981790) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 243,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (242 - x)) = _
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
    rw [show 87 = 9 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_242_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_242_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 61,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (243 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (243 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_243 :
    recurrence4B3A3.coeff 243 =
      (((5763682828194076862133010060746111361158515150 * 10 ^ 70 +
        9803307497561053972627367303363758583417212531600319885192435243943185) * 10 ^ 70 +
        2078716450960069192262785569458612261570979340487535909250535844834830) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 244,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (243 - x)) = _
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
    rw [show 87 = 8 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_243_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_243_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 62,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (244 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (244 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_244 :
    recurrence4B3A3.coeff 244 =
      -(((1464702832217740737919239733823443788196772702 * 10 ^ 70 +
        7142934715613563920029467897403511977408641417365391815928722584236943) * 10 ^ 70 +
        6407550550194552584428831711510539491767183501283125704913961558162230) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 245,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (244 - x)) = _
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
    rw [show 87 = 7 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_244_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_244_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 63,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (245 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (245 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_245 :
    recurrence4B3A3.coeff 245 =
      (((361127575561655547169102508792432556768856319 * 10 ^ 70 +
        3397460004729801951252501720319150948783318027009307731233785621042934) * 10 ^ 70 +
        1199236498281230108713161374740178580301062689629989723405661627966044) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 246,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (245 - x)) = _
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
    rw [show 87 = 6 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_245_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_245_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 64,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (246 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (246 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_246 :
    recurrence4B3A3.coeff 246 =
      -(((88048845557248867395106520396560455691262021 * 10 ^ 70 +
        7504760851457590003001033044000290593775652385443777228611689307696016) * 10 ^ 70 +
        6412043713851997188802989158382348924577685195588969849153634011943502) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 247,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (246 - x)) = _
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
    rw [show 87 = 5 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_246_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_246_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 65,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (247 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (247 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_247 :
    recurrence4B3A3.coeff 247 =
      (((21068484634900988552700135887803821771533763 * 10 ^ 70 +
        4959662422130886036273834312881115206326143289991457412626133747907110) * 10 ^ 70 +
        3422228894036770445996198708623092258624748960000945307781859988971031) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 248,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (247 - x)) = _
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
    rw [show 87 = 4 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_247_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_247_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 66,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (248 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (248 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_248 :
    recurrence4B3A3.coeff 248 =
      -(((4181685818370386685379556227330320506754779 * 10 ^ 70 +
        6238537126873161797850552037188058337459721910090167233672776697470233) * 10 ^ 70 +
        8454098023015155467180047116660308603815193399779785826366077255270663) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 249,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (248 - x)) = _
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
    rw [show 87 = 3 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_248_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_248_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 67,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (249 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (249 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_249 :
    recurrence4B3A3.coeff 249 =
      -(((122074967361057878802022131828935956821160 * 10 ^ 70 +
        1700001121976180904668410829149318427009118667132706343212680142599319) * 10 ^ 70 +
        7987876352999312351460735634463319562475158410654430885536655352808173) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 250,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (249 - x)) = _
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
    rw [show 87 = 2 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_249_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_249_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 68,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (250 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (250 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_250 :
    recurrence4B3A3.coeff 250 =
      (((990223379651402706379343898773149363192590 * 10 ^ 70 +
        7867012227552091946231734805017406099981170925405570131770520236234588) * 10 ^ 70 +
        4543479011350823615768126496843220712771259182336256734476020419164481) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 251,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (250 - x)) = _
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
    rw [show 87 = 1 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_250_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_250_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 69,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (251 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (251 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_251 :
    recurrence4B3A3.coeff 251 =
      -(((894960685253512527205731505035679184670107 * 10 ^ 70 +
        9659403248592416819073302786306731150279768565884575348430460318266470) * 10 ^ 70 +
        5411363168273020012848109951995674625265707403352609759780097131222745) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 252,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (251 - x)) = _
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
  rw [recurrence4B3A3_coeff_251_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_251_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 70,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (252 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 88,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (252 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_252 :
    recurrence4B3A3.coeff 252 =
      (((601939974285942643279486315184508408631357 * 10 ^ 70 +
        4757687675843690085467646296985015314918475091197001876821814175462268) * 10 ^ 70 +
        8590445229384010325283206079757340607438747629740773211666309205008203) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 253,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (252 - x)) = _
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
    rw [show 119 = 31 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_252_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_252_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 71,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (253 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 89,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (253 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_253 :
    recurrence4B3A3.coeff 253 =
      -(((347864950872002107560509230721819852821526 * 10 ^ 70 +
        0971783173299648908701696134294192633636621808148013782428143785864660) * 10 ^ 70 +
        0343200926596026698853901972842339184180742373275844451413642672189097) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 254,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (253 - x)) = _
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
    rw [show 119 = 30 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_253_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_253_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 72,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (254 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 90,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (254 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_254 :
    recurrence4B3A3.coeff 254 =
      (((180615682424410717740851222259952086302876 * 10 ^ 70 +
        5161731303119725190850478896802797188327305595686862771519855001207750) * 10 ^ 70 +
        5945309818479601527484401003080701106785963285262618495274929973425338) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 255,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (254 - x)) = _
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
    rw [show 119 = 29 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_254_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_254_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 73,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (255 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 91,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (255 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_255 :
    recurrence4B3A3.coeff 255 =
      -(((85910129753670993294956658337310638843009 * 10 ^ 70 +
        8904124028768948420232835191127542140054241908317616670008040806546887) * 10 ^ 70 +
        8173120215503495938017156527472720780499112277299716162074398903521380) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 256,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (255 - x)) = _
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
    rw [show 119 = 28 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_255_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_255_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 74,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (256 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 92,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (256 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_256 :
    recurrence4B3A3.coeff 256 =
      (((37789302759998989735055966864623770552239 * 10 ^ 70 +
        5832667376343204968817623640406459726841729693594054794778625628150126) * 10 ^ 70 +
        1743386791460258800431543187988364489521417805752474352001619577414937) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 257,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (256 - x)) = _
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
    rw [show 119 = 27 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_256_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_256_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (257 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 93,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (257 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_257 :
    recurrence4B3A3.coeff 257 =
      -(((15430518879791395846336510255634765956958 * 10 ^ 70 +
        3109851235990820027031827920229105779580185443811514137472372319280893) * 10 ^ 70 +
        7117589629814774449752211253135493244734328139101044599499422704909266) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 258,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (257 - x)) = _
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
    rw [show 119 = 26 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_257_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_257_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (258 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 94,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (258 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_258 :
    recurrence4B3A3.coeff 258 =
      (((5845733017717549002132196376234109612666 * 10 ^ 70 +
        3996198195800314906450936225405913296386303632031258122195694893015530) * 10 ^ 70 +
        5196179940127259127715276988372657786438643863457116565087683840742853) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 259,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (258 - x)) = _
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
    rw [show 119 = 25 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_258_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (259 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 95,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (259 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_259 :
    recurrence4B3A3.coeff 259 =
      -(((2043751739092822268139404012902393804160 * 10 ^ 70 +
        4038813304263851120369092803551841836678890625722697459167150103026362) * 10 ^ 70 +
        2084184994049502417196773160671549709827408624851471127197098730661494) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 260,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (259 - x)) = _
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
    rw [show 119 = 24 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_259_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (260 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 96,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (260 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_260 :
    recurrence4B3A3.coeff 260 =
      (((651121864650145123551268336931765996857 * 10 ^ 70 +
        5966944278714161126269375134328633803565558549136339122979733345230933) * 10 ^ 70 +
        5398787235056839692213375516723818070259875259115444231241770587986649) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 261,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (260 - x)) = _
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
    rw [show 119 = 23 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_260_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (261 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 97,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (261 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_261 :
    recurrence4B3A3.coeff 261 =
      -(((183897938625094488592552427421583356366 * 10 ^ 70 +
        8737166817011117336064785207201218089675185193866337081586782294972088) * 10 ^ 70 +
        0782605168368075481953428565592697179618175875602314155178063576089106) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 262,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (261 - x)) = _
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
    rw [show 119 = 22 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_261_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (262 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 98,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (262 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_262 :
    recurrence4B3A3.coeff 262 =
      (((42966529614151053276834659905490334207 * 10 ^ 70 +
        4732030517502292654128717950704233347126972469539352274262588243356006) * 10 ^ 70 +
        2332768690559718867963005877079818132543511115993720246307806050074367) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 263,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (262 - x)) = _
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
    rw [show 119 = 21 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_262_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (263 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 99,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (263 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_263 :
    recurrence4B3A3.coeff 263 =
      -(((6360054921462236715918768354647687098 * 10 ^ 70 +
        2430816437963330154179259222183613219603306293359380653689247638217316) * 10 ^ 70 +
        3328482197390832441674198676165765467862631248080663353900194931209872) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 264,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (263 - x)) = _
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
    rw [show 119 = 20 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_263_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (264 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 100,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (264 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_264 :
    recurrence4B3A3.coeff 264 =
      -(((840954610983212693243459807136790203 * 10 ^ 70 +
        2400354269100047795050455365946230361784619569227042425477702247071742) * 10 ^ 70 +
        3913738463039541010839901531785100207067714028226231360401802037451140) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 265,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (264 - x)) = _
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
    rw [show 119 = 19 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_264_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (265 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 101,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (265 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_265 :
    recurrence4B3A3.coeff 265 =
      (((1247466541255782752335306755868728320 * 10 ^ 70 +
        3789076938668778708808530826905104761677762616847006442575391870272776) * 10 ^ 70 +
        8001789772589512625329286234086517090993087594521189700033763051897537) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 266,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (265 - x)) = _
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
    rw [show 119 = 18 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_265_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (266 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 102,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (266 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_266 :
    recurrence4B3A3.coeff 266 =
      -(((693287335134881302636021205815258568 * 10 ^ 70 +
        5401199194826700888087156944273777718513072052087523626388231159853931) * 10 ^ 70 +
        7330536769891477760699445337420513994550549061788610773214416266743733) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 267,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (266 - x)) = _
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
    rw [show 119 = 17 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_266_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (267 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 103,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (267 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_267 :
    recurrence4B3A3.coeff 267 =
      (((299277040830515408331918564802901810 * 10 ^ 70 +
        1960495163585424676868721624978003856519485540530228576973286096438941) * 10 ^ 70 +
        4284006077933859989556481920724815955803521596707802569709854098802394) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 268,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (267 - x)) = _
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
    rw [show 119 = 16 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_267_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (268 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 104,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (268 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_268 :
    recurrence4B3A3.coeff 268 =
      -(((112922845375157998792912945366708568 * 10 ^ 70 +
        4348213440159377954191089028620814112469200425490369554768784065356963) * 10 ^ 70 +
        5337574266519676230878618897996826534726578177634309387837151180243529) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 269,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (268 - x)) = _
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
    rw [show 119 = 15 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_268_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (269 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 105,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (269 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_269 :
    recurrence4B3A3.coeff 269 =
      (((38897795821580566894715474569928129 * 10 ^ 70 +
        1493760661114442269956631592069390166985952457060380154842818497881110) * 10 ^ 70 +
        8865539383862293134914300655071865324654763884991602823659198829983752) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 270,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (269 - x)) = _
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
    rw [show 119 = 14 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_269_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (270 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 106,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (270 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_270 :
    recurrence4B3A3.coeff 270 =
      -(((12485369723524815557751417806573370 * 10 ^ 70 +
        3495795365563065046161937268763840887430998058654676451576979873232755) * 10 ^ 70 +
        4971959389573421258618125298965607254889933784028207981242704807372640) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 271,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (270 - x)) = _
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
    rw [show 119 = 13 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_270_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (271 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 107,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (271 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_271 :
    recurrence4B3A3.coeff 271 =
      (((3763572309804020607700146274424904 * 10 ^ 70 +
        3883993229941639419258929694532114855045231988187284186774578237344117) * 10 ^ 70 +
        3387336490128793388041678104436034651178163658364620742251117329916830) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 272,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (271 - x)) = _
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
    rw [show 119 = 12 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_271_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (272 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 108,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (272 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_272 :
    recurrence4B3A3.coeff 272 =
      -(((1059075060385397026671362408870924 * 10 ^ 70 +
        3322016351961455078192194187664732052987527725745176494159661875962770) * 10 ^ 70 +
        8971145515391045171438345420194827526040062759278698875464643880647782) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 273,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (272 - x)) = _
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
    rw [show 119 = 11 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_272_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (273 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 109,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (273 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_273 :
    recurrence4B3A3.coeff 273 =
      (((269686052953525261448358107268726 * 10 ^ 70 +
        3442232382267099517818791802857601940925070286053714007334462980351501) * 10 ^ 70 +
        2742848378259115599400032687866436455161088122713626896672005603921210) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 274,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (273 - x)) = _
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
    rw [show 119 = 10 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_273_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (274 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 110,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (274 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_274 :
    recurrence4B3A3.coeff 274 =
      -(((56086369835499634535042326725139 * 10 ^ 70 +
        1976659834794102292690843377747188249928126712877619690669967912171399) * 10 ^ 70 +
        2449096976933691659721360537579033076413464101260443279367752285652970) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 275,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (274 - x)) = _
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
    rw [show 119 = 9 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_274_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (275 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 111,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (275 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_275 :
    recurrence4B3A3.coeff 275 =
      (((5307732595295931689509770643553 * 10 ^ 70 +
        1461229917116865587042240018139331474517746249178967814874480321695155) * 10 ^ 70 +
        3769146507710776156274493225932204842876058177437240002744469830185693) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 276,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (275 - x)) = _
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
    rw [show 119 = 8 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_275_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (276 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 112,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (276 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_276 :
    recurrence4B3A3.coeff 276 =
      (((3401887042338899462273667791239 * 10 ^ 70 +
        2985501339375769786785735953826076542719930201626168124863767993405918) * 10 ^ 70 +
        1396201550790625163220462226845337414740458368546156513427310152855247) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 277,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (276 - x)) = _
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
    rw [show 119 = 7 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_276_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (277 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 113,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (277 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_277 :
    recurrence4B3A3.coeff 277 =
      -(((3063651656732604211931989007504 * 10 ^ 70 +
        8821460794853623261748518383760504603639349093530628470920505606808284) * 10 ^ 70 +
        8436074289495589486318098692498506688810772608650235061229075114649265) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 278,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (277 - x)) = _
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
    rw [show 119 = 6 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_277_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 96,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (278 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 114,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (278 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_278 :
    recurrence4B3A3.coeff 278 =
      (((1709176358855942704205178355329 * 10 ^ 70 +
        9228204533384163457438416703750733016285572122389797574863418398685927) * 10 ^ 70 +
        1300246899587191090477217816277164482093420137997879455051817548426010) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 279,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (278 - x)) = _
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
    rw [show 119 = 5 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_278_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 97,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (279 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 115,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (279 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_279 :
    recurrence4B3A3.coeff 279 =
      -(((801147130009384020618825547386 * 10 ^ 70 +
        3384774184793584637731471728151228670129775938948204110430095284262357) * 10 ^ 70 +
        1250899189525791480968042486754863592372502836456232193911782024611796) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 280,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (279 - x)) = _
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
    rw [show 119 = 4 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_279_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 98,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (280 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 116,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (280 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_280 :
    recurrence4B3A3.coeff 280 =
      (((339179497499419693617083899494 * 10 ^ 70 +
        6425093802959113444218645521649656109621986585807042680211337433004152) * 10 ^ 70 +
        6215236772323427575931174630477379364882483837851500186219313823304389) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 281,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (280 - x)) = _
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
    rw [show 119 = 3 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_280_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (281 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 117,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (281 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_281 :
    recurrence4B3A3.coeff 281 =
      -(((133190659108577635940029708535 * 10 ^ 70 +
        6835320184426083940406224530836709265143116703511565673039553877469120) * 10 ^ 70 +
        1070449264324448178078715136777499277835829410408785305942192839574596) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 282,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (281 - x)) = _
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
    rw [show 119 = 2 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_281_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (282 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 118,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (282 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_282 :
    recurrence4B3A3.coeff 282 =
      (((49031773633884792131835172574 * 10 ^ 70 +
        7454786701153031625403563860699162773246916175170811686368867488296252) * 10 ^ 70 +
        3041837531041888075027175934168485101258264203697113873993999471617251) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 283,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (282 - x)) = _
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
    rw [show 119 = 1 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_282_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (283 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 119,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (283 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_283 :
    recurrence4B3A3.coeff 283 =
      -(((16978750780142487890119737826 * 10 ^ 70 +
        0720901926555055758829143557725270029240180294182084290913288632108050) * 10 ^ 70 +
        4293809757832141302902741395482247706464040242046966311080045081270291) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 284,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (283 - x)) = _
  rw [show 284 = 101 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_283_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (284 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 120,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (284 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_284 :
    recurrence4B3A3.coeff 284 =
      (((5526842971956288697142434053 * 10 ^ 70 +
        8569973776412740312385409982023582807410943730304274362747837814448506) * 10 ^ 70 +
        8044970602600506499891346933016253273795549931567798039268871369546909) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 285,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (284 - x)) = _
  rw [show 285 = 102 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 31 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_284_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (285 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 121,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (285 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_285 :
    recurrence4B3A3.coeff 285 =
      -(((1685606205006759946960790779 * 10 ^ 70 +
        4218867824196998946947767262050240663511676631514378027382519343780279) * 10 ^ 70 +
        9386792345057666886504606019726924097576680070135560231390144846147590) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 286,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (285 - x)) = _
  rw [show 286 = 103 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 30 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_285_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (286 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 122,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (286 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_286 :
    recurrence4B3A3.coeff 286 =
      (((478955227310155733241131323 * 10 ^ 70 +
        7172297284239046692392327528609962012712645648550711403420907004687714) * 10 ^ 70 +
        3940198073388137765520109405860044411877002591683946503767859610189159) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 287,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (286 - x)) = _
  rw [show 287 = 104 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 29 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_286_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 105,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (287 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 123,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (287 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_287 :
    recurrence4B3A3.coeff 287 =
      -(((125709655530770064706833005 * 10 ^ 70 +
        3490715603479332490538587187558571837112261798616703308644435780844321) * 10 ^ 70 +
        0046386678468713309637799838077092320801128109939715597694704142069848) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 288,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (287 - x)) = _
  rw [show 288 = 105 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 28 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_287_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 106,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (288 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 124,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (288 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_288 :
    recurrence4B3A3.coeff 288 =
      (((30066174556095157827243164 * 10 ^ 70 +
        7815569250913873012062614953916381949550821820039958577660321790998972) * 10 ^ 70 +
        9174081438140080194781560108797129404114080645833170059728055185882545) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 289,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (288 - x)) = _
  rw [show 289 = 106 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 27 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_288_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 107,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (289 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 125,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (289 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_289 :
    recurrence4B3A3.coeff 289 =
      -(((6396769395637929617154799 * 10 ^ 70 +
        4054541302359559238336997338798252960016243702243017246587611196711258) * 10 ^ 70 +
        4916431666051763183123924191976475984273789705999791196404551918605344) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 290,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (289 - x)) = _
  rw [show 290 = 107 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 26 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_289_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 108,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (290 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 126,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (290 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_290 :
    recurrence4B3A3.coeff 290 =
      (((1149855075532106373516040 * 10 ^ 70 +
        4116231966957138585357307762417312344701604172279026162432603749489475) * 10 ^ 70 +
        2868756569194190615448928419156656566254246937429596290460986620536581) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 291,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (290 - x)) = _
  rw [show 291 = 108 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 25 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_290_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 109,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (291 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 127,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (291 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_291 :
    recurrence4B3A3.coeff 291 =
      -(((149492074201183622626066 * 10 ^ 70 +
        7092673970349745060612034193432626500298481088107006303383143081567518) * 10 ^ 70 +
        4285457614298897929220476327952912565513967774449908198556546312991054) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 292,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (291 - x)) = _
  rw [show 292 = 109 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 24 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_291_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 110,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (292 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 128,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (292 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_292 :
    recurrence4B3A3.coeff 292 =
      (((2310863282441633168343 * 10 ^ 70 +
        5097995218192528181573689083502830314371505372323888962229542278053170) * 10 ^ 70 +
        1156912850446579355231826632400343669061269185446656961972967925633931) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 293,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (292 - x)) = _
  rw [show 293 = 110 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 23 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_292_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 111,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (293 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 129,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (293 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_293 :
    recurrence4B3A3.coeff 293 =
      (((6844578954536399796171 * 10 ^ 70 +
        6925907995225189375411758483674778964318883670176607919924697107454371) * 10 ^ 70 +
        8378479116060402428801027098280737070398018451357885423415691289066869) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 294,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (293 - x)) = _
  rw [show 294 = 111 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 22 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_293_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 112,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (294 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 130,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (294 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_294 :
    recurrence4B3A3.coeff 294 =
      -(((2956069200742632456701 * 10 ^ 70 +
        2147764307613124254444039858617045863883342978850775216297496817613031) * 10 ^ 70 +
        5841735085765825622915159570975109207479414320795764221526823765111214) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 295,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (294 - x)) = _
  rw [show 295 = 112 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 21 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_294_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 113,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (295 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 131,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (295 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_295 :
    recurrence4B3A3.coeff 295 =
      (((870463065307669976209 * 10 ^ 70 +
        9924430033750371947490872649364115957609363990778996431765871283925917) * 10 ^ 70 +
        6870985715470045270258853762957585820397381655631213666758576294845962) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 296,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (295 - x)) = _
  rw [show 296 = 113 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 20 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_295_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 114,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (296 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 132,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (296 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_296 :
    recurrence4B3A3.coeff 296 =
      -(((209872530106294757837 * 10 ^ 70 +
        9508733645923161354756432881216644717124154641033818686188618474267640) * 10 ^ 70 +
        5110145524214885722985553024847240506109532426575008730504772331571607) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 297,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (296 - x)) = _
  rw [show 297 = 114 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 19 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_296_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 115,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (297 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 133,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (297 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_297 :
    recurrence4B3A3.coeff 297 =
      (((43516867137414699092 * 10 ^ 70 +
        3167129813217262308436733305191692792148502684136719213449845843121985) * 10 ^ 70 +
        7017136040254022174678727506478562807393863338948378660822320631526181) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 298,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (297 - x)) = _
  rw [show 298 = 115 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 18 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_297_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 116,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (298 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 134,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (298 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_298 :
    recurrence4B3A3.coeff 298 =
      -(((7866253970758043417 * 10 ^ 70 +
        1799269104689798149037990025698064781859136744944736599495809267643557) * 10 ^ 70 +
        3969200786285292168444630464988156043496344409129462665128293108177167) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 299,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (298 - x)) = _
  rw [show 299 = 116 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 17 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_298_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 117,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (299 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 135,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (299 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_299 :
    recurrence4B3A3.coeff 299 =
      (((1233903994902497876 * 10 ^ 70 +
        2200949330310554560123335973404324361199910170726345507067738412404599) * 10 ^ 70 +
        4354936693994909323612160624056089242541212241680219342610653274844897) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 300,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (299 - x)) = _
  rw [show 300 = 117 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 16 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_299_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 118,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (300 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 136,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (300 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_300 :
    recurrence4B3A3.coeff 300 =
      -(((163988216554949817 * 10 ^ 70 +
        7964662426214741568124438932673535959171430755294027278630207733805385) * 10 ^ 70 +
        2654800770372968718797656712696447174099893601045529716210971809486967) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 301,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (300 - x)) = _
  rw [show 301 = 118 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 15 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_300_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 119,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (301 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 137,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (301 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_301 :
    recurrence4B3A3.coeff 301 =
      (((17302811959230617 * 10 ^ 70 +
        3894058452425437158367066360170527996863967229047720962562189218292499) * 10 ^ 70 +
        4549702522998601085762099844005158194248926024238317779875767144768401) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 302,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (301 - x)) = _
  rw [show 302 = 119 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 14 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_301_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 120,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (302 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 138,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (302 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_302 :
    recurrence4B3A3.coeff 302 =
      -(((1143697874910713 * 10 ^ 70 +
        6961772480468243862613104142830179591142036128080228182474243386491921) * 10 ^ 70 +
        7235862396504512062945989919835827551131423260547023664347101947967249) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 303,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (302 - x)) = _
  rw [show 303 = 120 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 13 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_302_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 121,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (303 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 139,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (303 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_303 :
    recurrence4B3A3.coeff 303 =
      -(((39295102318857 * 10 ^ 70 +
        9992680937142435765781366218922630690955520077741894351317769929803997) * 10 ^ 70 +
        1690159937192549586444237592428039360600414417553110369042186070434024) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 304,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (303 - x)) = _
  rw [show 304 = 121 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 12 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_303_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 122,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (304 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 140,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (304 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_304 :
    recurrence4B3A3.coeff 304 =
      (((27991659528431 * 10 ^ 70 +
        2888596701217408354133141710232438641022667867666763285905441413656586) * 10 ^ 70 +
        4513527522427673216788378706273016369345849204745451416026700147501060) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 305,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (304 - x)) = _
  rw [show 305 = 122 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 11 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_304_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 123,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (305 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 141,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (305 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_305 :
    recurrence4B3A3.coeff 305 =
      -(((5448650536836 * 10 ^ 70 +
        5972417674086851264059059431640001481936400607469313418183315756684390) * 10 ^ 70 +
        8080739776317967253156821909674125634979532845884868504528015646102053) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 306,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (305 - x)) = _
  rw [show 306 = 123 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 10 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_305_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 124,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (306 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 142,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (306 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_306 :
    recurrence4B3A3.coeff 306 =
      (((727971978323 * 10 ^ 70 +
        6508392178501471832604505405032515649747854927909989323056868229341904) * 10 ^ 70 +
        1420052777402634375950724648765213686586369607387258019826775821705251) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 307,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (306 - x)) = _
  rw [show 307 = 124 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 9 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_306_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 125,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (307 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 143,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (307 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_307 :
    recurrence4B3A3.coeff 307 =
      -(((73066202703 * 10 ^ 70 +
        2856636195979743732789888768640893069461042326915435148111306088134810) * 10 ^ 70 +
        8536465098498926588670274543134803354826655738492801095572266172370193) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 308,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (307 - x)) = _
  rw [show 308 = 125 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 8 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_307_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 126,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (308 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 144,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (308 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_308 :
    recurrence4B3A3.coeff 308 =
      (((5296178052 * 10 ^ 70 +
        9208862000220236101772512738676544777532709762259015995377642046828864) * 10 ^ 70 +
        1773118394559484636539528732473897541113505688387358090306667430526649) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 309,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (308 - x)) = _
  rw [show 309 = 126 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 7 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_308_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 127,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (309 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 145,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (309 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_309 :
    recurrence4B3A3.coeff 309 =
      -(((209026623 * 10 ^ 70 +
        9837187814469460978081572231658942296423526286412745437169449597844258) * 10 ^ 70 +
        5652777586221937589372208864760764834447375594920394554024591131053420) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 310,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (309 - x)) = _
  rw [show 310 = 127 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 6 +
      145 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_309_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 128,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (310 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 146,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (310 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_310 :
    recurrence4B3A3.coeff 310 =
      -(((8166480 * 10 ^ 70 +
        4516128630941084092026038293921867358597725756502809968831736967717075) * 10 ^ 70 +
        4731005718893817726240438652887687669656223872090880244989485340837155) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 311,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (310 - x)) = _
  rw [show 311 = 128 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 5 +
      146 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_310_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 129,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (311 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 147,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (311 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_311 :
    recurrence4B3A3.coeff 311 =
      (((2240525 * 10 ^ 70 +
        7319983109516943300211275286599326035583257707231574689025573686082111) * 10 ^ 70 +
        5531075211959961993981934276861003389641100779360679615485994031671588) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 312,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (311 - x)) = _
  rw [show 312 = 129 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 4 +
      147 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_311_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 130,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (312 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 148,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (312 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_312 :
    recurrence4B3A3.coeff 312 =
      -(((204917 * 10 ^ 70 +
        1575050785750216940847369985174997454992682047584624786846303443483607) * 10 ^ 70 +
        9377978343683187331852870929566717617122621471207609307990657011496828) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 313,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (312 - x)) = _
  rw [show 313 = 130 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 3 +
      148 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_312_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 131,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (313 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 149,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (313 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_313 :
    recurrence4B3A3.coeff 313 =
      (((10483 * 10 ^ 70 +
        7820410902268148236355586711144779101218616435556789334143137897892501) * 10 ^ 70 +
        6822287957715437834107381556663713053298314183593036543625623942641397) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 314,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (313 - x)) = _
  rw [show 314 = 131 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 2 +
      149 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_313_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 132,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (314 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 150,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (314 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_314 :
    recurrence4B3A3.coeff 314 =
      -(((181 * 10 ^ 70 +
        2605010098219197355862098587864923965283923247190377093799334246328145) * 10 ^ 70 +
        7119609377758410930907137667225818025278603897737437886426133059241660) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 315,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (314 - x)) = _
  rw [show 315 = 132 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 1 +
      150 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_314_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 133,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (315 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 151,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (315 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_315 :
    recurrence4B3A3.coeff 315 =
      -(((15 * 10 ^ 70 +
        5868348938052610382906352076753718391412462847420577304753287069869472) * 10 ^ 70 +
        1061901066252889297710900147119053176262338268438388678094558412155443) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 316,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (315 - x)) = _
  rw [show 316 = 133 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_315_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 134,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (316 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 152,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (316 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_316 :
    recurrence4B3A3.coeff 316 =
      (((1 * 10 ^ 70 +
        2779243995993513209732663323458124153942772012078435867293862970963691) * 10 ^ 70 +
        1560115160698592202667808273033700188817974808969859729551656043732753) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 317,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (316 - x)) = _
  rw [show 317 = 134 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 31 +
      152 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_316_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 135,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (317 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 153,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (317 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_317 :
    recurrence4B3A3.coeff 317 =
      -((317330627654217927513646629430620937703208792437694326518896027399846 * 10 ^ 70 +
        9868700659074632124382432469520586231209879900295293101573498500118295) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 318,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (317 - x)) = _
  rw [show 318 = 135 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 30 +
      153 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_317_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 136,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (318 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 154,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (318 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_318 :
    recurrence4B3A3.coeff 318 =
      -((5574553762225364730270374481381245788282690118943645090392666321990 * 10 ^ 70 +
        7794682829727789728385253064951361319405222288094216713262714990363745) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 319,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (318 - x)) = _
  rw [show 319 = 136 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 29 +
      154 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_318_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 137,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (319 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 155,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (319 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_319 :
    recurrence4B3A3.coeff 319 =
      ((427882495424271404063921190374980547599717348877874646432677364713 * 10 ^ 70 +
        3119813578208334202928951345175719111125560673885800834092899411753063) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 320,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (319 - x)) = _
  rw [show 320 = 137 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 28 +
      155 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_319_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 138,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (320 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 156,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (320 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_320 :
    recurrence4B3A3.coeff 320 =
      -((1575810441584659592235991083819609706001859068070067095944294764 * 10 ^ 70 +
        2953865673918564850217387618083219159923562502361350165782077902846610) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 321,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (320 - x)) = _
  rw [show 321 = 138 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 27 +
      156 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_320_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 139,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (321 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 157,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (321 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_321 :
    recurrence4B3A3.coeff 321 =
      -((200106119016883849057575081102329832389066520130639342489022975 * 10 ^ 70 +
        7864490674812043303084662457604831334339873255969893206445481492537674) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 322,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (321 - x)) = _
  rw [show 322 = 139 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 26 +
      157 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_321_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 140,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (322 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 158,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (322 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_322 :
    recurrence4B3A3.coeff 322 =
      -((293060071971965252058838075360775851430710243919083327073279 * 10 ^ 70 +
        6466946528580022743568151013463476807329541090362690515206142629563358) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 323,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (322 - x)) = _
  rw [show 323 = 140 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 25 +
      158 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_322_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 141,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (323 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 159,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (323 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_323 :
    recurrence4B3A3.coeff 323 =
      ((31473773542116605867524346515895291259965244236146774152210 * 10 ^ 70 +
        7874119695026904505095476950133747934522273952136799899035332231691661) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 324,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (323 - x)) = _
  rw [show 324 = 141 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 24 +
      159 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_323_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 142,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (324 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 160,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (324 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_324 :
    recurrence4B3A3.coeff 324 =
      ((238537492799216512239845012553089252287045226110124150211 * 10 ^ 70 +
        5620871676227918393337011569108152922340903929037746156523409630203829) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 325,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (324 - x)) = _
  rw [show 325 = 142 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 23 +
      160 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_324_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 143,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (325 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 161,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (325 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_325 :
    recurrence4B3A3.coeff 325 =
      -((251473147568101933861687218486926663765461805101743617 * 10 ^ 70 +
        5026804860613764078902133680383832400630310154240861041237973554919330) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 326,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (325 - x)) = _
  rw [show 326 = 143 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 22 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_325_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 144,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (326 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 162,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (326 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_326 :
    recurrence4B3A3.coeff 326 =
      -((7943795490208979660731966067078416402396322330642522 * 10 ^ 70 +
        7784406139579207214086300612147736024950539908803681327363331435677257) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 327,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (326 - x)) = _
  rw [show 327 = 144 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 21 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_326_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 145,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (327 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 163,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (327 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_327 :
    recurrence4B3A3.coeff 327 =
      -((19572123682627594333355280293530555853560363889726 * 10 ^ 70 +
        4888996514519526668529162249216550890541986681254422960000180313659206) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 328,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (327 - x)) = _
  rw [show 328 = 145 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 20 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_327_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 146,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (328 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 164,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (328 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_328 :
    recurrence4B3A3.coeff 328 =
      ((49044383273069594192215275324609207071273977446 * 10 ^ 70 +
        6921118333425870886547895626665093204877151782959119700063431593177349) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 329,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (328 - x)) = _
  rw [show 329 = 146 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 19 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_328_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 147,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (329 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 165,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (329 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_329 :
    recurrence4B3A3.coeff 329 =
      ((218709142101810839237031500354437963693586138 * 10 ^ 70 +
        4579222343651986271261463427304159119087993809946306673236354068529789) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 330,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (329 - x)) = _
  rw [show 330 = 147 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 18 +
      165 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_329_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 148,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (330 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 166,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (330 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_330 :
    recurrence4B3A3.coeff 330 =
      -((60004249742314093267578794505736980946052 * 10 ^ 70 +
        1105745174715541101482667058952703227816928851904477850765610849585478) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 331,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (330 - x)) = _
  rw [show 331 = 148 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 17 +
      166 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_330_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 149,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (331 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 167,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (331 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_331 :
    recurrence4B3A3.coeff 331 =
      -((840638672159945688743309984756051385286 * 10 ^ 70 +
        8388367790896634248341095998622976500818219655659074550094455143574590) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 332,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (331 - x)) = _
  rw [show 332 = 149 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 16 +
      167 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_331_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 150,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (332 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 168,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (332 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_332 :
    recurrence4B3A3.coeff 332 =
      -((165659312141218293867449781303076216 * 10 ^ 70 +
        2046031640619215027073065749503410593348133922449287338762814837606655) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 333,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (332 - x)) = _
  rw [show 333 = 150 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 15 +
      168 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_332_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 151,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (333 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 169,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (333 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_333 :
    recurrence4B3A3.coeff 333 =
      ((1212001109888034307098170814910321 * 10 ^ 70 +
        7912392627639626502438776679015621806331289963656344347858379244799983) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 334,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (333 - x)) = _
  rw [show 334 = 151 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 14 +
      169 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_333_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 152,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (334 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 170,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (334 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_334 :
    recurrence4B3A3.coeff 334 =
      ((328860541003318769874109782885 * 10 ^ 70 +
        8053413055461951673209807210728983565833526526049463871258386162152279) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 335,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (334 - x)) = _
  rw [show 335 = 152 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 13 +
      170 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_334_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 153,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (335 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 171,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (335 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_335 :
    recurrence4B3A3.coeff 335 =
      -((369500153938215449772847787 * 10 ^ 70 +
        9351561765160702305709875762529361571665332434167421323643597521176251) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 336,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (335 - x)) = _
  rw [show 336 = 153 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 12 +
      171 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_335_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 154,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (336 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 172,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (336 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_336 :
    recurrence4B3A3.coeff 336 =
      -((66536024543333453476876 * 10 ^ 70 +
        5450429728863595495519312035827577652856927836333371756100495037165913) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 337,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (336 - x)) = _
  rw [show 337 = 154 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 11 +
      172 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_336_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 155,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (337 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 173,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (337 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_337 :
    recurrence4B3A3.coeff 337 =
      ((12158166416674343972 * 10 ^ 70 +
        9002068886828204118173479283073346698071546516559989376961435496564061) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 338,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (337 - x)) = _
  rw [show 338 = 155 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 10 +
      173 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_337_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 156,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (338 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 174,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (338 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_338 :
    recurrence4B3A3.coeff 338 =
      ((982969062409953 * 10 ^ 70 +
        7034253323484021467754744900538373403774585602812795169936281113722707) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 339,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (338 - x)) = _
  rw [show 339 = 156 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 9 +
      174 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_338_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 157,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (339 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 175,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (339 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_339 :
    recurrence4B3A3.coeff 339 =
      -((28695655203 * 10 ^ 70 +
        2055258521498779536182837052564263457142942940090194521729540794731061) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 340,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (339 - x)) = _
  rw [show 340 = 157 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 8 +
      175 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_339_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 158,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (340 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 176,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (340 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_340 :
    recurrence4B3A3.coeff 340 =
      -((754026 * 10 ^ 70 +
        8708015096502294711013361743276974093548983857075751147043306978783578) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 341,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (340 - x)) = _
  rw [show 341 = 158 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 7 +
      176 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_340_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 159,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (341 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 177,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (341 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_341 :
    recurrence4B3A3.coeff 341 =
      ((2 * 10 ^ 70 +
        9956417577900696938560386782097165574218696177621852968589296437430283) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 342,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (341 - x)) = _
  rw [show 342 = 159 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 6 +
      177 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_341_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 160,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (342 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 178,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (342 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_342 :
    recurrence4B3A3.coeff 342 =
      (166200577260865696213783152421897361960008116830691993548602083809 : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 343,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (342 - x)) = _
  rw [show 343 = 160 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 5 +
      178 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_342_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 161,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (343 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 179,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (343 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_343 :
    recurrence4B3A3.coeff 343 =
      (-65964408095844150986211479570731191572132853184750281546146 : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 344,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (343 - x)) = _
  rw [show 344 = 161 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 4 +
      179 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_343_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 162,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (344 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 180,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (344 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_344 :
    recurrence4B3A3.coeff 344 =
      (-37067519174062366567404384624756845455296850857098735 : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 345,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (344 - x)) = _
  rw [show 345 = 162 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 3 +
      180 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_344_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 163,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (345 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 181,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (345 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_345 :
    recurrence4B3A3.coeff 345 =
      (784397845382310995461708061609246340245151660 : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 346,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (345 - x)) = _
  rw [show 346 = 163 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 2 +
      181 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_345_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A3_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 164,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (346 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 182,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (346 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_346 :
    recurrence4B3A3.coeff 346 =
      (8446737236647738989518319492449559300 : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 347,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (346 - x)) = _
  rw [show 347 = 164 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 1 +
      182 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_346_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
