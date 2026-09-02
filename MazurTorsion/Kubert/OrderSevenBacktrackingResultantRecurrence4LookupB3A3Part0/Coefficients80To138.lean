/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3A3Part0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: B3A3 coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4A3_coeff_0
  recurrence4A3_coeff_1
  recurrence4A3_coeff_10
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
  recurrence4A3_coeff_11
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
  recurrence4A3_coeff_12
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
  recurrence4A3_coeff_13
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
  recurrence4A3_coeff_14
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
  recurrence4A3_coeff_15
  recurrence4A3_coeff_150
  recurrence4A3_coeff_151
  recurrence4A3_coeff_152
  recurrence4A3_coeff_153
  recurrence4A3_coeff_154
  recurrence4A3_coeff_155

attribute [local simp]
  recurrence4A3_coeff_156
  recurrence4A3_coeff_157
  recurrence4A3_coeff_158
  recurrence4A3_coeff_159
  recurrence4A3_coeff_16
  recurrence4A3_coeff_160
  recurrence4A3_coeff_161
  recurrence4A3_coeff_162
  recurrence4A3_coeff_163
  recurrence4A3_coeff_164
  recurrence4A3_coeff_165
  recurrence4A3_coeff_166
  recurrence4A3_coeff_167
  recurrence4A3_coeff_168
  recurrence4A3_coeff_169
  recurrence4A3_coeff_17
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
  recurrence4A3_coeff_18
  recurrence4A3_coeff_180
  recurrence4A3_coeff_181
  recurrence4A3_coeff_182
  recurrence4A3_coeff_19
  recurrence4A3_coeff_2
  recurrence4A3_coeff_20
  recurrence4A3_coeff_21
  recurrence4A3_coeff_22
  recurrence4A3_coeff_23
  recurrence4A3_coeff_24
  recurrence4A3_coeff_25
  recurrence4A3_coeff_26
  recurrence4A3_coeff_27
  recurrence4A3_coeff_28
  recurrence4A3_coeff_29
  recurrence4A3_coeff_3
  recurrence4A3_coeff_30
  recurrence4A3_coeff_31
  recurrence4A3_coeff_32
  recurrence4A3_coeff_33
  recurrence4A3_coeff_34
  recurrence4A3_coeff_35
  recurrence4A3_coeff_36
  recurrence4A3_coeff_37
  recurrence4A3_coeff_38
  recurrence4A3_coeff_39
  recurrence4A3_coeff_4
  recurrence4A3_coeff_40
  recurrence4A3_coeff_41
  recurrence4A3_coeff_42
  recurrence4A3_coeff_43
  recurrence4A3_coeff_44
  recurrence4A3_coeff_45
  recurrence4A3_coeff_46
  recurrence4A3_coeff_47
  recurrence4A3_coeff_48
  recurrence4A3_coeff_49

attribute [local simp]
  recurrence4A3_coeff_5
  recurrence4A3_coeff_50
  recurrence4A3_coeff_51
  recurrence4A3_coeff_52
  recurrence4A3_coeff_53
  recurrence4A3_coeff_54
  recurrence4A3_coeff_55
  recurrence4A3_coeff_56
  recurrence4A3_coeff_57
  recurrence4A3_coeff_58
  recurrence4A3_coeff_59
  recurrence4A3_coeff_6
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
  recurrence4A3_coeff_7
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
  recurrence4A3_coeff_8
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
  recurrence4A3_coeff_9
  recurrence4A3_coeff_90
  recurrence4A3_coeff_91
  recurrence4A3_coeff_92
  recurrence4A3_coeff_93
  recurrence4A3_coeff_94
  recurrence4A3_coeff_95
  recurrence4A3_coeff_96
  recurrence4A3_coeff_97
  recurrence4A3_coeff_98
  recurrence4A3_coeff_99
  recurrence4B3_coeff_0
  recurrence4B3_coeff_1
  recurrence4B3_coeff_10
  recurrence4B3_coeff_100
  recurrence4B3_coeff_101
  recurrence4B3_coeff_102
  recurrence4B3_coeff_103
  recurrence4B3_coeff_104
  recurrence4B3_coeff_105

attribute [local simp]
  recurrence4B3_coeff_106
  recurrence4B3_coeff_107
  recurrence4B3_coeff_108
  recurrence4B3_coeff_109
  recurrence4B3_coeff_11
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
  recurrence4B3_coeff_12
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
  recurrence4B3_coeff_13
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
  recurrence4B3_coeff_14
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
  recurrence4B3_coeff_15
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
  recurrence4B3_coeff_16
  recurrence4B3_coeff_160
  recurrence4B3_coeff_161
  recurrence4B3_coeff_162
  recurrence4B3_coeff_163

attribute [local simp]
  recurrence4B3_coeff_164
  recurrence4B3_coeff_17
  recurrence4B3_coeff_18
  recurrence4B3_coeff_19
  recurrence4B3_coeff_2
  recurrence4B3_coeff_20
  recurrence4B3_coeff_21
  recurrence4B3_coeff_22
  recurrence4B3_coeff_23
  recurrence4B3_coeff_24
  recurrence4B3_coeff_25
  recurrence4B3_coeff_26
  recurrence4B3_coeff_27
  recurrence4B3_coeff_28
  recurrence4B3_coeff_29
  recurrence4B3_coeff_3
  recurrence4B3_coeff_30
  recurrence4B3_coeff_31
  recurrence4B3_coeff_32
  recurrence4B3_coeff_33
  recurrence4B3_coeff_34
  recurrence4B3_coeff_35
  recurrence4B3_coeff_36
  recurrence4B3_coeff_37
  recurrence4B3_coeff_38
  recurrence4B3_coeff_39
  recurrence4B3_coeff_4
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
  recurrence4B3_coeff_5
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
  recurrence4B3_coeff_6
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
  recurrence4B3_coeff_7
  recurrence4B3_coeff_70
  recurrence4B3_coeff_71
  recurrence4B3_coeff_72
  recurrence4B3_coeff_73

attribute [local simp]
  recurrence4B3_coeff_74
  recurrence4B3_coeff_75
  recurrence4B3_coeff_76
  recurrence4B3_coeff_77
  recurrence4B3_coeff_78
  recurrence4B3_coeff_79
  recurrence4B3_coeff_8
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
  recurrence4B3_coeff_9
  recurrence4B3_coeff_90
  recurrence4B3_coeff_91
  recurrence4B3_coeff_92
  recurrence4B3_coeff_93
  recurrence4B3_coeff_94
  recurrence4B3_coeff_95
  recurrence4B3_coeff_96
  recurrence4B3_coeff_97
  recurrence4B3_coeff_98
  recurrence4B3_coeff_99

theorem recurrence4B3A3_coeff_80 :
    recurrence4B3A3.coeff 80 =
      -(((15453721930853017708888991 * 10 ^ 70 +
        4551367354388304104617582932346132503431548479993218363727679942451040) * 10 ^ 70 +
        6920635666721316592739053229454751672640386062292350985917026004886917) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 81,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (80 - x)) = _
  rw [show 81 = 0 +
    81 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_81 :
    recurrence4B3A3.coeff 81 =
      (((119570363796676093959971090 * 10 ^ 70 +
        8304889849945216187391818823872963773194576875567372126292756184380502) * 10 ^ 70 +
        0520152993100557520840316059241737810203381513402886062143259491277707) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 82,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (81 - x)) = _
  rw [show 82 = 0 +
    82 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_82 :
    recurrence4B3A3.coeff 82 =
      -(((896426063203731012609313975 * 10 ^ 70 +
        5841800100873871845670398845376108087743525401111940038048812392329756) * 10 ^ 70 +
        9670391104630950750788656132327762462500635113082862817551424032457909) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 83,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (82 - x)) = _
  rw [show 83 = 0 +
    83 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_83 :
    recurrence4B3A3.coeff 83 =
      (((6515147039143166748813286594 * 10 ^ 70 +
        5082824794396001230523701362984315672801451777076519658958609643438248) * 10 ^ 70 +
        8945782299656466400826661026144568681359193232767652255484585379699131) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 84,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (83 - x)) = _
  rw [show 84 = 0 +
    84 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_84 :
    recurrence4B3A3.coeff 84 =
      -(((45926183492967763257655010685 * 10 ^ 70 +
        0378711693381209709219433804117743470356743935936849777488860201121157) * 10 ^ 70 +
        0737470206206567483663092356948499716814529827207738687966483089711348) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 85,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (84 - x)) = _
  rw [show 85 = 0 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_85 :
    recurrence4B3A3.coeff 85 =
      (((314138094119025943494787858374 * 10 ^ 70 +
        3667467889109839397846189261162360077180695138686835047521944155805849) * 10 ^ 70 +
        9155650386125834163135191247634941702880106201469702614013730232490408) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 86,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (85 - x)) = _
  rw [show 86 = 0 +
    86 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_86 :
    recurrence4B3A3.coeff 86 =
      -(((2085900820639151045914912906301 * 10 ^ 70 +
        2201682088398910902173329640187820665177144361298536058425830716781173) * 10 ^ 70 +
        5532601992420633457538304493752547824374719338049493928593916303862801) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 87,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (86 - x)) = _
  rw [show 87 = 0 +
    87 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_87 :
    recurrence4B3A3.coeff 87 =
      (((13451163587095922353437235541955 * 10 ^ 70 +
        4297097292085543818098003068848219796828999328489548249823512261421582) * 10 ^ 70 +
        7858931729619661454891034393573656955822703090380007137566331342590524) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 88,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (87 - x)) = _
  rw [show 88 = 0 +
    88 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_88 :
    recurrence4B3A3.coeff 88 =
      -(((84273650028912159652996437616415 * 10 ^ 70 +
        8289677124306850623092536790211829125047774995160403340652144890843453) * 10 ^ 70 +
        3244488700036014198632749918002811600851442508736639887770864498824464) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 89,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (88 - x)) = _
  rw [show 89 = 0 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_89 :
    recurrence4B3A3.coeff 89 =
      (((513162464376428408954687967908022 * 10 ^ 70 +
        0950080895104285103049110018050224496065216734337673161462697239406052) * 10 ^ 70 +
        9330761627588037742225300516860059046981500312162248352377355978016541) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 90,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (89 - x)) = _
  rw [show 90 = 0 +
    90 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_90 :
    recurrence4B3A3.coeff 90 =
      -(((3038139409089611716130860954080254 * 10 ^ 70 +
        0927317827512764561492820197057864045678446156450542152824853977282463) * 10 ^ 70 +
        2706430881410725254668285241935056346320156053500247571991025884383930) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 91,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (90 - x)) = _
  rw [show 91 = 0 +
    91 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_91 :
    recurrence4B3A3.coeff 91 =
      (((17494538876578744408593515051997391 * 10 ^ 70 +
        5782401657006452806915102766298533087002276721394930628973733461375650) * 10 ^ 70 +
        1700347823858865558910427184135090318512732754490979607666666538062724) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 92,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (91 - x)) = _
  rw [show 92 = 0 +
    92 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 92 = 32 +
      60 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B3A3_coeff_92 :
    recurrence4B3A3.coeff 92 =
      -(((98013416948359976629223924628847991 * 10 ^ 70 +
        0904007208042728240467130777837393539988595797669265075824281508723197) * 10 ^ 70 +
        4902659865247855309934873744504764488745801198471864759392623156109643) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 93,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (92 - x)) = _
  rw [show 93 = 0 +
    93 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 93 = 32 +
      61 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B3A3_coeff_93 :
    recurrence4B3A3.coeff 93 =
      (((534438022187690123588910447219380773 * 10 ^ 70 +
        9410634330858511926693636410265212348885953932565186934438684878551938) * 10 ^ 70 +
        0544780280744438714554432512242950329950093118979132765719713537551135) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 94,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (93 - x)) = _
  rw [show 94 = 0 +
    94 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 94 = 32 +
      62 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B3A3_coeff_94 :
    recurrence4B3A3.coeff 94 =
      -(((2837090046219056597058772634570036085 * 10 ^ 70 +
        5912912981470495968580888432827076302482048428524258855384901117755581) * 10 ^ 70 +
        0871332593582896076074126771946121255548468707119482827902781128168771) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 95,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (94 - x)) = _
  rw [show 95 = 0 +
    95 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_95 :
    recurrence4B3A3.coeff 95 =
      (((14667053580248057701328839892604161608 * 10 ^ 70 +
        8299183922971093903076835327659214674932753244297190986776568509094982) * 10 ^ 70 +
        9536665274595409184371898248358875888210186592591018583263309211887035) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 96,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (95 - x)) = _
  rw [show 96 = 0 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_96 :
    recurrence4B3A3.coeff 96 =
      -(((73863819576149012326358771365257352049 * 10 ^ 70 +
        9174316908730970030592426683768118951680220020376784760516077187185790) * 10 ^ 70 +
        5277891148125437305412026174336196136894885200501231963832492431049935) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 97,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (96 - x)) = _
  rw [show 97 = 0 +
    97 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_97 :
    recurrence4B3A3.coeff 97 =
      (((362460121113085449111430645591257928926 * 10 ^ 70 +
        7140282083771943889097622794443377983121209707208101267021836960430724) * 10 ^ 70 +
        5594671853916757949525704128892972209947292882989100900741844743179096) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 98,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (97 - x)) = _
  rw [show 98 = 0 +
    98 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_98 :
    recurrence4B3A3.coeff 98 =
      -(((1733581533642381378380897784606092388873 * 10 ^ 70 +
        4370179335922016028877890993946095543449476546909492174602954355564502) * 10 ^ 70 +
        1162314312154579460408187817539397554717302594045158522432177284468595) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 99,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (98 - x)) = _
  rw [show 99 = 0 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_99 :
    recurrence4B3A3.coeff 99 =
      (((8083428075406988659320217504145445519634 * 10 ^ 70 +
        7629374409266947310206791152797052814610064730449569260955742305641405) * 10 ^ 70 +
        6754410392470741949849219339514685879407911637849939250155388009313039) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 100,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (99 - x)) = _
  rw [show 100 = 0 +
    100 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_100 :
    recurrence4B3A3.coeff 100 =
      -(((36755448319282185505972726419822586199853 * 10 ^ 70 +
        8650089412516608028964584419791422670961422936818648141171672572393804) * 10 ^ 70 +
        4492890505558878535532093877895478896636389411747572189335680682940680) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 101,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (100 - x)) = _
  rw [show 101 = 0 +
    101 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_101 :
    recurrence4B3A3.coeff 101 =
      (((163014533360109177890745536641060915044545 * 10 ^ 70 +
        3154400742345124734500609350217152674972230082967136864390482896777468) * 10 ^ 70 +
        1974155576394566300668323739280573763329880544457921185042560123799879) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 102,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (101 - x)) = _
  rw [show 102 = 0 +
    102 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_102 :
    recurrence4B3A3.coeff 102 =
      -(((705357333986786136617704753667173047848836 * 10 ^ 70 +
        6474499272252356853932143465850249830250919355001373002860349357150909) * 10 ^ 70 +
        7486824632681182353043997462973425714861580778361701802375030571086690) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 103,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (102 - x)) = _
  rw [show 103 = 0 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_103 :
    recurrence4B3A3.coeff 103 =
      (((2978286306602881935427218601355200133900013 * 10 ^ 70 +
        3480661897533340921343749430898538891701293144209294114705617968231563) * 10 ^ 70 +
        1347867163624037351920489879003078835531207859115501659003046776159535) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 104,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (103 - x)) = _
  rw [show 104 = 0 +
    104 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_104 :
    recurrence4B3A3.coeff 104 =
      -(((12274129496582101021982136475397110706946053 * 10 ^ 70 +
        6972225344313362676627524931188845385233999910904739108510033692790935) * 10 ^ 70 +
        7060570827246122631422215064127536912010548199432447469181252074751324) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 105,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (104 - x)) = _
  rw [show 105 = 0 +
    105 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_105 :
    recurrence4B3A3.coeff 105 =
      (((49382280767081145384623969019429065284316477 * 10 ^ 70 +
        3121821470461153634205998905498972967007722621394262098526383361611843) * 10 ^ 70 +
        4004989686545071422102547386480348954200991625691444531049735688901412) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 106,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (105 - x)) = _
  rw [show 106 = 0 +
    106 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_106 :
    recurrence4B3A3.coeff 106 =
      -(((193996400446966903835093609984288506068392960 * 10 ^ 70 +
        4743258358664080654422981590430978037364933281623875435458424796461057) * 10 ^ 70 +
        7008132059856781800470503193969656062607139444844305832707745479691514) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 107,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (106 - x)) = _
  rw [show 107 = 0 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_107 :
    recurrence4B3A3.coeff 107 =
      (((744287970521353799622331917505343539813485220 * 10 ^ 70 +
        6932587479731149670677145914009764233344668578350921008855680204660642) * 10 ^ 70 +
        0518759838592637761381663771752217675482608429104715372892820378437921) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 108,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (107 - x)) = _
  rw [show 108 = 0 +
    108 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_108 :
    recurrence4B3A3.coeff 108 =
      -(((2789284231372069342396016618246016220968688903 * 10 ^ 70 +
        4743887326723169331697375917470422548464257841562988994884292261503117) * 10 ^ 70 +
        6813365411504370785176087611188910900965594205892662411728822354327139) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 109,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (108 - x)) = _
  rw [show 109 = 0 +
    109 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_109 :
    recurrence4B3A3.coeff 109 =
      (((10212349250172835827584739399419531955615364460 * 10 ^ 70 +
        1281955751862713497823155054073320233883352382874320074004874872980828) * 10 ^ 70 +
        3051971577412390748096845286845259037338699712304585319614006961172004) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 110,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (109 - x)) = _
  rw [show 110 = 0 +
    110 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_110 :
    recurrence4B3A3.coeff 110 =
      -(((36535365596941737522505920113802224983061944266 * 10 ^ 70 +
        4150536886752906648151691922643476865282002082653101916611782385996037) * 10 ^ 70 +
        1178147887228887020508360185298487810740400918064752756292319813574871) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 111,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (110 - x)) = _
  rw [show 111 = 0 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_111 :
    recurrence4B3A3.coeff 111 =
      (((127740079362288940382824700706672301245825671896 * 10 ^ 70 +
        7277116039161103349569101386809880229939723484310350329402000394059026) * 10 ^ 70 +
        9883058648484536160163101739439623098849190922026427703230880684826666) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 112,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (111 - x)) = _
  rw [show 112 = 0 +
    112 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_112 :
    recurrence4B3A3.coeff 112 =
      -(((436551163025571962396820639458833559334985139980 * 10 ^ 70 +
        0497316025941108782410680136854459673405281666706117740800291371558789) * 10 ^ 70 +
        8499285311449253470921957837642101506139599828642058399105742868556582) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 113,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (112 - x)) = _
  rw [show 113 = 0 +
    113 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_113 :
    recurrence4B3A3.coeff 113 =
      (((1458488698995058303498346135359338565738794044628 * 10 ^ 70 +
        6773498002799156856973154474191357862843673774596282566415532049945739) * 10 ^ 70 +
        2955282012764733816330968263481427525844642120760013541532693400390772) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 114,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (113 - x)) = _
  rw [show 114 = 0 +
    114 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_114 :
    recurrence4B3A3.coeff 114 =
      -(((4764245287638895136619220302732658824943127127576 * 10 ^ 70 +
        2215198380217059250519922231108138943789804913630131598485086048770266) * 10 ^ 70 +
        0947585290607681034095890859149032487084277998142735929536959657663912) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 115,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (114 - x)) = _
  rw [show 115 = 0 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_115 :
    recurrence4B3A3.coeff 115 =
      (((15218400259634099834256316477751412947066269292995 * 10 ^ 70 +
        1731611276213332479131606235301942969504321496322985584868367148627909) * 10 ^ 70 +
        2796919286274083030670763332863682802493807850948747887345448432296376) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 116,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (115 - x)) = _
  rw [show 116 = 0 +
    116 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_116 :
    recurrence4B3A3.coeff 116 =
      -(((47542943871138426711725311654299425063436349017178 * 10 ^ 70 +
        1549630813062073531387774802158320095491854358691460113367521242291300) * 10 ^ 70 +
        5686358103455925595875817376418461792558461490136540847916614336082773) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 117,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (116 - x)) = _
  rw [show 117 = 0 +
    117 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_117 :
    recurrence4B3A3.coeff 117 =
      (((145278495116777939926409064055635952649997625598560 * 10 ^ 70 +
        8663399054543146346571243643219971704250126429562861615369445730262395) * 10 ^ 70 +
        7126636825427573121279391656067894657013639358734594263467892142025602) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 118,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (117 - x)) = _
  rw [show 118 = 0 +
    118 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_118 :
    recurrence4B3A3.coeff 118 =
      -(((434278725008955881340759552815207538478959448238230 * 10 ^ 70 +
        8013912551240536258204016109846203071087367066863245449279530759367558) * 10 ^ 70 +
        6266600582506829335266405903412574628098244887139859236207648121324438) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 119,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (118 - x)) = _
  rw [show 119 = 0 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_119 :
    recurrence4B3A3.coeff 119 =
      (((1270104064155195275844292270839053054559356931650660 * 10 ^ 70 +
        3975958569607219966498470492629178624366495689708551846200122746066148) * 10 ^ 70 +
        2259606614088214252418918965604432206239180499034065615647014365003671) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 120,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (119 - x)) = _
  rw [show 120 = 0 +
    120 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_120 :
    recurrence4B3A3.coeff 120 =
      -(((3634653559290836856613294477683601947279951236936672 * 10 ^ 70 +
        8521605374156185093171917739015306638349876531949374053371449991255204) * 10 ^ 70 +
        4104107547205240296619956963393811279916411133399566930761056226537697) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 121,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (120 - x)) = _
  rw [show 121 = 0 +
    121 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_121 :
    recurrence4B3A3.coeff 121 =
      (((10178576703087893521484454149487828593215477847288871 * 10 ^ 70 +
        1107037472194502102693591307691988990493296937918480451421993657896762) * 10 ^ 70 +
        3955835098661266082691855768203874941977276902768573502847746889022439) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 122,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (121 - x)) = _
  rw [show 122 = 0 +
    122 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_122 :
    recurrence4B3A3.coeff 122 =
      -(((27896949539067589009227497710968225968396859237337782 * 10 ^ 70 +
        0964885970891119908560403374855152383711761029867640367567834644507645) * 10 ^ 70 +
        4355064460991226877631444771084333193196627168638254513964402489087631) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 123,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (122 - x)) = _
  rw [show 123 = 0 +
    123 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_123 :
    recurrence4B3A3.coeff 123 =
      (((74836822078243251374939710551059728611503347778503306 * 10 ^ 70 +
        7777563863334124975609396175235104837887600308984679865356442592132483) * 10 ^ 70 +
        9769158051692817781439760484143759854638200078499520507483256923274860) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 124,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (123 - x)) = _
  rw [show 124 = 0 +
    124 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B3A3_coeff_124 :
    recurrence4B3A3.coeff 124 =
      -(((196518884637232506430898959990006948736367126139235575 * 10 ^ 70 +
        5054363862723545376443597193706807891556342650181563088977936918398334) * 10 ^ 70 +
        7800823136064883185734934797505262170825371893852197223913719445854239) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 125,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (124 - x)) = _
  rw [show 125 = 0 +
    125 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B3A3_coeff_125 :
    recurrence4B3A3.coeff 125 =
      (((505199650429950850715390844263500962906925643495787600 * 10 ^ 70 +
        5546160060750423900168349407187454279792300873454342975249977051883580) * 10 ^ 70 +
        1908570137081016412845628224120979119944533356027583618659361264291266) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 126,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (125 - x)) = _
  rw [show 126 = 0 +
    126 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B3A3_coeff_126 :
    recurrence4B3A3.coeff 126 =
      -(((1271537502010994931878394917020487889022767257163356921 * 10 ^ 70 +
        7814455016109535378722016058209853182542701512129981581922625751484632) * 10 ^ 70 +
        1005790362073344763177667809571027178739309713850850331000691493074422) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 127,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (126 - x)) = _
  rw [show 127 = 0 +
    127 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_127 :
    recurrence4B3A3.coeff 127 =
      (((3133562923170861209443280166781151505132475300931560036 * 10 ^ 70 +
        0877508033123144253600111228957310308216585967808687490580398750747755) * 10 ^ 70 +
        6503981697098523463411529042978135954366267911532962613982126812424727) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 128,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (127 - x)) = _
  rw [show 128 = 0 +
    128 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_128 :
    recurrence4B3A3.coeff 128 =
      -(((7561791286652043160436249455401637694160321691663815116 * 10 ^ 70 +
        4216520217530072329689977147669643252318290304513701000383897098325561) * 10 ^ 70 +
        2639738911557566466019016989154456375805954559842370191712109188870851) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 129,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (128 - x)) = _
  rw [show 129 = 0 +
    129 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_129 :
    recurrence4B3A3.coeff 129 =
      (((17869815575204822485861880680431944245142082168559563767 * 10 ^ 70 +
        2642494355235734155272434969178760297419672933351152607884346424330519) * 10 ^ 70 +
        7224686278362300208908143529936847058654478444473134186596520641940069) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 130,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (129 - x)) = _
  rw [show 130 = 0 +
    130 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_130 :
    recurrence4B3A3.coeff 130 =
      -(((41357557069400606491109877060791395478253990739209708837 * 10 ^ 70 +
        9507871421640239812884443119067173871279365070219294265780990344898355) * 10 ^ 70 +
        5434065135595702079891849431186452988281805604283038652613791772312163) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 131,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (130 - x)) = _
  rw [show 131 = 0 +
    131 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_131 :
    recurrence4B3A3.coeff 131 =
      (((93747054292404548098307968468598180612184040617832271957 * 10 ^ 70 +
        9180215831216009654612724014378932319957266885798059941686519267172841) * 10 ^ 70 +
        6389955856167392140220249260234445237056705146031752674493063962463786) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 132,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (131 - x)) = _
  rw [show 132 = 0 +
    132 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_132 :
    recurrence4B3A3.coeff 132 =
      -(((208139770754812327638720078309267274473657590921916534481 * 10 ^ 70 +
        5547650248345277148443180591602514695472704297928969703832472406584431) * 10 ^ 70 +
        5419212349446138215101432298848300899203754250069960948059458031062837) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 133,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (132 - x)) = _
  rw [show 133 = 0 +
    133 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_133 :
    recurrence4B3A3.coeff 133 =
      (((452660049939353175020617807020556038506491960500866920328 * 10 ^ 70 +
        4561849602688599918650340165497542329619889807541550255574838110089366) * 10 ^ 70 +
        2920995235471760005091226202541275940297791930242202284297531104126148) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 134,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (133 - x)) = _
  rw [show 134 = 0 +
    134 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_134 :
    recurrence4B3A3.coeff 134 =
      -(((964344246628250267987059068533280797649510332978443425341 * 10 ^ 70 +
        7967152777879196992709609404098645708315109622304469093905853487308400) * 10 ^ 70 +
        1371872523752766924050434374010719526365551519553882002435173845626020) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 135,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (134 - x)) = _
  rw [show 135 = 0 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_135 :
    recurrence4B3A3.coeff 135 =
      (((2012594265504518299410899817283699192016744344274493535104 * 10 ^ 70 +
        0008953374309904541984980580936457137126726620718090215477169877695042) * 10 ^ 70 +
        6077900598668429405830066204599236706837172389129754795386415481469822) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 136,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (135 - x)) = _
  rw [show 136 = 0 +
    136 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_136 :
    recurrence4B3A3.coeff 136 =
      -(((4114945971807347613800976143940095440112558211119898606606 * 10 ^ 70 +
        3370809584691635020317977568085032889526243338454704344674532276731027) * 10 ^ 70 +
        2089779268677805816147332187327461450929521964577306984170017695617267) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 137,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (136 - x)) = _
  rw [show 137 = 0 +
    137 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_137 :
    recurrence4B3A3.coeff 137 =
      (((8242776511371464563337097913336032509761175106742412600482 * 10 ^ 70 +
        5185966787356640540179689461277600495146163293303433781664578707682360) * 10 ^ 70 +
        5474846785566126482578720363966329953637997874832857214690541541715609) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 138,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (137 - x)) = _
  rw [show 138 = 0 +
    138 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

theorem recurrence4B3A3_coeff_138 :
    recurrence4B3A3.coeff 138 =
      -(((16177083288318065492647908237405527567632332554366081204684 * 10 ^ 70 +
        4348280077777450947441018014712419204635273981850890670724421062080878) * 10 ^ 70 +
        7386511175888223775595726231052438362877361234535872854044061526783411) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 139,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (138 - x)) = _
  rw [show 139 = 0 +
    139 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
