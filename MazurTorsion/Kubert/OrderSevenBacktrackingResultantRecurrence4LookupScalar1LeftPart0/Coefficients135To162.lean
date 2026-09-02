/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1LeftPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1Left coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4A1_coeff_1
  recurrence4A1_coeff_10
  recurrence4A1_coeff_100
  recurrence4A1_coeff_101
  recurrence4A1_coeff_102
  recurrence4A1_coeff_103
  recurrence4A1_coeff_104
  recurrence4A1_coeff_105
  recurrence4A1_coeff_106
  recurrence4A1_coeff_107
  recurrence4A1_coeff_108
  recurrence4A1_coeff_109
  recurrence4A1_coeff_11
  recurrence4A1_coeff_110
  recurrence4A1_coeff_111
  recurrence4A1_coeff_112
  recurrence4A1_coeff_113
  recurrence4A1_coeff_114
  recurrence4A1_coeff_115
  recurrence4A1_coeff_116
  recurrence4A1_coeff_117
  recurrence4A1_coeff_118
  recurrence4A1_coeff_119
  recurrence4A1_coeff_12
  recurrence4A1_coeff_120
  recurrence4A1_coeff_121
  recurrence4A1_coeff_122
  recurrence4A1_coeff_123
  recurrence4A1_coeff_124
  recurrence4A1_coeff_125
  recurrence4A1_coeff_126
  recurrence4A1_coeff_127
  recurrence4A1_coeff_128
  recurrence4A1_coeff_129
  recurrence4A1_coeff_13
  recurrence4A1_coeff_130
  recurrence4A1_coeff_131
  recurrence4A1_coeff_132
  recurrence4A1_coeff_133
  recurrence4A1_coeff_134
  recurrence4A1_coeff_135
  recurrence4A1_coeff_136
  recurrence4A1_coeff_137
  recurrence4A1_coeff_138
  recurrence4A1_coeff_139
  recurrence4A1_coeff_14
  recurrence4A1_coeff_140
  recurrence4A1_coeff_141
  recurrence4A1_coeff_142
  recurrence4A1_coeff_143
  recurrence4A1_coeff_144
  recurrence4A1_coeff_145
  recurrence4A1_coeff_146
  recurrence4A1_coeff_147
  recurrence4A1_coeff_148
  recurrence4A1_coeff_149
  recurrence4A1_coeff_15
  recurrence4A1_coeff_150
  recurrence4A1_coeff_151
  recurrence4A1_coeff_152
  recurrence4A1_coeff_153
  recurrence4A1_coeff_154
  recurrence4A1_coeff_155
  recurrence4A1_coeff_156

attribute [local simp]
  recurrence4A1_coeff_157
  recurrence4A1_coeff_158
  recurrence4A1_coeff_159
  recurrence4A1_coeff_16
  recurrence4A1_coeff_160
  recurrence4A1_coeff_161
  recurrence4A1_coeff_162
  recurrence4A1_coeff_17
  recurrence4A1_coeff_18
  recurrence4A1_coeff_19
  recurrence4A1_coeff_2
  recurrence4A1_coeff_20
  recurrence4A1_coeff_21
  recurrence4A1_coeff_22
  recurrence4A1_coeff_23
  recurrence4A1_coeff_24
  recurrence4A1_coeff_25
  recurrence4A1_coeff_26
  recurrence4A1_coeff_27
  recurrence4A1_coeff_28
  recurrence4A1_coeff_29
  recurrence4A1_coeff_3
  recurrence4A1_coeff_30
  recurrence4A1_coeff_31
  recurrence4A1_coeff_32
  recurrence4A1_coeff_33
  recurrence4A1_coeff_34
  recurrence4A1_coeff_35
  recurrence4A1_coeff_36
  recurrence4A1_coeff_37
  recurrence4A1_coeff_38
  recurrence4A1_coeff_39
  recurrence4A1_coeff_4
  recurrence4A1_coeff_40
  recurrence4A1_coeff_41
  recurrence4A1_coeff_42
  recurrence4A1_coeff_43
  recurrence4A1_coeff_44
  recurrence4A1_coeff_45
  recurrence4A1_coeff_46
  recurrence4A1_coeff_47
  recurrence4A1_coeff_48
  recurrence4A1_coeff_49
  recurrence4A1_coeff_5
  recurrence4A1_coeff_50
  recurrence4A1_coeff_51
  recurrence4A1_coeff_52
  recurrence4A1_coeff_53
  recurrence4A1_coeff_54
  recurrence4A1_coeff_55
  recurrence4A1_coeff_56
  recurrence4A1_coeff_57
  recurrence4A1_coeff_58
  recurrence4A1_coeff_59
  recurrence4A1_coeff_6
  recurrence4A1_coeff_60
  recurrence4A1_coeff_61
  recurrence4A1_coeff_62
  recurrence4A1_coeff_63
  recurrence4A1_coeff_64
  recurrence4A1_coeff_65
  recurrence4A1_coeff_66
  recurrence4A1_coeff_67
  recurrence4A1_coeff_68

attribute [local simp]
  recurrence4A1_coeff_69
  recurrence4A1_coeff_7
  recurrence4A1_coeff_70
  recurrence4A1_coeff_71
  recurrence4A1_coeff_72
  recurrence4A1_coeff_73
  recurrence4A1_coeff_74
  recurrence4A1_coeff_75
  recurrence4A1_coeff_76
  recurrence4A1_coeff_77
  recurrence4A1_coeff_78
  recurrence4A1_coeff_79
  recurrence4A1_coeff_8
  recurrence4A1_coeff_80
  recurrence4A1_coeff_81
  recurrence4A1_coeff_82
  recurrence4A1_coeff_83
  recurrence4A1_coeff_84
  recurrence4A1_coeff_85
  recurrence4A1_coeff_86
  recurrence4A1_coeff_87
  recurrence4A1_coeff_88
  recurrence4A1_coeff_89
  recurrence4A1_coeff_9
  recurrence4A1_coeff_90
  recurrence4A1_coeff_91
  recurrence4A1_coeff_92
  recurrence4A1_coeff_93
  recurrence4A1_coeff_94
  recurrence4A1_coeff_95
  recurrence4A1_coeff_96
  recurrence4A1_coeff_97
  recurrence4A1_coeff_98
  recurrence4A1_coeff_99
  recurrence4LeadingSquare_coeff_0
  recurrence4LeadingSquare_coeff_1
  recurrence4LeadingSquare_coeff_10
  recurrence4LeadingSquare_coeff_100
  recurrence4LeadingSquare_coeff_101
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

attribute [local simp]
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
  recurrence4LeadingSquare_coeff_160
  recurrence4LeadingSquare_coeff_161
  recurrence4LeadingSquare_coeff_17
  recurrence4LeadingSquare_coeff_18
  recurrence4LeadingSquare_coeff_19
  recurrence4LeadingSquare_coeff_2
  recurrence4LeadingSquare_coeff_20
  recurrence4LeadingSquare_coeff_21
  recurrence4LeadingSquare_coeff_22
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

attribute [local simp]
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

attribute [local simp]
  recurrence4LeadingSquare_coeff_96
  recurrence4LeadingSquare_coeff_97
  recurrence4LeadingSquare_coeff_98
  recurrence4LeadingSquare_coeff_99

private theorem recurrence4Scalar1Left_coeff_135_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (135 + x) *
        remainder4Coefficient1.coeff (135 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 135 + x
  · rw [recurrence4LeadingSquare_coeff_high (135 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (135 - (135 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_135 :
    recurrence4Scalar1Left.coeff 135 =
      -((((230957621458142933088808386290797939463050826354049388654 * 10 ^ 70 +
        6186185123122204331584243070414394776414990363953408333385402838719969) * 10 ^ 70 +
        3036398359322230819626690306898076961893128781840973394961172672571754) * 10 ^ 70 +
        8082343089004018029087659060809547084413237741516711250412300924292991) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 136,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (135 - x)) = _
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
    rw [show 8 = 7 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_135_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_136_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (136 + x) *
        remainder4Coefficient1.coeff (136 - (136 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 136 + x
  · rw [recurrence4LeadingSquare_coeff_high (136 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (136 - (136 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_136 :
    recurrence4Scalar1Left.coeff 136 =
      ((((1305885587246631111664525721926236132945934089649064326486 * 10 ^ 70 +
        2039338308394911311618938132016748399500317837132479020812442063913980) * 10 ^ 70 +
        5244312942401052746326040882134444837903792049467462839265310473315554) * 10 ^ 70 +
        8700926222847752584986928324836628446722601953291435934888414634317032) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 137,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (136 - x)) = _
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
    rw [show 9 = 8 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_136_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_137_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (137 + x) *
        remainder4Coefficient1.coeff (137 - (137 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 137 + x
  · rw [recurrence4LeadingSquare_coeff_high (137 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (137 - (137 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_137 :
    recurrence4Scalar1Left.coeff 137 =
      -((((7246567143532433742291002529958417240811431214738650230824 * 10 ^ 70 +
        7586929486905989430475411464251552148603488558702687236002735479063640) * 10 ^ 70 +
        4598386549834817739960622707675886671814119423209703883689071770312476) * 10 ^ 70 +
        9695732058912720511873459832424764671522321112952943390827333390351550) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 138,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (137 - x)) = _
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
    rw [show 10 = 9 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_137_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_138_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (138 + x) *
        remainder4Coefficient1.coeff (138 - (138 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 138 + x
  · rw [recurrence4LeadingSquare_coeff_high (138 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (138 - (138 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_138 :
    recurrence4Scalar1Left.coeff 138 =
      ((((39471422123477837227756848367768570976631748109463343824437 * 10 ^ 70 +
        7623976770720330407088834248897095885235857573818738750399202199132442) * 10 ^ 70 +
        9175645313439270123359122532777108464088636354694085542526156679039393) * 10 ^ 70 +
        9751525819691938071595650407026855596294201102043114864171132600586175) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 139,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (138 - x)) = _
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
    rw [show 11 = 10 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_138_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_139_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (139 + x) *
        remainder4Coefficient1.coeff (139 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 139 + x
  · rw [recurrence4LeadingSquare_coeff_high (139 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (139 - (139 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_139 :
    recurrence4Scalar1Left.coeff 139 =
      -((((211068477394068145201335917990235780962701742756185757339572 * 10 ^ 70 +
        6210116991021289063557811027915826761784511472062592733911270909492305) * 10 ^ 70 +
        4115475721753361424052085546373360933560734433556150405745484924040761) * 10 ^ 70 +
        5793384683995923449795281582540360672250157650341448429071369041776038) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 140,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (139 - x)) = _
  rw [show 140 = 0 +
    140 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 12 = 11 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_139_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_140_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (140 + x) *
        remainder4Coefficient1.coeff (140 - (140 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 140 + x
  · rw [recurrence4LeadingSquare_coeff_high (140 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (140 - (140 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_140 :
    recurrence4Scalar1Left.coeff 140 =
      ((((1108202395047440006986964287974530885550475448590885941212739 * 10 ^ 70 +
        6647964515239709201609479291328908754435628812301887242549460817323806) * 10 ^ 70 +
        8357685028716384396105576428053511575769313530647340001686943995910250) * 10 ^ 70 +
        3125549513819604985669902169926263775201767193257958461272984095366608) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 141,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (140 - x)) = _
  rw [show 141 = 0 +
    141 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 13 = 12 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_140_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_141_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (141 + x) *
        remainder4Coefficient1.coeff (141 - (141 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 141 + x
  · rw [recurrence4LeadingSquare_coeff_high (141 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (141 - (141 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_141 :
    recurrence4Scalar1Left.coeff 141 =
      -((((5713904628745579487679880378653370690579722667581277769481000 * 10 ^ 70 +
        2107084555043936216457602081016290478707187521134807767715897167021718) * 10 ^ 70 +
        7577923332404685496596971814593054342570673533642860089911499084574205) * 10 ^ 70 +
        1546884602230452653294762802553214219919361014729312094633859754991924) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 142,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (141 - x)) = _
  rw [show 142 = 0 +
    142 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 14 = 13 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_141_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_142_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (142 + x) *
        remainder4Coefficient1.coeff (142 - (142 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 142 + x
  · rw [recurrence4LeadingSquare_coeff_high (142 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (142 - (142 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_142 :
    recurrence4Scalar1Left.coeff 142 =
      ((((28935192917495262722649811512245059555039439558953041554768845 * 10 ^ 70 +
        9424786605040892914284566903250371540724921614294155951948914486607839) * 10 ^ 70 +
        1460079470788775490300366721093587425052132773358695805140971065328013) * 10 ^ 70 +
        1406169508639045197041270430415690759138307787499084653800020492171881) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 143,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (142 - x)) = _
  rw [show 143 = 0 +
    143 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 15 = 14 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_142_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_143_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (143 + x) *
        remainder4Coefficient1.coeff (143 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 143 + x
  · rw [recurrence4LeadingSquare_coeff_high (143 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (143 - (143 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_143 :
    recurrence4Scalar1Left.coeff 143 =
      -((((143932488174961270478544881182549441310327954436638380990806134 * 10 ^ 70 +
        4624350111609449115579532657180148027647887506539819853131005863826140) * 10 ^ 70 +
        1539168744434189141795854880018382607912636946322684784207428983738224) * 10 ^ 70 +
        1217871795681462709661542979013418607458243470754097336298535246202252) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 144,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (143 - x)) = _
  rw [show 144 = 0 +
    144 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 16 = 15 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_143_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_144_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (144 + x) *
        remainder4Coefficient1.coeff (144 - (144 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 144 + x
  · rw [recurrence4LeadingSquare_coeff_high (144 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (144 - (144 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_144 :
    recurrence4Scalar1Left.coeff 144 =
      ((((703377107665657374750520656955736560519087885586638954207180399 * 10 ^ 70 +
        0368719100433791274736913915003165974948543656350580699233105847261142) * 10 ^ 70 +
        1539709072976292939995149949564844853269030967684313971901772260908048) * 10 ^ 70 +
        1523267959009883751771142100270456748047320911392762656456598024619638) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 145,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (144 - x)) = _
  rw [show 145 = 0 +
    145 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 17 = 16 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_144_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_145_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (145 + x) *
        remainder4Coefficient1.coeff (145 - (145 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 145 + x
  · rw [recurrence4LeadingSquare_coeff_high (145 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (145 - (145 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_145 :
    recurrence4Scalar1Left.coeff 145 =
      -((((3377309344523401663786701520981810798711347744734241551753540277 * 10 ^ 70 +
        8957010814979120685767647816291671050064954342291495397477804139769639) * 10 ^ 70 +
        9642129291452390692006061683399237701205967643483707493525775137279099) * 10 ^ 70 +
        9341178807045647488961017793904807973188966272105755812659269328515583) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 146,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (145 - x)) = _
  rw [show 146 = 0 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 18 = 17 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_145_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_146_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (146 + x) *
        remainder4Coefficient1.coeff (146 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 146 + x
  · rw [recurrence4LeadingSquare_coeff_high (146 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (146 - (146 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_146 :
    recurrence4Scalar1Left.coeff 146 =
      ((((15935341394096552146299900493446153239108982967401328701351865084 * 10 ^ 70 +
        8693627957825815273674252891818377366814663493505768066362512292901594) * 10 ^ 70 +
        9892627443520054489229291485337963663520244460011417213182549506413780) * 10 ^ 70 +
        4494280286932599355252484480405385775305496066654320425595822037636760) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 147,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (146 - x)) = _
  rw [show 147 = 0 +
    147 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 19 = 18 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_146_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_147_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (147 + x) *
        remainder4Coefficient1.coeff (147 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 147 + x
  · rw [recurrence4LeadingSquare_coeff_high (147 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (147 - (147 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_147 :
    recurrence4Scalar1Left.coeff 147 =
      -((((73894651373416678683881211397959528346336996650033823645041323556 * 10 ^ 70 +
        5370772859540863891406745742221514835888496374751688888503344009292636) * 10 ^ 70 +
        6403205576056386847023482847206632226019434153753083872797712078396369) * 10 ^ 70 +
        9256163730753095070241418309444079596888236369883484032188701019729766) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 148,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (147 - x)) = _
  rw [show 148 = 0 +
    148 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 20 = 19 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_147_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_148_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (148 + x) *
        remainder4Coefficient1.coeff (148 - (148 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 148 + x
  · rw [recurrence4LeadingSquare_coeff_high (148 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (148 - (148 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_148 :
    recurrence4Scalar1Left.coeff 148 =
      ((((336804161931148420131586833911315848036549652301928724522864163409 * 10 ^ 70 +
        3985863481735741119027499304633034603045944327108810639627045434193267) * 10 ^ 70 +
        6808380569003805656034701073055723761773901215909321469291771715495301) * 10 ^ 70 +
        4345382973190821802322088531780476339494667603864164478085207918403533) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 149,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (148 - x)) = _
  rw [show 149 = 0 +
    149 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 21 = 20 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_148_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_149_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (149 + x) *
        remainder4Coefficient1.coeff (149 - (149 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 149 + x
  · rw [recurrence4LeadingSquare_coeff_high (149 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (149 - (149 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_149 :
    recurrence4Scalar1Left.coeff 149 =
      -((((1509054720260841208263187787473781710677553240613316285979151733008 * 10 ^ 70 +
        4364095839207659815100436651339291346055714811451666712666701791724773) * 10 ^ 70 +
        0690232480605690455529143479063826324972563328986142373798579700174849) * 10 ^ 70 +
        7389841626661889935065914359455396696155174087721670251025678746555943) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 150,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (149 - x)) = _
  rw [show 150 = 0 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_149_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_150_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (150 + x) *
        remainder4Coefficient1.coeff (150 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 150 + x
  · rw [recurrence4LeadingSquare_coeff_high (150 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (150 - (150 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_150 :
    recurrence4Scalar1Left.coeff 150 =
      ((((6647288275614925320626216414137719142167393854878810043228616677496 * 10 ^ 70 +
        1360130066434089777867590764691546671458874116101073002962780745874778) * 10 ^ 70 +
        8948206810980498162635453760884451368822048136424553936914174765009060) * 10 ^ 70 +
        5690223142803018246383251672461531674877719405759733935875881158565783) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 151,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (150 - x)) = _
  rw [show 151 = 0 +
    151 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 23 = 22 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_150_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_151_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (151 + x) *
        remainder4Coefficient1.coeff (151 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 151 + x
  · rw [recurrence4LeadingSquare_coeff_high (151 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (151 - (151 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_151 :
    recurrence4Scalar1Left.coeff 151 =
      -((((28790126248783433606524145756121366587494177432723155402748977105958 * 10 ^ 70 +
        1494724753717649529803927807364370539221293130291807880031782330286375) * 10 ^ 70 +
        4392197991623570186543050591384478763424803778018697637955247037140782) * 10 ^ 70 +
        2134172104182089725678232243613376062200848474450193674497244905107460) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 152,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (151 - x)) = _
  rw [show 152 = 0 +
    152 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 24 = 23 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_151_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_152_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (152 + x) *
        remainder4Coefficient1.coeff (152 - (152 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 152 + x
  · rw [recurrence4LeadingSquare_coeff_high (152 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (152 - (152 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_152 :
    recurrence4Scalar1Left.coeff 152 =
      ((((122616351217856780084763026543665285998430570631579741267111811155479 * 10 ^ 70 +
        7493818085646216693077783306269043229268195971546670238482302513788678) * 10 ^ 70 +
        0034399598784700607843613487449538316808516364878775197576279761938643) * 10 ^ 70 +
        9619206339622846039101404864517374095201315703289396235557731142381545) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 153,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (152 - x)) = _
  rw [show 153 = 0 +
    153 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 25 = 24 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_152_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_153_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (153 + x) *
        remainder4Coefficient1.coeff (153 - (153 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 153 + x
  · rw [recurrence4LeadingSquare_coeff_high (153 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (153 - (153 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_153 :
    recurrence4Scalar1Left.coeff 153 =
      -((((513575061846461407439514731207279549554656355659186499926850466038053 * 10 ^ 70 +
        0637647947531651381963642607165214524287709916470505964204353808178517) * 10 ^ 70 +
        1491044139492316830112537063328169339984069195529430861880192312549660) * 10 ^ 70 +
        4401316339682256266011063623110058484554790539396587046500665221130487) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 154,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (153 - x)) = _
  rw [show 154 = 0 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_153_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_154_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (154 + x) *
        remainder4Coefficient1.coeff (154 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 154 + x
  · rw [recurrence4LeadingSquare_coeff_high (154 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (154 - (154 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_154 :
    recurrence4Scalar1Left.coeff 154 =
      ((((2115699094989533225165478861583546909537321939865621631356731537201462 * 10 ^ 70 +
        6191655394902801391793638496953571634800693465998600129966647168725898) * 10 ^ 70 +
        6468815086407716599975943094194293533009665420986429559478361939871887) * 10 ^ 70 +
        4818819344018549460644760216725868025405391482030393073211866037288257) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 155,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (154 - x)) = _
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
    rw [show 27 = 26 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_154_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_155_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (155 + x) *
        remainder4Coefficient1.coeff (155 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 155 + x
  · rw [recurrence4LeadingSquare_coeff_high (155 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (155 - (155 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_155 :
    recurrence4Scalar1Left.coeff 155 =
      -((((8573157715465033042180239794756596250774418719755672785759979926660745 * 10 ^ 70 +
        6051111755659961187590030982535822869950934246476187414335456685919625) * 10 ^ 70 +
        3563609482355274962038260558053508539709121654472196233287489355294741) * 10 ^ 70 +
        3630104818890341964500423741313522401828606468182916680644315213084489) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 156,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (155 - x)) = _
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
    rw [show 28 = 27 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_155_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_156_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (156 + x) *
        remainder4Coefficient1.coeff (156 - (156 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 156 + x
  · rw [recurrence4LeadingSquare_coeff_high (156 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (156 - (156 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_156 :
    recurrence4Scalar1Left.coeff 156 =
      (((((3 * 10 ^ 70 +
        4174800922734981182965463450735471776805296053441893751308003716819026) * 10 ^ 70 +
        5474295502728210318866366456314982787759068644793513876753793040462671) * 10 ^ 70 +
        1937460715867705960172304585509997810698850599888470333062833476948166) * 10 ^ 70 +
        8751146924034491321392950273920409981921977937305355211054346960174327) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 157,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (156 - x)) = _
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
    rw [show 29 = 28 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_156_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_157_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (157 + x) *
        remainder4Coefficient1.coeff (157 - (157 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 157 + x
  · rw [recurrence4LeadingSquare_coeff_high (157 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (157 - (157 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_157 :
    recurrence4Scalar1Left.coeff 157 =
      -(((((13 * 10 ^ 70 +
        4026173858778127588761980981574403366284862594866075354133606495674612) * 10 ^ 70 +
        3172283854523659335376845722457755566500936925999046079265860582650222) * 10 ^ 70 +
        8167432739138624529723963619679060814507415965964755014356715021187815) * 10 ^ 70 +
        3693126540558433362953535160300824351735073162889594247005260485409478) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 158,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (157 - x)) = _
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
    rw [show 30 = 29 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_157_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_158_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (158 + x) *
        remainder4Coefficient1.coeff (158 - (158 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 158 + x
  · rw [recurrence4LeadingSquare_coeff_high (158 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (158 - (158 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_158 :
    recurrence4Scalar1Left.coeff 158 =
      (((((51 * 10 ^ 70 +
        7166936328631962922708342752439466420729432430051665559925976502627964) * 10 ^ 70 +
        1026522102086042207219422163685795682642144598002203006596680901571580) * 10 ^ 70 +
        3955639605157031808355620522813620373025171224562947572424656352854885) * 10 ^ 70 +
        0889634079686815127019649975942196563689124972887540949333123086590920) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 159,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (158 - x)) = _
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
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_158_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_159_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (159 + x) *
        remainder4Coefficient1.coeff (159 - (159 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 159 + x
  · rw [recurrence4LeadingSquare_coeff_high (159 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (159 - (159 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_159 :
    recurrence4Scalar1Left.coeff 159 =
      -(((((196 * 10 ^ 70 +
        3664807839383566866539888602367568308140981094587611475773773799724209) * 10 ^ 70 +
        5201455631795481236369835759205044187255448445185228493473350033753577) * 10 ^ 70 +
        4924263176646624013656637084150383017588825502364581795488243396531328) * 10 ^ 70 +
        2699308228407021637338368529969161575771804140567082319741558854943731) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 160,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (159 - x)) = _
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
    rw [show 32 = 31 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_159_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_160_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (160 + x) *
        remainder4Coefficient1.coeff (160 - (160 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 160 + x
  · rw [recurrence4LeadingSquare_coeff_high (160 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (160 - (160 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_160 :
    recurrence4Scalar1Left.coeff 160 =
      (((((733 * 10 ^ 70 +
        7301031123220794522986366477019237897598305365485907893024029835872056) * 10 ^ 70 +
        0627348515824885590022455673822888456550941776212385587543911682181532) * 10 ^ 70 +
        9724442063468040282407289710674440584096900918787203333967780506631034) * 10 ^ 70 +
        3254088603400413924567211762875668142709611665979742797257663351117083) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 161,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (160 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_160_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_161_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (161 + x) *
        remainder4Coefficient1.coeff (161 - (161 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 161 + x
  · rw [recurrence4LeadingSquare_coeff_high (161 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (161 - (161 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_161 :
    recurrence4Scalar1Left.coeff 161 =
      -(((((2698 * 10 ^ 70 +
        1963799780767528004897909398985686593249658446515735058012099542678176) * 10 ^ 70 +
        7177136355199734052016703610812792032559515952513718129203553113160546) * 10 ^ 70 +
        8577146315254621348328623077639921995550893592433708962533024370488360) * 10 ^ 70 +
        9344502120157696401102763121573963063662334789747510607889702104606259) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 162,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (161 - x)) = _
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
    rw [show 2 = 1 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_161_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_162_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (162 + x) *
        remainder4Coefficient1.coeff (162 - (162 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 162 + x
  · rw [recurrence4LeadingSquare_coeff_high (162 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (162 - (162 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_162 :
    recurrence4Scalar1Left.coeff 162 =
      (((((9765 * 10 ^ 70 +
        9356167476377851770820528171046157378007860059686520229685329202770280) * 10 ^ 70 +
        5536992070057220132941370990691628345360557054557096736194136207860322) * 10 ^ 70 +
        5258075204680635428809434206875360895680146121963255727510200588341087) * 10 ^ 70 +
        9904303404972139596744935386496663529035057748446106311019740896593142) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 163,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (162 - x)) = _
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
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_162_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
