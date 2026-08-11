/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenPellLocalCertificate

/-!
# A kernel-checked finite local certificate for the `X₁(13)` Pell form

This file checks the 191 possible inputs to the fixed degree-nineteen Pell
numerator separately.  Splitting the computation into one declaration per
residue keeps every kernel reduction small; no native evaluator is used.

Combined with the power-image calculation in the preceding module, the
certificate proves the honest local conclusion `191 ∣ a * b * (a + b)`.
It does not claim that this local condition is the global obstruction.
-/

namespace MazurTorsion.XOneThirteenPellLocalFiniteCertificate

open MazurTorsion.XOneThirteenDescent
open MazurTorsion.XOneThirteenPellLocalCertificate

local instance : NeZero 191 := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 191) := ⟨by norm_num⟩

private def pellHPreimageClaim (x : F191) : Prop :=
  (pellHValueF191 x = 0 ∨
      pellHValueF191 x = 10 ∨
      pellHValueF191 x = -10 ∨
      pellHValueF191 x = 75 ∨
      pellHValueF191 x = -75) →
    x = 0 ∨ x = -1

private theorem pellHPreimageCase0 : pellHPreimageClaim (0 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase1 : pellHPreimageClaim (1 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase2 : pellHPreimageClaim (2 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase3 : pellHPreimageClaim (3 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase4 : pellHPreimageClaim (4 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase5 : pellHPreimageClaim (5 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase6 : pellHPreimageClaim (6 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase7 : pellHPreimageClaim (7 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase8 : pellHPreimageClaim (8 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase9 : pellHPreimageClaim (9 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase10 : pellHPreimageClaim (10 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase11 : pellHPreimageClaim (11 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase12 : pellHPreimageClaim (12 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase13 : pellHPreimageClaim (13 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase14 : pellHPreimageClaim (14 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase15 : pellHPreimageClaim (15 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase16 : pellHPreimageClaim (16 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase17 : pellHPreimageClaim (17 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase18 : pellHPreimageClaim (18 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase19 : pellHPreimageClaim (19 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase20 : pellHPreimageClaim (20 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase21 : pellHPreimageClaim (21 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase22 : pellHPreimageClaim (22 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase23 : pellHPreimageClaim (23 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase24 : pellHPreimageClaim (24 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase25 : pellHPreimageClaim (25 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase26 : pellHPreimageClaim (26 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase27 : pellHPreimageClaim (27 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase28 : pellHPreimageClaim (28 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase29 : pellHPreimageClaim (29 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase30 : pellHPreimageClaim (30 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase31 : pellHPreimageClaim (31 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase32 : pellHPreimageClaim (32 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase33 : pellHPreimageClaim (33 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase34 : pellHPreimageClaim (34 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase35 : pellHPreimageClaim (35 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase36 : pellHPreimageClaim (36 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase37 : pellHPreimageClaim (37 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase38 : pellHPreimageClaim (38 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase39 : pellHPreimageClaim (39 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase40 : pellHPreimageClaim (40 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase41 : pellHPreimageClaim (41 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase42 : pellHPreimageClaim (42 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase43 : pellHPreimageClaim (43 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase44 : pellHPreimageClaim (44 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase45 : pellHPreimageClaim (45 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase46 : pellHPreimageClaim (46 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase47 : pellHPreimageClaim (47 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase48 : pellHPreimageClaim (48 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase49 : pellHPreimageClaim (49 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase50 : pellHPreimageClaim (50 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase51 : pellHPreimageClaim (51 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase52 : pellHPreimageClaim (52 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase53 : pellHPreimageClaim (53 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase54 : pellHPreimageClaim (54 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase55 : pellHPreimageClaim (55 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase56 : pellHPreimageClaim (56 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase57 : pellHPreimageClaim (57 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase58 : pellHPreimageClaim (58 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase59 : pellHPreimageClaim (59 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase60 : pellHPreimageClaim (60 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase61 : pellHPreimageClaim (61 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase62 : pellHPreimageClaim (62 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase63 : pellHPreimageClaim (63 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase64 : pellHPreimageClaim (64 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase65 : pellHPreimageClaim (65 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase66 : pellHPreimageClaim (66 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase67 : pellHPreimageClaim (67 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase68 : pellHPreimageClaim (68 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase69 : pellHPreimageClaim (69 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase70 : pellHPreimageClaim (70 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase71 : pellHPreimageClaim (71 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase72 : pellHPreimageClaim (72 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase73 : pellHPreimageClaim (73 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase74 : pellHPreimageClaim (74 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase75 : pellHPreimageClaim (75 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase76 : pellHPreimageClaim (76 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase77 : pellHPreimageClaim (77 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase78 : pellHPreimageClaim (78 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase79 : pellHPreimageClaim (79 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase80 : pellHPreimageClaim (80 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase81 : pellHPreimageClaim (81 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase82 : pellHPreimageClaim (82 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase83 : pellHPreimageClaim (83 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase84 : pellHPreimageClaim (84 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase85 : pellHPreimageClaim (85 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase86 : pellHPreimageClaim (86 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase87 : pellHPreimageClaim (87 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase88 : pellHPreimageClaim (88 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase89 : pellHPreimageClaim (89 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase90 : pellHPreimageClaim (90 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase91 : pellHPreimageClaim (91 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase92 : pellHPreimageClaim (92 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase93 : pellHPreimageClaim (93 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase94 : pellHPreimageClaim (94 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase95 : pellHPreimageClaim (95 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase96 : pellHPreimageClaim (96 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase97 : pellHPreimageClaim (97 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase98 : pellHPreimageClaim (98 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase99 : pellHPreimageClaim (99 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase100 : pellHPreimageClaim (100 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase101 : pellHPreimageClaim (101 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase102 : pellHPreimageClaim (102 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase103 : pellHPreimageClaim (103 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase104 : pellHPreimageClaim (104 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase105 : pellHPreimageClaim (105 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase106 : pellHPreimageClaim (106 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase107 : pellHPreimageClaim (107 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase108 : pellHPreimageClaim (108 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase109 : pellHPreimageClaim (109 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase110 : pellHPreimageClaim (110 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase111 : pellHPreimageClaim (111 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase112 : pellHPreimageClaim (112 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase113 : pellHPreimageClaim (113 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase114 : pellHPreimageClaim (114 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase115 : pellHPreimageClaim (115 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase116 : pellHPreimageClaim (116 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase117 : pellHPreimageClaim (117 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase118 : pellHPreimageClaim (118 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase119 : pellHPreimageClaim (119 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase120 : pellHPreimageClaim (120 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase121 : pellHPreimageClaim (121 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase122 : pellHPreimageClaim (122 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase123 : pellHPreimageClaim (123 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase124 : pellHPreimageClaim (124 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase125 : pellHPreimageClaim (125 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase126 : pellHPreimageClaim (126 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase127 : pellHPreimageClaim (127 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase128 : pellHPreimageClaim (128 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase129 : pellHPreimageClaim (129 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase130 : pellHPreimageClaim (130 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase131 : pellHPreimageClaim (131 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase132 : pellHPreimageClaim (132 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase133 : pellHPreimageClaim (133 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase134 : pellHPreimageClaim (134 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase135 : pellHPreimageClaim (135 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase136 : pellHPreimageClaim (136 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase137 : pellHPreimageClaim (137 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase138 : pellHPreimageClaim (138 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase139 : pellHPreimageClaim (139 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase140 : pellHPreimageClaim (140 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase141 : pellHPreimageClaim (141 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase142 : pellHPreimageClaim (142 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase143 : pellHPreimageClaim (143 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase144 : pellHPreimageClaim (144 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase145 : pellHPreimageClaim (145 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase146 : pellHPreimageClaim (146 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase147 : pellHPreimageClaim (147 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase148 : pellHPreimageClaim (148 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase149 : pellHPreimageClaim (149 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase150 : pellHPreimageClaim (150 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase151 : pellHPreimageClaim (151 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase152 : pellHPreimageClaim (152 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase153 : pellHPreimageClaim (153 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase154 : pellHPreimageClaim (154 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase155 : pellHPreimageClaim (155 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase156 : pellHPreimageClaim (156 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase157 : pellHPreimageClaim (157 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase158 : pellHPreimageClaim (158 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase159 : pellHPreimageClaim (159 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase160 : pellHPreimageClaim (160 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase161 : pellHPreimageClaim (161 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase162 : pellHPreimageClaim (162 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase163 : pellHPreimageClaim (163 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase164 : pellHPreimageClaim (164 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase165 : pellHPreimageClaim (165 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase166 : pellHPreimageClaim (166 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase167 : pellHPreimageClaim (167 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase168 : pellHPreimageClaim (168 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase169 : pellHPreimageClaim (169 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase170 : pellHPreimageClaim (170 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase171 : pellHPreimageClaim (171 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase172 : pellHPreimageClaim (172 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase173 : pellHPreimageClaim (173 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase174 : pellHPreimageClaim (174 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase175 : pellHPreimageClaim (175 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase176 : pellHPreimageClaim (176 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase177 : pellHPreimageClaim (177 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase178 : pellHPreimageClaim (178 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase179 : pellHPreimageClaim (179 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase180 : pellHPreimageClaim (180 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase181 : pellHPreimageClaim (181 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase182 : pellHPreimageClaim (182 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase183 : pellHPreimageClaim (183 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase184 : pellHPreimageClaim (184 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase185 : pellHPreimageClaim (185 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase186 : pellHPreimageClaim (186 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase187 : pellHPreimageClaim (187 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase188 : pellHPreimageClaim (188 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase189 : pellHPreimageClaim (189 : F191) := by
  unfold pellHPreimageClaim
  decide
private theorem pellHPreimageCase190 : pellHPreimageClaim (190 : F191) := by
  unfold pellHPreimageClaim
  decide

/-- The five nineteenth-power difference values have only the two cuspidal
preimages under the fixed Pell numerator modulo `191`. -/
theorem pellHValue_preimage_of_power_differences (x : F191) :
    (pellHValueF191 x = 0 ∨
      pellHValueF191 x = 10 ∨
      pellHValueF191 x = -10 ∨
      pellHValueF191 x = 75 ∨
      pellHValueF191 x = -75) →
    x = 0 ∨ x = -1 := by
  change pellHPreimageClaim x
  fin_cases x
  · exact pellHPreimageCase0
  · exact pellHPreimageCase1
  · exact pellHPreimageCase2
  · exact pellHPreimageCase3
  · exact pellHPreimageCase4
  · exact pellHPreimageCase5
  · exact pellHPreimageCase6
  · exact pellHPreimageCase7
  · exact pellHPreimageCase8
  · exact pellHPreimageCase9
  · exact pellHPreimageCase10
  · exact pellHPreimageCase11
  · exact pellHPreimageCase12
  · exact pellHPreimageCase13
  · exact pellHPreimageCase14
  · exact pellHPreimageCase15
  · exact pellHPreimageCase16
  · exact pellHPreimageCase17
  · exact pellHPreimageCase18
  · exact pellHPreimageCase19
  · exact pellHPreimageCase20
  · exact pellHPreimageCase21
  · exact pellHPreimageCase22
  · exact pellHPreimageCase23
  · exact pellHPreimageCase24
  · exact pellHPreimageCase25
  · exact pellHPreimageCase26
  · exact pellHPreimageCase27
  · exact pellHPreimageCase28
  · exact pellHPreimageCase29
  · exact pellHPreimageCase30
  · exact pellHPreimageCase31
  · exact pellHPreimageCase32
  · exact pellHPreimageCase33
  · exact pellHPreimageCase34
  · exact pellHPreimageCase35
  · exact pellHPreimageCase36
  · exact pellHPreimageCase37
  · exact pellHPreimageCase38
  · exact pellHPreimageCase39
  · exact pellHPreimageCase40
  · exact pellHPreimageCase41
  · exact pellHPreimageCase42
  · exact pellHPreimageCase43
  · exact pellHPreimageCase44
  · exact pellHPreimageCase45
  · exact pellHPreimageCase46
  · exact pellHPreimageCase47
  · exact pellHPreimageCase48
  · exact pellHPreimageCase49
  · exact pellHPreimageCase50
  · exact pellHPreimageCase51
  · exact pellHPreimageCase52
  · exact pellHPreimageCase53
  · exact pellHPreimageCase54
  · exact pellHPreimageCase55
  · exact pellHPreimageCase56
  · exact pellHPreimageCase57
  · exact pellHPreimageCase58
  · exact pellHPreimageCase59
  · exact pellHPreimageCase60
  · exact pellHPreimageCase61
  · exact pellHPreimageCase62
  · exact pellHPreimageCase63
  · exact pellHPreimageCase64
  · exact pellHPreimageCase65
  · exact pellHPreimageCase66
  · exact pellHPreimageCase67
  · exact pellHPreimageCase68
  · exact pellHPreimageCase69
  · exact pellHPreimageCase70
  · exact pellHPreimageCase71
  · exact pellHPreimageCase72
  · exact pellHPreimageCase73
  · exact pellHPreimageCase74
  · exact pellHPreimageCase75
  · exact pellHPreimageCase76
  · exact pellHPreimageCase77
  · exact pellHPreimageCase78
  · exact pellHPreimageCase79
  · exact pellHPreimageCase80
  · exact pellHPreimageCase81
  · exact pellHPreimageCase82
  · exact pellHPreimageCase83
  · exact pellHPreimageCase84
  · exact pellHPreimageCase85
  · exact pellHPreimageCase86
  · exact pellHPreimageCase87
  · exact pellHPreimageCase88
  · exact pellHPreimageCase89
  · exact pellHPreimageCase90
  · exact pellHPreimageCase91
  · exact pellHPreimageCase92
  · exact pellHPreimageCase93
  · exact pellHPreimageCase94
  · exact pellHPreimageCase95
  · exact pellHPreimageCase96
  · exact pellHPreimageCase97
  · exact pellHPreimageCase98
  · exact pellHPreimageCase99
  · exact pellHPreimageCase100
  · exact pellHPreimageCase101
  · exact pellHPreimageCase102
  · exact pellHPreimageCase103
  · exact pellHPreimageCase104
  · exact pellHPreimageCase105
  · exact pellHPreimageCase106
  · exact pellHPreimageCase107
  · exact pellHPreimageCase108
  · exact pellHPreimageCase109
  · exact pellHPreimageCase110
  · exact pellHPreimageCase111
  · exact pellHPreimageCase112
  · exact pellHPreimageCase113
  · exact pellHPreimageCase114
  · exact pellHPreimageCase115
  · exact pellHPreimageCase116
  · exact pellHPreimageCase117
  · exact pellHPreimageCase118
  · exact pellHPreimageCase119
  · exact pellHPreimageCase120
  · exact pellHPreimageCase121
  · exact pellHPreimageCase122
  · exact pellHPreimageCase123
  · exact pellHPreimageCase124
  · exact pellHPreimageCase125
  · exact pellHPreimageCase126
  · exact pellHPreimageCase127
  · exact pellHPreimageCase128
  · exact pellHPreimageCase129
  · exact pellHPreimageCase130
  · exact pellHPreimageCase131
  · exact pellHPreimageCase132
  · exact pellHPreimageCase133
  · exact pellHPreimageCase134
  · exact pellHPreimageCase135
  · exact pellHPreimageCase136
  · exact pellHPreimageCase137
  · exact pellHPreimageCase138
  · exact pellHPreimageCase139
  · exact pellHPreimageCase140
  · exact pellHPreimageCase141
  · exact pellHPreimageCase142
  · exact pellHPreimageCase143
  · exact pellHPreimageCase144
  · exact pellHPreimageCase145
  · exact pellHPreimageCase146
  · exact pellHPreimageCase147
  · exact pellHPreimageCase148
  · exact pellHPreimageCase149
  · exact pellHPreimageCase150
  · exact pellHPreimageCase151
  · exact pellHPreimageCase152
  · exact pellHPreimageCase153
  · exact pellHPreimageCase154
  · exact pellHPreimageCase155
  · exact pellHPreimageCase156
  · exact pellHPreimageCase157
  · exact pellHPreimageCase158
  · exact pellHPreimageCase159
  · exact pellHPreimageCase160
  · exact pellHPreimageCase161
  · exact pellHPreimageCase162
  · exact pellHPreimageCase163
  · exact pellHPreimageCase164
  · exact pellHPreimageCase165
  · exact pellHPreimageCase166
  · exact pellHPreimageCase167
  · exact pellHPreimageCase168
  · exact pellHPreimageCase169
  · exact pellHPreimageCase170
  · exact pellHPreimageCase171
  · exact pellHPreimageCase172
  · exact pellHPreimageCase173
  · exact pellHPreimageCase174
  · exact pellHPreimageCase175
  · exact pellHPreimageCase176
  · exact pellHPreimageCase177
  · exact pellHPreimageCase178
  · exact pellHPreimageCase179
  · exact pellHPreimageCase180
  · exact pellHPreimageCase181
  · exact pellHPreimageCase182
  · exact pellHPreimageCase183
  · exact pellHPreimageCase184
  · exact pellHPreimageCase185
  · exact pellHPreimageCase186
  · exact pellHPreimageCase187
  · exact pellHPreimageCase188
  · exact pellHPreimageCase189
  · exact pellHPreimageCase190

/-- The normalized nineteenth-power equation has only cuspidal abscissas
modulo `191`. -/
theorem normalized_pell_power_mod_191_cusp
    (x t : F191) (ht : t ≠ 0)
    (hpell : pellHValueF191 x = t ^ 19 - (t ^ 19)⁻¹) :
    x = 0 ∨ x = -1 := by
  apply pellHValue_preimage_of_power_differences x
  rw [hpell]
  exact nineteenth_power_difference_values t ht

/-- The homogeneous power split has cuspidal normalized reduction modulo
`191` whenever `191` does not divide `b`. -/
theorem pell_power_split_mod_191_cusp
    (a b c r s : ℤ)
    (hplus : positivePellFactor a b c = 2 * r ^ 38)
    (hminus : negativePellFactorMagnitude a b c = 2 * s ^ 38)
    (hbSplit : b = r * s)
    (hb : (b : F191) ≠ 0) :
    (a : F191) / (b : F191) = 0 ∨
      (a : F191) / (b : F191) = -1 :=
  pellHValue_preimage_of_power_differences _
    (pell_power_split_mod_191_rhs_values a b c r s
      hplus hminus hbSplit hb)

/-- Every integral solution of the two Pell-factor power equations lies in
one of the three cuspidal residue classes modulo `191`. -/
theorem pell_power_split_mod_191_cusp_divisor
    (a b c r s : ℤ)
    (hplus : positivePellFactor a b c = 2 * r ^ 38)
    (hminus : negativePellFactorMagnitude a b c = 2 * s ^ 38)
    (hbSplit : b = r * s) :
    (191 : ℤ) ∣ a ∨ (191 : ℤ) ∣ b ∨ (191 : ℤ) ∣ a + b := by
  by_cases hb : (b : F191) = 0
  · exact Or.inr (Or.inl
      ((ZMod.intCast_zmod_eq_zero_iff_dvd b 191).mp hb))
  · rcases pell_power_split_mod_191_cusp a b c r s
        hplus hminus hbSplit hb with ha | hab
    · have haZero : (a : F191) = 0 := by
        have haMul := (div_eq_iff hb).mp ha
        simpa using haMul
      exact Or.inl ((ZMod.intCast_zmod_eq_zero_iff_dvd a 191).mp haZero)
    · have haEq : (a : F191) = -(b : F191) := by
        have haMul := (div_eq_iff hb).mp hab
        simpa using haMul
      have habZero : ((a + b : ℤ) : F191) = 0 := by
        push_cast
        rw [haEq]
        simp
      exact Or.inr (Or.inr
        ((ZMod.intCast_zmod_eq_zero_iff_dvd (a + b) 191).mp habZero))

/-- Product form of the three-way local cusp condition.  This is the finite
sieve obligation exposed to a later global or `191`-adic descent. -/
theorem pell_power_split_mod_191_dvd_cusp_product
    (a b c r s : ℤ)
    (hplus : positivePellFactor a b c = 2 * r ^ 38)
    (hminus : negativePellFactorMagnitude a b c = 2 * s ^ 38)
    (hbSplit : b = r * s) :
    (191 : ℤ) ∣ a * b * (a + b) := by
  rcases pell_power_split_mod_191_cusp_divisor a b c r s
      hplus hminus hbSplit with ha | hb | hab
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left ha b) (a + b)
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hb a) (a + b)
  · exact dvd_mul_of_dvd_right hab (a * b)

end MazurTorsion.XOneThirteenPellLocalFiniteCertificate
