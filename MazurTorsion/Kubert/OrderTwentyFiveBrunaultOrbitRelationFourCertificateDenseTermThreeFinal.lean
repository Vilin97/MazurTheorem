/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateDenseTermThreeC15
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateTermThreeData
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Final dense multiplication and coefficient checks for RelationFour term three -/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Dense

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveRelationFourCertificate.Internal

private def termThreeStage16C0 : One :=
  []

private def termThreeStage16C1 : One :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -4, 12, -26, 48, -76, 107, -136, 156, -164,
    156, -136, 107, -76, 48, -26, 12, -4, 1]

private def termThreeStage16C2 : One :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 7, -29, 24, 75, -460, 1268, -2655, 4591, -6904, 9307,
    -11340, 12686, -13001, 12301, -10720, 8605, -6348, 4248, -2565, 1353, -616, 229, -68, 15, -2]

private def termThreeStage16C3 : One :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 70, -504, 2169, -4882, 7448, -4837, -8274, 37539, -84500,
    145547, -213836, 277704, -327744, 354176, -353832, 328095, -283256, 228572, -171802, 120119,
    -77112, 44953, -23344, 10625, -4170, 1382, -373, 79, -12, 1]

private def termThreeStage16C4 : One :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 26, -130, -1390, 13544, -65036, 180988, -370725, 569126,
    -668305, 538657, -102828, -612081, 1510039, -2416459, 3184368, -3676923, 3832110, -3659693,
    3231711, -2671602, 2083575, -1549495, 1099097, -738941, 463299, -265785, 137188, -62825,
    25120, -8631, 2498, -590, 108, -14, 1]

private def termThreeStage16C5 : One :=
  [0, 0, 0, 0, 0, 0, 0, 0, -2, 133, -1611, 9837, -8151, -146961, 989916, -3283361, 7746205,
    -14102777, 20954289, -26074802, 27430000, -24377797, 17587166, -8995525, 505901, 6276426,
    -10439199, 11791674, -10675741, 8061974, -5015347, 2492969, -929109, 260743, -129668, 176252,
    -205078, 176334, -118077, 63894, -28460, 10459, -3132, 744, -133, 16, -1]

private def termThreeStage16C6 : One :=
  [0, 0, 0, 0, 0, 0, -1, 19, -99, -2630, 39099, -266786, 790260, -427255, -7028614, 33280288,
    -92762851, 191120136, -317290156, 443299680, -534420802, 567122865, -536512471, 458083071,
    -355119760, 249205649, -155033549, 79987451, -27789719, -1940826, 12473159, -10274787,
    2806730, 3981225, -7303652, 7303096, -5517909, 3409535, -1772919, 783811, -294259, 92717,
    -23969, 4887, -731, 70, -3]

private def termThreeStage16C7 : One :=
  [0, 0, 0, 0, 0, -1, 64, -1054, 8049, 3681, -464747, 3914136, -15531651, 34150056, -14983981,
    -155959778, 652836794, -1610931137, 3008426497, -4611335301, 6030810623, -6902356937,
    7034292568, -6483966756, 5484381326, -4311795436, 3180001420, -2196976497, 1398048962,
    -782122360, 341689174, -63913245, -76541665, 118727537, -106087503, 74006136, -43259131,
    21693237, -9393701, 3498080, -1103532, 286486, -57947, 8062, -475, -68, 16, -1]

private def termThreeStage16C8 : One :=
  [0, 0, 0, 0, 0, 38, -1690, 26018, -214088, 714470, 1836006, -33446842, 169097910, -503240796,
    884544549, -591320883, -1795975933, 7831494450, -18149468474, 31623405543, -45341781001,
    55762164130, -60209540237, 58027676526, -50626629070, 40562213412, -30358284703, 21640470441,
    -14983731127, 10205968781, -6832763271, 4431601202, -2727017864, 1561626800, -820108291,
    390080934, -165756587, 61794426, -19608623, 4961552, -817599, -19734, 73218, -29793, 7215,
    -1111, 100, -4]

private def termThreeStage16C9 : One :=
  [0, 0, 0, 0, -3, -619, 25509, -384736, 3280481, -15295409, 27886644, 131294214, -1113610797,
    4206663137, -10034478355, 16044011389, -14330018872, -6737579601, 56296988963, -133814845376,
    225585100292, -308872776316, 361152777939, -369733939001, 336282308595, -274228112299,
    201825596021, -134789001463, 82221025106, -46302396427, 24523394992, -12563193623, 6421782720,
    -3335104431, 1750272939, -906541846, 450188112, -209220291, 89461332, -34716177, 12037551,
    -3651956, 939974, -196308, 31239, -3470, 234, -7]

private def termThreeStage16C10 : One :=
  [0, 0, 0, -2, 167, 4513, -240977, 3773964, -33437422, 178589134, -564522675, 551381928,
    3583344818, -21528562378, 65282565333, -135863903797, 205746307912, -215282239430,
    96356224782, 187140664875, -606134262887, 1067427661546, -1449566592548, 1654043230910,
    -1643692255416, 1448830869282, -1144449868507, 814491208404, -523161891024, 302853193919,
    -157282238967, 72638914867, -29342329754, 9991702832, -2581820593, 280029498, 198005237,
    -179059676, 93779909, -38037044, 12539775, -3297079, 635920, -67605, -4400, 3183, -577, 52,
    -2]

private def termThreeStage16C11 : One :=
  [0, 0, 0, 62, -3683, 6064, 1395172, -25390703, 240016384, -1401080805, 5367658623, -12348414290,
    9137463442, 52269445915, -256396227333, 676510704401, -1281438586896, 1867773439581,
    -2104714366437, 1692148921674, -545716526512, -1121800494862, 2877192199751, -4253907845742,
    4942955621999, -4886736660191, 4250176579232, -3309083173045, 2329142685693, -1490234183014,
    869075057474, -462412908893, 224504709400, -99414748998, 40092397273, -14679132880,
    4853715680, -1435741600, 372066088, -79946188, 11750608, 219226, -912221, 367713, -90668,
    15038, -1634, 105, -3]

private def termThreeStage16C12 : One :=
  [0, 0, -3, -819, 45669, -462207, -3574508, 114400142, -1233263790, 7865264884, -33802190680,
    98800793105, -186966110219, 142736331310, 407507303488, -1954809865608, 4757946953981,
    -8435864448756, 11883490882376, -13686839734143, 12845087979521, -9324661947647,
    4094384858539, 1340962560257, -5607251785701, 7952658173592, -8369994309383, 7386576149174,
    -5713974010798, 3957530522440, -2482119682163, 1418412398348, -740981014762, 354557768833,
    -155584442298, 62640254349, -23137784346, 7841986898, -2441768261, 700402602, -185530843,
    45193873, -9918146, 1881005, -290821, 34174, -2793, 138, -3]

private def termThreeStage16C13 : One :=
  [0, -1, 124, 5081, -356321, 4979668, -14904774, -291622776, 4434203611, -32126918297,
    152688123068, -509582281278, 1226495492683, -2043819710655, 1856612607150, 1298965223860,
    -9321260385292, 22460597438171, -38287619947013, 52245957168715, -59705239568679,
    58220411707058, -48569156072962, 34110084719566, -19057705437881, 6763562344125,
    1197963997478, -4968288916248, 5714268519108, -4833601396135, 3427895375637, -2131614671662,
    1185487091207, -595332268500, 271279245449, -112413039544, 42353476794, -14469978614,
    4459388484, -1230936093, 302453837, -66194905, 13086349, -2390269, 404504, -60572, 7362, -654,
    37, -1]

private def termThreeStage16C14 : One :=
  [0, 24, -2079, -2269, 1789535, -30979868, 204875915, -87208449, -9936258990, 93721302484,
    -505478014841, 1879132674331, -5160865721191, 10680444794341, -16439175169020, 17040794444920,
    -5207657475651, -23813242212663, 67744034742455, -116391710391872, 155737063380468,
    -174525445929081, 169102013497502, -143951004606504, 108448443610406, -72351407963321,
    42463561189914, -21529651944177, 9011720670538, -2694209305272, 126762240652, 576481681439,
    -554237575536, 357245797266, -187541948242, 84837792486, -33879115929, 12090949455,
    -3876551456, 1113662263, -282677203, 61585943, -10998086, 1501281, -137622, 5322, 450, -71, 3]

private def termThreeStage16C15 : One :=
  [-1, -230, 19436, -215771, -5327535, 127625467, -1119954121, 4491489756, 5216093112,
    -177494922731, 1207273081883, -5089000692863, 15553517528248, -36404265998307, 66893276185416,
    -96808056778662, 106770137465128, -77099422726302, 948412793188, 107934799443958,
    -219576164964857, 301944536299065, -335412212494207, 319051142209363, -267037975709055,
    199583100688190, -134338447041295, 81838511604140, -45255253594450, 22756325255870,
    -10414385149947, 4335292547324, -1636370169631, 556254832549, -168526797256, 44926806226,
    -10405159223, 2071239792, -343916805, 35620383, 7900223, -7576465, 3221868, -924458, 188025,
    -26872, 2580, -150, 4]

private def termThreeStage16C16 : One :=
  [21, 1067, -116058, 1934937, 4028135, -349622184, 3903775390, -22340095831, 57903791370,
    117404440256, -1903625501300, 9963195821127, -34462002204401, 89405143269312,
    -183182963641782, 304451646573266, -415125567352406, 462256378738351, -406305760010895,
    247242247495572, -28715680316635, -183413045333133, 332872802402009, -394811160658256,
    377851767178046, -310907097514749, 226225886296506, -147734059789859, 87326332523730,
    -46975783984680, 23088136944579, -10402877402884, 4308642016330, -1642467525686, 575714648769,
    -184968219431, 54252102216, -14505330931, 3562445810, -823390722, 185566623, -41277365,
    8675154, -1590099, 234841, -26040, 2002, -94, 2]

private def termThreeStage16C17 : One :=
  [-210, -1142, 470514, -9731355, 45376770, 541702139, -9255182825, 66574748182, -270280430852,
    508409663487, 1160821453674, -12834418937676, 54972503026980, -161309541064057,
    364327868944631, -665619628194708, 1010383586713783, -1293581761670596, 1405750777825243,
    -1292406426920114, 985670243589603, -586145274185218, 210174999544083, 61032030890226,
    -202883474046783, 237143489017031, -206249918679518, 150352302871508, -95841569642670,
    54465950087547, -27870795046202, 12916934181205, -5444794154321, 2094836379247, -737553246028,
    237739066745, -69894642868, 18540587660, -4341771047, 863545992, -136021830, 14367535,
    -295340, -234465, 51438, -5747, 359, -10]

private def termThreeStage16C18 : One :=
  [1328, -16947, -1301718, 33452392, -266222399, 138105005, 13918551297, -134864329344,
    691739828833, -2176980175571, 3257047161776, 6017959918392, -56360246997500, 206995845205322,
    -529952417741803, 1062820711158407, -1753365342936520, 2443783380631608, -2924990725089979,
    3037079370144857, -2750625694994387, 2174921388765167, -1493649644368919, 876710583252367,
    -421467597351938, 144463353421994, -9296076233031, -37264781538588, 40575399577320,
    -29286404700184, 17163387448197, -8644874069138, 3826543891515, -1504039794335, 528278224730,
    -166838595905, 47804843574, -12604581919, 3112889208, -728154724, 159632707, -31612232,
    5368181, -739428, 77887, -5822, 273, -6]

private def termThreeStage16C19 : One :=
  [-5949, 129450, 2223003, -83007975, 850129695, -3471393802, -6916405627, 179763620289,
    -1185984907248, 4728901163817, -12128258018298, 16371783648908, 15747851425654,
    -161779251676312, 534782826384933, -1226227955467374, 2219616825987610, -3338326625277187,
    4287090621221622, -4780687847302677, 4681592418736324, -4057467653188964, 3129113745064385,
    -2154945348903345, 1327774310514246, -732000097824917, 360148683947370, -157002091440885,
    59627354994054, -18935175172884, 4442797616277, -325198042526, -393766929959, 296013177073,
    -135966657639, 47778218820, -13263920667, 2777241181, -348195905, -20836511, 25754224,
    -8020053, 1603080, -226409, 22540, -1500, 59, -1]

private def termThreeStage16C20 : One :=
  [20043, -536064, -831050, 148524288, -1876553645, 11106834731, -26665707262, -110125767203,
    1342071690206, -6764537269909, 21927645428493, -48403847722741, 63813028342477, 5994619726683,
    -292671022678518, 934982718917435, -1977697093884701, 3284175017184791, -4543773383690243,
    5395096287130209, -5595500304980614, 5128602028434423, -4188460723489158, 3066612410014853,
    -2022470250278106, 1206260965777794, -652936852108560, 321843320066248, -144949328047887,
    59830931877112, -22681737705106, 7895458814492, -2513271656422, 724317533748, -185366263683,
    40518451823, -6869647657, 590800796, 136846659, -83688480, 24395310, -4981062, 752621, -83282,
    6420, -309, 7]

private def termThreeStage16C21 : One :=
  [-52633, 1562231, -8170655, -177052915, 3008241790, -21961295315, 89576080360, -133767405858,
    -738054214811, 6296604854416, -25638276029944, 70647323252685, -139369932226936,
    184735506042458, -93432982216625, -285706599357087, 1052602187904031, -2154615298454169,
    3355741398410432, -4320189404714040, 4767716099410140, -4601661390438610, 3933292316715869,
    -3002652113251382, 2059503022208022, -1274819642478130, 714581334100571, -363758142699819,
    168612814465340, -71369247472829, 27674192850399, -9866500494919, 3246429242064,
    -989183932706, 279872958250, -73678211649, 18063738174, -4115621270, 863852014, -164017263,
    27393548, -3883890, 448159, -39955, 2559, -104, 2]

private def termThreeStage16C22 : One :=
  [110175, -3464589, 30507622, 84524814, -3433145987, 30659863639, -157046460507, 478818882093,
    -555656272171, -2712121226312, 18859914101832, -65466647598305, 158637040390958,
    -286563937332690, 380780783986977, -319543765280449, -14713300973730, 648589069919699,
    -1465792664946538, 2240173532233972, -2740790072784971, 2840795876192885, -2562711664680196,
    2043190016567932, -1453503746708082, 928388856502015, -534601214045990, 278255020079641,
    -131100795548113, 55946948568165, -21623974660025, 7565775626490, -2393781356716,
    683578019927, -175509217638, 40220255052, -8122106279, 1415799858, -206256348, 23800252,
    -1947681, 74855, 5471, -1078, 73, -2]

private def termThreeStage16C23 : One :=
  [-186459, 6056312, -65867954, 172909380, 2413942464, -30492257299, 186805842386, -726663223750,
    1825287763087, -2047611397337, -5256146296565, 35755526846726, -111515071951621,
    244434900388669, -410620195694918, 538631889251681, -534190218651391, 335921932116375,
    35690412190449, -476281046330746, 847983712856145, -1047664241496730, 1048662007410557,
    -896274448075502, 670508127415927, -445133808566031, 264410882848230, -141239699446578,
    68042318424072, -29600421723488, 11627416445909, -4119321527957, 1313626855347, -376197172315,
    96542651099, -22166373841, 4548772065, -833142290, 135669254, -19452462, 2409461, -249811,
    20669, -1269, 51, -1]

private def termThreeStage16C24 : One :=
  [257257, -8495992, 102974327, -521558840, -109727778, 19695795596, -155408196610, 716284177724,
    -2281282326791, 4990950110915, -6169305036436, -3288186441500, 40109771266446,
    -121447115559113, 248618591009143, -393189053140748, 501454690200732, -520920940975714,
    432248869471097, -262692719134890, 70961496636159, 84440721062756, -171262098015799,
    190029738093542, -163033394596715, 117493516677728, -73553760206286, 40680590989139,
    -20066922259335, 8877308622931, -3532445693099, 1265492588525, -407715150700, 117746087816,
    -30309847557, 6898368961, -1373375485, 235960034, -34397095, 4162862, -406253, 30665, -1677,
    59, -1]

private def termThreeStage16C25 : One :=
  [-290433, 9648043, -124058719, 788949130, -2291029788, -4229722917, 83135154973, -478170850977,
    1790348047611, -4853450385249, 9650180072645, -13083949907181, 7037143518028, 19947507651865,
    -75338886858932, 153558533868069, -233546193103810, 287539947525781, -296107188617453,
    258582560854828, -191790520026131, 119329996887234, -59837019872049, 21174614338451,
    -1666565853394, -5020720038131, 5342395451018, -3635238356176, 1957206548650, -883947807995,
    342334846833, -114619937062, 33223670657, -8314076342, 1785681450, -326253306, 50077320,
    -6345497, 647288, -51170, 2946, -110, 2]

private def termThreeStage16C26 : One :=
  [268203, -8890333, 117862818, -833999294, 3500922778, -7141611759, -15487359368, 193958292153,
    -908964407883, 2881028068604, -6854810764317, 12629670887688, -17793963763258, 17498267393847,
    -6668459202897, -16046347780867, 45760166499180, -72974083342292, 88600394490895,
    -88718522989144, 75816470761440, -56313475056609, 36756031868954, -21232799584980,
    10909824160801, -5005563501575, 2057731636773, -760221038261, 252968183284, -75844651145,
    20431102030, -4909788445, 1040016849, -190978435, 29763572, -3834511, 394865, -31037, 1736,
    -61, 1]

private def termThreeStage16C27 : One :=
  [-201695, 6628314, -88893165, 662007062, -3192235556, 10300377870, -17903904717, -16150289954,
    246502306045, -1024440383207, 2856577376762, -6101275201955, 10441140681099, -14511808145876,
    16270504509042, -14190681398701, 8438789188040, -978147234694, -5552844070059, 9295185928344,
    -9914826734543, 8324869131356, -5855898143302, 3544119465187, -1869356408434, 864222560885,
    -350644138580, 124627750429, -38637697496, 10381813601, -2397098977, 470370776, -77316616,
    10442597, -1128188, 93710, -5616, 216, -4]

private def termThreeStage16C28 : One :=
  [122409, -3965964, 53042895, -402249038, 2052994890, -7632225169, 20395840375, -36124762753,
    19104710961, 133799767826, -601024602575, 1568180904046, -3079410299864, 4885259188330,
    -6443841776045, 7168654417970, -6779735434406, 5471524421497, -3766137727087, 2197118723678,
    -1069584479947, 419555176633, -120860336459, 16459145452, 6782458817, -6352717651, 2950763918,
    -999789722, 268027498, -58411346, 10426755, -1518400, 177609, -16166, 1079, -47, 1]

private def termThreeStage16C29 : One :=
  [-59067, 1877058, -24740053, 186556475, -963931273, 3756081212, -11273209876, 26516372286,
    -47828160227, 59282707743, -25081025582, -100017286834, 343036509144, -680345518347,
    1025553564979, -1261550411272, 1305312798787, -1155548597555, 885066307879, -590894870789,
    345368985133, -177001200262, 79467881328, -31159700681, 10617118070, -3122036468, 785205591,
    -166957721, 29562671, -4272081, 489988, -42826, 2674, -106, 2]

private def termThreeStage16C30 : One :=
  [22141, -686699, 8822033, -64808510, 328083136, -1273694219, 3909062668, -9780679430,
    20299181190, -34909612973, 49412029182, -56889228209, 51244385206, -31052502826, 1619798642,
    26615404997, -43677503592, 45904311218, -37053718677, 24269607235, -13211116914, 6048191035,
    -2341438651, 767175426, -212083875, 49112669, -9414447, 1467520, -181223, 17045, -1146, 49,
    -1]

private def termThreeStage16C31 : One :=
  [-6216, 187210, -2318480, 16251750, -78077625, 289717699, -858860157, 2096854261, -4329860387,
    7636834522, -11534352951, 15030302150, -17123361414, 17261414784, -15459848121, 12239691332,
    -8476313362, 5076358373, -2603116444, 1133628249, -416191714, 127825345, -32537902, 6780209,
    -1136839, 149600, -14877, 1051, -47, 1]

private def termThreeStage16C32 : One :=
  [1230, -35783, 422057, -2754532, 12062249, -40674495, 109697429, -241591882, 447368394,
    -709553837, 962074410, -1101170685, 1051780762, -832973764, 545551191, -295122784, 131632683,
    -48232749, 14424949, -3484578, 669199, -99757, 11124, -873, 43, -1]

private def termThreeStage16C33 : One :=
  [-153, 4275, -47347, 278260, -1039399, 2902122, -6398703, 11011638, -14556601, 14745557,
    -11503412, 6948280, -3255778, 1179559, -327114, 68118, -10305, 1069, -68, 2]

private def termThreeStage16C34 : One :=
  [9, -240, 2452, -12311, 33714, -55909, 60185, -43825, 22028, -7660, 1811, -278, 25, -1]

def TermThreeStage16 : Two :=
  [termThreeStage16C0, termThreeStage16C1, termThreeStage16C2, termThreeStage16C3,
    termThreeStage16C4, termThreeStage16C5, termThreeStage16C6, termThreeStage16C7,
    termThreeStage16C8, termThreeStage16C9, termThreeStage16C10, termThreeStage16C11,
    termThreeStage16C12, termThreeStage16C13, termThreeStage16C14, termThreeStage16C15,
    termThreeStage16C16, termThreeStage16C17, termThreeStage16C18, termThreeStage16C19,
    termThreeStage16C20, termThreeStage16C21, termThreeStage16C22, termThreeStage16C23,
    termThreeStage16C24, termThreeStage16C25, termThreeStage16C26, termThreeStage16C27,
    termThreeStage16C28, termThreeStage16C29, termThreeStage16C30, termThreeStage16C31,
    termThreeStage16C32, termThreeStage16C33, termThreeStage16C34]

theorem termThree_stage16_spec :
    Two.mul TermThreeStage15 RData = TermThreeStage16 := by
  decide

private theorem termThree_stage16_coefficient_0 (s : ℚ) :
    One.eval termThreeStage16C0 s = termThreeCoefficient 0 s := by
  norm_num [One.eval, evalWith, termThreeStage16C0, termThreeCoefficient,
    termThreeCoefficientLow]

private theorem termThree_stage16_coefficient_1 (s : ℚ) :
    One.eval termThreeStage16C1 s = termThreeCoefficient 1 s := by
  norm_num [One.eval, evalWith, termThreeStage16C1, termThreeCoefficient,
    termThreeCoefficientLow] ; ring

private theorem termThree_stage16_coefficient_2 (s : ℚ) :
    One.eval termThreeStage16C2 s = termThreeCoefficient 2 s := by
  norm_num [One.eval, evalWith, termThreeStage16C2, termThreeCoefficient,
    termThreeCoefficientLow] ; ring

private theorem termThree_stage16_coefficient_3 (s : ℚ) :
    One.eval termThreeStage16C3 s = termThreeCoefficient 3 s := by
  norm_num [One.eval, evalWith, termThreeStage16C3, termThreeCoefficient,
    termThreeCoefficientLow] ; ring

private theorem termThree_stage16_coefficient_4 (s : ℚ) :
    One.eval termThreeStage16C4 s = termThreeCoefficient 4 s := by
  norm_num [One.eval, evalWith, termThreeStage16C4, termThreeCoefficient,
    termThreeCoefficientLow] ; ring

private theorem termThree_stage16_coefficient_5 (s : ℚ) :
    One.eval termThreeStage16C5 s = termThreeCoefficient 5 s := by
  norm_num [One.eval, evalWith, termThreeStage16C5, termThreeCoefficient,
    termThreeCoefficientLow] ; ring

private theorem termThree_stage16_coefficient_6 (s : ℚ) :
    One.eval termThreeStage16C6 s = termThreeCoefficient 6 s := by
  norm_num [One.eval, evalWith, termThreeStage16C6, termThreeCoefficient,
    termThreeCoefficientLow] ; ring

private theorem termThree_stage16_coefficient_7 (s : ℚ) :
    One.eval termThreeStage16C7 s = termThreeCoefficient 7 s := by
  norm_num [One.eval, evalWith, termThreeStage16C7, termThreeCoefficient,
    termThreeCoefficientLow] ; ring

private theorem termThree_stage16_coefficient_8 (s : ℚ) :
    One.eval termThreeStage16C8 s = termThreeCoefficient 8 s := by
  norm_num [One.eval, evalWith, termThreeStage16C8, termThreeCoefficient,
    termThreeCoefficientLow] ; ring

private theorem termThree_stage16_coefficient_9 (s : ℚ) :
    One.eval termThreeStage16C9 s = termThreeCoefficient 9 s := by
  norm_num [One.eval, evalWith, termThreeStage16C9, termThreeCoefficient,
    termThreeCoefficientLow] ; ring

private theorem termThree_stage16_coefficient_10 (s : ℚ) :
    One.eval termThreeStage16C10 s = termThreeCoefficient 10 s := by
  norm_num [One.eval, evalWith, termThreeStage16C10, termThreeCoefficient,
    termThreeCoefficientLow] ; ring

private theorem termThree_stage16_coefficient_11 (s : ℚ) :
    One.eval termThreeStage16C11 s = termThreeCoefficient 11 s := by
  norm_num [One.eval, evalWith, termThreeStage16C11, termThreeCoefficient,
    termThreeCoefficientLow] ; ring

private theorem termThree_stage16_coefficient_12 (s : ℚ) :
    One.eval termThreeStage16C12 s = termThreeCoefficient 12 s := by
  norm_num [One.eval, evalWith, termThreeStage16C12, termThreeCoefficient,
    termThreeCoefficientMid] ; ring

private theorem termThree_stage16_coefficient_13 (s : ℚ) :
    One.eval termThreeStage16C13 s = termThreeCoefficient 13 s := by
  norm_num [One.eval, evalWith, termThreeStage16C13, termThreeCoefficient,
    termThreeCoefficientMid] ; ring

private theorem termThree_stage16_coefficient_14 (s : ℚ) :
    One.eval termThreeStage16C14 s = termThreeCoefficient 14 s := by
  norm_num [One.eval, evalWith, termThreeStage16C14, termThreeCoefficient,
    termThreeCoefficientMid] ; ring

private theorem termThree_stage16_coefficient_15 (s : ℚ) :
    One.eval termThreeStage16C15 s = termThreeCoefficient 15 s := by
  norm_num [One.eval, evalWith, termThreeStage16C15, termThreeCoefficient,
    termThreeCoefficientMid] ; ring

private theorem termThree_stage16_coefficient_16 (s : ℚ) :
    One.eval termThreeStage16C16 s = termThreeCoefficient 16 s := by
  norm_num [One.eval, evalWith, termThreeStage16C16, termThreeCoefficient,
    termThreeCoefficientMid] ; ring

private theorem termThree_stage16_coefficient_17 (s : ℚ) :
    One.eval termThreeStage16C17 s = termThreeCoefficient 17 s := by
  norm_num [One.eval, evalWith, termThreeStage16C17, termThreeCoefficient,
    termThreeCoefficientMid] ; ring

private theorem termThree_stage16_coefficient_18 (s : ℚ) :
    One.eval termThreeStage16C18 s = termThreeCoefficient 18 s := by
  norm_num [One.eval, evalWith, termThreeStage16C18, termThreeCoefficient,
    termThreeCoefficientMid] ; ring

private theorem termThree_stage16_coefficient_19 (s : ℚ) :
    One.eval termThreeStage16C19 s = termThreeCoefficient 19 s := by
  norm_num [One.eval, evalWith, termThreeStage16C19, termThreeCoefficient,
    termThreeCoefficientMid] ; ring

private theorem termThree_stage16_coefficient_20 (s : ℚ) :
    One.eval termThreeStage16C20 s = termThreeCoefficient 20 s := by
  norm_num [One.eval, evalWith, termThreeStage16C20, termThreeCoefficient,
    termThreeCoefficientMid] ; ring

private theorem termThree_stage16_coefficient_21 (s : ℚ) :
    One.eval termThreeStage16C21 s = termThreeCoefficient 21 s := by
  norm_num [One.eval, evalWith, termThreeStage16C21, termThreeCoefficient,
    termThreeCoefficientMid] ; ring

private theorem termThree_stage16_coefficient_22 (s : ℚ) :
    One.eval termThreeStage16C22 s = termThreeCoefficient 22 s := by
  norm_num [One.eval, evalWith, termThreeStage16C22, termThreeCoefficient,
    termThreeCoefficientMid] ; ring

private theorem termThree_stage16_coefficient_23 (s : ℚ) :
    One.eval termThreeStage16C23 s = termThreeCoefficient 23 s := by
  norm_num [One.eval, evalWith, termThreeStage16C23, termThreeCoefficient,
    termThreeCoefficientMid] ; ring

private theorem termThree_stage16_coefficient_24 (s : ℚ) :
    One.eval termThreeStage16C24 s = termThreeCoefficient 24 s := by
  norm_num [One.eval, evalWith, termThreeStage16C24, termThreeCoefficient,
    termThreeCoefficientHigh] ; ring

private theorem termThree_stage16_coefficient_25 (s : ℚ) :
    One.eval termThreeStage16C25 s = termThreeCoefficient 25 s := by
  norm_num [One.eval, evalWith, termThreeStage16C25, termThreeCoefficient,
    termThreeCoefficientHigh] ; ring

private theorem termThree_stage16_coefficient_26 (s : ℚ) :
    One.eval termThreeStage16C26 s = termThreeCoefficient 26 s := by
  norm_num [One.eval, evalWith, termThreeStage16C26, termThreeCoefficient,
    termThreeCoefficientHigh] ; ring

private theorem termThree_stage16_coefficient_27 (s : ℚ) :
    One.eval termThreeStage16C27 s = termThreeCoefficient 27 s := by
  norm_num [One.eval, evalWith, termThreeStage16C27, termThreeCoefficient,
    termThreeCoefficientHigh] ; ring

private theorem termThree_stage16_coefficient_28 (s : ℚ) :
    One.eval termThreeStage16C28 s = termThreeCoefficient 28 s := by
  norm_num [One.eval, evalWith, termThreeStage16C28, termThreeCoefficient,
    termThreeCoefficientHigh] ; ring

private theorem termThree_stage16_coefficient_29 (s : ℚ) :
    One.eval termThreeStage16C29 s = termThreeCoefficient 29 s := by
  norm_num [One.eval, evalWith, termThreeStage16C29, termThreeCoefficient,
    termThreeCoefficientHigh] ; ring

private theorem termThree_stage16_coefficient_30 (s : ℚ) :
    One.eval termThreeStage16C30 s = termThreeCoefficient 30 s := by
  norm_num [One.eval, evalWith, termThreeStage16C30, termThreeCoefficient,
    termThreeCoefficientHigh] ; ring

private theorem termThree_stage16_coefficient_31 (s : ℚ) :
    One.eval termThreeStage16C31 s = termThreeCoefficient 31 s := by
  norm_num [One.eval, evalWith, termThreeStage16C31, termThreeCoefficient,
    termThreeCoefficientHigh] ; ring

private theorem termThree_stage16_coefficient_32 (s : ℚ) :
    One.eval termThreeStage16C32 s = termThreeCoefficient 32 s := by
  norm_num [One.eval, evalWith, termThreeStage16C32, termThreeCoefficient,
    termThreeCoefficientHigh] ; ring

private theorem termThree_stage16_coefficient_33 (s : ℚ) :
    One.eval termThreeStage16C33 s = termThreeCoefficient 33 s := by
  norm_num [One.eval, evalWith, termThreeStage16C33, termThreeCoefficient,
    termThreeCoefficientHigh] ; ring

private theorem termThree_stage16_coefficient_34 (s : ℚ) :
    One.eval termThreeStage16C34 s = termThreeCoefficient 34 s := by
  norm_num [One.eval, evalWith, termThreeStage16C34, termThreeCoefficient,
    termThreeCoefficientHigh] ; ring

theorem eval_TermThreeStage16_eq_term3 (r s : ℚ) :
    Two.eval TermThreeStage16 r s = term3 r s := by
  rw [← termThree_stage16_spec, Two.eval_mul, eval_RData,
    ← termThree_stage15_spec, Two.eval_mul, eval_TData,
    ← termThree_stage14_spec, Two.eval_mul, eval_NData,
    ← termThree_stage13_spec, Two.eval_mul, eval_NData,
    ← termThree_stage12_spec, Two.eval_mul, eval_MData,
    ← termThree_stage11_spec, Two.eval_mul, eval_MData,
    ← termThree_stage10_spec, Two.eval_mul, eval_LData,
    ← termThree_stage9_spec, Two.eval_mul, eval_KData,
    ← termThree_stage8_spec, Two.eval_mul, eval_KData,
    ← termThree_stage7_spec, Two.eval_mul, eval_KData,
    ← termThree_stage6_spec, Two.eval_mul, eval_KData,
    ← termThree_stage5_spec, Two.eval_mul, eval_EData,
    ← termThree_stage4_spec, Two.eval_mul, eval_EData,
    ← termThree_stage3_spec, Two.eval_mul, eval_DData,
    ← termThree_stage2_spec, Two.eval_mul, eval_BData,
    ← termThree_stage1_spec, Two.eval_mul, eval_NegData, eval_BData]
  simp only [term3]
  ring

theorem eval_TermThreeStage16_eq_evalThirtyFive (r s : ℚ) :
    Two.eval TermThreeStage16 r s =
      evalThirtyFive (fun n => termThreeCoefficient n s) r := by
  simp only [Two.eval, TermThreeStage16, evalWith,
    termThree_stage16_coefficient_0, termThree_stage16_coefficient_1,
    termThree_stage16_coefficient_2, termThree_stage16_coefficient_3,
    termThree_stage16_coefficient_4, termThree_stage16_coefficient_5,
    termThree_stage16_coefficient_6, termThree_stage16_coefficient_7,
    termThree_stage16_coefficient_8, termThree_stage16_coefficient_9,
    termThree_stage16_coefficient_10, termThree_stage16_coefficient_11,
    termThree_stage16_coefficient_12, termThree_stage16_coefficient_13,
    termThree_stage16_coefficient_14, termThree_stage16_coefficient_15,
    termThree_stage16_coefficient_16, termThree_stage16_coefficient_17,
    termThree_stage16_coefficient_18, termThree_stage16_coefficient_19,
    termThree_stage16_coefficient_20, termThree_stage16_coefficient_21,
    termThree_stage16_coefficient_22, termThree_stage16_coefficient_23,
    termThree_stage16_coefficient_24, termThree_stage16_coefficient_25,
    termThree_stage16_coefficient_26, termThree_stage16_coefficient_27,
    termThree_stage16_coefficient_28, termThree_stage16_coefficient_29,
    termThree_stage16_coefficient_30, termThree_stage16_coefficient_31,
    termThree_stage16_coefficient_32, termThree_stage16_coefficient_33,
    termThree_stage16_coefficient_34, evalThirtyFive]
  ring

theorem termThree_dense_expansion (r s : ℚ) :
    term3 r s = evalThirtyFive (fun n => termThreeCoefficient n s) r := by
  rw [← eval_TermThreeStage16_eq_term3, eval_TermThreeStage16_eq_evalThirtyFive]

end MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Dense
