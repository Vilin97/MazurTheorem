/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateDenseTermTwoC12
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateTermTwoData
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Final dense multiplication and coefficient checks for RelationFour term two -/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Dense

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveRelationFourCertificate.Internal

private def termTwoStage13C0 : One :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, -1]

private def termTwoStage13C1 : One :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 5, -13, 27, 35, -14, 54, -25,
   69, -56, 32, -17, 8, -3, 1]

private def termTwoStage13C2 : One :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -13, 49, -66, -107, 678, -1982, 1078,
   -1103, 261, -735, -166, 1088, -1235, 1002, -689, 403, -213, 87, -28, 7, -1]

private def termTwoStage13C3 : One :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 8, -35, -25, 712, -3542, 9220, -13630, 7436,
   28503, -39322, 45601, -37120, 48850, -53087, 38137, -19924, 7368, -572, -1928, 2507, -1954,
   1118, -511, 183, -48, 9, -1]

private def termTwoStage13C4 : One :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -25, 232, -1370, 5818, -15193, 19785, 26192, -193068,
   481231, -735689, 447353, -99624, -128295, 38086, -88246, 347234, -509756, 490087, -379336,
   254945, -157731, 87359, -41370, 16401, -5108, 1053, -70, -39, 16, -2]

private def termTwoStage13C5 : One :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 15, -122, 600, -1874, 1072, 23725, -159621, 574951, -1371150,
   2037906, -1056476, -3111919, 10085961, -12560915, 10087863, -5903063, 5446355, -7234835,
   7039442, -4817560, 2525844, -1069035, 392683, -84084, -60103, 96031, -78195, 46581, -20793,
   6914, -1661, 248, -16, 0]

private def termTwoStage13C6 : One :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 50, -766, 6362, -34943, 141193, -407616, 725450, 104174, -5597804,
   21243107, -47989577, 71306091, -61610846, -6992022, 81353273, -104746662, 67316308,
   -24434340, 17201028, -29138564, 34005865, -27768142, 17805699, -10260780, 5905856, -3358791,
   1780995, -827835, 308680, -82033, 11039, 2002, -1471, 346, -40, 2]

private def termTwoStage13C7 : One :=
  [0, 0, 0, 0, 0, 0, -1, 22, -253, 805, 6487, -97211, 651174, -3022107, 10487532, -27540575,
   50570172, -46828062, -64497473, 375246093, -858673760, 1253747094, -1089790193, 377310555,
   366704979, -601899103, 347371191, -38501948, -69150855, 34138531, 15941687, -28578061,
   17881944, -6820492, 1897146, -867579, 953861, -852659, 516463, -221832, 67264, -13453, 1514,
   -39, -11, 1]

private def termTwoStage13C8 : One :=
  [0, 0, 0, 0, 0, 0, 40, -879, 10111, -61827, 199057, 44932, -4334063, 28629010, -120261749,
   376579641, -898194528, 1594515228, -1858275171, 494177912, 3482027961, -9369336742,
   13384641244, -12169638291, 6376267069, -334709544, -2352733174, 1895757980, -561481698,
   -190314016, 266489426, -108223366, 2575262, 17985123, -5402697, -5850236, 7837588, -4939360,
   1998524, -504744, 45682, 18875, -8745, 1724, -179, 8]

private def termTwoStage13C9 : One :=
  [0, 0, 0, 0, 1, -27, -399, 13445, -169953, 1201543, -5534723, 16468596, -22567064, -73389464,
   644840097, -2661024632, 7753980857, -17223710551, 29319527756, -36256623181, 25674804454,
   10622981180, -60129264345, 93885094253, -91098486761, 58474216994, -21802211138, 268046760,
   5154863929, -3044661957, 437053940, 511245189, -403882212, 106346024, 48375942, -67571840,
   37542988, -11626690, 783547, 1233810, -726915, 220869, -40502, 4049, -77, -26, 2]

private def termTwoStage13C10 : One :=
  [0, 0, 0, 0, -35, 937, -3271, -90201, 1565508, -12613335, 66559007, -252064963, 699520994,
   -1276129395, 447852257, 7313478143, -34369033917, 98357581551, -209223976279, 344656860849,
   -434202174784, 379180994446, -145733734781, -170228311492, 400541364920, -441306531483,
   327426943014, -171894625299, 59777919238, -8825434719, -3305768492, 1852949729, 535363457,
   -1152720383, 775946871, -302412838, 48500605, 23918975, -22506341, 9581308, -2509664, 367783,
   -3671, -10771, 2319, -226, 9]

private def termTwoStage13C11 : One :=
  [0, 0, 0, 0, 592, -15732, 128587, -109599, -7554200, 79929496, -480305641, 2052115630,
   -6749128050, 17378574067, -33707858420, 39715084434, 18279937019, -246663981695,
   775028286213, -1648036438764, 2679750216701, -3379670522334, 3218886894266, -2100489681474,
   535959319549, 718369134131, -1229207154460, 1095609469930, -692723441174, 329029530267,
   -115598164641, 26819946018, -2120826682, -658522248, -458392126, 896556782, -646368506,
   299785164, -95727953, 19004897, -837956, -856267, 321915, -60586, 6434, -298, -7, 1]

private def termTwoStage13C12 : One :=
  [0, 0, 1, -36, -5779, 161826, -1636790, 7783338, 2204955, -280986890, 2185994234,
   -10601378790, 38745975692, -113534617565, 271777939769, -522099754710, 749810973006,
   -590081251814, -607610958826, 3526051829210, -8294510792292, 13739290705318, -17479978157759,
   17399289776391, -13342287677249, 7343532126376, -2074770253859, -944272329204, 1814501307614,
   -1492088713852, 870754305022, -393902123439, 139200425143, -36033348740, 4979725372,
   774100320, -600757185, 58324330, 91237537, -64416149, 24409639, -6140593, 1034864, -103890,
   2673, 755, -98, 4]

private def termTwoStage13C13 : One :=
  [0, 0, -27, 958, 33219, -1114730, 12680619, -79022960, 250422453, 79732178, -5526296683,
   35060386608, -145552554484, 469924926652, -1249659985812, 2781868451013, -5160209985217,
   7771529783551, -8782836526377, 5238188799453, 5713479318413, -24066728544354, 44753596182769,
   -59304570263491, 61213663458231, -50519543287162, 33337895853423, -17087811280692,
   6095037057880, -694998028963, -988775866662, 1001440822828, -599872584190, 272821008615,
   -98916939504, 28052257837, -5528075525, 329629096, 261162812, -122485378, 27557813, -2348877,
   -608029, 270318, -51834, 5861, -380, 11]

private def termTwoStage13C14 : One :=
  [0, 0, 349, -12199, -87124, 5326983, -68088241, 482046947, -2098721873, 5258181262,
   -942622795, -60317891272, 345497118239, -1283085543126, 3757014364556, -9178096156599,
   19064664322645, -33799825176238, 50732741440158, -62836058796828, 59378148520849,
   -31240568825549, -20309679576806, 79565095493632, -123611407443509, 136646983238447,
   -119260992744795, 85224850368699, -50540221710238, 24838268962921, -9906098053478,
   2986830641597, -490589703523, -128349539923, 158901705563, -86210947816, 34188788959,
   -10694628258, 2618203497, -463431461, 42144243, 5347233, -2988378, 615106, -73260, 4491, 13,
   -21, 1]

private def termTwoStage13C15 : One :=
  [0, 0, -2875, 98974, -274892, -17323387, 266087520, -2078761305, 10352917118, -35121141473,
   77171748691, -61354735971, -343309289910, 2084796968377, -7304797439955, 19884475856516,
   -45196035366304, 88090565932778, -148776229530514, 218190259589962, -274730951129666,
   288227304411382, -236346160894432, 124390860147270, 10697203134232, -120176708180795,
   172481504767905, -167605839722821, 128499102313385, -81793901051451, 44248445739236,
   -20585960660731, 8273825901292, -2862702653480, 837726489924, -196692308142, 30651183584,
   724101743, -2734583928, 1214391209, -354467476, 76662911, -12317756, 1383716, -87686, -902,
   749, -64, 2]

private def termTwoStage13C16 : One :=
  [0, 0, 16950, -574699, 4195510, 31920157, -762384010, 6701242131, -36532159815, 140191501417,
   -394924598505, 806359458215, -997739199425, -436659299784, 7050394145943, -25938491177676,
   68264118414814, -147107597372418, 271427260102556, -438163621669550, 623111523037042,
   -775798868075218, 833109106566471, -754623179194116, 555136668036794, -303071028523737,
   81438761697211, 57388799894465, -109096889896322, 102319650016115, -71952609778665,
   41611304874750, -20549326518056, 8841151097311, -3354633511035, 1130796571669, -339526561682,
   90478191186, -21123510817, 4203353792, -675229205, 76890996, -3138459, -974678, 273114,
   -38170, 3309, -170, 4]

private def termTwoStage13C17 : One :=
  [0, -1, -76079, 2541800, -24559026, 18178057, 1518412098, -16396747652, 98013371147,
   -406935942890, 1269401960071, -3093634698593, 5951172392845, -8691505728413, 7400539461709,
   6815416112981, -49468081697562, 141154268455683, -300644543864177, 536470255621300,
   -837386370335926, 1158338212609181, -1415882190686908, 1515717176891213, -1406377277113205,
   1117921879682973, -748878194695474, 409809480802159, -169114834585049, 36966975344819,
   14977884969167, -24010009336564, 17658140970098, -9714992716224, 4416788574421,
   -1726124444542, 592071816235, -180517715771, 49283056133, -12069344585, 2638092552,
   -508152454, 84530621, -11817756, 1340942, -117893, 7499, -306, 6]

private def termTwoStage13C18 : One :=
  [0, 20, 269693, -8890295, 97839753, -383337458, -1535895593, 29692950424, -203539887726,
   911573024646, -3034355727583, 7973817174718, -17154786334334, 30935189123810,
   -46927484871180, 57464304870219, -47066300051383, -6984602085674, 126825805126867,
   -325568430728001, 605475449582954, -951172024629601, 1311552393891636, -1594790986799757,
   1702289269415495, -1586948212729129, 1287374043150409, -906194228280415, 551442366422965,
   -288047724986404, 127242972011250, -45952200008702, 12353733095726, -1540453075028,
   -718193117166, 657206331402, -318083195445, 117187074359, -35769840807, 9371984314,
   -2149418192, 436319051, -78576698, 12441009, -1693878, 191462, -17099, 1123, -48, 1]

private def termTwoStage13C19 : One :=
  [0, -188, -772240, 25177272, -297467706, 1638093210, -2253753643, -34884988185, 321600796921,
   -1601504087463, 5679139863308, -15691792107978, 35473709523174, -67992552865389,
   113478515260169, -167098737642862, 216010757802679, -238313804234446, 211687887017545,
   -127009235951798, -12857132958918, 206375029087625, -450786539782923, 718677920287200,
   -945791110777245, 1056762908352561, -1012802297217190, 838043834205688, -601950330215502,
   376988754584614, -206490281007495, 99050644818736, -41578953947715, 15220735493521,
   -4822711470274, 1303953448082, -292682184938, 51322676224, -5817707071, -54216614, 218446333,
   -60982944, 10431888, -1208176, 87007, -2044, -279, 30, -1]

private def termTwoStage13C20 : One :=
  [0, 1104, 1810090, -58587848, 722129056, -4632648763, 15164006431, 6305482129, -353513758068,
   2169051471982, -8411643972007, 24511633463952, -57481256633931, 113246893612129,
   -193857278907652, 295588716345363, -406703144984318, 504206753733201, -559538823246399,
   558905451834990, -515165073051875, 449734070818918, -365718866214989, 248511751038404,
   -93854786678177, -71266446842476, 200282810124732, -259244754670840, 247633855700720,
   -192286003368899, 126110518505302, -71239529620646, 35053271982292, -15122798372659,
   5740470071643, -1919102334168, 564188230822, -145216332084, 32462210412, -6220627236,
   1000777264, -130519229, 12883741, -794330, -697, 6385, -731, 41, -1]

private def termTwoStage13C21 : One :=
  [0, -4539, -3496799, 112984669, -1430632695, 9981690289, -42024521035, 85388431885,
   160088912613, -2090416582548, 9640312443646, -30449429319296, 74750979984780,
   -151071408047476, 261408492624299, -399504754214479, 551595835760528, -693849889894016,
   791147234829565, -813424286707745, 762257448535641, -673792841459581, 588195102312047,
   -517972687737728, 447257388253205, -357566177221427, 250208665085025, -145281904107920,
   64249334276874, -15788466526878, -5139530331964, 9637450586489, -7495473935703,
   4284961693548, -2000498057197, 792957611689, -271764125453, 81268380854, -21285671424,
   4881769810, -976381798, 168912619, -24950557, 3087755, -311526, 24608, -1427, 54, -1]

private def termTwoStage13C22 : One :=
  [0, 13872, 5576614, -181274432, 2337940585, -17164163708, 81504489818, -245521021397,
   330877702882, 962897847748, -7839026439582, 29118901298007, -77265556089152, 162731084824987,
   -286463856770943, 437176586788005, -596281185334668, 742094714500138, -846175492174619,
   875144772806821, -811223996300725, 673333618164946, -510633499565501, 371220481487067,
   -275384601171306, 214294223535649, -168394629306824, 125285173089156, -84205502326119,
   49946694947437, -25894990008678, 11682759506828, -4567983488440, 1537831368654,
   -440642074343, 105239388015, -20089065434, 2750999440, -154649174, -44243524, 17107986,
   -3403528, 468762, -46531, 3230, -142, 3, 0]

private def termTwoStage13C23 : One :=
  [0, -32642, -7318239, 241987802, -3164426234, 23998950308, -121986754208, 430090198213,
   -1002898544200, 1031098550431, 2965426673970, -19240037319799, 60501237318217,
   -138234615180156, 253379296763482, -391121204145375, 527155308486888, -640333402592396,
   716343247947094, -740885758084823, 699739813033619, -592345244117535, 442012442131756,
   -287606739684328, 163102687791859, -82614987739400, 40484619208449, -21970863235618,
   13967695831891, -9362843616856, 5866995645904, -3251216578537, 1569147028920, -658616059270,
   240704410978, -76620565305, 21208536614, -5085625106, 1050046349, -185052506, 27496759,
   -3386106, 337123, -26137, 1484, -55, 1]

private def termTwoStage13C24 : One :=
  [0, 60412, 7833596, -267850429, 3544806347, -27456561863, 145443869122, -556841755986,
   1558188164246, -3020956622752, 2911130224278, 4814041731971, -30776682214959, 86082550524810,
   -173556414718532, 280391412865376, -381167693821678, 452335193293595, -484922877740359,
   482546407916252, -450567625430908, 391785064123338, -311466001224648, 221717669864541,
   -138457058725919, 74132738415906, -32895913067158, 11256285854598, -2284348792978,
   -357974761046, 645775305489, -393851246447, 173200711228, -61755782200, 18556308265,
   -4761861551, 1044665200, -194589375, 30369940, -3892821, 398123, -31120, 1736, -61, 1]

private def termTwoStage13C25 : One :=
  [0, -89023, -6724621, 244065446, -3270428474, 25673954018, -139450433123, 559843821523,
   -1712472337403, 4001038978440, -6855281881778, 7059495650613, 2369289496871, -30316109726703,
   81625380144498, -150147966227323, 217514298076906, -262051516204118, 272263338595748,
   -252492862245146, 216201368107799, -175417084011697, 136123039020988, -100200983833969,
   68712007426644, -43050120952296, 24246063465421, -12129380552395, 5346968149087,
   -2067750560830, 700518334807, -208260807996, 54595761715, -12718679632, 2657707423,
   -501865345, 85661902, -13061736, 1734608, -193124, 17118, -1122, 48, -1]

private def termTwoStage13C26 : One :=
  [0, 105028, 4482377, -180929009, 2462402802, -19485558001, 107296211317, -442508451721,
   1420773750307, -3619545267955, 7335167992501, -11554648784817, 12891269163616,
   -5869116134959, -14317655131674, 47423992277111, -85436093870433, 115157738276393,
   -125783329436327, 115561822707510, -91723466972760, 64543882147012, -41434559075050,
   25033802848233, -14636359670628, 8391403844330, -4674491724842, 2464143913556,
   -1192646684237, 517153791139, -197576882540, 65801800987, -18968530097, 4705850703,
   -998723942, 179927578, -27215310, 3400307, -342394, 26743, -1521, 56, -1]

private def termTwoStage13C27 : One :=
  [0, -99176, -2161286, 107137278, -1491640374, 11851342701, -65557587416, 273702548295,
   -900771718659, 2397433467185, -5236912012898, 9434197432718, -13895337998970, 16174822206601,
   -13289615909169, 3560510789918, 11571742131818, -27370817224154, 38086677015386,
   -40336792029954, 34851454747300, -25302371924576, 15650272916776, -8268499588818,
   3690698834190, -1344315934583, 362180762770, -44630325192, -20200752440, 17367389997,
   -7603644433, 2414347221, -597614419, 117521535, -18322273, 2227522, -204377, 13347, -554, 11,
   0]

private def termTwoStage13C28 : One :=
  [0, 74504, 598681, -49226620, 711678610, -5663154879, 31209109809, -130249557312,
   431616396291, -1169007683420, 2638456265877, -5027055576724, 8140603960908, -11212161238728,
   13039205477424, -12512895981135, 9294251081109, -4199401862806, -1078941563033,
   4859455651876, -6356495377382, 5896255128634, -4420150241515, 2815297693647, -1563940420388,
   768769977709, -336390526602, 130921146620, -45062645951, 13598988972, -3561654519, 800545580,
   -152500182, 24257402, -3161161, 328794, -26260, 1513, -56, 1]

private def termTwoStage13C29 : One :=
  [0, -43965, 55766, 16692293, -258964347, 2063673734, -11234549753, 46268303837, -151796687583,
   409298027306, -926660826429, 1790086680292, -2984890522524, 4330981451143, -5499312373396,
   6130431211432, -5996333215780, 5115768791401, -3759345673233, 2329377874837, -1172088410170,
   440048509834, -88157744383, -26193055114, 36843466448, -21561521193, 8893010010, -2839033924,
   721409820, -146656741, 23664822, -2972434, 280773, -18790, 795, -16, 0, 0]

private def termTwoStage13C30 : One :=
  [0, 19944, -152969, -3759477, 68235355, -547611125, 2917938424, -11676810734, 37188305223,
   -97455299621, 214847962425, -405297068517, 662965771852, -949724412067, 1201049434044,
   -1350900023205, 1360906641453, -1234215620129, 1009081650720, -741601052797, 486848570355,
   -283252170767, 144893215446, -64689711614, 25039655694, -8348509717, 2381055959, -576222510,
   117126869, -19731691, 2705153, -294102, 24394, -1450, 55, -1]

private def termTwoStage13C31 : One :=
  [0, -6714, 81272, 389394, -11833224, 97932612, -505783452, 1924711974, -5784858612,
   14244659865, -29362486683, 51452586767, -77592094689, 101541154115, -115709021408,
   114712396153, -98604389670, 73182577826, -46708589805, 25542230932, -11923526374, 4732022292,
   -1588378474, 447898792, -105131458, 20282594, -3159903, 387561, -36016, 2383, -100, 2]

private def termTwoStage13C32 : One :=
  [0, 1580, -23950, 47480, 1062994, -10124346, 50437549, -176076558, 473871902, -1028292083,
   1835263595, -2711357213, 3320338702, -3373345087, 2847605111, -2000796500, 1171542982,
   -571648219, 232006493, -77987548, 21555148, -4844225, 870669, -122117, 12873, -959, 45, -1]

private def termTwoStage13C33 : One :=
  [0, -232, 3992, -20270, 1112, 378819, -1969438, 5852815, -11989923, 18006885, -20450896,
   17901865, -12221205, 6546127, -2753123, 904768, -229696, 44141, -6206, 602, -36, 1]

private def termTwoStage13C34 : One :=
  [0, 16, -296, 1948, -6026, 10368, -10961, 7511, -3409, 1019, -193, 21, -1]

def TermTwoStage13 : Two :=
  [termTwoStage13C0, termTwoStage13C1, termTwoStage13C2, termTwoStage13C3,
    termTwoStage13C4, termTwoStage13C5, termTwoStage13C6, termTwoStage13C7,
    termTwoStage13C8, termTwoStage13C9, termTwoStage13C10, termTwoStage13C11,
    termTwoStage13C12, termTwoStage13C13, termTwoStage13C14, termTwoStage13C15,
    termTwoStage13C16, termTwoStage13C17, termTwoStage13C18, termTwoStage13C19,
    termTwoStage13C20, termTwoStage13C21, termTwoStage13C22, termTwoStage13C23,
    termTwoStage13C24, termTwoStage13C25, termTwoStage13C26, termTwoStage13C27,
    termTwoStage13C28, termTwoStage13C29, termTwoStage13C30, termTwoStage13C31,
    termTwoStage13C32, termTwoStage13C33, termTwoStage13C34]

theorem termTwo_stage13_spec :
    Two.mul TermTwoStage12 SData = TermTwoStage13 := by
  decide

private theorem termTwo_stage13_coefficient_0 (s : ℚ) :
    One.eval termTwoStage13C0 s = termTwoCoefficient 0 s := by
  norm_num [One.eval, evalWith, termTwoStage13C0, termTwoCoefficient,
    termTwoCoefficientLow] ; ring

private theorem termTwo_stage13_coefficient_1 (s : ℚ) :
    One.eval termTwoStage13C1 s = termTwoCoefficient 1 s := by
  norm_num [One.eval, evalWith, termTwoStage13C1, termTwoCoefficient,
    termTwoCoefficientLow] ; ring

private theorem termTwo_stage13_coefficient_2 (s : ℚ) :
    One.eval termTwoStage13C2 s = termTwoCoefficient 2 s := by
  norm_num [One.eval, evalWith, termTwoStage13C2, termTwoCoefficient,
    termTwoCoefficientLow] ; ring

private theorem termTwo_stage13_coefficient_3 (s : ℚ) :
    One.eval termTwoStage13C3 s = termTwoCoefficient 3 s := by
  norm_num [One.eval, evalWith, termTwoStage13C3, termTwoCoefficient,
    termTwoCoefficientLow] ; ring

private theorem termTwo_stage13_coefficient_4 (s : ℚ) :
    One.eval termTwoStage13C4 s = termTwoCoefficient 4 s := by
  norm_num [One.eval, evalWith, termTwoStage13C4, termTwoCoefficient,
    termTwoCoefficientLow] ; ring

private theorem termTwo_stage13_coefficient_5 (s : ℚ) :
    One.eval termTwoStage13C5 s = termTwoCoefficient 5 s := by
  norm_num [One.eval, evalWith, termTwoStage13C5, termTwoCoefficient,
    termTwoCoefficientLow] ; ring

private theorem termTwo_stage13_coefficient_6 (s : ℚ) :
    One.eval termTwoStage13C6 s = termTwoCoefficient 6 s := by
  norm_num [One.eval, evalWith, termTwoStage13C6, termTwoCoefficient,
    termTwoCoefficientLow] ; ring

private theorem termTwo_stage13_coefficient_7 (s : ℚ) :
    One.eval termTwoStage13C7 s = termTwoCoefficient 7 s := by
  norm_num [One.eval, evalWith, termTwoStage13C7, termTwoCoefficient,
    termTwoCoefficientLow] ; ring

private theorem termTwo_stage13_coefficient_8 (s : ℚ) :
    One.eval termTwoStage13C8 s = termTwoCoefficient 8 s := by
  norm_num [One.eval, evalWith, termTwoStage13C8, termTwoCoefficient,
    termTwoCoefficientLow] ; ring

private theorem termTwo_stage13_coefficient_9 (s : ℚ) :
    One.eval termTwoStage13C9 s = termTwoCoefficient 9 s := by
  norm_num [One.eval, evalWith, termTwoStage13C9, termTwoCoefficient,
    termTwoCoefficientLow] ; ring

private theorem termTwo_stage13_coefficient_10 (s : ℚ) :
    One.eval termTwoStage13C10 s = termTwoCoefficient 10 s := by
  norm_num [One.eval, evalWith, termTwoStage13C10, termTwoCoefficient,
    termTwoCoefficientLow] ; ring

private theorem termTwo_stage13_coefficient_11 (s : ℚ) :
    One.eval termTwoStage13C11 s = termTwoCoefficient 11 s := by
  norm_num [One.eval, evalWith, termTwoStage13C11, termTwoCoefficient,
    termTwoCoefficientLow] ; ring

private theorem termTwo_stage13_coefficient_12 (s : ℚ) :
    One.eval termTwoStage13C12 s = termTwoCoefficient 12 s := by
  norm_num [One.eval, evalWith, termTwoStage13C12, termTwoCoefficient,
    termTwoCoefficientMid] ; ring

private theorem termTwo_stage13_coefficient_13 (s : ℚ) :
    One.eval termTwoStage13C13 s = termTwoCoefficient 13 s := by
  norm_num [One.eval, evalWith, termTwoStage13C13, termTwoCoefficient,
    termTwoCoefficientMid] ; ring

private theorem termTwo_stage13_coefficient_14 (s : ℚ) :
    One.eval termTwoStage13C14 s = termTwoCoefficient 14 s := by
  norm_num [One.eval, evalWith, termTwoStage13C14, termTwoCoefficient,
    termTwoCoefficientMid] ; ring

private theorem termTwo_stage13_coefficient_15 (s : ℚ) :
    One.eval termTwoStage13C15 s = termTwoCoefficient 15 s := by
  norm_num [One.eval, evalWith, termTwoStage13C15, termTwoCoefficient,
    termTwoCoefficientMid] ; ring

private theorem termTwo_stage13_coefficient_16 (s : ℚ) :
    One.eval termTwoStage13C16 s = termTwoCoefficient 16 s := by
  norm_num [One.eval, evalWith, termTwoStage13C16, termTwoCoefficient,
    termTwoCoefficientMid] ; ring

private theorem termTwo_stage13_coefficient_17 (s : ℚ) :
    One.eval termTwoStage13C17 s = termTwoCoefficient 17 s := by
  norm_num [One.eval, evalWith, termTwoStage13C17, termTwoCoefficient,
    termTwoCoefficientMid] ; ring

private theorem termTwo_stage13_coefficient_18 (s : ℚ) :
    One.eval termTwoStage13C18 s = termTwoCoefficient 18 s := by
  norm_num [One.eval, evalWith, termTwoStage13C18, termTwoCoefficient,
    termTwoCoefficientMid] ; ring

private theorem termTwo_stage13_coefficient_19 (s : ℚ) :
    One.eval termTwoStage13C19 s = termTwoCoefficient 19 s := by
  norm_num [One.eval, evalWith, termTwoStage13C19, termTwoCoefficient,
    termTwoCoefficientMid] ; ring

private theorem termTwo_stage13_coefficient_20 (s : ℚ) :
    One.eval termTwoStage13C20 s = termTwoCoefficient 20 s := by
  norm_num [One.eval, evalWith, termTwoStage13C20, termTwoCoefficient,
    termTwoCoefficientMid] ; ring

private theorem termTwo_stage13_coefficient_21 (s : ℚ) :
    One.eval termTwoStage13C21 s = termTwoCoefficient 21 s := by
  norm_num [One.eval, evalWith, termTwoStage13C21, termTwoCoefficient,
    termTwoCoefficientMid] ; ring

private theorem termTwo_stage13_coefficient_22 (s : ℚ) :
    One.eval termTwoStage13C22 s = termTwoCoefficient 22 s := by
  norm_num [One.eval, evalWith, termTwoStage13C22, termTwoCoefficient,
    termTwoCoefficientMid] ; ring

private theorem termTwo_stage13_coefficient_23 (s : ℚ) :
    One.eval termTwoStage13C23 s = termTwoCoefficient 23 s := by
  norm_num [One.eval, evalWith, termTwoStage13C23, termTwoCoefficient,
    termTwoCoefficientMid] ; ring

private theorem termTwo_stage13_coefficient_24 (s : ℚ) :
    One.eval termTwoStage13C24 s = termTwoCoefficient 24 s := by
  norm_num [One.eval, evalWith, termTwoStage13C24, termTwoCoefficient,
    termTwoCoefficientHigh] ; ring

private theorem termTwo_stage13_coefficient_25 (s : ℚ) :
    One.eval termTwoStage13C25 s = termTwoCoefficient 25 s := by
  norm_num [One.eval, evalWith, termTwoStage13C25, termTwoCoefficient,
    termTwoCoefficientHigh] ; ring

private theorem termTwo_stage13_coefficient_26 (s : ℚ) :
    One.eval termTwoStage13C26 s = termTwoCoefficient 26 s := by
  norm_num [One.eval, evalWith, termTwoStage13C26, termTwoCoefficient,
    termTwoCoefficientHigh] ; ring

private theorem termTwo_stage13_coefficient_27 (s : ℚ) :
    One.eval termTwoStage13C27 s = termTwoCoefficient 27 s := by
  norm_num [One.eval, evalWith, termTwoStage13C27, termTwoCoefficient,
    termTwoCoefficientHigh] ; ring

private theorem termTwo_stage13_coefficient_28 (s : ℚ) :
    One.eval termTwoStage13C28 s = termTwoCoefficient 28 s := by
  norm_num [One.eval, evalWith, termTwoStage13C28, termTwoCoefficient,
    termTwoCoefficientHigh] ; ring

private theorem termTwo_stage13_coefficient_29 (s : ℚ) :
    One.eval termTwoStage13C29 s = termTwoCoefficient 29 s := by
  norm_num [One.eval, evalWith, termTwoStage13C29, termTwoCoefficient,
    termTwoCoefficientHigh] ; ring

private theorem termTwo_stage13_coefficient_30 (s : ℚ) :
    One.eval termTwoStage13C30 s = termTwoCoefficient 30 s := by
  norm_num [One.eval, evalWith, termTwoStage13C30, termTwoCoefficient,
    termTwoCoefficientHigh] ; ring

private theorem termTwo_stage13_coefficient_31 (s : ℚ) :
    One.eval termTwoStage13C31 s = termTwoCoefficient 31 s := by
  norm_num [One.eval, evalWith, termTwoStage13C31, termTwoCoefficient,
    termTwoCoefficientHigh] ; ring

private theorem termTwo_stage13_coefficient_32 (s : ℚ) :
    One.eval termTwoStage13C32 s = termTwoCoefficient 32 s := by
  norm_num [One.eval, evalWith, termTwoStage13C32, termTwoCoefficient,
    termTwoCoefficientHigh] ; ring

private theorem termTwo_stage13_coefficient_33 (s : ℚ) :
    One.eval termTwoStage13C33 s = termTwoCoefficient 33 s := by
  norm_num [One.eval, evalWith, termTwoStage13C33, termTwoCoefficient,
    termTwoCoefficientHigh] ; ring

private theorem termTwo_stage13_coefficient_34 (s : ℚ) :
    One.eval termTwoStage13C34 s = termTwoCoefficient 34 s := by
  norm_num [One.eval, evalWith, termTwoStage13C34, termTwoCoefficient,
    termTwoCoefficientHigh] ; ring

theorem eval_TermTwoStage13_eq_term2 (r s : ℚ) :
    Two.eval TermTwoStage13 r s = term2 r s := by
  rw [← termTwo_stage13_spec, Two.eval_mul, eval_SData,
    ← termTwo_stage12_spec, Two.eval_mul, eval_TData,
    ← termTwo_stage11_spec, Two.eval_mul, eval_P9Data,
    ← termTwo_stage10_spec, Two.eval_mul, eval_NData,
    ← termTwo_stage9_spec, Two.eval_mul, eval_MData,
    ← termTwo_stage8_spec, Two.eval_mul, eval_LData,
    ← termTwo_stage7_spec, Two.eval_mul, eval_LData,
    ← termTwo_stage6_spec, Two.eval_mul, eval_KData,
    ← termTwo_stage5_spec, Two.eval_mul, eval_JData,
    ← termTwo_stage4_spec, Two.eval_mul, eval_CData,
    ← termTwo_stage3_spec, Two.eval_mul, eval_CData,
    ← termTwo_stage2_spec, Two.eval_mul, eval_CData,
    ← termTwo_stage1_spec, Two.eval_mul, eval_NegData, eval_AData]
  simp only [term2]
  ring

theorem eval_TermTwoStage13_eq_evalThirtyFive (r s : ℚ) :
    Two.eval TermTwoStage13 r s =
      evalThirtyFive (fun n => termTwoCoefficient n s) r := by
  simp only [Two.eval, TermTwoStage13, evalWith,
    termTwo_stage13_coefficient_0, termTwo_stage13_coefficient_1,
    termTwo_stage13_coefficient_2, termTwo_stage13_coefficient_3,
    termTwo_stage13_coefficient_4, termTwo_stage13_coefficient_5,
    termTwo_stage13_coefficient_6, termTwo_stage13_coefficient_7,
    termTwo_stage13_coefficient_8, termTwo_stage13_coefficient_9,
    termTwo_stage13_coefficient_10, termTwo_stage13_coefficient_11,
    termTwo_stage13_coefficient_12, termTwo_stage13_coefficient_13,
    termTwo_stage13_coefficient_14, termTwo_stage13_coefficient_15,
    termTwo_stage13_coefficient_16, termTwo_stage13_coefficient_17,
    termTwo_stage13_coefficient_18, termTwo_stage13_coefficient_19,
    termTwo_stage13_coefficient_20, termTwo_stage13_coefficient_21,
    termTwo_stage13_coefficient_22, termTwo_stage13_coefficient_23,
    termTwo_stage13_coefficient_24, termTwo_stage13_coefficient_25,
    termTwo_stage13_coefficient_26, termTwo_stage13_coefficient_27,
    termTwo_stage13_coefficient_28, termTwo_stage13_coefficient_29,
    termTwo_stage13_coefficient_30, termTwo_stage13_coefficient_31,
    termTwo_stage13_coefficient_32, termTwo_stage13_coefficient_33,
    termTwo_stage13_coefficient_34, evalThirtyFive]
  ring

theorem termTwo_dense_expansion (r s : ℚ) :
    term2 r s = evalThirtyFive (fun n => termTwoCoefficient n s) r := by
  rw [← eval_TermTwoStage13_eq_term2, eval_TermTwoStage13_eq_evalThirtyFive]

end MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Dense
