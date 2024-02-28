
function smolproof(system,invsys,systemlink)
    isassi,assi = initassignement(invsys)
    antecedants = Set(Int[])
    cone = Set(Int[])
    front = Set(Int[length(system)-1])
    while length(front)>0
        id = pop!(front)
        if isassigned(systemlink,id)
            antecedants = systemlink[id]
        else
            isassi .= false
            assi .= false
            antecedants = unitpropag(system,invsys,id,isassi,assi)
            # antecedants = findall(unitpropag2(system,invsys,id,isassi,assi))
        end
        for i in antecedants
            if !(i in cone)
                push!(cone,i)
                push!(front,i)
            end
        end
    end
    return cone
end


function unitpropag2(system,invsys,init,isassi,assi) 
    n = length(system)
    front = zeros(Bool,n)
    front[init] = true
    antecedants = zeros(Bool,n)
    id = init
    eq = system[init]
    s = 0
    while true in front
        id = findfirst(front)
        front[id] = false
        eq = id==init ? reverse(system[id]) : system[id]
        s = slack(eq,isassi,assi)
        if s<0
            antecedants[id]=true
            return antecedants
        else
            for l in eq.t
                if !isassi[l.var.x+1,l.var.v+1] && l.coef > s
                    isassi[l.var.x+1,l.var.v+1] = true
                    assi[l.var.x+1,l.var.v+1] = l.sign
                    antecedants[id] = true
                    for j in invsys[l.var]
                        if j!=id
                            front[j] = true
                        end
                    end
                end
            end
        end
    end
    return antecedants
end
function makesmol(system,invsys,systemlink)
    normcoefsystem(system)
    # printsys(system)
    cone = @time smolproof2(system,invsys,systemlink)
    println(sum(cone),"/",length(system))
    # printsys(system,cone)
    
    cone = @time smolproof(system,invsys,systemlink)
    println(length(cone),"/",length(system))
    # printsys(system,cone)

end
# rup stop at first contradiction
c = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 257, 258, 259, 260, 261, 262, 263, 267, 268, 269, 270, 271, 272, 273, 277, 278, 279, 280, 282, 283, 284, 285, 287, 288, 289, 290, 292, 297, 298, 299, 300, 302, 303, 304, 305, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 321, 322, 323, 324, 325, 327, 328, 329, 330, 331, 332, 333, 334, 335, 337, 338, 339, 340, 342, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 362, 363, 364, 365, 367, 368, 372, 373, 377, 378, 379, 380, 382, 383, 384, 385, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 400, 402, 403, 404, 405, 406, 407, 408, 412, 413, 414, 415, 417, 418, 419, 420, 422, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 442, 443, 444, 445, 446, 447, 448, 449, 450, 452, 453, 454, 455, 456, 457, 458, 459, 460, 462, 463, 464, 465, 466, 467, 468, 472, 473, 477, 482, 483, 484, 485, 487, 488, 489, 490, 492, 493, 494, 495, 496, 497, 498, 499, 500, 502, 503, 504, 505, 507, 508, 512, 513, 514, 515, 517, 518, 519, 520, 522, 523, 524, 525, 527, 528, 532, 533, 534, 535, 537, 538, 539, 540, 542, 543, 547, 548, 549, 550, 551, 552, 553, 554, 555, 557, 558, 562, 563, 567, 568, 569, 570, 572, 573, 574, 575, 577, 578, 579, 580, 581, 587, 592, 593, 594, 595, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607, 608, 609, 610, 612, 613, 614, 615, 616, 617, 622, 623, 624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 642, 643, 644, 645, 647, 648, 649, 650, 652, 653, 654, 655, 656, 657, 658, 659, 660, 662, 663, 664, 665, 667, 672, 673, 674, 675, 676, 677, 678, 682, 683, 684, 685, 687, 692, 697, 698, 702, 707, 708, 709, 710, 712, 713, 714, 715, 716, 717, 722, 723, 724, 725, 726, 727, 728, 729, 730, 732, 737, 738, 742, 747, 748, 749, 750, 752, 753, 754, 755, 757, 758, 759, 760, 762, 763, 764, 765, 767, 768, 769, 770, 771, 772, 773, 774, 775, 777, 778, 779, 780, 781, 782, 783, 784, 785, 786, 787, 788, 789, 790, 792, 793, 794, 795, 797, 798, 799, 800, 801, 802, 807, 812, 817, 818, 819, 820, 821, 822, 823, 827, 828, 829, 830, 831, 832, 833, 834, 835, 836, 837, 838, 839, 840, 841, 847, 852, 853, 854, 855, 856, 857, 858, 859, 860, 862, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879, 880, 881, 882, 883, 884, 885, 887, 888, 889, 890, 892, 893, 894, 895, 896, 897, 898, 899, 900, 902, 903, 904, 905, 907, 908, 912, 913, 914, 915, 917, 918, 919, 920, 922, 923, 924, 925, 927, 928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 942, 957, 958, 959, 960, 961, 962, 963, 964, 965, 967, 968, 969, 970, 972, 973, 974, 975, 977, 978, 979, 980, 982, 983, 984, 985, 987, 988, 989, 990, 991, 992, 993, 994, 995, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1017, 1018, 1019, 1020, 1021, 1027, 1028, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1040, 1042, 1043, 1044, 1045, 1047, 1048, 1049, 1050, 1052, 1057, 1058, 1059, 1060, 1062, 1063, 1064, 1065, 1066, 1067, 1068, 1069, 1070, 1072, 1073, 1074, 1075, 1077, 1078, 1079, 1080, 1081, 1082, 1083, 1084, 1085, 1087, 1088, 1089, 1090, 1092, 1093, 1094, 1095, 1097, 1098, 1099, 1100, 1101, 1102, 1107, 1108, 1109, 1110, 1111, 1112, 1113, 1114, 1115, 1116, 1117, 1118, 1119, 1120, 1122, 1123, 1124, 1125, 1127, 1128, 1129, 1130, 1132, 1133, 1134, 1135, 1137, 1138, 1142, 1143, 1144, 1145, 1147, 1148, 1149, 1150, 1151, 1152, 1153, 1154, 1155, 1157, 1162, 1163, 1164, 1165, 1166, 1167, 1168, 1172, 1173, 1174, 1175, 1177, 1178, 1179, 1180, 1182, 1183, 1184, 1185, 1187, 1188, 1189, 1190, 1191, 1192, 1193, 1194, 1195, 1196, 1197, 1198, 1199, 1200, 1201, 1202, 1203, 1204, 1205, 1207, 1208, 1212, 1213, 1214, 1215, 1216, 1217, 1218, 1219, 1220, 1221, 1222, 1223, 1224, 1225, 1227, 1228, 1229, 1230, 1231, 1232, 1233, 1234, 1235, 1236, 1237, 1238, 1239, 1240, 1242, 1243, 1244, 1245, 1247, 1248, 1249, 1250, 1251, 1252, 1253, 1254, 1255, 1257, 1258, 1259, 1260, 1262, 1263, 1264, 1265, 1266, 1267, 1268, 1269, 1270, 1271, 1272, 1273, 1274, 1275, 1276, 1277, 1278, 1282, 1283, 1284, 1285, 1287, 1292, 1293, 1294, 1295, 1296, 1297, 1298, 1302, 1303, 1304, 1305, 1306, 1307, 1308, 1309, 1310, 1311, 1312, 1313, 1314, 1315, 1317, 1318, 1319, 1320, 1321, 1322, 1323, 1324, 1325, 1327, 1328, 1332, 1333, 1334, 1335, 1336, 1337, 1338, 1342, 1343, 1344, 1345, 1347, 1359, 1367, 1368, 1376, 1383, 1384, 1385, 1393, 1401, 1417, 1418, 1419, 1427, 1435, 1436, 1443, 1444, 1452, 1453, 1461, 1469, 1470, 1477, 1478, 1485, 1486, 1487, 1495, 1503, 1504, 1512, 1520, 1521, 1522, 1538, 1539, 1546, 1574, 1580, 1585, 1586, 1600, 1612, 1618, 1621, 1625, 1633, 1634, 1642, 1650, 1651, 1659, 1697, 1698, 1706, 1744, 1745, 1746, 1754, 1762, 1763, 1771, 1784, 1807, 1808, 1810, 1818, 1824, 1825, 1836, 1845, 1848, 1849, 1853, 1854, 1856, 1857, 1858, 1866, 1875, 1883, 1921, 1922, 1930, 1937, 1943, 1965, 1966, 1969, 1970, 1987, 2033, 2034, 2081, 2082, 2154, 2161, 2176, 2188, 2189, 2190, 2191, 2193, 2201, 2210, 2211, 2219, 2257, 2258, 2265, 2273, 2279, 2284, 2288, 2301, 2303, 2304, 2305, 2323, 2370, 2416, 2417, 2418, 2426, 2434, 2435, 2443, 2450, 2456, 2479, 2482, 2489, 2494, 2500, 2504, 2516, 2518, 2519, 2520, 2528, 2529, 2530, 2537, 2538, 2546, 2547, 2555, 2594, 2602, 2609, 2640, 2641, 2642]
# full rup
c2 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 282, 283, 284, 285, 287, 288, 289, 290, 292, 297, 298, 299, 300, 302, 303, 304, 305, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 321, 322, 323, 324, 325, 327, 328, 329, 330, 331, 332, 333, 334, 335, 337, 338, 339, 340, 342, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 362, 363, 364, 365, 367, 368, 372, 373, 374, 375, 377, 378, 379, 380, 381, 382, 383, 384, 385, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 400, 402, 403, 404, 405, 406, 407, 408, 412, 413, 414, 415, 417, 418, 419, 420, 422, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 452, 453, 454, 455, 456, 457, 458, 459, 460, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 482, 483, 484, 485, 487, 488, 489, 490, 492, 493, 494, 495, 496, 497, 498, 499, 500, 502, 503, 504, 505, 507, 508, 512, 513, 514, 515, 517, 518, 519, 520, 522, 523, 524, 525, 527, 528, 529, 530, 532, 533, 534, 535, 537, 538, 539, 540, 542, 543, 544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 562, 563, 567, 568, 569, 570, 571, 572, 573, 574, 575, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607, 608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 622, 623, 624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639, 640, 642, 643, 644, 645, 647, 648, 649, 650, 652, 653, 654, 655, 656, 657, 658, 659, 660, 662, 663, 664, 665, 667, 668, 669, 670, 671, 672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684, 685, 687, 688, 689, 690, 691, 692, 693, 694, 695, 697, 698, 702, 707, 708, 709, 710, 712, 713, 714, 715, 716, 717, 718, 719, 720, 722, 723, 724, 725, 726, 727, 728, 729, 730, 732, 733, 734, 735, 737, 738, 739, 740, 741, 742, 747, 748, 749, 750, 751, 752, 753, 754, 755, 756, 757, 758, 759, 760, 762, 763, 764, 765, 766, 767, 768, 769, 770, 771, 772, 773, 774, 775, 777, 778, 779, 780, 781, 782, 783, 784, 785, 786, 787, 788, 789, 790, 792, 793, 794, 795, 797, 798, 799, 800, 801, 802, 803, 804, 805, 807, 812, 813, 814, 815, 816, 817, 818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 828, 829, 830, 831, 832, 833, 834, 835, 836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847, 848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858, 859, 860, 862, 863, 864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879, 880, 881, 882, 883, 884, 885, 887, 888, 889, 890, 892, 893, 894, 895, 896, 897, 898, 899, 900, 902, 903, 904, 905, 907, 908, 909, 910, 911, 912, 913, 914, 915, 917, 918, 919, 920, 922, 923, 924, 925, 927, 928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 942, 952, 953, 957, 958, 959, 960, 961, 962, 963, 964, 965, 967, 968, 969, 970, 972, 973, 974, 975, 976, 977, 978, 979, 980, 982, 983, 984, 985, 987, 988, 989, 990, 991, 992, 993, 994, 995, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1040, 1042, 1043, 1044, 1045, 1047, 1048, 1049, 1050, 1052, 1057, 1058, 1059, 1060, 1062, 1063, 1064, 1065, 1066, 1067, 1068, 1069, 1070, 1072, 1073, 1074, 1075, 1077, 1078, 1079, 1080, 1081, 1082, 1083, 1084, 1085, 1087, 1088, 1089, 1090, 1092, 1093, 1094, 1095, 1097, 1098, 1099, 1100, 1101, 1102, 1103, 1104, 1105, 1106, 1107, 1108, 1109, 1110, 1111, 1112, 1113, 1114, 1115, 1116, 1117, 1118, 1119, 1120, 1122, 1123, 1124, 1125, 1127, 1128, 1129, 1130, 1131, 1132, 1133, 1134, 1135, 1137, 1138, 1142, 1143, 1144, 1145, 1147, 1148, 1149, 1150, 1151, 1152, 1153, 1154, 1155, 1157, 1162, 1163, 1164, 1165, 1166, 1167, 1168, 1172, 1173, 1174, 1175, 1177, 1178, 1179, 1180, 1182, 1183, 1184, 1185, 1187, 1188, 1189, 1190, 1191, 1192, 1193, 1194, 1195, 1196, 1197, 1198, 1199, 1200, 1201, 1202, 1203, 1204, 1205, 1207, 1208, 1212, 1213, 1214, 1215, 1216, 1217, 1218, 1219, 1220, 1221, 1222, 1223, 1224, 1225, 1227, 1228, 1229, 1230, 1231, 1232, 1233, 1234, 1235, 1236, 1237, 1238, 1239, 1240, 1242, 1243, 1244, 1245, 1247, 1248, 1249, 1250, 1251, 1252, 1253, 1254, 1255, 1257, 1258, 1259, 1260, 1262, 1263, 1264, 1265, 1266, 1267, 1268, 1269, 1270, 1271, 1272, 1273, 1274, 1275, 1276, 1277, 1278, 1282, 1283, 1284, 1285, 1287, 1288, 1289, 1290, 1292, 1293, 1294, 1295, 1296, 1297, 1298, 1302, 1303, 1304, 1305, 1306, 1307, 1308, 1309, 1310, 1311, 1312, 1313, 1314, 1315, 1317, 1318, 1319, 1320, 1321, 1322, 1323, 1324, 1325, 1327, 1328, 1329, 1330, 1331, 1332, 1333, 1334, 1335, 1336, 1337, 1338, 1339, 1340, 1341, 1342, 1343, 1344, 1345, 1347, 1348, 1349, 1350, 1351, 1358, 1359, 1366, 1367, 1368, 1375, 1376, 1383, 1384, 1385, 1392, 1393, 1400, 1401, 1402, 1409, 1410, 1417, 1418, 1419, 1426, 1427, 1434, 1435, 1436, 1443, 1444, 1451, 1452, 1453, 1460, 1461, 1468, 1469, 1470, 1477, 1478, 1485, 1486, 1487, 1494, 1495, 1502, 1503, 1504, 1511, 1512, 1519, 1520, 1521, 1522, 1529, 1530, 1537, 1538, 1539, 1546, 1547, 1553, 1554, 1559, 1560, 1564, 1565, 1568, 1569, 1571, 1572, 1573, 1574, 1575, 1576, 1577, 1578, 1579, 1580, 1581, 1582, 1583, 1584, 1585, 1586, 1593, 1594, 1600, 1601, 1606, 1607, 1611, 1612, 1615, 1616, 1618, 1619, 1620, 1621, 1622, 1623, 1624, 1625, 1626, 1627, 1628, 1629, 1630, 1631, 1632, 1633, 1634, 1641, 1642, 1649, 1650, 1651, 1658, 1659, 1665, 1666, 1671, 1672, 1676, 1677, 1680, 1681, 1683, 1684, 1685, 1686, 1687, 1688, 1689, 1690, 1691, 1692, 1693, 1694, 1695, 1696, 1697, 1698, 1705, 1706, 1712, 1713, 1718, 1719, 1723, 1724, 1727, 1728, 1730, 1731, 1732, 1733, 1734, 1735, 1736, 1737, 1738, 1739, 1740, 1741, 1742, 1743, 1744, 1745, 1746, 1753, 1754, 1761, 1762, 1763, 1770, 1771, 1777, 1778, 1783, 1784, 1788, 1789, 1792, 1793, 1795, 1796, 1797, 1798, 1799, 1800, 1801, 1802, 1803, 1804, 1805, 1806, 1807, 1808, 1809, 1810, 1817, 1818, 1824, 1825, 1830, 1831, 1835, 1836, 1839, 1840, 1842, 1843, 1844, 1845, 1846, 1847, 1848, 1849, 1850, 1851, 1852, 1853, 1854, 1855, 1856, 1857, 1858, 1865, 1866, 1873, 1874, 1875, 1882, 1883, 1889, 1890, 1895, 1896, 1900, 1901, 1904, 1905, 1907, 1908, 1909, 1910, 1911, 1912, 1913, 1914, 1915, 1916, 1917, 1918, 1919, 1920, 1921, 1922, 1929, 1930, 1936, 1937, 1942, 1943, 1947, 1948, 1951, 1952, 1954, 1955, 1956, 1957, 1958, 1959, 1960, 1961, 1962, 1963, 1964, 1965, 1966, 1967, 1968, 1969, 1970, 1977, 1978, 1985, 1986, 1987, 1994, 1995, 2001, 2002, 2007, 2008, 2012, 2013, 2016, 2017, 2019, 2020, 2021, 2022, 2023, 2024, 2025, 2026, 2027, 2028, 2029, 2030, 2031, 2032, 2033, 2034, 2041, 2042, 2048, 2049, 2054, 2055, 2059, 2060, 2063, 2064, 2066, 2067, 2068, 2069, 2070, 2071, 2072, 2073, 2074, 2075, 2076, 2077, 2078, 2079, 2080, 2081, 2082, 2089, 2090, 2097, 2098, 2099, 2106, 2107, 2113, 2114, 2119, 2120, 2124, 2125, 2128, 2129, 2131, 2132, 2133, 2134, 2135, 2136, 2137, 2138, 2139, 2140, 2141, 2142, 2143, 2144, 2145, 2146, 2153, 2154, 2160, 2161, 2166, 2167, 2171, 2172, 2175, 2176, 2178, 2179, 2180, 2181, 2182, 2183, 2184, 2185, 2186, 2187, 2188, 2189, 2190, 2191, 2192, 2193, 2194, 2201, 2202, 2209, 2210, 2211, 2218, 2219, 2225, 2226, 2231, 2232, 2236, 2237, 2240, 2241, 2243, 2244, 2245, 2246, 2247, 2248, 2249, 2250, 2251, 2252, 2253, 2254, 2255, 2256, 2257, 2258, 2265, 2266, 2272, 2273, 2278, 2279, 2283, 2284, 2287, 2288, 2290, 2291, 2292, 2293, 2294, 2295, 2296, 2297, 2298, 2299, 2300, 2301, 2302, 2303, 2304, 2305, 2306, 2313, 2314, 2321, 2322, 2323, 2330, 2331, 2337, 2338, 2343, 2344, 2348, 2349, 2352, 2353, 2355, 2356, 2357, 2358, 2359, 2360, 2361, 2362, 2363, 2364, 2365, 2366, 2367, 2368, 2369, 2370, 2377, 2378, 2384, 2385, 2390, 2391, 2395, 2396, 2399, 2400, 2402, 2403, 2404, 2405, 2406, 2407, 2408, 2409, 2410, 2411, 2412, 2413, 2414, 2415, 2416, 2417, 2418, 2425, 2426, 2433, 2434, 2435, 2442, 2443, 2449, 2450, 2455, 2456, 2460, 2461, 2464, 2465, 2467, 2468, 2469, 2470, 2471, 2472, 2473, 2474, 2475, 2476, 2477, 2478, 2479, 2480, 2481, 2482, 2488, 2489, 2494, 2495, 2499, 2500, 2503, 2504, 2506, 2507, 2508, 2509, 2510, 2511, 2512, 2513, 2514, 2515, 2516, 2517, 2518, 2519, 2520, 2527, 2528, 2529, 2530, 2537, 2538, 2545, 2546, 2547, 2554, 2555, 2561, 2562, 2567, 2568, 2572, 2573, 2576, 2577, 2579, 2580, 2581, 2582, 2583, 2584, 2585, 2586, 2587, 2588, 2589, 2590, 2591, 2592, 2593, 2594, 2601, 2602, 2608, 2609, 2614, 2615, 2619, 2620, 2623, 2624, 2626, 2627, 2628, 2629, 2630, 2631, 2632, 2633, 2634, 2635, 2636, 2637, 2638, 2639, 2640, 2641, 2642]
# no rup in opb
c3 = [2, 3, 4, 6, 10, 12, 14, 18, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 267, 268, 269, 270, 271, 297, 298, 299, 300, 307, 308, 312, 313, 314, 315, 316, 317, 318, 319, 320, 321, 327, 328, 329, 330, 331, 337, 338, 339, 340, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 362, 363, 364, 365, 392, 393, 394, 395, 396, 402, 403, 404, 405, 406, 417, 418, 419, 420, 427, 428, 429, 430, 431, 442, 443, 444, 445, 446, 457, 458, 459, 460, 462, 463, 464, 465, 466, 467, 468, 487, 488, 489, 490, 492, 493, 494, 495, 496, 502, 503, 504, 505, 512, 513, 514, 515, 517, 518, 519, 520, 522, 523, 524, 525, 532, 533, 534, 535, 537, 538, 539, 540, 547, 548, 549, 550, 551, 552, 553, 554, 555, 567, 568, 569, 570, 572, 573, 574, 575, 577, 578, 579, 580, 581, 597, 598, 599, 600, 601, 607, 608, 609, 610, 612, 613, 614, 615, 616, 622, 623, 624, 625, 626, 632, 633, 634, 635, 636, 652, 653, 654, 655, 656, 657, 658, 659, 660, 662, 663, 664, 665, 672, 673, 674, 675, 676, 677, 678, 707, 757, 758, 759, 760, 767, 768, 769, 770, 771, 772, 773, 774, 775, 777, 782, 783, 784, 785, 786, 787, 792, 793, 794, 795, 822, 823, 827, 828, 829, 830, 831, 832, 833, 834, 835, 836, 852, 853, 854, 855, 856, 872, 873, 874, 875, 876, 907, 908, 912, 913, 914, 915, 917, 918, 919, 920, 922, 923, 924, 925, 927, 928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 957, 958, 959, 960, 961, 962, 963, 964, 965, 967, 968, 969, 970, 972, 973, 974, 975, 977, 978, 979, 980, 987, 988, 989, 990, 991, 992, 993, 994, 995, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1017, 1018, 1019, 1020, 1021, 1042, 1043, 1044, 1045, 1047, 1048, 1049, 1050, 1072, 1073, 1074, 1075, 1082, 1083, 1084, 1085, 1087, 1088, 1089, 1090, 1092, 1093, 1094, 1095, 1097, 1098, 1099, 1100, 1101, 1102, 1112, 1113, 1114, 1115, 1116, 1117, 1118, 1119, 1120, 1122, 1123, 1124, 1125, 1132, 1133, 1134, 1135, 1147, 1148, 1149, 1150, 1151, 1152, 1153, 1154, 1155, 1162, 1163, 1164, 1165, 1166, 1172, 1173, 1174, 1175, 1177, 1178, 1179, 1180, 1182, 1183, 1184, 1185, 1197, 1198, 1199, 1200, 1201, 1202, 1203, 1204, 1205, 1212, 1213, 1214, 1215, 1216, 1217, 1218, 1219, 1220, 1221, 1257, 1258, 1259, 1260, 1267, 1268, 1269, 1270, 1271, 1272, 1273, 1274, 1275, 1276, 1307, 1308, 1309, 1310, 1311, 1312, 1313, 1314, 1315, 1322, 1323, 1324, 1325, 1359, 1367, 1368, 1376, 1383, 1384, 1385, 1393, 1401, 1417, 1418, 1419, 1427, 1435, 1436, 1443, 1444, 1452, 1453, 1461, 1469, 1470, 1477, 1478, 1485, 1486, 1487, 1495, 1503, 1504, 1512, 1520, 1521, 1522, 1538, 1539, 1546, 1574, 1580, 1585, 1600, 1612, 1618, 1621, 1625, 1633, 1634, 1642, 1650, 1651, 1659, 1697, 1698, 1706, 1744, 1745, 1746, 1754, 1762, 1763, 1771, 1784, 1807, 1808, 1810, 1818, 1824, 1825, 1836, 1845, 1848, 1849, 1853, 1854, 1856, 1857, 1858, 1866, 1875, 1883, 1921, 1922, 1930, 1937, 1943, 1965, 1966, 1969, 1970, 1987, 2033, 2034, 2081, 2082, 2154, 2161, 2176, 2188, 2189, 2190, 2191, 2193, 2201, 2210, 2211, 2219, 2257, 2258, 2265, 2273, 2279, 2284, 2288, 2301, 2303, 2304, 2305, 2323, 2370, 2416, 2417, 2418, 2426, 2434, 2435, 2443, 2450, 2456, 2479, 2482, 2537, 2538, 2546, 2547, 2555, 2594, 2602, 2609, 2640, 2641, 2642]
v = [1358,1366,1375,1383,1392,1400,1409,1417,1426,1434,1443,1451,1460,1468,1477,1485,1494,1502,1511,1519,1529,1537,1546,1553,1559,1564,1568,1571,1573,1575,1577,1593,1600,1606,1611,1615,1618,1620,1622,1624,1641,1649,1658,1665,1671,1676,1680,1683,1685,1687,1689,1705,1712,1718,1723,1727,1730,1732,1734,1736,1753,1761,1770,1777,1783,1788,1792,1795,1797,1799,1801,1817,1824,1830,1835,1839,1842,1844,1846,1848,1865,1873,1882,1889,1895,1900,1904,1907,1909,1911,1913,1929,1936,1942,1947,1951,1954,1956,1958,1960,1977,1985,1994,2001,2007,2012,2016,2019,2021,2023,2025,2041,2048,2054,2059,2063,2066,2068,2070,2072,2089,2097,2106,2113,2119,2124,2128,2131,2133,2135,2137,2153,2160,2166,2171,2175,2178,2180,2182,2184,2201,2209,2218,2225,2231,2236,2240,2243,2245,2247,2249,2265,2272,2278,2283,2287,2290,2292,2294,2296,2313,2321,2330,2337,2343,2348,2352,2355,2357,2359,2361,2377,2384,2390,2395,2399,2402,2404,2406,2408,2425,2433,2442,2449,2455,2460,2464,2467,2469,2471,2473,2488,2494,2499,2503,2506,2508,2510,2512,2527,2537,2545,2554,2561,2567,2572,2576,2579,2581,2583,2585,2601,2608,2614,2619,2623,2626,2628,2630,2632]
for vv in v
    println(vv," ",vv in c2)
end

function smolproof2(system,invsys,systemlink,nbopb)
    isassi,assi = initassignement(invsys)
    front = getfront(system,invsys,isassi,assi,nbopb) #println("front:",findall(front))
    cone = copy(front)
    cone[end] = true
    antecedants = Set(Int[])
    while true in front
        id = findlast(front)
        front[id] = false
        if id>nbopb
            if isassigned(systemlink,id)
                antecedants=systemlink[id]
            else
                isassi .= false
                assi .= false
                antecedants = findall(revunitpropag(system,invsys,id,isassi,assi))
            end
            for i in antecedants
                if !cone[i]
                    cone[i]=true
                    front[i]=true
                end
            end
        end
    end
    cone[end] = true
    return cone
end

function getfront(system,invsys,isassi,assi,nbopb)
    n = length(system)
    antecedants = zeros(Bool,n)
    front = zeros(Bool,n)
    isassif,assif = initassignement(invsys)
    for i in eachindex(system)
        eq = system[i]
        s = slack(eq,isassif,assif)
        if s<0 println("solocontradiction ") end
        for l in eq.t 
            if l.coef > s
                printeq(eq)
                reset([front,antecedants,isassi,assi])
                x,v = l.var.x+1,l.var.v+1
                assi[x,v] = l.sign
                isassi[x,v] = true 
                front[i] = antecedants[i] = true
                for j in invsys[l.var]          
                    if j!=i
                        front[j] = true
                    end 
                end
                if unitpropag(front,antecedants,system,invsys,isassi,assi)
                    println(sum(antecedants))
                end
            end
        end
    end
    reset([antecedants])
    updumb(system,invsys,antecedants)
    return antecedants
end
function revunitpropag(system,invsys,init,isassi,assi) 
    n = length(system)
    front = zeros(Bool,n)
    front[init] = true
    antecedants = zeros(Bool,n)
    id = init
    eq = system[init]
    s = 0
    while true in front
        id = findlast(front)
        front[id] = false
        eq = id==init ? reverse(system[id]) : system[id]
        s = slack(eq,isassi,assi)
        if s<0
            antecedants[id] = true
            return antecedants
        else
            for l in eq.t
                if !isassi[l.var.x+1,l.var.v+1] && l.coef > s
                    isassi[l.var.x+1,l.var.v+1] = true
                    assi[l.var.x+1,l.var.v+1] = l.sign
                    antecedants[id] = true
                    for j in invsys[l.var]
                        if j!=id
                            front[j] = true
                        end
                    end
                end
            end
        end
    end
    println("\nRUP Failed from:",init)
    # println(findall(antecedants))
    return antecedants
end
function findassigned(front,antecedants,system,invsys,isassi,assi)
    for i in eachindex(system)
        eq = system[i]
        if length(eq.t)==1
            s = slack(eq,isassi,assi)
            if s>=0
                l = eq.t[1]
                if l.coef > s
                    x,v = l.var.x+1,l.var.v+1
                    assi[x,v] = l.sign
                    isassi[x,v] = true 
                    front[i] = antecedants[i] = true
                    for j in invsys[l.var]          
                        if j!=i
                            front[j] = true
                        end 
                    end
                end
            else
                println("contradicting litteral")
            end
        end
    end
end

function smolproof3(system,invsys,systemlink,nbopb)
    isassi,assi = initassignement(invsys)
    cone = zeros(Bool,length(system))
    cone[end] = true
    antecedants = zeros(Bool,length(system))
    front = zeros(Bool,length(system))
    updumb(system,invsys,front)
    while true in front
        id = findlast(front)
        front[id] = false
        if id>nbopb
            if isassigned(systemlink,id)
                for i in systemlink[id]
                    antecedants[i] = true
                end
            else
                rupdumb(system,invsys,antecedants,id,isassi,assi)
            end
            for i in findall(antecedants)
                if !cone[i]
                    cone[i]=true
                    front[i]=true
                end
            end
            
        end
    end
    cone[end] = true
    return cone
end
# system : array of equations
# invsys : dictonary mapping each variable to all the eqation indexesit is in
# init : first equation to propagate
# isassi : record of assigned variables
# assi : value of assignements
# nbopb : number of opb equations
function unitpropag(front,antecedants,system,invsys,isassi,assi)
    id = s = x = v = 0
    eq = system[end]
    while true in front
        id = findlast(front)
        front[id] = false
        eq = system[id]
        s = slack(eq,isassi,assi)
        if s<0                                      # contradiction
            antecedants[id] = true
            return true
        else
            for l in eq.t
                x,v = l.var.x+1,l.var.v+1
                if !isassi[x,v] && l.coef > s       # assign variable
                    isassi[x,v] = true
                    assi[x,v] = l.sign
                    antecedants[id] = true
                    for j in invsys[l.var]          # add impacted equations in front
                        if j!=id
                            front[j] = true
                        end end end end end 
    end
    println("\nUP Failed")
    return false
end


# using Profile
# using ProfileView
# ProfileView.@profile main()
# ProfileView.view()

#= 
g2-g3
        97 %    (7/230)
        99 %    (16/2301)
g2-g5
        98 %    (5/251)
        99 %    (31/2392)
g3-g6
        59 %    (249/609)
        92 %    (453/5952)
g4-g10
        80 %    (762/3751)
        1 %    (161/162)
g4-g14
        23 %    (3507/4570)
        0 %    (757/758)
g4-g33
        52 %    (4466/9211)
        0 %    (971/972)
g5-g6
        9 %    (731/801)
        86 %    (3459/25289)
g7-g11
        90 %    (864/8482)
        1 %    (165/166)



    sid = [1410,438,592,157,159,590,62,891,124,393]
==========================
threads available:10
g2-g3:1151/2531
g2-g5:1210/2643
g4-g14:4384/5328
g3-g6:5292/6561
g4-g10:3731/3913
g8-g9:4318/5407
g5-g6:16027/26090
g10-g25:5356/14535
g4-g33:10061/10183
g7-g28:14912/20291
g10-g14:7771/9430
g7-g15:8899/10912
g7-g11:8622/8648
g11-g13:9714/12357
g11-g28:17590/24059
g17-g25:7392/19381
g7-g23:16385/16653
 . . . 
 
==========================
g2-g3:
  0.015955 seconds (7.45 k allocations: 1.010 MiB)
  0.112484 seconds (200.47 k allocations: 23.322 MiB, 72.17% compilation time)
  0.574211 seconds (12.24 k allocations: 17.901 MiB)
1151/2531
g2-g5:
  0.012458 seconds (8.87 k allocations: 1.188 MiB)
  0.154311 seconds (178.67 k allocations: 31.551 MiB, 42.84% gc time)
  0.944702 seconds (13.41 k allocations: 19.213 MiB)
1210/2643
g3-g6:
  0.016844 seconds (20.48 k allocations: 2.673 MiB)
  0.059255 seconds (373.56 k allocations: 42.712 MiB, 5.60% gc time)
  3.866249 seconds (25.90 k allocations: 107.933 MiB, 0.28% gc time)
5292/6561
g4-g10:
  0.027052 seconds (127.54 k allocations: 16.919 MiB)
  0.020573 seconds (15.10 k allocations: 2.313 MiB)
  3.109376 seconds (148.18 k allocations: 564.057 MiB, 1.27% gc time)
3731/3913
g4-g14:
  0.044422 seconds (164.60 k allocations: 20.567 MiB)
  0.052560 seconds (64.25 k allocations: 9.464 MiB, 8.88% gc time)
  3.697321 seconds (142.81 k allocations: 372.954 MiB, 0.67% gc time)
4384/5328
g4-g33:
  0.095689 seconds (405.20 k allocations: 53.279 MiB, 4.81% gc time)
  0.050947 seconds (108.16 k allocations: 21.007 MiB, 11.53% gc time)
 61.463491 seconds (400.45 k allocations: 1.452 GiB, 0.13% gc time)
10061/10183
g5-g6:
  0.027208 seconds (26.59 k allocations: 3.473 MiB)
  0.355994 seconds (1.52 M allocations: 185.857 MiB, 42.89% gc time)
 14.876507 seconds (35.09 k allocations: 511.352 MiB, 1.04% gc time)
16027/26090
g7-g11:
  0.096185 seconds (353.21 k allocations: 46.271 MiB, 3.97% gc time)
  0.022820 seconds (19.47 k allocations: 4.870 MiB)
 59.304870 seconds (419.86 k allocations: 1.884 GiB, 0.14% gc time)
8622/8648
g7-g15:
  0.060827 seconds (437.18 k allocations: 57.182 MiB, 8.27% gc time)
  0.037761 seconds (79.31 k allocations: 15.907 MiB, 14.69% gc time)
 73.420885 seconds (394.00 k allocations: 1.535 GiB, 0.08% gc time)
8899/10912
g7-g23:
  0.093485 seconds (783.34 k allocations: 102.533 MiB, 9.16% gc time)
  0.050182 seconds (230.07 k allocations: 63.655 MiB, 14.89% gc time)
227.013073 seconds (705.20 k allocations: 5.889 GiB, 0.09% gc time)
16385/16653
g7-g28:
  0.067647 seconds (460.64 k allocations: 54.505 MiB, 4.65% gc time)
  0.026563 seconds (58.88 k allocations: 8.102 MiB)
 58.600608 seconds (637.56 k allocations: 5.279 GiB, 0.58% gc time)
14912/20291
g7-g33:
  0.102984 seconds (895.87 k allocations: 117.412 MiB, 8.72% gc time)
  0.018334 seconds (73.04 k allocations: 19.104 MiB)
887.864739 seconds (1.09 M allocations: 14.379 GiB, 0.04% gc time)
20931/20937
g8-g9:
  0.037838 seconds (156.49 k allocations: 19.754 MiB, 6.14% gc time)
  0.021842 seconds (33.77 k allocations: 4.363 MiB)
 10.019443 seconds (165.15 k allocations: 542.267 MiB, 0.20% gc time)
4318/5407
g10-g14:
  0.096011 seconds (313.64 k allocations: 39.333 MiB, 2.25% gc time)
  0.048104 seconds (66.76 k allocations: 12.383 MiB)
 75.430113 seconds (307.45 k allocations: 1.119 GiB, 0.27% gc time)
7771/9430
g10-g25:
  0.060173 seconds (385.80 k allocations: 46.176 MiB, 3.50% gc time)
  0.035077 seconds (96.54 k allocations: 11.414 MiB, 9.32% gc time)
 26.100259 seconds (238.26 k allocations: 855.204 MiB, 0.13% gc time)
5356/14535
g11-g13:
  0.074360 seconds (465.87 k allocations: 59.605 MiB, 9.29% gc time)
  0.027814 seconds (73.98 k allocations: 15.350 MiB)




veripb --trace --useColor test.opb test.pbp
restart RELP  alt j alt r
union ∪
intersect ∩
setdiff
symdiff rend les elements uniques
issubset ⊆⊇
i belive it matters




=#
