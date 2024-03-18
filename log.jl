==========================
==========================
abs_test : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.073804 seconds (1.39 k allocations: 60.062 KiB, 30.34% compilation time)

 !opb !opb size 12 1
  0.233071 seconds (527.66 k allocations: 33.580 MiB, 3.07% gc time, 99.99% compilation time)
abs_test
        92 %    (1/12)
        0 %    (1/1)
abs_test (smol) : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.043440 seconds (82 allocations: 3.750 KiB)
==========================

==========================
arithmetic_test : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.045767 seconds (82 allocations: 3.773 KiB)

 !opb size 6 1
  0.000003 seconds (5 allocations: 320 bytes)
arithmetic_test
        83 %    (1/6)
        0 %    (1/1)
arithmetic_test (smol) : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.037512 seconds (82 allocations: 3.797 KiB)
==========================

==========================
at_most_1_test : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.038862 seconds (82 allocations: 3.766 KiB)

 size 102 6
 init contradiction: 32[1, 3, 4, 5, 7, 8, 11, 12, 13, 14, 15, 16, 65, 68, 72, 73, 74, 75, 78, 81, 82, 83, 86, 89, 90, 91, 94, 97, 98, 99, 100, 101]
  0.042395 seconds (57.85 k allocations: 4.031 MiB, 99.33% compilation time)
at_most_1_test
        69 %    (32/102)
        83 %    (1/6)
at_most_1_test (smol) : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.036044 seconds (82 allocations: 3.789 KiB)
==========================

==========================
comparison_test : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.042061 seconds (82 allocations: 3.773 KiB)

 !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA size 7 174
 init contradiction: 11[8, 12, 79, 84, 105, 110, 131, 136, 157, 159, 180]
  0.000900 seconds (844 allocations: 44.922 KiB)
comparison_test
        43 %    (4/7)
        2 %    (170/174)
comparison_test (smol) : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.040548 seconds (82 allocations: 3.797 KiB)
==========================

==========================
count_test : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.035313 seconds (82 allocations: 3.742 KiB)

 size 22 2
 init contradiction: 3[1, 21, 23]
  0.000048 seconds (45 allocations: 1.938 KiB)
count_test
        91 %    (2/22)
        0 %    (2/2)
count_test (smol) : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.036884 seconds (82 allocations: 3.766 KiB)
==========================

==========================
element_test : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.036208 seconds (82 allocations: 3.766 KiB)

 !opb size 9 1
  0.000003 seconds (5 allocations: 320 bytes)
element_test
        89 %    (1/9)
        0 %    (1/1)
element_test (smol) : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.038735 seconds (82 allocations: 3.781 KiB)
==========================

==========================
equals_test : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.037940 seconds (82 allocations: 3.750 KiB)

 !FA !FA !FA !FA !FA !FA !FA !FA size 7 78
 init contradiction: 6[4, 6, 12, 65, 67, 84]
  0.000193 seconds (376 allocations: 20.055 KiB)
equals_test
        29 %    (5/7)
        3 %    (76/78)
equals_test (smol) : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.038451 seconds (82 allocations: 3.773 KiB)
==========================

==========================
knapsack_test : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.042837 seconds (82 allocations: 3.766 KiB)

 !FA !FA size 13 272
 init contradiction: 29[9, 11, 13, 15, 19, 23, 44, 48, 52, 79, 83, 95, 106, 111, 122, 129, 133, 137, 158, 162, 166, 252, 257, 263, 269, 278, 280, 282, 284]
  0.000683 seconds (608 allocations: 408.891 KiB)
 POL IDS ARE WRONG  POL IDS ARE WRONG  POL IDS ARE WRONG  POL IDS ARE WRONG  POL IDS ARE WRONG  POL IDS ARE WRONG  POL IDS ARE WRONG knapsack_test
        54 %    (6/13)
        66 %    (92/272)
knapsack_test (smol) : Running VeriPB version 2.0.0.post221+git.487290
ERROR:root:/home/arthur_gla/veriPB/trim/smol-proofs2/Instances//smol.knapsack_test.veripb:?:1: Stack should contain exactly one element at end of polish notation.
catch (u cant see me)
==========================

==========================
lex_test : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.038473 seconds (82 allocations: 3.734 KiB)

 size 85 11
 init contradiction: 28[1, 3, 4, 5, 7, 8, 11, 12, 13, 15, 16, 17, 19, 20, 21, 22, 24, 25, 26, 27, 28, 30, 31, 32, 33, 84, 86, 90]
  0.000148 seconds (197 allocations: 6.883 KiB)
lex_test
        69 %    (26/85)
        73 %    (3/11)
lex_test (smol) : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.035882 seconds (82 allocations: 3.750 KiB)
==========================

==========================
linear_equality_test : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.039757 seconds (82 allocations: 3.812 KiB)

 !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA size 9 115
 init contradiction: 11[1, 2, 4, 13, 18, 22, 78, 83, 102, 104, 123]
  0.000368 seconds (559 allocations: 29.359 KiB)
linear_equality_test
        44 %    (5/9)
        4 %    (110/115)
linear_equality_test (smol) : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.039995 seconds (82 allocations: 3.828 KiB)
==========================

==========================
logical_test : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.036858 seconds (82 allocations: 3.766 KiB)

 size 7 22
 init contradiction: 5[6, 19, 24, 25, 26]
  0.000032 seconds (100 allocations: 4.422 KiB)
logical_test
        71 %    (2/7)
        45 %    (12/22)
logical_test (smol) : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.035728 seconds (82 allocations: 3.781 KiB)
==========================

==========================
min_max_test : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.266594 seconds (82 allocations: 3.766 KiB)

 !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA !FA size 73 4428
 init contradiction: 12[2, 10, 16, 21, 23, 34, 43, 49, 55, 74, 2335, 4500]
  2.231330 seconds (33.70 k allocations: 21.845 MiB, 0.26% gc time)
min_max_test
        42 %    (42/73)
        0 %    (4427/4428)
min_max_test (smol) : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.330394 seconds (82 allocations: 3.781 KiB)
==========================

==========================
n_value_test : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.035418 seconds (82 allocations: 3.766 KiB)

 size 129 1
 init contradiction: 4[2, 6, 7, 129]
  0.000025 seconds (44 allocations: 2.023 KiB)
n_value_test
        97 %    (4/129)
        0 %    (1/1)
n_value_test (smol) : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.039616 seconds (82 allocations: 3.781 KiB)
==========================

==========================
regular_3_vars : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.037628 seconds (82 allocations: 3.766 KiB)

 size 67 56
 init contradiction: 13[7, 12, 13, 15, 16, 37, 43, 46, 71, 74, 75, 108, 122]
  0.000221 seconds (341 allocations: 15.594 KiB)
regular_3_vars
        24 %    (51/67)
        34 %    (37/56)
regular_3_vars (smol) : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.036318 seconds (82 allocations: 3.789 KiB)
==========================

==========================
regular_4_vars : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.078477 seconds (82 allocations: 3.766 KiB)

 size 244 2871
 init contradiction: 26[9, 19, 24, 30, 36, 39, 249, 255, 261, 267, 273, 279, 285, 302, 318, 359, 405, 431, 432, 433, 434, 445, 1010, 2010, 2562, 3114]
  0.029106 seconds (5.35 k allocations: 2.691 MiB)
regular_4_vars
        34 %    (162/244)
        81 %    (555/2871)
regular_4_vars (smol) : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.057077 seconds (82 allocations: 3.789 KiB)
==========================

==========================
regular_5_vars : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  3.239234 seconds (82 allocations: 3.766 KiB)

 size 629 256924
 init contradiction: 40[11, 23, 28, 34, 40, 46, 49, 635, 642, 649, 656, 663, 670, 677, 684, 691, 698, 705, 712, 719, 726, 733, 740, 766, 791, 816, 841, 866, 891, 916, 941, 1014, 1087, 1147, 1148, 50389, 99618, 147078, 202634, 257552]
133.376335 seconds (182.61 k allocations: 548.747 MiB, 0.22% gc time)
regular_5_vars
        36 %    (400/629)
        94 %    (15541/256924)
regular_5_vars (smol) : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.645531 seconds (82 allocations: 3.789 KiB)
==========================

==========================
smart_table_3 : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.057140 seconds (82 allocations: 3.766 KiB)

 !FA !FA !FA !FA size 55 206
 init contradiction: 13[7, 11, 17, 22, 27, 29, 54, 56, 58, 125, 170, 215, 260]
  0.003498 seconds (1.41 k allocations: 915.641 KiB)
smart_table_3
        18 %    (45/55)
        1 %    (204/206)
smart_table_3 (smol) : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.051582 seconds (82 allocations: 3.781 KiB)
==========================

==========================
smart_table_4 : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.044785 seconds (82 allocations: 3.766 KiB)

 size 133 67
 init contradiction: 42[9, 10, 13, 18, 28, 31, 33, 38, 41, 46, 51, 54, 56, 63, 65, 70, 75, 98, 103, 108, 118, 123, 125, 132, 136, 139, 142, 145, 148, 151, 154, 157, 160, 163, 166, 169, 172, 175, 178, 181, 190, 199]
  0.001022 seconds (466 allocations: 20.336 KiB)
smart_table_4
        22 %    (104/133)
        48 %    (35/67)
smart_table_4 (smol) : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.042451 seconds (82 allocations: 3.781 KiB)
==========================

==========================
smart_table_5 : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.111400 seconds (82 allocations: 3.766 KiB)

 size 215 3555
 init contradiction: 18[26, 32, 37, 42, 47, 52, 54, 57, 176, 214, 226, 230, 242, 3290, 3326, 3522, 3640, 3769]
  0.225842 seconds (14.81 k allocations: 7.466 MiB)
smart_table_5
        6 %    (203/215)
        58 %    (1510/3555)
smart_table_5 (smol) : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.090599 seconds (82 allocations: 3.781 KiB)
==========================

==========================
solve_test : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.044146 seconds (82 allocations: 3.742 KiB)

 size 3 2
 init contradiction: 1[3]
  0.000027 seconds (26 allocations: 944 bytes)
solve_test
        67 %    (1/3)
        50 %    (1/2)
solve_test (smol) : Running VeriPB version 2.0.0.post221+git.487290
Verification succeeded.
  0.043252 seconds (82 allocations: 3.766 KiB)
==========================

