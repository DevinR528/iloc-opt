    .data
    .string .int_wformat, "%d\12"
    .string .float_wformat, "%f\12"
    .string .char_wformat, "%c\12"
    .string .string_wformat, "%s\12"
    .string .int_rformat, "%d"
    .string .float_rformat, "%f"
    .string .char_rformat, "%c"
    .string .string_rformat, "%s"
    .text
.frame main, 60 
    loadI 32 => %vr8
    loadI 1 => %vr9
    i2i %vr0 => %vr10
    loadI -4 => %vr11
    add %vr10, %vr11 => %vr12
    loadI 0 => %vr13
    loadI 4 => %vr14
    loadI 0 => %vr15
    sub %vr12, %vr15 => %vr16
    store %vr8 => %vr16
    loadI 11 => %vr17
    loadI 2 => %vr18
    loadI 1 => %vr19
    loadI 4 => %vr20
    sub %vr12, %vr20 => %vr21
    store %vr17 => %vr21
    loadI 111 => %vr22
    loadI 3 => %vr23
    loadI 2 => %vr24
    loadI 8 => %vr25
    sub %vr12, %vr25 => %vr26
    store %vr22 => %vr26
    loadI 88 => %vr27
    loadI 3 => %vr28
    loadI 12 => %vr29
    sub %vr12, %vr29 => %vr30
    store %vr27 => %vr30
    loadI 5 => %vr31
    loadI 4 => %vr32
    loadI 16 => %vr33
    sub %vr12, %vr33 => %vr34
    store %vr17 => %vr34
    loadI 44 => %vr35
    loadI 6 => %vr36
    loadI 5 => %vr37
    loadI 20 => %vr38
    sub %vr12, %vr38 => %vr39
    store %vr35 => %vr39
    loadI 33 => %vr40
    loadI 7 => %vr41
    loadI 6 => %vr42
    loadI 24 => %vr43
    sub %vr12, %vr43 => %vr44
    store %vr40 => %vr44
    loadI 8 => %vr45
    loadI 7 => %vr46
    loadI 28 => %vr47
    sub %vr12, %vr47 => %vr48
    store %vr40 => %vr48
    loadI 22 => %vr49
    loadI 9 => %vr50
    loadI 8 => %vr51
    loadI 32 => %vr52
    sub %vr12, %vr52 => %vr53
    store %vr49 => %vr53
    loadI 77 => %vr54
    loadI 10 => %vr55
    loadI 9 => %vr56
    loadI 36 => %vr57
    sub %vr12, %vr57 => %vr58
    store %vr54 => %vr58
    loadI 45 => %vr59
    loadI 10 => %vr60
    loadI 40 => %vr61
    sub %vr12, %vr61 => %vr62
    store %vr59 => %vr62
    loadI 65 => %vr63
    loadI 12 => %vr64
    loadI 11 => %vr65
    loadI 44 => %vr66
    sub %vr12, %vr66 => %vr67
    store %vr63 => %vr67
    loadI 76 => %vr68
    loadI 13 => %vr69
    loadI 12 => %vr70
    loadI 48 => %vr71
    sub %vr12, %vr71 => %vr72
    store %vr68 => %vr72
    loadI 87 => %vr73
    loadI 14 => %vr74
    loadI 13 => %vr75
    loadI 52 => %vr76
    sub %vr12, %vr76 => %vr77
    store %vr73 => %vr77
    loadI 34 => %vr78
    loadI 15 => %vr79
    loadI 14 => %vr80
    loadI 56 => %vr81
    sub %vr12, %vr81 => %vr82
    store %vr78 => %vr82
    i2i %vr9 => %vr4
    comp %vr4, %vr74 => %vr83
    testgt %vr83 => %vr84
    cbr %vr84 -> .L0
.L1: nop
    i2i %vr4 => %vr7
    add %vr4, %vr9 => %vr85
    i2i %vr85 => %vr5
    comp %vr5, %vr79 => %vr86
    testgt %vr86 => %vr87
    cbr %vr87 -> .L2
.L3: nop
    i2i %vr0 => %vr10
    add %vr10, %vr11 => %vr12
    sub %vr5, %vr9 => %vr88
    mult %vr88, %vr14 => %vr89
    sub %vr12, %vr89 => %vr90
    load %vr90 => %vr91
    sub %vr7, %vr9 => %vr92
    mult %vr92, %vr14 => %vr93
    sub %vr12, %vr93 => %vr94
    load %vr94 => %vr95
    comp %vr91, %vr95 => %vr96
    testlt %vr96 => %vr97
    cbrne %vr97 -> .L4
    i2i %vr5 => %vr7
.L4: nop
    add %vr5, %vr9 => %vr98
    i2i %vr98 => %vr5
    comp %vr5, %vr79 => %vr86
    testle %vr86 => %vr87
    cbr %vr87 -> .L3
.L2: nop
    i2i %vr0 => %vr10
    add %vr10, %vr11 => %vr12
    sub %vr4, %vr9 => %vr99
    mult %vr99, %vr14 => %vr100
    sub %vr12, %vr100 => %vr101
    load %vr101 => %vr102
    i2i %vr102 => %vr6
    sub %vr7, %vr9 => %vr92
    mult %vr92, %vr14 => %vr93
    sub %vr12, %vr93 => %vr94
    load %vr94 => %vr95
    store %vr95 => %vr101
    store %vr6 => %vr94
    add %vr4, %vr9 => %vr85
    i2i %vr85 => %vr4
    comp %vr4, %vr74 => %vr83
    testle %vr83 => %vr84
    cbr %vr84 -> .L1
.L0: nop
    i2i %vr9 => %vr4
    comp %vr4, %vr79 => %vr103
    testgt %vr103 => %vr104
    cbr %vr104 -> .L5
.L6: nop
    i2i %vr0 => %vr10
    add %vr10, %vr11 => %vr12
    sub %vr4, %vr9 => %vr99
    mult %vr99, %vr14 => %vr100
    sub %vr12, %vr100 => %vr101
    load %vr101 => %vr102
    iwrite %vr102
    add %vr4, %vr9 => %vr85
    i2i %vr85 => %vr4
    comp %vr4, %vr79 => %vr103
    testle %vr103 => %vr104
    cbr %vr104 -> .L6
.L5: nop
    ret
