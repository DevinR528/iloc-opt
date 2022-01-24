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
.frame main, 3960 
    loadI 30 => %vr8
    i2i %vr8 => %vr5
    i2i %vr5 => %vr4
    loadI 1 => %vr9
    i2i %vr9 => %vr6
    cbr_GT %vr6, %vr5 -> .L0
.L1: nop
    subI %vr6, 1 => %vr12
    mult %vr6, %vr5 => %vr13
    addI %vr13, 1 => %vr14
    i2i %vr0 => %vr15
    addI %vr15, -244 => %vr17
    subI %vr14, 1 => %vr18
    multI %vr18, 4 => %vr20
    sub %vr17, %vr20 => %vr21
    store %vr12 => %vr21
    addI %vr15, -124 => %vr23
    multI %vr12, 4 => %vr24
    sub %vr23, %vr24 => %vr25
    store %vr6 => %vr25
    addI %vr6, 1 => %vr26
    i2i %vr26 => %vr6
    cbr_LE %vr6, %vr5 -> .L1
.L0: nop
    loadI 1 => %vr9
    i2i %vr9 => %vr7
    cbr_GT %vr7, %vr4 -> .L2
.L3: nop
    subI %vr7, 1 => %vr29
    i2i %vr5 => %vr30
    add %vr30, %vr7 => %vr31
    i2i %vr0 => %vr15
    addI %vr15, -244 => %vr17
    subI %vr31, 1 => %vr32
    multI %vr32, 4 => %vr33
    sub %vr17, %vr33 => %vr34
    store %vr29 => %vr34
    multI %vr7, 2 => %vr36
    addI %vr15, -124 => %vr23
    multI %vr29, 4 => %vr37
    sub %vr23, %vr37 => %vr38
    store %vr36 => %vr38
    addI %vr7, 1 => %vr39
    i2i %vr39 => %vr7
    cbr_LE %vr7, %vr4 -> .L3
.L2: nop
    loadI 2 => %vr35
    i2i %vr35 => %vr6
    cbr_GT %vr6, %vr5 -> .L4
.L5: nop
    loadI 2 => %vr35
    i2i %vr35 => %vr7
    cbr_GT %vr7, %vr4 -> .L6
.L7: nop
    subI %vr6, 1 => %vr12
    mult %vr12, %vr5 => %vr40
    subI %vr7, 1 => %vr29
    add %vr40, %vr29 => %vr41
    i2i %vr0 => %vr15
    addI %vr15, -244 => %vr17
    subI %vr41, 1 => %vr42
    multI %vr42, 4 => %vr43
    sub %vr17, %vr43 => %vr44
    load %vr44 => %vr45
    mult %vr6, %vr5 => %vr13
    add %vr13, %vr7 => %vr46
    subI %vr46, 1 => %vr47
    multI %vr47, 4 => %vr48
    sub %vr17, %vr48 => %vr49
    store %vr45 => %vr49
    addI %vr15, -124 => %vr23
    multI %vr12, 4 => %vr24
    sub %vr23, %vr24 => %vr25
    load %vr25 => %vr50
    addI %vr15, -4 => %vr52
    multI %vr29, 4 => %vr37
    sub %vr52, %vr37 => %vr53
    load %vr53 => %vr54
    cbr_EQ %vr50, %vr54 -> .L8
    load %vr49 => %vr57
    addI %vr57, 1 => %vr58
    store %vr58 => %vr49
.L8: nop
    subI %vr6, 1 => %vr12
    mult %vr12, %vr5 => %vr40
    add %vr40, %vr7 => %vr59
    i2i %vr0 => %vr15
    addI %vr15, -244 => %vr17
    subI %vr59, 1 => %vr60
    multI %vr60, 4 => %vr61
    sub %vr17, %vr61 => %vr62
    load %vr62 => %vr63
    mult %vr6, %vr5 => %vr13
    add %vr13, %vr7 => %vr46
    subI %vr46, 1 => %vr47
    multI %vr47, 4 => %vr48
    sub %vr17, %vr48 => %vr49
    load %vr49 => %vr57
    cbr_GE %vr63, %vr57 -> .L9
    addI %vr63, 1 => %vr66
    store %vr66 => %vr49
.L9: nop
    mult %vr6, %vr5 => %vr13
    subI %vr7, 1 => %vr29
    add %vr13, %vr29 => %vr67
    i2i %vr0 => %vr15
    addI %vr15, -244 => %vr17
    subI %vr67, 1 => %vr68
    multI %vr68, 4 => %vr69
    sub %vr17, %vr69 => %vr70
    load %vr70 => %vr71
    add %vr13, %vr7 => %vr46
    subI %vr46, 1 => %vr47
    multI %vr47, 4 => %vr48
    sub %vr17, %vr48 => %vr49
    load %vr49 => %vr57
    cbr_GE %vr71, %vr57 -> .L10
    addI %vr71, 1 => %vr74
    store %vr74 => %vr49
.L10: nop
    addI %vr7, 1 => %vr39
    i2i %vr39 => %vr7
    cbr_LE %vr7, %vr4 -> .L7
.L6: nop
    addI %vr6, 1 => %vr26
    i2i %vr26 => %vr6
    cbr_LE %vr6, %vr5 -> .L5
.L4: nop
    mult %vr5, %vr5 => %vr75
    add %vr75, %vr4 => %vr76
    i2i %vr0 => %vr15
    addI %vr15, -244 => %vr17
    subI %vr76, 1 => %vr77
    multI %vr77, 4 => %vr78
    sub %vr17, %vr78 => %vr79
    load %vr79 => %vr80
    iwrite %vr80
    ret
