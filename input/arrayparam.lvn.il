    .data
    .string .int_wformat, "%d\12"
    .string .float_wformat, "%f\12"
    .string .char_wformat, "%c\12"
    .string .string_wformat, "%s\12"
    .string .int_rformat, "%d"
    .string .float_rformat, "%f"
    .string .char_rformat, "%c"
    .string .string_rformat, "%s"
    .float .float_const_0, 0.01
    .global main_fp, 4, 4
    .text
.frame main, 40 
    loadI main_fp => %vr4
    store %vr0 => %vr4
    addI %vr0, -4 => %vr6
    call init, %vr6
    addI %vr0, -4 => %vr6
    call writearray, %vr6
    loadI 1 => %vr7
    i2i %vr7 => %vr4
    loadI 10 => %vr8
    cbr_GT %vr4, %vr8 -> .L0
.L1: nop
    i2i %vr0 => %vr11
    addI %vr11, -4 => %vr12
    subI %vr4, 1 => %vr13
    multI %vr13, 4 => %vr15
    sub %vr12, %vr15 => %vr16
    load %vr16 => %vr17
    mult %vr17, %vr4 => %vr18
    store %vr18 => %vr16
    call inc, %vr16
    addI %vr4, 1 => %vr19
    i2i %vr19 => %vr4
    loadI 10 => %vr8
    cbr_LE %vr4, %vr8 -> .L1
.L0: nop
    addI %vr0, -4 => %vr6
    call writearray, %vr6
    ret
.frame init, 0, %vr8
    loadI 1 => %vr9
    i2i %vr9 => %vr4
    loadI 10 => %vr10
    i2i %vr10 => %vr5
    cbr_GT %vr4, %vr10 -> .L2
.L3: nop
    i2f %vr4 => %vr13
    loadI .float_const_0 => %vr14
    fload %vr14 => %vr15
    fmult %vr13, %vr15 => %vr16
    i2f %vr5 => %vr17
    fadd %vr16, %vr17 => %vr18
    f2i %vr18 => %vr19
    subI %vr4, 1 => %vr20
    multI %vr20, 4 => %vr22
    sub %vr8, %vr22 => %vr23
    store %vr19 => %vr23
    addI %vr4, 1 => %vr24
    i2i %vr24 => %vr4
    addI %vr5, 1 => %vr25
    i2i %vr25 => %vr5
    loadI 10 => %vr10
    cbr_LE %vr4, %vr10 -> .L3
.L2: nop
    ret
.frame writearray, 0, %vr4
    i2i %vr4 => %vr9
    load %vr9 => %vr10
    iwrite %vr10
    subI %vr4, 4 => %vr14
    load %vr14 => %vr15
    iwrite %vr15
    subI %vr4, 8 => %vr19
    load %vr19 => %vr20
    iwrite %vr20
    subI %vr4, 12 => %vr23
    load %vr23 => %vr24
    iwrite %vr24
    subI %vr4, 16 => %vr28
    load %vr28 => %vr29
    iwrite %vr29
    subI %vr4, 20 => %vr33
    load %vr33 => %vr34
    iwrite %vr34
    subI %vr4, 24 => %vr38
    load %vr38 => %vr39
    iwrite %vr39
    subI %vr4, 28 => %vr43
    load %vr43 => %vr44
    iwrite %vr44
    subI %vr4, 32 => %vr48
    load %vr48 => %vr49
    iwrite %vr49
    subI %vr4, 36 => %vr53
    load %vr53 => %vr54
    iwrite %vr54
    ret
.frame inc, 0, %vr4
    load %vr4 => %vr5
    addI %vr5, 1 => %vr7
    store %vr7 => %vr4
    ret
