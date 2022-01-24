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
.frame main, 40 
    loadI 1 => %vr5
    i2i %vr5 => %vr4
    loadI 10 => %vr6
    cbr_GT %vr4, %vr6 -> .L0
.L1: nop
    i2i %vr0 => %vr9
    addI %vr9, -4 => %vr11
    subI %vr4, 1 => %vr12
    multI %vr12, 4 => %vr14
    sub %vr11, %vr14 => %vr15
    store %vr4 => %vr15
    addI %vr4, 1 => %vr16
    i2i %vr16 => %vr4
    loadI 10 => %vr6
    cbr_LE %vr4, %vr6 -> .L1
.L0: nop
    loadI 1 => %vr5
    i2i %vr5 => %vr4
    loadI 10 => %vr6
    cbr_GT %vr4, %vr6 -> .L2
.L3: nop
    loadI 5 => %vr17
    cbr_GE %vr4, %vr17 -> .L4
    i2i %vr0 => %vr9
    addI %vr9, -4 => %vr11
    subI %vr4, 1 => %vr12
    multI %vr12, 4 => %vr14
    sub %vr11, %vr14 => %vr15
    load %vr15 => %vr20
    iwrite %vr20
    jumpI -> .L5
.L4: nop
    loadI 0 => %vr21
    iwrite %vr21
.L5: nop
    addI %vr4, 1 => %vr16
    i2i %vr16 => %vr4
    loadI 10 => %vr6
    cbr_LE %vr4, %vr6 -> .L3
.L2: nop
    ret
