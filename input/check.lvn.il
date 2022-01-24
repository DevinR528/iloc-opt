    .data
    .string .int_wformat, "%d\12"
    .string .float_wformat, "%f\12"
    .string .char_wformat, "%c\12"
    .string .string_wformat, "%s\12"
    .string .int_rformat, "%d"
    .string .float_rformat, "%f"
    .string .char_rformat, "%c"
    .string .string_rformat, "%s"
    .string .string_const_0, "SUCCESS"
    .text
.frame main, 0 
    loadI 1 => %vr6
    i2i %vr6 => %vr4
    loadI 10 => %vr7
    cbr_GT %vr4, %vr7 -> .L0
.L1: nop
    loadI 0 => %vr10
    cbr_GE %vr4, %vr10 -> .L2
    loadI 10 => %vr7
    mod %vr7, %vr10 => %vr13
    i2i %vr13 => %vr5
.L2: nop
    addI %vr4, 1 => %vr14
    i2i %vr14 => %vr4
    loadI 10 => %vr7
    cbr_LE %vr4, %vr7 -> .L1
.L0: nop
    loadI .string_const_0 => %vr15
    swrite %vr15
    ret
