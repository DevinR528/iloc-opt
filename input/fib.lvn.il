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
.frame main, 0 
    loadI 1 => %vr8
    i2i %vr8 => %vr6
    loadI 0 => %vr9
    i2i %vr9 => %vr7
    i2i %vr7 => %vr5
    i2i %vr6 => %vr4
    loadI 20 => %vr10
    cbr_GT %vr4, %vr10 -> .L0
.L1: nop
    iwrite %vr5
    add %vr7, %vr6 => %vr13
    i2i %vr13 => %vr5
    i2i %vr7 => %vr6
    i2i %vr5 => %vr7
    addI %vr4, 1 => %vr14
    i2i %vr14 => %vr4
    loadI 20 => %vr10
    cbr_LE %vr4, %vr10 -> .L1
.L0: nop
    ret
