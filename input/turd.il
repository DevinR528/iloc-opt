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
    loadI 10 => %vr1
.L1: nop
    add %vr2, %vr3 => %vr69
    cbr_GE %vr2, %vr3 -> .L6
.L2: nop
    cbr_GE %vr2, %vr3 -> .L4
.L3: nop
    loadI 1 => %vr3
    jumpI -> .L5
.L4: nop
    loadI 3 => %vr3
.L5: nop
    loadI 2 => %vr2
.L6: nop
    addI %vr3, 2 => %vr3
.L7: nop
    iwrite %vr3
    iwrite %vr2
    ret
