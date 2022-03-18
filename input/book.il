    .data
    .string .int_wformat, "%d\12"
    .text
.frame main, 0
    loadI 10 => %vr1
.L1: nop
    add %vr2, %vr3 => %vr69
    cbr_GE %vr2, %vr3 -> .L5
.L2: nop
    loadI 1 => %vr3
.L3: nop
    loadI 1 => %vr3
    cbr_GE %vr2, %vr3 -> .L1
.L4: nop
    loadI 3 => %vr3
    ret
.L5: nop
    loadI 2 => %vr2
    cbr_GE %vr2, %vr3 -> .L8
.L6: nop
    addI %vr3, 2 => %vr3
    jumpI -> .L7
.L8: nop
    addI %vr3, 2 => %vr3
.L7: nop
    iwrite %vr3
    iwrite %vr2
    jumpI -> .L3
