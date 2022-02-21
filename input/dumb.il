    .data
    .global main_fp, 4, 4
    .text
.frame main, 8
    loadI 0 =>  %vr2
    loadI 0 =>  %vr4
    loadI 0 =>  %vr3
    loadI 0 =>  %vr5
.L0: nop
    loadI 1 =>  %vr10
    i2i %vr10 => %vr1
.L1: nop
    loadI 2 => %vr2
    loadI 3 => %vr3
    cbr_GT %vr2, %vr3 -> .L5
.L2: nop
    loadI 5 => %vr4
    loadI 3 => %vr3
    loadI 10 => %vr5
    iwrite %vr5
    iwrite %vr4
.L3: nop
    add %vr2, %vr4 => %vr6
    add %vr3, %vr5 => %vr7
    addI %vr1, 1 => %vr1
    iwrite %vr1
    iwrite %vr6
    cbr_GT %vr1, %vr6 -> .L1
.L4: nop
    ret
.L5: nop
    loadI 2 => %vr2
    loadI 3 => %vr5
    cbr_GT %vr2, %vr5 -> .L8
.L6: nop
    loadI 4 => %vr5
.L7: nop
    loadI 4 => %vr4
    iwrite %vr4
    jumpI -> .L3
.L8: nop
    loadI 6 => %vr3
    iwrite %vr3
    jumpI -> .L7
