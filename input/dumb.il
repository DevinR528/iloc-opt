    .data
    .global main_fp, 4, 4
    .text
.frame main, 8
.L0: nop
    loadI 1 =>  %vr1
    addI %vr1, 0 => %vr4
.L1: nop
    iwrite %vr4
    loadI main_fp => %vr10
    cbr %vr2 -> .L5
.L2: nop
    iwrite %vr4
    loadI main_fp  => %vr10
    cbr %vr2 -> .L3
.L3: nop
    iwrite %vr4
    loadI main_fp => %vr10
    cbr %vr2 -> .L1
.L4: nop
    iwrite %vr4
    loadI main_fp => %vr10
    ret
.L5: nop
    iwrite %vr4
    loadI main_fp => %vr10
    cbr %vr23 -> .L8
.L6: nop
    iwrite %vr4
    loadI main_fp => %vr10
.L7: nop
    iwrite %vr4
    loadI main_fp => %vr10
    jumpI -> .L3
.L8: nop
    iwrite %vr4
    loadI main_fp => %vr10
    jumpI -> .L7
