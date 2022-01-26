    .data
    .global main_fp, 4, 4
    .text
.frame main, 8
    loadI 1 =>  %vr1
    addI %vr1, 0 => %vr4
.L0: nop
    iwrite %vr4
    loadI main_fp => %vr10
    cbr %vr2 -> .L3
.L1: nop
    iwrite %vr4
    loadI main_fp  => %vr10
    cbr %vr2 -> .L3
.L2: nop
    iwrite %vr4
    loadI main_fp => %vr10
    cbr %vr2 -> .L3
.L3: nop
    iwrite %vr4
    loadI main_fp => %vr10

