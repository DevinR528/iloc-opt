    .data
    .global main_fp, 4, 4
    .text
.frame main, 8 
    loadI 1 => %vr4
.L1: nop
    iwrite %vr4
    loadI main_fp => %vr10
    load %vr10 => %vr11
    addI %vr11, -4 => %vr13
    i2i %vr4 => %vr15
    multI %vr15, 4 => %vr17
    sub %vr13, %vr17 => %vr18
    iread %vr18
    addI %vr4, 1 => %vr19
    i2i %vr19 => %vr4
    loadI 20 => %vr7
    comp %vr4, %vr7 => %vr8
    testlt %vr8 => %vr9
    cbr %vr9 -> .L1
