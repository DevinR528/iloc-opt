    .data
    .text
.frame main, 0
.B1: nop
    loadI 1 => %vr1
    loadI 1 => %vr17
    loadI 1 => %vr18
    loadI 1 => %vr19
    i2i %vr1 => %vr2
    loadI 10 => %vr3
    i2i %vr3 => %vr4
    cmp_GE %vr2, %vr4 => %vr5
    cbr %vr5 -> .B3
.B2: nop
    mult %vr17, %vr18 => %vr20
    add %vr19, %vr20 => %vr21
    i2i %vr21 => %vr8
    iwrite %vr2
    addI %vr2, 1 => %vr6
    i2i %vr6 => %vr2
    cmp_LT %vr2, %vr4 => %vr7
    cbr %vr7 -> .B2
.B3: nop
    iwrite %vr8
    ret
