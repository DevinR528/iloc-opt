.data

.text
.frame pre_example, 4, %vr1, %vr2, %vr3
    loadI 4 => %vr4
    i2i %vr4 => %vr5
    loadI 5 => %vr6
    comp %vr1, %vr6 => %vr7
    testge %vr7 => %vr8
    cbr %vr8 -> .L1
.L0: nop
    add %vr2, %vr5 => %vr9
    i2i %vr9 => %vr3
    loadI 1 => %vr10
    add %vr1, %vr10 => %vr11
    i2i %vr11 => %vr1
    loadI 5 => %vr6
    comp %vr1, %vr6 => %vr7
    testge %vr7 => %vr8
    cbrne %vr8 -> .L0
.L1: nop
    iwrite %vr3
    ret
.frame main, 0
    loadI 3 => %vr12
    loadI 2 => %vr13
    loadI 0 => %vr14
    call pre_example, %vr12, %vr13, %vr14
    ret
