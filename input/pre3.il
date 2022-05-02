.data

.text
.frame pre_example, 4, %vr5, %vr6
    loadI 0 => %vr7
    i2i %vr7 => %vr8
    loadI 5 => %vr9
    comp %vr8, %vr9 => %vr10
    testge %vr10 => %vr11
    cbr %vr11 -> .L1
.L0: nop
    loadI 7 => %vr12
    add %vr5, %vr12 => %vr13
    i2i %vr13 => %vr6
    loadI 1 => %vr14
    add %vr8, %vr14 => %vr15
    i2i %vr15 => %vr8
    loadI 5 => %vr9
    comp %vr8, %vr9 => %vr10
    testge %vr10 => %vr11
    cbrne %vr11 -> .L0
.L1: nop
    iwrite %vr6
    ret
.frame main, 0
    loadI 3 => %vr16
    loadI 2 => %vr17
    call pre_example, %vr16, %vr17
    ret
