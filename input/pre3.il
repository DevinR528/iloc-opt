.data
.text
.frame pre_example, 8, %vr5, %vr6
    loadI 0 => %vr7
    i2i %vr7 => %vr8
    loadI 0 => %vr7
    i2i %vr7 => %vr9
    loadI 5 => %vr10
    comp %vr8, %vr10 => %vr11
    testge %vr11 => %vr12
    cbr %vr12 -> .L1
.L0: nop
    add %vr5, %vr6 => %vr13
    i2i %vr13 => %vr9
    loadI 1 => %vr14
    add %vr8, %vr14 => %vr15
    i2i %vr15 => %vr8
    loadI 5 => %vr10
    comp %vr8, %vr10 => %vr11
    testge %vr11 => %vr12
    cbrne %vr12 -> .L0
.L1: nop
    iwrite %vr9
    ret
.frame main, 0
    loadI 1 => %vr12
    loadI 2 => %vr13
    call pre_example, %vr12, %vr13
    ret
