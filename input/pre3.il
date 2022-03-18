.data

.text
.frame pre_example, 0, %vr1, %vr2, %vr3
    loadI 5 => %vr4
    comp %vr1, %vr4 => %vr5
    testge %vr5 => %vr6
    cbr %vr6 -> .L1
.L0: nop
    loadI 4 => %vr7
    add %vr2, %vr7 => %vr8
    i2i %vr8 => %vr3
    loadI 1 => %vr9
    add %vr1, %vr9 => %vr10
    i2i %vr10 => %vr1
    loadI 5 => %vr4
    comp %vr1, %vr4 => %vr5
    testge %vr5 => %vr6
    cbrne %vr6 -> .L0
.L1: nop
    iwrite %vr3
    ret
.frame main, 0 
    loadI 3 => %vr11
    loadI 2 => %vr12
    loadI 0 => %vr13
    call pre_example, %vr11, %vr12, %vr13
    ret
