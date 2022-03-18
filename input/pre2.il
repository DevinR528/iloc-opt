.data
    .string .str_const_0, "howdy"
.text
.frame main, 12
    loadI 0 => %vr1
    i2i %vr1 => %vr2
    loadI 0 => %vr1
    i2i %vr1 => %vr3
    i2i %vr0 => %vr5
    loadI 4 => %vr4
    sub %vr5, %vr4 => %vr6
    store %vr3 => %vr6
    iread %vr6
    loadI 3 => %vr7
    i2i %vr7 => %vr8
    load %vr6 => %vr9
    loadI 3 => %vr7
    comp %vr9, %vr7 => %vr10
    testle %vr10 => %vr11
    cbr %vr11 -> .L0
    load %vr6 => %vr9
    add %vr9, %vr8 => %vr12
    i2i %vr12 => %vr2
    jumpI -> .L1
.L0: nop
    load %vr6 => %vr9
    add %vr9, %vr8 => %vr12
    i2i %vr12 => %vr2
    loadI .str_const_0 => %vr13
    swrite %vr13
.L1: nop
    iwrite %vr2
    ret
