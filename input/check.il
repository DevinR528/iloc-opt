    .data
    .array foo, 3, [0, 1, 2]
    .string .string_const_0, "SUCCESS\n"
    .text
.frame main, 0
    loadI 1 => %vr6
    i2i %vr6 => %vr4
    loadI 10 => %vr7
    comp %vr4, %vr7 => %vr8
    testgt %vr8 => %vr9
    cbr %vr9 -> .L0
.L1: nop
    loadI 0 => %vr10
    comp %vr4, %vr10 => %vr11
    testlt %vr11 => %vr12
    cbrne %vr12 -> .L2
    loadI 10 => %vr7
    loadI 0 => %vr10
    mod %vr7, %vr10 => %vr13
    i2i %vr13 => %vr5
.L2: nop
    loadI 1 => %vr6
    add %vr4, %vr6 => %vr14
    i2i %vr14 => %vr4
    loadI 10 => %vr7
    comp %vr4, %vr7 => %vr8
    testle %vr8 => %vr9
    cbr %vr9 -> .L1
.L0: nop
    loadI .string_const_0 => %vr15
    swrite %vr15
    ret
