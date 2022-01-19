    .data
    .string .int_rformat, "%d"
    .string .float_rformat, "%f"
    .string .char_rformat, "%c"
    .string .string_rformat, "%s"
    .text
.frame main, 60
    loadI 32 => %vr8
    loadI 1 => %vr9
    add %vr8, %vr9 => %vr10
.L1: nop
    comp %vr9, %vr8 => %vr33
    testgt %vr33 => %vr34
    cbr %vr34 -> .L3
.L4: nop
    iwrite %vr10
    store %vr8 => %vr0
    load %vr0 => %vr21
    iwrite %vr21
    ret
.L3: nop
    iwrite %vr33
    ret
