    .text
.frame main, 8 
    add %vr0, %vr7 => %vr8
    subI %vr2, 1 => %vr7
    i2i %vr8 => %vr9
    mult %vr10, %vr17 => %vr18
    i2i %vr18 => %vr19
