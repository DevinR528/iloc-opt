    .text
.frame main 8 
.L_main
    add %vr0, %vr7 => %vr8
    subI %vr2, 1 => %vr7
    add %vr0, %vr7 => %vr9
    mult %vr10, %vr17 => %vr18
    load %vr18 => %vr19
