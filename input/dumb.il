    .data
    .global main_fp, 4, 4
    .text
.frame	main, 8
    loadI 1 =>  %vr1
    addI %vr1, 0 => %vr4
.L1:	nop
	iwrite	%vr4
	loadI	main_fp  => %vr10
	load	%vr10  => %vr11
	loadI	-4  => %vr12
	add	%vr11, %vr12 => %vr13
	loadI	0  => %vr14
	sub	%vr4, %vr14 => %vr15
	loadI	4  => %vr16
	mult	%vr15, %vr16 => %vr17
	sub	%vr13, %vr17 => %vr18
	iread	%vr18
	loadI	1  => %vr6
	add	%vr4, %vr6 => %vr19
	i2i	%vr19  => %vr4
	loadI	20  => %vr7
	comp	%vr4, %vr7 => %vr8
	testlt	%vr8  => %vr9
	cbr	%vr9  -> .L1
