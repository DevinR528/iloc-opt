	.data
	.text
	.frame	main, 0
.B1:	nop
	loadI	1  => %vr1_1
	i2i	%vr1_1  => %vr2_0
	loadI	10  => %vr3_0
	i2i	%vr3_0  => %vr4_0
	comp	%vr2_0, %vr4_0 => %vr5_0
	testge	%vr5_0  => %vr11_0
	cbr	%vr11_0  -> .B3

	Phi Nodes for Block 5
		phi	%vr2_0, %vr2_2 	 => %vr2_1

.B2:	nop
	mult	%vr1_1, %vr1_1 => %vr20_0
	add	%vr1_1, %vr20_0 => %vr21_0
	i2i	%vr21_0  => %vr8_1
	iwrite	%vr2_1
	addI	%vr2_1, 1 => %vr6_0
	i2i	%vr6_0  => %vr2_2
	comp	%vr2_2, %vr4_0 => %vr7_0
	testlt	%vr7_0  => %vr10_0
	cbr	%vr10_0  -> .B2

	Phi Nodes for Block 6
		phi	%vr8_0, %vr8_1 	 => %vr8_2

.B3:	nop
	iwrite	%vr8_2
	ret
