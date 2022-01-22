	.data
	.string	.int_wformat, "%d\12"
	.string	.float_wformat, "%f\12"
	.string	.char_wformat, "%c\12"
	.string	.string_wformat, "%s\12"
	.string	.int_rformat, "%d"
	.string	.float_rformat, "%f"
	.string	.char_rformat, "%c"
	.string	.string_rformat, "%s"
	.global	main_fp, 4, 4
	.text
	.frame	main, 8
	loadI	main_fp  => %vr4
	store	%vr0  => %vr4
	addI	%vr0, -4 => %vr6
	iread	%vr6
	addI	%vr0, -8 => %vr8
	iread	%vr8
	load	%vr6  => %vr9
	loadI	0  => %vr10
	comp	%vr9, %vr10 => %vr11
	testne	%vr11  => %vr12
	load	%vr8  => %vr13
	comp	%vr13, %vr10 => %vr14
	testne	%vr14  => %vr15
	or	%vr12, %vr15 => %vr16
	comp	%vr16, %vr10 => %vr17
	testeq	%vr17  => %vr18
	cbr	%vr18  -> .L0
.L1:	nop
	addI	%vr0, -4 => %vr6
	addI	%vr0, -8 => %vr8
	icall	gcd, %vr6, %vr8 	 => %vr19
	iwrite	%vr19
	addI	%vr0, -4 => %vr6
	iread	%vr6
	addI	%vr0, -8 => %vr8
	iread	%vr8
	load	%vr6  => %vr9
	loadI	0  => %vr10
	comp	%vr9, %vr10 => %vr11
	testne	%vr11  => %vr12
	load	%vr8  => %vr13
	comp	%vr13, %vr10 => %vr14
	testne	%vr14  => %vr15
	or	%vr12, %vr15 => %vr16
	cbr	%vr16  -> .L1
.L0:	nop
	ret
	.frame	gcd, 4, %vr4, %vr5
	load	%vr5  => %vr6
	loadI	0  => %vr7
	comp	%vr6, %vr7 => %vr8
	testeq	%vr8  => %vr9
	cbrne	%vr9  -> .L2
	load	%vr4  => %vr10
	iret	%vr10
	jumpI	-> .L3
.L2:	nop
	load	%vr4  => %vr10
	load	%vr5  => %vr6
	mod	%vr10, %vr6 => %vr11
	addI	%vr0, -4 => %vr13
	store	%vr11  => %vr13
	icall	gcd, %vr5, %vr13 	 => %vr14
	iret	%vr14
.L3:	nop
	ret
