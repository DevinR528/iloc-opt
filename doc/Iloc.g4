grammar C;

program
  : (
			(DATA data)? TEXT procedures
			| listOfIlocInstructions
		)
	;

data
	: ( pseudoOp )*
	;

procedures
	: ( procedure )+
	;

procedure
	: frameInstruction listOfIlocInstructions
	;

listOfIlocInstructions
	: (
    	(LABEL COLON)? ( operation | LBRACKET  operationList RBRACKET ) )+
		)
	;

frameInstruction
	: FRAME LABEL  NUMBER (virtualReg)*
	;

operationList
  : operation (SEMICOLON operation)*
	;

operation
	 : (ADD virtualReg  virtualReg ASSIGN virtualReg
    	| ADDI virtualReg NUMBER ASSIGN virtualReg
    	| ANDI virtualReg NUMBER ASSIGN virtualReg
    	| AND virtualReg virtualReg ASSIGN virtualReg
    	| C2C virtualReg ASSIGN virtualReg
    	| C2I virtualReg ASSIGN virtualReg
    	| CALL LABEL ( virtualReg )*
    	| CBR virtualReg ASSIGN LABEL
    	| CBRNE virtualReg ASSIGN LABEL
    	| CBR_LT virtualReg ASSIGN LABEL  LABEL
    	| CBR_LE virtualReg ASSIGN LABEL  LABEL
    	| CBR_EQ virtualReg ASSIGN LABEL  LABEL
    	| CBR_NE virtualReg ASSIGN LABEL  LABEL
    	| CBR_GT virtualReg ASSIGN LABEL  LABEL
    	| CBR_GE virtualReg ASSIGN LABEL  LABEL
    	| CLOADAI virtualReg NUMBER ASSIGN virtualReg
    	| CLOADAO virtualReg  virtualReg ASSIGN virtualReg
    	| CLOAD virtualReg ASSIGN virtualReg
    	| CMP_LT virtualReg  virtualReg ASSIGN virtualReg
    	| CMP_LE virtualReg  virtualReg ASSIGN virtualReg
    	| CMP_EQ virtualReg  virtualReg ASSIGN virtualReg
    	| CMP_NE virtualReg  virtualReg ASSIGN virtualReg
    	| CMP_GT virtualReg  virtualReg ASSIGN virtualReg
    	| CMP_GE virtualReg  virtualReg ASSIGN virtualReg
    	| COMP virtualReg  virtualReg ASSIGN virtualReg
    	| CREAD virtualReg
    	| CSTOREAI virtualReg ASSIGN virtualReg NUMBER
    	| CSTOREAO virtualReg ASSIGN virtualReg  virtualReg
    	| CSTORE virtualReg ASSIGN virtualReg
    	| CWRITE virtualReg
    	|  EXIT
    	| DIVI virtualReg NUMBER ASSIGN virtualReg
    	| DIV virtualReg  virtualReg ASSIGN virtualReg
    	| F2F virtualReg ASSIGN virtualReg
    	| F2I virtualReg ASSIGN virtualReg
    	| FADD virtualReg  virtualReg ASSIGN virtualReg
    	| FCALL LABEL ( virtualReg )* ASSIGN virtualReg
    	| FCMP_LT virtualReg  virtualReg ASSIGN virtualReg
    	| FCMP_LE virtualReg  virtualReg ASSIGN virtualReg
    	| FCMP_EQ virtualReg  virtualReg ASSIGN virtualReg
    	| FCMP_NE virtualReg  virtualReg ASSIGN virtualReg
    	| FCMP_GT virtualReg  virtualReg ASSIGN virtualReg
    	| FCMP_GE virtualReg  virtualReg ASSIGN virtualReg
    	| FCOMP virtualReg  virtualReg ASSIGN virtualReg
    	| FDIV virtualReg  virtualReg ASSIGN virtualReg
    	| FLOADAI virtualReg NUMBER ASSIGN virtualReg
    	| FLOADAO virtualReg  virtualReg ASSIGN virtualReg
    	| FLOAD virtualReg ASSIGN virtualReg
    	| FMULT virtualReg  virtualReg ASSIGN virtualReg
    	| FREAD virtualReg
    	| FRET virtualReg
    	| FWRITE virtualReg
    	| FSTOREAI virtualReg ASSIGN virtualReg NUMBER
    	| FSTOREAO virtualReg ASSIGN virtualReg  virtualReg
    	| FSTORE virtualReg ASSIGN virtualReg
    	| FSUB virtualReg  virtualReg ASSIGN virtualReg
    	| I2F virtualReg ASSIGN virtualReg
    	| I2I virtualReg ASSIGN virtualReg
    	| ICALL LABEL ( virtualReg )* ASSIGN virtualReg
    	| IRCALL virtualReg ( virtualReg )* ASSIGN virtualReg
    	| IREAD virtualReg
    	| IRET virtualReg
    	| IWRITE virtualReg
    	| JUMPI LABEL
    	| JUMP ASSIGN virtualReg
    	| LOADAI virtualReg NUMBER ASSIGN virtualReg
    	| LOADAO virtualReg  virtualReg ASSIGN virtualReg
    	| LOAD virtualReg ASSIGN virtualReg
    	| LOADI constVal = immediateVal ASSIGN virtualReg
    	| LSHIFTI virtualReg NUMBER ASSIGN virtualReg
    	| LSHIFT virtualReg  virtualReg ASSIGN virtualReg
  		|  MALLOC  virtualReg  ASSIGN  virtualReg
    	| MOD virtualReg  virtualReg ASSIGN virtualReg
    	| MULTI virtualReg NUMBER ASSIGN virtualReg
    	| MULT virtualReg  virtualReg ASSIGN virtualReg
    	| NOP
    	| NOT virtualReg ASSIGN virtualReg
    	| ORI virtualReg NUMBER ASSIGN virtualReg
    	| OR virtualReg  virtualReg ASSIGN virtualReg
    	| RSHIFTI virtualReg NUMBER ASSIGN virtualReg
    	| RSHIFT virtualReg  virtualReg ASSIGN virtualReg
    	| RET
    	| STOREAI virtualReg ASSIGN virtualReg NUMBER
    	| STOREAO virtualReg ASSIGN virtualReg  virtualReg
    	| STORE virtualReg ASSIGN virtualReg
    	| SUBI virtualReg NUMBER ASSIGN virtualReg
    	| SUB virtualReg  virtualReg ASSIGN virtualReg
    	| SWRITE virtualReg
    	| TBL virtualReg  LABEL
    	| TESTEQ virtualReg ASSIGN virtualReg
    	| TESTGE virtualReg ASSIGN virtualReg
    	| TESTGT virtualReg ASSIGN virtualReg
    	| TESTLE virtualReg ASSIGN virtualReg
    	| TESTLT virtualReg ASSIGN virtualReg
    	| TESTNE virtualReg ASSIGN virtualReg
    	| XORI virtualReg NUMBER ASSIGN virtualReg
    	| XOR virtualReg  virtualReg ASSIGN virtualReg
    )
	;

pseudoOp
		: ( STRING LABEL  STRING_CONST
   		| FLOAT LABEL FLOAT_CONST
   		| GLOBAL LABEL NUMBER  NUMBER
  		)
		;

virtualReg: VR

immediateVal()
	: (
			LABEL
     	| NUMBER
		)
	;
}

ADD: 'add' ;
ADDI: 'addI' ;
AND: 'and' ;
ANDI: 'andI';
C2C: 'c2c';
C2I: 'c2i';
CALL: 'call' ;
CBR: 'cbr' ;
CBRNE: 'cbrne' ;
CBR_LT: 'cbr_LT';
CBR_LE: 'cbr_LE';
CBR_EQ: 'cbr_EQ';
CBR_NE: 'cbr_NE';
CBR_GT: 'cbr_GT';
CBR_GE: 'cbr_GE';
CLOADAI: 'cloadAI' ;
CLOADAO: 'cloadAO' ;
CLOAD: 'cload' ;
CMP_LT: 'cmp_LT';
CMP_LE: 'cmp_LE';
CMP_EQ: 'cmp_EQ';
CMP_NE: 'cmp_NE';
CMP_GT: 'cmp_GT';
CMP_GE: 'cmp_GE';
COMP: 'comp' ;
CREAD: 'cread' ;
CSTOREAI: 'cstoreAI' ;
CSTOREAO: 'cstoreAO' ;
CSTORE: 'cstore' ;
CWRITE: 'cwrite' ;
DATA: '.data' ;
DIVI: 'divI' ;
DIV: 'div' ;
EXIT: 'exit' ;
F2F:'f2f' ;
F2I: 'f2i' ;
FADD: 'fadd' ;
FCALL: 'fcall' ;
FCOMP: 'fcomp' ;
FCMP_LT: 'fcmp_LT';
FCMP_LE: 'fcmp_LE';
FCMP_EQ: 'fcmp_EQ';
FCMP_NE: 'fcmp_NE';
FCMP_GT: 'fcmp_GT';
FCMP_GE: 'fcmp_GE';
FDIV: 'fdiv' ;
FLOADAI: 'floadAI' ;
FLOADAO: 'floadAO' ;
FLOAD: 'fload' ;
FLOAT: '.float' ;
FMULT: 'fmult' ;
FRAME: '.frame' ;
FREAD: 'fread' ;
FRET: 'fret' ;
FWRITE: 'fwrite' ;
FSTOREAI: 'fstoreAI' ;
FSTOREAO: 'fstoreAO' ;
FSTORE: 'fstore' ;
FSUB: 'fsub' ;
GLOBAL: '.global' ;
I2F: 'i2f' ;
I2I: 'i2i' ;
ICALL: 'icall' ;
IRCALL: 'ircall' ;
IREAD: 'iread' ;
IRET: 'iret' ;
IWRITE: 'iwrite' ;
JUMPI: 'jumpI' ;
JUMP: 'jump' ;
LOADAI: 'loadAI' ;
LOADAO: 'loadAO' ;
LOAD: 'load' ;
LOADI: 'loadI' ;
LSHIFTI: 'lshiftI' ;
LSHIFT: 'lshift' ;
MALLOC: 'malloc' ;
MOD: 'mod' ;
MULTI: 'multI' ;
MULT: 'mult' ;
NOP: 'nop' ;
NOT: 'not' ;
OR: 'or' ;
ORI: 'orI';
RSHIFTI: 'rshiftI' ;
RSHIFT: 'rshift' ;
RET: 'ret' ;
STOREAI: 'storeAI' ;
STOREAO: 'storeAO' ;
STORE: 'store' ;
STRING: '.string' ;
SUBI: 'subI' ;
SUB: 'sub' ;
SWRITE: 'swrite' ;
TBL: 'tbl';
TESTEQ: 'testeq' ;
TESTGE: 'testge' ;
TESTGT: 'testgt' ;
TESTLE: 'testle' ;
TESTLT: 'testlt' ;
TESTNE: 'testne' ;
TEXT: '.text' ;
XOR: 'xor';
XORI: 'xorI';

ASSIGN: '=>';
ARROW: '->';
LON: ':' ;
SEMICOLON: ';';
LBRACKET: '[';
RBRACKET: ']';
COMMA: ',';
VR: '%vr' NUMBER;
STRING_CONST: '\''(~['\''])*'\'' >
LABEL: (INITIAL)* ALPHA (ALPHA | INITIAL | DIGIT)*;
FLOAT_CONST: NUMBER ('.' (DIGIT)+ (EXPONENT)? | EXPONENT);
NUMBER: '0' | ('-')? ['1' - '9'](DIGIT)*;

fragment
EXPONENT: ('e' | 'E') ('+' | '-')? (<DIGIT>)+;

fragment
INITIAL: <DOT> | <UNDERSCORE>;

fragment
UNDERSCORE: '_';

fragment
ALPHA: ['a' - 'z'] | ['A' - 'Z'];

fragment
DIGIT: ['0' - '9'];

fragment
DOT: '.';

WS : [ \t\r\n]+ -> skip ;
COMMENT: "#" (~["\n","\r"])* -> skip;
