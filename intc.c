#include <stdio.h>
#include <stdlib.h>
#include <string.h>
enum {
	WORD=4, // Size of machine word in bytes
	NAME=15, // Maximum name length
	TOK=4096, // Maximum token length
	NSYM=4096, // Maximum number of symbols
	PROG=65536, // Maximum program length
	ROM=65536, // Maximum size of constant data
	// Global, function, parameter, and local storage types
	GLOSTO=0,FUNSTO,PARSTO,LOCSTO,
	// Types
	ANY=0,BYTE,INT,
	// Type modifiers: pointer, function returning ~, ~ target (for the left side of =)
	PTR=16,FUN=64,TAR=128,
	// Tokens: keep in order w/ pun array
	TCOMMA=0,COLON,TSEMI,TLP,TRP,TLB,TRB,TLK,TRK,TASS,TEXC,
	TTIL,TMUL,TDIV,TMOD,TADD,TSUB,TAND,TOR,TXOR,TLT,TGT,TEQ,
	TNE,TLE,TGE,TINC,TDEC,TAND2,TOR2
};
FILE	*sf,*bin; // Source and ouput binary files
int	oc,nc; // old and next characters in file
int	top,back; // token operation(TADD, etc) and backup flag
int	ln=1; // line number
int	ret; // return type
int	brkj,cntj; // break jump, continue jump
int	nref; // number of references to functions/globals to fix up
char	*typenm[]={"any","byte","int"};
char	ref[NSYM][NAME]; // The name of a global that has references
char	sym[NSYM][NAME]; // The name of a symbol
char	prog[PROG],rom[ROM]; // Program machine code and data
int	pc,rc; // Program Counter and ROM counter
char	tok[TOK]; // Token text
char 	hex[256]; // Mapping from ASCII to hex values (hex['A']=10)
int	symt[NSYM];// Symbol type
int	syma[NSYM];// Symbol address
int	syms[NSYM];// Symbol storage type
int	nsym,nglo,npar,nloc; // Number of symbols, globals, params, locals
int	refa[NSYM], storeg[]={0x87,0x86,0x85,0x85};
// Punctuation, keep in order w/ token enum above
char	*pun[]={ ",:;()[]{}=!~*/%+-&|^<>", "==!=<=>=++--&&||" };
// Operator machine code for * through >=, ++,--,&&,|| 
char	*opc[]={
	"0fafc1			imul a,c",
	"9199f7f9		xchg a,c;cdq;idiv c",
	"9199f7f992		xchg a,c;cdq;idiv c;xchg a,d",
	"01c8			add a,c",
	"29c191			sub c,a;xchg a,c",
	"21c8			and a,c",
	"09c8			or a,c",
	"31c8			xor a,c",
	"39c10f9cc00fb6c0	cmp c,a; setl a; movzx",
	"39c10f9fc00fb6c0	cmp c,a; setg a; movzx",
	"39c10f94c00fb6c0	cmp c,a; sete a; movzx",
	"39c10f95c00fb6c0	cmp c,a; setne a; movzx",
	"39c10f9ec00fb6c0	cmp c,a; setle a; movzx",
	"39c10f9dc00fb6c0	cmp c,a; setge a; movzx",
	"ff008b00		inc dword[a];mov a,[a]",
	"ff088b00		dec dword[a];mov a,[a]",
	"85c00f84x		test a,a; jz END",
	"85c00f85x		test a,a; jnz END",
};
main(int argc, char **argv) {
	int	i,ent,x;
	for (i=0; i<16; i++) hex["0123456789abcdef"[i]]=i;
	lend("prnc",INT,putchar);
	lend("inpc",INT,getchar);
	lend("_ALLOC_",PTR,malloc);
	lend("_FREE_",PTR,free);
	lend("exit",INT,exit);
	if (! (sf=fopen(argv[1],"r")) ) {
		printf("cannot open: %s\n",argv);
		exit(1);
	}
	// Prime the tokeniser
	// Load the first character into nc
	// Skip the initial whitespace
	nextc(), skipws();
	while (peek() || fclose(sf))
		_top();
	err(nref,ref[0]," unresolved");
	ent=oi((int)calloc(1,nglo*WORD), "bf	mov di,DATA");
	oi((int)prog, 			"be	mov si,CODE");
	oi((int)rom, 			"bb	mov b,CODE");
	oi(find("main",&x,&x,0)-(pc+5),	"e9	jmp MAIN");
	bin=fopen("bin","wb");
	for (i=0;i<pc || fclose(bin);i++)
		fputc(prog[i],bin);
	printf("> %d\n",((int(*)()) (prog+ent-5))());
	return 0;
}
// Lend the client a function from the host
lend(char *name, int type, int fun()) {
	syma[decl(name,type+FUN,FUNSTO)]=(int)fun-(int)prog;
}
// Raise an error
err(int yes, char *obj, char *msg) {
	if (!yes) return 1;
	printf("err %d(%s): %s%s\n",ln,tok,obj?obj:"",msg);
	exit(1);
}
// Top-level declaration
_top() {
	int	pro,x;
	// Add symbol assuming its a global variable
	x=_decl("top level", GLOSTO);
	if (eat(";")) // Variable
		return;
	
	// Function
	nglo--; // It wasn't a global variable
	nloc=npar=0;
	syma[x]=pc; // Address of this symbol is the current EIP
	syms[x]=FUNSTO;

	// Params
	if (need("(") && peek()!=')')
		do
			_decl("param", PARSTO);
		while (eat(","));
	need(")");
	
	symt[x]=FUN+(ret=_type());
	
	// Allocate locals with ENTER instruction
	// It allocates locals below [EBP]
	// We don't know how many locals there are now
	// Patch it once we've read the function body
	pro=o("c8...	enter");
	_stmnt();
	prog[pro-3]=nloc*WORD;
	prog[pro-2]=(nloc*WORD)>>8;
	o("31c0c9c3	xor a,a;leave;ret"); // Automatic `return 0;`
	nsym=x+1;
}

// Parse a statement
// See patch() for an explanation of how jumps are resolved
_stmnt() {
	int	i,elsej,endj;
	if (eat(";"))
		return;
	else if (eat("{")) {
		while (!eat("}")) {
			err(!peek(), 0, "block not closed");
			_stmnt();
		}
		return;
	} else if (eat("break")) {
		err(!brkj, 0, "BREAK not in loop");
		brkj=oi(brkj, "e9	jmp BREAK");
	} else if (eat("continue")) {
		err(!cntj, 0, "CONTINUE not in loop");
		oi(cntj-(pc+5), "e9	jmp CONTINUE");
	} else if (eat("return")) {
		if (peek()==';')
			o("31c0 xor a,a");
		else
			ck(rval(_exp()), "return", ret);
		o("c9c3			leave;ret");
	} else if (eat("if")) {
		_pexp();
		elsej=o("85c00f84x	test a,a; jz ELSE");
		_stmnt();
		endj=o("e9x		jmp END");
		patch(elsej,1);
		if (eat("else")) {
			_stmnt();
			endj=oi(endj,"e9 jmp END");
		}
		patch(endj,1);
		return;
	} else if (eat("while")) {
		cntj=pc;
		_pexp();
		brkj=o("85c00f84x	test a,a; jz BREAK");
		_stmnt();
		oi(cntj-(pc+5),"e9	jmp	CONTINUE");
		patch(brkj,1);
		cntj=brkj=0;
		return;
	} else if (eat("var"))
		do
			_decl("var", LOCSTO);
		while (eat(","));
	else if (eat("goto")) {
		cka(rval(_exp()),FUN,"label");
		o("ffe0		jmp eax");
	} else if (isname(peek()) && nc==':')
		return next(), decl(tok,FUN,FUNSTO), next();
	else
		rval(_exp());
	need(";");
}
_pexp() {
	need("(");
	rval(_exp());
	need(")");
}
// Functions that parse expressions return the type
// When an l-value is encountered, a pseudo-type TAR (target) is set
// l-values are stored as pointers to memory
// rval() is used to turn that l-value into a normal r-value
// Expressions return their results in the eax register
_exp() { // Assignment expression
	int	l=_loge(),r;
	if (!range(TASS,TASS))
		return l;
	l=cka(l,TAR,"target")^TAR;
	o("50		push a");
	r=ck(rval(_exp()), "=", l);
	o("598901	pop c; mov [c],a");
	prog[pc-2] -= tsz(l)==1; /* fix for size */
	return r;
}
_loge() { // logic expression && ||
	int	oper,fix,r,l=_rele();
	while (oper=range(TAND2,TOR2)) {
		rval(l), l=INT;
		fix=o(opc[oper-TMUL]);
		r=rval(_rele());
		patch(fix,1);
		o("85c00f95c00fb6c0 test a,a;setnz a,a;movzx a");
	}
	return l;
}
// Binary expressions:
// Evaluate the left into the eax register
// Save eax, and evaluate the right into eax
// Pop ecx, now the right is in eax and the left in ecx.
// opc[] contains the machine code for the operators
#define _BIN_(LO,HI,ELEM,TYPE) int oper,r,l=ELEM();\
	while (oper=range(LO,HI)) {\
		l=ck(rval(l),tok,TYPE);\
		o("50	push a");\
		r=ck(rval(ELEM()),"",TYPE);\
		o("59	pop c");\
		o(opc[oper-TMUL]);\
	}\
	return l;
_rele() {_BIN_(TLT,TGE,_adde,INT)}
_adde() {_BIN_(TADD,TSUB,_bite,INT)}
_bite() {_BIN_(TAND,TXOR,_mule,INT)}
_mule() {_BIN_(TMUL,TMOD,_pree,INT)}
_pree() { // Prefix expressions
	int	t,x,oper;
	if (!strchr("+-*&~!",peek()))
		return _poste();
	next();
	oper=top;
	if (oper==TAND)
		return cka(_pree(),TAR,"target")^TAR^PTR;
	else if (oper==TINC || oper==TDEC) {
		t=cka(_pree(),TAR,"target")^TAR;
		o(opc[oper-TMUL]);
		prog[pc-4] -= tsz(t)==1; /* fix for size */
		return ck(t,"",INT);
	}
	t=rval(_pree());
	if (oper==TSUB)		t=ck(t,"-",INT), o("f7d8 neg a");
	else if (oper==TADD)	t=ck(t,"+",INT);
	else if (oper==TTIL)	t=ck(t,"~",INT), o("f7d0 not a");
	else if (oper==TMUL)	t=cka(t,PTR,"ptr")^(PTR+TAR);
	else if (oper==TEXC)
		t=INT, o("85c00f94c00fb6c0 test a,a;setz a;movzx");
	return t;
}
_poste() { // Postfix expressions: calling, indexing, casting, ++, --
	int	n,fix,t=_atome();
	for (;;)
	if (eat("(")) {
		// cdecl calling convention:
		// Variables are pushed on the stack
		// Return values are returned in eax
		//
		// The function is evaluated and pushed on the stack
		// Arguments are evaluated left-to-right
		// Once each argument is evaluated, it is put in [ESP+n]
		// The function is then popped and called
		// On return, the arguments are removed from the stack
		t=cka(rval(t),FUN,"fun")^FUN;
		n=0;
		fix=o("81ecx50	sub sp,X;push a");
		if (peek() != ')')
			do {
				rval(_exp());
				oi(n++*WORD+4,"898424 mov[sp+X],a");
			} while (eat(","));
		o("58ffd0	pop a;call a");
		oi(sx(fix-5,n*WORD), "81c4 add sp,X");
		need(")");
	} else if (eat("[")) {
		t=cka(rval(t),PTR,"ptr")^(PTR+TAR);
		o("50			push a");
		ck(rval(_exp()),"[",INT);
		if (tsz(t)==WORD)
			o("c1e002	shl a,2");
		o("5901c8		pop c;add a,c");
		need("]");
	} else if (eat("as"))
		t=_type()+(t & TAR); /* preserve target */
	else if (eat("++") || eat("--")) {
		t=ck(cka(t,TAR,"target")^TAR, tok, INT);
		o(opc[top-TMUL]);
		prog[pc-4] -= tsz(t)==1; /* fix for size */
		o(top==TINC? "48 dec a": "40 inc a");
	} else
		break;
	return t;
}
_atome() {
	int	soft=0,type,c,sto;
	if (eat("nil")) {
		type=ANY;
		oi(0, "b8		mov a,X");
	} else if (eat("fwdref")) {
		// Forward reference
		err(!isname(peek()),0,"need name");
		soft=1;
		goto load;
	} else

	// Variable reference
load:	if (isname(peek()) && next()) {
		// Find the variable
		// find() returns the address
		// Every storage type has its own register that it's relative to
		// storeg[] returns that register
		// Variables are l-values unless they're functions
		o("8d. lea a,[??+X]");
		sx(pc,find(tok,&type,&sto,soft)), pc+=WORD;
		prog[pc-5]=storeg[sto];
		if (sto!=FUNSTO)
			type+=TAR;
	} else if (isdigit(*tok) && next()) {
		// Integer
		oi(strtoul(tok,0,0), "b8 mov a,X");
		type=INT;
	} else if (eat("\"")) {
		// String:
		// Strings aren't handled by the lexer
		// Copy strings into ROM
		// Load the address into the eax register
		oi(rc, "8d83 lea eax,[ebx+X]");
		while (0<=(c=quote()) && c!='"')
			rom[rc++]=c;
		rom[rc++]=0;
		err(c!='"',0,"string not closed");
		skipws();
		type=BYTE+PTR;
	} else if (eat("(")) {
		type=_exp();
		need(")");
	} else
		err(1,0,"not expression");
	return type;
}
// Type size
tsz(t) {
	return (t&~TAR)==BYTE? 1: WORD;
}
// Check attribute or throw error
cka(int t,int x,char *s) {
	if (t&x)	return t;
	prntype(t);
	puts("");
	err(1,"not ",s);
}
// Check type or throw error
ck(int t, char *who, int w) {
	if (t==w || !(w&3) || !(t&3))
		return t;
	if (t==INT && w==BYTE || t==BYTE && w==INT)
		return t;
	prntype(t);
	fputs(" vs ",stdout);
	prntype(w);
	puts("");
	err(1, who, " got the wrong type");
}
// Convert l-value (target) to a normal r-value
rval(t) {
	if (!(t & TAR))
		return t;
	if (tsz(t ^= TAR)==WORD)
		return o("8b00 mov a,[a]"),t;
	return o("0fb600 movzx a,byte[a]"),t;
}
// Print type
prntype(t) {
	printf("(%x)%s%s%s",t,typenm[t&3],
		t&PTR?"*":"", t&FUN?"()":"");
}
// Parse type
_type() {
	int	t,i;
	if (!isname(peek()))		return INT;
	else if (eat("int"))		t=INT;
	else if (eat("byte"))		t=BYTE;
	else if (eat("any"))		t=ANY;
	else				return INT;
	if (eat("*"))			t+=PTR;
	else if (eat("(") && eat(")"))	t+=FUN;
	return t;
}
// Read one literal character
quote() {
	char *p, *esc="t\tn\nr\r0";
	if (nextc()!='\\')
		return oc;
	return (p=strchr(esc, nextc()))? p[1]: oc;
}
// Return the type of the next token without consuming it
peek() {
	return next(), back=1, *tok;
}
// Consume the next token if its between a and b (inclusive)
range(a,b) {
	return (peek() && !(back=top<a || b<top))? top: 0;
}
// Consume a token if its the same as the string 
eat(char *x) {
	return peek() && !strcmp(tok,x)? (next(),1): 0;
}
// Consume a token or throw an error
need(char *x) {
	return err(!eat(x), "need ", x);
}
// Read a declaration
_decl(char *who, int sto) {
	char name[NAME];
	err(!isname(peek()), who, " needs name");
	next(), strcpy(name,tok);
	return decl(name,_type(),sto);
}
// Skip whitespace
skipws() {
	while (0<nc && isspace(nc) || nc=='#')
		if (nextc()=='#')
			while (0<nc && nc!='\n') nextc();
}
// Lexical analyzer (lexer):
// A one-token+one-character look-ahead tokeniser
// The current character is in oc, the next in nc.
// Read the next token and return its type
// Types are either the first character of a token or from the token enum
// Strings are not analysed
// 
next() {
	char	*d,*p,*s=tok;
	if (back)
		return back=0, tok[0];
	*s++=nextc();
	top=-1;
	if (oc==EOF)
		return *tok=0;
	if (isname(oc) || isdigit(oc)) // 
		while (isname(nc) || isdigit(nc))
			*s++=nextc();
	else if (oc=='`') // Character literal
		s=tok+sprintf(tok,"%d", quote());
	else if (oc=='"'); // String
	else if (p=strchr(*pun, oc)) { // Punctuation
		for (d=pun[1]; *d && !(*d==oc&&d[1]==nc); d+=2);
		top=*d? (*s++=nextc(),TEQ+(d-pun[1])/2): (p-*pun);
	} else
		*s=0, err(1,0,"bad token");
	*s=0;
	skipws();
	return *tok;
}
// Advance the source file one character
nextc() {
	oc=nc;
	nc=fgetc(sf);
	if (nc=='\n')
		ln++;
	return oc;
}
isname(c) {
	return isalpha(c) || c=='_';
}
// Find a symbol
// `soft` tells whether we can create a forward reference to it
// Symbols with forward references are resolved at the end of compilation 
find(char *name, int *type, int *sto, int soft) {
	int	i,x;
	for (i=0; i<nsym && strcmp(name,sym[i]); i++);
	if (i==nsym && soft) {
		// The symbol is not in the table
		// `soft` to create a forward reference
		// Try to find it by name in the ref[] table
		// Otherwise, create a new one
		// Add the current EIP to the reference chain
		for (i=0; i<nref && strcmp(name,ref[i]); i++);
		if (i==nref) refa[i]=0, strcpy(ref[nref++],name);
		return *type=FUN,*sto=FUNSTO,x=refa[i],refa[i]=pc,x;
	} else err(i==nsym, name, " undefined");
	return *type=symt[i], *sto=syms[i], syma[i];
}
// Define a symbol
decl(char *name, int type, int sto) {
	int	i;
	if (sto==FUNSTO) {
		// Resolve any existing forward references to functions
		for (i=0; i<nref && strcmp(name,ref[i]); i++);
		if (i!=nref) {
			patch(refa[i],0);
			memmove(refa+i,refa+i+1,sizeof *refa*(nref-1-i));
			memmove(ref+i,ref+i+1,NAME*(--nref-i));
		}
	}
	for (i=0; i<nsym && strcmp(name,sym[i]); i++);
	// Throw an error if we found the symbol
	// The second clause checks if they're both local or both global
	err(i!=nsym++ && (i<nglo)==(sto==GLOSTO), name, " re-decl");
	
	// Address assignment:
	// Functions take the address of the EIP they were defined on
	// Global variables take ascending addresses from the number of globals
	// Parameters are passed so that their addresses are ascending [8+EBP+n]
	// Locals are allocated descending from EBP
	if (sto==GLOSTO)	syma[i]=nglo++*WORD;
	else if (sto==FUNSTO)	syma[i]=pc;
	else if (sto==PARSTO)	syma[i]=(2+npar++)*WORD;
	else if (sto==LOCSTO)	syma[i]=-++nloc*WORD;
	strcpy(sym[i],name);
	symt[i]=type | (sto==FUNSTO? FUN: 0);
	return syms[i]=sto, i;
}
// Output machine code then a 4-byte integer
oi(int x, char *opc) {
	o(opc);
	sx(pc,x);
	return pc+=4;
}
// Load a 4-byte integer from the machine code EIP
lx(at) {
	return *(int*)(prog+at);
}
// Store an 4-byte integer at the machine code EIP 
sx(at,x) {
	return *(int*)(prog+at) = x;
}
// Patch a reference chain whos last node is `at` to go to the current PC
// rel determines whether the patch is EIP-relative or to an absolute address
// 
// Reference chains form a linked list in memory
// The most recent user is the head
// The address of the next user is stored in the immediate field of the instruction
// patch() follows the addresses until the lead to 0
// Each of the addresses is fixed to now point to the current PC
patch(at,rel) {
	int next, base=rel? at: 0, bk=rel? WORD: 0;
	for ( ; at; at=next, base=rel? at: 0)
		next=lx(at-bk), sx(at-bk,pc-base);
}
// Output machine code (specified in hexadecimal)
// '.' signifies one 0 byte.
// 'x' signifies four 0 bytes.
o(char *p) {
	for ( ; *p && !isspace(*p); p++)
		if (*p=='.')		prog[pc++]=0;
		else if (*p=='x')	o("....");
		else p++, prog[pc++]=(hex[p[-1]]<<4) + hex[*p];
	return pc;
}
