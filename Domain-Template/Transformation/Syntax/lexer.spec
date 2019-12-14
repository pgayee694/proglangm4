(* ============================================================================================== *) 
datatype lexresult	= SHELL of string * string * {line: word, column: word};
val error 			= fn x => TextIO.output(TextIO.stdOut,x ^ "\n")
val eof 			= fn () => SHELL("","eof",getNextTokenPos(""))
(* ============================================================================================== *)
(* ------------------------------------------------------------------ *)
(* assumes that ">" does not occur as part of a nonterminal symbol *)
fun generateSchemaTokenName( yytext ) =
    let
		fun split(x, []   ) =  raise General.Fail("an_error")
		  | split(x, y::ys) = if x=y then ys else split(x,ys);
													
		fun splitFirst(symbol,[])    = 	[] (* symbol was not in the input list *)
		  | splitFirst(symbol,x::xs) = 	if x = symbol 
						then (* found split point *)
							[]
						else (* keep looking      *)
							x::splitFirst(symbol,xs);
																		
        val s0   = explode(yytext);
        val s1   = split(#"<",s0);
        val s2   = splitFirst(#">",s1);  
    in
        implode(explode("!#schema_variable_") @ s2)        
    end;
	
(* ------------------------------------------------------------------ *)

(* ============================================================================================== *)
%%
%header (functor Target_LexFn(val getNextTokenPos : string -> {line: word, column: word}));

alpha        = [A-Za-z];
digit        = [0-9];
alphanumeric = [A-Za-z0-9_];
integer      = 0 | [1-9][0-9]*;
boolean      = "true" | "false";
id           = [a-z][a-zA-Z0-9]*;
schema_id    = "<" {alpha}{alphanumeric}* ">_" {alphanumeric}+;
ws           = [\  \t \n];


%%

<INITIAL> "int"                     => ( SHELL(yytext        , yytext,     getNextTokenPos(yytext))    );
<INITIAL> "bool"                     => ( SHELL(yytext        , yytext,     getNextTokenPos(yytext))    );
<INITIAL> "while"                       => ( SHELL(yytext        , yytext,     getNextTokenPos(yytext))    );
<INITIAL> "for"                         => ( SHELL(yytext        , yytext,     getNextTokenPos(yytext))    );
<INITIAL> ";"                           => ( SHELL(yytext        , yytext,     getNextTokenPos(yytext))    );
<INITIAL> "if"                          => ( SHELL(yytext        , yytext,     getNextTokenPos(yytext))    );
<INITIAL> "else"                        => ( SHELL(yytext        , yytext,     getNextTokenPos(yytext))    );
<INITIAL> "print"                       => ( SHELL(yytext        , yytext,     getNextTokenPos(yytext))    );
<INITIAL> "false"                       => ( SHELL(yytext        , yytext,     getNextTokenPos(yytext))    );
<INITIAL> "true"                        => ( SHELL(yytext        , yytext,     getNextTokenPos(yytext))    );
<INITIAL> "}"                           => ( SHELL(yytext        , yytext,     getNextTokenPos(yytext))    );
<INITIAL> "{"                           => ( SHELL(yytext        , yytext,     getNextTokenPos(yytext))    );
<INITIAL> "++"                          => ( SHELL(yytext        , yytext,     getNextTokenPos(yytext))    );
<INITIAL> "--"                          => ( SHELL(yytext        , yytext,     getNextTokenPos(yytext))    );
<INITIAL> "+"                           => ( SHELL(yytext        , yytext,     getNextTokenPos(yytext))    );
<INITIAL> "-"                           => ( SHELL(yytext        , yytext,     getNextTokenPos(yytext))    );
<INITIAL> "*"                           => ( SHELL(yytext        , yytext,     getNextTokenPos(yytext))    );
<INITIAL> "/"                           => ( SHELL(yytext        , yytext,     getNextTokenPos(yytext))    );
<INITIAL> "%"                           => ( SHELL(yytext        , yytext,     getNextTokenPos(yytext))    );
<INITIAL> "^"                           => ( SHELL(yytext        , yytext,     getNextTokenPos(yytext))    );
<INITIAL> "<"                           => ( SHELL(yytext        , yytext,     getNextTokenPos(yytext))    );
<INITIAL> "<="                          => ( SHELL(yytext        , yytext,     getNextTokenPos(yytext))    );
<INITIAL> ">"                           => ( SHELL(yytext        , yytext,     getNextTokenPos(yytext))    );
<INITIAL> ">="                          => ( SHELL(yytext        , yytext,     getNextTokenPos(yytext))    );
<INITIAL> "=="                          => ( SHELL(yytext        , yytext,     getNextTokenPos(yytext))    );
<INITIAL> "!="                          => ( SHELL(yytext        , yytext,     getNextTokenPos(yytext))    );
<INITIAL> "&&"                          => ( SHELL(yytext        , yytext,     getNextTokenPos(yytext))    );
<INITIAL> "||"                          => ( SHELL(yytext        , yytext,     getNextTokenPos(yytext))    );
<INITIAL> "="                           => ( SHELL(yytext        , yytext,     getNextTokenPos(yytext))    );
<INITIAL> "("                           => ( SHELL(yytext        , yytext,     getNextTokenPos(yytext))    );
<INITIAL> ")"                           => ( SHELL(yytext        , yytext,     getNextTokenPos(yytext))    );
<INITIAL> "|"                           => ( SHELL(yytext        , yytext,     getNextTokenPos(yytext))    );
<INITIAL> "!"                           => ( SHELL(yytext        , yytext,     getNextTokenPos(yytext))    );

<INITIAL> {integer}                     => ( SHELL("integer"   , yytext,     getNextTokenPos(yytext))    );
<INITIAL> {boolean}                     => ( SHELL("boolean"        , yytext,     getNextTokenPos(yytext))    );
<INITIAL> {id}                          => ( SHELL("id"        , yytext,     getNextTokenPos(yytext))    );

<INITIAL> {ws}+        => ( getNextTokenPos(yytext); lex()  );
<INITIAL> {schema_id}               => ( SHELL(generateSchemaTokenName(yytext), yytext, getNextTokenPos(yytext))    );

<INITIAL>  .                            => ( error("ignored an unprintable character: " ^ yytext); getNextTokenPos(yytext); lex()  );
