(* =========================================================================================================== *)
structure TypeChecker =
struct

open Model;
open CONCRETE_REPRESENTATION;

(* =========================================================================================================== *)
(*
    Here is where your typeCheck and typeOf definitions go. The primary challenge here is to translate the parse 
    expression notation we used in M2 to the actual SML tree patterns used in the TL System. See the comments in
    the semantics.sml file for a more detailed discussion on this topic. 
*)
exception model_error;

fun typeCheck( itree(inode("prog",_), [ stmt_list ] ), m) = m
  | typeCheck( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn typeCheck root = " ^ x_root ^ "\n\n")
  | typeCheck _ = raise Fail("Error in Model.typeCheck - this should never occur")

(* expression ::= expression || disjunction | disjunction *)
fun typeOf( itree(inode("expression",_),
                    [
                         expression, 
                         itree(inode(“||”, _), [] ),
                         disjunction
                    ]
                ), m ) =
    let
        val t1 = typeOf(expression ,m)
        val t2 = typeOf(disjunction,m)
    in
        if t1 = t2 andalso t1 = BOOL then BOOL
        else ERROR
    end

| typeOf( itree(inode("expression",_),
                    [
                         disjunction
                    ]
                ),
           m
           ) 
           = 
    typeOf(disjunction,m)

(*disjunction ::= disjunction && conjunction | conjunction*)
| typeOf( itree(inode("disjunction",_),
                    [
                         disjunction, 
                         itree(inode(“&&”, _), [] ),
                         conjunction
                    ]
                ),
           m
           ) =
    let
        val t1 = typeOf(conjunction,m)
 		val t2 = typeOf(disjunction,m)
    in
        if t1 = t2 andalso t1 = BOOL then BOOL
        else ERROR
    end

| typeOf( itree(inode("disjunction",_),
                    [
                         conjunction
                    ]
                ),
           m
           ) =
    typeOf(conjunction,m)
(*conjunction ::= conjunction != equality | conjunction == equality | equality*)
| typeOf( itree(inode("conjunction",_),
                    [
                         conjunction, 
                         itree(inode(“!=”, _), [] ),
                         equality
                    ]
                ),
           m
           ) =

    let
        val t1 = typeOf(conjunction,m)
        val t2 = typeOf(equality,m)
    in
		if t1 = t2 andalso t1 <> ERROR then BOOL
        else ERROR
    end
    
| typeOf( itree(inode("conjunction",_),
                    [
                         conjunction, 
                         itree(inode(“==”, _), [] ),
                         equality
                    ]
                ),
           m
           )  =

    let
        val t1 = typeOf(conjunction,m)
        val t2 = typeOf(equality,m)
    in
        if t1 = t2 andalso t1 <> ERROR then BOOL 
        else ERROR
    end
    
| typeOf( itree(inode("conjunction",_),
                    [
                   
                         equality
                    ]
                ),
           m
           ) =
    typeOf(equality,m)
    
(*equality ::= equality < expr | equality <= expr | equality > expr | equality >= expr | expr*)

| typeOf( itree(inode("equality",_),
                    [
                         equality, 
                         itree(inode(“<”, _), [] ),
                         expr
                    ]
                ),
           m
           )   =

    let
        val t1 = typeOf(equality,m)
        val t2 = typeOf(expr,m)
    in
        if t1 = t2 andalso t1 = INT then BOOL
        else ERROR
    end
    
| typeOf( itree(inode("equality",_),
                    [
                         equality, 
    			 itree(inode(“<=”, _), [] ),
                         expr
                    ]
                ),
           m
           ) =

    let
        val t1 = typeOf(equality,m)
        val t2 = typeOf(expr,m)
    in
        if t1 = t2 andalso t1 = INT then BOOL
        else ERROR
    end

| typeOf( itree(inode("equality",_),
                    [
                         equality, 
    			 itree(inode(“>”, _), [] ),
                         expr
                    ]
                ),
           m
           ) =

    let
        val t1 = typeOf(equality,m)
 		val t2 = typeOf(expr,m)
    in
        if t1 = t2 andalso t1 = INT then BOOL
        else ERROR
    end

| typeOf( itree(inode("equality",_),
                    [
                         equality, 
                         itree(inode(“>=”, _), [] ),
                         expr
                    ]
                ),
           m
           ) =
    let
        val t1 = typeOf(equality,m)
        val t2 = typeOf(expr,m)
    in
        if t1 = t2 andalso t1 = INT then BOOL
        else ERROR
    end
    
| typeOf( itree(inode("equality",_),
                    [
                    
                         expr
                    ]
                ),
           m
           ) =
    typeOf(expr,m)
(*expr ::= expr + term | expr - term | term*)
| typeOf( itree(inode("expr",_),
                    [
                         expr, 
                         itree(inode(“+”, _), [] ),
                         term
                    ]
                ),
           m
           ) = 

    let
        val t1 = typeOf(expr,m)
        val t2 = typeOf(term,m)
    in
        if t1 = t2 andalso t1 = INT then INT
        else ERROR
    end

| typeOf( itree(inode("expr",_),
                    [
                         expr, 
                         itree(inode(“-”, _), [] ),
                         term
                    ]
                ),
           m
           ) = 

    let
        val t1 = typeOf(expr,m)
        val t2 = typeOf(term,m)
    in
        if t1 = t2 andalso t1 = INT then INT
        else ERROR
    end

| typeOf( itree(inode("expr",_),
                    [
                         term
                    ]
                ),
           m
           ) = 
    typeOf(term,m)

(*term ::= term * complex | term / complex | term % complex | complex*)
| typeOf( itree(inode("term",_),
                    [
                         term, 
                         itree(inode(“*”, _), [] ),
                         complex
                    ]
                ),
           m
           ) = 

    let
        val t1 = typeOf(term,m)
        val t2 = typeOf(complex,m)
    in
        if t1 = t2 andalso t1 = INT then INT
        else ERROR
    end

| typeOf( itree(inode("term",_),
                    [
                         term, 
                          itree(inode(“/”, _), [] ),
                         complex
                    ]
                ),
           m
           ) = 

    let
        val t1 = typeOf(term,m)
        val t2 = typeOf(complex,m)
    in
        if t1 = t2 andalso t1 = INT then INT
        else ERROR
    end

| typeOf ( itree(inode("term",_),
                    [
                         term, 
                          itree(inode(“%”, _), [] ),
                         complex
                    ]
                ),
           m
           ) = 

    let
        val t1 = typeOf (term,m)
        val t2 = typeOf (complex,m)
    in
        if t1 = t2 andalso t1 = INT then INT
        else ERROR
    end

| typeOf ( itree(inode("term",_),
                    [
                         complex
                    ]
                ),
           m
           ) = 
     typeOf (complex,m)
(*complex ::= -complex | !complex | exponent*)
| typeOf ( itree(inode("complex",_),
                    [  
                         itree(inode(“-”, _), [] ),
                         complex
                    ]
                ),
           m
           )  = 
    let
        val t1 = typeOf(complex,m)
    in
        if t1 = INT then INT
        else ERROR
    end

| typeOf ( itree(inode("complex",_),
                    [  
                         itree(inode(“!”, _), [] ),
                         complex
                    ]
                ),
           m
           )  = 
    let
        val t1 = typeOf(complex,m)
    in
        if t1 = INT then INT
        else ERROR
    end

| typeOf ( itree(inode("complex",_),
                    [
                         exponent
                    ]
                ),
           m
           ) =
    typeOf(exponent,m)

(* exponent ::= factor ^ exponent | factor *)
| typeOf ( itree(inode("exponent",_),
		         [
			     factor,
			     itree(inode(“^”,_),children2),
			     exponent
		         ]
		  ),
	      m
	      ) = 

    let
        val t1 = typeOf(factor,m)
        val t2 = typeOf(exponent,m)
    in
        if t1 = t2 andalso t1 = INT then INT
        else ERROR
    end

| typeOf ( itree(inode("exponent",_),
		         [
			     factor
		         ]
		  ),
	      m
	      ) = typeOf(factor,m)
(* factor ::= integer | boolean | id | increment | (expression) | |expression| *)          
| typeOf ( itree(inode("factor",_),
		         [
			     integer
		         ]
		  ),
	      m
	 ) = INT
| typeOf ( itree(inode("factor",_),
		         [
			     boolean
		         ]
		  ),
	      m
	 )  = BOOL
| typeOf ( itree(inode("factor",_),
		         [
			     itree(inode("id", i1), [])
		         ]
		  ),
	      m
	 ) = getType(accessEnv(itree(inode("id", i1), []), m))

| typeOf ( itree(inode("factor",_),
		         [
			     increment
		         ]
		  ),
	       m
	  ) = typeOf(increment, m)
      
| typeOf ( itree(inode("factor",_),
		         [
			     itree(inode("(",_),[]),
			     expression,
			     itree(inode(")",_),[])
		         ]
		  ),
	       m
	  ) = typeOf(expression,m)
      
| typeOf ( itree(inode("factor",_),
		         [
			     itree(inode("|",_),[]),
			     expression,
			     itree(inode("|",_),[])
		         ]
		  ),
	       m
	  ) =
    let
        val t1 = typeOf(expression, m)
    in
        if t1 = INT then INT
        else ERROR
    end
  (* postIncr ::= id++ | id-- *)
  | typeOf ( itree(inode("postIncr",_),
                    [
                        itree(inode("id", i1), []),
                        itree(inode("++", _), [])
                    ]
                ),
           m
        ) = 
    let
        val t1 = typeOf(itree(inode("id", i1), []), m)
    in
        if t1 = INT then INT
        else ERROR
    end
    
  | typeOf ( itree(inode("postIncr",_),
                    [
                        itree(inode("id", i1), []),
                        itree(inode("--", _), [])
                    ]
                ),
           m
        ) = 
    let
        val t1 = typeOf(itree(inode("id", i1), []), m)
    in
        if t1 = INT then INT
        else ERROR
    end
  (* preIncr ::= ++id | --id *)      
  | typeOf ( itree(inode("preIncr",_),
                    [
                        itree(inode("++", _), []),
                        itree(inode("id", id1), [])
                    ]
                ),
           m
        ) = 
    let
        val t1 = typeOf(itree(inode("id", i1), []), m)
    in
        if t1 = INT then INT
        else ERROR
    end
  | typeOf ( itree(inode("preIncr",_),
                    [
                        itree(inode("--", _), []),
                        itree(inode("id", i1), [])
                    ]
                ),
           m
        ) = 
    let
        val t1 = typeOf(itree(inode("id", i1), []), m)
    in
        if t1 = INT then INT
        else ERROR
    end
(* =========================================================================================================== *)  
end (* struct *)
(* =========================================================================================================== *)








