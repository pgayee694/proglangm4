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


fun typeCheck( itree(inode("prog",_), [ stmt_list ] ), m) = m
  | typeCheck( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn typeCheck root = " ^ x_root ^ "\n\n")
  | typeCheck _ = raise Fail("Error in Model.typeCheck - this should never occur")


fun typeOf( itree(inode("expression",_),
                    [
                         itree(inode(“expression”, i1), c1), 
                         itree(inode(“||”, _), [] ),
                         itree(inode(“disjunction”, i2), c2)
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
                         itree(inode(“disjunction”, _), c1)
                    ]
                ),
           m
           ) 
           = 
    typeOf(disjunction,m)


| typeOf( itree(inode("disjunction",_),
                    [
                         itree(inode(“disjunction”, i1), c1), 
                         itree(inode(“&&”, _), [] ),
                         itree(inode(“conjunction”, i2), c2)
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
                         itree(inode(“conjunction”, i1), c1)
                    ]
                ),
           m
           ) =
    typeOf(conjunction,m)

| typeOf( itree(inode("conjunction",_),
                    [
                         itree(inode(“conjunction”, i1), c1), 
                         itree(inode(“!=”, _), [] ),
                         itree(inode(“equality”, i2), c2)
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
                         itree(inode(“conjunction”, i1), c1), 
                         itree(inode(“==”, _), [] ),
                         itree(inode(“equality”, i2), c2)
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
    
| E( itree(inode("conjunction",_),
                    [
                   
                         itree(inode(“equality”, i1), c1)
                    ]
                ),
           m
           ) =
    typeOf(equality,m)
    

| typeOf( itree(inode("equality",_),
                    [
                         itree(inode(“equality”, i1), c1), 
                         itree(inode(“<”, _), [] ),
                         itree(inode(“expr”, i2), c2)
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
                         itree(inode(“equality”, i1), c1), 
    itree(inode(“<=”, _), [] ),
                         itree(inode(“expr”, i2), c2)
                    ]
                ),
           m
           )) =

    let
        val t1 = typeOf(equality,m)
        val t2 = typeOf(expr,m)
    in
        if t1 = t2 andalso t1 = INT then BOOL
        else ERROR
    end

| typeOf( itree(inode("equality",_),
                    [
                         itree(inode(“equality”, i1), c1), 
    itree(inode(“>”, _), [] ),
                         itree(inode(“expr”, i2), c2)
                    ]
                ),
           m0
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
                         itree(inode(“equality”, i1), c1), 
                         itree(inode(“>=”, _), [] ),
                         itree(inode(“expr”, i2), c2)
                    ]
                ),
           m0
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
                    
                         itree(inode(“expr”, i1), c1)
                    ]
                ),
           m
           ) =
    typeOf(expr,m)

expr ::= expr + term | expr - term | term
| typeOf( itree(inode("expr",_),
                    [
                         itree(inode(“expr”, i1), c1), 
                         itree(inode(“+”, _), [] ),
                         itree(inode(“term”, i2), c2)
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
                         itree(inode(“expr”, i1), c1), 
                         itree(inode(“-”, _), [] ),
                         itree(inode(“term”, i2), c2)
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
                         itree(inode(“term”, i2), c2)
                    ]
                ),
           m
           ) = 
    typeOf(term,m)

| typeOf( itree(inode("term",_),
                    [
                         itree(inode("term", i1), c1), 
                          itree(inode(“*”, _), [] ),
                         itree(inode(“complex”, i2), c2)
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
                         itree(inode("term", i1), c1), 
                          itree(inode(“/”, _), [] ),
                         itree(inode(“complex”, i2), c2)
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
                         itree(inode("term", i1), c1), 
                          itree(inode(“%”, _), [] ),
                         itree(inode(“complex”, i2), c2)
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
                         itree(inode(“complex”, i2), c2)
                    ]
                ),
           m
           ) = 
     typeOf(complex,m)

complex ::= -complex | !complex | exponent



| typeOf( itree(inode("complex",_),
                    [  
                         itree(inode(“-”, _), [] ),
                         itree(inode(“complex”, i2), c2)
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

| typeOf( itree(inode("complex",_),
                    [  
                         itree(inode(“!”, _), [] ),
                         itree(inode(“complex”, i2), c2)
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

| typeOf( itree(inode("complex",_),
                    [
                         itree(inode(“exponent”, i2), c2)
                    ]
                ),
           m
           ) =
    typeOf(exponent,m)

exponent ::= factor ^ exponent | factor

| typeOf( itree(inode("exponent",_),
		         [
			     itree(inode(“factor”,nodeInfo1),children1),
			     itree(inode(“^”,_),children2),
			     itree(inode(“exponent”,nodeInfo3),children3)
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

| typeOf( itree(inode("exponent",_),
		         [
			     itree(inode(“factor”,nodeInfo1),children1)
		         ]
		  ),
	      m
	      ) = typeOf(factor,m)
          
| typeOf( itree(inode("factor",_),
		         [
			     itree(inode( “integer”,_),children1)
		         ]
		  ),
	      m
	 ) = INT
| typeOf( itree(inode("factor",_),
		         [
			     itree(inode( "boolean", info),children1)
		         ]
		  ),
	      m
	 )  = BOOL
| typeOf( itree(inode("factor",_),
		         [
			     itree(inode( "id", info),children1)
		         ]
		  ),
	      m
	 ) = getType(accessEnv(id, m))

| typeOf( itree(inode("factor",_),
		         [
			     itree(inode("increment", nodeInfo1),children1)
		         ]
		  ),
	       m
	  ) = typeOf(increment, m)
      
| typeOf( itree(inode("factor",_),
		         [
			     itree(inode("(",_),children1),
			     itree(inode("expression", nodeInfo2),children2),
			     itree(inode(")",_),children3)
		         ]
		  ),
	       m
	  ) = typeOf(expression,m)
      
| typeOf( itree(inode("factor",_),
		         [
			     itree(inode("|",_),children1),
			     itree(inode("expression", nodeInfo2),children2),
			     itree(inode("|",_),children3)
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

(* =========================================================================================================== *)  
end (* struct *)
(* =========================================================================================================== *)








