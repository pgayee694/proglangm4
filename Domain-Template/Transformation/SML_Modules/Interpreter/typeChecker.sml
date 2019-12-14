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

(* expression ::= expression || disjunction | disjunction *)
fun typeOf( itree(inode("expression",_),
                    [
                         expression, 
                         itree(inode("||", _), [] ),
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
                         itree(inode("&&", _), [] ),
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
           ) = typeOf(conjunction,m)
    
(*conjunction ::= conjunction != equality | conjunction == equality | equality*)
| typeOf( itree(inode("conjunction",_),
                    [
                         conjunction, 
                         itree(inode("!=", _), [] ),
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
                         itree(inode("==", _), [] ),
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
                         itree(inode("<", _), [] ),
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
    			 itree(inode("<=", _), [] ),
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
    			 itree(inode(">", _), [] ),
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
                         itree(inode(">=", _), [] ),
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
                         itree(inode("+", _), [] ),
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
                         itree(inode("-", _), [] ),
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
                         itree(inode("*", _), [] ),
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
                          itree(inode("/", _), [] ),
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
                          itree(inode("%", _), [] ),
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
                         itree(inode("-", _), [] ),
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
                         itree(inode("!", _), [] ),
                         complex
                    ]
                ),
           m
           )  = 
    let
        val t1 = typeOf(complex,m)
    in
        if t1 = BOOL then BOOL
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
			     itree(inode("^",_),children2),
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
			     itree(inode("id", i1), [])
		         ]
		  ),
	      m
	 ) = getType(accessEnv(getLeaf(itree(inode("id", i1), [])), m))
      
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
    
| typeOf ( itree(inode("factor",_),
		         [
			     itree(inode("integer", _), _)
		         ]
		  ),
	      m
	 ) = INT
         
| typeOf ( itree(inode("factor",_),
		         [
			     itree(inode("true", _), _)
		         ]
		  ),
	      m
	 )  = BOOL
 
| typeOf ( itree(inode("factor",_),
		         [
			     itree(inode("false", _), _)
		         ]
		  ),
	      m
	 )  = BOOL
         
| typeOf ( itree(inode("factor",_),
		         [
			     increment
		         ]
		  ),
	       m
	  ) = typeOf(increment, m)
    
  (* postIncr ::= id++ | id-- *)
  | typeOf ( itree(inode("postIncr",_),
                    [
                        itree(inode("id", i1), c),
                        itree(inode("++", _), [])
                    ]
                ),
           m
        ) = 
    let
        val t1 = typeOf(itree(inode("id", i1), c), m)
    in
        if t1 = INT then INT
        else ERROR
    end
    
  | typeOf ( itree(inode("postIncr",_),
                    [
                        itree(inode("id", i1), c),
                        itree(inode("--", _), [])
                    ]
                ),
           m
        ) = 
    let
        val t1 = typeOf(itree(inode("id", i1), c), m)
    in
        if t1 = INT then INT
        else ERROR
    end
  (* preIncr ::= ++id | --id *)      
  | typeOf ( itree(inode("preIncr",_),
                    [
                        itree(inode("++", _), []),
                        id_node
                    ]
                ),
           m
        ) = 
    let
        val t1 = typeOf(id_node, m)
    in
        if t1 = INT then INT
        else ERROR
    end
    
  | typeOf ( itree(inode("preIncr",_),
                    [
                        itree(inode("--", _), []),
                        id as itree(inode("id", i1), c)
                    ]
                ),
           m
        ) = 
    let
        val t1 = typeOf(id, m)
    in
        if t1 = INT then INT
        else ERROR
    end
    
  | typeOf ( id as itree(inode("id", i1), c), m) =
        let
            val id_val = getLeaf(id)
            val t = getType(accessEnv(id_val, m))
        in
            t
        end
        
  | typeOf( itree(inode(x_root,_),children), _) = raise General.Fail("\n\nIn typeOf root = " ^ x_root ^ "\n\n")
  | typeOf _ = raise Fail("Error in Model.typeOf - this should never occur")
  
fun typeCheck( itree(inode("stmtList",_), 
                    [
                         stmt,
                         stmtList
                    ]
                ), m0 ) =
    let
        val m1 = typeCheck(stmt, m0)
        val m2 = typeCheck(stmtList, m1)
    in
        m2
    end
    
| typeCheck( itree(inode("stmtList",_), 
                    [
                         epsilon
                    ]
                ), m0 ) = m0
                
| typeCheck( itree(inode("stmt",_), 
                    [
                         stmt,
                         itree(inode(";",_), [] )
                    ]
                ), m0 ) =
    let
        val m1 = typeCheck(stmt, m0)
    in
        m1
    end
 
| typeCheck( itree(inode("stmt",_), 
                    [
                         block
                    ]
                ), m0 ) =
    let
        val m1 = typeCheck(block, m0)
    in
        m1
    end
    
| typeCheck( itree(inode("dec",_), 
                    [
                         itree(inode("int",_), [] ),
                         id_node
                    ]
                ),
            (env, loc, s)
        ) = let 
                val id = getLeaf(id_node)
            in
                updateEnv(id, INT, loc, (env, loc+1, s))
            end
                
| typeCheck( itree(inode("dec",_), 
                    [
                         itree(inode("bool",_), [] ),
                         id_node
                    ]
                ),
        (env, loc, s)
        ) = let
                val id = getLeaf(id_node)
            in
                updateEnv(id, BOOL, loc, (env, loc+1, s))
            end
                
| typeCheck( itree(inode("dec",_), 
                    [
                         itree(inode("int",_), [] ),
                         id_node,
                         itree(inode("=",_), [] ),
                         expression
                    ]
                ), (env, loc, s) ) =
    let
        val id = getLeaf(id_node)
        val t1 = typeOf(expression, (env, loc, s))
	val m1 = updateEnv(id, INT, loc, (env, loc+1, s))
    in
        if t1 = INT then m1 else raise model_error
    end
    
| typeCheck( itree(inode("dec",_), 
                    [
                         itree(inode("bool",_), [] ),
                         id_node,
                         itree(inode("=",_), [] ),
                         expression
                    ]
                ), (env, loc, s) ) =
    let
        val id = getLeaf(id_node)
        val t1 = typeOf(expression, (env, loc, s))
	val m1 = updateEnv(id, BOOL, loc, (env, loc+1, s))
    in
        if t1 = BOOL then m1 else raise model_error
    end
    
| typeCheck( itree(inode("assign",_), 
                    [
                         id_node,
                         itree(inode("=",_), [] ),
                         expression
                    ]
                ), m0 ) =
    let
        val id = getLeaf(id_node)
        val t1 = typeOf(expression, m0)
	val t2 = getType(accessEnv(id, m0))
    in
        if t1 = t2 then m0
	else raise model_error
    end
    
| typeCheck( itree(inode("cond",_), 
                    [
                         itree(inode("if",_), [] ),
                         itree(inode("(",_), [] ),
                         expression,
                         itree(inode(")",_), [] ),
                         block
                    ]
                ), m0 ) =
    let
        val t = typeOf(expression, m0)
	val m1 = typeCheck(block, m0)
    in
        if t = BOOL then m0 else raise model_error
    end
    
| typeCheck( itree(inode("cond", _),
                    [
                        itree(inode("if",_), [] ),
                        itree(inode("(",_), [] ),
                        expression,
                        itree(inode(")",_), [] ),
                        block1,
                        itree(inode("else", _), []),
                        block2
                    ]
                ),
            m0
        ) = let
                val t = typeOf(expression, m0)
                val m1 = typeCheck(block1, m0)
                val m2 = typeCheck(block2, m0)
            in
                if t = BOOL then m0 else raise model_error
            end
    
| typeCheck( itree(inode("increment",_), 
                    [
                         increment
                    ]
                ), m0 ) =
    let
	val t1 = typeOf(increment, m0)
    in
        if t1 = INT then m0 else raise model_error
    end
    
| typeCheck( itree(inode("iter",_), 
                    [
                         itree(inode("while",_), [] ),
                         itree(inode("(",_), [] ),
                         expression,
                         itree(inode(")",_), [] ),
                         block
                    ]
                ), m0 ) =
    let
	val t = typeOf(expression, m0)
	val m1 = typeCheck(block, m0)
    in
        if t = BOOL then m0 else raise model_error
    end
| typeCheck( itree(inode("iter",_), 
                    [
                         itree(inode("for",_), [] ),
                         itree(inode("(",_), [] ),
                         assign,
                         itree(inode(";",_), [] ),
                         expression,
                         itree(inode(";",_), [] ),
                         increment,
                         itree(inode(")",_), [] ),
                         block
                    ]
                ), m0 ) =
    let
	val m1 = typeCheck(assign, m0)
	val t = typeOf(expression, m0)
	val m2 = typeCheck(increment, m0)
	val m3 = typeCheck(block, m0)
    in
        if t = BOOL then m0 else raise model_error
    end
| typeCheck( itree(inode("block",_), 
                    [
                         itree(inode("{", _), [] ),
                         stmtList,
                         itree(inode("}", _), [] )
                    ]
                ), m0 ) =
    let
        val m1 = typeCheck(stmtList, m0)
    in
        m1
    end

| typeCheck( itree(inode("printExpression",_), 
                    [
                         itree(inode("print",info1), [] ),
                         expression
                    ]
                ), m0 ) = 
            (
                typeOf(expression, m0);
                m0
            )

  | typeCheck( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn typeCheck root = " ^ x_root ^ "\n\n")
  | typeCheck _ = raise Fail("Error in Model.typeCheck - this should never occur")
  
(* =========================================================================================================== *)  
end (* struct *)
(* =========================================================================================================== *)