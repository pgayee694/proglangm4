(* =========================================================================================================== *)
structure Semantics =
struct


(* This makes contents of the Model structure directly accessible (i.e., the prefix "Model." is not needed. *)            
open Model; 
            
(* This makes the internal representation of parse trees directly accessible. *)            
open CONCRETE_REPRESENTATION;

(* The following tree structure, defined in the CONCERETE_REPRESENTATION structure, is used in the TL System:

    datatype NODE_INFO = info of { id : IntInf.int, line : int * int , column : int * int, label : string };
	datatype INODE = inode of string * NODE_INFO
	                 | ...  
															
	datatype ITREE = itree of INODE * ITREE list;
*)


(* =========================================================================================================== *)
(* Here is where you add the M and E (as well as any other) definitions you developed in M2. The primary challenge here
   is to translate the parse expression notation we used in M2 to the actual SML tree patterns used in the TL System. 
   
   Example:
   
   M1: <stmtList> ::= <stmt> ";" <stmList>
   
   M2: M( [[ stmt_1 ; stmtList_1 ]], m) = M(stmtList_1, M(stmt_1,m))
    
   M4: 
        M( itree(inode("stmtList",_),
                    [
                        stmt,       (* this is a regular variable in SML and has no other special meaning *)
                        semiColon,  (* this is a regular variable in SML and has no other special meaning *)
                        stmtList    (* this is a regular variable in SML and has no other special meaning *) 
                    ]
                ),
           m
           
        ) = M( stmtList, M(stmt, m) )  
        
        
        Note that the above M4 implementation will match ANY tree whose root is "stmtList" having three children.
        Such matches can be further constrained by explicitly exposing more of the tree structure.
        
        M( itree(inode("stmtList",_),
                    [
                        stmt,                       (* this is a regular variable in SML and has no other special meaning *)
                        itree(inode(";",_), [] ),   (* A semi-colon is a leaf node. All leaf nodes have an empty children list. *)
                        
                        stmtList                    (* this is a regular variable in SML and has no other special meaning *) 
                    ]
                ),
           m
           
        ) = M( stmtList, M(stmt, m) )  
        
        Note that the above M4 implementation will match ANY tree satisifying the following constraints:
            (1) the root is "stmtList"
            (2) the root has three children
            (3) the second child is a semi-colon   
*)

(*
fun M(  itree(inode("stmtList",_), 
                [ 
                    stmt_list
                ] 
             ), 
        m
    ) = m *)

(* or *)
fun E( itree(inode("expression",_),
                    [
                         itree(inode("expression", i1), c1), 
                         itree(inode("||", _), [] ),
                         itree(inode("disjunction", i2), c2)
                    ]
                ),
           m0
           ) = let
                    val (v1,m1) = E(itree(inode("expression", i1), c1),m0)		
               in 
                    if v1 then (v1, m1) else E(itree(inode("disjunction", i2), c2),m1)
               end
               
  |  E( itree(inode("expression",_),
                    [
                         itree(inode("disjunction", i1), c1)
                    ]
                ),
           m0
           )  = E(itree(inode("disjunction", i1), c1),m0)
           
  (* and *)         
  | E( itree(inode("disjunction",_),
                    [
                         itree(inode("disjunction", i1), c1), 
                         itree(inode("&&", _), [] ),
                         itree(inode("conjunction", i2), c2)
                    ]
                ),
           m0
           ) = let
                    val (v1,m1) = E(itree(inode("disjunction", i1), c1),m0)
               in 
                    if v1 then E(itree(inode("conjunction", i2), c2),m1) else (v1,m1)
               end
        
  | E( itree(inode("disjunction",_),
                    [
                         itree(inode("conjunction", i1), c1)
                    ]
                ),
           m0
           ) = E(itree(inode("conjunction", i1), c1), m0)
          
  (* not equal *)        
  | E( itree(inode("conjunction",_),
                    [
                         itree(inode("conjunction", i1), c1), 
                         itree(inode("!=", _), [] ),
                         itree(inode("equality", i2), c2)
                    ]
                ),
           m0
           ) = let
                    val (v1,m1) = E(itree(inode("conjunction", i1), c1),m0)
                    val (v2, m2) = E(itree(inode("equality", i2), c2),m1)
                in 
                    (v1 <> v2, m2)
                end

  (* equal *)
  | E( itree(inode("conjunction",_),
                    [
                         itree(inode("conjunction", i1), c1), 
                         itree(inode("==", _), [] ),
                         itree(inode("equality", i2), c2)
                    ]
                ),
           m0
           )  = let
                    val (v1,m1) = E(itree(inode("conjunction", i1), c1),m0)
                    val (v2, m2) = E(itree(inode("equality", i2), c2),m1)
                in 
                    (v1 <> v2, m2)
                end
                
  | E( itree(inode("conjunction",_),
                    [
                   
                         itree(inode("equality", i1), c1)
                    ]
                ),
           m0
           ) = E(itree(inode("equality", i1), c1), m0)

  (* less than *)
  | E( itree(inode("equality",_),
                    [
                         itree(inode("equality", i1), c1), 
    itree(inode("<", _), [] ),
                         itree(inode("expr", i2), c2)
                    ]
                ),
           m0
           )   = let
                    val (v1,m1) = E(itree(inode("equality", i1), c1),m0)
                    val (v2, m2) = E(itree(inode("expr", i2), c2),m1)
                 in 
                    (v1 < v2, m2)
                end
  
  (* less than equal *)
  | E( itree(inode("equality",_),
                    [
                         itree(inode("equality", i1), c1), 
                         itree(inode("<=", _), [] ),
                         itree(inode("expr", i2), c2)
                    ]
                ),
                m0
           ) = let
                    val (v1,m1) = E(itree(inode("equality", i1), c1),m0)
                    val (v2, m2) = E(itree(inode("expr", i2), c2),m1)
                in 
                    (v1 <= v2, m2)
                end
      
  (* greater than *)
  | E( itree(inode("equality",_),
                    [
                         itree(inode("equality", i1), c1), 
                         itree(inode(">", _), [] ),
                         itree(inode("expr", i2), c2)
                    ]
                ),
            m0
           ) = let
                    val (v1,m1) = E(itree(inode("equality", i1), c1),m0)
                    val (v2, m2) = E(itree(inode("expr", i2), c2),m1)
                in 
                    (v1 > v2, m2)
                end
  
  (*greater than equal *)
  | E( itree(inode("equality",_),
                    [
                         itree(inode("equality", i1), c1), 
                         itree(inode(">=", _), [] ),
                         itree(inode("expr", i2), c2)
                    ]
                ),
            m0
           ) = let
                    val (v1,m1) = E(itree(inode("equality", i1), c1),m0)
                    val (v2, m2) = E(itree(inode("expr", i2), c2),m1)
                in 
                    (v1 >= v2, m2)
            end
            
  | E( itree(inode("equality",_),
                    [
                    
                         itree(inode("expr", i1), c1)
                    ]
                ),
           m0
           ) = E( itree(inode("expr", i1), c1) ,m0)
           
  (* plus *)         
  | E( itree(inode("expr",_),
                    [
                         itree(inode("expr", i1), c1), 
                         itree(inode("+", _), [] ),
                         itree(inode("term", i2), c2)
                    ]
                ),
           m0
           ) = let
                    val (v1,m1) = E( itree(inode("expr", i1), c1),m0)
                    val (v2,m2) = E(itree(inode("term", i2), c2),m1)
               in
                    (v1 + v2,m2)
               end
               
  (* minus *)             
  | E( itree(inode("expr",_),
                    [
                         itree(inode("expr", i1), c1), 
                         itree(inode("-", _), [] ),
                         itree(inode("term", i2), c2)
                    ]
                ),
            m0
           ) = let
                    val (v1,m1) = E( itree(inode("expr", i1), c1),m0)
                    val (v2,m2) = E(itree(inode("term", i2), c2),m1)
                in
                    (v1 - v2,m2)
                end
                
  | E( itree(inode("expr",_),
                    [
                      
                         itree(inode("term", i2), c2)
                    ]
                ),
            m0
           )= E(itree(inode("term", i2), c2),m0)

  | E( itree(inode("term",_),
                    [
                    
                         itree(inode("complex", i1), c1)
                    ]
                ),
           m0
           ) = E(itree(inode("complex", i1), c1),m0)

  | E( itree(inode("term",_),
                    [
                         itree(inode("term", i1), c1), 
                         itree(inode("*", _), [] ),
                         itree(inode("complex", i2), c2)
                    ]
                ),
           m0
           ) =  let
                    val (v1,m1) = E(itree(inode("term", i1), c1),m0)
                    val (v2,m2) = E(itree(inode("complex", i2), c2),m1)
                in
                    (v1 * v2,m2)
                end
                
  | E( itree(inode("term",_),
                    [
                         itree(inode("term", i1), c1), 
                         itree(inode("/", _), [] ),
                         itree(inode("complex", i2), c2)
                    ]
                ),
           m0
           ) = let
                    val (v1,m1) = E(itree(inode("term", i1), c1),m0)
                    val (v2,m2) = E(itree(inode("complex", i2), c2),m1)
                in
                    (v1 / v2,m2)
                end

  | E( itree(inode("term",_),
                    [
                        itree(inode("term", i1), c1), 
                        itree(inode("%", _), [] ),
                        itree(inode("complex", i2), c2)
                    ]
                ),
           m0
           ) = let
                    val (v1,m1) = E(itree(inode("term", i1), c1),m0)
                    val (v2,m2) = E(itree(inode("complex", i2), c2),m1)
                in
                    (v1 mod v2,m2)
                end

  | E( itree(inode("complex",_),
                    [
                        itree(inode("exponent", i2), c2)
                    ]
                ),
            m0
           ) = E(itree(inode("exponent", i2), c2), m0)

  | E( itree(inode("complex",_),
                    [
                        itree(inode("-", _), [] ),
                        itree(inode("complex", i2), c2)
                    ]
                ),
            m0
           )  = let
                    val (v,m1) = E(itree(inode("complex", i2), c2),m0)
                in
                    (-1 * v, m1)
                end 

  | E( itree(inode("complex",_),
                    [
                        itree(inode("!", _), [] ),
                        itree(inode("complex", i2), c2)
                    ]
                ),
            m0
           ) = let
                    val (v,m1) = E(itree(inode("complex", i2), c2),m0)
               in
                    (if v then false else true, m1)
               end
   
  | E( itree(inode("exponent",_),
		         [
			     itree(inode("factor",nodeInfo1),children1),
			     itree(inode("^",_),children2),
			     itree(inode("exponent",nodeInfo3),children3)
		         ]
		  ),
                m0
	      ) = let
                        val (v1,m1) = E(itree(inode("factor",nodeInfo1),children1),m0)
                        val (v2, m2) = E(itree(inode("exponent",nodeInfo3),children3),m1)
		  in 
                      (pow(v1,v2), m2)
                  end
                  
  | E( itree(inode("exponent",_),
		         [
			     itree(inode("factor",nodeInfo1),children1)
		         ]
		  ),
                m0
	      ) = E(itree(inode("factor",nodeInfo1),children1), m0)

  | E( itree(inode("factor",_),
		         [
			     itree(inode( "integer", info), children1)
		         ]
		  ),
	      m
	 ) = let
                    val v = getLeaf(itree(inode( "integer", info),children1))
                    val int = valOf(Int.fromString(v))
	      in
	        (Integer int, m)
	end

	| E( itree(inode("factor",_),
		         [
			     itree(inode( "boolean", info),children1)
		         ]
		  ),
	      m
	 ) = let
	         val v = getLeaf(itree(inode( "boolean", info),children1))
	         val bool = valOf(Bool.fromString(v))
	      in
	        (Boolean bool, m)
	end
	| E( itree(inode("factor",_),
		         [
			     itree(inode( "id", info),children1)
		         ]
		  ),
	      m
	 ) = let
	         val id = getLeaf(itree(inode( "id", info),children1))
	         val loc = getLoc(accessEnv(id,m))
	         val v = accessStore(loc,m)
	      in
	        (v, m)
	end

  | E( itree(inode("factor",_),
		         [
			     itree(inode("(",_),children1),
			     itree(inode("expression", nodeInfo2),children2),
			     itree(inode(")",_),children3)
		         ]
		  ),
	       m
	  ) = E(itree(inode("expression", nodeInfo2),children2), m)

  | E( itree(inode("factor",_),
		         [
			     itree(inode("|",_),children1),
			     itree(inode("expression", nodeInfo2),children2),
			     itree(inode("|",_),children3)
		         ]
		  ),
	       m
	  ) = E(itree(inode("expression", nodeInfo2),children2), m)

  | E( itree(inode("factor",_),
		         [
			     itree(inode("increment", nodeInfo1),children1)
		         ]
		  ),
	       m
	  ) = E(itree(inode("increment", nodeInfo1),children1), m)

  | E ( itree(inode("postIncr",_),
                    [
                        itree(inode("id_node", i1), c1),
                        itree(inode("++", _), [])
                    ]
                ),
           m0
        ) = let
                val id = getLeaf(itree(inode("id_node", i1), c1))
		val (v1,m1) = E(id,m0)
		val loc = getLoc(accessEnv(id, m1)) 
		val m2 = updateStore(loc, v1 + 1, m2)
	in
		(v1, m2)
	end
  | E ( itree(inode("postIncr",_),
                    [
                        itree(inode("id_node", i1), c1),
                        itree(inode("--", _), [])
                    ]
                ),
           m0
        ) = let
                val id = getLeaf(itree(inode("id_node", i1), c1))
		val (v1,m1) = E(id,m0)
		val loc = getLoc(accessEnv(id, m1))
		val m2 = updateStore(loc, v1 - 1, m2)
	in
		(v1, m2)
	end
        
  | E ( itree(inode("preIncr",_),
                    [
                        itree(inode("++", _), []),
                        itree(inode("id_node", id1), c1)
                    ]
                ),
           m0
        ) = let
                val id = getLeaf(itree(inode("id_node", id1), c1))
		val (v1,m1) = E(id,m0)
		val loc = getLoc(accessEnv(id, m1))
		val m2 = updateStore(loc, v1 + 1, m2)
	in
		(v1 + 1,m2)
	end
  | E ( itree(inode("preIncr",_),
                    [
                        itree(inode("--", _), []),
                        itree(inode("id_node", i1), c1)
                    ]
                ),
           m0
        ) = let
                val id = getLeaf(itree(inode("id_node", i1), c1))
		val (v1,m1) = E(id,m0)
		val loc = getLoc(accessEnv(id, m1))
		val m2 = updateStore(loc, v1 + 1, m2)
	in
		(v1 - 1,m2)
	end

fun O( expression1, increment1, block1, m0 ) =
    let
        val (v1, m1) = E( expression1, m0 )
    in
        if v1 then
            let
                val m2 = M( block1, m1 )
                val (v3, m3) = E( increment1, m2 )
                val m4 = O( expression1, increment1, block1, m3) 
            in
                m4
            end
        else m1
    end

fun M( itree(inode("stmtList", _),
                    [
                         itree(inode("stmt", nodeInfo1), children1),
                         itree(inode("stmtList", nodeInfo2), children2)
                    ]
                ),
           m0
           ) = let
                 val m1 = M( itree(inode("stmt", nodeInfo1), children1), m0)
                 val m2 = M( itree(inode("stmtList", nodeInfo2), children2), m1 )
                 in
                   m2
               end
               
  | M( itree(inode("stmtList",_),
                    [
                        itree(inode("epsilon", _), [])
                    ]
                ),
           m0
           ) = m0
           
  | M( itree(inode("epsilon",_),
                    [
                    ]
                ),
           m0
           ) = m0
           
  | M( itree(inode("stmt", _),
                    [
                        stmt, (* dec, cond, iter, etc *)                     
                        itree(inode(";", _), [])
                    ]
                ),
           m0
        ) = M( stmt, m0)
  
  | M ( itree(inode("iter",info1),
                    [
                        itree(inode("while", info2), children2),
                        itree(inode("(",info3), []),
                        itree(inode("expression", info4), children4),
                        itree(inode(")",info5), [] ),
                        itree(inode("block", info6), children6)
                    ]
                ),
           m0
        ) = let
		val (v, m1) = E(itree(inode("expression", info4), children4), m0 )
	in
	    if v then M(itree(inode("iter",info1),
                    [
                        itree(inode("while", info2), children2),
                        itree(inode("(",info3), []),
                        itree(inode("expression", info4), children4),
                        itree(inode(")",info5), [] ),
                        itree(inode("block", info6), children6)
                    ]
                ),
                 M(itree(inode("block", info6), children6), m1))
	    else m1
	end
        
  | M ( itree(inode("iter",_),
                    [
                        itree(inode("for", _), []),
                        itree(inode("(",_), [] ),
                        itree(inode("assign", info1), children1),
                        itree(inode(";",_), [] ),
                        itree(inode("expression", info2), children2),
                        itree(inode(";",_), [] ),
                        itree(inode("increment", info3), children3),
                        itree(inode(";",_), [] ),
                        itree(inode("block", info4), children4)
                    ]
                ),
           m0
        ) = let
		val m1 = M(itree(inode("assign", info1), children1), m0 )
		val m2 = O(itree(inode("expression", info2), children2), itree(inode("increment", info3), children3), itree(inode("block", info4), children4), m1 )
           in
	 	m2
	end
  
  | M ( itree(inode("dec",_),
                    [
                        itree(inode("int", _), []),
                        id_term
                    ]
                ),
           (env, loc, s)
        ) = let
                val id = getLeaf(id_term)
            in
                updateEnv( id, INT, loc, (env, loc+1, s))
            end

  | M ( itree(inode("dec",_),
                    [
                        itree(inode("int", _), []),
                        id_term,
                        itree(inode("=", _), []),
                        expression_node
                    ]
                ),
           (env, loc, s)
        ) = let
                val id = getLeaf(id_term)
		val m1 = updateEnv( id, INT, loc, (env, loc+1, s) )
		val (v, m2) = E( expression_node, m1 )
		val loc = getLoc(accessEnv( id, m2 ))
		val m3 = updateStore( loc, v, m2 )
	in
		m3
	end

  | M ( itree(inode("dec",_),
                    [
                        itree(inode("bool", _), []),
                        id_term
                    ]
                ),
           (env, loc, s)
        ) = let
                val id = getLeaf(id_term)
            in
                updateEnv( id, BOOL, loc, (env, loc+1, s) )
            end
  | M ( itree(inode("dec",_),
                    [
                        itree(inode("bool", _), []),
                        id_term,
                        itree(inode("=", _), []),
                        expression_node
                    ]
                ),
            (env, loc, s)
        ) = let
                val id = getLeaf(id_term)
		val m1 = updateEnv( id, BOOL, loc, (env, loc+1, s) )
		val (v, m2) = E( expression_node, m1 )
		val loc = getLoc(accessEnv( id, m2 ))
		val m3 = updateStore( loc, v, m2 )
	in
		m3
	end

  | M ( itree(inode("cond",_),
                    [
                        itree(inode("if", _), []),     
                        itree(inode("(", _), []),
                        expression_node,
                        itree(inode(")", _), []),
                        itree(inode("block", info2), children2)
                    ]
                ),
           m0
        ) = let
                val (v, m1) = E( expression_node, m0 )
            in
                if v then M ( itree(inode("block", info2), children2), m1)
                else m1
            end 

  | M ( itree(inode("increment",_),
                    [
                        incr_node
                    ]
                ),
           m0
        ) = let 
		val m1 = M( incr_node, m0 )
	in
		m1
	end

  | M ( itree(inode("assign",_),
                    [
                        id_node,
                        itree(inode("=", _), []),
                        expression_node
                    ]
                ),
           m0
        ) = let
                val id = getLeaf(id_node)
                val (v, m1) = E( expression_node, m0 )
                val loc = getLoc(accessEnv( id, m1 ))
                val m2 = updateStore( loc, v, m1 )
            in
                m2
            end

  | M ( itree(inode("block",_),
                    [
                        itree(inode("{", _), []),
                        stmtList_node,
                        itree(inode("}", _), [])
                    ]
                ),
           (env0, loc, s0)
        ) = let
                val (env1, loc1, s1) = M(stmtList_node, (env0,loc, s0))
                val m2 = ( env0, loc, s1)
            in
                m2
            end

  | M ( itree(inode("printExpression",_),
                    [
                        itree(inode("print", _), []),
                        expression_node
                    ]
                ),
           m0
        ) = let
                val (v, m1)  = E( expression_node, m0 )
            in
                print(valToString(v));
                m1
            end



  | M(  itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn M root = " ^ x_root ^ "\n\n")
  
  | M _ = raise Fail("error in Semantics.M - this should never occur")

(* =========================================================================================================== *)
end (* struct *)
(* =========================================================================================================== *)








