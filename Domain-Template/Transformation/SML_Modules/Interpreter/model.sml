(* =========================================================================================================== *)
exception runtime_error;

structure Model =

struct 

(* =========================================================================================================== *)
(* This function may be useful to get the leaf node of a tree -- which is always a string (even for integers).
   It is up to the interpreter to translate values accordingly (e.g., string to integer and string to boolean).
   
   Consult (i.e., open Int and open Bool) the SML structures Int and Bool for functions that can help with 
   this translation. 
*)
fun getLeaf( term ) = CONCRETE.leavesToStringRaw term 


(* For your typeChecker you may want to have a datatype that defines the types 
  (i.e., integer, boolean and error) in your language. *)
datatype types = INT | BOOL | ERROR;


(* It is recommended that your model store integers and Booleans in an internal form (i.e., as terms belonging to
   a userdefined datatype (e.g., denotable_value). If this is done, the store can be modeled as a list of such values.
*)
datatype denotable_value =  Boolean of bool 
                          | Integer of int;


type loc   = int
type env   = (string * types * loc) list
type store = (loc * denotable_value) list


(* The model defined here is a triple consisting of an environment, an address counter, and a store. The environment
   and the store are lists similar to what we have used in class. The address counter serves as an implementation of
   new(). Note that, depending on your implementation, this counter either contains the address of (1) the
   next available memory location, or (2) the last used memory location -- it all depends on when the counter is 
   incremented. *)
val initialModel = ( []:env, 0:loc, []:store )

(* this is strictly for adding in new values *)
fun updateEnv(id, a_type, a_location, (env, loc, s)) = ((id, a_type, a_location)::env, loc, s);

fun updateStore(a_location, a_value, (env, loc, [])) = (env, loc, [(a_location, a_value)])
  | updateStore(a_location, a_value, (env, loc, (loc1, v1)::s)) = if a_location = loc1 then (env, loc, (a_location, a_value)::s) else
        let
            val (env2, loc2, s2) = updateStore(a_location, a_value, (env, loc, s))
        in
            (env2, loc2, (loc1, v1)::s2)
        end;
        
fun accessEnv(id1,([],loc, s)) = raise Domain
 | accessEnv(id1, ((id2, a_type, a_location)::env, loc, s)) =
      if id1 = id2 then (a_type, a_location)
      else accessEnv(id1, (env, loc, s))

fun accessStore(loc1, (env, loc, [])) = raise Domain
  | accessStore(loc1, (env, loc, (loc2, d)::s)) = 
      if loc1 = loc2 then d else accessStore(loc1,(env, loc, s))

fun getLoc (a_type, a_location) = a_location;

fun getType (a_type, a_location) = a_type;

fun getAddressCounter (env, loc, s) = loc;

fun valToString (Boolean(v)) = Bool.toString v
  | valToString (Integer(v)) = Int.toString v;
  
fun error msg = ( print msg; raise runtime_error );
  
fun toInt(Boolean(x)) = error "not an int"
  | toInt(Integer(x)) = x;

fun toBool (Integer(x)) = error "not a bool"
  | toBool (Boolean(x)) = x;

fun typeToString BOOL = "BOOL"
  | typeToString INT = "INT"
  | typeToString ERROR = "ERROR";
  
fun envItemToString (id, t, loc) = "( " ^ id ^ ", " ^ typeToString t ^ ", " ^ Int.toString loc ^ " )";

fun denotableToString (Boolean(x)) = Bool.toString x
  | denotableToString (Integer(x)) = Int.toString x;
  
fun storeItemToString (loc, v) = "( " ^ Int.toString loc ^ ", " ^ denotableToString v ^ " )";

fun printEnv [] = print "\n"
  | printEnv (item::env) = 
        (
            print("\n" ^ envItemToString item);
            printEnv env
        );

fun printStore [] = print "\n"
  | printStore (item::store) =
        (
            print("\n" ^ storeItemToString item);
            printStore store
        );

fun printModel (env, loc, s) =
    (
        print("ENV");
        printEnv(env);
        
        print("\n");
        print("ADDRESS COUNTER\n");
        print(Int.toString loc ^ "\n");
        
        print("\n");
        print("STORE");
        printStore s   
    );

(* =========================================================================================================== *)
end; (* struct *) 
(* =========================================================================================================== *)
