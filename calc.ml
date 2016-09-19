(* A simple infix calculator lexer/parser.
 *
 * Sam Hubbard - seh208@cam.ac.uk *)

(* Elementary data type declarations. *)
datatype 'a stream = Nil | Cons of 'a * (unit -> 'a stream);
exception nil_head;
exception nil_tail;
fun hd  Nil          = raise nil_head
  | hd (Cons(x, xf)) = x;
fun tl  Nil          = raise nil_tail
  | tl (Cons(x, xf)) = xf ();

(* Lexer data types. *)
datatype token_name = Add | Sub | Mul | Cos | Fact | Int | Real | End;
datatype attr_value = IntAttr of int
                    | RealAttr of real
                    | NullAttr;
datatype token = Token of token_name * attr_value;

(* Parser data types. *)
type nonterminal_name = string;
datatype production = Production of nonterminal_name * int;
type state = int;
datatype action = Shift of state
                | Reduce of production
                | Accept
                | Error;
datatype parse_tree = Br of nonterminal_name * parse_tree list
                    | Lf of token;

(* Decompose a line of input into a stream for ux in interactive mode. *)
fun inputLine () =
  let
    (* Poly includes the newline that started the previous command in the
     * input stream, so read that (empty) line first. *)
    val hack = TextIO.inputLine TextIO.stdIn;

    val line = valOf (TextIO.inputLine TextIO.stdIn);
    val size = String.size line;
    fun next 0 = Nil
      | next i =
          Cons(String.sub (line, size - i), fn () => next (i - 1));
  in
    next size
  end;

(* Lex a stream of characters to a stream of tokens. Removal of white-space
 * and basic float parsing is performed here. *)
exception invalid_char;
exception missing_terminator;
fun lex          Nil          = Nil
  | lex (cons as Cons(c, cf)) =
  let
    (* Convert a char digit to the repesented integer value.
     * Note: this function assumes valid (0-9) input. *)
    fun toInt k = Char.ord k - Char.ord #"0";

    (* Recursively lex the fractional part of a real. *)
    fun lexFract _ _ _              Nil          = raise missing_terminator
      | lexFract r p first (kons as Cons(k, kf)) =
        if Char.isDigit k then lexFract (r + p * real (toInt k))
                                        (p * 0.1)
                                        false
                                        (kf ()) else
        (* Make sure we scan at least one digit after the dot. *)
        if first then raise invalid_char
                 else Cons(Token(Real, RealAttr(r)), fn () => lex kons);

    (* Recursively lex the integer part of a number, be it int or real. *)
    fun lexNum _          Nil          = raise missing_terminator
      | lexNum n (kons as Cons(k, kf)) =
        if Char.isDigit k then lexNum (10 * n + (toInt k)) (kf ()) else
        if #"." = k       then lexFract (real n) 0.1 true (kf ())
        else Cons(Token(Int, IntAttr(n)), fn () => lex kons);

    (* Recusively lex an operator.
     * 
     * Note: we shouldn't reach the Nil case for correct input, since
     *       lexOp tail-calls lex immediately upon matching a token;
     *       if we were in the process of matching cos we would
     *       either have yielded it already or we would have reached
     *       Nil halfway through. This eager approach to yielding
     *       operators/keywords is possible because the language has
     *       no identifiers or keywords which have others as prefixes. *)
    fun lexOp _   Nil          = raise missing_terminator
      | lexOp ks (Cons(k, kf)) =
      let
        val next_ks = ks ^ (Char.toString k);
      in
        if #"+" = k then Cons(Token(Add, NullAttr), fn () => lex (kf ())) else
        if #"-" = k then Cons(Token(Sub, NullAttr), fn () => lex (kf ())) else
        if #"*" = k then Cons(Token(Mul, NullAttr), fn () => lex (kf ())) else
        if #"!" = k then Cons(Token(Fact, NullAttr), fn () => lex (kf ())) else
        if "cos" = next_ks then Cons(Token(Cos, NullAttr), fn () => lex (kf ())) else
        if String.isPrefix next_ks "cos" then lexOp next_ks (kf ())
                                         else raise invalid_char
      end;
  in
    if Char.contains "\n\r" c then Cons(Token(End, NullAttr), fn () => Nil) else
    if Char.isSpace c then lex (cf ()) else
    if Char.isDigit c then lexNum 0 cons else
    if #"." = c then lexFract 0.0 0.1 true (cf ())
                else lexOp "" cons
  end;

(* Parse a token stream into a parse tree using an SLR(1) table.
 * 
 * Note: by convention, the headmost element of a non-terminal's parse
 *       tree node's child list is it's leftmost constituent symbol. *)
exception invalid_syntax;
exception invalid_action_table;
exception invalid_goto_table;
exception internal_error;
val parse =
  let
    (* Load the action and goto functions from file. *)
    local
        (* Strip whitespace from the start and end of a string. *)
        fun strip s =
          let
            val l = String.explode s;
            fun left [] = []
              | left (c::cs) = if Char.isSpace c then left cs
                                                 else (c::cs);
          in
            String.implode (left (List.rev (left (List.rev l))))
          end;
        fun ordNT "expr"      = 0
          | ordNT "term"      = 1
          | ordNT "factor"    = 2
          | ordNT "factorial" = 3
          | ordNT "int"       = 4
          | ordNT "real"      = 5
          | ordNT _           = raise internal_error;

        fun ordT Add  = 0
          | ordT Sub  = 1
          | ordT Mul  = 2
          | ordT Cos  = 3
          | ordT Fact = 4
          | ordT Int  = 5
          | ordT Real = 6
          | ordT End  = 7;  (* End should always be ordered last... *)

        (* Load a file formatted as a table to a list of row lists. *)
        fun load path =
          let
            (* Open the file and read an int from the first line (# of rows). *)
            val input = TextIO.openIn path;
            val rows = valOf (Int.fromString (valOf (TextIO.inputLine input)));
            val cols = valOf (Int.fromString (valOf (TextIO.inputLine input)));

            (* Process a single line of fields: drop the first (line label),
             * and strip whitespace from the following. Ensure there are `cols`
             * number of fields in the returned line, by using options. *)
            fun processLine () =
              let
                fun aux 0 l  _      = List.rev l
                  | aux n l  []     = aux (n - 1) (NONE::l) []
                  | aux n l (f::fs) = aux (n - 1) ((SOME(strip f))::l) fs;

                val fs = String.fields (Char.contains ":,")
                                       (valOf (TextIO.inputLine input));
              in
                aux cols [] (List.tl fs)
              end;
          in
            List.tabulate (rows, fn i => processLine ())
          end;

        (* Process the goto table. *)
        val gotoTable =
          let
            fun processCell  NONE     = ~1
              | processCell (SOME(s)) =
                  case Int.fromString s of (SOME(i)) => i
                                         |  NONE     => ~1;
            
            val processRow = List.map processCell;
          in
            List.map processRow (load "goto.txt")
              handle _ => raise invalid_goto_table
          end;

        (* Process the action table. *)
        val actionTable =
          let
            fun processShift s =
                Shift(valOf (Int.fromString (String.extract (s, 1, NONE))));
            
            fun processReduce s =
              let
                val fields = String.fields (Char.contains "\"") s;
                val name = List.nth (fields, 1);
                val symbols = valOf (Int.fromString (List.nth (fields, 2)));
              in
                Reduce(Production(name, symbols))
              end;

            fun processCell  NONE     = Error
              | processCell (SOME(s)) =
                  if String.isPrefix "a" s then Accept else
                  if String.isPrefix "s" s then processShift s else
                  if String.isPrefix "r" s then processReduce s
                                           else Error;

            val processRow = List.map processCell;
          in
            List.map processRow (load "action.txt")
              handle _ => raise invalid_action_table
          end;
    in
        fun goto state name =
          List.nth (List.nth (gotoTable, state), ordNT name);
        fun action state token =
          List.nth (List.nth (actionTable, state), ordT token);
    end;

    (* Push a new leaf (token) node to the forest. *)
    fun push t forest = (Lf(t))::forest;

    (* Return new forest after a reduction. This involves creating a new node
     * representing the reduced production, popping elements from the old
     * forest to form its children, and adding it to the head of the new forest. *)
    fun grow (Production(name, symbols)) forest =
      let
        val popN =
          let
            fun aux ys 0  _      = ys
              | aux ys n  []     = ys
              | aux ys n (x::xs) = aux (x::ys) (n - 1) xs;
          in
            aux []
          end;
      in
        (Br(name, popN symbols forest))::(List.drop (forest, symbols))
      end;

    (* Return the new state stack after reducing by a production. *)
    fun reduce (Production(name, symbols)) states =
      let
        val base = List.drop (states, symbols);
      in
        (goto (List.hd base) name)::base
      end;

    (* Implementation of the lr parsing algorithm.
     *
     * Note: `forest` is a list of sub-trees currently parsed, in ltr order.
     *        To build a full parse tree: during a reduction, a number of
     *        sub-trees determined by the reducing production are popped
     *        from this list. They are then repurposed as the children of
     *        a new sub-tree, which is pushed. *)
    fun lr _ [] _   = raise internal_error
      | lr _ _  Nil = raise invalid_syntax
      | lr forest (states as s::ss) (cons as Cons(t as Token(t_name, _), tf)) =
      let
        val a = action s t_name;
      in
        case a of (Shift(next))  => lr (push t forest) (next::states) (tf ())
                | (Reduce(prod)) => lr (grow prod forest) (reduce prod states) cons
                |  Accept        => List.hd forest
                |  Error         => raise invalid_syntax
      end;
  in
    lr [] [0]
  end;

(* Convenience functions. *)
fun interactive () = parse (lex (inputLine ()));

