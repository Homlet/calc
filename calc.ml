(* A simple infix calculator lexer/parser.
 *
 * Sam Hubbard - seh208@cam.ac.uk *)

(* Elementary data type declarations. *)
datatype 'a tree = Br of 'a * 'a tree list;
datatype 'a stream = Nil | Cons of 'a * (unit -> 'a stream);
exception nil_head;
exception nil_tail;
fun hd  Nil          = raise nil_head
  | hd (Cons(x, xf)) = x;
fun tl  Nil          = raise nil_tail
  | tl (Cons(x, xf)) = xf ();

(* Lexer data types. *)
datatype token_name = Int | Real | Mul | Add | Sub | Cos | Fact | End;
datatype attr_value = IntAttr of int
                    | RealAttr of real
                    | NullAttr;
datatype token = Token of token_name * attr_value;

(* Parser data types. *)
type nonterminal_name = string;
datatype symbol = NT of nonterminal_name
                | T of token_name;
datatype production = Production of nonterminal_name * symbol list;
type state = int;
datatype action = Shift of state
                | Reduce of production
                | Accept
                | Error;
datatype parse_tree_label = Internal of nonterminal_name
                          | Leaf of token;

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
exception internal_error;
val parse =
  let
    fun s i = Shift(i);
    fun r l rs = Reduce(Production(l, rs));
    fun action 0  Sub  = s 7
      | action 0  Cos  = s 9
      | action 0  Int  = s 10
      | action 0  Real = s 11
      | action 1  Add  = s 12
      | action 1  Sub  = s 13
      | action 1  End  = Accept
      | action 2  Add  = r "expr" [NT("term")]
      | action 2  Sub  =     action 2 Add
      | action 2  End  =     action 2 Add
      | action 3  Add  = r "term" [NT("factor")]
      | action 3  Sub  =     action 3 Add
      | action 3  Mul  = s 14
      | action 3  End  =     action 3 Add
      | action 4  Add  = r "factor" [NT("factorial")]
      | action 4  Sub  =     action 4 Add
      | action 4  Mul  =     action 4 Add
      | action 4  Fact = s 15
      | action 4  End  =     action 4 Add
      | action 5  Add  = r "factorial" [NT("int")]
      | action 5  Sub  =     action 5 Add
      | action 5  Mul  =     action 5 Add
      | action 5  Fact =     action 5 Add
      | action 5  End  =     action 5 Add
      | action 6  Add  = r "factor" [NT("real")]
      | action 6  Sub  =     action 6 Add
      | action 6  Mul  =     action 6 Add
      | action 6  End  =     action 6 Add
      | action 7  Int  = s 16
      | action 7  Real = s 17
    (* No state 8 because I made a mistake drawing up the table. *)
      | action 9  Int  = s 10
      | action 9  Real = s 11
      | action 10 Add  = r "int" [T(Int)]
      | action 10 Sub  =     action 10 Add
      | action 10 Mul  =     action 10 Add
      | action 10 Fact =     action 10 Add
      | action 10 End  =     action 10 Add
      | action 11 Add  = r "real" [T(Real)]
      | action 11 Sub  =     action 11 Add
      | action 11 Mul  =     action 11 Add
      | action 11 End  =     action 11 Add
      | action 12 Sub  = s 7
      | action 12 Cos  = s 9
      | action 12 Int  = s 10
      | action 12 Real = s 11
      | action 13 Sub  = s 7
      | action 13 Cos  = s 9
      | action 13 Int  = s 10
      | action 13 Real = s 11
      | action 14 Sub  = s 7
      | action 14 Cos  = s 9
      | action 14 Int  = s 10
      | action 14 Real = s 11
      | action 15 Add  = r "factorial" [NT("factorial"), T(Fact)]
      | action 15 Sub  =     action 15 Add
      | action 15 Mul  =     action 15 Add
      | action 15 Fact =     action 15 Add
      | action 15 End  =     action 15 Add
      | action 16 Add  = r "int" [T(Sub), T(Int)]
      | action 16 Sub  =     action 16 Add
      | action 16 Mul  =     action 16 Add
      | action 16 Fact =     action 16 Add
      | action 16 End  =     action 16 Add
      | action 17 Add  = r "real" [T(Real), T(Real)]
      | action 17 Sub  =     action 17 Add
      | action 17 Mul  =     action 17 Add
      | action 17 Fact =     action 17 Add
      | action 17 End  =     action 17 Add
      | action 18 Add  = r "factor" [T(Cos), NT("factorial")]
      | action 18 Sub  =     action 18 Add
      | action 18 Mul  =     action 18 Add
      | action 18 Fact = s 15
      | action 18 End  =     action 18 Add
      | action 19 Add  = r "factor" [T(Cos), NT("real")]
      | action 19 Sub  =     action 19 Add
      | action 19 Mul  =     action 19 Add
      | action 19 End  =     action 19 Add
      | action 20 Add  = r "expr" [NT("expr"), T(Add), NT("term")]
      | action 20 Sub  =     action 20 Add
      | action 20 End  =     action 20 Add
      | action 21 Add  = r "expr" [NT("expr"), T(Sub), NT("term")]
      | action 21 Sub  =     action 21 Add
      | action 21 End  =     action 21 Add
      | action 22 Add  = r "term" [NT("factor"), T(Mul), NT("term")]
      | action 22 Sub  =     action 22 Add
      | action 22 End  =     action 22 Add
      | action _  _    = Error;

    fun goto 0  "expr"      = 1
      | goto 0  "term"      = 2
      | goto 0  "factor"    = 3
      | goto 0  "factorial" = 4
      | goto 0  "int"       = 5
      | goto 0  "real"      = 6
      | goto 9  "factorial" = 18
      | goto 9  "int"       = 5
      | goto 9  "real"      = 19
      | goto 12 "term"      = 20
      | goto 12 "factor"    = 3
      | goto 12 "factorial" = 4
      | goto 12 "int"       = 5
      | goto 12 "real"      = 6
      | goto 13 "term"      = 21
      | goto 13 "factor"    = 3
      | goto 13 "factorial" = 4
      | goto 13 "int"       = 5
      | goto 13 "real"      = 6
      | goto 14 "term"      = 22
      | goto 14 "factor"    = 3
      | goto 14 "factorial" = 4
      | goto 14 "int"       = 5
      | goto 14 "real"      = 6
      | goto _  _           = ~1;

    (* Push a new leaf (token) node to the forest. *)
    fun push t forest = (Br(Leaf(t), []))::forest;

    (* Return new forest after a reduction. This involves creating a new node
     * representing the reduced production, popping elements from the old
     * forest to form its children, and adding it to the head of the new forest. *)
    fun grow (Production(name, symbols)) forest =
      let
        val n = List.length symbols; 
        val popN =
          let
            fun aux ys 0  _      = ys
              | aux ys n  []     = ys
              | aux ys n (x::xs) = aux (x::ys) (n - 1) xs;
          in
            aux []
          end;
      in
        (Br(Internal(name), popN n forest))::(List.drop (forest, n))
      end;

    (* Return the new state stack after reducing by a production. *)
    fun reduce (Production(name, symbols)) states =
      let
        val base = List.drop (states, List.length symbols);
      in
        (goto (List.hd base) name)::base
      end;

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

