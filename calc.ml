(* A simple infix calculator lexer/parser.
 *
 * Sam Hubbard - seh208@cam.ac.uk *)

(* Elementary data type declarations. *)
datatype 'a tree = Lf | Br of 'a * 'a tree list;
datatype 'a stream = Nil | Cons of 'a * (unit -> 'a stream);
exception nil_head;
exception nil_tail;
fun hd  Nil          = raise nil_head
  | hd (Cons(x, xf)) = x;
fun tl  Nil          = raise nil_tail
  | tl (Cons(x, xf)) = xf ();
fun take n s =
  let
    fun aux xs _  Nil          = xs
      | aux xs 0  _            = xs
      | aux xs 1 (Cons(x, xf)) = (x::xs)
      | aux xs k (Cons(x, xf)) = aux (x::xs) (k - 1) (xf ());
  in List.rev (aux [] n s) end;

(* Lexer data types. *)
datatype token_name = Int | Real | Mul | Add | Sub | Cos | Fact;
datatype attr_value = IntAttr of int | RealAttr of real | NullAttr;
datatype token = Token of token_name * attr_value;

(* Parser data types. *)
type nonterminal_name = string;
datatype symbol = NT of nonterminal_name
                | T of token_name;
datatype production = Production of nonterminal_name * symbol list;
datatype item = Item of production * int;
datatype state = State of item list;
datatype action = Shift of state
                | Reduce of production
                | Accept
                | Error;

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
fun lex          Nil          = Nil
  | lex (cons as Cons(c, cf)) =
  let
    (* Convert a char digit to the repesented integer value.
     * Note: this function assumes valid (0-9) input. *)
    fun toInt k = Char.ord k - Char.ord #"0";

    (* Recursively lex the fractional part of a real. *)
    fun lexFract r p          Nil          = Cons(Token(Real, RealAttr(r)), fn () => Nil)
      | lexFract r p (kons as Cons(k, kf)) =
        if Char.isDigit k then lexFract (r + p * real (toInt k))
                                        (p * 0.1)
                                        (kf ())
                          else Cons(Token(Real, RealAttr(r)), fn () => lex kons);

    (* Recursively lex the integer part of a number, be it int or real. *)
    fun lexNum n          Nil          = Cons(Token(Int, IntAttr(n)), fn () => Nil)
      | lexNum n (kons as Cons(k, kf)) =
        if Char.isDigit k then lexNum (10 * n + (toInt k)) (kf ()) else
        if #"." = k       then lexFract (real n) 0.1 (kf ())
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
    fun lexOp ks  Nil          = raise invalid_char
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
    if Char.contains "\n\r" c then Nil else
    if Char.isSpace c then lex (cf ()) else
    if Char.isDigit c then lexNum 0 cons
                      else lexOp "" cons
  end;

(* Parse a token stream into a parse tree using the LR(0) technique.
 * 
 * Note: by convention, the headmost element of a non-terminal's parse
 *       tree node's child list is it's leftmost constituent symbol. *)
fun parse          Nil          = Lf
  | parse (cons as Cons(t, tf)) =
  let
    fun prod l rs = Production(l, rs);
    val grammar = [prod "root" [NT("expr")],
                   prod "expr" [NT("term")],
                   prod "expr" [NT("expr"), T(Add), NT("term")],
                   prod "expr" [NT("expr"), T(Sub), NT("term")],
                   prod "term" [NT("factor")],
                   prod "term" [NT("term"), T(Mul), NT("factor")],
                   prod "factor" [NT("number")],
                   prod "factor" [NT("number"), T(Fact)],
                   prod "factor" [T(Add), NT("number")],
                   prod "factor" [T(Sub), NT("number")],
                   prod "factor" [T(Cos), NT("number")],
                   prod "number" [T(Int)],
                   prod "number" [T(Real)]]; 
  in
    Lf (* TODO: implement. *)
  end;

(* Convenience functions. *)
val interactive = fn () => lex (inputLine ());

