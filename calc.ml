(* A simple infix calculator lexer-parser.
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

(* Lexer data types. *)
datatype token = Int of int
               | Real of real
               | Op of string;

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
 * and float parsing is performed here. *)
fun lex          Nil          = Nil
  | lex (cons as Cons(c, cf)) =
  let
    (* Convert a char digit to the repesented integer value.
     * Note: this function assumes valid (0-9) input. *)
    fun toInt c = Char.ord c - Char.ord #"0";

    (* Recursively lex the fractional part of a real. *)
    fun lexFract r p          Nil          = Cons(Real(r), fn () => Nil)
      | lexFract r p (cons as Cons(k, kf)) =
        if Char.isDigit k then lexFract (r + p * real (toInt k))
                                        (p * 0.1)
                                        (kf ())
                          else Cons(Real(r), fn () => lex cons);

    (* Recursively lex the integer part of a number, be it int or real. *)
    fun lexNum n          Nil          = Cons(Int(n), fn () => Nil)
      | lexNum n (cons as Cons(k, kf)) =
        if Char.isDigit k then lexNum (10 * n + (toInt k)) (kf ()) else
        if #"." = k       then lexFract (real n) 0.1 (kf ())
                          else Cons(Int(n), fn () => lex cons);
  in
    if Char.isSpace c then lex (cf ()) else
    if Char.isDigit c then lexNum 0 cons
                      else Nil (* TODO: Operators. *)
  end;

(* Note: by convention, the headmost element of a non-terminal's parse
 *       tree node's child list is it's leftmost constituent symbol. *)

(* Convenience functions. *)
val interactive = fn () => lex (inputLine ());

