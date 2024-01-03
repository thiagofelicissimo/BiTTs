module C = Concrete

exception Lexing_error
exception SyntaxError of Lexing.position * Lexing.position

val get_concrete_syntax : string -> C.entry list
