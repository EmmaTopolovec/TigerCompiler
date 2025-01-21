structure Types =
struct

  type unique = unit ref

  datatype ty = 
            RECORD of (Symbol.symbol * ty) list * unique
          | NIL
          | INT
          | STRING
          | ARRAY of ty * unique
          | NAME of Symbol.symbol * ty option ref
          | UNIT (* A type for expressions that do not produce a value. *)
          | BOTTOM (* BOTTOM is a placeholder, if we cannot figure out the type of an expression.
                      BOTTOM should only occur in the case of a type error. *)

end

