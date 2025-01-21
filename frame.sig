signature FRAME =
sig
    type frame
    type access
    val FP : Temp.temp
    val RV : Temp.temp
    (* val BP : Temp.temp *)
    val wordSize : int
    val newFrame : { name : Temp.label, formals : bool list } -> frame
    val name : frame -> Temp.label
    val formals : frame -> access list
    val allocLocal : frame -> bool -> access
    val allocLocal2 : frame -> int

    val printAccess : access -> string

    val exp : access -> Tree.exp -> Tree.exp

    val prologue : frame -> string
    val epilogue : frame -> string

    val string : Temp.label * string -> string
end