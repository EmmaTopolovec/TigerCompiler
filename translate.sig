signature TRANSLATE =
sig
    type level
    type access

    val outermost : level
    val newLevel : { parent : level, name : Temp.label, formals : bool list} -> level
    val formals : level -> access list
    val allocLocal : level -> bool -> access 

    val printAccess : Symbol.symbol -> access -> unit
    val printLevel : Symbol.symbol -> level -> unit

    datatype exp = Ex of Tree.exp
                 | Stm of Tree.stm
                 | Cond of Temp.label * Temp.label -> Tree.stm

    val toEx : exp -> Tree.exp
    val toStm : exp -> Tree.stm
    val toCond : exp -> (Temp.label * Temp.label -> Tree.stm)

    val simpleVar : access * level -> exp
    val fieldVar : exp -> int -> exp
    val subscriptVar : exp -> exp -> exp
    val nilExp : unit -> exp
    val intExp : int -> exp
    val stringExp : string -> exp
    val callExp : level -> level -> Temp.label -> Temp.label -> exp list -> exp
    val opExp : exp -> Absyn.oper -> exp -> Types.ty -> exp
    val recordExp : exp list -> exp
    val seqExp : exp list -> exp
    val assignExp : exp -> exp -> exp
    val ifExp : exp * exp * exp option -> exp
    val whileExp : Temp.label -> exp -> exp -> exp
    val forExp : Temp.label -> exp -> exp -> exp -> exp -> exp
    val breakExp : Temp.label -> exp
    val letExp : exp list -> exp -> exp
    val arrayExp : exp -> exp -> exp

    datatype frag = PROC of { body : Tree.stm, frame : X86Frame.frame }
                  | STRING of Temp.label * string
    
    val frags : frag list ref

    val procEntryExit : { level : level, body : exp } -> unit

    val printFrags : unit -> unit
end