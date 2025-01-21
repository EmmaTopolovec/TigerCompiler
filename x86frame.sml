structure X86Frame : FRAME =
struct
    datatype access = InFrame of int | InReg of Temp.temp
    type frame = { name : Temp.label, formals : access list, frameOff : int ref}

    val FP = Temp.newtemp()
    val RV = Temp.newtemp()
    (* val BP = Temp.newtemp() *)
    val wordSize = 4

    fun name frame : Temp.label =
      let
        val { name=n, formals=_, frameOff=_} = frame
      in
        n
      end

    fun formals frame : access list =
      let
        val { name=_, formals=f, frameOff=_} = frame
      in
        f
      end

    fun allocLocal ({ name=n, formals=f, frameOff=fo} : frame) escape : access =
      (if (escape)
        then (fo := !fo - wordSize; InFrame (!fo + wordSize))
        else (InReg (Temp.newtemp())))

    fun allocLocal2 ({ name=n, formals=f, frameOff=fo} : frame) : int =
      (fo := !fo - wordSize; !fo + wordSize)

    fun newFrame { name : Temp.label, formals : bool list } : frame =
      let
        fun makeAccessList ([]) (_) : access list = []
          | makeAccessList (b :: bs : bool list) (s : int) : access list = 
            (if (true)
              then (InFrame s :: (makeAccessList bs (s + wordSize)))
              else (InReg (Temp.newtemp()) :: (makeAccessList bs s)))
            (* (if (b)
              then (InFrame s :: (makeAccessList bs (s + wordSize)))
              else (InReg (Temp.newtemp()) :: (makeAccessList bs s))) *)
      in
        {name=name, formals=(makeAccessList formals 8), frameOff=ref(~4)}
      end

    fun printAccess (InFrame w) = 
        ("(InFrame " ^ Int.toString w ^ ")")
      | printAccess (InReg _) = "InReg"

    fun exp (a : access) (exp : Tree.exp) : Tree.exp =
      case a
        of InFrame(0) => Tree.MEM(exp)
         | InFrame(k) => Tree.MEM(Tree.BINOP(Tree.PLUS, exp, Tree.CONST(k)))
         | InReg t => Tree.TEMP(t)

    fun prologue ({name, formals, frameOff} : frame) = 
      "PUSH %ebp\t# start of prologue()\n" ^
      "MOV %esp, %ebp\n" ^
      "SUB $" ^ Int.toString (~(!frameOff)) ^ ", %esp\n" ^
      "PUSH %ebx\n" ^
      "PUSH %edi\n" ^
      "PUSH %esi\t# end of prologue()\n"

    fun epilogue (f : frame) =
      "POP %esi\t# start of epilogue()\n" ^
      "POP %edi\n" ^
      "POP %ebx\n" ^
      "MOV %ebp, %esp\n" ^
      "POP %ebp\n" ^
      "RET\t# end of epilogue()\n"

    fun addEscapes (s : string) : string =
      let
          fun escapeChar c =
              (case c
                of #"\"" => "\\\""
                 | #"\n" => "\\n"
                 | _ => String.str c)
      in
          String.concat (List.map escapeChar (String.explode s))
      end

    fun string ((l, s) : Temp.label * string) = (Symbol.name l) ^ ":\n\t.int " ^ Int.toString (size(s)) ^ "\n\t.string \"" ^ addEscapes s ^ "\"\n"
end