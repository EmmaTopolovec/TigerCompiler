

structure Translate : TRANSLATE =
struct
    datatype level = Outermost | Level of { prev_level : level, frame : X86Frame.frame, eqc : unit ref  }
    type access = level * X86Frame.access

    val outermost = Outermost

    datatype frag = PROC of { body : Tree.stm, frame : X86Frame.frame }
                  | STRING of Temp.label * string
    
    val frags : frag list ref = ref []
    
    fun printFrags_ ([] : frag list) : unit = ()
      | printFrags_ (f :: fs : frag list) : unit =
        ((
          case f
            of PROC {body, frame={name, formals, frameOff}} => (print(Symbol.name name ^ " = " ); Printtree.printtree(TextIO.stdOut, body))
             | STRING(lbl, s) => (print(Symbol.name lbl); print(" = "); print(s); print("\n"))
         );
        printFrags_ fs)
    fun printFrags () : unit = printFrags_ (!frags)

    fun newLevel {parent, name, formals} =
        Level {prev_level=parent, frame=(X86Frame.newFrame {name=name, formals=(true::formals)}), eqc=ref()}

    fun formalsHelper (lv : level) ([] : X86Frame.access list) : access list = []
      | formalsHelper (lv : level) (x86a :: xs : X86Frame.access list) : access list = 
          (lv, x86a) :: (formalsHelper lv xs)  

    fun formals (l : level) : access list = 
      (case l
        of Outermost => []
         | Level {prev_level=p, frame=f, eqc=_} =>
              (formalsHelper l (X86Frame.formals f)))

    fun allocLocal (l : level) (b : bool) : access =
      (case l
        of Outermost =>
          (ErrorMsg.error 0 "ERROR: Cannot allocate local variable in outermost frame";
          (outermost, X86Frame.allocLocal (X86Frame.newFrame {name=Temp.newlabel(), formals=[]}) b))
         | Level {prev_level=p, frame=f, eqc=e} => 
          (Level {prev_level=p, frame=f, eqc=e}, X86Frame.allocLocal f b))

    fun printAccess_ (_, acc) = X86Frame.printAccess acc
    fun printAccess n loc = print("var " ^ Symbol.name n ^ " " ^ printAccess_ loc ^ "\n")
    fun printLevel n l =
      print("function " ^ Symbol.name n ^ " "
            ^ (String.concatWith " " (map printAccess_ (formals l))) ^ "\n")

    datatype exp = Ex of Tree.exp
                 | Stm of Tree.stm
                 | Cond of Temp.label * Temp.label -> Tree.stm

    (*  *)
    fun seq [] = Tree.EXP (Tree.CONST 0)
      | seq [s] = s
      | seq (s :: stms) = Tree.SEQ (s, seq stms)

    (* toExp : Translate.exp -> Tree.exp *)
    fun toEx (Ex e) = e
      | toEx (Stm s) = Tree.ESEQ(s, Tree.CONST 0)
      | toEx (Cond cond) =
        let
          val r = Temp.newtemp ()
          val t = Temp.newlabel ()
          val f = Temp.newlabel ()
          val d = Temp.newlabel ()
        in
          Tree.ESEQ(seq[ 
                      cond(t, f),
                      Tree.LABEL t,
                      Tree.MOVE(Tree.TEMP r, Tree.CONST 1),
                      Tree.JUMP(Tree.NAME(d), [d]),
                      Tree.LABEL f,
                      Tree.MOVE(Tree.TEMP r, Tree.CONST 0),
                      Tree.LABEL d],
                      Tree.TEMP r)
        end

    fun toStm (Stm s) = s
      | toStm (Ex e) = Tree.EXP e
      | toStm (Cond cond) = Tree.EXP(toEx(Cond cond))

    fun toCond (Cond c) = c
      | toCond (Ex e) = (fn(l1, l2) => Tree.CJUMP(Tree.EQ, e, Tree.CONST 1, l1, l2))
      | toCond (Stm _) = (fn(_,_) => (Tree.LABEL(Temp.newlabel()))) (* Should never happen *)

    fun procEntryExit { level = Level {frame, ...}, body } =
          frags := PROC { body = Tree.MOVE(Tree.TEMP X86Frame.RV, toEx body), frame = frame } :: (!frags)
      | procEntryExit { level = Outermost, ...} = (print "procEntryExit: impossible"; raise ErrorMsg.Error)

    fun walkBack (dl : level) (cl : level) (exp : Tree.exp) : Tree.exp = 
        ( if ((dl = cl))
          then (exp)
          else (case cl
                  of Level {prev_level=clparent, frame=_, eqc=_} => (walkBack dl clparent (Tree.MEM(Tree.BINOP(Tree.PLUS, exp, Tree.CONST(2 * X86Frame.wordSize)))))
                  | Outermost => (ErrorMsg.error 0 "Error: static link failed"; Tree.CONST(999))))

    fun simpleVar (((dl, a), cl) : (access * level)) : exp = Ex(X86Frame.exp a (walkBack dl cl (Tree.TEMP(X86Frame.FP))))
    (* fun simpleVar (((dl, a), cl) : (access * level)) : exp = Ex(X86Frame.exp a (Tree.TEMP(X86Frame.FP))) *)

    fun fieldVar (exp : exp) (i : int) : exp =
        Ex(Tree.MEM(Tree.BINOP(Tree.PLUS, toEx(exp), Tree.CONST(i * X86Frame.wordSize))))

    fun subscriptVar (arr : exp) (sub : exp) : exp =
        Ex(Tree.MEM(Tree.BINOP(Tree.PLUS, toEx(arr), Tree.BINOP(Tree.MUL, toEx(sub), Tree.CONST(X86Frame.wordSize)))))

    fun nilExp () : exp =
        Ex(Tree.CONST 0)

    fun intExp (i : int) : exp =
        Ex(Tree.CONST i)

    fun stringExp (s : string) : exp =
      let
        val sl = Temp.newlabel()
      in
        (frags := STRING(sl, s) :: !frags;
        Ex(Tree.NAME(sl)))
      end

    fun callExp (cl : level) (dl as Outermost : level) (f : Temp.label) (label : Temp.label) (args : exp list) : exp =
        let
          val exp = Tree.TEMP(X86Frame.FP)
          val argExps = map toEx args
        in
          (case (Symbol.name f)
            of ("print" 
              | "ord"
              | "chr"
              | "concat"
              | "initArray"
              | "allocRecord"
              | "flush"
              | "main"
              | "size"
              | "substring"
              | "not"
              | "stringEqual"
              | "stringLT"
              | "stringGT") => Ex(Tree.CALL(Tree.NAME(f), argExps))
             | "getchar" => Ex(Tree.CALL(Tree.NAME(Symbol.symbol "my_getchar"), argExps))
             | _ =>  Ex(Tree.CALL(Tree.NAME(label), exp :: argExps)))
        end
      | callExp (cl : level) (dl as Level {prev_level, frame, eqc} : level) (f : Temp.label) (label : Temp.label) (args : exp list) : exp =
        let
          val exp = 
            if dl = cl (* recursion *) 
            then Tree.MEM(Tree.BINOP(Tree.PLUS, Tree.TEMP(X86Frame.FP), Tree.CONST(2 * X86Frame.wordSize)))
            else (* walkBack prev_level cl *) (Tree.TEMP(X86Frame.FP))
          val argExps = map toEx args
        in
          (case (Symbol.name f)
            of ("print" 
              | "ord"
              | "chr"
              | "concat"
              | "initArray"
              | "allocRecord"
              | "flush"
              | "main"
              | "size"
              | "substring"
              | "not"
              | "stringEqual"
              | "stringLT"
              | "stringGT") => Ex(Tree.CALL(Tree.NAME(f), argExps))
             | "getchar" => Ex(Tree.CALL(Tree.NAME(Symbol.symbol "my_getchar"), argExps))
             | _ =>  Ex(Tree.CALL(Tree.NAME(label), exp :: argExps)))
        end

    fun labelInFrags (lbl : Temp.label) : bool = 
        let
          fun checkLbl (lbl : Temp.label) ([] : frag list) : bool = false
            | checkLbl (lbl : Temp.label) (f :: fragList : frag list) : bool =
              (case f
                of STRING(lbl2, _) => (if (lbl = lbl2) then (true) else (checkLbl lbl fragList))
                 | _ => checkLbl lbl fragList)
        in
          (checkLbl lbl (!frags))
        end

    fun opExp (e1 : exp) (oper : Absyn.oper) (e2 : exp) (ty : Types.ty) : exp =
      (case oper
        of Absyn.PlusOp => Ex(Tree.BINOP(Tree.PLUS, toEx(e1), toEx(e2)))
         | Absyn.MinusOp => Ex(Tree.BINOP(Tree.MINUS, toEx(e1), toEx(e2)))
         | Absyn.TimesOp => Ex(Tree.BINOP(Tree.MUL, toEx(e1), toEx(e2)))
         | Absyn.DivideOp => Ex(Tree.BINOP(Tree.DIV, toEx(e1), toEx(e2)))
         | Absyn.EqOp => 
            (case ty
              of Types.STRING => Ex(Tree.CALL(Tree.NAME(Temp.namedlabel "stringEqual"), [toEx e1, toEx e2]))
              | _ => Cond(fn (t, f) => Tree.CJUMP(Tree.EQ,
                                                  toEx e1,
                                                  toEx e2,
                                                  t,
                                                  f)))
          | Absyn.NeqOp => 
            (case ty
              of Types.STRING =>
                let 
                  val returnValue = Ex(Tree.CALL(Tree.NAME(Temp.namedlabel "stringEqual"), [toEx e1, toEx e2]))
                in
                  Cond(fn (t, f) => Tree.CJUMP( Tree.EQ,
                                                toEx returnValue,
                                                Tree.CONST(1),
                                                f,
                                                t))
                end
              | _ => Cond(fn (t, f) => Tree.CJUMP(Tree.NE,
                                                  toEx e1,
                                                  toEx e2,
                                                  t,
                                                  f)))
          | Absyn.LtOp =>
            (case ty
              of Types.STRING =>  Ex(Tree.CALL(Tree.NAME(Temp.namedlabel "stringLT"), [toEx e1, toEx e2]))
              | _ => Cond(fn (t, f) => Tree.CJUMP(Tree.LT,
                                                  toEx e1,
                                                  toEx e2,
                                                  t,
                                                  f)))
          | Absyn.GtOp =>
            (case ty
              of Types.STRING =>  Ex(Tree.CALL(Tree.NAME(Temp.namedlabel "stringGT"), [toEx e1, toEx e2]))
              | _ => Cond(fn (t, f) => Tree.CJUMP(Tree.GT,
                                                  toEx e1,
                                                  toEx e2,
                                                  t,
                                                  f)))
          | Absyn.LeOp =>
            (case ty
              of Types.STRING =>
                let 
                  val returnValue = Ex(Tree.CALL(Tree.NAME(Temp.namedlabel "stringGT"), [toEx e1, toEx e2]))
                in
                  Cond(fn (t, f) => Tree.CJUMP( Tree.EQ,
                                                toEx returnValue,
                                                Tree.CONST(1),
                                                f,
                                                t))
                end
              | _ => Cond(fn (t, f) => Tree.CJUMP(Tree.LE,
                                                  toEx e1,
                                                  toEx e2,
                                                  t,
                                                  f)))
          | Absyn.GeOp =>
            (case ty
              of Types.STRING =>
                let 
                  val returnValue = Ex(Tree.CALL(Tree.NAME(Temp.namedlabel "stringLT"), [toEx e1, toEx e2]))
                in
                  Cond(fn (t, f) => Tree.CJUMP( Tree.EQ,
                                                toEx returnValue,
                                                Tree.CONST(1),
                                                f,
                                                t))
                end
              | _ => Cond(fn (t, f) => Tree.CJUMP(Tree.GE,
                                                  toEx e1,
                                                  toEx e2,
                                                  t,
                                                  f)))
      )

    fun assignExp (var : exp) (exp : exp) : exp =
      Ex(toEx(Stm(Tree.MOVE(toEx(var), toEx(exp)))))

    fun recordExp (exps : exp list) : exp =
      let
        val recTemp = Temp.newtemp()
        val allocExp = Ex(Tree.CALL(Tree.NAME(Temp.namedlabel "allocRecord"), [Tree.CONST(length(exps))])) 
        val recInitExp = Tree.MOVE(Tree.TEMP recTemp, toEx(allocExp));
        fun assignFieldExps ([] : exp list) (_ : int) : Tree.stm list = []
          | assignFieldExps (e :: exps : exp list) (i : int) : Tree.stm list =
            (toStm(assignExp (Ex(Tree.MEM(Tree.BINOP(Tree.PLUS, Tree.TEMP recTemp, Tree.CONST(i * X86Frame.wordSize))))) e)
            :: (assignFieldExps exps (i+1)))
        val fieldExps = (assignFieldExps exps 0)
      in
        Ex(Tree.ESEQ(seq (recInitExp :: fieldExps), Tree.TEMP recTemp))
      end
      
    fun seqExpHelper ([] : exp list) : Tree.exp = Tree.CONST(0)
      | seqExpHelper (exp :: [] : exp list) : Tree.exp = toEx(exp)
      | seqExpHelper (exp :: exps : exp list) : Tree.exp = Tree.ESEQ(toStm(exp), seqExpHelper(exps))

    fun seqExp (exps : exp list) : exp = Ex(seqExpHelper(exps))

    (* ifExp : exp * exp * exp option -> Tree.exp *)
    fun ifExp (test, then', SOME else') =
        let
          val t = Temp.newlabel ()
          val f = Temp.newlabel ()
          val j = Temp.newlabel ()
          (* var z := x > y*)
          (* CJUMP(GT, CONST ~10, CONST 0, l1, l2) *)
          val ctest = toCond test
          val ethen = toEx then'
          val eelse = toEx else'
          val res = Temp.newtemp ()
          val s = seq [ ctest(t, f)
                      , Tree.LABEL t
                      , Tree.MOVE(Tree.TEMP res, ethen)
                      , Tree.JUMP(Tree.NAME j, [j])
                      , Tree.LABEL f
                      , Tree.MOVE(Tree.TEMP res, eelse)
                      , Tree.LABEL j]
        in
          Ex (Tree.ESEQ(s, Tree.TEMP res))
        end
      | ifExp (test, then', NONE) =
        let
          val t = Temp.newlabel ()
          val f = Temp.newlabel ()
          val ctest = toCond test
          val ethen = toEx then'
          val s = seq [ ctest(t, f)
                      , Tree.LABEL t
                      , Tree.EXP ethen
                      , Tree.LABEL f]        
        in
          Stm s
        end 

    fun whileExp (done : Temp.label) (test : exp) (body : exp) : exp =
        (* 
          test:
            if not(condition) goto done
            body
            goto test
          done:
        *)
      let
        val start = Temp.newlabel () (* start label *)
        val t = Temp.newlabel () (* test label *)
        val ctest = toCond test
        val s = seq [ Tree.LABEL start
                    , ctest(t, done)
                    , Tree.LABEL t
                    , toStm(body)
                    , Tree.JUMP(Tree.NAME start, [start])
                    , Tree.LABEL done]
      in
        Ex(Tree.ESEQ(s, Tree.CONST 0))
      end

    fun letExp (decs : exp list) (body : exp) : exp =
      Ex(Tree.ESEQ(seq (map toStm decs), toEx(body)))

    fun forExp (done : Temp.label) (i : exp) (lo : exp) (hi : exp) (body : exp) : exp =
        (* 
          let 
            var i := lo
            var limit := hi
          in 
            while i <= limit
              do (body; i := i + 1)
          end
        *)
      let
        val limit = Temp.newtemp()
        val startwhile = Temp.newlabel()
        val whileloop = Temp.newlabel()
        val s = seq[
          Tree.MOVE(toEx(i), toEx(lo)),
          Tree.MOVE(Tree.TEMP(limit), toEx(hi)),
          Tree.LABEL(startwhile),
          Tree.CJUMP(Tree.LE, toEx(i), Tree.TEMP(limit), whileloop, done),
          Tree.LABEL(whileloop),
          toStm(body),
          Tree.MOVE(toEx(i), Tree.BINOP(Tree.PLUS, toEx(i), Tree.CONST(1))),
          Tree.JUMP(Tree.NAME(startwhile), [startwhile]),
          Tree.LABEL(done)
        ]
      in
        Ex(Tree.ESEQ(s, Tree.CONST 0))
      end

    fun breakExp (jump : Temp.label) : exp =
      Ex(toEx(Stm(Tree.JUMP(Tree.NAME(jump), [jump]))))

    fun arrayExp (size : exp) (init : exp) : exp =
      let
        val arrTemp = Temp.newtemp()
        val arrInit = Ex(Tree.CALL(Tree.NAME(Temp.namedlabel "initArray"), [toEx size, toEx init]))
        val arrInitExp = Tree.MOVE(Tree.TEMP arrTemp, toEx(arrInit))
      in
        Ex(Tree.ESEQ(arrInitExp, Tree.TEMP arrTemp))
      end
end