structure CodeGen =
struct
  structure T = Tree
  structure A = Assem
   structure F = X86Frame

  fun codegen (frame : F.frame) (stm: T.stm) : (Temp.temp A.instr) list =
    let
      val ilist = ref (nil : (Temp.temp A.instr) list)
      fun emit x = ilist := x :: !ilist
      fun result(gen) = let val t = Temp.newtemp() in  gen t; t end

      fun intString i = if i >= 0 then Int.toString i else "-" ^ Int.toString (~i)

      and munchStm (T.JUMP(T.NAME l, ls)) = (* Simple jump *)
          emit (A.JUMP{assem = "JMP `j0\n", jump = [l]})
        | munchStm (T.MOVE(T.TEMP t1, T.TEMP t2)) = (* Simple temp move *)
          emit (A.OPER{assem = "MOV `s0, `d0\t# simple mov\n", dst = [t1], src = [t2]})
        | munchStm (T.MOVE(T.MEM(T.BINOP(T.PLUS, e1, e2)), T.CONST(c))) = (* Move const into sum of two exps *)
          emit (A.OPER{assem="MOVL $" ^ intString c ^ ", (`s0, `s1, 1)\n", src=[munchExp e1, munchExp e2], dst=[]})
        (* | munchStm (T.MOVE(T.MEM(T.BINOP(T.PLUS, T.TEMP arrOrRec, T.CONST i)), e))  = (* Array/record indexing *)
          emit (A.OPER{assem="MOV `s0, (`d0, 4, $" ^ intString i ^ ")\n", src=[munchExp e], dst=[arrOrRec]}) *)
        
        (* | munchStm(T.CJUMP(T.EQ, e1, e2, t, f)) = (* opExp EQ (non-string) *)
          emit (A.OPER{assem = "CMP `s0, `s1\nJE " ^ Symbol.name t ^ "\n", src = [munchExp e1, munchExp e2], dst = []})
        | munchStm(T.CJUMP(T.NE, e1, e2, t, f)) = (* opExp NE (non-string) *)
          emit (A.OPER{assem = "CMP `s0, `s1\nJNE " ^ Symbol.name t ^ "\n", src = [munchExp e1, munchExp e2], dst = []})
        | munchStm(T.CJUMP(T.LT, e1, e2, t, f)) = (* opExp LT (non-string) *)
          emit (A.OPER{assem = "CMP `s0, `s1\nJG " ^ Symbol.name t ^ "\n", src = [munchExp e1, munchExp e2], dst = []})
        | munchStm(T.CJUMP(T.GT, e1, e2, t, f)) = (* opExp GT (non-string) *)
          emit (A.OPER{assem = "CMP `s0, `s1\nJL " ^ Symbol.name t ^ "\n", src = [munchExp e1, munchExp e2], dst = []})
        | munchStm(T.CJUMP(T.LE, e1, e2, t, f)) = (* opExp LE (non-string) *)
          emit (A.OPER{assem = "CMP `s0, `s1\nJGE " ^ Symbol.name t ^ "\n", src = [munchExp e1, munchExp e2], dst = []})
        | munchStm(T.CJUMP(T.GE, e1, e2, t, f)) = (* opExp GE (non-string) *)
          emit (A.OPER{assem = "CMP `s0, `s1\nJLE " ^ Symbol.name t ^ "\n", src = [munchExp e1, munchExp e2], dst = []}) *)
        
        | munchStm(T.CJUMP(T.EQ, e1, e2, t, f)) = (* opExp EQ (non-string) *)
          (emit (A.OPER{assem = "CMP `s0, `d0\n", src = [munchExp e1], dst = [munchExp e2]});
          emit (A.OPER{assem = "JE " ^ Symbol.name t ^ "\n", src = [], dst = []}))
        | munchStm(T.CJUMP(T.NE, e1, e2, t, f)) = (* opExp NE (non-string) *)
          (emit (A.OPER{assem = "CMP `s0, `d0\n", src = [munchExp e1], dst = [munchExp e2]});
          emit (A.OPER{assem = "JNE " ^ Symbol.name t ^ "\n", src = [], dst = []}))
        | munchStm(T.CJUMP(T.LT, e1, e2, t, f)) = (* opExp LT (non-string) *)
          (emit (A.OPER{assem = "CMP `s0, `d0\n", src = [munchExp e1], dst = [munchExp e2]});
          emit (A.OPER{assem = "JG " ^ Symbol.name t ^ "\n", src = [], dst = []}))
        | munchStm(T.CJUMP(T.GT, e1, e2, t, f)) = (* opExp GT (non-string) *)
          (emit (A.OPER{assem = "CMP `s0, `d0\n", src = [munchExp e1], dst = [munchExp e2]});
          emit (A.OPER{assem = "JL " ^ Symbol.name t ^ "\n", src = [], dst = []}))
        | munchStm(T.CJUMP(T.LE, e1, e2, t, f)) = (* opExp LE (non-string) *)
          (emit (A.OPER{assem = "CMP `s0, `d0\n", src = [munchExp e1], dst = [munchExp e2]});
          emit (A.OPER{assem = "JGE " ^ Symbol.name t ^ "\n", src = [], dst = []}))
        | munchStm(T.CJUMP(T.GE, e1, e2, t, f)) = (* opExp GE (non-string) *)
          (emit (A.OPER{assem = "CMP `s0, `d0\n", src = [munchExp e1], dst = [munchExp e2]});
          emit (A.OPER{assem = "JLE " ^ Symbol.name t ^ "\n", src = [], dst = []}))


        | munchStm(T.MOVE(d, T.MEM(T.BINOP(T.PLUS, e, T.CONST(k))))) =
          emit (A.OPER{assem = "MOV " ^ intString k ^ "(`s0), `d0\t# store mem access w/ offset in exp\n", dst = [munchExp d], src = [munchExp e]})

        | munchStm(T.MOVE(T.TEMP t, e)) = (* recordInitExp *)
          emit (A.OPER{assem = "MOV `s0, `d0\t# mov exp into temp\n", dst = [t], src = [munchExp e]})
        | munchStm(T.MOVE(T.MEM(loc), e)) = (* move something into mem *)
          emit (A.OPER{assem = "MOV `s0, (`d0)\t# mov val from temp to memory\n", dst = [munchExp loc], src = [munchExp e]})
        | munchStm(T.MOVE(e, T.MEM(loc))) = (* move something from mem *)
          emit (A.OPER{assem = "MOV (`s0), `d0\t# mov val from mem to temp\n", dst = [munchExp e], src = [munchExp loc]})
        | munchStm(T.MOVE(e1, e2)) = (* assignExp *)
          emit (A.OPER{assem = "MOV `s0, `d0\t# assign\n", dst = [munchExp e1], src = [munchExp e2]})
        | munchStm(T.EXP(e)) = (* toEx *)
          (munchExp e; ())
        | munchStm(T.SEQ(s1, s2)) = (* SEQ *)
          (munchStm s1; munchStm s2)
        | munchStm(T.LABEL(l)) = (* labels - ifExp | whileExp | forExp *)
          emit (A.LABEL{assem = "" ^ Symbol.name l ^ ":\n", lab = l})
        | munchStm s = (Printtree.printtree(TextIO.stdOut, s); raise ErrorMsg.Error)

      and result(gen) = let val t = Temp.newtemp() in gen t; t end

      and callerPrologue args = 
        let
          fun pushArgs [] = []
            | pushArgs (arg :: args) =
              let
                val argsFinal = pushArgs args
                val argFinal = munchExp arg
              in
                emit (A.OPER{assem="PUSH `s0\t# caller push arg\n", src=[argFinal], dst=[]});
                argFinal :: argsFinal
              end
        in
          (* emit (A.OPER{assem="PUSH %eax\t# caller saved\nPUSH %ecx\t# caller saved\nPUSH %edx\t# caller saved\n", src=[], dst=[]}); *)
          emit (A.OPER{assem="PUSH %ecx\nPUSH %edx\n", src=[], dst=[]});
          pushArgs args
        end

      and callerEpilogue args =
        let
          fun popArgs [] = ()
            | popArgs (arg :: args) =
              (emit (A.OPER{assem="POP `d0\t# caller pop arg\n", src=[], dst=[arg]});
              popArgs args)
        in
          popArgs args;
          emit (A.OPER{assem="POP %edx\nPOP %ecx\n", src=[], dst=[]});
          
          emit (A.OPER{assem="MOV %eax, `d0\t# caller store return val\n", src=[], dst=[F.RV]})
          (* emit (A.OPER{assem="POP %eax\n", src=[], dst=[]}) *)
          (* emit (A.OPER{assem="POP %edx\t# caller saved\nPOP %ecx\t# caller saved\nPOP %eax\t# caller saved\n", src=[], dst=[]}) *)
        end

      and munchExp(T.CALL(T.NAME(n), args)) = (* callExp + records, arrays and string comparisons *)
          let
            val argsFinal = callerPrologue args
          in
            emit (A.OPER{assem = "CALL " ^ Symbol.name n ^ "\n", src = [], dst = []});
            callerEpilogue argsFinal;
            F.RV
          end
        | munchExp(T.MEM(T.BINOP(T.PLUS, e, T.CONST(k)))) = (* simpleVar b. | fieldVar *)
          result (fn r =>
            emit (A.OPER{assem = "MOV " ^ intString k ^ "(`s0), `d0\t# mem access with offset\n", src = [munchExp e], dst = [r]}))
        (* | munchExp(T.MEM(T.BINOP(T.PLUS, arr, i))) = (* subscriptVar 1/2 *)
          result (fn r =>
            emit (A.OPER{assem = "MOV `s0(`s1), `d0\n", src = [munchExp i, munchExp arr], dst = [r]})) *)
        (* | munchExp(T.BINOP(T.MUL, sub, T.CONST(wdSz))) = (* subscriptVar 2/2 *)
          let
            val retAddr = munchExp sub
            val _ = emit (A.OPER{assem = "IMUL $" ^ intString wdSz ^ ", `s0, `d0\n", src = [retAddr], dst = [retAddr]})
          in
            retAddr
          end *)
        (* | munchExp(T.BINOP(T.PLUS, e1, e2)) = (* opExp PLUS *)
          let
            val retAddr = Temp.newtemp()
            val e2Reg = munchExp e2
            val e1Reg = munchExp e1
            val _ = emit (A.OPER{assem = "MOV `s0, `d0\t # Set up add\nADD `s1, `d0\t # add!\n", src = [e2Reg, e1Reg], dst = [retAddr]})
          in
            retAddr
          end
        | munchExp(T.BINOP(T.MINUS, e2, e1)) = (* opExp MINUS *)
          let
            val retAddr = Temp.newtemp()
            val e2Reg = munchExp e2
            val e1Reg = munchExp e1
            val _ = emit (A.OPER{assem = "MOV `s0, `d0\t # Set up sub\nSUB `s1, `d0\t # subtract!\n", src = [e2Reg, e1Reg], dst = [retAddr]})
          in
            retAddr
          end
        | munchExp(T.BINOP(T.MUL, e1, e2)) = (* opExp MUL *)
          let
            val retAddr = Temp.newtemp()
            val e2Reg = munchExp e2
            val e1Reg = munchExp e1
            val _ = emit (A.OPER{assem = "MOV `s0, `d0\t # Set up mul\nIMUL `s1, `d0\t # multiply!\n", src = [e2Reg, e1Reg], dst = [retAddr]})
          in
            retAddr
          end *)
        | munchExp(T.BINOP(T.PLUS, e1, e2)) = (* opExp PLUS *)
          let
            val retAddr = Temp.newtemp()
            val e2Reg = munchExp e2
            val e1Reg = munchExp e1
            val _ = emit (A.OPER{assem = "MOV `s0, `d0\t # Set up add\n", src = [e2Reg], dst = [retAddr]})
            val _ = emit (A.OPER{assem = "ADD `s0, `d0\t # add!\n", src = [e1Reg], dst = [retAddr]})
          in
            retAddr
          end
        | munchExp(T.BINOP(T.MINUS, e2, e1)) = (* opExp MINUS *)
          let
            val retAddr = Temp.newtemp()
            val e2Reg = munchExp e2
            val e1Reg = munchExp e1
            val _ = emit (A.OPER{assem = "MOV `s0, `d0\t # Set up sub\n", src = [e2Reg], dst = [retAddr]})
            val _ = emit (A.OPER{assem = "SUB `s0, `d0\t # subtract!\n", src = [e1Reg], dst = [retAddr]})
          in
            retAddr
          end
        | munchExp(T.BINOP(T.MUL, e1, e2)) = (* opExp MUL *)
          let
            val retAddr = Temp.newtemp()
            val e2Reg = munchExp e2
            val e1Reg = munchExp e1
            val _ = emit (A.OPER{assem = "MOV `s0, `d0\t # Set up mul\n", src = [e2Reg], dst = [retAddr]})
            val _ = emit (A.OPER{assem = "IMUL `s0, `d0\t # multiply!\n", src = [e1Reg], dst = [retAddr]})
          in
            retAddr
          end
        | munchExp(T.BINOP(T.DIV, e1, e2)) = (* opExp DIV *)
          let
            val retAddr =  Temp.newtemp()
            val e2Reg = munchExp e2
            val e1Reg = munchExp e1
            val _ = emit (A.OPER{assem = "PUSH %ebx\n", src = [], dst = []})
            val _ = emit (A.OPER{assem = "MOV `s0, %ebx\n", src = [e2Reg], dst = []})
            val _ = emit (A.OPER{assem = "MOV `s0, %eax\n", src = [e1Reg], dst = []})
            val _ = emit (A.OPER{assem = "CDQ\n", src = [], dst = []})
            val _ = emit (A.OPER{assem = "IDIV %ebx\n", src = [], dst = []})
            val _ = emit (A.OPER{assem = "POP %ebx\n", src = [], dst = []})
            val _ = emit (A.OPER{assem = "MOV %eax, `d0\n", src = [], dst = [retAddr]})
          in
            retAddr
          end
        | munchExp(T.MEM e) = (* simpleVar a. *)
          result (fn r =>
          (emit (A.OPER{assem = "MOV (`s0), `d0\t# simple mem access\n", src = [munchExp e], dst = [r]})))
        | munchExp(T.TEMP t) = (* simpleVar c. *)
          t
        | munchExp(T.CONST(c)) = (* nilExp | intExp *)
          result (fn r =>
            emit (A.OPER{assem = "MOV $" ^ intString c ^ ", `d0\n", src = [], dst = [r]}))
        | munchExp(T.NAME(n)) = (* stringExp *)
          result (fn r =>
            emit (A.OPER{assem = "MOV $" ^ Symbol.name n ^ ", `d0\n", src = [], dst = [r]}))
        | munchExp(T.ESEQ(s, e)) = (* ESEQ *)
          (
            munchStm s;
            munchExp e
          )

        | munchExp e = (Printtree.printtree(TextIO.stdOut, T.EXP(e)); raise ErrorMsg.Error)

    in
      munchStm stm; rev (!ilist)
    end
end