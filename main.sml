structure Main = struct

   structure Tr = Translate
   structure F = X86Frame
   (* structure R = RegAlloc *)

   fun getsome (SOME x) = x

    val tempMap = 
        let
            fun add ((t, s), table) = Temp.Table.enter(table, t, s)
        in
            foldr add Temp.Table.empty ([(X86Frame.FP, "%ebp"), (X86Frame.FP, "%eax")])
        end

   fun tempname t =
    case Temp.Table.look (tempMap, t)
      of SOME s => s
       | NONE => Temp.makestring t

   fun emitproc out (Tr.PROC{body,frame}) =
     let val _ = print ("emit " ^ Symbol.name (X86Frame.name frame) ^ "\n")
        (* val _ = Printtree.printtree(out,body); *)
        val stms = Canon.linearize body
        (* val _ = app (fn s => Printtree.printtree(out,s)) stms; *)
        val stms' = Canon.traceSchedule(Canon.basicBlocks stms)
	      val instrs =   List.concat(map (CodeGen.codegen frame) stms') 
        val format0 = Assem.format(tempname)
        val live = Live.live instrs
        val _ = print (Live.printLive live)
        val alloced = Alloc.allocRecords frame live instrs
        val format1 = Assem.format(fn x => x)
      in
        TextIO.output(out, Symbol.name (X86Frame.name frame) ^ ":\n");
         TextIO.output(out, F.prologue frame);
         (* app (fn i => TextIO.output(out,format0 i)) instrs *)
         app (fn i => TextIO.output(out,format1 i)) alloced;
         TextIO.output(out, F.epilogue frame)
     end
    | emitproc out (Tr.STRING(lab,s)) = () (* TextIO.output(out,s) *)

   fun emitstring out (Tr.PROC{body,frame}) = ()
     (* | emitstring out (Tr.STRING(lab,s)) = TextIO.output(out,s) *)
     | emitstring out (Tr.STRING(lab,s)) = TextIO.output(out,X86Frame.string(lab, s))

   fun withOpenFile fname f = 
       let val out = TextIO.openOut fname
        in (f out before TextIO.closeOut out) 
	    handle e => (TextIO.closeOut out; raise e)
       end 

   fun comp filename = 
       let val absyn = Parse.parse filename
           val _ = Tr.frags := []
           (* val _ = Alloc.resetAlloc() *)
           (* val _ = Temp.resetTempsAndLabels() *)
           val _ = FindEscape.findEscape absyn
           val _ = Semant.transProg absyn
           val frags = !Tr.frags

           val non_ext = Substring.string
                         (Substring.taker (fn c => c <> #"/")
                         (Substring.trimr 1
                         (Substring.dropr (fn c => c <> #".")
                         (Substring.extract (filename, 0, NONE)))))
        
           val _ = withOpenFile (filename ^ ".s") 
                (fn out => (TextIO.output(out, ".global tigermain\n\n");
                            TextIO.output(out, ".data\n");
                            app (emitstring out) frags;
                            TextIO.output(out, "\n.text\n");
                            app (emitproc out) frags))
           val s = OS.Process.system ("gcc -m32 -static runtime.c " ^ filename ^ ".s -o " ^ non_ext)
           val removeThisBeforeSubmitting = OS.Process.system ("./" ^ non_ext)
       in
       ()
       end

  fun compile (_, [fileName]) = (comp fileName; print "AFTER"; OS.Process.success)
    | compile _ = (print "Incorrect arguments: pass a filename"; OS.Process.failure)


end



