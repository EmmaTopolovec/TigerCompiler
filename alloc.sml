structure Alloc = struct

structure A = Assem
structure F = X86Frame

structure TT = Temp.Table

type interval = Live.interval
type register = string

datatype alloced = Reg of register | Spilled of int

fun intString i = if i >= 0 then Int.toString i else "-" ^ Int.toString (~i)

val eax = (X86Frame.RV, "%eax")
val ecx = (Temp.newtemp (), "%ecx")
val edx = (Temp.newtemp (), "%edx")
val ebx = (Temp.newtemp (), "%ebx")
val edi = (Temp.newtemp (), "%edi")
val esi = (Temp.newtemp (), "%esi")

(* val args = [ebx, edi, esi, ecx] *)
val args = [edi, esi, ecx]

val initArgs = map (fn (_, x) => x) args

val initMap = 
    let
        fun add ((t, s), table) = Temp.Table.enter(table, t, s)
    in
        foldr add Temp.Table.empty ([(F.FP, Reg "%ebp"), (F.RV, Reg "%eax")])
    end

fun insertBy (f : 'a * 'a -> bool) (x : 'a) ([] : 'a list) = [x]
  | insertBy f x (y :: ys) =
    if f (x, y) then x :: y :: ys else y :: insertBy f x ys

fun insertByFinish (i : interval) (ins : interval list) =
    insertBy (fn(t1, t2) => #finish t1 < #finish t2) i ins

fun allocRecords (frame : X86Frame.frame) (ins : interval list) (assem : (Temp.temp A.instr) list) : (register A.instr) list =
    let
        val ilist = ref (nil : (register A.instr) list)
        fun emit x = ilist := x :: !ilist

        and alloc (aenv : alloced TT.table) (* Assignment of temporaries to registers/spilled positions *)
                (useable : register list) (* Registers that have not been assigned *)
                (active : interval list) (* Intervals that are currently active, in order of increasing endpoint *)
                (intvls : interval list) (* Upcoming intervals, in order of increasing start point*)
                ([] : (int * Temp.temp A.instr) list) (* Upcoming instructions *)
                : alloced TT.table = aenv
        | alloc (aenv : alloced TT.table) (* Assignment of temporaries to registers/spilled positions *)
                (useable : register list) (* Registers that have not been assigned *)
                (active : interval list) (* Intervals that are currently active, in order of increasing endpoint *)
                (intvls : interval list) (* Upcoming intervals, in order of increasing start point*)
                ((i, instr) :: instrs : (int * Temp.temp A.instr) list) (* Upcoming instructions *)
                : alloced TT.table =
                    let                        
                        fun retrieveRegs ([] : interval list) : register list = []
                            | retrieveRegs ({temp, first, finish} :: acts : interval list) : register list =
                            (case Temp.Table.look(aenv, temp)
                                of SOME (Reg r) => r :: retrieveRegs acts
                                    | _ => retrieveRegs acts)

                        fun assignRegs (useable : register list) ([] : interval list) = (useable, aenv)
                          | assignRegs (useable : register list) ({temp, first, finish} :: actives : interval list) =
                                let
                                    val (useable', aenv') = assignRegs useable actives
                                in
                                    if temp = F.RV orelse temp = F.FP then (useable', aenv') else
                                    (case useable'
                                        of [] => ([], Temp.Table.enter(aenv', temp, Spilled (F.allocLocal2 frame)))
                                            | (reg :: useable'') => (useable'', Temp.Table.enter(aenv', temp, Reg reg)))
                                end
                                

                        val remove_actives = List.filter (fn {temp, first, finish} => finish = i) active
                        val add_actives = List.filter (fn {temp, first, finish} => first = i) intvls
                        val active' = List.filter (fn {temp, first, finish} => finish > i) active
                        val useable' = (retrieveRegs remove_actives) @ useable
                        val (useable'', aenv') = assignRegs useable' add_actives
                    in
                        alloc aenv' useable'' active' intvls instrs
                    end

        val aenv' = alloc initMap initArgs [] ins
                        (ListPair.zip ((List.tabulate (length assem, fn x => x), assem)));

        fun emitWithAenv (aenv : alloced TT.table) ([] : Temp.temp A.instr list) = ()
          | emitWithAenv (aenv : alloced TT.table) (instr :: instrs : Temp.temp A.instr list) = 
            let
                fun replaceSpills ([]) (spillTmps) regs = (spillTmps, regs)
                  | replaceSpills (tmp :: tmps) (spillTmps) (reg :: regs) =
                    (case Temp.Table.look(aenv, tmp)
                        of SOME (Spilled loc) => replaceSpills tmps (spillTmps @ [(tmp, SOME (reg, loc))]) regs
                         | _ => replaceSpills tmps (spillTmps @ [(tmp, NONE)]) (reg :: regs))
                  | replaceSpills (tmp :: tmps) (spillTmps) ([]) =
                    (case Temp.Table.look(aenv, tmp)
                        of SOME (Spilled loc) => (ErrorMsg.error 0 "ERROR: Emitted instruction has >2 spilled alloceds"; ([], []))
                         | _ => replaceSpills tmps (spillTmps @ [(tmp, NONE)]) ([]))

                fun emitSpilledDst (_, NONE) = ()
                  | emitSpilledDst (_, SOME (reg, loc)) =
                    emit (A.OPER {  assem = "MOV " ^ reg ^ ", " ^ intString loc ^ "(%ebp)\t# store dst from reg to spill\n",
                                    dst = [],
                                    src = []})

                fun emitSpilledSrc (_, NONE) = ()
                  | emitSpilledSrc (_, SOME (reg, loc)) =
                    emit (A.OPER {  assem = "MOV " ^ intString loc ^ "(%ebp), " ^ reg ^ "\t# store src from spill to reg\n",
                                    dst = [],
                                    src = []})

                fun replaceTemp (tmp, NONE) =
                    (case Temp.Table.look(aenv, tmp)
                        of SOME (Reg reg) => reg
                         | _ => "ERROR")
                  | replaceTemp (_, SOME (reg, _)) = reg

                val _ =
                    (case instr
                        of A.OPER {assem, dst, src} =>
                            let
                                val (spilledDsts, freeSpillRegs) = replaceSpills dst [] ["%edx", "%ebx"]
                                val (spilledSrcs, _) = replaceSpills src [] freeSpillRegs
                            in
                                map emitSpilledSrc spilledSrcs;
                                (emit (A.OPER { assem = assem,
                                                dst = map replaceTemp spilledDsts,
                                                src = map replaceTemp spilledSrcs}));
                                map emitSpilledDst spilledDsts;
                                ()
                            end
                         | A.JUMP {assem, jump} => emit (A.JUMP {assem=assem, jump=jump})
                         | A.LABEL {assem, lab} => emit (A.LABEL {assem=assem, lab=lab}))
            in
                emitWithAenv aenv instrs
            end

    in
        emitWithAenv aenv' assem;
        (* let
            fun replaceTemp2 (temp : Temp.temp) =
                (case Temp.Table.look(aenv', temp)
                    of SOME (Reg reg) => reg
                     | SOME (Spilled loc) => (Int.toString loc ^ "(%ebp)")
                     | NONE => "ERROR")
        in
            emit (A.OPER {  assem = "MOV `s0, %eax\t# store return val in $eax\n", 
                            src = [replaceTemp2 F.RV],
                            dst = []})
        end; *)
        rev (!ilist)
    end


end