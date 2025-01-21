structure Tr = Translate

structure FindEscape : sig val findEscape : Absyn.exp -> unit end =
struct
    type depth = int
    type escEnv = (depth * bool ref) Symbol.table

    fun traverseVar (env : escEnv) (d : depth) (v : Absyn.var) : unit =
        let
            fun trvvar (Absyn.SimpleVar (s, pos)) =
                (case Symbol.look(env, s)
                    of SOME(d2, esc) =>
                        if (d2 < d) then (esc := true) else ()
                     | _ => ())
              | trvvar (Absyn.FieldVar (var, s, pos)) = trvvar var
              | trvvar (Absyn.SubscriptVar (var, exp, pos)) =
                (trvvar var;
                traverseExp env d exp)
        in
            trvvar v
        end

    and traverseExp (env : escEnv) (d : depth) (e : Absyn.exp) : unit = 
        let
            fun trvexp (Absyn.VarExp(v)) =
                traverseVar env d v
              | trvexp (Absyn.OpExp { left, oper, right, pos} : Absyn.exp) = 
                ((traverseExp env d left);
                (traverseExp env d right))
              | trvexp (Absyn.IntExp _) = () (* Done *)
              | trvexp (Absyn.StringExp _) = () (* Done *)
              | trvexp (Absyn.LetExp {decs = declist, body, pos}) =
                let
                    fun letexp ([]) (env) = env
                      | letexp (dc :: declist : (Absyn.dec list)) (env) = 
                        let
                          val new_env = traverseDec env d dc
                        in
                          letexp declist new_env
                        end
                in
                    traverseExp (letexp declist env) d body
                end
              | trvexp (Absyn.SeqExp exps) =
                let
                    fun seqexp ([]) = ()
                      | seqexp (((e, pos) :: exps) : (Absyn.exp * Absyn.pos) list) = (trvexp e; seqexp exps)
                in
                    seqexp exps
                end
              | trvexp (Absyn.CallExp {func, args, pos}) =
                let
                    fun callexp ([]) = ()
                      | callexp ((e :: exps) : (Absyn.exp list)) = (trvexp e; callexp exps)
                in
                    callexp args
                end
              | trvexp (Absyn.NilExp) = () (* Done *)
              | trvexp (Absyn.RecordExp ({fields, typ, pos})) =
                let
                    fun recexp ([]) = ()
                      | recexp ((_, e, _) :: exps) = (trvexp e; recexp exps)
                in
                    recexp fields
                end
              | trvexp (Absyn.AssignExp ({var, exp, pos})) =
                (traverseVar env d var;
                trvexp exp)
              | trvexp (Absyn.IfExp ({test, then', else', pos})) =
                (trvexp test;
                trvexp then';
                (case else'
                    of SOME exp => trvexp exp
                     | NONE => ())
                )
              | trvexp (Absyn.WhileExp ({test, body, pos})) = 
                (trvexp test;
                trvexp body)
              | trvexp (Absyn.ForExp ({var, escape, lo, hi, body, pos})) = 
                let
                  val new_env = Symbol.enter(env, var, (d, escape))
                in
                  traverseExp new_env d lo;
                  traverseExp new_env d hi;
                  traverseExp new_env d body
                end
              | trvexp (Absyn.BreakExp (pos)) = () (* Done *)
              | trvexp (Absyn.ArrayExp ({typ, size, init, pos})) = 
                (trvexp size;
                trvexp init)
        in
            trvexp e
        end
    
    and traverseDec (env : escEnv) (d : depth) (dec : Absyn.dec) : escEnv =
        let
            fun trvdec (Absyn.FunctionDec (fs : Absyn.fundec list)) : escEnv =
                let
                    fun processParams ([]) : escEnv = env
                      | processParams ({name, escape, typ, pos} :: params) : escEnv =
                        Symbol.enter(processParams params, name, (d + 1, escape))
                    fun processFuns ([]) = ()
                      | processFuns ({name, params, result, body, pos} :: fs) =
                        (let
                            val new_env = processParams params
                        in
                            traverseExp new_env (d + 1) body
                        end;
                        processFuns fs)
                in
                    processFuns fs;
                    env
                end
              | trvdec (Absyn.TypeDec (tes : {name: Symbol.symbol, ty: Absyn.ty, pos: Absyn.pos} list)) : escEnv =
                  env
              | trvdec (Absyn.VarDec ({name, escape, typ, init, pos})) : escEnv =
                let
                    val new_env = Symbol.enter(env, name, (d, escape))
                in
                    traverseExp new_env d init;
                    new_env
                end
        in
            trvdec dec
        end

    fun findEscape (prog : Absyn.exp) : unit =  traverseExp Symbol.empty 0 prog
end