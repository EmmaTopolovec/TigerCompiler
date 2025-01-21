structure A = Absyn
structure T = Types

structure Semant =
struct
  type venv = Env.enventry Symbol.table
  type tenv = T.ty Symbol.table

  val inloop : int ref = ref 0

  fun actualTy (tenv) (ty) : T.ty = 
    (case ty
      of T.NAME(name, r) =>
        (case (!r)
          of SOME typ => (actualTy tenv typ)
           | NONE => ty)
       | x => x)

  fun equalTypes (T.NIL : T.ty) (T.RECORD(_,_) : T.ty) : bool = true
    | equalTypes (T.RECORD(_,_) : T.ty) (T.NIL : T.ty) : bool = true
    | equalTypes (T.ARRAY(s1,u1)) (T.ARRAY(s2,u2)) = (u1 = u2)
    | equalTypes (T.RECORD(f1,u1)) (T.RECORD(f2,u2)) = (u1 = u2)
    | equalTypes (T.NAME(s1,_)) (T.NAME(s2,_)) = (s1 = s2)
    | equalTypes (T.BOTTOM) (_) = true
    | equalTypes (_) (T.BOTTOM) = true
    | equalTypes (ty1 : T.ty) (ty2 : T.ty) : bool =
      (ty1 = ty2)

  fun checkInt (pos : A.pos) (ty : T.ty) =
      case ty
          of T.INT => ()
           | T.BOTTOM => ()
           | _ => ErrorMsg.error pos "TYPE: Expected Int, got other type";

  fun checkEq (pos : A.pos) (T.BOTTOM) (_) = true
    | checkEq (pos : A.pos) (_) (T.BOTTOM) = true
    | checkEq (pos : A.pos) (T.INT) (T.INT) = true
    | checkEq (pos : A.pos) (T.STRING) (T.STRING) = true
    | checkEq (pos : A.pos) (T.RECORD(f1,u1)) (T.RECORD(f2,u2)) = (f1 = f2 andalso u1 = u2)
    | checkEq (pos : A.pos) (T.RECORD(_,_)) (T.NIL) = true
    | checkEq (pos : A.pos) (T.NIL) (T.RECORD(_,_)) = true
    | checkEq (pos : A.pos) (T.ARRAY(s1,u1)) (T.ARRAY(s2,u2)) = (s1 = s2 andalso u1 = u2)
    | checkEq (pos : A.pos) (ty1 : T.ty) (ty2 : T.ty) = (ErrorMsg.error pos "TYPE: these types cannot be compared with = or <>"; false)

  fun checkComp (pos : A.pos) (T.BOTTOM) (_) = true
    | checkComp (pos : A.pos) (_) (T.BOTTOM) = true
    | checkComp (pos : A.pos) (T.INT) (T.INT) = true
    | checkComp (pos : A.pos) (T.STRING) (T.STRING) = true
    | checkComp (pos : A.pos) (ty1 : T.ty) (ty2 : T.ty) = (ErrorMsg.error pos "TYPE: these types cannot be compared"; false)
  
  fun lookupTy (pos : A.pos) (ty_sym : A.symbol) (tenv : tenv) : T.ty =
      case Symbol.look (tenv, ty_sym)
        of SOME (T.NAME (_, r)) =>
              (case !r
                of SOME ty => ty
                  | NONE => (ErrorMsg.error pos ("SCOPE: Did not recognize type " ^ Symbol.name ty_sym); T.BOTTOM))
         | SOME ty => ty
         | NONE => (ErrorMsg.error pos ("SCOPE: Did not recognize type " ^ Symbol.name ty_sym); T.BOTTOM)

  fun transVar (venv : venv) (tenv : tenv) (v : A.var) (level : Translate.level) (break_lab : Temp.label option) : (Translate.exp * T.ty * bool) = 
    let
      fun trvar (A.SimpleVar (s, pos)) : {exp : Translate.exp, s: Symbol.symbol, ty: T.ty, a : bool} =
            (case Symbol.look(venv, s) of
                SOME (Env.VarEntry { ty, assignable, access }) => ({exp=Translate.simpleVar(access, level), s=s, ty=ty, a=assignable})
              | NONE => (ErrorMsg.error pos "SCOPE: variable not found"; {exp=Translate.nilExp(), s=Symbol.symbol "none", ty=T.BOTTOM, a=true}))
        | trvar (A.FieldVar (var, s, pos)) : {exp : Translate.exp, s: Symbol.symbol, ty: T.ty, a : bool} = 
            let
              val {exp=exp, s=varsym, ty=varty, a=a} = trvar var
            in
              (case (actualTy tenv varty)
                of T.RECORD(fields, unique) => 
                  let
                    fun checkid ([]) (id : Symbol.symbol) (i : int) = (ErrorMsg.error pos "SCOPE: given record field does not exist"; ({exp=Translate.nilExp(), s=id, ty=T.BOTTOM, a=true}))
                      | checkid ((((s,t) :: fs) : (Symbol.symbol * T.ty) list)) (id : Symbol.symbol) (i : int) =
                        (if (s = id) then ({exp=(Translate.fieldVar exp i), s=s, ty=(actualTy tenv t), a=true}) else checkid fs id (i+1))
                  in
                    checkid fields s 0
                  end
                 | _ =>  (ErrorMsg.error pos "SCOPE: id in scope is not a record"; {exp=Translate.nilExp(), s = Symbol.symbol "none", ty=T.BOTTOM, a=true}))
            end
        | trvar (A.SubscriptVar (var, exp, pos)) : {exp : Translate.exp, s: Symbol.symbol, ty: T.ty, a : bool} = 
            let
              val {exp=varexp, s=varsym, ty=varty, a=a} = trvar var
              val (translate_exp, exp_type) = transExp venv tenv exp level break_lab
            in
              (case (actualTy tenv varty)
                of T.ARRAY(ty, unique) =>
                  ((if (equalTypes T.INT (actualTy tenv (exp_type))) then () else (ErrorMsg.error pos "TYPE: array subscript must be an int"));
                  {exp=(Translate.subscriptVar varexp translate_exp), s=varsym, ty=(actualTy tenv ty), a=a})
                | _ => (ErrorMsg.error pos "SCOPE: id must be an array"; {exp=Translate.nilExp(), s=Symbol.symbol "none", ty=T.BOTTOM, a=true}))
            end
    in
      let 
        val {exp=exp, s=varsym, ty=varty, a=a} = trvar v 
      in
        (exp, varty, a)
      end
    end
      
    

  and transExp (venv : venv) (tenv : tenv) (e : A.exp) (level : Translate.level) (break_lab : Temp.label option) : (Translate.exp * T.ty) =
    let
      fun letexp ((dec :: []) : A.dec list) (venv : venv) (tenv : tenv) : (Translate.exp list * {venv : venv, tenv : tenv}) =
          let 
            val (exps, {venv=venv2, tenv=tenv2}) = transDec venv tenv dec level break_lab
          in
            (exps, {venv = venv2, tenv = tenv2})
          end
        | letexp ((dec :: declist) : A.dec list) (venv : venv) (tenv : tenv) : (Translate.exp list * {venv : venv, tenv : tenv}) =
          let
            val (exps, {venv=venv2, tenv=tenv2}) = transDec venv tenv dec level break_lab
            val (exps2, {venv=venv3, tenv=tenv3}) = letexp declist venv2 tenv2
          in
            (exps @ exps2, {venv=venv3, tenv=tenv3})
          end
      and seqexp ([]) : (Translate.exp list * T.ty) = ([], T.UNIT)
        | seqexp (((e, pos) :: []) : (A.exp * A.pos) list) : (Translate.exp list * T.ty) =
          let
            val (eExp, eTy) = (trexp e)
          in
            ([eExp], eTy)
          end
        | seqexp (((e, pos) :: exps) : (A.exp * A.pos) list) : (Translate.exp list * T.ty) =
          let
            val (eExp, eTy) = (trexp e)
            val (seqExps, seqTy) = seqexp exps
          in
            (eExp :: seqExps, seqTy)
          end
      and trexp (A.VarExp(v)) = 
          (case (transVar venv tenv v level break_lab)
            of (exp, t, _) => (exp, t))
        | trexp (A.OpExp { left, oper=A.PlusOp, right, pos} : A.exp) : (Translate.exp * T.ty) =
          let
            val (leftExp, leftTy) = trexp left
            val (rightExp, rightTy) = trexp right
          in
            (checkInt pos (actualTy tenv leftTy);
            checkInt pos (actualTy tenv rightTy);
            ((Translate.opExp leftExp A.PlusOp rightExp leftTy), T.INT))
          end
        | trexp (A.OpExp { left, oper=A.MinusOp, right, pos} : A.exp) : (Translate.exp * T.ty) =
          let
            val (leftExp, leftTy) = trexp left
            val (rightExp, rightTy) = trexp right
          in
            (checkInt pos (actualTy tenv leftTy);
            checkInt pos (actualTy tenv rightTy);
            ((Translate.opExp leftExp A.MinusOp rightExp leftTy), T.INT))
          end
        | trexp (A.OpExp { left, oper=A.TimesOp, right, pos} : A.exp) : (Translate.exp * T.ty) =
          let
            val (leftExp, leftTy) = trexp left
            val (rightExp, rightTy) = trexp right
          in
            (checkInt pos (actualTy tenv leftTy);
            checkInt pos (actualTy tenv rightTy);
            ((Translate.opExp leftExp A.TimesOp rightExp leftTy), T.INT))
          end
        | trexp (A.OpExp { left, oper=A.DivideOp, right, pos} : A.exp) : (Translate.exp * T.ty) =
          let
            val (leftExp, leftTy) = trexp left
            val (rightExp, rightTy) = trexp right
          in
            (checkInt pos (actualTy tenv leftTy);
            checkInt pos (actualTy tenv rightTy);
            ((Translate.opExp leftExp A.DivideOp rightExp leftTy), T.INT))
          end
        | trexp (A.OpExp { left, oper=A.EqOp, right, pos} : A.exp) : (Translate.exp * T.ty) =
          let
            val (leftExp, leftTy) = trexp left
            val (rightExp, rightTy) = trexp right
          in
            (checkEq pos (actualTy tenv leftTy) (actualTy tenv rightTy);
            ((Translate.opExp leftExp A.EqOp rightExp leftTy), T.INT))
          end
        | trexp (A.OpExp { left, oper=A.NeqOp, right, pos} : A.exp) : (Translate.exp * T.ty) =
          let
            val (leftExp, leftTy) = trexp left
            val (rightExp, rightTy) = trexp right
          in
            (checkEq pos (actualTy tenv leftTy) (actualTy tenv rightTy);
            ((Translate.opExp leftExp A.NeqOp rightExp leftTy), T.INT))
          end
        | trexp (A.OpExp { left, oper=A.LtOp, right, pos} : A.exp) : (Translate.exp * T.ty) =
          let
            val (leftExp, leftTy) = trexp left
            val (rightExp, rightTy) = trexp right
          in
            (checkEq pos (actualTy tenv leftTy) (actualTy tenv rightTy);
            ((Translate.opExp leftExp A.LtOp rightExp leftTy), T.INT))
          end
        | trexp (A.OpExp { left, oper=A.LeOp, right, pos} : A.exp) : (Translate.exp * T.ty) =
          let
            val (leftExp, leftTy) = trexp left
            val (rightExp, rightTy) = trexp right
          in
            (checkEq pos (actualTy tenv leftTy) (actualTy tenv rightTy);
            ((Translate.opExp leftExp A.LeOp rightExp leftTy), T.INT))
          end
        | trexp (A.OpExp { left, oper=A.GtOp, right, pos} : A.exp) : (Translate.exp * T.ty) =
          let
            val (leftExp, leftTy) = trexp left
            val (rightExp, rightTy) = trexp right
          in
            (checkEq pos (actualTy tenv leftTy) (actualTy tenv rightTy);
            ((Translate.opExp leftExp A.GtOp rightExp leftTy), T.INT))
          end
        | trexp (A.OpExp { left, oper=A.GeOp, right, pos} : A.exp) : (Translate.exp * T.ty) =
          let
            val (leftExp, leftTy) = trexp left
            val (rightExp, rightTy) = trexp right
          in
            (checkEq pos (actualTy tenv leftTy) (actualTy tenv rightTy);
            ((Translate.opExp leftExp A.GeOp rightExp leftTy), T.INT))
          end
        | trexp (A.IntExp i) = ((Translate.intExp i), T.INT)
        | trexp (A.StringExp (s, p)) = ((Translate.stringExp s), T.STRING)
        | trexp (A.LetExp ({decs = [], body, pos})) =
          let
            val (bodyExp, bodyTy) = (transExp venv tenv body level break_lab)
          in
            ((Translate.letExp [] bodyExp), bodyTy)
          end
        | trexp (A.LetExp {decs = declist, body, pos}) = 
          let
            val (exps, {venv=venv2, tenv=tenv2}) = letexp declist venv tenv
            val (bodyExp, bodyTy) = transExp venv2 tenv2 body level break_lab
          in
            (Translate.letExp exps bodyExp, bodyTy)
          end
        | trexp (A.SeqExp [(e, _)]) =
          let
            val (eExp, eTy) = (trexp e)
          in
            (Translate.seqExp [eExp], eTy)
          end
        | trexp (A.SeqExp exps) =
          let
            val (seqExps, seqTy) = seqexp exps
          in
            ((Translate.seqExp seqExps), seqTy)
          end
        | trexp (A.CallExp {func, args, pos}) =
          (case Symbol.look (venv, func)
            of SOME (Env.FunEntry {formals, result, level=declevel, label} ) => 
                let 
                  fun checkargslength ([] : T.ty list) ([] :  A.exp list) (pos : A.pos) = true
                    | checkargslength (formals : T.ty list) ([] :  A.exp list) (pos : A.pos) = 
                      (ErrorMsg.error pos "SCOPE: missing argument(s)"; false)
                    | checkargslength ([] : T.ty list) (args :  A.exp list) (pos : A.pos) = 
                      (ErrorMsg.error pos "SCOPE: extraneous argument(s)"; false)
                    | checkargslength ((formal :: formals) : T.ty list) ((arg :: args) : A.exp list) (pos : A.pos) =
                      checkargslength formals args pos

                  fun checkargstypes ([] : T.ty list) ([] :  A.exp list) (pos : A.pos) : Translate.exp list = []
                    | checkargstypes (formals : T.ty list) ([] :  A.exp list) (pos : A.pos) : Translate.exp list = []
                    | checkargstypes ([] : T.ty list) (args :  A.exp list) (pos : A.pos) : Translate.exp list = []
                    | checkargstypes ((formal :: formals) : T.ty list) ((arg :: args) : A.exp list) (pos : A.pos) : Translate.exp list =
                      let
                        val (argExp, argTy) = trexp arg
                      in
                        ((if (equalTypes (actualTy tenv formal) (actualTy tenv argTy)) then () else (ErrorMsg.error pos "TYPE: function argument is incorrect type"));
                        argExp :: (checkargstypes formals args pos))
                      end
                in
                  let
                    val argExpList = (if (checkargslength formals args pos) then (checkargstypes formals args pos) else ([]))
                  in
                    (Translate.callExp level declevel func label argExpList, result)
                  end
                end
             | _ => (ErrorMsg.error pos "SCOPE: function is out of scope"; (Translate.nilExp(), T.BOTTOM)))
        | trexp (A.NilExp) = (Translate.nilExp(), T.NIL)
        | trexp (A.RecordExp ({fields, typ, pos})) = 
          (case Symbol.look (tenv, typ)
            of SOME ty => 
                let
                  val givenfields =
                    case (actualTy tenv ty)
                      of T.RECORD(givenfields, _) => givenfields
                       | _ => (ErrorMsg.error pos "TYPE: type must be record"; [])
                  fun checkfields ([]) ([]) (pos : A.pos) : Translate.exp list = []
                    | checkfields (f1) ([]) (pos : A.pos) : Translate.exp list = 
                      (ErrorMsg.error pos "SCOPE: missing record field(s)"; [])
                    | checkfields ([]) (f2) (pos : A.pos) : Translate.exp list = 
                      (ErrorMsg.error pos "SCOPE: extraneous record field(s)"; [])
                    | checkfields (((s1,e1,_) :: f1s) : (A.symbol * A.exp * A.pos) list) (((s2,t2) :: f2s) : (Symbol.symbol * T.ty) list) (pos : A.pos) : Translate.exp list =
                      let
                        val (e1Exp, e1Ty) = (trexp e1)
                      in
                        ((if (equalTypes (actualTy tenv e1Ty) (actualTy tenv t2)) then () else (ErrorMsg.error pos "TYPE: record field is not the expected type"));
                        (if (s1 = s2) then () else (ErrorMsg.error pos "SCOPE: record field is not the expected name"));
                        e1Exp :: checkfields f1s f2s pos)
                      end
                in
                  (Translate.recordExp (checkfields fields givenfields pos), ty)
                end
             | _ => (ErrorMsg.error pos "SCOPE: record type is out of scope"; (Translate.nilExp(), T.BOTTOM)))
        | trexp (A.AssignExp ({var, exp, pos})) = 
          let
            val (varExp, vartyp, a) = transVar venv tenv var level break_lab
            val (expExp, expTy) = trexp exp
          in
            ((if (a) then () else (ErrorMsg.error pos "READONLY: variable is not assignable"));
            (if (equalTypes (actualTy tenv vartyp) (actualTy tenv expTy)) then () else (ErrorMsg.error pos "TYPE: exp must be the same type as the var"));
            (Translate.assignExp varExp expExp, T.UNIT))
          end
        | trexp (A.IfExp ({test, then', else', pos})) = 
          let
            val (testExp, testTy) = trexp test
            val (thenExp, thenTy) = trexp then'
          in
            (checkInt pos (actualTy tenv testTy);
            (case else' of 
              SOME(exp) => 
                let
                  val (elseExp, elseTy) = trexp exp
                in
                  ((if (equalTypes (actualTy tenv thenTy) (actualTy tenv elseTy)) then () else (ErrorMsg.error pos "TYPE: then and else return types do not match"));
                  (Translate.ifExp(testExp, thenExp, SOME(elseExp)), thenTy))
                end
            | NONE =>
                ((if (equalTypes (actualTy tenv thenTy) T.UNIT) then () else (ErrorMsg.error pos "TYPE: if-then must return unit"));
                (Translate.ifExp(testExp, thenExp, NONE), T.UNIT))
            ))
          end
        | trexp (A.WhileExp ({test, body, pos})) = 
          let
            val while_break = Temp.newlabel()
            val (testExp, testTy) = trexp test
            val (bodyExp, bodyTy) = transExp venv tenv body level (SOME while_break)
          in
            (checkInt pos (actualTy tenv testTy);
            inloop := !inloop + 1;
            if (equalTypes (actualTy tenv bodyTy) T.UNIT) then () else (ErrorMsg.error pos "TYPE: return type of while body must be UNIT");
            inloop := !inloop - 1;
            (Translate.whileExp while_break testExp bodyExp, T.UNIT))
          end
        | trexp (A.ForExp ({var, escape, lo, hi, body, pos})) =
          let
            val for_break = Temp.newlabel()
            val (loExp, loTy) = trexp lo
            val (hiExp, hiTy) = trexp hi
          in
            ((if (equalTypes T.INT (actualTy tenv loTy)) then () else (ErrorMsg.error pos "TYPE: lo expr must be an int"));
            (if (equalTypes T.INT (actualTy tenv hiTy)) then () else (ErrorMsg.error pos "TYPE: hi expr must be an int"));
            inloop := !inloop + 1;
            let 
              val varAccess = (Translate.allocLocal level (!escape))
              val venv2 = Symbol.enter (venv, var, Env.VarEntry({ty=T.INT, assignable=false, access=varAccess}))
              val varExp = Translate.simpleVar(varAccess, level)
              val (bodyExp, bodyTy) = (transExp venv2 tenv body level (SOME for_break))
            in
              (Translate.printAccess var varAccess;
              if (equalTypes (actualTy tenv bodyTy) T.UNIT) then () else (ErrorMsg.error pos "TYPE: return type of for body must be UNIT");
              inloop := !inloop - 1;
              (Translate.forExp for_break varExp loExp hiExp bodyExp, T.UNIT))
            end)
          end
        | trexp (A.BreakExp (pos)) = 
          (if !inloop = 0 then ErrorMsg.error pos "MISPLACED: break statement is not inside a loop" else ();
          (case break_lab
            of SOME break_label => (Translate.breakExp (break_label), T.UNIT)
             | _ => (ErrorMsg.error pos "MISPLACED: no break label found"; ((Translate.nilExp()), T.UNIT))))
        | trexp (A.ArrayExp ({typ, size, init, pos})) = 
          let
            val (sizeExp, sizeTy) = trexp size
            val (initExp, initTy) = trexp init
          in
            ((if (equalTypes (actualTy tenv sizeTy) T.INT) then () else (ErrorMsg.error pos "TYPE: array size must be an int"));
            (case Symbol.look (tenv, typ)
              of (SOME ty1) => 
                (case (actualTy tenv ty1)
                  of T.ARRAY(ty2, _) => 
                    ((if (equalTypes (actualTy tenv initTy) (actualTy tenv ty2)) then () else (ErrorMsg.error pos "TYPE: array init must match array type"));
                    (Translate.arrayExp sizeExp initExp, ty1))
                  | _ => (ErrorMsg.error pos "TYPE: type must be an array"; (Translate.nilExp(), T.BOTTOM)))
              | _ => (ErrorMsg.error pos "SCOPE: array type is out of scope"; (Translate.nilExp(), T.BOTTOM))))
          end
    in
      trexp e
    end
    
  and transTy ((tenv, e) : tenv * A.ty) : T.ty =
    let
      fun trty (A.NameTy (s, r)) : T.ty = 
          (case Symbol.look(tenv, s)
            of SOME x => x
             | NONE => (ErrorMsg.error 0 "SCOPE: named type not in scope"; T.NAME(s, ref(NONE))))
        | trty (A.RecordTy (fields : A.field list)) : T.ty = 
          let
            fun getRecFields ([] : A.field list) : (Symbol.symbol * T.ty) list = []
              | getRecFields ({name, escape, typ, pos} :: fields : A.field list) : (Symbol.symbol * T.ty) list =
                (case Symbol.look(tenv, typ)
                  of SOME x => (name, x) :: (getRecFields fields)
                   | NONE => (ErrorMsg.error pos "SCOPE: record field type not in scope"; (name, T.BOTTOM) :: (getRecFields fields)))

            val recFields = getRecFields fields
            val unique = ref ()
          in
            T.RECORD (recFields, unique)
          end
        | trty (A.ArrayTy (s, pos)) : T.ty =
          T.ARRAY(transTy(tenv, A.NameTy(s, pos)), ref())
    in
      trty e
    end
  
  and transDec (venv : venv) (tenv : tenv) (d : A.dec) (level : Translate.level) (break_lab : Temp.label option) : ((Translate.exp list) * { venv : venv, tenv : tenv}) =
    let
      fun getBoolListFromFormals [] = []
        | getBoolListFromFormals ({name, escape, typ, pos} :: params) =
          (!escape) :: (getBoolListFromFormals params)
      
      and getFunEntry ({name, params, result, body, pos} : A.fundec)
                              : ((Symbol.symbol * Env.enventry)
                                      * A.exp
                                      * (Symbol.symbol * Env.ty) list
                                      * A.pos) = 
          let
              fun fieldType ({typ, pos, ...} : A.field) = lookupTy pos typ tenv

              val arg_info = map (fn {name, typ, pos, escape} =>
                                              (name, lookupTy pos typ tenv) )
                              params

              val res = case result
                          of SOME (r, p) => lookupTy p r tenv
                           | NONE => T.UNIT

              val funLabel = Temp.newlabel()

          in
          ((name, Env.FunEntry { formals = map fieldType params, result = res, level=Translate.newLevel({parent=level, name=funLabel, formals=(getBoolListFromFormals params)}), label=funLabel}), body, arg_info, pos)
          end

      and trdec (A.FunctionDec (fs : A.fundec list)) : ((Translate.exp list) * { venv : venv, tenv : tenv}) =
        let
          (* Collecting information *)
          val fes = map getFunEntry fs

          (* Putting FunEntries in venv *)
          val fun_entries = map (fn (x, _, _, _) => x) fes

          fun insert (v : 'a Symbol.table) (xs : (Symbol.symbol * 'a) list) =
            List.foldl (fn ((n, x), v') => Symbol.enter(v', n, x) ) v xs

          fun insertArgs (v : Env.enventry Symbol.table) ([] : (Symbol.symbol * Env.ty) list) (_ : Translate.access list) : Env.enventry Symbol.table =
                v
            | insertArgs v ((n, t) :: xs) (a :: accs : Translate.access list) : Env.enventry Symbol.table = 
                insertArgs (Symbol.enter (v, n, Env.VarEntry({ty=t, assignable=true, access=a}))) xs accs

          val new_venv = insert venv fun_entries

          fun removeStaticLink (x :: xs) = xs

          (* Semantic checking of function declarations *)
          fun checkFunEntry (s) (Env.FunEntry { formals, result, level, label }) (ars : (Symbol.symbol * Env.ty) list) (body : A.exp) (pos : A.pos) =
            let
                  (* Before checking the body of the expression, we want the value environemnt
                  to have all of the function fields inserted int it *)
                  val ars_venv = insertArgs new_venv ars (removeStaticLink (Translate.formals level))

                  val (exp_body, ty_body) = transExp ars_venv tenv body level break_lab

                  (* val _ = Printtree.printtree(TextIO.stdOut, Tree.EXP(Translate.toEx(exp_body))) *)

                  val _ = Translate.procEntryExit ({level=level, body=exp_body})
            in
              (Translate.printLevel s level;
              if (equalTypes (actualTy tenv result) (actualTy tenv ty_body)) then () else (ErrorMsg.error pos "TYPE: unexpected result type"))
            end

          fun checkAllFunEntry ([] : ((Symbol.symbol * Env.enventry) * A.exp * (Symbol.symbol * Env.ty) list * A.pos) list) = ()
            | checkAllFunEntry (((s, fe), b, ars, pos) :: xs) =
              (checkFunEntry s fe ars b pos;
              checkAllFunEntry xs)

          fun checkForDupes ([] : ((Symbol.symbol * Env.enventry) * A.exp * (Symbol.symbol * Env.ty) list * A.pos) list) (_ : ((Symbol.symbol * Env.enventry) * A.exp * (Symbol.symbol * Env.ty) list * A.pos) list) = ()
            | checkForDupes (((s1, fe1), b1, ars1, pos1) :: xs1) ( _ :: fes2) = 
              (checkDupe s1 fes2;
              checkForDupes xs1 fes2)

          and checkDupe (s1 : Symbol.symbol) ([] : ((Symbol.symbol * Env.enventry) * A.exp * (Symbol.symbol * Env.ty) list * A.pos) list) = ()
            | checkDupe (s1 : Symbol.symbol) ((((s2, fe2), b2, ars2, pos2) :: xs2) : ((Symbol.symbol * Env.enventry) * A.exp * (Symbol.symbol * Env.ty) list * A.pos) list) =
              ((if (s1 = s2) then (ErrorMsg.error pos2 "DUPLICATE: two functions with same name") else ());
              checkDupe s1 xs2)

        in
          (checkAllFunEntry fes;
          checkForDupes fes fes;
          ([], {venv = new_venv, tenv = tenv}))
        end
        
        | trdec (A.VarDec ({name, escape, typ, init, pos})) : ((Translate.exp list) * { venv : venv, tenv : tenv}) = 
          (case typ of
              SOME (s, pos) => 
                let
                  val varAccess = Translate.allocLocal level (!escape)
                  val (initExp, initTy) = transExp venv tenv init level break_lab
                  val varExp = Translate.simpleVar (varAccess, level)
                  val assignExp = (Translate.assignExp varExp initExp)
                in
                  (case Symbol.look(tenv, s)
                    of SOME t => (
                            (if (equalTypes (actualTy tenv t) (actualTy tenv (initTy))) then () else (ErrorMsg.error pos "TYPE: var type does not match init exp type");
                            Translate.printAccess name varAccess;
                            ([assignExp], {venv = Symbol.enter(venv, name, (Env.VarEntry({ty=(actualTy tenv t), assignable=true, access=varAccess}))), tenv = tenv})))
                    | _ => (ErrorMsg.error pos "SCOPE: var type is out of scope"; 
                            Translate.printAccess name varAccess;
                            ([Translate.nilExp()], {venv = Symbol.enter(venv, name, (Env.VarEntry({ty=T.BOTTOM, assignable=true, access=varAccess}))), tenv = tenv}))
                  )
                end
            | _ => (
              let
                val varAccess = Translate.allocLocal level (!escape)
                val (initExp, initTy) = transExp venv tenv init level break_lab
                val varExp = Translate.simpleVar (varAccess, level)
                val assignExp = (Translate.assignExp varExp initExp)
              in
                ((if (T.NIL = (actualTy tenv initTy)) then (ErrorMsg.error pos "TYPE: cannot infer var type with nil") else ());
                Translate.printAccess name varAccess;
                ([assignExp], {venv = Symbol.enter(venv, name, (Env.VarEntry({ty=initTy, assignable=true, access=varAccess}))), tenv = tenv}))
              end)
            )

        | trdec (A.TypeDec (tes : {name: Symbol.symbol, ty: A.ty, pos: A.pos} list)) : ((Translate.exp list) * { venv : venv, tenv : tenv}) = 
          let
            fun checkForDupes ([] : {name: Symbol.symbol, ty: A.ty, pos: A.pos} list) (_ : {name: Symbol.symbol, ty: A.ty, pos: A.pos} list) = []
              | checkForDupes ({name=s1, ty=t1, pos=pos1} :: xs1 : {name: Symbol.symbol, ty: A.ty, pos: A.pos} list) (_ :: tes2 : {name: Symbol.symbol, ty: A.ty, pos: A.pos} list) = 
                ((checkDupe {name=s1, ty=t1, pos=pos1} tes2) @ (checkForDupes xs1 tes2))

            and checkDupe ({name=s1, ty=t1, pos=pos1}) ([] : {name: Symbol.symbol, ty: A.ty, pos: A.pos} list) = [{name=s1, ty=t1, pos=pos1}]
              | checkDupe ({name=s1, ty=t1, pos=pos1}) ({name=s2, ty=t2, pos=pos2} :: xs2 : {name: Symbol.symbol, ty: A.ty, pos: A.pos} list) =
                (if (s1 = s2) then ((ErrorMsg.error pos2 "DUPLICATE: two types with same name"); []) else (checkDupe {name=s1, ty=t1, pos=pos1} xs2))

            fun makeTempTenv ([]) (tenv) = tenv
              | makeTempTenv ({name, ty, pos} :: tes) (tenv) = 
                makeTempTenv tes (Symbol.enter(tenv, name, T.NAME(name, ref(NONE))))

            val t' = makeTempTenv (checkForDupes tes tes) tenv

            fun updateRefs (t') ([] : {name: Symbol.symbol, ty: A.ty, pos: A.pos} list) = t'
              | updateRefs (t') ({name=n, ty=x, pos=p} :: xs: {name: Symbol.symbol, ty: A.ty, pos: A.pos} list) = 
                (case Symbol.look(t', n)
                  of SOME (T.NAME(s, r)) => (r := SOME (transTy(t', x)); updateRefs t' xs))

            val new_tenv = updateRefs t' tes

            fun inList (s) ([]) = false
              | inList (s) (s2 :: sList) = if (s = s2) then (true) else (inList s sList)

            fun checkForInfiniteTypeRecursion (t') (name) (pos) (visited) =
                (case Symbol.look(t', name)
                  of (SOME (T.NAME(s1,r1))) =>
                      (case (!r1)
                        of SOME (T.NAME(s2, r2)) =>
                          (if (inList s2 visited)
                            then (r1 := SOME T.BOTTOM; ErrorMsg.error pos "LOOP: invalid mutually recursive types"; ())
                            else (checkForInfiniteTypeRecursion t' s2 pos (name :: visited)))
                        | _ => ())
                   | _ => ())

            fun checkForInfiniteTypeRecursions (t') ([]) = ()
              | checkForInfiniteTypeRecursions (t') ({name, ty, pos} :: tes) =
                (checkForInfiniteTypeRecursion t' name pos [];
                checkForInfiniteTypeRecursions t' tes)
          in
            (checkForInfiniteTypeRecursions t' tes;
            ([], {venv = venv, tenv = t'}))
          end
    in
      trdec d
    end

  fun transProg e = 
    let
      val level = Translate.newLevel {parent = Translate.outermost, name = Temp.namedlabel "tigermain" , formals = []}
      val (e, _) = transExp Env.base_venv Env.base_tenv e level NONE
    in
      Translate.procEntryExit {level = level, body = e}
    end
end