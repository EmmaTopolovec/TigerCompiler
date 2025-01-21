structure Live = struct

structure A = Assem
structure TT = Temp.Table
structure F = X86Frame
structure S = Symbol

type interval = {temp : Temp.temp, first : int, finish : int}

fun dedup [] = []
  | dedup (x :: xs) = x :: dedup(List.filter (fn y => x <> y) xs)

fun diff xs ys = List.filter (fn x => List.all (fn y => x <> y) ys) xs

fun live opers : interval list =
        let
          val all_labels = ref []
          val use = ref (S.empty : (Temp.temp list) S.table)
          val def = ref (S.empty : (Temp.temp list) S.table)
          val blocks = ref S.empty

          val block_start = ref (S.empty : int S.table)
          val block_end = ref (S.empty : int S.table)


          (* Initalizing used/def/block information *)
          fun updateUse def l src = case S.look(!use, l)
                                  of SOME srcs => use := S.enter (!use, l, dedup (diff src def @ srcs))
                                    | NONE => use := S.enter(!use, l, diff src def)

          fun updateDef use l dst = case S.look(!def, l)
                                  of SOME dsts => def := S.enter (!def, l, dedup (diff dst use @ dsts))
                                    | NONE => def := S.enter(!def, l, diff dst use)

          fun updateBlocks l jmps pred =
              case S.look(!blocks, l)
                of SOME {jumps, preds} => blocks := S.enter(!blocks, l, {jumps = jmps @ jumps, preds = pred @ preds})
                  | NONE => blocks := S.enter(!blocks, l, {jumps = jmps, preds = pred})

          fun updateBlockEnd l i = case S.look(!block_end, l)
                                    of SOME j => block_end := S.enter(!block_end, l, if i > j then i else j)
                                      | NONE => block_end := S.enter(!block_end, l, i)

          fun initRefs u d l ((i, A.OPER {assem, src, dst, ...}) :: opers) =
                    (updateUse [] l src; updateDef u l dst; initRefs (dedup (src @ u)) (dedup (dst @ d)) l opers)
            | initRefs _ _ l ((i, A.JUMP {jump, ... }) :: opers) =
              (updateBlockEnd l i;
                updateBlocks l jump [];
                map (fn j => updateBlocks j [] [l]) jump;
                initRefs [] [] l opers)
            | initRefs _ _ l ((i, A.LABEL {lab, ...}) :: opers) =
              (block_start := S.enter(!block_start, lab, i);
                updateBlockEnd l i;
                updateBlocks lab [] [];
                all_labels := lab :: (!all_labels);
                initRefs [] [] lab opers)
            | initRefs _ _ _ [] = ()

          (* Finding in/out fixpoint *)
          val live_in = ref (S.empty : (Temp.temp list) S.table)
          val live_out = ref (S.empty : (Temp.temp list) S.table)

          fun updateLiveIn n t = (live_in := S.enter(!live_in, n, t); t)

          fun updateLiveOut n t = (live_out := S.enter(!live_out, n, t); t)

          val changed = ref false

          fun updateInOut l =
            let
              val (SOME {jumps, preds}) = S.look(!blocks, l)
              val jumps_in = List.concat (map (fn j => Option.getOpt (S.look(!live_in, j), [])) jumps)

              val curr_live_in = Option.getOpt(S.look(!live_in, l), [])
              val curr_live_out = Option.getOpt(S.look(!live_out, l), [])

              val live_out = updateLiveOut l jumps_in
              
              val use_l = Option.getOpt(S.look(!use, l), [])
              val def_l = Option.getOpt(S.look(!def, l), [])
              val live_in = updateLiveIn l (dedup (use_l @ (diff live_out def_l)))

              val _ = if diff live_in curr_live_in <> [] then changed := true else ()
              val _ = if diff live_out curr_live_out  <> [] then changed := true else ()
            in
            ()
            end

        fun findFix lin lout =
          let
            val _ = app updateInOut (!all_labels)
          in
          if !changed
            then (changed := false; findFix (!live_in) (!live_out))
            else (lin, lout)
          end

        val intervals_map = ref (TT.empty : interval TT.table)

        fun setFirst new_first t = case TT.look(!intervals_map, t)
                              of SOME {temp, first, finish} =>
                                if new_first < first
                                  then intervals_map := TT.enter(!intervals_map, t, {temp=temp, first=new_first, finish=finish})
                                  else ()
                                | NONE => intervals_map := TT.enter(!intervals_map, t, {temp=t, first=new_first, finish=new_first})

        fun setFinish new_finish t = case TT.look(!intervals_map, t)
                              of SOME {temp, first, finish} =>
                                  if finish < new_finish
                                    then intervals_map := TT.enter(!intervals_map, t, {temp=temp, first=first, finish=new_finish})
                                    else ()
                                | NONE => intervals_map := TT.enter(!intervals_map, t, {temp=t, first=new_finish, finish=new_finish})

        fun createIntervals () =
          app (fn l => 
                    let
                      val first = Option.getOpt(S.look(!block_start, l), ~1)
                      val finish = Option.getOpt(S.look(!block_end, l), ~1)

                      val lin = Option.getOpt(S.look(!live_in, l), [])
                      val lout = Option.getOpt(S.look(!live_out, l), [])
                      val ldef = Option.getOpt(S.look(!def, l), [])
                    in
                    app (setFirst first) (dedup (lin @ lout @ ldef)); app (setFinish finish) (dedup (lin @ lout @ ldef))
                    end) (!all_labels)
        

        val num_ops = ListPair.zip (List.tabulate (length opers, fn x => x), opers)

        val _ = (initRefs [] [] (Temp.newlabel ()) num_ops; findFix S.empty S.empty)
        val _ = createIntervals ()
        in
        ListMergeSort.sort (fn(t1, t2) => #first t1 > #first t2) (TT.list (!intervals_map))
        end

  fun printInterval ({ temp, first, finish }) =
      Temp.makestring temp ^ ": " ^ Int.toString first ^ " - " ^ Int.toString finish

  fun printLive live = String.concatWith "\n" (map printInterval live)
end