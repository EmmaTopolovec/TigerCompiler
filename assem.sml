structure Assem = struct

  type reg = string
  type temp = Temp.temp
  type label = Temp.label

  datatype 'a instr = OPER of {assem: string,
			    dst: 'a list,
			    src: 'a list}
				 | JUMP of {assem: string,
			    jump: Temp.label list}
                 | LABEL of {assem: string, lab: Temp.label}

  fun format saytemp =
    let 
	fun speak(assem,dst,src,jump) =
	    let val saylab = Symbol.name    
		fun f(#"`":: #"s":: i::rest) = 
		    (explode(saytemp(List.nth(src,ord i - ord #"0"))) @ f rest)
		  | f( #"`":: #"d":: i:: rest) = 
		    (explode(saytemp(List.nth(dst,ord i - ord #"0"))) @ f rest)
		  | f( #"`":: #"j":: i:: rest) = 
		    (explode(saylab(List.nth(jump,ord i - ord #"0"))) @ f rest)
		  | f( #"`":: #"`":: rest) = #"`" :: f rest
		  | f( #"`":: _ :: rest) = ErrorMsg.impossible "bad Assem format"
		  | f(c :: rest) = (c :: f rest)
		  | f nil = nil
	    in implode(f(explode assem))
	    end
      in fn OPER{assem,dst,src} => speak(assem,dst,src,[])
		  | JUMP{assem,jump=j} => speak(assem,[],[],j)
	  | LABEL{assem,...} => assem
     end

end

