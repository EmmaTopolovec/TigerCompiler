type svalue = Tokens.svalue
type pos = int
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (svalue,pos) token

val lineNum = ErrorMsg.lineNum
val linePos = ErrorMsg.linePos
fun err(p1,p2) = ErrorMsg.error p1

val comment = ref 0
val string = ref ""
val in_string = ref false
val string_yypos = ref 0

fun eof() = 
    let val pos = hd(!linePos) in
        if (!comment > 0) then
            ErrorMsg.error pos ("Error: EOF Inside Comment")
        else if (!in_string)
            then ErrorMsg.error pos ("Error: EOF Inside String")
        else ();
        Tokens.EOF(pos, pos)
    end

%%

%s COMMENT STRING ;
%header (functor TigerLexFun(structure Tokens: Tiger_TOKENS));

%%

<INITIAL,COMMENT> "\n"  => (lineNum := !lineNum+1; linePos := yypos :: !linePos; continue());

<INITIAL> "while"  	    => (Tokens.WHILE(yypos, yypos + 5));
<INITIAL> "for"     	=> (Tokens.FOR(yypos, yypos + 3));
<INITIAL> "to"      	=> (Tokens.TO(yypos, yypos + 2));
<INITIAL> "break"  	    => (Tokens.BREAK(yypos, yypos + 5));
<INITIAL> "let"     	=> (Tokens.LET(yypos, yypos + 3));
<INITIAL> "in"      	=> (Tokens.IN(yypos, yypos + 2));
<INITIAL> "end"     	=> (Tokens.END(yypos, yypos + 3));
<INITIAL> "function" 	=> (Tokens.FUNCTION(yypos, yypos + 8));
<INITIAL> "var"     	=> (Tokens.VAR(yypos, yypos + 3));
<INITIAL> "type"  	    => (Tokens.TYPE(yypos, yypos + 4));
<INITIAL> "array"  	    => (Tokens.ARRAY(yypos, yypos + 5));
<INITIAL> "if"  	    => (Tokens.IF(yypos, yypos + 2));
<INITIAL> "then"  	    => (Tokens.THEN(yypos, yypos + 4));
<INITIAL> "else"  	    => (Tokens.ELSE(yypos, yypos + 4));
<INITIAL> "do"    	    => (Tokens.DO(yypos, yypos + 2));
<INITIAL> "of"    	    => (Tokens.OF(yypos, yypos + 2));
<INITIAL> "nil"    	    => (Tokens.NIL(yypos, yypos + 3));

<INITIAL> ","	        => (Tokens.COMMA(yypos, yypos + 1));
<INITIAL> ":"	        => (Tokens.COLON(yypos, yypos + 1));
<INITIAL> ";"	        => (Tokens.SEMICOLON(yypos, yypos + 1));
<INITIAL> "("	        => (Tokens.LPAREN(yypos, yypos + 1));
<INITIAL> ")"	        => (Tokens.RPAREN(yypos, yypos + 1));
<INITIAL> "["	        => (Tokens.LBRACK(yypos, yypos + 1));
<INITIAL> "]"	        => (Tokens.RBRACK(yypos, yypos + 1));
<INITIAL> "{"	        => (Tokens.LBRACE(yypos, yypos + 1));
<INITIAL> "}"	        => (Tokens.RBRACE(yypos, yypos + 1));
<INITIAL> "."	        => (Tokens.DOT(yypos, yypos + 1));
<INITIAL> "+"	        => (Tokens.PLUS(yypos, yypos + 1));
<INITIAL> "-"	        => (Tokens.MINUS(yypos, yypos + 1));
<INITIAL> "*"	        => (Tokens.TIMES(yypos, yypos + 1));
<INITIAL> "/"	        => (Tokens.DIVIDE(yypos, yypos + 1));
<INITIAL> "="	        => (Tokens.EQ(yypos, yypos + 1));
<INITIAL> "<>"	        => (Tokens.NEQ(yypos, yypos + 2));
<INITIAL> "<"	        => (Tokens.LT(yypos, yypos + 1));
<INITIAL> "<="	        => (Tokens.LE(yypos, yypos + 2));
<INITIAL> ">"	        => (Tokens.GT(yypos, yypos + 1));
<INITIAL> ">="	        => (Tokens.GE(yypos, yypos + 2));
<INITIAL> "&"	        => (Tokens.AND(yypos, yypos + 1));
<INITIAL> "|"	        => (Tokens.OR(yypos, yypos + 1));
<INITIAL> ":="	        => (Tokens.ASSIGN(yypos, yypos + 2));

<INITIAL> [0-9]+	    => (Tokens.INT(valOf(Int.fromString yytext), yypos, yypos + String.size yytext));
<INITIAL> [a-zA-Z][a-zA-Z0-9_]*     => (Tokens.ID(yytext, yypos, yypos + String.size yytext));

<INITIAL> "\"\""        => (Tokens.STRING("", yypos, yypos));
<INITIAL> "\""          => (string := ""; in_string := true; string_yypos := yypos; YYBEGIN STRING; continue());
<STRING> \\\"           => (string := !string ^ "\""; continue());
<STRING> \\n           => (string := !string ^ "\n"; continue());
<STRING> \\t           => (string := !string ^ "\t"; continue());
<STRING> \\\\           => (string := !string ^ "\\"; continue());
<STRING> \\\^[@A-Z\[\]\\\^_? ]   => (string := !string ^ yytext; continue());
<STRING> \\[\t\n\f ]+\\   => (continue());
<STRING> \\[0-9][0-9][0-9]  => (
    (
    if Option.valOf(Int.fromString(String.substring(yytext, 1, 3))) >= 128 then
        ErrorMsg.error yypos ("Error: Invalid ASCII code")
    else
        string := !string ^ Char.toString(Char.chr(Option.valOf(Int.fromString(String.substring(yytext, 1, 3)))))
    );
    continue()
    );
<STRING> "\""           => (YYBEGIN INITIAL; in_string := false; Tokens.STRING(!string, !string_yypos, yypos));
<STRING> "\n"           => (ErrorMsg.error yypos ("Error: Newline in String"); continue());
<STRING> \\             => (ErrorMsg.error yypos ("Error: Invalid escape character"); continue());
<STRING> .              => (string := !string ^ yytext; continue());

<INITIAL> "/*"          => (comment := !comment+1; YYBEGIN COMMENT; continue());
<COMMENT> "/*"          => (comment := !comment+1; continue());
<COMMENT> "*/"          => (comment := !comment-1; if !comment > 0 then continue() else (YYBEGIN INITIAL; continue()));
<COMMENT> .             => (continue());

<INITIAL> [\t\n\r\f ]   => (continue());

<INITIAL> .             => (ErrorMsg.error yypos ("Error: Invalid Character " ^ yytext); continue());
