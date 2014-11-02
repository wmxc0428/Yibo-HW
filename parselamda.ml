(*test function*)
exception ERROR_CHAR
fun printchars i str = if i<String.size(str) then 
							(print (String.substring( str, i, 1)); print "\n"; (printchars (i+1) str))
						else (print "");


fun printstr str = printchars 0 str;

val alphabet = "abcdefghijklmnopqrstuvwxyz";
fun is_char_alphabet i char = if i<String.size(alphabet) then
									if String.substring(alphabet,i,1)=char then
										true
									else
										is_char_alphabet (i+1) char
								else 
									false
							

fun is_alphabet char = is_char_alphabet 0 char;

fun head str = String.substring(str,0,1);
fun tail str = String.extract(str,1,NONE);

fun filterWhiteSpace str = let val h=(head str)
								val t=(tail str)
						    in	
								if String.size(str)>1 then
									if (h=" ") then
										filterWhiteSpace t
									else
										h ^ (filterWhiteSpace t)
								else if String.size(str)=1 then
									if (h=" ") then
										""
									else
										h
								else 
									""
							end

(* \x.x input= x.x *)
fun lamda_len i lamstr  = let val h=(head lamstr)
							 val t=(tail lamstr)
							 val result= if String.size(lamstr)>1 then
											 if i>0 then
												if is_alphabet h then
													1+(lamda_len i t)
												else if h="(" then
													1+(lamda_len (i+1) t)
												else if h=")" then
													1+(lamda_len (i-1) t)
												else
													1+(lamda_len i t)
											 else
												  0
										 else if String.size(lamstr)=1 then
											if i>0 then
											  if is_alphabet h then
												  1
											  else if h="(" then
												  raise ERROR_CHAR
											  else if h=")" then
												  1
											  else
											      raise ERROR_CHAR
											else
											   0
										 else
											0 
						  in
							  result
					      end
								 
						  

fun parseLam lamstr parse1 =  let val h=(head lamstr)
									val t=(tail lamstr)
								in
									if (h<>".") then 
										(LAM(h,(parseLam t parse1)))
									else 
										
										(parse1 t)
									
								end
								

fun bracketlength i str = let val h = (head str)
							  val t = (tail str)
							  val result=if String.size(str)>1 then
										  if i>0 then
											  if is_alphabet h then
												1+(bracketlength i t)
											  else if h="(" then
												1+(bracketlength (i+1) t)
											  else if h=")" then
												1+(bracketlength (i-1) t)
											  else
											    1+(bracketlength i t)
										   else
											  0
										 else if String.size(str)=1 then
											if i>0 then
											  if is_alphabet h then
												  raise ERROR_CHAR
											  else if h="(" then
												  raise ERROR_CHAR
											  else if h=")" then
												  1
										      else 
										          0
											else
											   0
										else
										    raise ERROR_CHAR
							  
						  in 
								result
						  end	 
						       
						      

fun parseBracket brac_str parse1 = (parse1 brac_str)

(*function that handels string longer than 1

           LEXP STR *)
           
fun parse2 e str parse1= (*if (e=()) then 
						(*handles if only variable is input*)
						if String.size(str)=1 then
							if is_alphabet(str) then
								(ID str)
							else 
								raise ERROR_CHAR
						else if String.size(str)>1 then
							let val h=(head str)
								val t=(tail str)
								val result = if (is_alphabet h) then
													(parse2 (ID h) t)
												else if h="(" then (*bracket handle*)
													let val brac_len=(bracketlength 1 t)
														val new_t = String.extract(str, brac_len, NONE)
													in
														(parse2 (parseBracket t) new_t)
													end
												else if h="\\" then
													let val lam_len=(lamda_len 1 t)
														val new_t = String.extract(str, lam_len, NONE)
													in
														(parse2 (parseLam t) new_t)
													end
												else
													raise ERROR_CHAR
								
								in
									result
								end
							else
								raise ERROR_CHAR
					else (*if e not empty, with some lamda expression*)*)
						if String.size(str)=1 then
							if is_alphabet(str) then
								APP(e,(ID str))
							else 
								(*raise ERROR_CHAR*)
								 if str=")" then
										e
								else
									(ID "ERROR")
						else if String.size(str)>1 then
							
							let val h=(head str)
								val t=(tail str)
								val result=
							
									if (is_alphabet h) then
										(let val new_e = APP(e,(ID h))
											
										in
											
											(parse2 new_e t parse1)
										end)
									else if h="(" then (*bracket handle*)
										(let val brac_len=(bracketlength 1 t)
											val new_t = String.extract(str, brac_len, NONE)
											val braket_t=String.substring(t,0,brac_len)
											val new_e = APP(e,(parseBracket braket_t parse1))
											
										in
											(parse2 new_e new_t parse1)
										end)
									else if h=")" then
										(parse2 e t parse1)
									else if h="\\" then
										(let val lam_len=(lamda_len 1 t)
											val new_t = String.extract(str, (lam_len+1), NONE)
											val lamda_t=String.substring(t,0,lam_len)
											val new_e = APP(e, (parseLam lamda_t parse1))
											val tmpresult= if String.size(new_t)>0 then (parse2 new_e new_t parse1)
															else new_e
										in
											tmpresult
										end)
									else
										(*raise ERROR_CHAR*)
										(ID "ERROR")
								in
									result
								end
							else
							    (*raise ERROR_CHAR*)
							    (ID "ERROR")

fun parse str_raw = let val str=(filterWhiteSpace str_raw) in
					if String.size(str)=1 then
							if is_alphabet(str) then
								(ID str)
							else 
								(*raise ERROR_CHAR*)
								if str=")" then
									(ID "ERROR")
								else
									(ID "ERROR")
						else if String.size(str)>1 then
							let val h=(head str)
								val t=(tail str)
								val result = if (is_alphabet h) then
													(parse2 (ID h) t parse)
												else if h="(" then (*bracket handle*)
													let val brac_len=(bracketlength 1 t)
														val new_t = String.extract(str, brac_len, NONE)
														val braket_t=String.substring(t,0,brac_len)
														val new_e = parseBracket braket_t parse
														
													in
														(parse2 new_e new_t parse)
													end
												else if h="\\" then
													let val lam_len=(lamda_len 1 t)
														val new_t = String.extract(str, (lam_len+1), NONE)
														val lamda_t=String.substring(t,0,lam_len)
														val new_e = parseLam lamda_t parse
														val tmpresult= if String.size(new_t)>0 then (parse2 new_e new_t parse)
																		else new_e
													in
														tmpresult
													end
												else
													(*raise ERROR_CHAR*)
													(ID "ERROR")
								
							  in
									result
							end
						else
							(*raise ERROR_CHAR*)
							(ID "ERROR")
					end
	
				
