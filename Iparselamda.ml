(*test function*)
exception ERROR_CHAR;

fun head str = String.substring(str,0,1);
fun tail str = if String.size(str)>1 then String.extract(str,1,NONE)
				else str;


					      
(*count i as bracket level*)
fun Ibracketlength i str = (let val h = (head str)
							  val t = (tail str)
							  val result=if String.size(str)>=1 then
										  if i>0 then
											  if h="<" then
												1+(Ibracketlength (i+1) t)
											  else if h=">" then
												1+(Ibracketlength (i-1) t)
											  else
											    1+(Ibracketlength i t)
										   else if i=0 then
										   
											  0
											else
											    raise ERROR_CHAR
										 else 
											0
							  
						  in 
								result
						  end);



fun Iparse str = (let val str=filterWhiteSpace str
					  val char=(head str)
				      val t=(tail str)
				in
					if is_alphabet char then
						(IID char)
					else if char="[" then
						let val lam_char= head t
							
							val lam_e=String.extract(str,3,NONE)
						in
							ILAM(lam_char, (Iparse lam_e))
						end
					else if char="<" then
						let val brac_len=Ibracketlength 1 t
							val str1= String.substring(t,0, (brac_len-1))
							val str2= String.extract(t,(brac_len),NONE)
							val e1=(Iparse str1)
							val e2=(Iparse str2)
							
						in
							APPon(e1, e2)
						end
					else
						raise ERROR_CHAR
				end);
				
