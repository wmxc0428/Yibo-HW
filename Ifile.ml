use("data-files.ml");
use("parselamda.ml");


datatype ILEXP =  APPon of ILEXP * ILEXP | ILAM of string *  ILEXP |  IID of string;


fun O (IID v) = (ID v) |
    O (ILAM(str,e)) = (LAM(str, (O e))) |
    O (APPon(e2,e1)) = (APP((O e1), (O e2))) ;

fun I (ID v) = (IID v) |
    I (LAM(str,e)) = (ILAM(str, (I e))) |
    I (APP(e1,e2)) = (APPon((I e2), (I e1))) ;



fun printILEXP (IID v) =
    print v
  | printILEXP (ILAM (v,e)) =
    (print "[";
     print v;
     print "]";
     printILEXP e;
     print "")
  | printILEXP (APPon(e1,e2)) =
    (print "<";
     printILEXP e1;
     print ">";
     printILEXP e2;
     print "");
         
(*  -NEW ILEXP  ----------------------------------------------------------------------------------     *)

(* checks whether a variable is free in a term *)
fun Ifree iid1 (IID iid2) = if (iid1 = iid2) then  true else false|
    Ifree iid1 (APPon(e1,e2))= (Ifree iid1 e2) orelse (Ifree iid1 e1) | 
    Ifree iid1 (ILAM(iid2, e1)) = if (iid1 = iid2) then false else (Ifree iid1 e1);


(* finds the list of free variables in a term *)

fun IfreeVars (IID id2)       = [id2]
  | IfreeVars (APPon(e1,e2))   = IfreeVars e1 @ IfreeVars e2
  | IfreeVars (ILAM(id2, e1)) = List.filter (fn x => not (x = id2)) (IfreeVars e1);


(* finds new variables which are fresh  in l and different from id*)  
fun Ifindme iid l = (let val iid1 = iid^"1"  in if not (List.exists (fn x => iid1 = x) l) then iid1 else (Ifindme iid1 l) end);


(*does substitution avoiding the capture of free variables*)

fun Isubs e iid (IID id1) =  if iid = id1 then e else (IID id1) |
    Isubs e iid (APPon(e1,e2)) = APPon(Isubs e iid e1, Isubs e iid e2)|
    Isubs e iid (ILAM(id1,e1)) = (if iid = id1 then ILAM(id1,e1) else
                                   if (not (Ifree iid e1) orelse not (Ifree id1 e))
				       then ILAM(id1,Isubs e iid e1)
                                   else (let val id2 = (Ifindme iid ([id1]@ (IfreeVars e) @ (IfreeVars e1)))
					 in ILAM(id2, Isubs e iid (Isubs (IID id2) id1 e1)) end));


(*Finds a beta redex*)
fun Iis_redex (APPon(_,ILAM(_,_))) =
      true
  | Iis_redex _ =
      false;
      
fun Ihas_redex (IID id) = false |
    Ihas_redex (ILAM(id,e)) = Ihas_redex e|
    Ihas_redex (APPon(e1,e2)) = if (Iis_redex  (APPon(e1,e2))) then true else
                              ((Ihas_redex e2) orelse (Ihas_redex e1));


fun Iis_var (IID id) =  true |
    Iis_var _ = false;
    
(*the function below adds lambda id to a list of terms *)
fun Iaddlam id [] = [] |
    Iaddlam id (e::l) = (ILAM(id,e))::(Iaddlam id l);

(*similar to above but adds app backward *)
fun Iaddbackapp [] e2 = []|
    Iaddbackapp (e1::l) e2 = (APPon(e2,e1)):: (Iaddbackapp l e2);
    

(*similar to above but adds app forward *)
fun Iaddfrontapp e1 [] = []|
    Iaddfrontapp e1  (e2::l) = (APPon(e2,e1)):: (Iaddfrontapp e1 l);


(*prints elements from a list putting an arrow in between*)
fun Iprintlistreduce [] = ()|
    Iprintlistreduce (e::[]) = (printILEXP e;(print"\n")) |
    Iprintlistreduce (e::l) = (printILEXP e; print "\n-->" ; (Iprintlistreduce l));

(*beta-reduces a redex*)

fun Ired (APPon(e2,ILAM(id,e1))) = Isubs e2 id e1;

 fun Iexpression_size (IID id) = 1 |
	Iexpression_size (ILAM(id,e)) = (0 + (Iexpression_size e))|
	Iexpression_size (APPon(e1,e2)) =1+(Iexpression_size e2)*(Iexpression_size e1);

fun	Iexpression_size2 boundidlist (IID id) = if boundidlist=[] then 1 else if is_inlist (IID id) boundidlist then 1 else 0 |
    Iexpression_size2 boundidlist (ILAM(id,e)) = (Iexpression_size2 (boundidlist @ [(IID id) ]) e) |
    Iexpression_size2 boundidlist (APPon(e1,e2))=1 + (Iexpression_size2 boundidlist e1)*(Iexpression_size2 boundidlist e2);

 
(* MID REDUCE*)
fun Imreduce (IID id) =  [(IID id)] | 
    Imreduce (ILAM(id,e)) = (Iaddlam id (Imreduce e)) |
    Imreduce (APPon(e1,e2)) = (let val l1 = (Imreduce e2)
				val l2 = (Imreduce e1)
				val l3 = (Iaddbackapp l2 e1)				
				val l4 = (Iaddfrontapp (List.last l2) l1)
				val l5 = (List.last l4)
				val l6 =  if (Iis_redex l5) then (Imreduce (Ired l5)) else []
			    in l3 @ (List.tl l4) @ l6
			    end);
(*  -LE         ----------------------------------------------------------------------------------     *)
fun Iprintmreduce e = (let val tmp =  (Imreduce e)
		      in Iprintlistreduce tmp end);

(* RIGHT FIRST REDUCE *)

fun Ione_rireduce (IID id) = (IID id)|
    Ione_rireduce (ILAM(id,e)) = ILAM(id, (Ione_rireduce e))|
    Ione_rireduce (APPon(e1,e2)) = if (Ihas_redex e1) then (APPon( (Ione_rireduce e1),e2)) else
                                if (Iis_redex (APPon(e1,e2))) then (Ired (APPon(e1,e2))) else
                                          if (Ihas_redex e2) then (APPon(e1,(Ione_rireduce e2))) else
                                              (APPon(e1,e2));


fun Irireduce2 i (IID id) =  [(IID id)] |
    Irireduce2 i (ILAM(id,e)) = (Iaddlam id (Irireduce2 i e)) |
    Irireduce2 i (APPon(e1,e2)) = let val l1=[APPon(e1,e2)]
									  val l2=
										if i>0 then
											if Ihas_redex e1 then
												Irireduce2 (i-1) (APPon((Ione_rireduce e1) , e2 ))
											else
												if Iis_redex (APPon(e1,e2)) then
													(Irireduce2 (i-1) (Ired (APPon(e1,e2))))
												else if Ihas_redex(e2) then
												Irireduce2 (i-1) (APPon(e1,(Ione_rireduce e2)))
											else
												[]
										else
											[]
								val result=l1 @ l2
									in converge result
								end
								;
											
(*rireduce provided does not stop at infinite loop, this one does when it reached the number of a expression size!*)
fun Irireduce e = let val size= Iexpression_size e
					 val result=Irireduce2 size e
					in
						result
					end;

fun printIrireduce e = (let val tmp =  (Irireduce e)
							val count= (count_list tmp-1)
						in 
						
							if Ihas_redex (List.last tmp) then
								(*if the expression from the lreduce has a redex, it means it terminated earlier due to repeated lines or expanding lines
								  therefore, it is a infinite loop of doing beta reduction.
								  Else it is the normal form
								 *)
								(Iprintlistreduce tmp;print "Found at step ";print (Int.toString(count)); print "\nINFINITE LOOP, THIS LAMDA EXPRESSION DOES NOT HAVE A NORMAL FORM!!";(print "\n")) 
							else
								(Iprintlistreduce tmp;print "step count=";print (Int.toString(count));(print "\n")) 
						
						   end);


                       
(* LEFT FIRST REDUCE *)

fun Ione_lreduce (IID id) = (IID id)|
    Ione_lreduce (ILAM(id,e)) = ILAM(id, (Ione_lreduce e))|
    Ione_lreduce (APPon(e1,e2)) = if (Iis_redex (APPon(e1,e2))) then 
								let val eo=(APPon(e1,e2))
									val e3= (Ired eo) 
								    val result= if eo=e3 then
													eo
												else
													e3
								in
									result
								end
                               else if (Ihas_redex e2) then 
								(APPon(e1,(Ione_lreduce  e2))) 
                               else if (Ihas_redex e1) then 
								(APPon((Ione_lreduce e1 ), e2)) 
                               else
                                (APPon(e1,e2));


fun Ilreduce3 i elist (IID id) =  [(IID id)] |
    Ilreduce3 i elist (ILAM(id,e)) = (Iaddlam id (Ilreduce3 i elist e)) |
    Ilreduce3 i elist (APPon(e1,e2)) = (let val eo = (APPon(e1,e2))
									   val new_i=(i-1)
									   val l1=[eo]
									   val new_elist=(elist @ l1)
									   val l2=  if i<=0 then 
										[]
									   else
									   if (Iis_redex eo) then 
										   let val e3=(Ione_lreduce eo) in
											if (is_inlist e3 elist) then
												[]
											
											else if(is_inlist eo elist) then
												[]
											else
												(Ilreduce3 new_i new_elist e3)
										    end
									else if Ihas_redex e2 then 
										let val e3=(Ione_lreduce e2)
											val e4=(APPon(e1, e3))
											val new_elist=(elist @ l1 )
										in
											if (is_inlist e3 elist) then
												[]
											else if(is_inlist eo elist) then
												[]
											else if (is_inlist e2 elist) then	
												[]
											else
											(Ilreduce3 new_i new_elist e4)
										end
									else if Ihas_redex e1 then
										let val e3=(Ione_lreduce e1)
											val e4=(APPon(e3, e2))
											val new_elist=(elist @ l1)
										in
											if (is_inlist e3 elist) then
												[]
											else if(is_inlist eo elist) then
												[]
											else if (is_inlist e1 elist) then	
												[]
											else
											(Ilreduce3 new_i new_elist e4)
											end
									else
										[]
								in
									l1 @ l2
								end);
    
fun Ilreduce e = let val size=(Iexpression_size e)
					val result= Ilreduce3 size [] e
				in
					result
				end;

fun printIlreduce e = (let val tmp =  (Ilreduce e)
					      val count= (count_list tmp-1)
		    in 
			
				if Ihas_redex (List.last tmp) then
				    (*if the expression from the lreduce has a redex, it means it terminated earlier due to repeated lines or expanding lines
				      therefore, it is a infinite loop of doing beta reduction.
				      Else it is the normal form
				     *)
					(Iprintlistreduce tmp;print "Found at step ";print (Int.toString(count)); print "\nINFINITE LOOP, THIS LAMDA EXPRESSION DOES NOT HAVE A NORMAL FORM!!";(print "\n")) 
		        else
					(Iprintlistreduce tmp;print "step count=";print (Int.toString(count));(print "\n")) 
			
		       end);




val Ivx = I vx;
val Ivy = I vy;
val Ivz = I vz;
val It1 = I t1;
val It2 = I t2;
val It3 = I t3;
val It4 = I t4;
val It5 = I t5;
val It6 = I t6;
val It7 = I t7;
val It8 = I t8;
val It9 = I t9;
val It10 = I t10;
val It11 = I t11;
val It12 = I t12;
val It13 = I t13;
val It14 = I t14;
val It15 = I t15;
val It16 = I t16;
val It17 = I t17;
val aa= parse "(\\x.xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx)";
val bb= parse "(\\x.xxxxxxxxxxxxxxxxx)(\\x.x)";
val cc= (APP(aa,bb));
val dd= (APP(cc,vx));
val ee=(APP(dd,cc));
