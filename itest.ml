use("data-files.ml");
use("parselamda.ml");

datatype ILEXP =  IAPP of ILEXP * ILEXP | ILAM of string *  ILEXP |  IID of string;

fun O (IID v) = (ID v) |
    O (ILAM(str,e)) = (LAM(str, (O e))) |
    O (IAPP(e1,e2)) = (APP((O e1), (O e2))) ;

fun I (ID v) = (IID v) |
    I (LAM(str,e)) = (ILAM(str, (I e))) |
    I (APP(e1,e2)) = (IAPP((I e1), (I e2))) ;

fun printILEXP (IID v) =
    print v
  | printILEXP (ILAM (v,e)) =
    (print "[";
     print v;
     print "]";
     printILEXP e;
     print "")
  | printILEXP (IAPP(e1,e2)) =
    (print "<";
     printILEXP e2;
     print ">";
     printILEXP e1;
     print "");
     
(*  -original LEXP  ----------------------------------------------------------------------------------     *)
(* checks whether a variable is free in a term *)

fun Ifree iid1 (IID iid2) = if (iid1 = iid2) then  true else false|
    Ifree iid1 (IAPP(e1,e2))= (Ifree iid1 e1) orelse (Ifree iid1 e2) | 
    Ifree iid1 (ILAM(iid2, e1)) = if (iid1 = iid2) then false else (Ifree iid1 e1);

(* finds new variables which are fresh  in l and different from id*)
    
fun Ifindme iid l = (let val iid1 = iid^"1"  in if not (List.exists (fn x => iid1 = x) l) then iid1 else (Ifindme iid1 l) end);


(* finds the list of free variables in a term *)

fun IfreeVars (IID id2)       = [id2]
  | IfreeVars (IAPP(e1,e2))   = IfreeVars e1 @ IfreeVars e2
  | IfreeVars (ILAM(id2, e1)) = List.filter (fn x => not (x = id2)) (IfreeVars e1);


(*does substitution avoiding the capture of free variables*)

fun Isubs e iid (IID id1) =  if iid = id1 then e else (IID id1) |
    Isubs e iid (IAPP(e1,e2)) = IAPP(Isubs e iid e1, Isubs e iid e2)|
    Isubs e iid (ILAM(id1,e1)) = (if iid = id1 then ILAM(id1,e1) else
                                   if (not (Ifree iid e1) orelse not (Ifree id1 e))
				       then ILAM(id1,Isubs e iid e1)
                                   else (let val id2 = (Ifindme iid ([id1]@ (IfreeVars e) @ (IfreeVars e1)))
					 in ILAM(id2, Isubs e iid (Isubs (IID id2) id1 e1)) end));

(*Finds a beta redex*)
fun Iis_redex (IAPP(ILAM(_,_),_)) =
      true
  | Iis_redex _ =
      false;
      

fun Iis_var (IID id) =  true |
    Iis_var _ = false;

(*the function below adds lambda id to a list of terms *)
fun Iaddlam id [] = [] |
    Iaddlam id (e::l) = (ILAM(id,e))::(Iaddlam id l);

(*similar to above but adds app backward *)
fun Iaddbackapp [] e2 = []|
    Iaddbackapp (e1::l) e2 = (IAPP(e1,e2)):: (Iaddbackapp l e2);

(*similar to above but adds app forward *)
fun Iaddfrontapp e1 [] = []|
    Iaddfrontapp e1  (e2::l) = (IAPP(e1,e2)):: (Iaddfrontapp e1 l);

(*prints elements from a list putting an arrow in between*)
fun Iprintlistreduce [] = ()|
    Iprintlistreduce (e::[]) = (printILEXP e;(print"\n")) |
    Iprintlistreduce (e::l) = (printILEXP e; print "\n-->" ; (Iprintlistreduce l));

fun idebuglist n l = (print n; print ": "; Iprintlistreduce l; print "\n");

(*beta-reduces a redex*)

fun Ired (IAPP(ILAM(id,e1),e2)) = Isubs e2 id e1;

(*reduces a term to normal form using the m-strategy in which the contracted redex is:
 m(AB) = m(A) if m(A) is defined
 m(AB) = m(B) if m(A) undefined and m(B) defined
 m(AB) = AB if m(A) undefined and m(B) undefined and AB redex
 m(AB) = undefined
 m(\v.A) = m(A)
 m(v) = undefined *)
 
fun Imreduce (IID id) =  [(IID id)] | 
    Imreduce (ILAM(id,e)) = (Iaddlam id (Imreduce e)) |
    Imreduce (IAPP(e1,e2)) = (let val l1 = (Imreduce e1)
				val l2 = (Imreduce e2)
				val l3 = (Iaddbackapp l1 e2)				
				val l4 = (Iaddfrontapp (List.last l1) l2)
				val l5 = (List.last l4)
				val l6 =  if (Iis_redex l5) then (Imreduce (Ired l5)) else [l5]
			    in l3 @ l4 @ l6
			    end);
(*  -LE         ----------------------------------------------------------------------------------     *)


fun Iprintmreduce e = (let val tmp = isolate (Imreduce e)
		      in Iprintlistreduce tmp end);



fun Ihas_redex (IID id) = false |
    Ihas_redex (ILAM(id,e)) = Ihas_redex e|
    Ihas_redex (IAPP(e1,e2)) = if (Iis_redex  (IAPP(e1,e2))) then true else
                              ((Ihas_redex e1) orelse (Ihas_redex e2));

fun Ione_rireduce (IID id) = (IID id)|
    Ione_rireduce (ILAM(id,e)) = ILAM(id, (Ione_rireduce e))|
    Ione_rireduce (IAPP(e1,e2)) = if (Ihas_redex e2) then (IAPP(e1, (Ione_rireduce e2))) else
                                if (Iis_redex (IAPP(e1,e2))) then (Ired (IAPP(e1,e2))) else
                                          if (Ihas_redex e1) then (IAPP((Ione_rireduce e1), e2)) else
                                              (IAPP(e1,e2));



fun Ione_lreduce (IID id) = (IID id)|
    Ione_lreduce (ILAM(id,e)) = ILAM(id, (Ione_lreduce e))|
    Ione_lreduce (IAPP(e1,e2)) = if (Iis_redex (IAPP(e1,e2))) then (Ired (IAPP(e1,e2))) else
                               if (Ihas_redex e1) then (IAPP((Ione_lreduce e1 ),  e2)) else
                                          if (Ihas_redex e2) then (IAPP(e1,(Ione_lreduce  e2))) else
                                              (IAPP(e1,e2));
                                


fun Ilreduce (IID id) =  [(IID id)] |
    Ilreduce (ILAM(id,e)) = (Iaddlam id (Ilreduce e)) |
    Ilreduce (IAPP(e1,e2)) = (let val eo = (IAPP(e1,e2))
								val l1=[eo]
								val l2= if (Iis_redex eo) then (Ilreduce (Ired eo)) else
								        if (Iis_var e1) then
								           if (Iis_var e2) then [eo] else
								           (Ilreduce (IAPP(e1, Ione_lreduce e2)))
										else
								          (* if e1 is not variable, and eo has no redex, then e1 mush be a app, so reduce it*)
										   (Ilreduce (IAPP(Ione_lreduce e1, e2)))
								in
									l1 @ l2
								end);



fun Irireduce (IID id) =  [(IID id)] |
    Irireduce (ILAM(id,e)) = (Iaddlam id (Irireduce e)) |
    Irireduce (IAPP(e1,e2)) = (let val l1 = (Irireduce e2)
				val e3 = (List.last l1)
                                val l2 = (Iaddfrontapp e1 l1)
				val e4 = (IAPP(e1,e3))
                                val l3 =  if (Iis_redex e4) then (Irireduce (Ired e4)) else 
					  if Iis_var(e1) then [e4] else
					      (Irireduce (IAPP(Ione_rireduce e1, e3)))
			    in l2 @ l3
                            end);

fun Iprintlreduce e = (let val tmp = converge (Ilreduce e)
		      in Iprintlistreduce tmp end);

fun Iprintrireduce e = (let val tmp =  (Irireduce e)
		      in Iprintlistreduce tmp end);

fun Ione_loreduce (IID id) = (IID id)|
    Ione_loreduce (ILAM(id,e)) = ILAM(id, (Ione_loreduce e))|
    Ione_loreduce (IAPP(e1,e2)) = if (Iis_redex (IAPP(e1,e2))) then (Ired (IAPP(e1,e2))) else
                                 if (Ihas_redex e1) then IAPP(Ione_loreduce e1, e2) else
                                 if (Ihas_redex e2) then IAPP(e1, (Ione_loreduce e2)) else (IAPP(e1,e2));


fun Iloreduce (IID id) =  [(IID id)] |
    Iloreduce (ILAM(id,e)) = (Iaddlam id (Iloreduce e)) |
    Iloreduce (IAPP(e1,e2)) = (let val l1 = if (Iis_redex (IAPP(e1,e2))) then  (Iloreduce (Ired (IAPP(e1,e2)))) else 
				 if (Ihas_redex e1) then (Iloreduce (IAPP(Ione_loreduce e1, e2))) else 
				 if (Ihas_redex e2) then (Iloreduce (IAPP(e1, (Ione_loreduce e2)))) else []
				 in [IAPP(e1,e2)]@l1
			      end);



fun Iprintloreduce e = (let val tmp =  (Iloreduce e)
		      in Iprintlistreduce tmp end);
		      
		      
Ifindme   "x" ["x", "x1", "x11", "x111"];

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

