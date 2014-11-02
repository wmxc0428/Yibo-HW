
(*note that in the program below, the list of reduction steps given by
mreduce has many duplications.  This is very easy to avoid by
monitoring l2,l3,l4, l5,l6, etc, in mreduce and the print functions.
This is your job to do. *)

datatype LEXP =  APP of LEXP * LEXP | LAM of string *  LEXP |  ID of string;

(* checks whether a variable is free in a term *)

fun free id1 (ID id2) = if (id1 = id2) then  true else false|
    free id1 (APP(e1,e2))= (free id1 e1) orelse (free id1 e2) | 
    free id1 (LAM(id2, e1)) = if (id1 = id2) then false else (free id1 e1);

(* finds new variables which are fresh  in l and different from id*)
    
fun findme id l = (let val id1 = id^"1"  in if not (List.exists (fn x => id1 = x) l) then id1 else (findme id1 l) end);


(* finds the list of free variables in a term *)

fun freeVars (ID id2)       = [id2]
  | freeVars (APP(e1,e2))   = freeVars e1 @ freeVars e2
  | freeVars (LAM(id2, e1)) = List.filter (fn x => not (x = id2)) (freeVars e1);


(*does substitution avoiding the capture of free variables*)

fun subs e id (ID id1) =  if id = id1 then e else (ID id1) |
    subs e id (APP(e1,e2)) = APP(subs e id e1, subs e id e2)|
    subs e id (LAM(id1,e1)) = (if id = id1 then LAM(id1,e1) else
                                   if (not (free id e1) orelse not (free id1 e))
				       then LAM(id1,subs e id e1)
                                   else (let val id2 = (findme id ([id1]@ (freeVars e) @ (freeVars e1)))
					 in LAM(id2, subs e id (subs (ID id2) id1 e1)) end));





(*Prints a term*)
fun printLEXP (ID v) =
    print v
  | printLEXP (LAM (v,e)) =
    (print "(\\";
     print v;
     print ".";
     printLEXP e;
     print ")")
  | printLEXP (APP(e1,e2)) =
    (print "(";
     printLEXP e1;
     print " ";
     printLEXP e2;
     print ")");

(*Finds a beta redex*)
fun is_redex (APP(LAM(_,_),_)) =
      true
  | is_redex _ =
      false;

fun is_var (ID id) =  true |
    is_var _ = false;


(*the function below adds lambda id to a list of terms *)
fun addlam id [] = [] |
    addlam id (e::l) = (LAM(id,e))::(addlam id l);

(*similar to above but adds app backward *)
fun addbackapp [] e2 = []|
    addbackapp (e1::l) e2 = (APP(e1,e2)):: (addbackapp l e2);

(*similar to above but adds app forward *)
fun addfrontapp e1 [] = []|
    addfrontapp e1  (e2::l) = (APP(e1,e2)):: (addfrontapp e1 l);

(*prints elements from a list putting an arrow in between*)
fun printlistreduce [] = ()|
    printlistreduce (e::[]) = (printLEXP e) |
    printlistreduce (e::l) = (printLEXP e; print "\n-->" ; (printlistreduce l));

fun debuglist n l = (print n; print ": "; printlistreduce l; print "\n");

(*beta-reduces a redex*)

fun red (APP(LAM(id,e1),e2)) = subs e2 id e1;

(*reduces a term to normal form using the m-strategy in which the contracted redex is:
 m(AB) = m(A) if m(A) is defined
 m(AB) = m(B) if m(A) undefined and m(B) defined
 m(AB) = AB if m(A) undefined and m(B) undefined and AB redex
 m(AB) = undefined
 m(\v.A) = m(A)
 m(v) = undefined *)



fun mreduce (ID id) =  [(ID id)] | 
    mreduce (LAM(id,e)) = (addlam id (mreduce e)) |
    mreduce (APP(e1,e2)) = (let val l1 = (mreduce e1)
				val l2 = (mreduce e2)
				val l3 = (addbackapp l1 e2)				
				val l4 = (addfrontapp (List.last l1) l2)
				val l5 = (List.last l4)
				val l6 =  if (is_redex l5) then (mreduce (red l5)) else [l5]
			    in l3 @ l4 @ l6
			    end);


(*printmreduce first m-reduces the term giving the list of all intermediary 
terms and then prints this list separating intermediary terms with -->*)

fun printmreduce e = (let val tmp =  (mreduce e)
		      in printlistreduce tmp end);



fun has_redex (ID id) = false |
    has_redex (LAM(id,e)) = has_redex e|
    has_redex (APP(e1,e2)) = if (is_redex  (APP(e1,e2))) then true else
                              ((has_redex e1) orelse (has_redex e2));

fun  one_rireduce (ID id) = (ID id)|
    one_rireduce (LAM(id,e)) = LAM(id, (one_rireduce e))|
    one_rireduce (APP(e1,e2)) = if (has_redex e2) then (APP(e1, (one_rireduce e2))) else
                                if (is_redex (APP(e1,e2))) then (red (APP(e1,e2))) else
                                          if (has_redex e1) then (APP((one_rireduce e1), e2)) else
                                              (APP(e1,e2));



fun rireduce (ID id) =  [(ID id)] |
    rireduce (LAM(id,e)) = (addlam id (rireduce e)) |
    rireduce (APP(e1,e2)) = (let val l1 = (rireduce e2)
				val e3 = (List.last l1)
                                val l2 = (addfrontapp e1 l1)
				val e4 = (APP(e1,e3))
                                val l3 =  if (is_redex e4) then (rireduce (red e4)) else 
					  if is_var(e1) then [e4] else
					      (rireduce (APP(one_rireduce e1, e3)))
			    in l2 @ l3
                            end);


fun printrireduce e = (let val tmp =  (rireduce e)
		      in printlistreduce tmp end);

fun one_loreduce (ID id) = (ID id)|
    one_loreduce (LAM(id,e)) = LAM(id, (one_loreduce e))|
    one_loreduce (APP(e1,e2)) = if (is_redex (APP(e1,e2))) then (red (APP(e1,e2))) else
                                 if (has_redex e1) then APP(one_loreduce e1, e2) else
                                 if (has_redex e2) then APP(e1, (one_loreduce e2)) else (APP(e1,e2));


fun loreduce (ID id) =  [(ID id)] |
    loreduce (LAM(id,e)) = (addlam id (loreduce e)) |
    loreduce (APP(e1,e2)) = (let val l1 = if (is_redex (APP(e1,e2))) then  (loreduce (red (APP(e1,e2)))) else 
				 if (has_redex e1) then (loreduce (APP(one_loreduce e1, e2))) else 
				 if (has_redex e2) then  (loreduce (APP(e1, (one_loreduce e2)))) else []
				 in [APP(e1,e2)]@l1
			      end);


fun printloreduce e = (let val tmp =  (loreduce e)
		      in printlistreduce tmp end);

findme   "x" ["x", "x1", "x11", "x111"];


val vx = (ID "x");
val vy = (ID "y");
val vz = (ID "z");
val t1 = (LAM("x",vx));
val t2 = (LAM("y",vx));
val t3 = (APP(APP(t1,t2),vz));
val t4 = (APP(t1,vz));
val t5 = (APP(t3,t3));
val t6 = (LAM("x",(LAM("y",(LAM("z",(APP(APP(vx,vz),(APP(vy,vz))))))))));
val t7 = (APP(APP(t6,t1),t1));
val t8 = (LAM("z", (APP(vz,(APP(t1,vz))))));
val t9 = (APP(t8,t3));

(*Note that printmreduce t7; gives:
(((\x.(\y.(\z.((x z) (y z))))) (\x.x)) (\x.x))-->
(((\x.(\y.(\z.((x z) (y z))))) (\x.x)) (\x.x))-->
(((\x.(\y.(\z.((x z) (y z))))) (\x.x)) (\x.x))-->
(((\x.(\y.(\z.((x z) (y z))))) (\x.x)) (\x.x))-->
(((\x.(\y.(\z.((x z) (y z))))) (\x.x)) (\x.x))-->
(((\x.(\y.(\z.((x z) (y z))))) (\x.x)) (\x.x))-->
(((\x.(\y.(\z.((x z) (y z))))) (\x.x)) (\x.x))-->
(((\x.(\y.(\z.((x z) (y z))))) (\x.x)) (\x.x))-->
((\y.(\z.(((\x.x) z) (y z)))) (\x.x))-->
((\y.(\z.(((\x.x) z) (y z)))) (\x.x))-->
((\y.(\z.(z (y z)))) (\x.x))-->
((\y.(\z.(z (y z)))) (\x.x))-->
((\y.(\z.(z (y z)))) (\x.x))-->
((\y.(\z.(z (y z)))) (\x.x))-->
((\y.(\z.(z (y z)))) (\x.x))-->
((\y.(\z.(z (y z)))) (\x.x))-->
(\z.(z ((\x.x) z)))-->
(\z.(z ((\x.x) z)))-->
(\z.(z ((\x.x) z)))-->
(\z.(z z))-->
(\z.(z z))
val it = () : unit

instead of giving 
(((\x.(\y.(\z.((x z) (y z))))) (\x.x)) (\x.x))-->
((\y.(\z.(((\x.x) z) (y z)))) (\x.x))-->
((\y.(\z.(z (y z)))) (\x.x))-->
(\z.(z ((\x.x) z)))-->
(\z.(z z))
val it = () : unit

Can you sort out the program to avoid repetition?

Similarly, printmreduce t9; gives:
((\z.(z ((\x.x) z))) (((\x.x) (\y.x)) z))-->
((\z.(z ((\x.x) z))) (((\x.x) (\y.x)) z))-->
((\z.(z ((\x.x) z))) (((\x.x) (\y.x)) z))-->
((\z.(z z)) (((\x.x) (\y.x)) z))-->
((\z.(z z)) (((\x.x) (\y.x)) z))-->
((\z.(z z)) (((\x.x) (\y.x)) z))-->
((\z.(z z)) (((\x.x) (\y.x)) z))-->
((\z.(z z)) ((\y.x) z))-->
((\z.(z z)) ((\y.x) z))-->
((\z.(z z)) x)-->
(x x)-->
(x x)-->
(x x)
val it = () : unit

instead of giving:
((\z.(z ((\x.x) z))) (((\x.x) (\y.x)) z))-->
((\z.(z z)) (((\x.x) (\y.x)) z))-->
((\z.(z z)) ((\y.x) z))-->
((\z.(z z)) x)-->
(x x)
val it = () : unit

Can you  sort out the program to avoid repetition?


printloreduce t9; gives:
((\z.(z ((\x.x) z))) (((\x.x) (\y.x)) z))-->
((((\x.x) (\y.x)) z) ((\x.x) (((\x.x) (\y.x)) z)))-->
(((\y.x) z) ((\x.x) (((\x.x) (\y.x)) z)))-->
(x ((\x.x) (((\x.x) (\y.x)) z)))-->
(x (((\x.x) (\y.x)) z))-->
(x ((\y.x) z))-->
(x x)
val it = () : unit

*)
