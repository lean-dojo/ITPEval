(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1933521,
  "Kleene's recursion theorem": every partial-recursive operation on a program
  code and a natural input has a code whose partial evaluation agrees
  extensionally with the operation applied to that same code. This file
  contains no proof.
*)

let q1933521_code_INDUCT,q1933521_code_RECURSION = define_type
  "q1933521_code =
       Q1933521_Zero
     | Q1933521_Succ
     | Q1933521_Left
     | Q1933521_Right
     | Q1933521_Pair q1933521_code q1933521_code
     | Q1933521_Comp q1933521_code q1933521_code
     | Q1933521_Prec q1933521_code q1933521_code
     | Q1933521_Rfind q1933521_code";;

let q1933521_pair = new_definition
  `q1933521_pair a b =
     if a < b then b * b + a else a * a + a + b`;;

let q1933521_encode = new_recursive_definition q1933521_code_RECURSION
  `(q1933521_encode Q1933521_Zero = 0) /\
   (q1933521_encode Q1933521_Succ = 1) /\
   (q1933521_encode Q1933521_Left = 2) /\
   (q1933521_encode Q1933521_Right = 3) /\
   (q1933521_encode (Q1933521_Pair c d) =
      4 + 4 * q1933521_pair
        (q1933521_encode c) (q1933521_encode d)) /\
   (q1933521_encode (Q1933521_Comp c d) =
      6 + 4 * q1933521_pair
        (q1933521_encode c) (q1933521_encode d)) /\
   (q1933521_encode (Q1933521_Prec c d) =
      5 + 4 * q1933521_pair
        (q1933521_encode c) (q1933521_encode d)) /\
   (q1933521_encode (Q1933521_Rfind c) =
      7 + 4 * q1933521_encode c)`;;

let q1933521_eval_RULES,q1933521_eval_INDUCT,q1933521_eval_CASES =
  new_inductive_definition
   `(!n:num. q1933521_eval Q1933521_Zero n 0) /\
    (!n:num. q1933521_eval Q1933521_Succ n (SUC n)) /\
    (!a b:num.
       q1933521_eval Q1933521_Left (q1933521_pair a b) a) /\
    (!a b:num.
       q1933521_eval Q1933521_Right (q1933521_pair a b) b) /\
    (!c d n x y.
       q1933521_eval c n x /\ q1933521_eval d n y
       ==> q1933521_eval (Q1933521_Pair c d) n
             (q1933521_pair x y)) /\
    (!c d n x y.
       q1933521_eval d n x /\ q1933521_eval c x y
       ==> q1933521_eval (Q1933521_Comp c d) n y) /\
    (!c d a y.
       q1933521_eval c a y
       ==> q1933521_eval (Q1933521_Prec c d)
             (q1933521_pair a 0) y) /\
    (!c d a k i y.
       q1933521_eval (Q1933521_Prec c d)
         (q1933521_pair a k) i /\
       q1933521_eval d (q1933521_pair a (q1933521_pair k i)) y
       ==> q1933521_eval (Q1933521_Prec c d)
             (q1933521_pair a (SUC k)) y) /\
    (!c a m k.
       q1933521_eval c (q1933521_pair a (m + k)) 0 /\
       (!j. j < k
            ==> ?z. q1933521_eval c
                       (q1933521_pair a (m + j)) z /\
                    ~(z = 0))
       ==> q1933521_eval (Q1933521_Rfind c)
             (q1933521_pair a m) (m + k))`;;

let q1933521_partrec2 = new_definition
  `q1933521_partrec2
      (f:q1933521_code->num->num->bool) <=>
     ?program:q1933521_code.
       !c n y.
         q1933521_eval program
           (q1933521_pair (q1933521_encode c) n) y <=>
         f c n y`;;

let Q1933521_KLEENES_RECURSION_THEOREM =
  `!f:q1933521_code->num->num->bool.
     q1933521_partrec2 f
     ==> ?c:q1933521_code.
           !n y. q1933521_eval c n y <=> f c n y`;;
