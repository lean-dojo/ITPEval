(*
  Statement-only formalization of PutnamBench artifact putnam_1980_b6:
  nondivisibility by a prime of the reduced denominator of the recursively
  defined rational number G(d,p). This file contains no proof.
*)

let statement =
  `let rat_value =
     \q:int#num. real_of_int (FST q) / &(SND q) in
   let reduced =
     \q:int#num.
       0 < SND q /\ coprime (num_of_int (abs (FST q)),SND q) in
   !G:(int#int)->(int#num).
     (!x:int#int. reduced (G x)) /\
     (!d n:num.
        d <= n
        ==>
        ((d = 1
          ==> rat_value (G ((&d:int),(&n:int))) = &1 / &n) /\
         (d > 1
          ==> rat_value (G ((&d:int),(&n:int))) =
              (&d / &n) *
              sum (d..n)
                (\i:num.
                   rat_value
                     (G (((&d:int) - &1),((&i:int) - &1)))))))
     ==>
     !d p:num.
       1 < d /\ d <= p /\ prime p
       ==> ~(p divides SND (G ((&d:int),(&p:int))))`;;
