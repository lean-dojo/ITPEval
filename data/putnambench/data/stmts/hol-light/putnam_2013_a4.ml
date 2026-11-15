(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2013_a4:
  balanced zero counts on equal-length arcs of a finite binary circle force
  integral average zero and one counts to occur on one arc. This file contains
  no proof.
*)

let statement =
  `!n k:num.
   !circle:num->num.
   !Z N:(num#num)->int.
   !ws:num->(num#num).
   !Zsum Nsum:int.
     let arc =
       \w:num#num. FST w < n /\ SND w <= n in
     1 <= n /\
     1 <= k /\
     (!i:num.
        i < n ==> circle i = 0 \/ circle i = 1) /\
     (!w:num#num.
        arc w
        ==>
        Z w =
        isum {l:num | l < SND w}
          (\l. if circle ((FST w + l) MOD n) = 0 then &1 else &0)) /\
     (!w:num#num.
        arc w
        ==>
        N w =
        isum {l:num | l < SND w}
          (\l. if circle ((FST w + l) MOD n) = 1 then &1 else &0)) /\
     (!w w':num#num.
        arc w /\ arc w' /\ SND w = SND w'
        ==> abs (Z w - Z w') <= &1) /\
     (!j:num. j < k ==> arc (ws j)) /\
     real_of_int Zsum =
       sum {j:num | j < k} (\j. real_of_int (Z (ws j))) / &k /\
     real_of_int Nsum =
       sum {j:num | j < k} (\j. real_of_int (N (ws j))) / &k
     ==>
     ?w:num#num.
       arc w /\ Z w = Zsum /\ N w = Nsum`;;
