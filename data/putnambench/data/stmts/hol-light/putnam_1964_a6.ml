(*
  Statement-only formalization of PutnamBench artifact putnam_1964_a6:
  rationality of ratios of distances between ordered pairs from a finite
  set of collinear real points under the repeated-distance condition. This
  file contains no proof.
*)

let statement =
  `!S:real->bool.
     let pairs =
       {p:real#real |
          FST p IN S /\ SND p IN S /\ FST p < SND p} in
     let distance = \p:real#real. SND p - FST p in
     FINITE S /\
     (!p:real#real.
        p IN pairs
        ==> ((?m:real#real.
                m IN pairs /\ distance m > distance p)
             ==> ?q:real#real.
                   q IN pairs /\ ~(q = p) /\
                   distance p = distance q))
     ==> !p q:real#real.
           p IN pairs /\ q IN pairs /\ ~(q = p)
           ==> ?n d:int.
                 ~(d = (&0:int)) /\
                 distance p / distance q =
                 real_of_int n / real_of_int d`;;
