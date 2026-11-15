(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2011_b2:
  the primes occurring in at least seven ordered prime triples whose
  associated quadratic has a rational root are exactly 2 and 5. This file
  contains no proof.
*)

let statement =
  `let is_rational =
     \x:real.
       ?m n:int.
         ~(n = (&0:int)) /\
         x = real_of_int m / real_of_int n in
   let triples =
     {s:num#(num#num) |
        prime (FST s) /\
        prime (FST (SND s)) /\
        prime (SND (SND s)) /\
        ?x:real.
          is_rational x /\
          &(FST s) * x pow 2 +
          &(FST (SND s)) * x +
          &(SND (SND s)) = &0} in
   let occurrences =
     \t:num.
       {s:num#(num#num) |
          s IN triples /\
          (FST s = t \/ FST (SND s) = t \/ SND (SND s) = t)} in
   !t:num.
     (prime t /\
      (?A:(num#(num#num))->bool.
         A SUBSET occurrences t /\ A HAS_SIZE 7))
     <=> t = 2 \/ t = 5`;;
