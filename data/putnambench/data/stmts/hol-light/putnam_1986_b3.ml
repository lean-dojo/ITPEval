(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1986_b3:
  lifting a factorization of an integer-coefficient polynomial modulo a prime
  to a factorization modulo an arbitrary positive power of that prime. This
  file contains no proof.
*)

let statement =
  `let polynomial =
     \f:num->int. ?d:num. !i:num. d < i ==> f i = &0 in
   let padd =
     \f g:num->int. \i:num. f i + g i in
   let pmul =
     \f g:num->int. \k:num.
       isum (0..k) (\i:num. f i * g (k - i)) in
   let pone =
     \i:num. if i = 0 then &1 else &0 in
   let pcong =
     \f g:num->int. \m:int.
       !i:num. (f i == g i) (mod m) in
   !n p:num. !f g h r s:num->int.
     0 < n /\
     0 < p /\
     prime p /\
     polynomial f /\
     polynomial g /\
     polynomial h /\
     polynomial r /\
     polynomial s /\
     pcong (padd (pmul r f) (pmul s g)) pone (&p) /\
     pcong (pmul f g) h (&p)
     ==> ?F G:num->int.
           polynomial F /\
           polynomial G /\
           pcong F f (&p) /\
           pcong G g (&p) /\
           pcong (pmul F G) h (&(p EXP n))`;;
