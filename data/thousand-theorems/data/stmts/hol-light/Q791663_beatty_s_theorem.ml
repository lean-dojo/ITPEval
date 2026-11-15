(*
  Statement-only formalization of Thousand Theorems corpus artifact Q791663,
  (thousand-theorems__hol-light__Q791663), "Beatty's theorem":
  Holder-conjugate real parameters give complementary two-sided floor/ceiling
  Beatty sets, and with an irrational first parameter the positive floor
  Beatty sets partition the positive integers. This file contains no proof.
*)

needs "Library/floor.ml";;

let Q791663_COMPL_BEATTYSEQ =
  `let ceil_int =
     \x:real. int_of_real (--(floor (--x))) in
   let beatty_seq =
     \r:real. \k:int.
       int_of_real (floor (real_of_int k * r)) in
   let beatty_seq_prime =
     \r:real. \k:int.
       ceil_int (real_of_int k * r) - &1 in
   let holder_conjugate =
     \r s:real.
       &1 < r /\ &1 < s /\ inv r + inv s = &1 in
   !r s:real.
     holder_conjugate r s
     ==> !j:int.
           (~(?k:int. j = beatty_seq r k) <=>
            ?k:int. j = beatty_seq_prime s k)`;;

let Q791663_IRRATIONAL_BEATTYSEQ_SYMMDIFF_POS =
  `let beatty_seq =
     \r:real. \k:int.
       int_of_real (floor (real_of_int k * r)) in
   let holder_conjugate =
     \r s:real.
       &1 < r /\ &1 < s /\ inv r + inv s = &1 in
   !r s:real.
     holder_conjugate r s /\ ~rational r
     ==> !n:int.
           (((?k:int. &0 < k /\ n = beatty_seq r k) /\
             ~(?k:int. &0 < k /\ n = beatty_seq s k)) \/
            ((?k:int. &0 < k /\ n = beatty_seq s k) /\
             ~(?k:int. &0 < k /\ n = beatty_seq r k))
            <=> &0 < n)`;;
