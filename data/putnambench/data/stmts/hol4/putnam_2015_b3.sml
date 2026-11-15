(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2015_b3:
  the 2 by 2 real matrices whose entries form an arithmetic progression and
  whose power of some integer exponent greater than one also has this property.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory fcpTheory realTheory;

val putnam_2015_b3 =
  ``let in_ap =
      \A : real['N]['N].
        A ' 0 ' 1 - A ' 0 ' 0 = A ' 1 ' 0 - A ' 0 ' 1 /\
        A ' 1 ' 0 - A ' 0 ' 1 = A ' 1 ' 1 - A ' 1 ' 0
    in
    let matrix_mul =
      \A B : real['N]['N].
        ((FCP i j.
            A ' i ' 0 * B ' 0 ' j + A ' i ' 1 * B ' 1 ' j) :
          real['N]['N])
    in
    let matrix_one =
      ((FCP i j. if i = j then 1 else 0) : real['N]['N])
    in
    let matrix_pow =
      \A : real['N]['N].
      \k : num.
        FUNPOW
          (\B : real['N]['N]. matrix_mul B A)
          k
          matrix_one
    in
      dimindex (:'N) = 2
      ==>
      !M : real['N]['N].
        (in_ap M /\
         (?k : num.
            1 < k /\
            in_ap (matrix_pow M k)))
        <=>
        ((?alpha : real.
            M ' 0 ' 0 = alpha /\
            M ' 0 ' 1 = alpha /\
            M ' 1 ' 0 = alpha /\
            M ' 1 ' 1 = alpha) \/
         (?beta : real.
            M ' 0 ' 0 = beta * ~3 /\
            M ' 0 ' 1 = beta * ~1 /\
            M ' 1 ' 0 = beta * 1 /\
            M ' 1 ' 1 = beta * 3))``;
