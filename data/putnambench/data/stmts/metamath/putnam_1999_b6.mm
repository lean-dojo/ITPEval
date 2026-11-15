$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1999_b6: a finite set of integers satisfying a universal
  greatest-common-divisor selection property contains two members whose
  greatest common divisor is prime. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  S ranges over finite sets and S C_ ZZ preserves the integer carrier.
  The first restricted universal quantifier states that every member is
  greater than one. The second retains the source quantifier over every
  integer n and its internally existential choice of s in S.

  Membership of ( s gcd t ) in Prime is SetMM's direct formulation that the
  greatest common divisor is prime. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

${
  $d S n s t $.

  putnambench-putnam-1999-b6 $a |- A. S e. Fin
    (
      (
        S C_ ZZ
        /\
        (
          A. s e. S 1 < s
          /\
          A. n e. ZZ
            E. s e. S
              (
                ( s gcd n ) = 1
                \/
                ( s gcd n ) = s
              )
        )
      )
      ->
      E. s e. S E. t e. S ( s gcd t ) e. Prime
    )
  $.
$}
