$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1974_a1: the largest cardinality of a subset of the integers 1
  through 16 containing no three distinct pairwise relatively prime
  elements is 11. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The class 1 ... 16 is the inclusive integer interval from the sources.
  The displayed restricted quantifiers expand the conspiratorial condition:
  among any three distinct members, at least one pair has greatest common
  divisor greater than one. Positivity is automatic from interval membership.

  Existence of an eleven-element such subset together with the universal
  cardinality bound is equivalent to saying that the largest possible
  cardinality is eleven. The final declaration is the single unproved $a
  corpus statement; this database contains no $p proof statement.
$)

${
  $d S a b c $.

  putnambench-putnam-1974-a1 $a |- (
    (
      E. S e. ~P ( 1 ... ( 9 + 7 ) )
        (
          ( # ` S ) = ( 9 + 2 )
          /\
          A. a e. S A. b e. S A. c e. S
            (
              (
                (
                  a =/= b
                  /\
                  b =/= c
                )
                /\
                a =/= c
              )
              ->
              (
                1 < ( a gcd b )
                \/
                (
                  1 < ( b gcd c )
                  \/
                  1 < ( a gcd c )
                )
              )
            )
        )
    )
    /\
    A. S e. ~P ( 1 ... ( 9 + 7 ) )
      (
        (
          A. a e. S A. b e. S A. c e. S
            (
              (
                (
                  a =/= b
                  /\
                  b =/= c
                )
                /\
                a =/= c
              )
              ->
              (
                1 < ( a gcd b )
                \/
                (
                  1 < ( b gcd c )
                  \/
                  1 < ( a gcd c )
                )
              )
            )
        )
        ->
        ( # ` S ) <_ ( 9 + 2 )
      )
  ) $.
$}
