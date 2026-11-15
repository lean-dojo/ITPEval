$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1980_a4: upper and lower bounds for nonzero bounded integer linear
  combinations of 1, sqrt(2), and sqrt(3). This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The source predicate abcvals is inlined as its defining condition: a, b,
  and c are integers, are not all zero, and each has absolute value less
  than one million. The thresholds 10^(-11) and 10^(-21) are written as
  the definitionally equal positive real quotients 1 / 10^11 and 1 / 10^21.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a b c $.

  putnambench-putnam-1980-a4 $a |- (
    E. a e. ZZ E. b e. ZZ E. c e. ZZ
      (
        (
          -.
          (
            a = 0
            /\
            (
              b = 0
              /\
              c = 0
            )
          )
          /\
          (
            ( abs ` a ) < ; ; ; ; ; ; 1 0 0 0 0 0 0
            /\
            (
              ( abs ` b ) < ; ; ; ; ; ; 1 0 0 0 0 0 0
              /\
              ( abs ` c ) < ; ; ; ; ; ; 1 0 0 0 0 0 0
            )
          )
        )
        /\
        (
          abs
          `
          (
            (
              a
              +
              ( b x. ( sqrt ` 2 ) )
            )
            +
            ( c x. ( sqrt ` 3 ) )
          )
        )
        <
        (
          1
          /
          ( ; 1 0 ^ ; 1 1 )
        )
      )
    /\
    A. a e. ZZ A. b e. ZZ A. c e. ZZ
      (
        (
          -.
          (
            a = 0
            /\
            (
              b = 0
              /\
              c = 0
            )
          )
          /\
          (
            ( abs ` a ) < ; ; ; ; ; ; 1 0 0 0 0 0 0
            /\
            (
              ( abs ` b ) < ; ; ; ; ; ; 1 0 0 0 0 0 0
              /\
              ( abs ` c ) < ; ; ; ; ; ; 1 0 0 0 0 0 0
            )
          )
        )
        ->
        (
          1
          /
          ( ; 1 0 ^ ; 2 1 )
        )
        <
        (
          abs
          `
          (
            (
              a
              +
              ( b x. ( sqrt ` 2 ) )
            )
            +
            ( c x. ( sqrt ` 3 ) )
          )
        )
      )
  ) $.
$}
