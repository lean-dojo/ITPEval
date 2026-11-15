$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2018_a1: classification of the positive integer ordered pairs
  satisfying 1/a + 1/b = 3/2018. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Quantifying a and b over NN is equivalent to the source's integer
  variables with explicit positivity assumptions. The right side is the
  six-pair solution set given explicitly by the Rocq source and annotated
  in the Lean and Isabelle sources.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a b $.

  putnambench-putnam-2018-a1 $a |- A. a e. NN A. b e. NN
    (
      (
        ( 1 / a ) + ( 1 / b )
      )
      =
      (
        3 / ( ; ; ; 2 0 1 8 )
      )
      <->
      (
        (
          a = ( ; ; 6 7 3 )
          /\
          b = ( ; ; ; ; ; ; 1 3 5 8 1 1 4 )
        )
        \/
        (
          (
            a = ( ; ; 6 7 4 )
            /\
            b = ( ; ; ; ; ; 3 4 0 0 3 3 )
          )
          \/
          (
            (
              a = ( ; ; ; 1 0 0 9 )
              /\
              b = ( ; ; ; 2 0 1 8 )
            )
            \/
            (
              (
                a = ( ; ; ; 2 0 1 8 )
                /\
                b = ( ; ; ; 1 0 0 9 )
              )
              \/
              (
                (
                  a = ( ; ; ; ; ; 3 4 0 0 3 3 )
                  /\
                  b = ( ; ; 6 7 4 )
                )
                \/
                (
                  a = ( ; ; ; ; ; ; 1 3 5 8 1 1 4 )
                  /\
                  b = ( ; ; 6 7 3 )
                )
              )
            )
          )
        )
      )
    )
  $.
$}
