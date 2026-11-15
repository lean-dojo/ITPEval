$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1977_a2: classification of the nonzero real quadruples satisfying
  a + b + c = d and 1/a + 1/b + 1/c = 1/d. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The four variables range over all real numbers, and the antecedent preserves
  the four nonzero assumptions from the source statements. The solution
  predicate is expanded explicitly as the three possible pair-cancellation
  cases.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a b c d $.

  putnambench-putnam-1977-a2 $a |-
    A. a e. RR A. b e. RR A. c e. RR A. d e. RR
      (
        (
          (
            a =/= 0
            /\
            b =/= 0
          )
          /\
          (
            c =/= 0
            /\
            d =/= 0
          )
        )
        ->
        (
          (
            (
              ( ( a + b ) + c )
              =
              d
            )
            /\
            (
              ( ( 1 / a ) + ( 1 / b ) ) + ( 1 / c )
              =
              ( 1 / d )
            )
          )
          <->
          (
            (
              d = a
              /\
              b = ( -u c )
            )
            \/
            (
              (
                d = b
                /\
                a = ( -u c )
              )
              \/
              (
                d = c
                /\
                a = ( -u b )
              )
            )
          )
        )
      )
  $.
$}
