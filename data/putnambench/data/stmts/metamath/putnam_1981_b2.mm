$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1981_b2: the minimum of a four-term sum of squared successive
  ratio deviations over real numbers satisfying 1 <= r <= s <= t <= 4
  is 12 - 8 times the square root of 2. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The first conjunct states that 12 - 8 sqrt(2) is a lower bound for the
  objective on every admissible real triple. The second conjunct keeps the
  attaining triple existentially quantified inside the statement and requires
  both its admissibility and equality with that lower bound. Together these
  clauses are the explicit IsLeast characterization used by the sources.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d r s t $.

  putnambench-putnam-1981-b2 $a |-
    (
      A. r e. RR A. s e. RR A. t e. RR
        (
          (
            1 <_ r
            /\
            (
              r <_ s
              /\
              (
                s <_ t
                /\
                t <_ 4
              )
            )
          )
          ->
          (
            ( 3 x. 4 )
            -
            ( 8 x. ( sqrt ` 2 ) )
          )
          <_
          (
            (
              (
                ( r - 1 ) ^ 2
                +
                ( ( ( s / r ) - 1 ) ^ 2 )
              )
              +
              ( ( ( t / s ) - 1 ) ^ 2 )
            )
            +
            ( ( ( 4 / t ) - 1 ) ^ 2 )
          )
        )
      /\
      E. r e. RR E. s e. RR E. t e. RR
        (
          (
            1 <_ r
            /\
            (
              r <_ s
              /\
              (
                s <_ t
                /\
                t <_ 4
              )
            )
          )
          /\
          (
            (
              (
                ( r - 1 ) ^ 2
                +
                ( ( ( s / r ) - 1 ) ^ 2 )
              )
              +
              ( ( ( t / s ) - 1 ) ^ 2 )
            )
            +
            ( ( ( 4 / t ) - 1 ) ^ 2 )
          )
          =
          (
            ( 3 x. 4 )
            -
            ( 8 x. ( sqrt ` 2 ) )
          )
        )
    )
  $.
$}
