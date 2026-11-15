$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1997_a6: a recursively defined real sequence at the greatest
  parameter making its (n+1)-st term zero has binomial-coefficient values.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The family x ranges over arbitrary total maps from real parameters to
  NN0-indexed real sequences. The recurrence uses ordinary real subtraction,
  multiplication, and division, with n and k canonically embedded in RR.

  The two conditions on r say that r is itself a parameter making the
  (n+1)-st term zero and that every such real parameter is at most r. Thus r
  is exactly the greatest member of the source root set, equivalently the
  source largest-value/supremum formulation under its greatest-root
  hypothesis. The conclusion uses set.mm's inclusive natural interval and
  _C binomial-coefficient operation.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d c k n r x $.

  putnambench-putnam-1997-a6 $a |-
    A. n e. NN
      A. x e. ( ( RR ^m NN0 ) ^m RR )
        A. r e. RR
          (
            (
              (
                (
                  A. c e. RR
                    (
                      ( ( x ` c ) ` 0 ) = 0
                      /\
                      ( ( x ` c ) ` 1 ) = 1
                    )
                  /\
                  A. c e. RR
                    A. k e. NN0
                      ( ( x ` c ) ` ( k + 2 ) )
                      =
                      (
                        (
                          c x. ( ( x ` c ) ` ( k + 1 ) )
                        )
                        -
                        (
                          ( n - k ) x. ( ( x ` c ) ` k )
                        )
                      )
                      /
                      ( k + 1 )
                )
                /\
                ( ( x ` r ) ` ( n + 1 ) ) = 0
              )
              /\
              A. c e. RR
                (
                  ( ( x ` c ) ` ( n + 1 ) ) = 0
                  ->
                  c <_ r
                )
            )
            ->
            A. k e. ( 1 ... n )
              ( ( x ` r ) ` k )
              =
              ( ( n - 1 ) _C ( k - 1 ) )
          )
  $.
$}
