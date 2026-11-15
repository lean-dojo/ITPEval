$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2024_b3: consecutive positive solutions of tan(x) = x, ordered
  increasingly without omitted solutions, have excess spacing above pi
  bounded by 1 / ((n^2 + n) pi). This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN is the class of positive integers, so RR ^m NN is exactly the
  source domain of positive-integer-indexed real sequences. The first
  conjunct states strict increase. The remaining assumptions say that r(1)
  is preceded by no positive solution, every r(k) is a positive solution of
  tan(x) = x, and no solution occurs strictly between r(k) and r(k+1).

  Membership in the final open interval is exactly the source pair of strict
  inequalities. SetMM's tan and _pi are the standard tangent function and
  pi, respectively. The declaration is the single unproved $a corpus
  statement; this database contains no $p proof declaration.
$)

${
  $d i j k n r x $.

  putnambench-putnam-2024-b3 $a |-
    A. r e. ( RR ^m NN )
      A. n e. NN
        (
          (
            A. i e. NN
              A. j e. NN
                (
                  i < j
                  ->
                  ( r ` i ) < ( r ` j )
                )
            /\
            (
              A. x e. ( 0 (,) ( r ` 1 ) )
                ( tan ` x ) =/= x
              /\
              A. k e. NN
                (
                  0 < ( r ` k )
                  /\
                  (
                    ( tan ` ( r ` k ) ) = ( r ` k )
                    /\
                    A. x e. ( ( r ` k ) (,) ( r ` ( k + 1 ) ) )
                      ( tan ` x ) =/= x
                  )
                )
            )
          )
          ->
          (
            (
              ( ( r ` ( n + 1 ) ) - ( r ` n ) )
              -
              _pi
            )
            e.
            (
              0
              (,)
              (
                1
                /
                (
                  ( ( n ^ 2 ) + n )
                  x.
                  _pi
                )
              )
            )
          )
        )
  $.
$}
