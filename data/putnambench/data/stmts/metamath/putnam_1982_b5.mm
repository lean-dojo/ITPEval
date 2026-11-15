$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1982_b5: convergence of the recursively defined real sequence
  u_0 = e, u_(n+1) = log base u_n of x for x greater than e^e, and
  continuity of its real limit as a function of x. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  S ranges over all real-indexed families of NN0-indexed real sequences.
  The source set T is inlined as the open interval
  ( exp(exp(1)), +infinity ). Real.logb u x and the Rocq recurrence are both
  represented by (log x) / (log u).

  The first conclusion retains the real limit existentially at every x in
  T. The second quantifies over every total real function G whose values are
  those limits and asserts continuity of its restriction to T. Since real
  sequence limits are unique, this is equivalent to continuity of the
  canonical limit function used by the Rocq source. Relative continuity on
  this open interval is equivalent to pointwise real continuity at each of
  its points.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d G L S n x $.

  putnambench-putnam-1982-b5 $a |-
    A. S e. ( ( RR ^m NN0 ) ^m RR )
      (
        (
          A. x e. RR
            (
              ( exp ` ( exp ` 1 ) ) < x
              ->
              (
                ( ( S ` x ) ` 0 ) = ( exp ` 1 )
                /\
                A. n e. NN0
                  ( ( S ` x ) ` ( n + 1 ) )
                  =
                  (
                    ( log ` x )
                    /
                    ( log ` ( ( S ` x ) ` n ) )
                  )
              )
            )
        )
        ->
        (
          A. x e. RR
            (
              ( exp ` ( exp ` 1 ) ) < x
              ->
              E. L e. RR
                ( ( S ` x ) ~~> L )
            )
          /\
          A. G e. ( RR ^m RR )
            (
              A. x e. RR
                (
                  ( exp ` ( exp ` 1 ) ) < x
                  ->
                  ( ( S ` x ) ~~> ( G ` x ) )
                )
              ->
              (
                ( G |` ( ( exp ` ( exp ` 1 ) ) (,) +oo ) )
                e.
                (
                  ( ( exp ` ( exp ` 1 ) ) (,) +oo )
                  -cn->
                  RR
                )
              )
            )
        )
      )
  $.
$}
