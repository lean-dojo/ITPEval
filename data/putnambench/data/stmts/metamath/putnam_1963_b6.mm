$(
  Statement-only formalization of PutnamBench artifact putnam_1963_b6:
  stabilization after two iterations of closed-segment closure for a
  nonempty subset of a real Euclidean space of dimension one, two, or three.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For a natural number d, RR ^m ( 1 ... d ) is the d-dimensional real
  coordinate space. P63B6SegClosure D B is the set of all coordinatewise convex
  combinations (1-t)p+tq with p,q in B and t in the closed interval [0,1].
  Thus it is exactly the union of the closed segments joining pairs of points
  of B, including one-point segments. The final declaration is one unproved
  $a corpus statement; this database contains no $p proof statement.
$)

$c P63B6SegClosure $.

p63b6-segment-closure-syntax $a
  class ( P63B6SegClosure D B )
$.

${
  $d B D i p q r t $.

  p63b6-segment-closure-definition $a |- (
    P63B6SegClosure D B
  ) = {
    r e. ( RR ^m D ) |
      E. p e. B E. q e. B E. t e. ( 0 [,] 1 )
        A. i e. D
          ( r ` i ) =
            (
              ( ( 1 - t ) x. ( p ` i ) )
              +
              ( t x. ( q ` i ) )
            )
  } $.
$}

${
  $d A d i n p q r t $.

  putnambench-putnam-1963-b6 $a |- A. d e. NN
    A. A e. ( ( ~P ( RR ^m ( 1 ... d ) ) ) ^m NN0 )
      (
        (
          (
            1 <_ d
            /\
            d <_ 3
          )
          /\
          (
            ( A ` 0 ) =/= (/)
            /\
            A. n e. NN0
              (
                1 <_ n
                ->
                ( A ` n ) =
                  (
                    P63B6SegClosure ( 1 ... d )
                      ( A ` ( n - 1 ) )
                  )
              )
          )
        )
        ->
        A. n e. NN0
          (
            2 <_ n
            ->
            ( A ` n ) = ( A ` ( n + 1 ) )
          )
      )
  $.
$}
