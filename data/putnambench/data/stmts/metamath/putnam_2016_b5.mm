$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2016_b5: classification of functions from (1, +infinity) to itself
  satisfying a two-sided power inequality as positive real power functions.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The class ( 1 (,) +oo ) is set.mm's open real interval (1, +infinity),
  and the function space quantifies arbitrary functions from that interval
  to itself. Thus the source codomain condition f(x) > 1 is retained in the
  type of f.

  Natural powers express the inequalities in the hypothesis. Since x > 1
  and c is real, set.mm's complex-power expression x ^c c is real-valued
  and agrees with the source real power. The exponent witness remains
  internally existentially quantified. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof
  declaration.
$)

${
  $d c f x y $.

  putnambench-putnam-2016-b5 $a |-
    A. f e. ( ( 1 (,) +oo ) ^m ( 1 (,) +oo ) )
      (
        A. x e. ( 1 (,) +oo ) A. y e. ( 1 (,) +oo )
          (
            (
              ( x ^ 2 ) <_ y
              /\
              y <_ ( x ^ 3 )
            )
            ->
            (
              ( ( f ` x ) ^ 2 ) <_ ( f ` y )
              /\
              ( f ` y ) <_ ( ( f ` x ) ^ 3 )
            )
          )
        <->
        E. c e. RR
          (
            0 < c
            /\
            A. x e. ( 1 (,) +oo )
              ( f ` x ) = ( x ^c c )
          )
      )
  $.
$}
