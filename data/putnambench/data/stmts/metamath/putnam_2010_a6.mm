$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2010_a6: divergence of the improper integral formed from a strictly
  decreasing continuous real function on the nonnegative half-line that
  tends to zero at positive infinity. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The interval ( 0 [,) +oo ) is set.mm's full set of nonnegative real
  numbers. The first two hypotheses say exactly that the restriction of f to
  this interval is strictly decreasing and continuous, while f ~~>r 0 is its
  finite real limit at positive infinity.

  The S. binder is set.mm's real Lebesgue integral. Closed rather than
  half-open finite endpoints do not change its value, so the upper-endpoint
  function agrees with the source interval integral. The negated
  existential keeps the finite real limit witness internal and states
  divergence in exactly the source sense. The final declaration is the
  single unproved $a corpus statement; this database contains no $p proof
  statement.
$)

${
  $d L f x y z $.

  putnambench-putnam-2010-a6 $a |- A. f e. ( RR ^m RR )
    (
      (
        (
          A. x e. ( 0 [,) +oo )
            A. y e. ( 0 [,) +oo )
              (
                x < y
                ->
                ( f ` y ) < ( f ` x )
              )
          /\
          ( f |` ( 0 [,) +oo ) )
            e. ( ( 0 [,) +oo ) -cn-> RR )
        )
        /\
        f ~~>r 0
      )
      ->
      -.
      E. L e. RR
        (
          z e. RR |->
            S. ( 0 [,] z )
              (
                (
                  ( f ` x )
                  -
                  ( f ` ( x + 1 ) )
                )
                /
                ( f ` x )
              )
              _d x
        )
        ~~>r
        L
    )
  $.
$}
