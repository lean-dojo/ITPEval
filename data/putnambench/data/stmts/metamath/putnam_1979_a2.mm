$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1979_a2: characterization of the real constants k for which a
  continuous real function satisfies f(f(x)) = k x^9 for every real x.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  f ranges over all total real-valued functions on the reals, and membership
  in ( RR -cn-> RR ) is set.mm's native assertion of continuity. The
  existential quantifier over f remains internal to each real parameter k.
  The right side is the explicit solution predicate k >= 0 recorded in the
  ground-truth sources.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d f k x $.

  putnambench-putnam-1979-a2 $a |- A. k e. RR
    (
      E. f e. ( RR ^m RR )
        (
          f e. ( RR -cn-> RR )
          /\
          A. x e. RR
            ( f ` ( f ` x ) )
            =
            ( k x. ( x ^ 9 ) )
        )
      <->
      0 <_ k
    )
  $.
$}
