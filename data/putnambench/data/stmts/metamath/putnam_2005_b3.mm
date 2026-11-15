$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2005_b3: classification of positive differentiable functions on
  the positive reals satisfying a reciprocal-argument derivative equation
  as positive constant multiples of positive real powers. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m RR is the class of total real-valued functions. The hypotheses
  restrict positivity and membership in the domain of set.mm's real
  derivative to positive inputs, exactly representing a differentiable
  function from (0,+infinity) to (0,+infinity). Since a and x are positive,
  a / x is also in that derivative domain.

  On positive x, set.mm's complex-power expression x ^c d agrees with the
  real power exp(d log x). The right side inlines the source solution set:
  c and d are positive, d = 1 implies c = 1, and F(x) = c x^d for every
  positive x. All witnesses remain internally existentially quantified.
  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d F a c d x $.

  putnambench-putnam-2005-b3 $a |-
    A. F e. ( RR ^m RR )
      (
        (
          A. x e. RR
            (
              0 < x
              ->
              0 < ( F ` x )
            )
          /\
          A. x e. RR
            (
              0 < x
              ->
              x e. dom ( RR _D F )
            )
        )
        ->
        (
          E. a e. RR
            (
              0 < a
              /\
              A. x e. RR
                (
                  0 < x
                  ->
                  ( ( RR _D F ) ` ( a / x ) )
                  =
                  ( x / ( F ` x ) )
                )
            )
          <->
          E. c e. RR E. d e. RR
            (
              0 < c
              /\
              0 < d
              /\
              ( d = 1 -> c = 1 )
              /\
              A. x e. RR
                (
                  0 < x
                  ->
                  ( F ` x )
                  =
                  ( c x. ( x ^c d ) )
                )
            )
        )
      )
  $.
$}
