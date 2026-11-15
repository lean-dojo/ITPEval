$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2005_a3: every nonzero differentiable critical point of
  g(z) = p(z) / z^(n/2), for a positive-degree complex polynomial whose
  zeros all have modulus one, has modulus one. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Poly ` CC is set.mm's set of complex polynomial functions, and deg is
  their natural-valued degree. Complex exponentiation ^c gives the source's
  z^(n/2), while membership in dom ( CC _D g ) explicitly preserves the
  Lean differentiability-at-z premise. The function g remains an arbitrary
  total complex function constrained pointwise by its defining equation.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d P g n w z $.

  putnambench-putnam-2005-a3 $a |-
    A. P e. ( Poly ` CC )
      A. n e. NN
        A. g e. ( CC ^m CC )
          A. z e. CC
            (
              (
                (
                  ( deg ` P ) = n
                  /\
                  A. w e. CC
                    (
                      ( P ` w ) = 0
                      ->
                      ( abs ` w ) = 1
                    )
                )
                /\
                (
                  A. w e. CC
                    ( g ` w )
                    =
                    (
                      ( P ` w )
                      /
                      ( w ^c ( n / 2 ) )
                    )
                  /\
                  (
                    z =/= 0
                    /\
                    (
                      z e. dom ( CC _D g )
                      /\
                      ( ( CC _D g ) ` z ) = 0
                    )
                  )
                )
              )
              ->
              ( abs ` z ) = 1
            )
  $.
$}
