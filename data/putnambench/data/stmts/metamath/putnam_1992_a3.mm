$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1992_a3: classification of positive integer solutions to
  (x^2+y^2)^m = (xy)^n when n and m are relatively prime.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is set.mm's class of natural numbers including zero. The antecedent
  retains the source assumption that m is positive. The right side inlines
  the documented solution: for an internal natural witness r, m = 2r,
  n = 2r+1, and x = y = 2^r.

  This pointwise biconditional is extensionally equivalent to the
  Lean/Isabelle equality between the set of solution triples and the
  documented solution set, and directly matches the Rocq formulation.
  The final declaration is a single unproved $a statement encoding; this
  database contains no $p proof declaration.
$)

${
  $d m n r x y $.

  putnambench-putnam-1992-a3 $a |-
    A. m e. NN0
      (
        0 < m
        ->
        A. n e. NN0 A. x e. NN0 A. y e. NN0
          (
            (
              (
                0 < n
                /\
                (
                  0 < x
                  /\
                  (
                    0 < y
                    /\
                    (
                      ( n gcd m ) = 1
                      /\
                      ( ( ( x ^ 2 ) + ( y ^ 2 ) ) ^ m )
                      =
                      ( ( x x. y ) ^ n )
                    )
                  )
                )
              )
              <->
              E. r e. NN0
                (
                  x = ( 2 ^ r )
                  /\
                  (
                    y = ( 2 ^ r )
                    /\
                    (
                      n = ( ( 2 x. r ) + 1 )
                      /\
                      m = ( 2 x. r )
                    )
                  )
                )
            )
          )
      )
  $.
$}
