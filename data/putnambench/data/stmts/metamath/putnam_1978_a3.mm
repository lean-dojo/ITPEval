$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1978_a3: among the four integrals over the nonnegative real
  half-line of x^k divided by the specified degree-six polynomial, the
  integral with exponent 2 is smallest. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The interval ( 0 [,) +oo ) is set.mm's full set of nonnegative real
  numbers. Its inclusion of zero agrees with the Isabelle and Rocq sources
  and does not change the Lean integral over the open positive half-line,
  since the domains differ only by a singleton. The polynomial is inlined
  pointwise, and the Lebesgue integral binder S. A F _d x therefore gives
  exactly the source integral I_k.

  The first conjunct records that 2 is an admissible index. The restricted
  universal states that its integral is no greater than I_k for every
  integer k from 1 through 4. Together these are equivalent to the source
  least-value formulation with solution index 2.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d k x $.

  putnambench-putnam-1978-a3 $a |- (
    2 e. ( 1 ... 4 )
    /\
    A. k e. ( 1 ... 4 )
      (
        S. ( 0 [,) +oo )
          (
            ( x ^ 2 )
            /
            (
              (
                (
                  2
                  x.
                  ( ( x ^ 6 ) + 1 )
                )
                +
                (
                  4
                  x.
                  ( ( x ^ 5 ) + x )
                )
              )
              +
              (
                (
                  3
                  x.
                  ( ( x ^ 4 ) + ( x ^ 2 ) )
                )
                +
                ( 5 x. ( x ^ 3 ) )
              )
            )
          )
          _d x
        <_
        S. ( 0 [,) +oo )
          (
            ( x ^ k )
            /
            (
              (
                (
                  2
                  x.
                  ( ( x ^ 6 ) + 1 )
                )
                +
                (
                  4
                  x.
                  ( ( x ^ 5 ) + x )
                )
              )
              +
              (
                (
                  3
                  x.
                  ( ( x ^ 4 ) + ( x ^ 2 ) )
                )
                +
                ( 5 x. ( x ^ 3 ) )
              )
            )
          )
          _d x
      )
  ) $.
$}
