$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1978_b3: the largest real roots of a recursively defined sequence
  of real polynomials are strictly increasing and converge to zero. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  Poly1 ` RRfld is SetMM's ring of finite-support real univariate
  polynomials. The sequence p ranges over all functions from the positive
  integers NN into that ring, while a ranges over all positive-indexed real
  sequences. The operations var1, algSc, and eval1 are respectively the
  indeterminate, constant-polynomial embedding, and polynomial evaluation.

  The root hypotheses say both that a(n) is a root of p(n) and that every
  real root is at most a(n), exactly characterizing the largest real root.
  Strict increase is stated for every pair of positive indices, and the
  epsilon-threshold clause is convergence to zero at infinity.

  Isabelle extends a to index zero with a(0) = -2 and asks for strict
  monotonicity on all nonnegative indices. Since P(1) = 1 + X forces its
  largest real root a(1) to equal -1, that extension is bidirectionally
  equivalent to the positive-indexed formulation used here, in Lean, and
  in Rocq. The final declaration is the single unproved $a corpus statement;
  this database contains no $p proof statement.
$)

${
  $d a e i j m n p x $.

  putnambench-putnam-1978-b3 $a |-
    A. p e. ( ( Base ` ( Poly1 ` RRfld ) ) ^m NN )
    A. a e. ( RR ^m NN )
      (
        (
          (
            (
              ( p ` 1 )
              =
              (
                ( ( algSc ` ( Poly1 ` RRfld ) ) ` 1 )
                ( +g ` ( Poly1 ` RRfld ) )
                ( var1 ` RRfld )
              )
              /\
              ( p ` 2 )
              =
              (
                ( ( algSc ` ( Poly1 ` RRfld ) ) ` 1 )
                ( +g ` ( Poly1 ` RRfld ) )
                (
                  ( ( algSc ` ( Poly1 ` RRfld ) ) ` 2 )
                  ( .r ` ( Poly1 ` RRfld ) )
                  ( var1 ` RRfld )
                )
              )
            )
            /\
            (
              A. n e. NN
                (
                  ( p ` ( ( 2 x. n ) + 1 ) )
                  =
                  (
                    ( p ` ( 2 x. n ) )
                    ( +g ` ( Poly1 ` RRfld ) )
                    (
                      (
                        ( ( algSc ` ( Poly1 ` RRfld ) ) ` ( n + 1 ) )
                        ( .r ` ( Poly1 ` RRfld ) )
                        ( var1 ` RRfld )
                      )
                      ( .r ` ( Poly1 ` RRfld ) )
                      ( p ` ( ( 2 x. n ) - 1 ) )
                    )
                  )
                )
              /\
              A. n e. NN
                (
                  ( p ` ( ( 2 x. n ) + 2 ) )
                  =
                  (
                    ( p ` ( ( 2 x. n ) + 1 ) )
                    ( +g ` ( Poly1 ` RRfld ) )
                    (
                      (
                        ( ( algSc ` ( Poly1 ` RRfld ) ) ` ( n + 1 ) )
                        ( .r ` ( Poly1 ` RRfld ) )
                        ( var1 ` RRfld )
                      )
                      ( .r ` ( Poly1 ` RRfld ) )
                      ( p ` ( 2 x. n ) )
                    )
                  )
                )
            )
          )
          /\
          (
            A. n e. NN
              (
                (
                  ( ( eval1 ` RRfld ) ` ( p ` n ) )
                  `
                  ( a ` n )
                )
                =
                0
              )
            /\
            A. n e. NN
              A. x e. RR
                (
                  (
                    (
                      ( ( eval1 ` RRfld ) ` ( p ` n ) )
                      `
                      x
                    )
                    =
                    0
                  )
                  ->
                  x <_ ( a ` n )
                )
          )
        )
        ->
        (
          (
            A. i e. NN
              A. j e. NN
                (
                  i < j
                  ->
                  ( a ` i ) < ( a ` j )
                )
          )
          /\
          A. e e. RR
            (
              0 < e
              ->
              E. m e. NN
                A. n e. NN
                  (
                    m <_ n
                    ->
                    ( abs ` ( a ` n ) ) < e
                  )
            )
        )
      )
  $.
$}
