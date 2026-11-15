$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2021_a6: a zero-one coefficient integer polynomial that factors
  into two nonconstant integer polynomials has composite value at two.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Base ` ( Poly1 ` ZZring ) is SetMM's ring of all finite-support
  univariate polynomials over the integers. The function coe1 gives the
  complete nonnegative-integer-indexed coefficient sequence, and eval1 is
  ordinary polynomial evaluation.

  A factor has positive degree exactly when some coefficient at a positive
  index is nonzero. Thus both nonconstant factors remain internally
  existentially quantified without selecting external degree bounds.
  Membership in Prime is primality for positive natural integers; together
  with exclusion of zero and one, its negation states the source composite
  conclusion. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof declaration.
$)

${
  $d P Q R i j n $.

  putnambench-putnam-2021-a6 $a |-
    A. P e. ( Base ` ( Poly1 ` ZZring ) )
      (
        (
          A. n e. NN0
            (
              ( ( coe1 ` P ) ` n ) = 0
              \/
              ( ( coe1 ` P ) ` n ) = 1
            )
          /\
          E. Q e. ( Base ` ( Poly1 ` ZZring ) )
            E. R e. ( Base ` ( Poly1 ` ZZring ) )
              (
                P
                =
                (
                  Q
                  ( .r ` ( Poly1 ` ZZring ) )
                  R
                )
                /\
                (
                  E. i e. NN ( ( coe1 ` Q ) ` i ) =/= 0
                  /\
                  E. j e. NN ( ( coe1 ` R ) ` j ) =/= 0
                )
              )
        )
        ->
        (
          (
            (
              ( eval1 ` ZZring )
              `
              P
            )
            `
            2
          )
          =/= 0
          /\
          (
            (
              (
                ( eval1 ` ZZring )
                `
                P
              )
              `
              2
            )
            =/= 1
            /\
            -.
            (
              (
                (
                  ( eval1 ` ZZring )
                  `
                  P
                )
                `
                2
              )
              e. Prime
            )
          )
        )
      )
  $.
$}
