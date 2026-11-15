$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1990_b5: existence of an infinite sequence of nonzero real
  coefficients whose nth truncation has exactly n distinct real roots for
  every positive integer n. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m NN0 is set.mm's class of all real-valued sequences indexed by the
  nonnegative integers. For each positive n, the finite sum is exactly the
  polynomial a_0 + a_1 x + ... + a_n x^n, and the cardinality expression
  counts its distinct real roots.

  The Rocq source expresses the same root condition by exhibiting n distinct
  roots. Since the coefficient at n is nonzero, the polynomial has degree n
  and therefore has at most n roots, making that formulation equivalent to
  the exact-cardinality formulation below. The annotated solution is True,
  so the source biconditional is equivalent to this existence assertion.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d A i n x $.

  putnambench-putnam-1990-b5 $a |-
    E. A e. ( RR ^m NN0 )
      (
        A. i e. NN0
          ( A ` i ) =/= 0
        /\
        A. n e. NN
          (
            #
            `
            {
              x e. RR |
              (
                sum_ i e. ( 0 ... n )
                  (
                    ( A ` i )
                    x.
                    ( x ^ i )
                  )
              )
              =
              0
            }
          )
          =
          n
      )
  $.
$}
