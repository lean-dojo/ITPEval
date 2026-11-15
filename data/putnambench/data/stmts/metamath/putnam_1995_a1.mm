$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1995_a1: a partition of a multiplicatively closed set of real
  numbers into two triple-product-closed subsets has at least one subset
  closed under binary multiplication. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  S, T, and U range over arbitrary sets of real numbers. The antecedent
  preserves the closure of S under multiplication, the two subset
  conditions, the disjoint-union partition of S, and closure of each part
  under products of three not necessarily distinct elements.

  The conclusion is the source disjunction: either T or U is closed under
  products of two elements. The final declaration is the single unproved
  $a corpus statement; this database contains no $p proof statement.
$)

${
  $d S T U a b c $.

  putnambench-putnam-1995-a1 $a |-
    A. S e. ~P RR
      A. T e. ~P RR
        A. U e. ~P RR
          (
            (
              (
                A. a e. S A. b e. S
                  ( a x. b ) e. S
                /\
                (
                  ( T C_ S /\ U C_ S )
                  /\
                  (
                    ( T u. U ) = S
                    /\
                    ( T i^i U ) = (/)
                  )
                )
              )
              /\
              (
                A. a e. T A. b e. T A. c e. T
                  ( ( a x. b ) x. c ) e. T
                /\
                A. a e. U A. b e. U A. c e. U
                  ( ( a x. b ) x. c ) e. U
              )
            )
            ->
            (
              A. a e. T A. b e. T
                ( a x. b ) e. T
              \/
              A. a e. U A. b e. U
                ( a x. b ) e. U
            )
          )
  $.
$}
