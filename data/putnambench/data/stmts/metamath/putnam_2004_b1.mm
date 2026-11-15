$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2004_b1: partial sums formed from the reversed coefficients of an
  integer polynomial at a rational root are integers. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  For n in NN0, the inclusive interval 0 ... n indexes every coefficient of
  a polynomial of degree n. The function c has integer values on this
  interval, and ( c ` n ) =/= 0 makes the degree exactly n. Conversely, every
  integer polynomial of exact degree n determines exactly one such
  coefficient function, so this finite coefficient representation is
  bidirectionally equivalent to the source polynomial object.

  The root assumption is the usual evaluation sum from degree zero through
  n. The half-open interval 0 ..^ n indexes exactly the source's n
  conclusions, and each conclusion directly asserts membership of the
  reversed-coefficient partial sum in ZZ. All coefficient, root, and index
  domains and all quantifiers remain explicit.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d c i j k n r $.

  putnambench-putnam-2004-b1 $a |-
    A. n e. NN0
      A. c e. ( ZZ ^m ( 0 ... n ) )
        A. r e. QQ
          (
            (
              ( c ` n ) =/= 0
              /\
              (
                sum_ k e. ( 0 ... n )
                  ( ( c ` k ) x. ( r ^ k ) )
              )
              =
              0
            )
            ->
            A. i e. ( 0 ..^ n )
              (
                sum_ j e. ( 0 ... i )
                  (
                    ( c ` ( n - j ) )
                    x.
                    ( r ^ ( ( i + 1 ) - j ) )
                  )
              )
              e. ZZ
          )
  $.
$}
