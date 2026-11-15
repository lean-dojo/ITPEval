$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2021_b2: the maximum of a weighted infinite series of geometric
  means over nonnegative real sequences with total sum one is two-thirds.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The function a ranges over all real-valued sequences indexed by the
  positive integers NN. The first unbounded sum is the source constraint
  sum_k a_k = 1. The second is the source series, with 1 ... n indexing its
  finite prefix product. Since every factor is nonnegative and n is
  positive, set.mm's complex-power operation ^c with exponent 1 / n agrees
  with the nonnegative real n-th root.

  The first conjunct supplies an admissible sequence attaining 2 / 3. The
  second bounds the same series by 2 / 3 for every admissible sequence.
  Together these are definitionally the IsGreatest formulation in the Lean
  source and the maximum requested by the published problem. The final
  declaration is a single unproved $a corpus statement; this database
  contains no $p proof declaration.
$)

${
  $d a k n $.

  putnambench-putnam-2021-b2 $a |-
    (
      E. a e. ( RR ^m NN )
        (
          (
            (
              sum_ k e. NN
                ( a ` k )
            )
            =
            1
            /\
            A. k e. NN
              0 <_ ( a ` k )
          )
          /\
          (
            sum_ n e. NN
              (
                (
                  n
                  /
                  ( 2 ^ n )
                )
                x.
                (
                  (
                    prod_ k e. ( 1 ... n )
                      ( a ` k )
                  )
                  ^c
                  ( 1 / n )
                )
              )
          )
          =
          ( 2 / 3 )
        )
      /\
      A. a e. ( RR ^m NN )
        (
          (
            (
              sum_ k e. NN
                ( a ` k )
            )
            =
            1
            /\
            A. k e. NN
              0 <_ ( a ` k )
          )
          ->
          (
            sum_ n e. NN
              (
                (
                  n
                  /
                  ( 2 ^ n )
                )
                x.
                (
                  (
                    prod_ k e. ( 1 ... n )
                      ( a ` k )
                  )
                  ^c
                  ( 1 / n )
                )
              )
          )
          <_
          ( 2 / 3 )
        )
    )
  $.
$}
