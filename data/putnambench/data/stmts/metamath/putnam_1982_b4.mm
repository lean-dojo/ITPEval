$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1982_b4: two claims about nonempty finite sets of distinct integers
  whose product divides the product obtained after every integer translation:
  such a set contains 1 or -1, and if all its members are positive then it is
  the initial interval from 1 through its cardinality. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  A finite set N represents the distinct integers n_1, ..., n_s. The
  antecedent in each claim inlines the source predicate: N is a nonempty
  subset of ZZ, and for every integer k its finite product divides the finite
  product of the translated members i + k.

  Membership of 1 or -1 is equivalent to the source conclusion that some
  member has absolute value 1. For a positive N, the set.mm interval
  1 ... (# ` N) is exactly {1, ..., card N}. The ground-truth annotation gives
  the solution pair (True, True), so the conjunction below is equivalent to
  the source's two biconditionals with the components of that pair. The final
  declaration is the single unproved $a corpus statement; this database
  contains no $p proof statement.
$)

${
  $d N i k $.

  putnambench-putnam-1982-b4 $a |-
    (
      A. N e. Fin
        (
          (
            (
              N C_ ZZ
              /\
              N =/= (/)
            )
            /\
            A. k e. ZZ
              (
                prod_ i e. N i
                ||
                prod_ i e. N ( i + k )
              )
          )
          ->
          (
            1 e. N
            \/
            ( -u 1 ) e. N
          )
        )
      /\
      A. N e. Fin
        (
          (
            (
              (
                N C_ ZZ
                /\
                N =/= (/)
              )
              /\
              A. k e. ZZ
                (
                  prod_ i e. N i
                  ||
                  prod_ i e. N ( i + k )
                )
            )
            /\
            A. i e. N 0 < i
          )
          ->
          N = ( 1 ... ( # ` N ) )
        )
    )
  $.
$}
