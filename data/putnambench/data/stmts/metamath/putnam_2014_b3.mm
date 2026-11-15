$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2014_b3: a rational matrix with at least m+n distinct primes among
  the absolute values of its entries has rank at least two. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  For positive m and n, the carriers 0 ..^ m and 0 ..^ n represent Fin m
  and Fin n. Thus QQ ^m ((0 ..^ m) X. (0 ..^ n)) is the full class of
  m-by-n rational matrices, with no finiteness restriction on the entry
  values.

  The restricted class abstraction is exactly the set of natural primes
  occurring as absolute values of entries of A, and # gives its finite
  cardinality. The conclusion says that A has a nonzero two-by-two minor.
  Over the rationals this is equivalent to matrix rank at least two. The
  final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d A i j m n p r s $.

  putnambench-putnam-2014-b3 $a |-
    A. m e. NN
      A. n e. NN
        A. A e.
          (
            QQ
            ^m
            ( ( 0 ..^ m ) X. ( 0 ..^ n ) )
          )
          (
            (
              ( m + n )
              <_
              (
                #
                `
                {
                  p e. Prime |
                  E. i e. ( 0 ..^ m )
                    E. j e. ( 0 ..^ n )
                      ( abs ` ( A ` <. i , j >. ) ) = p
                }
              )
            )
            ->
            E. r e. ( 0 ..^ m )
              E. s e. ( 0 ..^ m )
                E. i e. ( 0 ..^ n )
                  E. j e. ( 0 ..^ n )
                    (
                      ( r =/= s /\ i =/= j )
                      /\
                      (
                        (
                          ( A ` <. r , i >. )
                          x.
                          ( A ` <. s , j >. )
                        )
                        -
                        (
                          ( A ` <. r , j >. )
                          x.
                          ( A ` <. s , i >. )
                        )
                      )
                      =/=
                      0
                    )
          )
  $.
$}
