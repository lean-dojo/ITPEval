$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1984_a3: evaluation of a punctured real limit involving the
  determinant of a parity-patterned two-n-by-two-n matrix. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  The matrix is indexed by 0 through 2n - 1, matching the Lean Fin
  indexing. Its diagonal entries are x; an off-diagonal entry is a when
  the sum of its indices is even and b otherwise. The Isabelle source
  uses indices 1 through 2n; shifting every index by one preserves both
  the parity of each index sum and the determinant.

  The limCC relation expresses the punctured two-sided limit, so the
  totalized value of the displayed quotient at x = a is irrelevant.
  The annotated solution polynomial evaluates to n^2 (a^2 - b^2).
  The final $a assertion is the statement encoding; no $p proof is
  supplied.
$)

${
  $d a b i j n x $.

  putnambench-putnam-1984-a3 $a |-
    A. n e. NN
      A. a e. RR
        A. b e. RR
          ( a =/= b ->
            ( ( n ^ 2 ) x. ( ( a ^ 2 ) - ( b ^ 2 ) ) ) e.
              ( ( x e. RR |->
                    ( ( ( ( 0 ..^ ( 2 x. n ) ) maDet RRfld ) `
                          ( i e. ( 0 ..^ ( 2 x. n ) ) ,
                            j e. ( 0 ..^ ( 2 x. n ) ) |->
                              if ( i = j , x ,
                                if ( ( ( i + j ) mod 2 ) = 0 ,
                                  a , b ) ) ) )
                      / ( ( x - a ) ^ ( ( 2 x. n ) - 2 ) ) ) )
                limCC a ) ) $.
$}
