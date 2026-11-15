$(
  Statement-only formalization of PutnamBench artifact putnam_1965_a3:
  equivalence of convergence for complex exponential averages over the first
  n terms and over the first n squared terms of an arbitrary real sequence.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A ranges over all real-valued sequences indexed by the nonnegative
  integers, and L ranges over the complex numbers. Each side of the
  biconditional expands convergence to L in the complex modulus into its
  epsilon-threshold form. The inclusive finite intervals reproduce the source
  sums from 1 through n and from 1 through n squared. The final declaration is
  the single unproved $a corpus statement; this database contains no $p proof
  statement.
$)

${
  $d A L e k m n $.

  putnambench-putnam-1965-a3 $a |- A. A e. ( RR ^m NN0 )
    A. L e. CC
      (
        A. e e. RR
          (
            0 < e
            ->
            E. m e. NN0
              A. n e. NN0
                (
                  m <_ n
                  ->
                  (
                    abs
                    `
                    (
                      (
                        (
                          sum_ k e. ( 1 ... n )
                            ( exp ` ( _i x. ( A ` k ) ) )
                        )
                        /
                        n
                      )
                      -
                      L
                    )
                  )
                  < e
                )
          )
        <->
        A. e e. RR
          (
            0 < e
            ->
            E. m e. NN0
              A. n e. NN0
                (
                  m <_ n
                  ->
                  (
                    abs
                    `
                    (
                      (
                        (
                          sum_ k e. ( 1 ... ( n ^ 2 ) )
                            ( exp ` ( _i x. ( A ` k ) ) )
                        )
                        /
                        ( n ^ 2 )
                      )
                      -
                      L
                    )
                  )
                  < e
                )
          )
      )
  $.
$}
